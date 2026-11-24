/** Layer 1: the TypeScript models must agree with the TLA+ specs.
 *  DESIGN.md §10.2.
 *
 *  This is a REPLICATION check: two implementations of the same semantics
 *  agreeing. It cannot catch an error in the semantics itself, in question
 *  selection, in rendering, or in diagnosis — layers 2 through 5 exist for
 *  those. What it does catch is the TypeScript port drifting from the spec,
 *  which is the single most likely way a wrong answer gets shipped.
 */

import { execFileSync } from 'node:child_process';
import { copyFileSync, existsSync, mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { bfs } from '@dyp/engine';
import { ALL_CONFIGS, MUTANTS, defaultConstants, flagsFor, paxos } from '@dyp/models';
import { repoPath } from './paths.js';

const TOOLS = repoPath('tools');
const JAR = join(TOOLS, 'tla2tools.jar');
const SPEC_DIR = repoPath('specs', 'tla', 'paxos');
const WORK = repoPath('specs', 'tla', 'tracecheck');
const TLA_URL =
  'https://github.com/tlaplus/tlaplus/releases/download/v1.7.1/tla2tools.jar';

/* Two ballots, explored exhaustively. Three ballots is where P2 separates but
 * TLC's full state space there is large enough to make CI slow; the bound here
 * is about checking the port, not about generating questions. */
const MAX_BALLOT = 1;

if (!existsSync(JAR)) {
  mkdirSync(TOOLS, { recursive: true });
  console.log('downloading tla2tools.jar ...');
  execFileSync('curl', ['-sSL', '-o', JAR, TLA_URL], { stdio: 'inherit' });
}
mkdirSync(WORK, { recursive: true });
/* TLC resolves the config relative to the spec file, so run everything from a
 * single scratch directory with plain relative names. */
copyFileSync(join(SPEC_DIR, 'PaxosFlagged.tla'), join(WORK, 'PaxosFlagged.tla'));

const FLAG_OF: Record<string, string> = {
  ownValue: 'OwnValue',
  anyReported: 'AnyReported',
  noQuorumPhase1: 'NoQuorumPhase1',
  ignorePromise: 'IgnorePromise',
  forgetfulPromise: 'ForgetfulPromise',
  noPromiseUpdate: 'NoPromiseUpdate',
  multiProposalPerBallot: 'MultiProposalPerBallot',
  strictAccept: 'StrictAccept',
  unanimousPhase1: 'UnanimousPhase1',
  voteOnce: 'VoteOnce',
  monotoneBallots: 'MonotoneBallots',
};
const ALL_TLA_FLAGS = Object.values(FLAG_OF);

function cfgFor(config: string): string {
  const on = new Set<string>();
  for (const [ts, tla] of Object.entries(FLAG_OF)) if (flagsFor(config)[ts as never]) on.add(tla);
  const lines = [
    'SPECIFICATION Spec',
    'CONSTANTS',
    '  Acceptors = {a1, a2, a3}',
    '  Values = {vx, vy}',
    '  None = NoneVal',
    `  MaxBallot = ${MAX_BALLOT}`,
    ...ALL_TLA_FLAGS.map((f) => `  ${f} = ${on.has(f) ? 'TRUE' : 'FALSE'}`),
    'INVARIANT TypeOK',
    'CHECK_DEADLOCK FALSE',
  ];
  return lines.join('\n') + '\n';
}

interface TlcResult {
  distinct: number;
  agreementBroken: boolean;
}

function runTlc(config: string, checkAgreement: boolean): TlcResult {
  const cfgName = `cc_${config}${checkAgreement ? '_agr' : ''}`;
  let cfg = cfgFor(config);
  if (checkAgreement) cfg = cfg.replace('INVARIANT TypeOK', 'INVARIANT TypeOK\nINVARIANT Agreement');
  writeFileSync(join(WORK, `${cfgName}.cfg`), cfg);

  let out: string;
  let broke = false;
  try {
    out = execFileSync(
      'java',
      [
        '-XX:+UseParallelGC',
        '-cp',
        JAR,
        'tlc2.TLC',
        '-config',
        `${cfgName}.cfg`,
        '-workers',
        'auto',
        '-cleanup',
        'PaxosFlagged.tla',
      ],
      { encoding: 'utf8', maxBuffer: 64 * 1024 * 1024, cwd: WORK },
    );
  } catch (e) {
    const err = e as { stdout?: string; status?: number };
    out = err.stdout ?? '';
    // TLC exits non-zero on an invariant violation, which is the expected
    // outcome for the mutants that break agreement.
    if (/Invariant Agreement is violated/.test(out)) broke = true;
    else if (!/generated.*distinct states/.test(out)) {
      console.error(out.slice(-4000));
      throw new Error(`TLC failed for ${config}`);
    }
  }

  const m = /([0-9]+) states generated, ([0-9]+) distinct states found/.exec(out);
  if (!m && !broke) {
    console.error(out.slice(-4000));
    throw new Error(`could not parse TLC output for ${config}`);
  }
  /* TLC exits 0 even when it aborts on a spec error, reporting "0 distinct
   * states found". Treat that as the failure it is rather than silently
   * comparing against zero. */
  if (!broke && (Number(m![2]) === 0 || /^Error: (?!TLC threw)/m.test(out))) {
    console.error(out.slice(-4000));
    throw new Error(`TLC reported an error for ${config}`);
  }
  return { distinct: m ? Number(m[2]) : -1, agreementBroken: broke };
}

/* ------------------------------------------------------------------ */

const K = defaultConstants(Array.from({ length: MAX_BALLOT + 1 }, (_, i) => i));
let failures = 0;

console.log(`TLC cross-check — ${K.acceptors} acceptors, ${K.values.length} values, ballots 0..${MAX_BALLOT}\n`);
console.log('cfg    JS states   TLC states   match   agreement(JS/TLC)   direction');

for (const cfg of ALL_CONFIGS) {
  const m = paxos(K, flagsFor(cfg));
  const g = bfs(m, { maxStates: 500_000, keepTransitions: false });
  let jsBroke = false;
  for (const s of g.states.values())
    if (!m.predicates.Agreement(s)) {
      jsBroke = true;
      break;
    }

  const tlc = runTlc(cfg, true);
  // When TLC stops on a violated invariant its state count is partial, so the
  // count comparison is only meaningful for configs that preserve agreement.
  const counted = tlc.agreementBroken ? runTlc(cfg, false) : tlc;

  const match = counted.distinct === g.depth.size;
  const agrMatch = jsBroke === tlc.agreementBroken;
  if (!match || !agrMatch) failures++;

  const spec = MUTANTS.find((x) => x.id === cfg);
  console.log(
    `${cfg.padEnd(5)} ${String(g.depth.size).padStart(10)} ${String(counted.distinct).padStart(12)}` +
      `   ${match ? ' ok ' : 'FAIL'}    ${String(jsBroke).padStart(5)}/${String(tlc.agreementBroken).padEnd(5)} ` +
      `${agrMatch ? ' ok ' : 'FAIL'}   ${spec?.direction ?? 'correct'}`,
  );
}

console.log(
  failures === 0
    ? '\nCross-check passed: the TypeScript models and the TLA+ spec agree on every config.'
    : `\nCross-check FAILED on ${failures} config(s). The TLA+ spec is the source of truth; fix the TypeScript.`,
);
process.exit(failures === 0 ? 0 : 1);
