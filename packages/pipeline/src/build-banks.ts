/** Bank generation. DESIGN.md §6.
 *
 *  Step difference is the only primitive (§14). Note what that buys: mutant
 *  membership is evaluated LOCALLY on each candidate step, so generating the
 *  step levels needs a BFS of the correct config only. The mutants never get
 *  explored. BFS of the mutants is needed only for Agreement verdicts and for
 *  the reachability/closure levels.
 */

import { copyFileSync, mkdirSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import {
  Rng,
  bfs,
  buildPairs,
  enumerateSteps,
  hash,
  selectPairs,
  stableStringify,
  type Bank,
  type FieldRef,
  type Justification,
  type Model,
  type PairCand,
  type Question,
  type Scenario,
  type StepCand,
  type Value,
} from '@dyp/engine';
import {
  ALL_CONFIGS,
  CORRECT,
  MUTANTS,
  PHASE1_MUTANTS,
  PHASE2_MUTANTS,
  accName,
  defaultConstants,
  flagsFor,
  msgKey,
  paxos,
  type Msg,
  type PaxosState,
} from '@dyp/models';
import { buildAnchoredBank } from './anchored.js';
import {
  CONTENT_STATUS,
  MISCONCEPTIONS,
  RULES,
  checkNoNotation,
  checkRuleCoverage,
  ruleFor,
} from './content.js';
import { repoPath } from './paths.js';

const SEED = 20261123;
const BANK_DIR = repoPath('banks', 'paxos');

/* ---- generation bound ------------------------------------------------- */
/* Three ballots because P2 (anyReported) is state-equivalent to Paxos at two:
 * with ballots {0,1} the 1b messages seen in ballot 1 can only report votes
 * from ballot 0, and ballot 0 carries at most one value, so there is never a
 * choice to get wrong. Depth 14 is where P2 first separates (measured).
 *
 * The depth bound restricts WHICH reachable pre-states we draw from. It never
 * affects an answer at the step level, because step legality is local: the
 * guard is evaluated against the pre-state in front of the learner. */
const BALLOTS = [0, 1, 2];
const GEN_DEPTH = 14;

const K = defaultConstants(BALLOTS);
const models: Record<string, Model<PaxosState>> = {};
for (const cfg of ALL_CONFIGS) models[cfg] = paxos(K, flagsFor(cfg));
const CM = models[CORRECT];

checkRuleCoverage([
  ...new Set(
    Object.values(models).flatMap((m) => m.actions.flatMap((a) => a.guard.map((c) => c.id))),
  ),
  ...CM.actions.map((a) => `${a.name}.effect`),
]);
checkNoNotation();

const msgCount = (s: PaxosState) => s.msgs.length;

/* ---- justification ---------------------------------------------------- */

const ballotWord = (b: number) => (b < 0 ? 'nothing' : `ballot ${b}`);
const voteWord = (s: PaxosState, a: number) =>
  s.maxVBal[a] < 0 ? 'no vote at all' : `${s.maxVal[a]} in ballot ${s.maxVBal[a]}`;
const reportWord = (m: Msg) =>
  m.t === '1b'
    ? m.mbal < 0
      ? 'that it has never voted'
      : `its last vote, ${m.mval} in ballot ${m.mbal}`
    : '';

/** Say exactly WHICH part of the step is wrong, by diffing the state it
 *  produces against the one Paxos would produce.
 *
 *  Naming the rule is not enough when a rule has two halves. A promise both
 *  reports the acceptor's last vote AND raises its promised ballot; a step that
 *  gets the second half wrong was being explained with a paragraph covering
 *  both, leaving the reader to work out which one broke. The correct successor
 *  is right there at build time, so the difference can simply be stated.
 */
function describeEffectDifference(step: StepCand<PaxosState>): string[] {
  const correct = CM.actions.find((a) => a.name === step.action)!.effect(step.pre, step.params);
  const shown = step.post;
  const out: string[] = [];

  for (let a = 0; a < shown.maxBal.length; a++) {
    if (shown.maxBal[a] !== correct.maxBal[a])
      out.push(
        `promising must raise ${accName(a)}'s promised ballot to ${correct.maxBal[a]}, and this ` +
          `step leaves it ${shown.maxBal[a] < 0 ? 'unset' : `at ${shown.maxBal[a]}`} — so ` +
          `${accName(a)} has not actually committed to anything and could still go on to accept ` +
          `an older ballot, which is the one thing a promise is supposed to rule out`,
      );
    if (shown.maxVBal[a] !== correct.maxVBal[a] || shown.maxVal[a] !== correct.maxVal[a])
      out.push(
        `it must record ${accName(a)}'s last vote as ${voteWord(correct, a)}, ` +
          `but this step records ${voteWord(shown, a)}`,
      );
  }

  const shownKeys = new Set(shown.msgs.map(msgKey));
  const correctKeys = new Set(correct.msgs.map(msgKey));
  const missing = correct.msgs.filter((m) => !shownKeys.has(msgKey(m)));
  const extra = shown.msgs.filter((m) => !correctKeys.has(msgKey(m)));

  for (const want of missing) {
    // A message of the same kind that was sent instead is a changed message,
    // not a missing one plus a spurious one.
    const instead = extra.find((m) => m.t === want.t);
    if (instead && want.t === '1b' && instead.t === '1b') {
      out.push(
        `the promise must report ${accName(want.acc)}'s last vote — ${reportWord(want).replace(/^its last vote, /, '')} ` +
          `— and this one reports ${reportWord(instead)}`,
      );
      extra.splice(extra.indexOf(instead), 1);
    } else if (!instead) {
      out.push(`it must announce something it does not announce here`);
    }
  }
  for (const spurious of extra)
    out.push(`it announces a ${spurious.t} message that Paxos would not send`);

  return out;
}

function justify(step: StepCand<PaxosState>): Justification {
  const action = CM.actions.find((a) => a.name === step.action)!;

  if (!step.membership[CORRECT]) {
    const id = step.failed[CORRECT];
    const rule = ruleFor(id);
    const refs = id.endsWith('.effect')
      ? CM.view.displayed(step.pre).filter((r) => r.kind !== 'param')
      : (action.guard.find((c) => c.id === id)?.reads(step.pre, step.params) ?? []);

    if (id.endsWith('.effect')) {
      const diffs = describeEffectDifference(step);
      const what =
        diffs.length === 0
          ? 'the state it leaves behind is not the one Paxos would produce'
          : diffs.length === 1
            ? diffs[0]
            : `${diffs.slice(0, -1).join('; ')}; and ${diffs[diffs.length - 1]}`;
      return {
        verdict: 'illegal',
        conjunct: id,
        refs,
        // Lead with the concrete difference; the rule follows as the reason.
        text: `Paxos does not allow this step as shown: ${what}. ${rule.text}`,
      };
    }

    return {
      verdict: 'illegal',
      conjunct: id,
      refs,
      text: `Paxos does not allow this step — ${rule.short}. ${rule.text}`,
    };
  }

  const refs: FieldRef[] = [];
  for (const c of action.guard) refs.push(...c.reads(step.pre, step.params));
  const shorts = action.guard.map((c) => ruleFor(c.id).short);
  return {
    verdict: 'legal',
    refs,
    text:
      (shorts.length === 0
        ? 'Paxos allows this step. '
        : `Paxos allows this step — ${shorts.join('; ')}. `) +
      ruleFor(`${step.action}.effect`).text,
  };
}

/** §10.5 check 2: the reasoning must only reference facts the renderer shows. */
function checkRefsVisible(step: StepCand<PaxosState>, j: Justification): void {
  const shown = new Set(CM.view.displayed(step.pre).map((r) => stableStringify(r)));
  for (const r of j.refs)
    if (!shown.has(stableStringify(r)))
      throw new Error(
        `justification for ${step.action} references ${stableStringify(r)}, which the renderer does not display`,
      );
}

function scenarioOf(step: StepCand<PaxosState>): Scenario {
  const j = justify(step);
  checkRefsVisible(step, j);
  return {
    payload: {
      kind: 'step',
      pre: step.pre as unknown as Value,
      post: step.post as unknown as Value,
      action: step.action,
      params: step.params,
      reads: step.reads,
      sends: step.sends,
      describe: step.describe,
    },
    justification: j,
  };
}

/* ---- pre-state sampling ----------------------------------------------- */
/* Stratified by message count, not just "smallest first". The subtle mutants
 * need elaborate situations: P2 needs a quorum reporting two different values
 * at two different ballots, which cannot happen in a small state. Taking only
 * the smallest states silently drops exactly the misconceptions worth testing. */

function stratify(
  states: PaxosState[],
  range: [number, number],
  perBucket: number,
  seed: number,
): PaxosState[] {
  const buckets = new Map<number, PaxosState[]>();
  for (const s of states) {
    const n = msgCount(s);
    if (n < range[0] || n > range[1]) continue;
    let arr = buckets.get(n);
    if (!arr) buckets.set(n, (arr = []));
    arr.push(s);
  }
  const rng = new Rng(seed);
  const seen = new Set<string>();
  const out: PaxosState[] = [];
  for (const n of [...buckets.keys()].sort((a, b) => a - b)) {
    let taken = 0;
    for (const s of rng.shuffle(buckets.get(n)!)) {
      if (taken >= perBucket) break;
      const rep = CM.symmetry!.orbit(s).map((x) => CM.key(x)).sort()[0];
      if (seen.has(rep)) continue;
      seen.add(rep);
      out.push(s);
      taken++;
    }
  }
  return out;
}

/* ---- step levels ------------------------------------------------------ */

interface LevelSpec {
  level: string;
  title: string;
  blurb: string;
  actions: string[];
  mutants: string[];
  total: number;
  msgRange: [number, number];
  perBucket: number;
}

const STEP_LEVELS: LevelSpec[] = [
  {
    level: 'paxos-phase1-steps',
    title: 'Phase 1 — promises',
    blurb:
      'A proposer asks the acceptors to promise a ballot, and each acceptor answers. ' +
      'Which of these two steps does Paxos allow?',
    actions: ['Phase1a', 'Phase1b'],
    mutants: PHASE1_MUTANTS,
    total: 24,
    msgRange: [0, 8],
    perBucket: 60,
  },
  {
    level: 'paxos-phase2-steps',
    title: 'Phase 2 — proposing and accepting',
    blurb:
      'The proposer has heard back and now proposes a value; acceptors vote. ' +
      'This is where the protocol is won or lost.',
    actions: ['Phase2a', 'Phase2b'],
    mutants: PHASE2_MUTANTS,
    total: 40,
    msgRange: [1, 14],
    perBucket: 70,
  },
];

/** Targeted search for pre-states that separate one named mutant from Paxos.
 *
 *  Stratified random sampling misses the subtle mutants. P2 (anyReported) is
 *  the clearest case: separating it needs a quorum whose promises report two
 *  DIFFERENT values at two different ballots, and the smallest state with that
 *  shape carries thirteen messages and sits at depth 13. There are very few of
 *  them among 74k states, so a 70-per-bucket sample will essentially never draw
 *  one. Scanning for them directly is the only way they make it into the bank.
 */
function findSeparating(mutant: string, actions: string[], limit: number): PaxosState[] {
  const out: PaxosState[] = [];
  const seen = new Set<string>();
  for (const s of allStates) {
    let hit = false;
    for (const a of CM.actions) {
      if (!actions.includes(a.name)) continue;
      for (const p of a.domain()) {
        const okC = CM.enabled(s, a.name, p).ok;
        const okM = models[mutant].enabled(s, a.name, p).ok;
        if (okC !== okM) {
          hit = true;
          break;
        }
        if (okC && CM.key(a.effect(s, p)) !== models[mutant].key(models[mutant].actions.find((x) => x.name === a.name)!.effect(s, p))) {
          hit = true;
          break;
        }
      }
      if (hit) break;
    }
    if (!hit) continue;
    const rep = CM.symmetry!.orbit(s).map((x) => CM.key(x)).sort()[0];
    if (seen.has(rep)) continue;
    seen.add(rep);
    out.push(s);
    if (out.length >= limit) break;
  }
  return out;
}

console.log(`BFS of the correct config: ballots ${JSON.stringify(BALLOTS)}, depth<=${GEN_DEPTH}`);
let t = Date.now();
const g = bfs(CM, { maxStates: 500_000, maxDepth: GEN_DEPTH, keepTransitions: false });
console.log(`  ${g.depth.size} reachable states in ${Date.now() - t}ms`);
const allStates = [...g.states.values()];

mkdirSync(BANK_DIR, { recursive: true });
const summary: string[] = [];

function writeBank(bank: Bank, note: string) {
  /* §10.5 check 3: the renderer must be injective on the bank. If two
   * semantically different scenarios render identically the question is
   * unanswerable no matter how correct the key is.
   *
   * The sharp case is WITHIN a question: if A and B render the same, the
   * learner is being asked to tell apart two identical pictures. An earlier
   * version of this check only compared across questions and happily shipped
   * a `chosen` level whose two cards were byte-identical. */
  const rendered = new Map<string, string>();
  for (const q of bank.questions) {
    const sides = ([q.a, q.b].filter(Boolean) as Scenario[]).map((sc) =>
      stableStringify(sc.payload as unknown as Value),
    );
    if (sides.length === 2 && sides[0] === sides[1])
      throw new Error(`${bank.level} ${q.id}: both cards render identically`);
    for (const identity of sides) {
      const prev = rendered.get(hash(identity));
      if (prev && prev !== identity) throw new Error(`renderer collision in ${bank.level}`);
      rendered.set(hash(identity), identity);
    }
  }
  writeFileSync(join(BANK_DIR, `${bank.level}.json`), JSON.stringify(bank, null, 1));
  summary.push(note);
}

for (const spec of STEP_LEVELS) {
  t = Date.now();
  const sampled = stratify(allStates, spec.msgRange, spec.perBucket, SEED);

  const pairs: PairCand<PaxosState>[] = [];
  for (const s of sampled) {
    const cands = enumerateSteps(models, CORRECT, s).filter((c) => spec.actions.includes(c.action));
    if (cands.length < 2) continue;
    pairs.push(...buildPairs(cands, CORRECT, ALL_CONFIGS, (c) => msgCount(c.pre)));
  }

  const eligible = new Map<string, number>();
  for (const p of pairs) for (const m of p.misconceptions) eligible.set(m, (eligible.get(m) ?? 0) + 1);

  // Any target mutant the general sample missed gets a targeted scan.
  const rescued: string[] = [];
  for (const mut of spec.mutants) {
    if ((eligible.get(mut) ?? 0) >= 8) continue;
    const extra = findSeparating(mut, spec.actions, 12);
    for (const s of extra) {
      const cands = enumerateSteps(models, CORRECT, s).filter((c) => spec.actions.includes(c.action));
      if (cands.length < 2) continue;
      for (const p of buildPairs(cands, CORRECT, ALL_CONFIGS, (c) => msgCount(c.pre)))
        if (p.misconceptions.includes(mut)) pairs.push(p);
    }
    const now = pairs.filter((p) => p.misconceptions.includes(mut)).length;
    rescued.push(`${mut}:${eligible.get(mut) ?? 0}->${now}`);
    eligible.set(mut, now);
  }

  const chosen = selectPairs(pairs, {
    mix: { one: 0.6, both: 0.2, neither: 0.2 },
    total: spec.total,
    seed: SEED,
    restrictTo: spec.mutants,
  });

  /* Randomise which member is shown as A. Without this the generator's own
   * enumeration order leaks into the answer key: candidate steps come out in
   * action/parameter order, so the legal one lands in slot A far more often
   * than chance and "always pick A" scores well above guessing. The harness
   * catches it, but only because the harness exists. */
  let oneSeen = 0;
  const questions: Question[] = chosen.map((p, i) => {
    // Alternate deterministically rather than flipping a coin. A coin only
    // re-randomises the bias; it does not remove it, and with a dozen questions
    // drawn from the bank a run of heads puts "always pick B" well above
    // chance. Alternating makes any subset close to balanced by construction.
    const flip = p.type === 'one' ? oneSeen++ % 2 === 1 : (i & 1) === 1;
    const [x, y] = flip ? [p.b, p.a] : [p.a, p.b];
    const answer: Record<string, [boolean, boolean]> = {};
    for (const c of ALL_CONFIGS) answer[c] = [x.membership[c], y.membership[c]];
    return {
      id: `${spec.level}-${String(i).padStart(3, '0')}`,
      kind: 'step',
      type: p.type,
      a: scenarioOf(x),
      b: scenarioOf(y),
      distance: p.distance,
      contrast: p.contrast,
      answer,
      targets: p.targets,
      misconceptions: p.misconceptions,
      size: p.size,
    };
  });

  const mix = { one: 0, both: 0, neither: 0 };
  for (const q of questions) mix[q.type]++;
  const cover = new Map<string, number>();
  for (const q of questions) for (const m of q.misconceptions) cover.set(m, (cover.get(m) ?? 0) + 1);

  writeBank(
    {
      protocol: 'paxos',
      level: spec.level,
      title: spec.title,
      blurb: spec.blurb,
      generatedFrom: {
        modelVersion: '0.1.0',
        constants: { ...(K as unknown as Record<string, Value>), genDepth: GEN_DEPTH },
        configs: ALL_CONFIGS,
        seed: SEED,
      },
      configs: ALL_CONFIGS,
      questions,
      mix,
    },
    `${spec.level.padEnd(20)} q=${String(questions.length).padStart(3)} ` +
      `mix=${mix.one}/${mix.both}/${mix.neither}  ${sampled.length} pre-states, ${pairs.length} pairs\n` +
      `    selected  [${spec.mutants.map((m) => `${m}:${cover.get(m) ?? 0}`).join(' ')}]\n` +
      `    eligible  [${spec.mutants.map((m) => `${m}:${eligible.get(m) ?? 0}`).join(' ')}]` +
      (rescued.length ? `\n    rescued   [${rescued.join(' ')}]` : '') +
      `  ${Date.now() - t}ms`,
  );
}

/* ---- the anchored level ---------------------------------------- */
/* Replaces the old `chosen` level. Asking "has a majority voted for this
 * inside one ballot" is bookkeeping with a nearly-always-no answer; asking
 * "could this still end up being chosen" is the idea the protocol is built
 * around. See packages/pipeline/src/anchored.ts. */
{
  t = Date.now();
  const { bank, report } = buildAnchoredBank(SEED);
  for (const line of report) console.log(line);
  const cover = new Map<string, number>();
  for (const q of bank.questions) for (const d of q.misconceptions) cover.set(d, (cover.get(d) ?? 0) + 1);
  writeBank(
    bank,
    `paxos-anchored${' '.repeat(7)}q=${String(bank.questions.length).padStart(3)} ` +
      `mix=${bank.mix.one}/${bank.mix.both}/${bank.mix.neither}  ` +
      `[${bank.configs.filter((d) => d !== 'C').map((d) => `${d}:${cover.get(d) ?? 0}`).join(' ')}]  ${Date.now() - t}ms`,
  );
}

/* Ship the human-written text alongside the banks so the web app has no
 * build-time dependency on the YAML or on a parser. */
const defMembers: Record<string, string[]> = {};
writeFileSync(
  join(BANK_DIR, 'content.json'),
  JSON.stringify(
    {
      status: CONTENT_STATUS,
      misconceptions: MISCONCEPTIONS,
      rules: RULES,
      /** which raw candidates each (possibly collapsed) config id stands for */
      members: defMembers,
      levels: [
        { id: 'paxos-phase1-steps', order: 1, track: 'both' },
        { id: 'paxos-phase2-steps', order: 2, track: 'both' },
        { id: 'paxos-anchored', order: 3, track: 'both' },
      ],
    },
    null,
    1,
  ),
);

/* Mirror into the web app's public dir so Vite serves them. The copy under
 * packages/web/public is gitignored; banks/ is the reviewed source of truth. */
{
  const dest = repoPath('packages', 'web', 'public', 'banks');
  mkdirSync(dest, { recursive: true });
  for (const f of readdirSync(BANK_DIR)) copyFileSync(join(BANK_DIR, f), join(dest, f));
}

console.log('\nBanks written:');
for (const s of summary) console.log('  ' + s);
console.log(`\nConfigs: ${ALL_CONFIGS.join(' ')}  (${MUTANTS.length} mutants)`);
