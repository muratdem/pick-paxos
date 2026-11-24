/** Layer 5: does the bank actually diagnose? DESIGN.md §10.6.
 *
 *  This is the verification of the GAME rather than of the model, and nothing
 *  else in the pipeline substitutes for it. TLC can tell us the answer key is
 *  right; only this can tell us the questions identify anything.
 *
 *  Two populations:
 *    baselines - cheap strategies that should score at or below chance. If any
 *                beats chance the bank has a surface regularity and is broken.
 *    believers - a learner running exactly mutant i. Must end with p_i high and
 *                every other p_j low, or the results screen will lie.
 */

import { readFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import {
  EPSILON,
  PRIOR,
  Rng,
  clusterReport,
  membershipAnswer,
  recompute,
  recomputeCategorical,
  selectNext,
  selectNextExclusive,
  verdict,
  type Answer,
  type AnswerRecord,
  type Bank,
  type Question,
} from '@dyp/engine';
import { repoPath } from './paths.js';

const BANK_DIR = repoPath('banks', 'paxos');
const SEEDS = 200;
const MAX_QUESTIONS = Number(process.env.MAX_Q ?? 14);

function loadBanks(): Bank[] {
  return readdirSync(BANK_DIR)
    .filter((f) => f.endsWith('.json') && f !== 'content.json')
    .map((f) => JSON.parse(readFileSync(join(BANK_DIR, f), 'utf8')) as Bank)
    .filter((b) => Array.isArray(b.configs) && b.questions.length > 0);
}

const pairOf = (q: Question, cfg: string) => q.answer[cfg] as [boolean, boolean];

/* ---- learners ---------------------------------------------------------- */

type Learner = (q: Question, rng: Rng) => Answer;

function believer(config: string, eps: number): Learner {
  return (q, rng) => {
    const truth = pairOf(q, config);
    const noisy: [boolean, boolean] = [
      rng.bool(eps) ? !truth[0] : truth[0],
      rng.bool(eps) ? !truth[1] : truth[1],
    ];
    return membershipAnswer(noisy);
  };
}

/** Size of the side's POST-state. Using the pre-state would be useless: both
 *  members of a pair share one pre-state by construction, so a pre-state
 *  heuristic silently degenerates into "always answer B". */
const sizeOfSide = (q: Question, side: 'a' | 'b'): number => {
  const p = (side === 'a' ? q.a : q.b!).payload as unknown as {
    post?: { msgs?: unknown[]; maxVal?: unknown[] };
    state?: { msgs?: unknown[]; maxVal?: unknown[] };
  };
  const st = p.post ?? p.state;
  return (st?.msgs?.length ?? 0) * 10 + (st?.maxVal?.filter(Boolean).length ?? 0);
};

const BASELINES: Record<string, Learner> = {
  'always-A': () => 'A',
  'always-B': () => 'B',
  'always-both': () => 'both',
  'always-neither': () => 'neither',
  'uniform-random': (_q, rng) => rng.pick(['A', 'B', 'both', 'neither'] as Answer[]),
  'bigger-is-illegal': (q) => (sizeOfSide(q, 'a') >= sizeOfSide(q, 'b') ? 'B' : 'A'),
  'prefer-first-shown': () => 'A',
};

/* ---- one simulated session --------------------------------------------- */

interface SessionResult {
  correctAnswers: number;
  total: number;
  p: Record<string, number>;
}

function runSession(bank: Bank, learner: Learner, seed: number): SessionResult {
  const rng = new Rng(seed);
  const misconceptions = bank.configs.filter((c) => c !== 'C');
  const asked = new Set<string>();
  const answers: AnswerRecord[] = [];
  let p: Record<string, number> = Object.fromEntries(misconceptions.map((m) => [m, PRIOR]));
  let correct = 0;

  for (let n = 0; n < MAX_QUESTIONS; n++) {
    const q = bank.exclusive
      ? selectNextExclusive(bank.questions, asked, p, bank.configs)
      : selectNext(bank.questions, asked, p);
    if (!q) break;
    const ans = learner(q, rng);
    if (ans === membershipAnswer(pairOf(q, 'C'))) correct++;
    answers.push({ questionId: q.id, answer: ans });
    asked.add(q.id);
    p = bank.exclusive
      ? recomputeCategorical(bank.questions, answers, bank.configs)
      : recompute(bank.questions, answers, misconceptions);
    /* Stop when the posterior is settled. For an exclusive bank that means
     * one candidate has won, NOT that every misconception is below 0.1 -
     * the latter is also true when the correct candidate is leading, which
     * would end the session before it ever had to choose between them. */
    if (
      bank.exclusive
        ? Math.max(...bank.configs.map((c) => p[c] ?? 0)) > 0.95
        : misconceptions.every((m) => p[m] < 0.1 || p[m] > 0.9)
    )
      break;
  }
  return { correctAnswers: correct, total: answers.length, p };
}

/* ---- report ------------------------------------------------------------ */

let failures = 0;

for (const bank of loadBanks()) {
  const misconceptions = bank.configs.filter((c) => c !== 'C');
  /* A level only targets some mutants: the phase-1 bank says nothing about a
   * phase-2 misconception, so a P1-believer answers it exactly like an honest
   * learner and p_P1 correctly stays at the prior. Requiring identification of
   * an untargeted mutant measures nothing. */
  const targeted = new Set<string>();
  for (const q of bank.questions) for (const m of q.misconceptions) targeted.add(m);
  console.log(`\n=== ${bank.level} — ${bank.questions.length} questions, ` +
    `mix ${bank.mix.one}/${bank.mix.both}/${bank.mix.neither}, up to ${MAX_QUESTIONS} asked ===`);
  console.log(`    targets: ${[...targeted].join(' ')}`);

  /* Baselines are scored over the WHOLE bank, not over a sampled session.
   * Constant strategies are deterministic, so a session-based number is a
   * single trajectory, not an average, and swings by 1/n between rebuilds.
   * "What fraction of this bank would this strategy get right?" is a stable
   * property of the artifact and is what we actually want to bound. */
  console.log('\n  baseline accuracy over the whole bank (must stay near chance, <=40%)');
  for (const [name, l] of Object.entries(BASELINES)) {
    const rng = new Rng(99);
    let acc = 0;
    for (const q of bank.questions)
      if (l(q, rng) === membershipAnswer(pairOf(q, 'C'))) acc++;
    const pct = (100 * acc) / bank.questions.length;
    const bad = pct > 40;
    if (bad) failures++;
    console.log(`    ${name.padEnd(20)} ${pct.toFixed(1).padStart(5)}%  ${bad ? '  <-- BEATS CHANCE' : ''}`);
  }

  /* an honest learner must come out clean */
  {
    let clean = 0;
    for (let s = 0; s < SEEDS; s++) {
      const r = runSession(bank, believer('C', EPSILON), 7000 + s);
      if (misconceptions.every((m) => verdict(r.p[m]) !== 'likely')) clean++;
    }
    const pct = (100 * clean) / SEEDS;
    const bad = pct < 85;
    if (bad) failures++;
    console.log(
      `\n  learner with NO misconceptions reported clean: ${pct.toFixed(0)}%` +
        `${bad ? '   <-- FALSE POSITIVES' : ''}`,
    );
  }

  /* believers and the confusion matrix */
  console.log('\n  confusion matrix — rows: the learner truly holds this.');
  console.log('  columns: how often that misconception is reported "likely".\n');
  const confusion: Record<string, Record<string, number>> = {};
  const header = misconceptions.map((m) => m.padStart(5)).join('');
  console.log(`      ${header}    identified`);
  for (const truth of misconceptions) {
    const hits: Record<string, number> = Object.fromEntries(misconceptions.map((m) => [m, 0]));
    let identified = 0;
    for (let s = 0; s < SEEDS; s++) {
      const r = runSession(bank, believer(truth, EPSILON), 2000 + s);
      for (const m of misconceptions) if (verdict(r.p[m]) === 'likely') hits[m]++;
      if (verdict(r.p[truth]) === 'likely') identified++;
    }
    confusion[truth] = Object.fromEntries(misconceptions.map((m) => [m, hits[m] / SEEDS]));
    const row = misconceptions
      .map((m) => {
        const v = (100 * hits[m]) / SEEDS;
        return (v === 0 ? '  .' : v.toFixed(0)).padStart(5);
      })
      .join('');
    const idPct = (100 * identified) / SEEDS;
    const inScope = targeted.has(truth);
    const bad = inScope && idPct < 90;
    if (bad) failures++;
    console.log(
      `  ${truth.padEnd(4)}${row}    ${inScope ? idPct.toFixed(0).padStart(3) + '%' : '   -'}` +
        `${bad ? ' <-- MISSED' : ''}`,
    );
  }

  const scoped: Record<string, Record<string, number>> = {};
  for (const t of targeted) scoped[t] = Object.fromEntries([...targeted].map((m) => [m, confusion[t][m]]));
  const clusters = clusterReport(scoped).filter((c) => c.length > 1);
  if (clusters.length)
    console.log(
      `\n  inseparable, must be reported as clusters: ${clusters.map((c) => c.join('/')).join(', ')}`,
    );
  else console.log('\n  all misconceptions separable — no clustering needed.');
}

console.log(
  failures === 0
    ? '\nHarness passed.'
    : `\nHarness FAILED with ${failures} problem(s). The bank does not diagnose reliably.`,
);
process.exit(failures === 0 ? 0 : 1);
