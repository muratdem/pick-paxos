/** Learner model and question selection at runtime. DESIGN.md §7.2-§7.3.
 *
 *  Each misconception is tracked independently, because a learner can hold
 *  several at once. The independence assumption is KNOWN TO BE WRONG -
 *  misconceptions are correlated, so a learner holding P1 answers like P3 and
 *  P5 on most `one` pairs. Two defences: `neither` pairs are generated
 *  specifically to separate adding mutants from each other, and the results
 *  screen reports inseparable misconceptions as a cluster rather than
 *  individually (see `clusterReport`).
 */

import type { Question } from './types.js';

export type Answer = 'A' | 'B' | 'both' | 'neither' | 'unsure';

export const PRIOR = 0.3;
export const EPSILON = 0.1;

export function answerMembership(a: Answer): [boolean, boolean] | null {
  switch (a) {
    case 'A':
      return [true, false];
    case 'B':
      return [false, true];
    case 'both':
      return [true, true];
    case 'neither':
      return [false, false];
    case 'unsure':
      return null;
  }
}

export function membershipAnswer(m: [boolean, boolean]): Exclude<Answer, 'unsure'> {
  if (m[0] && m[1]) return 'both';
  if (m[0]) return 'A';
  if (m[1]) return 'B';
  return 'neither';
}

export interface AnswerRecord {
  questionId: string;
  answer: Answer;
}

function pairOf(q: Question, config: string): [boolean, boolean] {
  const v = q.answer[config];
  if (Array.isArray(v) && typeof v[0] === 'boolean') return v as [boolean, boolean];
  throw new Error(`question ${q.id} has no pair membership for ${config}`);
}

/** Recompute every p_i from scratch over the full answer history.
 *  Never update incrementally only: answers can be edited from the history
 *  drawer, and an incremental update cannot be undone correctly (§7.2). */
export function recompute(
  questions: Question[],
  answers: AnswerRecord[],
  misconceptions: string[],
  correct = 'C',
  prior = PRIOR,
  eps = EPSILON,
): Record<string, number> {
  const byId = new Map(questions.map((q) => [q.id, q]));
  const p: Record<string, number> = {};
  for (const m of misconceptions) p[m] = prior;

  for (const rec of answers) {
    if (rec.answer === 'unsure') continue;
    const q = byId.get(rec.questionId);
    if (!q) continue;
    const obs = answerMembership(rec.answer);
    if (!obs) continue;

    const mc = pairOf(q, correct);
    for (const i of misconceptions) {
      if (!q.misconceptions.includes(i)) continue; // this question says nothing about i
      const mi = pairOf(q, i);
      if (mi[0] === mc[0] && mi[1] === mc[1]) continue;

      const lik = (truth: [boolean, boolean]) =>
        (obs[0] === truth[0] ? 1 - eps : eps) * (obs[1] === truth[1] ? 1 - eps : eps);

      const li = lik(mi);
      const lc = lik(mc);
      const num = p[i] * li;
      const den = num + (1 - p[i]) * lc;
      p[i] = den === 0 ? p[i] : num / den;
    }
  }
  return p;
}

/** Categorical posterior over MUTUALLY EXCLUSIVE candidates, including the
 *  correct one. DESIGN.md §7.2.
 *
 *  Rule misconceptions are independent: you can believe both that the leader
 *  proposes its own value and that a promise is a bare ack. Definitions are
 *  not. You hold exactly one definition of "chosen", so the candidates are
 *  exclusive and the posterior must be a distribution over them.
 *
 *  Getting this wrong is not cosmetic. The definitions form a containment
 *  chain - a majority having voted implies someone voted implies something was
 *  proposed - so every state that is evidence for the strictest is equally
 *  evidence for all the looser ones. Scored independently, each gets pushed
 *  over the threshold and the results screen reports all three whichever one
 *  the learner actually holds. Scored categorically, the answers that the
 *  looser belief predicts and the stricter one does not are what decide it.
 */
export function recomputeCategorical(
  questions: Question[],
  answers: AnswerRecord[],
  configs: string[],
  eps = EPSILON,
): Record<string, number> {
  const byId = new Map(questions.map((q) => [q.id, q]));
  const logp: Record<string, number> = Object.fromEntries(configs.map((c) => [c, 0]));

  for (const rec of answers) {
    if (rec.answer === 'unsure') continue;
    const q = byId.get(rec.questionId);
    if (!q) continue;
    const obs = answerMembership(rec.answer);
    if (!obs) continue;
    for (const c of configs) {
      const truth = pairOf(q, c);
      const lik =
        (obs[0] === truth[0] ? 1 - eps : eps) * (obs[1] === truth[1] ? 1 - eps : eps);
      logp[c] += Math.log(Math.max(lik, 1e-12));
    }
  }

  const max = Math.max(...Object.values(logp));
  let z = 0;
  const out: Record<string, number> = {};
  for (const c of configs) {
    out[c] = Math.exp(logp[c] - max);
    z += out[c];
  }
  for (const c of configs) out[c] /= z;
  return out;
}

export type Verdict = 'likely' | 'not-detected' | 'unclear';

export function verdict(pi: number): Verdict {
  if (pi > 0.9) return 'likely';
  if (pi < 0.1) return 'not-detected';
  return 'unclear';
}

/** Pick the next question: the misconception with the highest uncertainty that
 *  still has unused questions, then an under-represented pair type, then
 *  distance 1, then smaller size (§7.3). */
export function selectNext(
  questions: Question[],
  asked: Set<string>,
  p: Record<string, number>,
): Question | null {
  const pool = questions.filter((q) => !asked.has(q.id));
  if (pool.length === 0) return null;

  const order = Object.keys(p).sort((a, b) => Math.abs(p[a] - 0.5) - Math.abs(p[b] - 0.5));

  const seenTypes = { one: 0, both: 0, neither: 0 } as Record<string, number>;
  for (const q of questions) if (asked.has(q.id)) seenTypes[q.type]++;
  const totalAsked = asked.size || 1;
  // Target mix follows the bank's own composition; see selectNextExclusive.
  const want = { one: 0, both: 0, neither: 0 } as Record<string, number>;
  for (const q of questions) want[q.type]++;
  for (const k of Object.keys(want)) want[k] /= questions.length || 1;

  let best: Question | null = null;
  let bestScore = -Infinity;
  for (const q of pool) {
    const focusRank = Math.min(
      ...q.misconceptions.map((m) => {
        const i = order.indexOf(m);
        return i < 0 ? 99 : i;
      }),
      99,
    );
    const deficit = want[q.type] - seenTypes[q.type] / totalAsked;
    const score = -focusRank * 3 + deficit * 5 - (q.distance - 1) * 1.5 - q.size * 0.2;
    if (score > bestScore) {
      bestScore = score;
      best = q;
    }
  }
  return best;
}

/** Selection for MUTUALLY EXCLUSIVE candidates — PICK's actual rule
 *  (Algorithm 1, step 2): draw the next scenario from where the live
 *  candidates disagree, prioritising the pair that is currently hardest to
 *  tell apart. Ranking by distance-from-0.5, as the independent model does,
 *  is meaningless over a distribution: with four candidates the "most
 *  uncertain" one is often just the one nobody is arguing about. */
export function selectNextExclusive(
  questions: Question[],
  asked: Set<string>,
  p: Record<string, number>,
  configs: string[],
): Question | null {
  const pool = questions.filter((q) => !asked.has(q.id));
  if (pool.length === 0) return null;

  const ranked = [...configs].sort((a, b) => (p[b] ?? 0) - (p[a] ?? 0));
  const top = ranked.slice(0, 2);

  /* Derive the target type mix from what the bank actually contains, rather
   * than hardcoding one. A fixed preference tuned for the step levels steers
   * hard away from `both` questions — which on the anchored level is half the
   * bank and precisely where the interesting misconceptions live. */
  const seenTypes: Record<string, number> = { one: 0, both: 0, neither: 0 };
  for (const q of questions) if (asked.has(q.id)) seenTypes[q.type]++;
  const want: Record<string, number> = { one: 0, both: 0, neither: 0 };
  for (const q of questions) want[q.type]++;
  for (const k of Object.keys(want)) want[k] /= questions.length || 1;
  const totalAsked = asked.size || 1;

  let best: Question | null = null;
  let bestScore = -Infinity;
  for (const q of pool) {
    const differs = (x: string, y: string) => {
      const a = q.answer[x] as [boolean, boolean];
      const b = q.answer[y] as [boolean, boolean];
      return a && b && (a[0] !== b[0] || a[1] !== b[1]);
    };
    // Primary: split the two leading candidates. Secondary: split any live pair,
    // weighted by how much posterior mass is actually at stake.
    const splitsTop = differs(top[0], top[1]) ? 1 : 0;
    let massSplit = 0;
    for (let i = 0; i < configs.length; i++)
      for (let j = i + 1; j < configs.length; j++)
        if (differs(configs[i], configs[j]))
          massSplit += Math.min(p[configs[i]] ?? 0, p[configs[j]] ?? 0);

    const deficit = want[q.type] - seenTypes[q.type] / totalAsked;
    const score = splitsTop * 10 + massSplit * 8 + deficit * 3 - q.size * 0.1;
    if (score > bestScore) {
      bestScore = score;
      best = q;
    }
  }
  return best;
}

/** Group misconceptions that the bank cannot separate, using the confusion
 *  matrix produced by the synthetic-learner harness (§10.6). Reported as
 *  "you hold at least one of P1/P3/P5" rather than claimed individually. */
export function clusterReport(
  confusion: Record<string, Record<string, number>>,
  threshold = 0.35,
): string[][] {
  const ids = Object.keys(confusion);
  const parent = new Map(ids.map((i) => [i, i]));
  const find = (x: string): string => (parent.get(x) === x ? x : find(parent.get(x)!));
  const union = (x: string, y: string) => parent.set(find(x), find(y));

  for (const i of ids)
    for (const j of ids)
      if (i !== j && (confusion[i]?.[j] ?? 0) > threshold) union(i, j);

  const groups = new Map<string, string[]>();
  for (const i of ids) {
    const r = find(i);
    if (!groups.has(r)) groups.set(r, []);
    groups.get(r)!.push(i);
  }
  return [...groups.values()];
}
