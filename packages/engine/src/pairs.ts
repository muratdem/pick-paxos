/** Step enumeration and contrast-pair construction. DESIGN.md §6.1-§6.2.
 *
 *  A step is a fully concrete labelled transition (s, action, params, s').
 *  The post-state is part of the step, not derived from it, because some
 *  mutants change an action's EFFECT rather than its guard (P5 forgetfulPromise,
 *  P6 noPromiseUpdate). Those mutants enable exactly the same action instances
 *  as Paxos but land somewhere else, and a membership vector defined only over
 *  guards would miss them entirely.
 */

import { leafDistance, stableStringify } from './canonical.js';
import { Rng } from './rng.js';
import type { Model, Params, PairType, Value } from './types.js';

export interface StepCand<S> {
  fromKey: string;
  pre: S;
  action: string;
  params: Params;
  toKey: string;
  post: S;
  reads: Value[];
  sends: Value[];
  describe: string;
  /** per config: does this config allow exactly this labelled transition? */
  membership: Record<string, boolean>;
  /** per config, when membership is false: the id of the first failing conjunct,
   *  or "<action>.effect" when the guard passes but the post-state differs. */
  failed: Record<string, string>;
}

/** Enumerate every candidate step out of `pre`, across all configs.
 *  Includes steps no config allows: those are useful filler for `neither` pairs. */
export function enumerateSteps<S>(
  models: Record<string, Model<S>>,
  correct: string,
  pre: S,
): StepCand<S>[] {
  const preKey = models[correct].key(pre);
  const configs = Object.keys(models);
  const cm = models[correct];
  const out: StepCand<S>[] = [];

  for (const action of cm.actions) {
    for (const params of action.domain()) {
      // Collect the distinct post-states this instance can land in, over configs.
      const posts = new Map<string, S>();
      for (const j of configs) {
        const m = models[j];
        if (!m.enabled(pre, action.name, params).ok) continue;
        const act = m.actions.find((a) => a.name === action.name)!;
        const post = act.effect(pre, params);
        posts.set(m.key(post), post);
      }
      // If nobody allows it, still emit the natural post-state so the step is
      // available as an illegal-for-everyone distractor.
      if (posts.size === 0) {
        const post = action.effect(pre, params);
        posts.set(cm.key(post), post);
      }

      for (const [toKey, post] of posts) {
        if (toKey === preKey) continue; // stutter is never a useful question
        const membership: Record<string, boolean> = {};
        const failed: Record<string, string> = {};
        for (const j of configs) {
          const m = models[j];
          const en = m.enabled(pre, action.name, params);
          if (!en.ok) {
            membership[j] = false;
            failed[j] = en.failed;
            continue;
          }
          const act = m.actions.find((a) => a.name === action.name)!;
          const got = m.key(act.effect(pre, params));
          membership[j] = got === toKey;
          if (got !== toKey) failed[j] = `${action.name}.effect`;
        }
        out.push({
          fromKey: preKey,
          pre,
          action: action.name,
          params,
          toKey,
          post,
          reads: action.reads(pre, params),
          sends: action.sends(pre, params),
          describe: action.describe(params),
          membership,
          failed,
        });
      }
    }
  }
  return out;
}

export interface PairCand<S> {
  a: StepCand<S>;
  b: StepCand<S>;
  distance: 1 | 2;
  contrast: 'effect' | 'params' | 'action';
  type: PairType;
  /** config pairs separated, as "X|Y" */
  targets: string[];
  /** mutants whose joint vector differs from the correct config's */
  misconceptions: string[];
  size: number;
}

/** Distance between two steps out of the same pre-state.
 *  1 = one parameter differs, or the effect differs; 2 = the action differs.
 *  Anything larger is not a contrasting case and is rejected (§6.2 step 4). */
export function contrastDistance<S>(a: StepCand<S>, b: StepCand<S>): number {
  if (a.fromKey !== b.fromKey) return Infinity;
  if (a.action !== b.action) return 2;
  const ka = Object.keys(a.params);
  let differing = 0;
  for (const k of ka) {
    if (stableStringify(a.params[k]) !== stableStringify(b.params[k])) differing++;
  }
  if (differing === 0) {
    // same instance, different post-state: an effect contrast
    return a.toKey === b.toKey ? Infinity : 1;
  }
  return differing === 1 ? 1 : Infinity;
}

export function buildPairs<S>(
  cands: StepCand<S>[],
  correct: string,
  configs: string[],
  sizeOf: (s: StepCand<S>) => number,
): PairCand<S>[] {
  const out: PairCand<S>[] = [];
  for (let i = 0; i < cands.length; i++) {
    for (let j = i + 1; j < cands.length; j++) {
      const a = cands[i];
      const b = cands[j];
      const d = contrastDistance(a, b);
      if (d !== 1 && d !== 2) continue;

      // Separation: the joint vector must differ between at least two configs.
      // NOT necessarily involving the correct one - that is what admits the
      // `neither` type, which separates one adding mutant from another.
      const joint = new Map<string, string[]>();
      for (const c of configs) {
        const key = `${a.membership[c] ? 1 : 0}${b.membership[c] ? 1 : 0}`;
        let arr = joint.get(key);
        if (!arr) joint.set(key, (arr = []));
        arr.push(c);
      }
      if (joint.size < 2) continue;

      const targets: string[] = [];
      for (let x = 0; x < configs.length; x++)
        for (let y = x + 1; y < configs.length; y++) {
          const cx = configs[x];
          const cy = configs[y];
          if (a.membership[cx] !== a.membership[cy] || b.membership[cx] !== b.membership[cy])
            targets.push(`${cx}|${cy}`);
        }

      const misconceptions = configs.filter(
        (c) =>
          c !== correct &&
          (a.membership[c] !== a.membership[correct] || b.membership[c] !== b.membership[correct]),
      );

      const ac = a.membership[correct];
      const bc = b.membership[correct];
      const type: PairType = ac && bc ? 'both' : !ac && !bc ? 'neither' : 'one';

      const sameParams = Object.keys(a.params).every(
        (k) => stableStringify(a.params[k]) === stableStringify(b.params[k]),
      );
      out.push({
        a,
        b,
        distance: d as 1 | 2,
        contrast: a.action !== b.action ? 'action' : sameParams ? 'effect' : 'params',
        type,
        targets,
        misconceptions,
        size: Math.max(sizeOf(a), sizeOf(b)),
      });
    }
  }
  return out;
}

export interface SelectOptions<S = unknown> {
  /** target share per pair type (DESIGN.md §6.1) */
  mix: Record<PairType, number>;
  total: number;
  seed: number;
  /** id of the correct config, needed to work out what each pair teaches */
  correct: string;
  /** Optional protocol-specific description of the SHAPE of the situation.
   *  Two questions that turn on the same rule still feel different if one has
   *  an acceptor that already voted and the other does not, so shape joins the
   *  rule in deciding what counts as a repeat. */
  shapeOf?: (p: PairCand<S>) => string;
  /** only pairs that bear on one of these mutants are eligible */
  restrictTo?: string[];
}

/** Greedy selection: fill the type quotas while maximising misconception
 *  coverage, preferring distance 1 and small pre-states. Deterministic given
 *  the seed (§6.2 step 8). */
export function selectPairs<S>(
  pairs: PairCand<S>[],
  opts: SelectOptions<S>,
): PairCand<S>[] {
  const rng = new Rng(opts.seed);
  const quota: Record<PairType, number> = {
    one: Math.round(opts.total * opts.mix.one),
    both: Math.round(opts.total * opts.mix.both),
    neither: Math.round(opts.total * opts.mix.neither),
  };

  const eligible = pairs.filter(
    (p) =>
      p.misconceptions.length > 0 &&
      (!opts.restrictTo || p.misconceptions.some((m) => opts.restrictTo!.includes(m))),
  );

  // Shuffle first so ties break deterministically but without positional bias.
  const pool = rng.shuffle(eligible);
  const coverage = new Map<string, number>();
  /** coverage of CONFIG PAIRS ("P1|P2"), not just individual mutants. */
  const sepCoverage = new Map<string, number>();
  /** coverage of LESSONS: which rule each side turns on. */
  const lessonCoverage = new Map<string, number>();
  /** coverage of SHAPES: what kind of situation the question is set in. */
  const shapeCoverage = new Map<string, number>();
  const chosen: PairCand<S>[] = [];
  const usedFrom = new Map<string, number>();

  /** What a question actually teaches: for each side, the action and either
   *  "legal" or the rule it breaks.
   *
   *  Diagnostic coverage and pedagogical variety are different things, and
   *  optimising only the first produces a bank that is formally excellent and
   *  deadly dull. Measured on the first release: 24 phase-1 questions carried
   *  7 distinct lessons, one of them repeated 10 times, and readers noticed
   *  immediately that the questions "all feel the same". Symmetry dedup does
   *  not help - it removes exact relabelings, while these were genuinely
   *  different states telling an identical story. */
  const lessonOf = (p: PairCand<S>) => {
    const side = (c: StepCand<S>) =>
      `${c.action}:${c.membership[opts.correct] ? 'legal' : c.failed[opts.correct]}`;
    return [side(p.a), side(p.b)].sort().join('|') + '#' + p.type;
  };

  const inScope = (m: string) => !opts.restrictTo || opts.restrictTo.includes(m);
  const relevantTargets = (p: PairCand<S>) =>
    p.targets.filter((t) => {
      const [x, y] = t.split('|');
      return (inScope(x) || x === 'C') && (inScope(y) || y === 'C');
    });

  const score = (p: PairCand<S>) => {
    // Count coverage only over the mutants this level is actually targeting.
    // Counting all of them lets a pair that happens to touch four off-level
    // mutants outrank the only pair in the bank that tests a rare one.
    const relevant = opts.restrictTo
      ? p.misconceptions.filter((m) => opts.restrictTo!.includes(m))
      : p.misconceptions;
    const novel = relevant.reduce((acc, m) => acc + 1 / (1 + (coverage.get(m) ?? 0)), 0);

    // Separating a mutant from PAXOS is not enough. If every question that
    // distinguishes P1 also distinguishes P2 in the same direction, the bank
    // can tell you a misconception is present but not WHICH, and the results
    // screen will confidently name both. Reward pairs that split two mutants
    // from each other - that is the whole job of the `neither` type.
    const sep = relevantTargets(p).reduce((acc, t) => {
      const [x, y] = t.split('|');
      if (x === 'C' || y === 'C') return acc; // mutant-vs-Paxos, already counted
      return acc + 1 / (1 + (sepCoverage.get(t) ?? 0));
    }, 0);

    // Variety, as TWO independent terms. Folding shape into the lesson
    // signature does not work: a pair then earns full credit for a novel
    // shape while repeating a lesson for the eighth time, and lesson variety
    // collapses. They have to compete separately.
    const freshLesson = 1 / (1 + (lessonCoverage.get(lessonOf(p)) ?? 0));
    const freshShape = opts.shapeOf
      ? 1 / (1 + (shapeCoverage.get(opts.shapeOf(p)) ?? 0))
      : 0;

    const reuse = usedFrom.get(p.a.fromKey) ?? 0;
    return (
      novel * 6 +
      sep * 10 +
      freshLesson * 11 +
      freshShape * 5 -
      p.size * 0.25 -
      (p.distance - 1) * 2 -
      reuse * 1.5
    );
  };

  for (const t of ['one', 'both', 'neither'] as PairType[]) {
    const bucket = pool.filter((p) => p.type === t);
    for (let n = 0; n < quota[t]; n++) {
      let best: PairCand<S> | null = null;
      let bestScore = -Infinity;
      for (const p of bucket) {
        if (chosen.includes(p)) continue;
        const sc = score(p);
        if (sc > bestScore) {
          bestScore = sc;
          best = p;
        }
      }
      if (!best) break;
      chosen.push(best);
      usedFrom.set(best.a.fromKey, (usedFrom.get(best.a.fromKey) ?? 0) + 1);
      for (const m of best.misconceptions) coverage.set(m, (coverage.get(m) ?? 0) + 1);
      for (const t of relevantTargets(best)) sepCoverage.set(t, (sepCoverage.get(t) ?? 0) + 1);
      const ls = lessonOf(best);
      lessonCoverage.set(ls, (lessonCoverage.get(ls) ?? 0) + 1);
      if (opts.shapeOf) {
        const sh = opts.shapeOf(best);
        shapeCoverage.set(sh, (shapeCoverage.get(sh) ?? 0) + 1);
      }
    }
  }
  return chosen;
}

export { leafDistance };
