/** The anchored level: is the outcome already decided?
 *
 *  This is the question DESIGN.md §6.1 called the most valuable one in the
 *  whole app, and the first release shipped `chosen` instead because `chosen`
 *  was a cheap predicate and this needed a reachability fixpoint. That was the
 *  wrong trade. Asking "has a majority voted for this inside one ballot" is
 *  bookkeeping: the answer is almost always no, and knowing it teaches nothing.
 *
 *  The idea that actually matters is ANCHORING. Long before any value is
 *  chosen — before anybody could possibly observe a decision — the outcome can
 *  already be sealed, because every majority that could still form overlaps
 *  with acceptors that will force a future proposer's hand. The fate is decided
 *  in advance and nobody knows it yet. That is the thing worth testing.
 *
 *  So: given a situation in which NOTHING has been chosen, which values could
 *  still end up being chosen? "Only Alice" means Alice is anchored.
 */

import {
  Rng,
  type Bank,
  type Question,
  type Scenario,
  type Value,
} from '@dyp/engine';
import { accName, defaultConstants, paxos, qName, type PaxosState } from '@dyp/models';

/* ------------------------------------------------------------------ */
/* An integer-indexed reachability graph.
 *
 * The engine's `bfs` keeps full Transition objects with parameters, which is
 * what the step levels need and what makes 185k states too heavy to hold.
 * Here only the shape of the graph matters, so states are interned to integers
 * and edges are arrays of ints. */

export interface ReachIndex {
  key: string[];
  state: PaxosState[];
  succ: number[][];
  idOf: Map<string, number>;
  initial: number[];
}

export function buildIndex(
  model: ReturnType<typeof paxos>,
  maxStates = 1_000_000,
  maxDepth = Infinity,
): ReachIndex {
  const idOf = new Map<string, number>();
  const key: string[] = [];
  const state: PaxosState[] = [];
  const succ: number[][] = [];
  const initial: number[] = [];

  const intern = (s: PaxosState): number => {
    const k = model.key(s);
    let i = idOf.get(k);
    if (i === undefined) {
      i = key.length;
      idOf.set(k, i);
      key.push(k);
      state.push(s);
      succ.push([]);
    }
    return i;
  };

  /* The worklist is `key` itself, which is appended to in discovery order, so
   * this is breadth-first and a parallel depth array is enough to bound it. */
  const depth: number[] = [];
  for (const s0 of model.init()) {
    const i = intern(s0);
    depth[i] = 0;
    initial.push(i);
  }

  for (let i = 0; i < key.length; i++) {
    if (key.length > maxStates) throw new Error('state space larger than expected');
    if (depth[i] >= maxDepth) continue;
    const out: number[] = [];
    for (const inst of model.successors(state[i])) {
      const j = intern(inst.next);
      if (depth[j] === undefined) depth[j] = depth[i] + 1;
      out.push(j);
    }
    succ[i] = out;
  }
  return { key, state, succ, idOf, initial };
}

/** Every state from which some state satisfying `goal` is reachable.
 *  Least fixpoint, computed by one reverse pass over the edge list. */
export function canReach(g: ReachIndex, goal: (s: PaxosState) => boolean): Uint8Array {
  const n = g.key.length;
  const pred: number[][] = Array.from({ length: n }, () => []);
  for (let i = 0; i < n; i++) for (const j of g.succ[i]) pred[j].push(i);

  const mark = new Uint8Array(n);
  const stack: number[] = [];
  for (let i = 0; i < n; i++)
    if (goal(g.state[i])) {
      mark[i] = 1;
      stack.push(i);
    }
  while (stack.length) {
    const i = stack.pop()!;
    for (const p of pred[i])
      if (!mark[p]) {
        mark[p] = 1;
        stack.push(p);
      }
  }
  return mark;
}

/** Shortest sequence of states from `from` to any state satisfying `goal`,
 *  as a witness for "yes, this could still happen". */
export function witnessTo(
  g: ReachIndex,
  from: number,
  goal: (s: PaxosState) => boolean,
): PaxosState[] | null {
  const prev = new Map<number, number>();
  const seen = new Set<number>([from]);
  const queue = [from];
  let head = 0;
  while (head < queue.length) {
    const i = queue[head++];
    if (goal(g.state[i])) {
      const path: PaxosState[] = [];
      let c: number | undefined = i;
      while (c !== undefined) {
        path.unshift(g.state[c]);
        c = prev.get(c);
      }
      return path;
    }
    for (const j of g.succ[i])
      if (!seen.has(j)) {
        seen.add(j);
        prev.set(j, i);
        queue.push(j);
      }
  }
  return null;
}

/* ------------------------------------------------------------------ */
/* Competing theories of "what can still happen".
 *
 * As with the definitions of "chosen", a learner holds exactly ONE theory of
 * what is still possible, so these are mutually exclusive candidates and the
 * level is scored categorically (DESIGN.md §7.2). */

export const THEORIES = ['C', 'T1', 'T2', 'T3', 'T4'] as const;

export function theoryAnswer(
  theory: string,
  s: PaxosState,
  values: string[],
  quorums: number[][],
  truth: [boolean, boolean],
): [boolean, boolean] {
  const votedFor = (v: string) => s.msgs.some((m) => m.t === '2b' && m.val === v);
  const topBallot = Math.max(...s.maxVBal);

  switch (theory) {
    case 'C':
      return truth;

    /* "Nothing is settled until it is chosen." The naive view, and the one
     * this level exists to break: anything that has not happened yet is
     * assumed to be still possible. */
    case 'T1':
      return [true, true];

    /* "Whoever has the highest vote wins" — right instinct about recency,
     * no notion of a majority having to agree. */
    case 'T2': {
      if (topBallot < 0) return [true, true];
      return values.map((v) =>
        s.maxVBal.some((b, a) => b === topBallot && s.maxVal[a] === v),
      ) as [boolean, boolean];
    }

    /* "The first vote locks it in" — treats a single acceptor's vote as a
     * commitment rather than as evidence. */
    case 'T3': {
      const any = values.filter(votedFor);
      if (any.length === 0) return [true, true];
      return values.map((v) => any.includes(v)) as [boolean, boolean];
    }

    /* "A majority currently holding it locks it in" — reads the present
     * snapshot rather than what any future majority would be forced to say. */
    case 'T4': {
      const held = values.filter((v) => quorums.some((q) => q.every((a) => s.maxVal[a] === v)));
      if (held.length === 0) return [true, true];
      return values.map((v) => held.includes(v)) as [boolean, boolean];
    }
  }
  throw new Error(`unknown theory ${theory}`);
}

/* ------------------------------------------------------------------ */

export interface AnchoredResult {
  bank: Bank;
  report: string[];
}

/** Ballot numbering for one run.
 *
 *  Paxos only ever compares ballot numbers, so a set like {0, 2} is a
 *  perfectly ordinary reachable world with a gap in it — and the first release
 *  could never show one, because holding the top ballot in reserve for the
 *  bound-safety argument forced every situation into {0, 1}. The soundness
 *  trick had quietly deleted an entire class of scenario, which readers
 *  noticed as "the ballots are always consecutive".
 *
 *  `situation` is the world the shown state lives in; `answer` adds the
 *  reserve ballot the reachability fixpoint runs in; `check` adds a second
 *  reserve for the bound-stability re-derivation. */
export interface BallotPlan {
  situation: number[];
  answer: number[];
  check: number[];
  depth: number;
  label: string;
}

export const BALLOT_PLANS: BallotPlan[] = [
  /* Depth 17 is where the interesting situations live. A value being accepted
   * and then overwritten on the same acceptor takes ten steps to set up, and
   * the trap where a majority accepted a value at some point without holding
   * it needs fifteen. The old depth-14 bound could not reach either. */
  /* `answer` MUST hold a ballot above everything `situation` can use, or the
   * forward search has no fresh ballot to open and reports that nothing more
   * can be chosen — which is an artifact, and which the stability check then
   * turns into silently dropping every deep situation. */
  { situation: [0, 1, 2], answer: [0, 1, 2, 3], check: [0, 1, 2, 3, 4], depth: 17, label: 'three ballots' },
  { situation: [0, 2, 3], answer: [0, 2, 3, 4], check: [0, 2, 3, 4, 5], depth: 17, label: 'ballot gap' },
];

export function buildAnchoredBank(seed: number, plan: BallotPlan): AnchoredResult {
  const report: string[] = [];

  /* Situations come from a deeper world than the first version allowed.
   *
   * That version drew them from a two-ballot model so a spare ballot was
   * always in reserve for the reachability fixpoint, and every sealed
   * situation came out the same shape: two acceptors holding the same value in
   * two different ballots. You could answer by glancing for a matching pair,
   * which is a majority check rather than reasoning about the protocol.
   *
   * The cases worth showing are deeper. One acceptor accepting Alice and later
   * Bob, so its history and its current value disagree, takes ten steps to set
   * up. The trap where a majority accepted a value at SOME point but one of
   * them has since overwritten it — so the value is NOT sealed — takes fifteen.
   *
   * The answer for a deep situation cannot come from a global fixpoint, since
   * that needs a reserve ballot and the four-ballot graph does not fit. It is
   * computed per situation instead, by forward search in a model that has the
   * reserve, which is cheap because the search stops as soon as both values
   * have been seen chosen. */
  const KS = defaultConstants(plan.situation);
  const KA = defaultConstants(plan.answer);
  const KC = defaultConstants(plan.check);
  const mS = paxos(KS);
  const mA = paxos(KA);
  const mC = paxos(KC);
  const values = KS.values;

  const VISIT_CAP = 120_000;

  /** Which values can still be chosen from `s`, by forward search in a model
   *  that holds a ballot in reserve above anything the situation uses. */
  function choosableFrom(
    model: ReturnType<typeof paxos>,
    s0: PaxosState,
    maxDepth: number,
  ): Set<string> | null {
    const found = new Set<string>();
    const seen = new Set<string>([model.key(s0)]);
    let frontier = [s0];
    for (let d = 0; d <= maxDepth && found.size < values.length; d++) {
      const next: PaxosState[] = [];
      for (const st of frontier) {
        for (const v of values) if (model.predicates[`C0:${v}`](st)) found.add(v);
        if (found.size === values.length) return found;
        for (const inst of model.successors(st)) {
          const k = model.key(inst.next);
          if (seen.has(k)) continue;
          if (seen.size > VISIT_CAP) return null; // too expensive; skip this situation
          seen.add(k);
          next.push(inst.next);
        }
      }
      frontier = next;
      if (!frontier.length) break;
    }
    return found;
  }

  let t = Date.now();
  const gS = buildIndex(mS, 400_000, plan.depth);
  report.push(
    `  [${plan.label}] situations in {${plan.situation}} to depth ${plan.depth}: ` +
      `${gS.key.length} states (${Date.now() - t}ms)`,
  );

  const nothingChosen = (s: PaxosState) => !values.some((v) => mS.predicates[`C0:${v}`](s));

  /* ---- candidate situations --------------------------------------- */
  /* Ranked so the structurally interesting ones are verified first: an
   * acceptor whose history holds a value it no longer holds, and a value a
   * majority accepted at some point without a majority still holding it. Both
   * are the cases a reader asked for and neither existed before. */
  const overwrote = (s: PaxosState) =>
    s.maxVal.some(
      (v, a) => v !== null && s.msgs.some((m) => m.t === '2b' && m.acc === a && m.val !== v),
    );
  const staleMajority = (s: PaxosState) =>
    values.some(
      (v) =>
        KS.quorums.some((q) => q.every((a) => s.msgs.some((m) => m.t === '2b' && m.acc === a && m.val === v))) &&
        !KS.quorums.some((q) => q.every((a) => s.maxVal[a] === v)),
    );

  const rng = new Rng(seed);
  const seen = new Set<string>();
  const pool: PaxosState[] = [];
  for (const s of rng.shuffle(gS.state)) {
    if (!nothingChosen(s)) continue; // the interesting case is before anyone knows
    if (s.msgs.length < 3) continue;
    const rep = mS.symmetry!.orbit(s).map((x) => mS.key(x)).sort()[0];
    if (seen.has(rep)) continue;
    seen.add(rep);
    pool.push(s);
  }
  /* Verification order: the richest situations first, then a shuffled mix of
   * everything else.
   *
   * Sorting the WHOLE pool by richness is a trap. It makes every verified
   * situation deep and elaborate, and on those "nothing is settled until it is
   * chosen" and "the first acceptance locks it in" give identical answers —
   * both values have been accepted by somebody — so the two theories collapse
   * into one candidate and the level can no longer tell them apart. The simple
   * situations are what separates them. */
  const score = (s: PaxosState) => (staleMajority(s) ? 2 : 0) + (overwrote(s) ? 1 : 0);
  const rich = pool.filter((s) => score(s) > 0).sort((x, y) => score(y) - score(x));
  const plain = pool.filter((s) => score(s) === 0);
  const order = [...rich.slice(0, 70), ...rng.shuffle([...plain, ...rich.slice(70)])];
  pool.length = 0;
  pool.push(...order);

  interface Cand {
    s: PaxosState;
    truth: [boolean, boolean];
  }
  const cands: Cand[] = [];
  let skipped = 0;
  let unstable = 0;
  t = Date.now();
  for (const s of pool) {
    if (cands.length >= 170) break;
    const near = choosableFrom(mA, s, 12);
    if (!near) {
      skipped++;
      continue;
    }
    /* Bound stability, per situation: a deeper search with one MORE spare
     * ballot must give the same answer, or the number we would ship is an
     * artifact of how far we happened to look. */
    const far = choosableFrom(mC, s, 15);
    if (!far) {
      skipped++;
      continue;
    }
    if (near.size !== far.size || [...near].some((v) => !far.has(v))) {
      unstable++;
      continue;
    }
    cands.push({ s, truth: [near.has(values[0]), near.has(values[1])] });
  }
  /* Targeted top-up. The general pass is driven by richness and chance, so a
   * theory whose separating situations are rare ends up with three or four
   * questions and cannot be identified. Scan specifically for each one, the
   * same way the step levels rescue the subtle mutants. */
  {
    const have = new Set(cands.map((c) => mS.key(c.s)));
    for (const d of THEORIES.filter((x) => x !== 'C')) {
      const count = () =>
        cands.filter((c) => {
          const a = theoryAnswer(d, c.s, values, KS.quorums, c.truth);
          return a[0] !== c.truth[0] || a[1] !== c.truth[1];
        }).length;
      let n = count();
      if (n >= 12) continue;
      let tried = 0;
      for (const s of pool) {
        if (n >= 12 || tried > 120) break;
        if (have.has(mS.key(s))) continue;
        tried++;
        const near = choosableFrom(mA, s, 12);
        if (!near) continue;
        const far = choosableFrom(mC, s, 15);
        if (!far) continue;
        if (near.size !== far.size || [...near].some((v) => !far.has(v))) continue;
        const truth: [boolean, boolean] = [near.has(values[0]), near.has(values[1])];
        const a = theoryAnswer(d, s, values, KS.quorums, truth);
        if (a[0] === truth[0] && a[1] === truth[1]) continue; // does not separate d
        cands.push({ s, truth });
        have.add(mS.key(s));
        n++;
      }
      report.push(`  targeted top-up for ${d}: ${n} separating situations`);
    }
  }

  report.push(
    `  verified ${cands.length} situations by forward search ` +
      `(${skipped} too costly, ${unstable} bound-unstable) in ${Date.now() - t}ms`,
  );
  report.push(
    `  of those: ${cands.filter((c) => overwrote(c.s)).length} have an acceptor that overwrote an ` +
      `earlier value, ${cands.filter((c) => staleMajority(c.s)).length} have a majority that accepted ` +
      `a value without still holding it`,
  );

  /* ---- verification: the answer is monotone ----------------------- */
  /* A value that can no longer be chosen never becomes possible again. This is
   * a property of Paxos rather than of how the answer was computed, so it is an
   * independent check on the search. An earlier attempt to replace the search
   * with a closed-form snapshot formula was killed by exactly this test: the
   * formula missed that an acceptor can still take an OLD pending proposal,
   * which brings a value back from the dead. */
  {
    /* Successors are not generally among the verified set, so their answers are
     * computed here on a sample rather than looked up. */
    const idxOf = new Map(gS.key.map((k, i) => [k, i]));
    let violations = 0;
    let compared = 0;
    for (const c of rng.shuffle(cands).slice(0, 120)) {
      const i = idxOf.get(mS.key(c.s));
      if (i === undefined) continue;
      for (const j of gS.succ[i]) {
        const after = choosableFrom(mA, gS.state[j], 12);
        if (!after) continue;
        compared++;
        for (let v = 0; v < values.length; v++)
          if (!c.truth[v] && after.has(values[v])) violations++;
      }
    }
    if (violations > 0)
      throw new Error(`answers are not monotone across ${violations} edges — the search is wrong`);
    report.push(`  monotonicity: holds on ${compared} sampled situation/successor edges`);
  }

  /* Collapse theories that agree with each other, or with the truth, on every
   * situation this level could ever show. PICK does this before generating
   * scenarios (paper §2.3) and it matters here for the same reason it did for
   * the definitions of "chosen": a candidate that no question can distinguish
   * must not be reported as a separate finding. */
  const sig = new Map<string, string[]>();
  for (const d of THEORIES) {
    let bits = '';
    for (const c of cands) {
      const a = theoryAnswer(d, c.s, values, KS.quorums, c.truth);
      bits += (a[0] ? '1' : '0') + (a[1] ? '1' : '0');
    }
    const g = sig.get(bits);
    if (g) g.push(d);
    else sig.set(bits, [d]);
  }
  const live: string[] = [];
  for (const group of sig.values()) {
    if (group.includes('C')) {
      // indistinguishable from the truth: it is not a misconception here at all
      for (const d of group) if (d !== 'C') report.push(`  ${d} agrees with the truth on every situation — dropped`);
      live.push('C');
    } else {
      if (group.length > 1) report.push(`  ${group.join(' and ')} are indistinguishable — merged`);
      live.push(group.join('+'));
    }
  }
  const memberOf = (id: string) => id.split('+')[0];
  const answerOf = (id: string, c: Cand) =>
    theoryAnswer(memberOf(id), c.s, values, KS.quorums, c.truth);

  for (const d of live.filter((x) => x !== 'C')) {
    let one = 0;
    let both = 0;
    for (const c of cands) {
      const a = answerOf(d, c);
      if (a[0] === c.truth[0] && a[1] === c.truth[1]) continue;
      if (c.truth[0] !== c.truth[1]) one++;
      else both++;
    }
    report.push(`  ${d} separable on ${one + both} situations (${one} sealed, ${both} open)`);
  }

  for (let i = 0; i < live.length; i++)
    for (let j = i + 1; j < live.length; j++) {
      const [x, y] = [live[i], live[j]];
      const n = cands.filter((c) => {
        const a = answerOf(x, c);
        const b = answerOf(y, c);
        return a[0] !== b[0] || a[1] !== b[1];
      }).length;
      report.push(`  ${x} vs ${y}: separable on ${n} situations`);
    }

  const anchoredCount = cands.filter((c) => c.truth[0] !== c.truth[1]).length;
  report.push(
    `  situations with nothing chosen yet: ${cands.length}; ` +
      `already sealed on one value: ${anchoredCount} (${((100 * anchoredCount) / cands.length).toFixed(0)}%)`,
  );
  if (anchoredCount === 0)
    throw new Error('no anchored situations found — the level would teach nothing');

  /* ---- justifications --------------------------------------------- */
  const explainYes = (c: Cand, vi: number): string => {
    /* Name the majority that keeps it alive. That is the whole reasoning:
     * a proposer that happens to ask these acceptors is free to propose it,
     * or is forced to. */
    const v = values[vi];
    const open = KS.quorums.find((q) => {
      let top = -1;
      let val: string | null = null;
      for (const a of q)
        if (c.s.maxVBal[a] > top) {
          top = c.s.maxVBal[a];
          val = c.s.maxVal[a];
        }
      return top < 0 || val === v;
    });
    if (!open) return `Yes. ${v} can still be chosen.`;
    const silent = open.every((a) => c.s.maxVBal[a] < 0);
    return silent
      ? `Yes. A proposer that opens a new ballot and hears from ${qName(open)} learns nothing ` +
          `about any earlier acceptance, so it is free to propose ${v}, and they can accept it.`
      : `Yes. A proposer that opens a new ballot and hears from ${qName(open)} would see ${v} as ` +
          `the highest acceptance among them, so it would have to propose ${v}, and they can accept it.`;
  };

  const explainNo = (c: Cand, vi: number): string => {
    const other = values[1 - vi];
    const top = Math.max(...c.s.maxVBal);
    const holders = c.s.maxVBal
      .map((b, a) => (b === top && c.s.maxVal[a] === other ? a : -1))
      .filter((a) => a >= 0);
    const majorityBlocked = holders.length * 2 > c.s.maxBal.length;
    const because = majorityBlocked
      ? `${holders.map(accName).join(' and ')} have both already accepted ${other} at the highest ` +
        `ballot anyone has reached. Any future proposer needs a majority, every majority overlaps ` +
        `with those two, so it will hear about ${other} and have to propose it.`
      : `Every majority a future proposer could gather would report ${other} as the highest acceptance it ` +
        `has seen, which forces that proposer to propose ${other} rather than ${values[vi]}.`;
    return (
      `No. ${values[vi]} can no longer be chosen, whatever happens from here. ${because} ` +
      `Nothing has been chosen yet, and no acceptor in this situation knows that, ` +
      `but it is already decided.`
    );
  };

  /* ---- selection --------------------------------------------------- */
  /* "Neither" is never the answer: with a spare ballot something can always
   * still be chosen. The types available are therefore `one` (sealed) and
   * `both` (genuinely open), and the mix has to keep a constant answer below
   * chance. */
  const byType = { one: [] as Cand[], both: [] as Cand[] };
  for (const c of rng.shuffle(cands)) (c.truth[0] !== c.truth[1] ? byType.one : byType.both).push(c);

  /* `both` must stay under 40% or "they are all still possible" - which is
   * precisely the misconception this level exists to break - scores well by
   * doing nothing. Sized against however many sealed situations exist. */
  /* Use every sealed situation there is - they are the scarce, valuable ones -
   * and match them with an equal number of open ones. "Always both" scoring
   * around half is fine here: that answer is the T1 misconception itself, and
   * the level is built to catch it. */
  /* Capped. The pool is now large enough that taking all of it would ship
   * hundreds of questions for a level that shows fourteen. */
  const quota = { one: Math.min(24, byType.one.length), both: Math.min(16, byType.both.length) };
  const coverage = new Map<string, number>();
  const sepCoverage = new Map<string, number>();
  const mis = (c: Cand) =>
    live.filter((d) => {
      if (d === 'C') return false;
      const a = answerOf(d, c);
      return a[0] !== c.truth[0] || a[1] !== c.truth[1];
    });
  const seps = (c: Cand) => {
    const out: string[] = [];
    const ans = Object.fromEntries(live.map((d) => [d, answerOf(d, c)]));
    for (let i = 0; i < live.length; i++)
      for (let j = i + 1; j < live.length; j++) {
        const [x, y] = [live[i], live[j]];
        if (x === 'C' || y === 'C') continue;
        if (ans[x][0] !== ans[y][0] || ans[x][1] !== ans[y][1]) out.push(`${x}|${y}`);
      }
    return out;
  };

  /* Shape, so the sealed situations are not sixteen retellings of one story.
   * The first release shipped exactly that: every sealed case was two
   * proposals of the same value, voted by two acceptors in two ballots, with
   * only the names changed. */
  const shapeCoverage = new Map<string, number>();
  const shapeOf = (c: Cand) => {
    const votes = c.s.msgs.filter((m) => m.t === '2b');
    const props = c.s.msgs.filter((m) => m.t === '2a');
    const vb = new Set(votes.map((m) => m.bal));
    const pv = new Set(props.map((m) => ('val' in m ? m.val : '')));
    /* The two features a reader asked for have to be IN the shape, or the
     * selector diversifies along axes that do not matter and ships none of
     * them: they were present among the verified situations and simply never
     * picked. */
    return (
      `n${votes.length}/b${vb.size}/p${props.length}/v${pv.size}` +
      `${overwrote(c.s) ? '/ow' : ''}${staleMajority(c.s) ? '/stale' : ''}`
    );
  };

  const picked: Cand[] = [];
  const take = (c: Cand) => {
    picked.push(c);
    for (const d of mis(c)) coverage.set(d, (coverage.get(d) ?? 0) + 1);
    for (const sp of seps(c)) sepCoverage.set(sp, (sepCoverage.get(sp) ?? 0) + 1);
    const sh = shapeOf(c);
    shapeCoverage.set(sh, (shapeCoverage.get(sh) ?? 0) + 1);
  };

  // floor per theory, so a rare one cannot be squeezed out by greedy scoring
  for (const d of live.filter((x) => x !== 'C')) {
    const pool = rng.shuffle(cands.filter((c) => mis(c).includes(d)));
    let n = picked.filter((c) => mis(c).includes(d)).length;
    for (const c of pool) {
      if (n >= 12) break;
      if (picked.includes(c)) continue;
      take(c);
      n++;
    }
  }

  /* A floor on each PAIR of theories, not just on each theory alone.
   * "Whoever has the highest vote wins" and "the first vote locks it in" agree
   * on 165 of 179 situations - they only come apart when both values have been
   * voted for somewhere. Without reserving those few, the posterior splits
   * between the two and neither is ever reported, so a learner holding one of
   * them is told nothing. */
  for (let i = 0; i < live.length; i++)
    for (let j = i + 1; j < live.length; j++) {
      const [x, y] = [live[i], live[j]];
      if (x === 'C' || y === 'C') continue;
      const pool = rng.shuffle(
        cands.filter((c) => {
          const a = answerOf(x, c);
          const b = answerOf(y, c);
          return a[0] !== b[0] || a[1] !== b[1];
        }),
      );
      let n = picked.filter((c) => seps(c).includes(`${x}|${y}`)).length;
      for (const c of pool) {
        if (n >= 8) break;
        if (picked.includes(c)) continue;
        take(c);
        n++;
      }
    }

  /* Floors on the two families, so they cannot be squeezed out by scoring. */
  for (const [label, test, want] of [
    ['overwrite', overwrote, 10],
    ['stale majority', staleMajority, 8],
  ] as [string, (s: PaxosState) => boolean, number][]) {
    const avail = rng.shuffle(cands.filter((c) => test(c.s)));
    let n = picked.filter((c) => test(c.s)).length;
    for (const c of avail) {
      if (n >= want) break;
      if (picked.includes(c)) continue;
      if (!mis(c).length) continue;
      take(c);
      n++;
    }
    report.push(`  floor on ${label}: ${n} in the bank (${avail.length} available)`);
  }

  for (const type of ['one', 'both'] as const) {
    const already = picked.filter(
      (c) => (c.truth[0] !== c.truth[1] ? 'one' : 'both') === type,
    ).length;
    for (let n = already; n < quota[type]; n++) {
      let best: Cand | null = null;
      let bestScore = -Infinity;
      for (const c of byType[type]) {
        if (picked.includes(c)) continue;
        const ms = mis(c);
        if (!ms.length) continue;
        const novel = ms.reduce((a, d) => a + 1 / (1 + (coverage.get(d) ?? 0)), 0);
        const sep = seps(c).reduce((a, sp) => a + 1 / (1 + (sepCoverage.get(sp) ?? 0)), 0);
        const freshShape = 1 / (1 + (shapeCoverage.get(shapeOf(c)) ?? 0));
        const score = novel * 4 + sep * 5 + freshShape * 9 - c.s.msgs.length * 0.3;
        if (score > bestScore) {
          bestScore = score;
          best = c;
        }
      }
      if (!best) break;
      take(best);
    }
  }

  /* ---- questions --------------------------------------------------- */
  /* Alternate sides WITHIN each type. Alternating on the raw index leaves the
   * sealed questions clumped, and the clumps all land on the same side —
   * "always answer B" was scoring 41% until this was fixed. */
  const flips = { one: 0, both: 0 };
  const questions: Question[] = picked.map((c, i): Question => {
    const ty = c.truth[0] !== c.truth[1] ? 'one' : 'both';
    const flip = flips[ty]++ % 2 === 1;
    const slot = (n: number) => (flip ? 1 - n : n);
    const answer: Record<string, [boolean, boolean]> = {};
    for (const d of live) {
      const a = answerOf(d, c);
      answer[d] = flip ? [a[1], a[0]] : a;
    }
    const mk = (n: number): Scenario => {
      const v = slot(n);
      return {
        payload: { kind: 'state', state: c.s as unknown as Value, subject: values[v] },
        justification: {
          verdict: c.truth[v] ? 'legal' : 'illegal',
          refs: [],
          text: c.truth[v] ? explainYes(c, v) : explainNo(c, v),
        },
      };
    };
    const [ax, bx] = answer['C'];
    return {
      id: `paxos-anchored-${String(i).padStart(3, '0')}`,
      kind: 'future',
      type: ax && bx ? 'both' : !ax && !bx ? 'neither' : 'one',
      a: mk(0),
      b: mk(1),
      distance: 1,
      answer,
      targets: [],
      misconceptions: live.filter(
        (d) => d !== 'C' && (answer[d][0] !== answer['C'][0] || answer[d][1] !== answer['C'][1]),
      ),
      size: c.s.msgs.length,
      subject: `${values[slot(0)]}/${values[slot(1)]}`,
      boundStable: true,
    };
  });

  const mix = { one: 0, both: 0, neither: 0 };
  for (const q of questions) mix[q.type]++;
  const cover = new Map<string, number>();
  for (const q of questions) for (const d of q.misconceptions) cover.set(d, (cover.get(d) ?? 0) + 1);
  report.push(
    `  questions ${questions.length}, mix ${mix.one}/${mix.both}/${mix.neither}  ` +
      `[${live.filter((d) => d !== 'C').map((d) => `${d}:${cover.get(d) ?? 0}`).join(' ')}]`,
  );

  const bank: Bank = {
    protocol: 'paxos',
    level: 'paxos-anchored',
    title: 'Is it already decided?',
    blurb:
      'Nothing has been chosen yet in any of these situations. That does not mean anything is ' +
      'still possible — in Paxos the outcome can be sealed long before anyone could know it. ' +
      'Which of these values could still end up being chosen?',
    generatedFrom: {
      modelVersion: '0.2.0',
      constants: KS as unknown as Record<string, Value>,
      configs: live,
      seed,
    },
    configs: live,
    exclusive: true,
    questions,
    mix,
  };
  return { bank, report };
}
