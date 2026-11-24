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
import { accName, defaultConstants, paxos, type PaxosState } from '@dyp/models';

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

  for (const s0 of model.init()) initial.push(intern(s0));

  for (let i = 0; i < key.length; i++) {
    if (key.length > maxStates) throw new Error('state space larger than expected');
    const out: number[] = [];
    for (const inst of model.successors(state[i])) out.push(intern(inst.next));
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
  label: string;
}

export const BALLOT_PLANS: BallotPlan[] = [
  { situation: [0, 1], answer: [0, 1, 2], check: [0, 1, 2, 3], label: 'consecutive ballots' },
  { situation: [0, 2], answer: [0, 2, 3], check: [0, 2, 3, 4], label: 'ballot gap' },
];

export function buildAnchoredBank(seed: number, plan: BallotPlan): AnchoredResult {
  const report: string[] = [];

  /* Situations are drawn from the two-ballot world, so every one of them has
   * at least one entirely unused ballot available for the future. The
   * reachability answer is then computed in the three-ballot world: one spare
   * ballot is all it takes to get an anchored value chosen (open it, collect a
   * majority of promises, propose what you are forced to propose, collect the
   * votes), and the stability check below confirms a second spare changes
   * nothing. */
  const K2 = defaultConstants(plan.situation);
  const K3 = defaultConstants(plan.answer);
  const K4 = defaultConstants(plan.check);
  const m2 = paxos(K2);
  const m3 = paxos(K3);
  const values = K3.values;

  let t = Date.now();
  const g3 = buildIndex(m3);
  report.push(
    `  [${plan.label}] situations in {${plan.situation}}, answers in {${plan.answer}}: ` +
      `${g3.key.length} states (${Date.now() - t}ms)`,
  );

  const chosen = (v: string) => (s: PaxosState) => m3.predicates[`C0:${v}`](s);
  const reachMarks = values.map((v) => canReach(g3, chosen(v)));
  const nothingChosen = (s: PaxosState) => !values.some((v) => m3.predicates[`C0:${v}`](s));

  /* ---- verification 1: anchoring is monotone ---------------------- */
  /* Whatever can no longer be chosen can never become possible again. This is
   * a property of Paxos, not of how the sets were computed, so it is an
   * independent check on the fixpoint: a bug in the reverse pass would almost
   * certainly break it. */
  {
    let violations = 0;
    for (let i = 0; i < g3.key.length; i++)
      for (const j of g3.succ[i])
        for (let v = 0; v < values.length; v++)
          if (!reachMarks[v][i] && reachMarks[v][j]) violations++;
    if (violations > 0)
      throw new Error(`anchoring is not monotone across ${violations} edges — the fixpoint is wrong`);
    report.push('  monotonicity: once a value is ruled out it never returns — holds on every edge');
  }

  /* ---- candidate situations --------------------------------------- */
  const idx2 = buildIndex(m2);
  const rng = new Rng(seed);
  const seen = new Set<string>();
  interface Cand {
    s: PaxosState;
    id3: number;
    truth: [boolean, boolean];
  }
  const cands: Cand[] = [];
  for (const s of rng.shuffle(idx2.state)) {
    if (!nothingChosen(s)) continue; // the interesting case is before anyone knows
    if (s.msgs.length < 3) continue;
    const rep = m3.symmetry!.orbit(s).map((x) => m3.key(x)).sort()[0];
    if (seen.has(rep)) continue;
    seen.add(rep);
    const id3 = g3.idOf.get(m3.key(s));
    if (id3 === undefined) continue;
    cands.push({ s, id3, truth: [!!reachMarks[0][id3], !!reachMarks[1][id3]] });
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
      const a = theoryAnswer(d, c.s, values, K3.quorums, c.truth);
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
    theoryAnswer(memberOf(id), c.s, values, K3.quorums, c.truth);

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

  /* ---- verification 2: one spare ballot is enough ------------------ */
  /* The answer must not depend on how many ballots the model happens to allow
   * (DESIGN.md §6.4). Re-derive it for a sample with a second spare ballot, by
   * bounded forward search, and require agreement. */
  {
    const m4 = paxos(K4);
    const sample = rng.shuffle(cands).slice(0, 40);
    let checked = 0;
    for (const c of sample) {
      const found = [false, false];
      const seenF = new Set<string>([m4.key(c.s)]);
      let frontier = [c.s];
      for (let d = 0; d < 9 && (!found[0] || !found[1]); d++) {
        const next: PaxosState[] = [];
        for (const s of frontier) {
          for (let v = 0; v < values.length; v++)
            if (m4.predicates[`C0:${values[v]}`](s)) found[v] = true;
          if (seenF.size > 60_000) break;
          for (const inst of m4.successors(s)) {
            const k = m4.key(inst.next);
            if (seenF.has(k)) continue;
            seenF.add(k);
            next.push(inst.next);
          }
        }
        frontier = next;
        if (frontier.length === 0) break;
      }
      for (let v = 0; v < values.length; v++)
        if (found[v] !== c.truth[v])
          throw new Error(
            `bound artifact: with a second spare ballot, "${values[v]} can still be chosen" ` +
              `changed from ${c.truth[v]} to ${found[v]}`,
          );
      checked++;
    }
    report.push(`  bound stability: a second spare ballot changes nothing (${checked} situations re-derived)`);
  }

  /* ---- justifications --------------------------------------------- */
  const explainYes = (c: Cand, vi: number): string => {
    const path = witnessTo(g3, c.id3, chosen(values[vi]));
    const steps = path ? path.length - 1 : 0;
    return (
      `Yes. ${values[vi]} can still end up being chosen — it takes ${steps} more step${steps === 1 ? '' : 's'} ` +
      `from here, and nothing in the situation rules it out.`
    );
  };

  const explainNo = (c: Cand, vi: number): string => {
    const other = values[1 - vi];
    const top = Math.max(...c.s.maxVBal);
    const holders = c.s.maxVBal
      .map((b, a) => (b === top && c.s.maxVal[a] === other ? a : -1))
      .filter((a) => a >= 0);
    const majorityBlocked = holders.length * 2 > c.s.maxBal.length;
    const because = majorityBlocked
      ? `${holders.map(accName).join(' and ')} have both already voted for ${other} at the highest ballot ` +
        `anyone has reached. Any future proposer needs a majority, and every majority overlaps with those two, ` +
        `so it will always hear about ${other} and be forced to propose it.`
      : `Every majority a future proposer could gather would report ${other} as the highest vote it ` +
        `has seen, which forces that proposer to propose ${other} rather than ${values[vi]}.`;
    return (
      `No — and this is the point. ${values[vi]} can never be chosen now, in any continuation whatsoever, ` +
      `even though nothing has been chosen yet and no acceptor could tell you so. ${because} ` +
      `The outcome was sealed before anyone could observe it.`
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
  const quota = { one: byType.one.length, both: byType.one.length };
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
    return `n${votes.length}/b${vb.size}/p${props.length}/v${pv.size}`;
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
      if (n >= 10) break;
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
      constants: K3 as unknown as Record<string, Value>,
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
