import { describe, expect, it } from 'vitest';
import {
  bfs,
  buildPairs,
  contrastDistance,
  enumerateSteps,
  leafDistance,
  recompute,
  recomputeCategorical,
  sortSet,
  stableStringify,
  type Model,
  type Question,
} from './index.js';
import {
  ALL_CONFIGS,
  CORRECT,
  MUTANTS,
  defaultConstants,
  flagsFor,
  paxos,
  type PaxosState,
} from '@dyp/models';

const K = defaultConstants([0, 1]);
const models: Record<string, Model<PaxosState>> = {};
for (const c of ALL_CONFIGS) models[c] = paxos(K, flagsFor(c));

describe('canonicalization', () => {
  it('is independent of object key order', () => {
    expect(stableStringify({ a: 1, b: 2 })).toBe(stableStringify({ b: 2, a: 1 }));
  });

  it('sorts sets into a canonical order', () => {
    expect(sortSet([3, 1, 2])).toEqual(sortSet([2, 3, 1]));
  });

  it('counts differing leaves', () => {
    expect(leafDistance({ a: 1, b: 2 }, { a: 1, b: 3 })).toBe(1);
    expect(leafDistance({ a: 1, b: 2 }, { a: 9, b: 3 })).toBe(2);
  });

  it('gives the same state key regardless of the order messages were sent', () => {
    const m = models[CORRECT];
    const s0 = m.init()[0];
    // Two different interleavings that send the same set of messages must be
    // the same state - msgs is a set, not a log.
    const a = m.actions.find((x) => x.name === 'Phase1a')!;
    const viaA = a.effect(a.effect(s0, { bal: 0 }), { bal: 1 });
    const viaB = a.effect(a.effect(s0, { bal: 1 }), { bal: 0 });
    expect(m.key(viaA)).toBe(m.key(viaB));
  });
});

describe('symmetry', () => {
  it('collapses states that differ only by renaming acceptors', () => {
    const m = models[CORRECT];
    const s0 = m.init()[0];
    const p1a = m.actions.find((x) => x.name === 'Phase1a')!;
    const p1b = m.actions.find((x) => x.name === 'Phase1b')!;
    const base = p1a.effect(s0, { bal: 0 });
    const a1 = p1b.effect(base, { acc: 0, bal: 0 });
    const a2 = p1b.effect(base, { acc: 1, bal: 0 });
    expect(m.key(a1)).not.toBe(m.key(a2));
    const rep = (s: PaxosState) => m.symmetry!.orbit(s).map((x) => m.key(x)).sort()[0];
    expect(rep(a1)).toBe(rep(a2));
  });
});

describe('golden Paxos facts', () => {
  const graph = (c: string) => bfs(models[c], { maxStates: 200_000, keepTransitions: false });

  it('correct Paxos never chooses two values', () => {
    const g = graph(CORRECT);
    for (const s of g.states.values()) expect(models[CORRECT].predicates.Agreement(s)).toBe(true);
  });

  it.each(['P1', 'P4', 'P6', 'P7'])('%s reaches disagreement', (id) => {
    const g = graph(id);
    const broken = [...g.states.values()].some((s) => !models[id].predicates.Agreement(s));
    expect(broken).toBe(true);
  });

  // DESIGN.md §10.3: the classification is DERIVED and compared against the
  // declaration, not hand-asserted. This is what caught P5 and P6 being
  // overlapping rather than adding.
  it.each(MUTANTS.map((m) => [m.id, m.directionAt2Ballots] as const))(
    '%s is %s at two ballots',
    (id, declared) => {
      const rc = new Set(graph(CORRECT).depth.keys());
      const ri = new Set(graph(id).depth.keys());
      const onlyI = [...ri].filter((k) => !rc.has(k)).length;
      const onlyC = [...rc].filter((k) => !ri.has(k)).length;
      const measured =
        onlyI === 0 && onlyC === 0
          ? 'equal'
          : onlyC === 0
            ? 'adding'
            : onlyI === 0
              ? 'restricting'
              : 'overlapping';
      expect(measured).toBe(declared);
    },
  );
});

describe('pair construction', () => {
  const m = models[CORRECT];
  const g = bfs(m, { maxStates: 400, maxDepth: 4 });
  const some = [...g.states.values()].filter((s) => s.msgs.length >= 2).slice(0, 12);

  it('only produces contrasts of distance 1 or 2', () => {
    for (const s of some) {
      const cands = enumerateSteps(models, CORRECT, s);
      for (const p of buildPairs(cands, CORRECT, ALL_CONFIGS, (c) => c.pre.msgs.length)) {
        expect([1, 2]).toContain(p.distance);
        expect(contrastDistance(p.a, p.b)).toBe(p.distance);
      }
    }
  });

  it('every pair separates at least two configs', () => {
    for (const s of some) {
      const cands = enumerateSteps(models, CORRECT, s);
      for (const p of buildPairs(cands, CORRECT, ALL_CONFIGS, (c) => c.pre.msgs.length)) {
        const seen = new Set(
          ALL_CONFIGS.map((c) => `${p.a.membership[c] ? 1 : 0}${p.b.membership[c] ? 1 : 0}`),
        );
        expect(seen.size).toBeGreaterThanOrEqual(2);
      }
    }
  });

  it('records effect-level differences, not just guard differences', () => {
    // P5 and P6 enable exactly the same Phase1b instances as Paxos but land in
    // a different state. A membership vector over guards alone would miss them.
    const s = some.find((x) => x.msgs.some((msg) => msg.t === '1a'))!;
    const cands = enumerateSteps(models, CORRECT, s).filter((c) => c.action === 'Phase1b');
    const effectDiffs = cands.filter((c) => c.failed['P6'] === 'Phase1b.effect');
    expect(effectDiffs.length).toBeGreaterThan(0);
  });
});

describe('learner model', () => {
  const q = (id: string, c: [boolean, boolean], m: [boolean, boolean]): Question => ({
    id,
    kind: 'step',
    type: 'one',
    a: { payload: { kind: 'state', state: null }, justification: { verdict: 'legal', refs: [], text: '' } },
    b: { payload: { kind: 'state', state: null }, justification: { verdict: 'legal', refs: [], text: '' } },
    distance: 1,
    answer: { C: c, X: m },
    targets: ['C|X'],
    misconceptions: ['X'],
    size: 1,
  });

  it('moves the posterior toward a misconception the answers match', () => {
    const qs = [q('q1', [false, true], [true, true]), q('q2', [true, false], [true, true])];
    const p = recompute(qs, [
      { questionId: 'q1', answer: 'both' },
      { questionId: 'q2', answer: 'both' },
    ], ['X']);
    expect(p['X']).toBeGreaterThan(0.9);
  });

  it('is unmoved by "unsure"', () => {
    const qs = [q('q1', [false, true], [true, true])];
    const p = recompute(qs, [{ questionId: 'q1', answer: 'unsure' }], ['X']);
    expect(p['X']).toBeCloseTo(0.3, 10);
  });

  it('recomputes from scratch, so editing an answer fully undoes it', () => {
    const qs = [q('q1', [false, true], [true, true]), q('q2', [true, false], [true, true])];
    const withBad = recompute(qs, [
      { questionId: 'q1', answer: 'both' },
      { questionId: 'q2', answer: 'A' },
    ], ['X']);
    const edited = recompute(qs, [
      { questionId: 'q1', answer: 'both' },
      { questionId: 'q2', answer: 'A' },
    ], ['X']);
    expect(edited['X']).toBeCloseTo(withBad['X'], 12);
    const justFirst = recompute(qs, [{ questionId: 'q1', answer: 'both' }], ['X']);
    expect(justFirst['X']).not.toBeCloseTo(withBad['X'], 3);
  });

  it('categorical posterior is a distribution over all candidates', () => {
    const qs = [q('q1', [false, true], [true, true])];
    const p = recomputeCategorical(qs, [{ questionId: 'q1', answer: 'both' }], ['C', 'X']);
    expect(p['C'] + p['X']).toBeCloseTo(1, 10);
    expect(p['X']).toBeGreaterThan(p['C']);
  });
});
