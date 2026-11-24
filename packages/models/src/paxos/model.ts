/** Single-decree Paxos, a literal transcription of Lamport's Paxos.tla with
 *  each guard broken into named conjuncts (DESIGN.md §5.1, §5.2).
 *
 *  Do not merge conjuncts and do not reorder them: justification generation
 *  reports the FIRST false conjunct, and mutation flags are defined as edits to
 *  individual conjuncts by id.
 */

import type { Action, Conjunct, Enabled, FieldRef, Model, Params, Value } from '@dyp/engine';
import { stableStringify } from '@dyp/engine';

export type Msg =
  | { t: '1a'; bal: number }
  | { t: '1b'; acc: number; bal: number; mbal: number; mval: string | null }
  | { t: '2a'; bal: number; val: string }
  | { t: '2b'; acc: number; bal: number; val: string };

export interface PaxosState {
  maxBal: number[];
  maxVBal: number[];
  maxVal: (string | null)[];
  msgs: Msg[];
}

export interface PaxosConstants {
  acceptors: number;
  values: string[];
  ballots: number[];
  /** Explicit quorum system. Majorities by default; Flexible Paxos overrides. */
  quorums: number[][];
}

export const MUTANT_FLAGS = [
  'ownValue',
  'anyReported',
  'noQuorumPhase1',
  'ignorePromise',
  'forgetfulPromise',
  'noPromiseUpdate',
  'multiProposalPerBallot',
  'strictAccept',
  'unanimousPhase1',
  'voteOnce',
  'monotoneBallots',
] as const;

export type MutantFlag = (typeof MUTANT_FLAGS)[number];
export type Flags = Partial<Record<MutantFlag, boolean>>;

export function majorities(n: number): number[][] {
  const out: number[][] = [];
  const need = Math.floor(n / 2) + 1;
  for (let mask = 0; mask < 1 << n; mask++) {
    const q: number[] = [];
    for (let i = 0; i < n; i++) if (mask & (1 << i)) q.push(i);
    if (q.length >= need) out.push(q);
  }
  return out;
}

export function defaultConstants(ballots = [0, 1]): PaxosConstants {
  /* Named candidates rather than `x` and `y`. Single-decree Paxos decides ONE
   * value; naming the two candidates makes it obvious they compete for a
   * single slot, and makes "has Alice been chosen?" a sentence instead of a
   * variable lookup. */
  return { acceptors: 3, values: ['Alice', 'Bob'], ballots, quorums: majorities(3) };
}

export const accName = (i: number) => `Acceptor ${i + 1}`;
export const qName = (q: number[]) => {
  const names = q.map(accName);
  return names.length <= 1
    ? (names[0] ?? 'nobody')
    : `${names.slice(0, -1).join(', ')} and ${names[names.length - 1]}`;
};

/* ------------------------------------------------------------------ */

/** Compact canonical key for a message. Hand-rolled rather than
 *  stableStringify because this is the hot path: BFS calls it millions of
 *  times and the generic serializer dominated the profile. */
export const msgKey = (m: Msg): string => {
  switch (m.t) {
    case '1a':
      return `a|${m.bal}`;
    case '1b':
      return `b|${m.acc}|${m.bal}|${m.mbal}|${m.mval ?? '~'}`;
    case '2a':
      return `c|${m.bal}|${m.val}`;
    case '2b':
      return `d|${m.acc}|${m.bal}|${m.val}`;
  }
};

/** Messages are a SET: kept sorted by msgKey so that state identity is
 *  canonical regardless of the order they were sent in. */
function addMsg(msgs: Msg[], m: Msg): Msg[] {
  const k = msgKey(m);
  let lo = 0;
  let hi = msgs.length;
  while (lo < hi) {
    const mid = (lo + hi) >> 1;
    if (msgKey(msgs[mid]) < k) lo = mid + 1;
    else hi = mid;
  }
  if (lo < msgs.length && msgKey(msgs[lo]) === k) return msgs;
  const out = msgs.slice();
  out.splice(lo, 0, m);
  return out;
}

export const paxosKey = (s: PaxosState): string =>
  `${s.maxBal.join(',')}/${s.maxVBal.join(',')}/${s.maxVal.map((v) => v ?? '~').join(',')}/` +
  s.msgs.map(msgKey).join(';');

const has1a = (s: PaxosState, bal: number) => s.msgs.some((m) => m.t === '1a' && m.bal === bal);
const get1b = (s: PaxosState, acc: number, bal: number) =>
  s.msgs.find((m) => m.t === '1b' && m.acc === acc && m.bal === bal) as
    | Extract<Msg, { t: '1b' }>
    | undefined;
const has2a = (s: PaxosState, bal: number) => s.msgs.some((m) => m.t === '2a' && m.bal === bal);
const get2a = (s: PaxosState, bal: number, val: string) =>
  s.msgs.find((m) => m.t === '2a' && m.bal === bal && m.val === val);

/** The 1b messages for ballot `bal` from quorum `q` that report a prior acceptance. */
function reported(s: PaxosState, q: number[], bal: number): Extract<Msg, { t: '1b' }>[] {
  const out: Extract<Msg, { t: '1b' }>[] = [];
  for (const a of q) {
    const m = get1b(s, a, bal);
    if (m && m.mbal >= 0) out.push(m);
  }
  return out;
}

const accRefs = (acc: number): FieldRef[] => [
  { kind: 'acceptor', acc, field: 'maxBal' },
  { kind: 'acceptor', acc, field: 'maxVBal' },
  { kind: 'acceptor', acc, field: 'maxVal' },
];

/* ------------------------------------------------------------------ */
/* Conjunct library. Each is referenced by id from content/paxos/rules.yaml. */

type C = Conjunct<PaxosState>;

const c = {
  // ---- Phase1a ----
  noGaps: {
    id: 'phase1a.noGaps',
    holds: (s, p) => (p.bal as number) === 0 || has1a(s, (p.bal as number) - 1),
    reads: (_s, p) => [{ kind: 'msgset', msgType: '1a' }, { kind: 'param', name: 'bal' }],
  } satisfies C,

  // ---- Phase1b ----
  requestExists: {
    id: 'phase1b.requestExists',
    holds: (s, p) => has1a(s, p.bal as number),
    reads: () => [{ kind: 'msgset', msgType: '1a' }],
  } satisfies C,
  newer: {
    id: 'phase1b.newer',
    holds: (s, p) => (p.bal as number) > s.maxBal[p.acc as number],
    reads: (_s, p) => [{ kind: 'acceptor', acc: p.acc as number, field: 'maxBal' }],
  } satisfies C,

  // ---- Phase2a ----
  noPriorProposal: {
    id: 'phase2a.noPriorProposal',
    holds: (s, p) => !has2a(s, p.bal as number),
    reads: () => [{ kind: 'msgset', msgType: '2a' }],
  } satisfies C,
  quorumPromised: {
    id: 'phase2a.quorumPromised',
    holds: (s, p) => (p.quorum as number[]).every((a) => !!get1b(s, a, p.bal as number)),
    reads: () => [{ kind: 'msgset', msgType: '1b' }, { kind: 'param', name: 'quorum' }],
  } satisfies C,
  someOnePromised: {
    id: 'phase2a.someOnePromised',
    holds: (s, p) => (p.quorum as number[]).some((a) => !!get1b(s, a, p.bal as number)),
    reads: () => [{ kind: 'msgset', msgType: '1b' }, { kind: 'param', name: 'quorum' }],
  } satisfies C,
  unanimousPromised: {
    id: 'phase2a.unanimousPromised',
    holds: (s, p) => s.maxBal.every((_, a) => !!get1b(s, a, p.bal as number)),
    reads: () => [{ kind: 'msgset', msgType: '1b' }],
  } satisfies C,
  highestReported: {
    id: 'phase2a.highestReported',
    holds: (s, p) => {
      const r = reported(s, p.quorum as number[], p.bal as number);
      if (r.length === 0) return true;
      const top = Math.max(...r.map((m) => m.mbal));
      return r.some((m) => m.mbal === top && m.mval === (p.val as string));
    },
    reads: () => [{ kind: 'msgset', msgType: '1b' }, { kind: 'param', name: 'quorum' }],
  } satisfies C,
  anyReported: {
    id: 'phase2a.anyReported',
    holds: (s, p) => {
      const r = reported(s, p.quorum as number[], p.bal as number);
      if (r.length === 0) return true;
      return r.some((m) => m.mval === (p.val as string));
    },
    reads: () => [{ kind: 'msgset', msgType: '1b' }, { kind: 'param', name: 'quorum' }],
  } satisfies C,

  // ---- Phase2b ----
  proposalExists: {
    id: 'phase2b.proposalExists',
    holds: (s, p) => !!get2a(s, p.bal as number, p.val as string),
    reads: () => [{ kind: 'msgset', msgType: '2a' }],
  } satisfies C,
  ballotAtLeastPromised: {
    id: 'phase2b.ballotAtLeastPromised',
    holds: (s, p) => (p.bal as number) >= s.maxBal[p.acc as number],
    reads: (_s, p) => [{ kind: 'acceptor', acc: p.acc as number, field: 'maxBal' }],
  } satisfies C,
  ballotStrictlyGreater: {
    id: 'phase2b.ballotStrictlyGreater',
    holds: (s, p) => (p.bal as number) > s.maxBal[p.acc as number],
    reads: (_s, p) => [{ kind: 'acceptor', acc: p.acc as number, field: 'maxBal' }],
  } satisfies C,
  neverVoted: {
    id: 'phase2b.neverVoted',
    holds: (s, p) => s.maxVBal[p.acc as number] === -1,
    reads: (_s, p) => [{ kind: 'acceptor', acc: p.acc as number, field: 'maxVBal' }],
  } satisfies C,
};

/* ------------------------------------------------------------------ */

export function paxos(k: PaxosConstants, flags: Flags = {}): Model<PaxosState> {
  const N = k.acceptors;
  const f = (x: MutantFlag) => flags[x] === true;

  /* ---- guards, assembled per flag ---- */
  const g1a: C[] = f('monotoneBallots') ? [c.noGaps] : [];
  const g1b: C[] = [c.requestExists, c.newer];

  const g2a: C[] = [];
  if (!f('multiProposalPerBallot')) g2a.push(c.noPriorProposal);
  if (f('noQuorumPhase1')) g2a.push(c.someOnePromised);
  else if (f('unanimousPhase1')) g2a.push(c.unanimousPromised);
  else g2a.push(c.quorumPromised);
  if (f('ownValue')) {
    /* drop the value-selection rule entirely */
  } else if (f('anyReported')) g2a.push(c.anyReported);
  else g2a.push(c.highestReported);

  const g2b: C[] = [c.proposalExists];
  if (f('strictAccept')) g2b.push(c.ballotStrictlyGreater);
  else if (!f('ignorePromise')) g2b.push(c.ballotAtLeastPromised);
  if (f('voteOnce')) g2b.push(c.neverVoted);

  /* ---- actions ---- */
  const actions: Action<PaxosState>[] = [
    {
      name: 'Phase1a',
      domain: () => k.ballots.map((bal) => ({ bal })),
      guard: g1a,
      effect: (s, p) => ({ ...s, msgs: addMsg(s.msgs, { t: '1a', bal: p.bal as number }) }),
      sends: (_s, p) => [{ t: '1a', bal: p.bal as number } as unknown as Value],
      reads: () => [],
      describe: (p) =>
        `The proposer running ballot ${p.bal} asks every acceptor to promise ballot ${p.bal}.`,
    },
    {
      name: 'Phase1b',
      domain: () => {
        const out: Params[] = [];
        for (let acc = 0; acc < N; acc++) for (const bal of k.ballots) out.push({ acc, bal });
        return out;
      },
      guard: g1b,
      effect: (s, p) => {
        const acc = p.acc as number;
        const bal = p.bal as number;
        const maxBal = [...s.maxBal];
        if (!f('noPromiseUpdate')) maxBal[acc] = bal;
        const m: Msg = f('forgetfulPromise')
          ? { t: '1b', acc, bal, mbal: -1, mval: null }
          : { t: '1b', acc, bal, mbal: s.maxVBal[acc], mval: s.maxVal[acc] };
        return { ...s, maxBal, msgs: addMsg(s.msgs, m) };
      },
      sends: (s, p) => {
        const acc = p.acc as number;
        return [
          (f('forgetfulPromise')
            ? { t: '1b', acc, bal: p.bal, mbal: -1, mval: null }
            : { t: '1b', acc, bal: p.bal, mbal: s.maxVBal[acc], mval: s.maxVal[acc] }) as unknown as Value,
        ];
      },
      reads: (_s, p) => [{ t: '1a', bal: p.bal as number } as unknown as Value],
      describe: (p) =>
        `${accName(p.acc as number)} promises ballot ${p.bal}, and reports what it last accepted.`,
    },
    {
      name: 'Phase2a',
      domain: () => {
        const out: Params[] = [];
        for (const bal of k.ballots)
          for (const val of k.values) for (const quorum of k.quorums) out.push({ bal, val, quorum });
        return out;
      },
      guard: g2a,
      effect: (s, p) => ({
        ...s,
        msgs: addMsg(s.msgs, { t: '2a', bal: p.bal as number, val: p.val as string }),
      }),
      sends: (_s, p) => [{ t: '2a', bal: p.bal, val: p.val } as unknown as Value],
      reads: (s, p) =>
        (p.quorum as number[])
          .map((a) => get1b(s, a, p.bal as number))
          .filter(Boolean) as unknown as Value[],
      describe: (p) =>
        `The proposer running ballot ${p.bal}, after hearing back from ` +
        `${qName(p.quorum as number[])}, proposes ${p.val}.`,
    },
    {
      name: 'Phase2b',
      domain: () => {
        const out: Params[] = [];
        for (let acc = 0; acc < N; acc++)
          for (const bal of k.ballots) for (const val of k.values) out.push({ acc, bal, val });
        return out;
      },
      guard: g2b,
      effect: (s, p) => {
        const acc = p.acc as number;
        const bal = p.bal as number;
        const val = p.val as string;
        const maxBal = [...s.maxBal];
        const maxVBal = [...s.maxVBal];
        const maxVal = [...s.maxVal];
        maxBal[acc] = bal;
        maxVBal[acc] = bal;
        maxVal[acc] = val;
        return { maxBal, maxVBal, maxVal, msgs: addMsg(s.msgs, { t: '2b', acc, bal, val }) };
      },
      sends: (_s, p) => [{ t: '2b', acc: p.acc, bal: p.bal, val: p.val } as unknown as Value],
      reads: (_s, p) => [{ t: '2a', bal: p.bal, val: p.val } as unknown as Value],
      describe: (p) =>
        `${accName(p.acc as number)} accepts ${p.val} in ballot ${p.bal}.`,
    },
  ];

  const byName = new Map(actions.map((a) => [a.name, a]));

  function enabled(s: PaxosState, name: string, p: Params): Enabled {
    const a = byName.get(name);
    if (!a) return { ok: false, failed: 'unknown.action' };
    for (const cj of a.guard) if (!cj.holds(s, p)) return { ok: false, failed: cj.id };
    return { ok: true };
  }

  /* ---- predicates ---- */
  const chosenC0 = (s: PaxosState, v: string) =>
    k.ballots.some((b) =>
      k.quorums.some((q) =>
        q.every((a) => s.msgs.some((m) => m.t === '2b' && m.acc === a && m.bal === b && m.val === v)),
      ),
    );
  const chosenD1 = (s: PaxosState, v: string) =>
    k.quorums.some((q) => q.every((a) => s.msgs.some((m) => m.t === '2b' && m.acc === a && m.val === v)));
  const chosenD2 = (s: PaxosState, v: string) => s.msgs.some((m) => m.t === '2a' && m.val === v);
  const chosenD3 = (s: PaxosState, v: string) => s.msgs.some((m) => m.t === '2b' && m.val === v);
  const chosenD4 = (s: PaxosState, v: string) => k.quorums.some((q) => q.every((a) => s.maxVal[a] === v));

  const predicates: Record<string, (s: PaxosState) => boolean> = {
    Agreement: (s) => k.values.filter((v) => chosenC0(s, v)).length <= 1,
    AnyChosen: (s) => k.values.some((v) => chosenC0(s, v)),
  };
  for (const v of k.values) {
    predicates[`C0:${v}`] = (s) => chosenC0(s, v);
    predicates[`D1:${v}`] = (s) => chosenD1(s, v);
    predicates[`D2:${v}`] = (s) => chosenD2(s, v);
    predicates[`D3:${v}`] = (s) => chosenD3(s, v);
    predicates[`D4:${v}`] = (s) => chosenD4(s, v);
  }

  const model: Model<PaxosState> = {
    id: 'paxos',
    title: 'Single-decree Paxos',
    constants: k as unknown as Record<string, Value>,
    flags: flags as Record<string, boolean>,
    init: () => [
      {
        maxBal: Array(N).fill(-1),
        maxVBal: Array(N).fill(-1),
        maxVal: Array(N).fill(null),
        msgs: [],
      },
    ],
    actions,
    key: paxosKey,
    enabled,
    successors(s) {
      const out = [];
      for (const a of actions) {
        for (const p of a.domain()) {
          if (!enabled(s, a.name, p).ok) continue;
          const next = a.effect(s, p);
          // Skip stutter: a step that changes nothing is never a useful question
          // and would otherwise fill the graph with self-loops.
          if (paxosKey(next) === paxosKey(s)) continue;
          out.push({ action: a.name, params: p, reads: a.reads(s, p), sends: a.sends(s, p), next });
        }
      }
      return out;
    },
    predicates,
    symmetry: {
      orbit(s) {
        const perms = permutations([...Array(N).keys()]);
        const vperms = permutations(k.values);
        const out: PaxosState[] = [];
        for (const pa of perms)
          for (const pv of vperms) {
            const vmap = new Map(k.values.map((v, i) => [v, pv[i]]));
            const mv = (v: string | null) => (v === null ? null : vmap.get(v)!);
            const maxBal = Array(N).fill(0);
            const maxVBal = Array(N).fill(0);
            const maxVal: (string | null)[] = Array(N).fill(null);
            for (let i = 0; i < N; i++) {
              maxBal[pa[i]] = s.maxBal[i];
              maxVBal[pa[i]] = s.maxVBal[i];
              maxVal[pa[i]] = mv(s.maxVal[i]);
            }
            const msgs = s.msgs.map((m): Msg => {
              switch (m.t) {
                case '1a':
                  return m;
                case '1b':
                  return { ...m, acc: pa[m.acc], mval: mv(m.mval) };
                case '2a':
                  return { ...m, val: vmap.get(m.val)! };
                case '2b':
                  return { ...m, acc: pa[m.acc], val: vmap.get(m.val)! };
              }
            });
            msgs.sort((x, y) => (msgKey(x) < msgKey(y) ? -1 : msgKey(x) > msgKey(y) ? 1 : 0));
            out.push({ maxBal, maxVBal, maxVal, msgs });
          }
        return out;
      },
    },
    toTLA(s) {
      const fn = (xs: (number | string | null)[], lit: (x: never) => string) =>
        `(${xs.map((x, i) => `${i + 1} :> ${lit(x as never)}`).join(' @@ ')})`;
      const num = (x: number) => String(x);
      const val = (x: string | null) => (x === null ? 'None' : `"${x}"`);
      const msg = (m: Msg): string => {
        switch (m.t) {
          case '1a':
            return `[type |-> "1a", bal |-> ${m.bal}]`;
          case '1b':
            return `[type |-> "1b", acc |-> ${m.acc + 1}, bal |-> ${m.bal}, mbal |-> ${m.mbal}, mval |-> ${val(m.mval)}]`;
          case '2a':
            return `[type |-> "2a", bal |-> ${m.bal}, val |-> ${val(m.val)}]`;
          case '2b':
            return `[type |-> "2b", acc |-> ${m.acc + 1}, bal |-> ${m.bal}, val |-> ${val(m.val)}]`;
        }
      };
      return [
        `maxBal = ${fn(s.maxBal, num as never)}`,
        `maxVBal = ${fn(s.maxVBal, num as never)}`,
        `maxVal = ${fn(s.maxVal, val as never)}`,
        `msgs = {${s.msgs.map(msg).join(', ')}}`,
      ].join(' /\\ ');
    },
    view: {
      /* The renderer shows the full acceptor table and the full message panel,
       * plus the action's parameters. §10.5 check 2 asserts justification refs
       * are a subset of this; the live case is Phase2a's `quorum` parameter,
       * which the step renderer must display or the question is unanswerable. */
      displayed() {
        const refs: FieldRef[] = [];
        for (let a = 0; a < N; a++) refs.push(...accRefs(a));
        for (const t of ['1a', '1b', '2a', '2b']) refs.push({ kind: 'msgset', msgType: t });
        for (const n of ['bal', 'val', 'acc', 'quorum']) refs.push({ kind: 'param', name: n });
        return refs;
      },
    },
  };

  return model;
}

function permutations<T>(xs: T[]): T[][] {
  if (xs.length <= 1) return [xs];
  const out: T[][] = [];
  for (let i = 0; i < xs.length; i++) {
    const rest = [...xs.slice(0, i), ...xs.slice(i + 1)];
    for (const p of permutations(rest)) out.push([xs[i], ...p]);
  }
  return out;
}
