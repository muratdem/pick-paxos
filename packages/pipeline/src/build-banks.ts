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
  defaultConstants,
  flagsFor,
  paxos,
  type PaxosState,
} from '@dyp/models';
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

function justify(step: StepCand<PaxosState>): Justification {
  const action = CM.actions.find((a) => a.name === step.action)!;

  if (!step.membership[CORRECT]) {
    const id = step.failed[CORRECT];
    const rule = ruleFor(id);
    const refs = id.endsWith('.effect')
      ? CM.view.displayed(step.pre).filter((r) => r.kind !== 'param')
      : (action.guard.find((c) => c.id === id)?.reads(step.pre, step.params) ?? []);
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

/* ---- chosen level ------------------------------------------------------ */
/* Definition-level candidates (§5.4). The "configs" here are competing
 * definitions of Chosen rather than protocol variants, but the pair machinery
 * and the Bayes update are identical: C0 plays the role of the correct config.
 *
 * The contrast is the same state asked about BOTH values. That always has a
 * partner, it differs in exactly one feature, and it is the form that exposes
 * D4 ("a majority currently holds v") most sharply. */

let DEFS = ['C', 'D1', 'D2', 'D3', 'D4'];

/* PICK collapses candidates with equivalent languages before generating
 * scenarios (paper §2.3), and the same step is needed here.
 *
 * D1 ("a majority voted for v at some point, in any ballots") and D4 ("a
 * majority currently holds v") turn out to agree on EVERY reachable Paxos
 * state. That is not an artifact of the bound: it is Paxos's safety theorem
 * showing through. For a majority to have voted for v and then be broken up,
 * some acceptor would have to vote for a different value later - and the
 * phase-2a rule makes that impossible, because any quorum promising a later
 * ballot intersects the majority that voted v and is forced to re-propose it.
 *
 * So the two are indistinguishable BY CONSTRUCTION, and no amount of question
 * generation will separate them. Reporting them as two candidates would mean
 * the results screen naming a misconception the learner may not hold. */
function collapseEquivalentDefs(states: PaxosState[]): Map<string, string[]> {
  const sig = new Map<string, string[]>();
  for (const d of DEFS.filter((x) => x !== 'C')) {
    const id = d === 'C' ? 'C0' : d;
    let bits = '';
    for (const s of states)
      bits += (CM.predicates[`${id}:${K.values[0]}`](s) ? '1' : '0') +
        (CM.predicates[`${id}:${K.values[1]}`](s) ? '1' : '0');
    const key = hash(bits);
    (sig.get(key) ?? sig.set(key, []).get(key)!).push(d);
  }
  const classes = new Map<string, string[]>();
  for (const group of sig.values()) classes.set(group.join('+'), group);
  return classes;
}

{
  t = Date.now();
  {
    const probe = allStates.filter((s) => msgCount(s) >= 3 && msgCount(s) <= 12);
    const classes = collapseEquivalentDefs(probe);
    const merged = [...classes.keys()].filter((k) => k.includes('+'));
    if (merged.length)
      console.log(`  collapsing equivalent definitions: ${merged.join(', ')} (agree on all ${probe.length} states)`);
    DEFS = ['C', ...classes.keys()];
  }
  const DEFMEMBERS: Record<string, string> = {};
  for (const d of DEFS) DEFMEMBERS[d] = d.split('+')[0];

  /* Scan EVERY reachable state, not a stratified sample. These are pure
   * predicate evaluations and cost nothing, and the states that separate D1
   * ("a majority voted for v at some point") from D4 ("a majority holds v
   * right now") are genuinely rare: they need an acceptor to have voted for v
   * and then voted again for something else. A sample of a thousand states
   * contains almost none of them, and the level then cannot tell the two
   * definitions apart at all. */
  interface DefCand {
    s: PaxosState;
    m: Record<string, [boolean, boolean]>; // per def: [chosen x?, chosen y?]
  }
  const cands: DefCand[] = [];
  const seenDef = new Set<string>();
  for (const s of allStates) {
    if (msgCount(s) < 3 || msgCount(s) > 12) continue;
    const m: Record<string, [boolean, boolean]> = {};
    for (const d of DEFS) {
      const id = d === 'C' ? 'C0' : DEFMEMBERS[d];
      m[d] = [CM.predicates[`${id}:${K.values[0]}`](s), CM.predicates[`${id}:${K.values[1]}`](s)];
    }
    // useful only if some definition disagrees with C0 on at least one value
    if (!DEFS.some((d) => m[d][0] !== m['C'][0] || m[d][1] !== m['C'][1])) continue;
    const rep = CM.symmetry!.orbit(s).map((x) => CM.key(x)).sort()[0];
    if (seenDef.has(rep)) continue;
    seenDef.add(rep);
    cands.push({ s, m });
  }
  const pool = cands;

  const dis = (d: string) => cands.filter((c) => c.m[d][0] !== c.m['C'][0] || c.m[d][1] !== c.m['C'][1]).length;
  console.log(
    `  chosen-level candidates: ${cands.length}; disagree with C0: ` +
      `${DEFS.filter((d) => d !== 'C').map((d) => `${d}:${dis(d)}`).join(' ')}`,
  );

  const rng = new Rng(SEED + 2);
  const byType: Record<string, DefCand[]> = { one: [], both: [], neither: [] };
  for (const c of rng.shuffle(cands)) {
    const [cx, cy] = c.m['C'];
    byType[cx && cy ? 'both' : !cx && !cy ? 'neither' : 'one'].push(c);
  }

  /* No `both` quota: two values chosen at once IS an agreement violation, so a
   * `both` pair cannot exist in a reachable state of correct Paxos. The level
   * is structurally one/neither, which still defeats every constant answer. */
  /* Keep `neither` well under half, or "answer neither to everything" walks
   * the level - the harness catches this directly. */
  const quota = { one: 24, both: 0, neither: 12 };
  const coverage = new Map<string, number>();
  /* As with the step levels, separating each definition from C0 is not enough:
   * D1-D4 disagree with C0 on heavily overlapping sets of states, so without
   * explicitly rewarding states that split two DEFINITIONS from each other the
   * bank reports all four as likely whichever one the learner actually holds. */
  const sepCoverage = new Map<string, number>();
  const sepsOf = (c: DefCand) => {
    const out: string[] = [];
    for (let i = 0; i < DEFS.length; i++)
      for (let j = i + 1; j < DEFS.length; j++) {
        const [x, y] = [DEFS[i], DEFS[j]];
        if (x === 'C' || y === 'C') continue;
        if (c.m[x][0] !== c.m[y][0] || c.m[x][1] !== c.m[y][1]) out.push(`${x}|${y}`);
      }
    return out;
  };
  const picked: DefCand[] = [];

  /* Guarantee a floor per definition before filling by score. D1+D4 disagrees
   * with C0 on only 174 of 2165 states, and those states are large (a value
   * voted across two ballots needs ten-plus messages), so the size penalty
   * means pure greedy scoring leaves it with two questions and the level
   * cannot detect it. A floor is blunt but it is the thing that makes the
   * level able to diagnose what it claims to diagnose. */
  const MIN_PER_DEF = 6;
  for (const d of DEFS.filter((x) => x !== 'C')) {
    const disagreeing = rng
      .shuffle(cands.filter((c) => c.m[d][0] !== c.m['C'][0] || c.m[d][1] !== c.m['C'][1]))
      .sort((a, b) => msgCount(a.s) - msgCount(b.s));
    let n = 0;
    for (const c of disagreeing) {
      if (n >= MIN_PER_DEF) break;
      if (picked.includes(c)) continue;
      picked.push(c);
      n++;
      for (const x of DEFS)
        if (x !== 'C' && (c.m[x][0] !== c.m['C'][0] || c.m[x][1] !== c.m['C'][1]))
          coverage.set(x, (coverage.get(x) ?? 0) + 1);
      for (const tt of sepsOf(c)) sepCoverage.set(tt, (sepCoverage.get(tt) ?? 0) + 1);
    }
  }

  /* A second floor, over definition PAIRS. D1+D4 implies D3, so every state
   * that is evidence FOR D1+D4 is equally evidence for D3 and can never tell
   * them apart. The only questions that separate them are the ones where some
   * acceptor voted for v but no majority did: there D3 says "chosen", D1+D4
   * says "not", and the learner's answer picks a side. Without a floor on
   * these the level reports both whichever one is held. */
  const MIN_PER_SEP = 5;
  const allSeps = new Set<string>();
  for (const c of cands) for (const tt of sepsOf(c)) allSeps.add(tt);
  for (const tt of allSeps) {
    const having = rng
      .shuffle(cands.filter((c) => sepsOf(c).includes(tt)))
      .sort((a, b) => msgCount(a.s) - msgCount(b.s));
    let n = picked.filter((c) => sepsOf(c).includes(tt)).length;
    for (const c of having) {
      if (n >= MIN_PER_SEP) break;
      if (picked.includes(c)) continue;
      const mis = DEFS.filter((d) => d !== 'C' && (c.m[d][0] !== c.m['C'][0] || c.m[d][1] !== c.m['C'][1]));
      if (!mis.length) continue;
      picked.push(c);
      n++;
      for (const x of mis) coverage.set(x, (coverage.get(x) ?? 0) + 1);
      for (const u of sepsOf(c)) sepCoverage.set(u, (sepCoverage.get(u) ?? 0) + 1);
    }
  }

  for (const type of ['one', 'both', 'neither'] as const) {
    const already = picked.filter((c) => {
      const [cx, cy] = c.m['C'];
      return (cx && cy ? 'both' : !cx && !cy ? 'neither' : 'one') === type;
    }).length;
    for (let n = already; n < quota[type]; n++) {
      let best: DefCand | null = null;
      let bestScore = -Infinity;
      for (const c of byType[type]) {
        if (picked.includes(c)) continue;
        const mis = DEFS.filter((d) => d !== 'C' && (c.m[d][0] !== c.m['C'][0] || c.m[d][1] !== c.m['C'][1]));
        if (!mis.length) continue;
        const novel = mis.reduce((a, d) => a + 1 / (1 + (coverage.get(d) ?? 0)), 0);
        const sep = sepsOf(c).reduce((a, t) => a + 1 / (1 + (sepCoverage.get(t) ?? 0)), 0);
        const score = novel * 4 + sep * 5 - msgCount(c.s) * 0.3;
        if (score > bestScore) {
          bestScore = score;
          best = c;
        }
      }
      if (!best) break;
      picked.push(best);
      for (const d of DEFS)
        if (d !== 'C' && (best.m[d][0] !== best.m['C'][0] || best.m[d][1] !== best.m['C'][1]))
          coverage.set(d, (coverage.get(d) ?? 0) + 1);
      for (const t of sepsOf(best)) sepCoverage.set(t, (sepCoverage.get(t) ?? 0) + 1);
    }
  }

  const explain = (s: PaxosState, v: string, yes: boolean): string =>
    yes
      ? `Yes — some majority of acceptors all voted for ${v} in the SAME ballot, which is what "chosen" means.`
      : `No — no majority voted for ${v} within a single ballot. Votes for ${v} scattered across ` +
        `different ballots do not add up to a decision; neither does a proposal, a single vote, ` +
        `or a majority that merely holds ${v} right now.`;

  /* Alternate which value is asked first, for the same reason the step levels
   * alternate sides: otherwise "x" is systematically the unchosen one and
   * "always answer B" walks the level. */
  const questions: Question[] = picked.map((c, i): Question => {
    const flip = i % 2 === 1;
    const vi = (n: number) => (flip ? 1 - n : n);
    const answer: Record<string, [boolean, boolean]> = {};
    for (const d of DEFS) answer[d] = flip ? [c.m[d][1], c.m[d][0]] : c.m[d];
    const misconceptions = DEFS.filter(
      (d) => d !== 'C' && (c.m[d][0] !== c.m['C'][0] || c.m[d][1] !== c.m['C'][1]),
    );
    const mk = (slot: number): Scenario => {
      const v = vi(slot);
      return {
        payload: { kind: 'state', state: c.s as unknown as Value, subject: K.values[v] },
        justification: {
          verdict: c.m['C'][v] ? 'legal' : 'illegal',
          refs: [],
          text: explain(c.s, K.values[v], c.m['C'][v]),
        },
      };
    };
    const [cx, cy] = answer['C'];
    return {
      id: `paxos-chosen-${String(i).padStart(3, '0')}`,
      kind: 'chosen',
      type: cx && cy ? 'both' : !cx && !cy ? 'neither' : 'one',
      a: mk(0),
      b: mk(1),
      distance: 1,
      answer,
      targets: [],
      misconceptions,
      size: msgCount(c.s),
      subject: `${K.values[vi(0)]}/${K.values[vi(1)]}`,
    };
  });

  /* Cap the `neither` share at a third. The coverage floors above pick purely
   * for separation and happily push it past half, at which point "answer
   * neither to everything" beats chance - which the harness flags. */
  const capped: Question[] = [];
  const nMax = Math.ceil(questions.length / 3);
  let nSeen = 0;
  for (const q of questions) {
    if (q.type === 'neither' && ++nSeen > nMax) continue;
    capped.push(q);
  }
  questions.length = 0;
  questions.push(...capped);

  const mix = { one: 0, both: 0, neither: 0 };
  for (const q of questions) mix[q.type]++;
  const cover = new Map<string, number>();
  for (const q of questions) for (const m of q.misconceptions) cover.set(m, (cover.get(m) ?? 0) + 1);

  writeBank(
    {
      protocol: 'paxos',
      level: 'paxos-chosen',
      title: 'What does "chosen" mean?',
      blurb:
        'One situation, two candidate values. Decide which of them has actually been ' +
        'chosen — it may be one, or neither. The definition is exact, and the plausible ' +
        'near-misses are not it.',
      generatedFrom: {
        modelVersion: '0.1.0',
        constants: K as unknown as Record<string, Value>,
        configs: DEFS,
        seed: SEED,
      },
      configs: DEFS,
      exclusive: true,
      questions,
      mix,
    },
    `paxos-chosen${' '.repeat(9)}q=${String(questions.length).padStart(3)} ` +
      `mix=${mix.one}/${mix.both}/${mix.neither}  ${pool.length} states, ${cands.length} useful\n` +
      `    selected  [${DEFS.filter((d) => d !== 'C').map((d) => `${d}:${cover.get(d) ?? 0}`).join(' ')}]  ${Date.now() - t}ms`,
  );
}

/* Ship the human-written text alongside the banks so the web app has no
 * build-time dependency on the YAML or on a parser. */
const defMembers: Record<string, string[]> = {};
for (const d of DEFS) if (d !== 'C') defMembers[d] = d.split('+');
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
        { id: 'paxos-chosen', order: 3, track: 'both' },
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
