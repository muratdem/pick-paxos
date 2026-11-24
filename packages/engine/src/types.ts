/** Core model-agnostic types. See DESIGN.md §5.1. */

export type Value = string | number | boolean | null | Value[] | { [k: string]: Value };
export type Params = Record<string, Value>;

/** A structured reference to a state field, used to check that the rendering
 *  shows everything the learner needs to decide (DESIGN.md §10.5). */
export type FieldRef =
  | { kind: 'acceptor'; acc: number; field: 'maxBal' | 'maxVBal' | 'maxVal' }
  | { kind: 'msg'; msg: Value }
  | { kind: 'msgset'; msgType: string }
  | { kind: 'param'; name: string };

/** One named guard conjunct. Guards are ordered lists of these, never opaque
 *  booleans: that is what makes justification generation free and makes a
 *  mutation flag a precise edit rather than a rewrite. */
export interface Conjunct<S> {
  id: string;
  /** Human-readable rule text, spliced into justifications. */
  holds(s: S, p: Params): boolean;
  reads(s: S, p: Params): FieldRef[];
}

export interface Action<S> {
  name: string;
  /** All candidate parameter bindings, enabled or not. Must not depend on `s`
   *  so that perturbation neighbourhoods are well defined across states. */
  domain(): Params[];
  guard: Conjunct<S>[];
  effect(s: S, p: Params): S;
  sends(s: S, p: Params): Value[];
  reads(s: S, p: Params): Value[];
  /** Plain-words description, e.g. "Acceptor a2 accepts the ballot-1 proposal." */
  describe(p: Params): string;
}

export type Enabled = { ok: true } | { ok: false; failed: string };

export interface ActionInstance<S> {
  action: string;
  params: Params;
  reads: Value[];
  sends: Value[];
  next: S;
}

export interface Symmetry<S> {
  /** All permutations of symmetric model values applied to a state. */
  orbit(s: S): S[];
}

export interface ViewSpec {
  /** Field refs the renderer displays for a given state. §10.5 check 2 asserts
   *  that every justification's refs are a subset of this. */
  displayed(s: unknown): FieldRef[];
}

export interface Model<S> {
  id: string;
  title: string;
  constants: Record<string, Value>;
  flags: Record<string, boolean>;
  init(): S[];
  actions: Action<S>[];
  /** Canonical identity of a state. Must be injective on states and agree with
   *  the model's own set canonicalization; everything downstream keys on it. */
  key(s: S): string;
  enabled(s: S, action: string, p: Params): Enabled;
  successors(s: S): ActionInstance<S>[];
  predicates: Record<string, (s: S) => boolean>;
  symmetry?: Symmetry<S>;
  toTLA(s: S): string;
  view: ViewSpec;
}

export type ModelFactory<S> = (
  constants: Record<string, Value>,
  flags: Record<string, boolean>,
) => Model<S>;

/* ------------------------------------------------------------------ */
/* Bank schema (DESIGN.md §6.8)                                        */
/* ------------------------------------------------------------------ */

export type PairType = 'one' | 'both' | 'neither';

export interface Justification {
  verdict: 'legal' | 'illegal';
  conjunct?: string;
  refs: FieldRef[];
  text: string;
}

export interface StepPayload {
  kind: 'step';
  pre: Value;
  post: Value;
  action: string;
  params: Params;
  reads: Value[];
  sends: Value[];
  describe: string;
}

export interface StatePayload {
  kind: 'state';
  state: Value;
  /** For `chosen`: which value THIS card asks about. Without it the two cards
   *  of a chosen question render identically and the pair is unanswerable. */
  subject?: string;
}

export interface TracePayload {
  kind: 'trace';
  steps: StepPayload[];
}

export type Payload = StepPayload | StatePayload | TracePayload;

export interface Scenario {
  payload: Payload;
  justification: Justification;
}

export type AnswerValue = boolean | [boolean, boolean] | string[] | number;

export interface Question {
  id: string;
  kind: 'step' | 'chosen' | 'future' | 'trace-locate' | 'state' | 'which';
  type: PairType;
  a: Scenario;
  b?: Scenario;
  distance: 1 | 2;
  /** What the two options differ in. `effect` means the SAME action with the
   *  same parameters, landing in different states — the two cards then carry
   *  identical titles and the reader needs telling that the difference is in
   *  what the action does, not in which action it is. */
  contrast?: 'effect' | 'params' | 'action';
  /** Per config: the pair membership [inA, inB], or a kind-specific answer. */
  answer: Record<string, AnswerValue>;
  /** Config pairs this question separates, as "C|P3" strings. */
  targets: string[];
  /** Misconception ids this question bears on, for the learner model. */
  misconceptions: string[];
  size: number;
  boundStable?: boolean;
  /** For `chosen`: which value the question asks about. */
  subject?: string;
  /** For `trace-locate`: index of the first illegal step. */
  firstIllegal?: number;
}

export interface Bank {
  protocol: string;
  level: string;
  title: string;
  blurb: string;
  generatedFrom: {
    modelVersion: string;
    constants: Record<string, Value>;
    configs: string[];
    seed: number;
  };
  configs: string[];
  /** true when the candidates are mutually exclusive (one definition of
   *  "chosen" is held, not a subset of several). Drives categorical scoring. */
  exclusive?: boolean;
  questions: Question[];
  mix: Record<PairType, number>;
}
