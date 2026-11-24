/** The candidate family: correct Paxos plus one mutant per misconception.
 *  DESIGN.md §5.3.
 *
 *  The design assumed every mutant either adds behaviours or removes them.
 *  Measurement says otherwise: P5 and P6 edit what Phase1b DOES rather than
 *  when it fires, so they both gain states and lose them. That is a third
 *  category, and a useful one - an overlapping mutant supplies `both` pairs
 *  (steps Paxos allows and it forbids) as well as `neither` pairs, without
 *  needing a dedicated restricting mutant.
 *
 *  Why the categories matter at all: restricting and overlapping mutants are
 *  the only source of pairs whose answer is "yes, Paxos allows both" (§6.3).
 *  With adding mutants alone the answer key is all-no and a constant answer
 *  beats the game.
 *
 *  `direction` is MEASURED by packages/engine/src/engine.test.ts, not asserted
 *  here; the test fails if this table drifts from the models.
 */

import type { Flags, MutantFlag } from './model.js';

export interface MutantSpec {
  id: string;
  flag: MutantFlag;
  /** Conjunct ids this mutant touches, for cross-referencing with rules.yaml. */
  touches: string[];
  /** Measured at `minBallots`, not asserted. Effect mutants come out
   *  `overlapping`: changing what an action DOES rather than when it is
   *  enabled both gains states and loses them. `equal` means the mutant is
   *  indistinguishable at that bound and needs a larger one. */
  direction: 'adding' | 'restricting' | 'overlapping';
  /** direction at two ballots, which is what the TLC cross-check uses */
  directionAt2Ballots: 'adding' | 'restricting' | 'overlapping' | 'equal';
  /** Minimum ballot bound at which this mutant is distinguishable. */
  minBallots: number;
}

export const MUTANTS: MutantSpec[] = [
  { id: 'P1', flag: 'ownValue', touches: ['phase2a.highestReported'], direction: 'adding', directionAt2Ballots: 'adding', minBallots: 2 },
  { id: 'P2', flag: 'anyReported', touches: ['phase2a.highestReported', 'phase2a.anyReported'], direction: 'adding', directionAt2Ballots: 'equal', minBallots: 3 },
  { id: 'P3', flag: 'noQuorumPhase1', touches: ['phase2a.quorumPromised', 'phase2a.someOnePromised'], direction: 'adding', directionAt2Ballots: 'adding', minBallots: 2 },
  { id: 'P4', flag: 'ignorePromise', touches: ['phase2b.ballotAtLeastPromised'], direction: 'adding', directionAt2Ballots: 'adding', minBallots: 2 },
  { id: 'P5', flag: 'forgetfulPromise', touches: ['phase1b.effect'], direction: 'overlapping', directionAt2Ballots: 'overlapping', minBallots: 2 },
  { id: 'P6', flag: 'noPromiseUpdate', touches: ['phase1b.effect'], direction: 'overlapping', directionAt2Ballots: 'overlapping', minBallots: 2 },
  { id: 'P7', flag: 'multiProposalPerBallot', touches: ['phase2a.noPriorProposal'], direction: 'adding', directionAt2Ballots: 'adding', minBallots: 1 },
  { id: 'P8', flag: 'strictAccept', touches: ['phase2b.ballotAtLeastPromised', 'phase2b.ballotStrictlyGreater'], direction: 'restricting', directionAt2Ballots: 'restricting', minBallots: 1 },
  { id: 'P9', flag: 'unanimousPhase1', touches: ['phase2a.quorumPromised', 'phase2a.unanimousPromised'], direction: 'restricting', directionAt2Ballots: 'restricting', minBallots: 1 },
  { id: 'P10', flag: 'voteOnce', touches: ['phase2b.neverVoted'], direction: 'restricting', directionAt2Ballots: 'restricting', minBallots: 2 },
  { id: 'P11', flag: 'monotoneBallots', touches: ['phase1a.noGaps'], direction: 'restricting', directionAt2Ballots: 'restricting', minBallots: 2 },
];

export const CORRECT = 'C';

export function flagsFor(configId: string): Flags {
  if (configId === CORRECT) return {};
  const m = MUTANTS.find((x) => x.id === configId);
  if (!m) throw new Error(`unknown config ${configId}`);
  return { [m.flag]: true };
}

export const ALL_CONFIGS = [CORRECT, ...MUTANTS.map((m) => m.id)];

/** Which misconceptions a step-level question about a given phase can target.
 *  Determined by which action each mutant edits: P8 touches Phase2b, so it can
 *  only ever show up in a phase-2 question. */
export const PHASE1_MUTANTS = ['P5', 'P6', 'P11'];
export const PHASE2_MUTANTS = ['P1', 'P2', 'P3', 'P4', 'P7', 'P8', 'P9', 'P10'];
