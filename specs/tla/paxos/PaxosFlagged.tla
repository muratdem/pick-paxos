-------------------------- MODULE PaxosFlagged --------------------------
(***************************************************************************)
(* Single-decree Paxos, following Lamport's Paxos.tla from the TLA+        *)
(* Examples repository, with each mutation exposed as a CONSTANT flag.     *)
(*                                                                         *)
(* With every flag FALSE this must be behaviourally identical to the       *)
(* pristine spec; `npm run crosscheck` asserts that, because nothing else  *)
(* checks that adding the flag machinery left the one configuration        *)
(* everything rests on untouched (DESIGN.md §10.2 item 4).                 *)
(*                                                                         *)
(* This file is the semantic source of truth. If it and the TypeScript     *)
(* model disagree, the TypeScript is wrong.                                *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Acceptors, Values, MaxBallot, None

\* One flag per mutant (DESIGN.md §5.3). Exactly one is TRUE per run.
CONSTANTS OwnValue,            \* P1  Phase2a ignores reported votes
          AnyReported,         \* P2  Phase2a may pick any reported value
          NoQuorumPhase1,      \* P3  one promise is enough to propose
          IgnorePromise,       \* P4  Phase2b drops the promise check
          ForgetfulPromise,    \* P5  Phase1b reports no prior vote
          NoPromiseUpdate,     \* P6  Phase1b does not raise maxBal
          MultiProposalPerBallot, \* P7 two proposals may share a ballot
          StrictAccept,        \* P8  Phase2b requires strictly greater
          UnanimousPhase1,     \* P9  all acceptors must promise
          VoteOnce,            \* P10 an acceptor votes at most once ever
          MonotoneBallots      \* P11 ballots must be used in order

Ballots == 0..MaxBallot
Quorums == {Q \in SUBSET Acceptors : Cardinality(Q) * 2 > Cardinality(Acceptors)}

\* None is a CONSTANT, not `CHOOSE v : v \notin Values`: TLC cannot evaluate an
\* unbounded CHOOSE, and the model value is clearer anyway.
ASSUME None \notin Values

VARIABLES maxBal, maxVBal, maxVal, msgs
vars == <<maxBal, maxVBal, maxVal, msgs>>

Messages ==
       [type : {"1a"}, bal : Ballots]
  \cup [type : {"1b"}, acc : Acceptors, bal : Ballots,
        mbal : Ballots \cup {-1}, mval : Values \cup {None}]
  \cup [type : {"2a"}, bal : Ballots, val : Values]
  \cup [type : {"2b"}, acc : Acceptors, bal : Ballots, val : Values]

TypeOK == /\ maxBal  \in [Acceptors -> Ballots \cup {-1}]
          /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
          /\ maxVal  \in [Acceptors -> Values \cup {None}]
          /\ msgs \subseteq Messages

Send(m) == msgs' = msgs \cup {m}

Init == /\ maxBal  = [a \in Acceptors |-> -1]
        /\ maxVBal = [a \in Acceptors |-> -1]
        /\ maxVal  = [a \in Acceptors |-> None]
        /\ msgs = {}

(***************************************************************************)
(* Phase 1a.  P11 adds an ordering constraint that real Paxos does not     *)
(* have.                                                                   *)
(***************************************************************************)
Phase1a(b) ==
  /\ \/ ~MonotoneBallots
     \/ b = 0
     \/ \E m \in msgs : m.type = "1a" /\ m.bal = b - 1
  /\ Send([type |-> "1a", bal |-> b])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

(***************************************************************************)
(* Phase 1b.  P5 strips the report out of the promise; P6 stops the        *)
(* promise from binding.                                                   *)
(***************************************************************************)
Phase1b(a) ==
  /\ \E m \in msgs :
       /\ m.type = "1a"
       /\ m.bal > maxBal[a]
       /\ IF NoPromiseUpdate
            THEN UNCHANGED maxBal
            ELSE maxBal' = [maxBal EXCEPT ![a] = m.bal]
       /\ IF ForgetfulPromise
            THEN Send([type |-> "1b", acc |-> a, bal |-> m.bal,
                       mbal |-> -1, mval |-> None])
            ELSE Send([type |-> "1b", acc |-> a, bal |-> m.bal,
                       mbal |-> maxVBal[a], mval |-> maxVal[a]])
  /\ UNCHANGED <<maxVBal, maxVal>>

(***************************************************************************)
(* Phase 2a.  The value-selection disjunct is the heart of the protocol:   *)
(* P1 removes it, P2 weakens it to "any reported value".                   *)
(***************************************************************************)
Phase2a(b, v) ==
  /\ \/ MultiProposalPerBallot
     \/ ~ \E m \in msgs : (m.type = "2a") /\ (m.bal = b)
  /\ \E Q \in Quorums :
       LET Q1b  == {m \in msgs : /\ m.type = "1b"
                                 /\ m.acc \in Q
                                 /\ m.bal = b}
           Q1bv == {m \in Q1b : m.mbal >= 0}
       IN  /\ \/ /\ NoQuorumPhase1
                 /\ \E a \in Q : \E m \in Q1b : m.acc = a
              \/ /\ UnanimousPhase1
                 /\ \A a \in Acceptors :
                      \E m \in msgs : m.type = "1b" /\ m.acc = a /\ m.bal = b
              \/ /\ ~NoQuorumPhase1 /\ ~UnanimousPhase1
                 /\ \A a \in Q : \E m \in Q1b : m.acc = a
           /\ \/ OwnValue
              \/ /\ AnyReported /\ ~OwnValue
                 /\ \/ Q1bv = {}
                    \/ \E m \in Q1bv : m.mval = v
              \/ /\ ~OwnValue /\ ~AnyReported
                 /\ \/ Q1bv = {}
                    \/ \E m \in Q1bv : /\ m.mval = v
                                       /\ \A mm \in Q1bv : m.mbal >= mm.mbal
  /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

(***************************************************************************)
(* Phase 2b.  P4 drops the promise check, P8 makes it strict, P10 lets an  *)
(* acceptor vote only once.                                                *)
(***************************************************************************)
Phase2b(a) ==
  \E m \in msgs :
    /\ m.type = "2a"
    /\ \/ /\ StrictAccept /\ m.bal > maxBal[a]
       \/ /\ IgnorePromise /\ ~StrictAccept
       \/ /\ ~StrictAccept /\ ~IgnorePromise /\ m.bal >= maxBal[a]
    /\ \/ ~VoteOnce
       \/ maxVBal[a] = -1
    /\ maxBal'  = [maxBal  EXCEPT ![a] = m.bal]
    /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
    /\ maxVal'  = [maxVal  EXCEPT ![a] = m.val]
    /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val])

Next == \/ \E b \in Ballots : \/ Phase1a(b)
                              \/ \E v \in Values : Phase2a(b, v)
        \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Chosen, and the safety property.                                        *)
(***************************************************************************)
VotedForIn(a, v, b) == \E m \in msgs : /\ m.type = "2b"
                                       /\ m.acc = a
                                       /\ m.bal = b
                                       /\ m.val = v

ChosenIn(v, b) == \E Q \in Quorums : \A a \in Q : VotedForIn(a, v, b)
Chosen(v) == \E b \in Ballots : ChosenIn(v, b)

Agreement == \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => (v1 = v2)

=============================================================================
