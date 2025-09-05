------------------------------ MODULE AG_FastCertUniq ------------------------------
EXTENDS Naturals, Integers, FiniteSets, TLC

(***************************************************************************
  Alpenglow Votor — Certificate Uniqueness (per slot)
  ---------------------------------------------------
  We model ONE slot with multiple candidate blocks {B1, B2, ...}. Validators
  cast *notarization votes* (first-round). A Fast-Finalization certificate for
  a block b exists when notarized stake ≥ 80% of total stake. A Notarization
  certificate exists when notarized stake ≥ 60% of total stake.

  Honest validators *never* cast more than one notarization vote in the slot.
  Byzantine validators may vote for multiple blocks.

  Invariants we check:
    - FastFinalUnique:   impossible for two different blocks to both reach ≥80%
    - NotarizationUnique: impossible for two different blocks to both reach ≥60%
    - HonestNonEquivocate: honest validators don't sign two different blocks

  Assumption:
    - Byzantine stake < 20% of total stake.

  These match the whitepaper thresholds (Table 6) and non-equivocation
  condition (Lemma 20), and are a required "Safety: certificate uniqueness"
  item in the task brief.
***************************************************************************)

CONSTANTS
  Validators,     \* finite set of validator ids
  Blocks,         \* finite set of candidate blocks in this slot
  Byz             \* subset of Validators (Byzantine)

\* Define Stake as a function mapping validators to their stake amounts
Stake == [v \in Validators |-> 
  IF v = 1 THEN 201 
  ELSE IF v = 5 THEN 199 
  ELSE 200]

(***************************************************************************
 We assume that (1) Byzantine nodes are always a subset of Validators, (2) 
 there is at least one Block, and (3) there is at least one Validator.
***************************************************************************)
ASSUME Byz \subseteq Validators /\ Blocks # {} /\ Validators # {}

(***************************************************************************
 Helper: sum of stakes of a finite set of validators.
***************************************************************************)
RECURSIVE Weight(_)
Weight(S) == IF S = {} THEN 0
             ELSE LET x == CHOOSE v \in S : TRUE IN
                  Stake[x] + Weight(S \ {x})

(***************************************************************************
 Byzantine stake < 20% of total stake (strict).
  Using integer arithmetic: 10 * Weight(Byz) < 2 * Weight(Validators)
***************************************************************************)
ASSUME 10 * Weight(Byz) < 2 * Weight(Validators)

Honest == Validators \ Byz

(***************************************************************************
 PlusCal harness: validators (honest/byz) keep taking steps. Honest can vote
 at most once (for any block). Byzantine may vote for any/many.
***************************************************************************)
(*--algorithm AG_FastCertUniq
variables
  votes    = [b \in Blocks |-> [i \in Validators |-> FALSE]],
  hasVoted = [i \in Validators |-> FALSE];

define
  NotarStake(b) == Weight({ i \in Validators : votes[b][i] })
  TotalStake    == Weight(Validators)
  NotarThreshold == (TotalStake * 6) \div 10
  FastThreshold  == (TotalStake * 8) \div 10
  Notarized(b) == NotarStake(b) >= NotarThreshold
  FastCert(b)  == NotarStake(b) >= FastThreshold
end define;

process HonestProc \in Honest
variables anyBlock;
begin
HLoop:
  while TRUE do
    either
      with b \in Blocks do
        if ~hasVoted[self] then
          anyBlock := b;
          votes[anyBlock][self] := TRUE;
          hasVoted[self] := TRUE;
        end if;
      end with;
    or
      skip;
    end either;
  end while;
end process;

process ByzProc \in Byz
variables anyBlock;
begin
BLoop:
  while TRUE do
    with b \in Blocks do
      anyBlock := b;
      votes[anyBlock][self] := TRUE;
    end with;
  end while;
end process;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "c2b843cd" /\ chksum(tla) = "688de1b5")
\* Process variable anyBlock of process HonestProc at line 76 col 11 changed to anyBlock_
CONSTANT defaultInitValue
VARIABLES votes, hasVoted

(* define statement *)
NotarStake(b) == Weight({ i \in Validators : votes[b][i] })
TotalStake    == Weight(Validators)
NotarThreshold == (TotalStake * 6) \div 10
FastThreshold  == (TotalStake * 8) \div 10
Notarized(b) == NotarStake(b) >= NotarThreshold
FastCert(b)  == NotarStake(b) >= FastThreshold

VARIABLES anyBlock_, anyBlock

vars == << votes, hasVoted, anyBlock_, anyBlock >>

ProcSet == (Honest) \cup (Byz)

Init == (* Global variables *)
        /\ votes = [b \in Blocks |-> [i \in Validators |-> FALSE]]
        /\ hasVoted = [i \in Validators |-> FALSE]
        (* Process HonestProc *)
        /\ anyBlock_ = [self \in Honest |-> defaultInitValue]
        (* Process ByzProc *)
        /\ anyBlock = [self \in Byz |-> defaultInitValue]

HonestProc(self) == /\ \/ /\ \E b \in Blocks:
                               IF ~hasVoted[self]
                                  THEN /\ anyBlock_' = [anyBlock_ EXCEPT ![self] = b]
                                       /\ votes' = [votes EXCEPT ![anyBlock_'[self]][self] = TRUE]
                                       /\ hasVoted' = [hasVoted EXCEPT ![self] = TRUE]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << votes, hasVoted, 
                                                       anyBlock_ >>
                       \/ /\ TRUE
                          /\ UNCHANGED <<votes, hasVoted, anyBlock_>>
                    /\ UNCHANGED anyBlock

ByzProc(self) == /\ \E b \in Blocks:
                      /\ anyBlock' = [anyBlock EXCEPT ![self] = b]
                      /\ votes' = [votes EXCEPT ![anyBlock'[self]][self] = TRUE]
                 /\ UNCHANGED << hasVoted, anyBlock_ >>

Next == (\E self \in Honest: HonestProc(self))
           \/ (\E self \in Byz: ByzProc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

(***************************************************************************
 Invariants to be model-checked by TLC.
***************************************************************************)
TypeOK ==
  /\ votes \in [Blocks -> [Validators -> BOOLEAN]]
  /\ hasVoted \in [Validators -> BOOLEAN]
  /\ anyBlock_ \in [Honest -> Blocks \union {defaultInitValue}]
  /\ anyBlock \in [Byz -> Blocks \union {defaultInitValue}]

HonestNonEquivocate ==
  \A i \in Honest :
    \A b1, b2 \in Blocks :
      (b1 # b2) => ~(votes[b1][i] /\ votes[b2][i])

FastFinalUnique ==
  \A b1, b2 \in Blocks :
    (b1 # b2) => ~ (FastCert(b1) /\ FastCert(b2))

NotarizationUnique ==
  \A b1, b2 \in Blocks :
    (b1 # b2) => ~ (Notarized(b1) /\ Notarized(b2))

============================================================================= 
