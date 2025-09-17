---------------------------- MODULE Rotor ----------------------------
(***************************************************************************
 * ABSTRACT ROTOR BROADCAST MODEL (ENHANCED)
 *
 * Adds:
 *   - Erasure coding parameters (Γ, γ, κ) with over‑provision constraint (κ > 5/3)
 *   - Abstract PS-P (partition sampling) style constraints (§3.1) for relay sampling
 *   - Failure tolerance: ensure enough stake remains after worst‑case relay failures
 *   - Streaming model hooks (slices pipelined; latency optimisation for next leader)
 *   - Safety: explicit empty result if no feasible relay set exists
 *
 * NOTE: Randomness is modelled nondeterministically via CHOOSE over candidates
 * satisfying structural constraints; probabilistic properties are abstracted.
 ***************************************************************************)

EXTENDS Naturals, FiniteSets, Certificates

(***************************************************************************
 * ERASURE CODING CONSTANTS (Section 2.2)
 *   Γ (GammaTotalShreds): total shreds per slice
 *   γ (GammaDataShreds): minimum distinct shreds to reconstruct
 *   κ (KappaExpRatio): expansion ratio (Γ / γ)  — over‑provisioning > 5/3
 * Assumptions stay purely arithmetic to avoid rationals.
 ***************************************************************************)
CONSTANTS
    RotorFanout,          \* Number of relays contacted per dissemination step
    RotorMinRelayStake,   \* Minimum total stake covered by a relay set
    RotorGamma,           \* Minimum number of correct relays required for success
    GammaTotalShreds,       \* Γ > 0
    GammaDataShreds,        \* γ > 0
    KappaExpRatio,          \* κ > 1 such that Γ = κ * γ and 3*Γ > 5*γ (κ > 5/3)
    RotorMaxFailedRelayStake, \* Upper bound (stake) of relays that may fail (crash/Byz)
    MaxSlicesPerBlock

ASSUME
    /\ GammaTotalShreds \in Nat \ {0}
    /\ GammaDataShreds \in Nat \ {0}
    /\ KappaExpRatio \in Nat \ {0}
    /\ GammaTotalShreds = KappaExpRatio * GammaDataShreds
    /\ 3 * GammaTotalShreds > 5 * GammaDataShreds   \* κ > 5/3 resilience condition (Lemma 7)
    /\ GammaDataShreds < GammaTotalShreds
    /\ RotorFanout \in Nat \ {0}
    /\ RotorMinRelayStake \in Nat \ {0}
    /\ RotorMinRelayStake <= TotalStake
    /\ RotorGamma \in Nat \ {0}
    /\ RotorMaxFailedRelayStake \in Nat
    /\ RotorMaxFailedRelayStake < RotorMinRelayStake   \* Need residual stake after failures
    /\ MaxSlicesPerBlock \in Nat \ {0}

(***************************************************************************
 * DERIVED / HELPER DEFINITIONS
 ***************************************************************************)

\* Minimum residual stake required after worst allowed relay failures
RequiredResilientStake == RotorMinRelayStake

\* A set of relays is failure-resilient if even after losing up to RotorMaxFailedRelayStake
\* stake (contained inside the chosen set), the remaining stake still meets RotorMinRelayStake.
FailureResilient(sample) ==
    LET stake == CalculateStake(sample)
    IN stake >= RotorMinRelayStake /\ (stake - RotorMaxFailedRelayStake) >= RotorMinRelayStake

\* Large stakeholders per PS-P Step 1: ρ_i > 1/Γ  <=> StakeMap[v] * GammaTotalShreds > TotalStake
LargeStakeholders(S) == { v \in S : StakeMap[v] * GammaTotalShreds > TotalStake }

\* PS-P structural constraint (abstract): all large stakeholders that still need the block
\* must be included (they would deterministically occupy ⌊ρ_i Γ⌋ bins).
PSPConstraint(sample, needers) == LargeStakeholders(needers) \subseteq sample

\* Latency optimisation: include next leader early if it still needs the block.
NextLeaderConstraint(sample, needers, nextLeader) ==
    (nextLeader \in needers => nextLeader \in sample)

\* Fanout bound
FanoutConstraint(sample) == Cardinality(sample) <= RotorFanout

\* Basic non-empty requirement when dissemination needed
NonEmptyConstraint(sample, needers) == (needers # {} => sample # {})

\* Combined structural constraints (excluding feasibility check)
StructuralOK(sample, needers, nextLeader) ==
    /\ sample \subseteq needers
    /\ FanoutConstraint(sample)
    /\ NextLeaderConstraint(sample, needers, nextLeader)
    /\ PSPConstraint(sample, needers)
    /\ FailureResilient(sample)
    /\ NonEmptyConstraint(sample, needers)

\* Simple candidate relay sets that satisfy basic constraints
RotorCandidates(needers, nextLeader) ==
    {sample \in SUBSET needers :
        /\ sample # {}
        /\ Cardinality(sample) <= RotorFanout
        /\ Cardinality(sample) >= RotorGamma
        /\ (nextLeader \in needers => nextLeader \in sample)
        /\ CalculateStake(sample) >= RotorMinRelayStake}

\* Enhanced candidate relay sets with failure resilience and erasure coding
Candidates(block, needers, nextLeader) ==
    { S \in SUBSET needers : StructuralOK(S, needers, nextLeader) }

\* Feasibility predicate: some structurally valid selection exists when needed
RotorSelectionPossible(block, needers, nextLeader) ==
    IF needers = {} THEN TRUE ELSE Candidates(block, needers, nextLeader) # {}

(***************************************************************************
 * RotorSelect(block, needers, nextLeader)
 * Enhanced selection with safety fallback: returns {} iff no feasible set.
 * Randomized PS-P sampling abstracted by nondeterministic CHOOSE over candidates.
 ***************************************************************************)
RotorSelect(block, needers, nextLeader) ==
    IF needers = {} THEN {}
    ELSE LET cands == Candidates(block, needers, nextLeader)
         IN IF cands = {} THEN {} \* Explicit failure (edge case)
            ELSE CHOOSE sample \in cands : TRUE

(***************************************************************************
 * Streaming Progress (abstract): a slice is reconstructable after γ distinct
 * successful relay deliveries. We do not model individual shreds; instead we
 * expose a predicate that other modules can use if they wish.
 ***************************************************************************)
SliceReconstructable(receivedShredsCount) ==
    receivedShredsCount >= GammaDataShreds

(***************************************************************************
 * Latency Hint: next leader prioritized -> zero additional delay if included.
 * (Purely advisory; other modules may incorporate this in time progression.)
 ***************************************************************************)
NextDisseminationDelay(sample, nextLeader) == IF nextLeader \in sample THEN 0 ELSE 1

(***************************************************************************
 * Selection Safety Invariant (can be referenced elsewhere):
 * Whenever needers is non-empty and a non-empty result returned, constraints hold.
 ***************************************************************************)
RotorSelectSound(block, needers, nextLeader) ==
    LET sel == RotorSelect(block, needers, nextLeader)
    IN sel = {} /\ needers # {} => ~RotorSelectionPossible(block, needers, nextLeader)
       \/ (sel # {} /\ StructuralOK(sel, needers, nextLeader))

(***************************************************************************
 * Commentary mapping to Whitepaper
 *  - Γ, γ, κ: Erasure coding & over-provisioning (Lemma 7 requirement κ > 5/3)
 *  - LargeStakeholders + PSPConstraint: Step 1 of Definition 46 (PS-P)
 *  - FailureResilient: Ensures sufficient residual stake after crashes/faults
 *  - NextDisseminationDelay + NextLeaderConstraint: “send to next leader first”
 *  - SliceReconstructable: abstracts Reed–Solomon recovery threshold
 ***************************************************************************)

=============================================================================
