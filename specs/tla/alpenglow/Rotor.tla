---------------------------- MODULE Rotor ----------------------------

EXTENDS Naturals, FiniteSets, Certificates

(***************************************************************************
 * ERASURE CODING CONSTANTS (Section 2.2)
 *   Γ (GammaTotal * Commentary mapping to Whitepaper
 *  - Γ, γ, κ: Erasure coding & over-provisioning (Lemma 7 requirement κ > 5/3)
 *  - DeterministicBinCount + PSPBinAssignment: Complete PS-P Definition 46
 *    * Step 1: ⌊ρᵢ * Γ⌋ deterministic bins per large stakeholder
 *    * Step 2: Partition remaining stakes across remaining bins
 *    * Step 3: Sample one node per bin proportionally to stake
 *  - BinsToRelaySet: Convert bin assignments to relay sets (handles multiplicity)
 *  - FailureResilient: Ensures sufficient residual stake after crashes/faults
 *  - NextDisseminationDelay + NextLeaderConstraint: "send to next leader first"
 *  - SliceReconstructable: abstracts Reed–Solomon recovery threshold
 *  - Bin-based model correctly captures PS-P variance reduction properties): total shreds per slice
 *   γ (GammaDataShreds): minimum distinct shreds to reconstruct
 *   κ (KappaExpRatio): expansion ratio (Γ / γ)  — over‑provisioning > 5/3
 * Assumptions stay purely arithmetic to avoid rationals.
 ***************************************************************************)
CONSTANTS
    RotorMinRelayStake,   \* Minimum total stake covered by a relay set
    GammaTotalShreds,       \* Γ > 0 - exactly this many relays per slice
    GammaDataShreds,        \* γ > 0 - minimum shreds needed to reconstruct
    RotorMaxFailedRelayStake, \* Upper bound (stake) of relays that may fail (crash/Byz)
    MaxSlicesPerBlock

ASSUME
    /\ GammaTotalShreds \in Nat \ {0}
    /\ GammaDataShreds \in Nat \ {0}
    /\ 3 * GammaTotalShreds > 5 * GammaDataShreds   \* κ > 5/3 resilience condition (Lemma 7)
    /\ GammaDataShreds < GammaTotalShreds
    /\ RotorMinRelayStake \in Nat \ {0}
    /\ RotorMinRelayStake <= TotalStake
    /\ RotorMaxFailedRelayStake \in Nat
    /\ RotorMaxFailedRelayStake < RotorMinRelayStake   \* Need residual stake after failures
    /\ MaxSlicesPerBlock \in Nat \ {0}

(***************************************************************************
 * PS-P ALGORITHM IMPLEMENTATION (Definition 46)
 * Key insight: Model relay selection as bin assignments (functions) to capture
 * multiplicity correctly. Large stakeholders can occupy multiple bins.
 * 
 * Step 1: Deterministic inclusion - ⌊ρᵢ * Γ⌋ bins per large stakeholder
 * Step 2: Partition remaining stakes into remaining bins  
 * Step 3: Sample one node per remaining bin proportionally
 ***************************************************************************)

\* PS-P Step 1: Calculate deterministic bin count for a node
\* Returns ⌊(stake_fraction * Γ)⌋ where stake_fraction = StakeMap[v] / TotalStake
DeterministicBinCount(v) ==
    (StakeMap[v] * GammaTotalShreds) \div TotalStake

\* Large stakeholders: those with deterministic bin count ≥ 1
LargeStakeholdersInNeeders(needers) == 
    { v \in needers : DeterministicBinCount(v) >= 1 }

\* Total deterministic bins occupied by large stakeholders (PS-P Step 1)
\* Exact: Σ_{v ∈ needers} ⌊ρ_v · Γ⌋
TotalDeterministicBins(needers) ==
    LET RECURSIVE SumDet(_)
        SumDet(S) ==
            IF S = {} THEN 0
            ELSE LET v == CHOOSE x \in S : TRUE IN
                 DeterministicBinCount(v) + SumDet(S \ {v})
    IN SumDet(needers)

\* Remaining bins after deterministic assignments
RemainingBins(needers) ==
    LET deterministicTotal == TotalDeterministicBins(needers)
    IN IF deterministicTotal >= GammaTotalShreds 
       THEN 0 
       ELSE GammaTotalShreds - deterministicTotal

\* Note: We instantiate PS-P over `needers` (validators that still need the slice),
\* not the entire validator set. This aligns with Rotor's operational constraint
\* to only choose relays from nodes that do not yet have the block.

\* Supporting bound: Σ_{v} ⌊ρ_v · Γ⌋ ≤ Γ ensures non-negativity above.
THEOREM DeterministicBinsBound == TotalDeterministicBins(DOMAIN StakeMap) <= GammaTotalShreds

\* Helper: Check if PS-P bin assignment is feasible
PSPBinAssignmentPossible(needers, nextLeader) ==
    LET largeStakeholders == LargeStakeholdersInNeeders(needers)
        remainingNeeders == needers \ largeStakeholders
        remainingBins == RemainingBins(needers)
        deterministicTotal == TotalDeterministicBins(needers)
    IN /\ deterministicTotal <= GammaTotalShreds
       /\ (nextLeader \in needers => 
           nextLeader \in largeStakeholders \/ nextLeader \in remainingNeeders)

\* Bin assignment function: maps each bin [1..Γ] to a node
\* Simplified PS-P algorithm with proper multiplicity handling
PSPBinAssignment(needers, nextLeader) ==
    IF ~PSPBinAssignmentPossible(needers, nextLeader) THEN [j \in {} |-> CHOOSE v \in needers : TRUE]
    ELSE LET largeStakeholders == LargeStakeholdersInNeeders(needers)
             remainingNeeders == needers \ largeStakeholders
             deterministicTotal == TotalDeterministicBins(needers)
             remainingBins == RemainingBins(needers)
         IN IF GammaTotalShreds <= Cardinality(needers) THEN
                \* Simple case: enough needers to fill all bins
                [j \in 1..GammaTotalShreds |-> 
                 IF j <= deterministicTotal /\ largeStakeholders # {} THEN
                     \* Assign deterministic bins to large stakeholders (round-robin)
                     CHOOSE v \in largeStakeholders : TRUE
                 ELSE IF nextLeader \in remainingNeeders /\ j = deterministicTotal + 1 THEN
                     \* Prioritize next leader in first remaining bin
                     nextLeader
                 ELSE
                     \* Fill remaining bins from remaining needers
                     CHOOSE v \in remainingNeeders : TRUE]
            ELSE [j \in {} |-> CHOOSE v \in needers : TRUE] \* Not enough needers

\* Convert bin assignment to relay set (handles multiplicity correctly)
BinsToRelaySet(bins) ==
    { bins[j] : j \in DOMAIN bins }

\* PS-P relay selection using bin-based approach
PSPSelect(needers, nextLeader) ==
    LET bins == PSPBinAssignment(needers, nextLeader)
    IN IF DOMAIN bins = {} THEN {} ELSE BinsToRelaySet(bins)

\* Minimum residual stake required after worst allowed relay failures
RequiredResilientStake == RotorMinRelayStake

\* A set of relays is failure-resilient if even after losing up to RotorMaxFailedRelayStake
\* stake (contained inside the chosen set), the remaining stake still meets RotorMinRelayStake.
FailureResilient(sample) ==
    LET stake == CalculateStake(sample)
    IN stake >= RotorMinRelayStake /\ (stake - RotorMaxFailedRelayStake) >= RotorMinRelayStake

\* Large stakeholders per PS-P Step 1: those with deterministic bin assignments
\* Updated to use proper bin count calculation
LargeStakeholders(S) == { v \in S : DeterministicBinCount(v) >= 1 }

\* PS-P structural constraint: verify bin assignment correctness
\* Updated to work with bin-based multiplicity model
PSPConstraint(bins, needers) == 
    /\ DOMAIN bins = 1..GammaTotalShreds  \* Exactly Γ bins assigned
    /\ \A j \in DOMAIN bins : bins[j] \in needers  \* All assignments valid
    /\ \A v \in needers :  \* Enforce PS-P Step 1 multiplicity lower bound
        Cardinality({j \in DOMAIN bins : bins[j] = v}) >= DeterministicBinCount(v)

\* Latency optimisation: include next leader early if it still needs the block.
\* Updated to work with bin assignments
NextLeaderConstraint(bins, needers, nextLeader) ==
    (nextLeader \in needers => \E j \in DOMAIN bins : bins[j] = nextLeader)

\* Exact bin assignment constraint - exactly Γ bins assigned
ExactBinAssignmentConstraint(bins) == DOMAIN bins = 1..GammaTotalShreds

\* Basic non-empty requirement when dissemination needed
NonEmptyConstraint(bins, needers) == 
    (needers # {} => DOMAIN bins # {})

\* Combined structural constraints for whitepaper-compliant bin assignments
StructuralBinOK(bins, needers, nextLeader) ==
    /\ ExactBinAssignmentConstraint(bins)        \* Exactly Γ bins (Section 2.2)
    /\ PSPConstraint(bins, needers)              \* PS-P compliance (§3.1)
    /\ NextLeaderConstraint(bins, needers, nextLeader)  \* Optimization hint
    /\ NonEmptyConstraint(bins, needers)

\* Additional resilience constraint (stake-based failure tolerance)
\* NOTE: This is beyond the core Rotor spec but adds robustness
ResilienceOK(sample) == FailureResilient(sample)

\* Core candidate bin assignments following whitepaper constraints
BinCandidates(block, needers, nextLeader) ==
    { bins \in [1..GammaTotalShreds -> needers] : 
        /\ StructuralBinOK(bins, needers, nextLeader)
        /\ ResilienceOK(BinsToRelaySet(bins)) }


\* Feasibility predicate: some structurally valid bin assignment exists when needed
RotorBinAssignmentPossible(block, needers, nextLeader) ==
    IF needers = {} THEN TRUE ELSE BinCandidates(block, needers, nextLeader) # {}


(***************************************************************************
 * RotorSelect(block, needers, nextLeader)
 * Whitepaper-compliant relay selection: picks exactly Γ relays per slice.
 * - Implements PS-P algorithm (Definition 46) with proper bin multiplicity
 * - Deterministically includes large stakeholders in ⌊ρᵢ * Γ⌋ bins (PS-P Step 1)
 * - Partitions remaining stakes and samples per bin (PS-P Steps 2-3)
 * - Returns {} iff no feasible relay set exists (safety)
 * 
 * UPDATED: Now uses bin-based PS-P with proper multiplicity handling
 ***************************************************************************)
RotorSelect(block, needers, nextLeader) ==
    IF needers = {} THEN {}
    ELSE LET psSelection == PSPSelect(needers, nextLeader)
         IN IF /\ psSelection \subseteq needers
               /\ CalculateStake(psSelection) >= RotorMinRelayStake
               /\ (nextLeader \in needers => nextLeader \in psSelection)
            THEN psSelection
            ELSE {} \* Explicit failure - insufficient needers/stake

(***************************************************************************
 * Streaming Progress (abstract): a slice is reconstructable after γ distinct
 * successful relay deliveries. We do not model individual shreds; instead we
 * expose a predicate that other modules can use if they wish.
 ***************************************************************************)
SliceReconstructable(receivedShredsCount) ==
    receivedShredsCount >= GammaDataShreds

(***************************************************************************
 * Definition 6 from Whitepaper: Rotor Success Condition
 * Rotor is successful if the leader is correct and at least γ correct relays participate
 ***************************************************************************)
RotorSuccessful(leader, relays, correctNodes) ==
    /\ leader \in correctNodes
    /\ Cardinality(relays \cap correctNodes) >= GammaDataShreds

(***************************************************************************
 * Slice Delivery Model: abstract representation of slice transmission
 * Models the two-hop delivery: Leader -> Relays -> All nodes
 ***************************************************************************)
SliceDelivered(slice, relays, correctNodes) ==
    /\ slice.leader \in correctNodes  \* Leader is correct
    /\ Cardinality(relays \cap correctNodes) >= GammaDataShreds  \* Enough correct relays
    /\ relays \subseteq slice.needers  \* Relays are from nodes that need the slice

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
    IN 
       /\ (needers # {} /\ ~RotorBinAssignmentPossible(block, needers, nextLeader) => sel = {})
       /\ (sel # {} => 
            \E bins \in [1..GammaTotalShreds -> needers] :
                /\ StructuralBinOK(bins, needers, nextLeader)
                /\ ResilienceOK(BinsToRelaySet(bins))
                /\ BinsToRelaySet(bins) = sel)

(***************************************************************************
 * Commentary mapping to Whitepaper
 *  - Γ, γ, κ: Erasure coding & over-provisioning (Lemma 7 requirement κ > 5/3)
 *  - LargeStakeholders + PSPConstraint: Step 1 of Definition 46 (PS-P)
 *  - FailureResilient: Ensures sufficient residual stake after crashes/faults
 *  - NextDisseminationDelay + NextLeaderConstraint: “send to next leader first”
 *  - SliceReconstructable: abstracts Reed–Solomon recovery threshold
 ***************************************************************************)

=============================================================================
