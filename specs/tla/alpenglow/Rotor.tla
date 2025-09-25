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
\* Parameter semantics:
\*  - Units: RotorMinRelayStake and RotorMaxFailedRelayStake use the same stake units
\*    as StakeMap/TotalStake (Certificates.tla). In the MC harness, TotalStake = 100
\*    (percent-style normalization), so values like 40 and 10 read as percentages.
\*  - Relation to γ and κ (Γ/γ): These parameters act as an explicit robustness
\*    guard for relay selection, complementing the whitepaper’s success condition
\*    (≥γ correct relays). They are not directly bound to γ or κ here; calibrate
\*    them per model goals if needed (e.g., to target a desired failure tolerance).

(***************************************************************************
 * PS-P ALGORITHM IMPLEMENTATION (Definition 46)
 * Key insight: Model relay selection as bin assignments (functions) to capture
 * multiplicity correctly. Large stakeholders can occupy multiple bins.
 * 
 * Step 1: Deterministic inclusion - ⌊ρᵢ * Γ⌋ bins per large stakeholder
 * Step 2: Partition remaining stakes into remaining bins  
 * Step 3: Sample one node per remaining bin proportionally
 ***************************************************************************)

\* DeterministicBinCount preconditions (typing/totality documentation):
\*  - StakeMap ∈ [Validators → Nat{0}] (Certificates.tla)
\*  - Validators # {} (Messages.tla) ⇒ TotalStake > 0 (division safe)
\* These are assumed globally and ensure PS‑P Step 1 arithmetic is well-defined.
\* PS-P Step 1: Calculate deterministic bin count for a node
\* Returns ⌊(stake_fraction * Γ)⌋ where stake_fraction = StakeMap[v] / TotalStake
DeterministicBinCount(v) ==
    (StakeMap[v] * GammaTotalShreds) \div TotalStake

\* Large stakeholders helper used across the module.
\* PS-P Step 1 alignment note: ⌊ρ_v · Γ⌋ ≥ 1 ⇔ ρ_v ≥ 1/Γ; this reconciles the
\* strict “> 1/Γ” phrasing in prose with the Σ⌊ρ_i·Γ⌋ arithmetic for k.
LargeStakeholders(S) == { v \in S : DeterministicBinCount(v) >= 1 }

\* Large stakeholders per PS-P Step 1 (Definition 46): those with
\* ⌊ρ_v · Γ⌋ ≥ 1, i.e., ρ_v ≥ 1/Γ. Using the bin-count test with integer
\* division makes the boundary explicit and keeps k = Γ − Σ⌊ρ_i · Γ⌋ consistent
\* with deterministic assignments (the equality case ρ = 1/Γ is included).
LargeStakeholdersInNeeders(needers) == LargeStakeholders(needers)

\* Total deterministic bins occupied by large stakeholders (PS-P Step 1)
\* Exact: Σ_{v ∈ needers} ⌊ρ_v · Γ⌋
TotalDeterministicBins(needers) ==
    LET RECURSIVE SumDet(_)
        SumDet(S) ==
            IF S = {} THEN 0
            ELSE LET v == CHOOSE x \in S : TRUE IN
                 DeterministicBinCount(v) + SumDet(S \ {v})
    IN SumDet(needers)

\* Exact total deterministic bins occupied by large stakeholders (PS-P Step 1)
\* Exact per Definition 46: Σ_{v ∈ large} ⌊ρ_v · Γ⌋, capped by Γ
TotalDeterministicBinsExact(needers) ==
    LET large == LargeStakeholdersInNeeders(needers)
        RECURSIVE SumDet(_)
        SumDet(S) ==
            IF S = {} THEN 0
            ELSE LET v == CHOOSE x \in S : TRUE IN
                 DeterministicBinCount(v) + SumDet(S \ {v})
        total == SumDet(large)
    IN IF total >= GammaTotalShreds THEN GammaTotalShreds ELSE total

\* Remaining bins after deterministic assignments
RemainingBins(needers) ==
    LET deterministicTotal == TotalDeterministicBinsExact(needers)
    IN IF deterministicTotal >= GammaTotalShreds 
       THEN 0 
       ELSE GammaTotalShreds - deterministicTotal

\* Note: We instantiate PS-P over `needers` (validators that still need the slice),
\* not the entire validator set. This aligns with Rotor's operational constraint
\* to only choose relays from nodes that do not yet have the block.
\* Consistency with the whitepaper’s wording “other nodes that still need it”
\* (alpenglow-whitepaper.md:384–386): the current leader is not a needer.
\* In MainProtocol, the leader records the new block upon proposal, ensuring
\* leader ∉ needers by construction.

\* Supporting bound: Σ_{v} ⌊ρ_v · Γ⌋ ≤ Γ ensures non-negativity above.
THEOREM DeterministicBinsBound == TotalDeterministicBinsExact(DOMAIN StakeMap) <= GammaTotalShreds

\* Helper: Check if PS-P bin assignment is feasible
PSPBinAssignmentPossible(needers, nextLeader) ==
    LET largeStakeholders == LargeStakeholdersInNeeders(needers)
        remainingNeeders == needers \ largeStakeholders
        remainingBins == RemainingBins(needers)
        deterministicTotal == TotalDeterministicBinsExact(needers)
    IN /\ deterministicTotal <= GammaTotalShreds
       /\ (nextLeader \in needers => 
           nextLeader \in largeStakeholders \/ nextLeader \in remainingNeeders)

\* Deterministic bin indices (first d bins are PS-P Step 1 allocations)
DeterministicIndices(needers) == 1..TotalDeterministicBinsExact(needers)

\* Bin assignment function: maps each bin [1..Γ] to a node
\* Implements PS-P Step 1 exactly (per-validator multiplicities), then models
\* Steps 2–3 with an abstract partitioning witness over non‑large validators.
\* We avoid probabilities and keep only per‑bin eligibility (support), which is
\* sufficient to constrain choices without committing to a specific RNG.
\* Always returns a total function on domain 1..GammaTotalShreds; duplicates
\* across bins are allowed (PS‑P permits repeated selection when |needers| < Γ).

\* Partitioning witness (support only, no probabilities):
\*  - For each remaining bin j, choose a non‑empty eligible subset of
\*    remaining (non‑large) needers.
\*  - If there are no non‑large needers, we fall back to choosing from
\*    all needers for the remaining bins, preserving PS‑P's allowance of
\*    duplicates.
PartitionWeights(needers) ==
    LET largeStakeholders == LargeStakeholdersInNeeders(needers)
        remainingNeeders == needers \ largeStakeholders
        d == TotalDeterministicBinsExact(needers)
        idx == (d + 1)..GammaTotalShreds
    IN IF idx = {}
       THEN [ j \in {} |-> [ v \in remainingNeeders |-> 0 ] ]
       ELSE IF remainingNeeders = {}
            THEN [ j \in idx |-> [ v \in remainingNeeders |-> 0 ] ]
            ELSE CHOOSE part \in [ idx -> [ remainingNeeders -> Nat ] ] :
                    /\ \A j \in idx : \E v \in remainingNeeders : part[j][v] > 0

EligibleInBin(part, j) == { v \in DOMAIN part[j] : part[j][v] > 0 }
PSPBinAssignment(needers, nextLeader) ==
    \* Always returns a total function on 1..Γ. Duplicates across bins are allowed
    \* (PS-P permits repeated selection when |needers| < Γ), and Step 2/3 sampling
    \* is modeled via per-bin eligibility (PartitionWeights), not probabilities.
    LET largeStakeholders == LargeStakeholdersInNeeders(needers)
        remainingNeeders == needers \ largeStakeholders
        deterministicTotal == TotalDeterministicBinsExact(needers)
        part == PartitionWeights(needers)
         detBins ==
             IF deterministicTotal = 0 THEN [j \in {} |-> CHOOSE v \in needers : TRUE]
             ELSE 
                 \* Choose an arbitrary function that assigns exact multiplicities
                 CHOOSE f \in [1..deterministicTotal -> largeStakeholders] :
                     \A v \in largeStakeholders :
                         Cardinality({ i \in 1..deterministicTotal : f[i] = v }) = DeterministicBinCount(v)
    IN [j \in 1..GammaTotalShreds |-> 
        IF j \in 1..deterministicTotal /\ largeStakeholders # {} THEN
            \* Deterministic allocations first, honoring exact multiplicities
            detBins[j]
        ELSE IF remainingNeeders # {} THEN
            \* Partitioned sampling for remaining bins (PS‑P Steps 2–3, support only)
            IF nextLeader \in remainingNeeders /\ j = deterministicTotal + 1 /\
               nextLeader \in EligibleInBin(part, j)
            THEN nextLeader
            ELSE CHOOSE v \in EligibleInBin(part, j) : TRUE
        ELSE
            \* Fallback: if no non-large needers exist, choose any needer (duplicates allowed)
            IF nextLeader \in needers /\ j = deterministicTotal + 1
            THEN nextLeader
            ELSE CHOOSE v \in needers : TRUE]

\* Convert bin assignment to relay set (distinct relays)
\* Note: This collapses per-bin multiplicity into the set of distinct relays.
\* Success (Definition 6) and resilience checks are over distinct correct relays.
BinsToRelaySet(bins) ==
    { bins[j] : j \in DOMAIN bins }

\* Minimum residual stake required after worst allowed relay failures.
\* Alias of `RotorMinRelayStake` for clarity and compatibility.
RequiredResilientStake == RotorMinRelayStake

\* A set of relays is failure-resilient if even after losing up to
\* RotorMaxFailedRelayStake stake (inside the chosen set), the remaining
\* stake still meets RotorMinRelayStake.
\* Simplified for clarity: equivalent single constraint.
FailureResilient(sample) ==
    CalculateStake(sample) >= RotorMinRelayStake + RotorMaxFailedRelayStake

\* PS-P structural constraint: verify bin assignment correctness
\* - Exactly Γ bins assigned and range within needers
\* - Enforce PS-P Step 1 multiplicities exactly over the deterministic prefix
\*   (allows additional probabilistic assignments for large stakeholders beyond Step 1)
PSPConstraint(bins, needers) == 
    /\ DOMAIN bins = 1..GammaTotalShreds
    /\ \A j \in DOMAIN bins : bins[j] \in needers
    /\ \A v \in LargeStakeholdersInNeeders(needers) :
          Cardinality({ j \in 1..TotalDeterministicBinsExact(needers) : bins[j] = v }) = DeterministicBinCount(v)

\* Latency optimisation: include next leader early if it still needs the block.
\* Updated to work with bin assignments
NextLeaderConstraint(bins, needers, nextLeader) ==
    (nextLeader \in needers => \E j \in DOMAIN bins : bins[j] = nextLeader)

\* Exact bin assignment constraint - exactly Γ bins assigned
ExactBinAssignmentConstraint(bins) == DOMAIN bins = 1..GammaTotalShreds

\* Combined structural constraints for whitepaper-compliant bin assignments
StructuralBinOK(bins, needers, nextLeader) ==
    /\ ExactBinAssignmentConstraint(bins)        \* Exactly Γ bins (Section 2.2)
    /\ PSPConstraint(bins, needers)              \* PS-P compliance (§3.1)
    /\ NextLeaderConstraint(bins, needers, nextLeader)  \* Optimization hint

\* Additional resilience constraint (stake-based failure tolerance)
\* Note: This is an explicit modeling guard beyond the whitepaper.
\* Guidance: set `RotorMinRelayStake` to target sufficient stake coverage
\* among selected relays, and `RotorMaxFailedRelayStake` as the maximum
\* admissible failed stake within the chosen set, so that even after
\* failures the remaining stake still meets `RotorMinRelayStake`.
ResilienceOK(sample) == FailureResilient(sample)

\* Core candidate bin assignments following whitepaper constraints
\* Intent: over-approximate PS-P feasibility by structural compliance
\* (Step 1 multiplicities + next-leader priority) plus resilience guard.
\* This is used as a feasibility/existence witness; actual selection can
\* be any member of this set (e.g., via `PSPSelect`).
BinCandidates(needers, nextLeader) ==
    { bins \in [1..GammaTotalShreds -> needers] : 
        /\ StructuralBinOK(bins, needers, nextLeader)
        /\ ResilienceOK(BinsToRelaySet(bins)) }

\* PS-P relay selection bound to structural feasibility.
\* Picks any relay set induced by a structurally valid and resilient bin assignment.
PSPSelect(needers, nextLeader) ==
    LET candBins == BinCandidates(needers, nextLeader)
        candSets == { BinsToRelaySet(b) : b \in candBins }
    IN IF candSets = {}
       THEN {}
       ELSE CHOOSE s \in candSets : TRUE


\* Feasibility predicate: some structurally valid bin assignment exists when needed
RotorBinAssignmentPossible(needers, nextLeader) ==
    IF needers = {} THEN TRUE ELSE BinCandidates(needers, nextLeader) # {}


(***************************************************************************
 * RotorSelect(block, needers, nextLeader)
 * Whitepaper-compliant relay selection: picks exactly Γ relays per slice.
 * - Implements PS-P algorithm (Definition 46) with proper bin multiplicity
 * - Deterministically includes large stakeholders in ⌊ρᵢ * Γ⌋ bins (PS-P Step 1)
 * - Partitions remaining stakes and samples per bin (PS-P Steps 2-3)
 * - Returns {} iff no feasible relay set exists (safety)
 * 
 * UPDATED: Now uses bin-based PS-P with proper multiplicity handling
 * Note: `block` is currently unused here; it remains in the signature to
 * allow referencing per-slice/block metadata in future constraints.
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
       /\ (needers # {} /\ ~RotorBinAssignmentPossible(needers, nextLeader) => sel = {})
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
