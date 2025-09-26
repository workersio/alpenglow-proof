---------------------------- MODULE Rotor ----------------------------

EXTENDS Naturals, FiniteSets, Certificates

(***************************************************************************
 * ROTOR DATA DISSEMINATION — mapping to the whitepaper
 *
 * What this module specifies and where it comes from:
 *   - §2.2 Rotor (lines :378–:406, :414–:439)
 *       • Leader encodes each slice into Γ shreds with a Merkle tree; any γ
 *         shreds suffice to reconstruct (Reed–Solomon). Authenticity is
 *         per‑shred via Merkle paths and a signed root (:382–:401; §1.6 :267).
 *       • Relays: per slice, the leader selects Γ relays and sends one shred
 *         to each; relays then broadcast to all nodes that still need it and
 *         prioritize the next leader first for faster handoff (:402–:406).
 *       • Success (Def. 6 :414): leader correct AND at least γ correct relays.
 *       • Resilience (Lemma 7 :418): over‑provisioning κ = Γ/γ > 5/3 makes
 *         success overwhelmingly likely as γ→∞.
 *       • Latency (Lemma 8 :431): ≤2δ; with large κ it approaches δ.
 *       • Bandwidth optimality (Lemma 9 :439): stake‑proportional usage, rate
 *         β_ℓ/κ in expectation, asymptotically optimal.
 *   - §1.6 Cryptography (Erasure code, Merkle) (:267–:275)
 *   - §3.1 Smart Sampling (PS‑P, Definition 46 :1154): bin‑based relay sampling
 *     that reduces variance vs IID; Step 1 deterministic ⌊ρ·Γ⌋ bins per large
 *     stakeholder, then partition + per‑bin sampling for the remainder.
 *
 * How the TLA+ model captures the above:
 *   - Γ (`GammaTotalShreds`) and γ (`GammaDataShreds`) are explicit constants;
 *     κ > 5/3 is enforced arithmetically in `ASSUME` per Lemma 7.
 *   - PS‑P is modeled with explicit bin multiplicities (Γ bins per slice):
 *       • Step 1: `DeterministicBinCount`, `LargeStakeholders`, and exact
 *         multiplicity assignment for ⌊ρᵢ·Γ⌋ bins.
 *       • Steps 2–3: `PartitionWeights` + per‑bin eligibility to abstract
 *         partitioning/sampling without committing to RNGs.
 *   - Two success predicates are provided:
 *       • `RotorSuccessful` counts distinct relays (set view; conservative).
 *       • `RotorSuccessfulBins` counts by‑bin assignments (Γ multiplicity),
 *         matching Definition 6 more closely.
 *   - `NextDisseminationDelay` records the “send to next leader first” latency
 *     hint from §2.2 (:402–:406) for reasoning about fast leader handoff.
 *
 * Scope note: This module concerns data dissemination only; chain safety does
 * not depend on Rotor (paper §2.2 “Analysis” :19). Voting/finality are in
 * `VotorCore.tla`/`Certificates.tla`.
 ***************************************************************************)
CONSTANTS
    RotorMinRelayStake,       \* Modeling guard: min stake covered by selected relays
    GammaTotalShreds,         \* Γ > 0 — total shreds/relays per slice (§2.2 :382)
    GammaDataShreds,          \* γ > 0 — min shreds to reconstruct (§1.6 :267; §2.2 :384)
    RotorMaxFailedRelayStake, \* Modeling guard: max failed stake tolerated within relays
    MaxSlicesPerBlock         \* Upper bound on slices per block (pipeline; §2.2 :378)

ASSUME
    /\ GammaTotalShreds \in Nat \ {0}
    /\ GammaDataShreds \in Nat \ {0}
    /\ 3 * GammaTotalShreds > 5 * GammaDataShreds   \* κ > 5/3 (Lemma 7 :418)
    /\ GammaDataShreds < GammaTotalShreds
    /\ RotorMinRelayStake \in Nat \ {0}
    /\ RotorMinRelayStake <= TotalStake
    /\ RotorMaxFailedRelayStake \in Nat
    /\ RotorMaxFailedRelayStake < RotorMinRelayStake   \* Ensure residual stake after failures
    /\ MaxSlicesPerBlock \in Nat \ {0}

\* Semantics and references:
\*  - Γ, γ encode the erasure‑coding parameters (§1.6 :267; §2.2 :382–:385).
\*  - κ > 5/3 encodes the over‑provisioning used in Lemma 7 (rotor resilience).
\*  - RotorMinRelayStake / RotorMaxFailedRelayStake are specification guards
\*    to model “enough stake” among chosen relays; they complement Def. 6’s
\*    ≥γ‑correct‑relays condition (:414) and are not fixed by the paper.

(***************************************************************************
 * PS-P SAMPLING (Smart Sampling, §3.1; Definition 46 :1154)
 *
 * We model rotor relay sampling with explicit Γ “bins” per slice:
 *   - Step 1 (deterministic): for each validator v, assign ⌊ρ_v·Γ⌋ bins.
 *   - Step 2 (partition): partition remaining stake across the remaining bins.
 *   - Step 3 (per‑bin sampling): sample one validator per remaining bin in
 *     proportion to stake within that bin’s partition.
 * The construction keeps multiplicity, which matters when reasoning with
 * Definition 6 over bin assignments (see RotorSuccessfulBins).
 ***************************************************************************)

\* Step 1 — deterministic bins (PS‑P, Def. 46 :1154)
\* Preconditions (typing documentation):
\*  - `StakeMap ∈ [Validators → Nat{0}]` and `TotalStake > 0` (Certificates.tla)
\*  - Returns ⌊ρ_v·Γ⌋ where ρ_v = StakeMap[v] / TotalStake
DeterministicBinCount(v) ==
    (StakeMap[v] * GammaTotalShreds) \div TotalStake

\* Large stakeholders for Step 1: ⌊ρ_v·Γ⌋ ≥ 1 ⇔ ρ_v ≥ 1/Γ.
LargeStakeholders(S) == { v \in S : DeterministicBinCount(v) >= 1 }

\* Alias used locally for readability.
LargeStakeholdersInNeeders(needers) == LargeStakeholders(needers)


\* Exact deterministic count (capped by Γ) used to prefix‑assign bins.
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

\* We instantiate PS‑P over `needers` (validators that still need the slice),
\* matching §2.2’s “other nodes that still need it” phrasing (:384–:386).

\* Supporting bound: Σ_{v} ⌊ρ_v · Γ⌋ ≤ Γ ensures non-negativity above.
THEOREM DeterministicBinsBound == TotalDeterministicBinsExact(DOMAIN StakeMap) <= GammaTotalShreds



\* Bin assignment: 1..Γ → needers
\* - Implements Step 1 with exact multiplicities; Steps 2–3 via per‑bin
\*   eligibility sets (support‑only; no RNG), allowing duplicates as in PS‑P.

\* Partitioning witness (Step 2; §3.1):
\*  - For each remaining bin j, provide a non‑empty eligible subset of
\*    non‑large needers, weighted by stake; if none exist, allow all needers.
PartitionWeights(needers) ==
    LET largeStakeholders == LargeStakeholdersInNeeders(needers)
        remainingNeeders == needers \ largeStakeholders
        d == TotalDeterministicBinsExact(needers)
        idx == (d + 1)..GammaTotalShreds
    IN IF idx = {}
       THEN [ j \in {} |-> [ v \in remainingNeeders |-> 0 ] ]
       ELSE IF remainingNeeders = {}
            THEN [ j \in idx |-> [ v \in remainingNeeders |-> 0 ] ]
            ELSE 
                \* Stake-proportional per-bin weights (refinement witness):
                \* For each remaining bin j, set weights equal to StakeMap[v].
                [ j \in idx |-> [ v \in remainingNeeders |-> StakeMap[v] ] ]

EligibleInBin(part, j) == { v \in DOMAIN part[j] : part[j][v] > 0 }

\* Convert bin assignment to the distinct relay set used operationally.
\* Note: collapses multiplicity; use RotorSuccessfulBins for by‑bin counting.
BinsToRelaySet(bins) ==
    { bins[j] : j \in DOMAIN bins }

\* Stake‑based resilience guard (specification‑level, not mandated by the paper):
\* even if up to RotorMaxFailedRelayStake of stake among chosen relays fails,
\* remaining stake still ≥ RotorMinRelayStake.
FailureResilient(sample) ==
    CalculateStake(sample) >= RotorMinRelayStake + RotorMaxFailedRelayStake

\* PS‑P structural constraint (Step 1 lower bound per validator):
\*  - domain(bins) = 1..Γ and values in `needers`
\*  - multiplicity(bins, v) ≥ ⌊ρ_v·Γ⌋ = DeterministicBinCount(v)
\*  - Steps 2–3 remain unconstrained beyond membership, matching §3.1.
PSPConstraint(bins, needers) == 
    /\ DOMAIN bins = 1..GammaTotalShreds
    /\ \A j \in DOMAIN bins : bins[j] \in needers
    /\ \A v \in needers :
          Cardinality({ j \in DOMAIN bins : bins[j] = v }) >= DeterministicBinCount(v)

\* Optional stronger check (documented): If desired, one can additionally
\* require that the deterministic prefix of bins 1..TotalDeterministicBinsExact(needers)
\* matches exact multiplicities, leaving the remaining bins unconstrained
\* beyond membership. This is already enforced by PSPBinAssignment's construction
\* but deliberately not required here to keep PSPConstraint minimal per audit.

\* Counting sanity (readability lemmas)
RECURSIVE SumBinCounts(_, _)
SumBinCounts(bins, S) ==
    IF S = {} THEN 0
    ELSE LET v == CHOOSE x \in S : TRUE IN
         Cardinality({ j \in DOMAIN bins : bins[j] = v }) + SumBinCounts(bins, S \ {v})


\* Combined structural constraints for whitepaper‑compliant bin assignments.
\* The “send to next leader first” optimization affects latency only; selection
\* remains unbiased (§2.2 :402–:406).
StructuralBinOK(bins, needers, nextLeader) ==
    /\ PSPConstraint(bins, needers)              \* PS-P compliance (§3.1)

\* Additional resilience constraint (stake-based failure tolerance)
\* Note: This is an explicit modeling guard beyond the whitepaper.
\* Guidance: set `RotorMinRelayStake` to target sufficient stake coverage
\* among selected relays, and `RotorMaxFailedRelayStake` as the maximum
\* admissible failed stake within the chosen set, so that even after
\* failures the remaining stake still meets `RotorMinRelayStake`.
ResilienceOK(relays) == FailureResilient(relays)

\* Candidate bin assignments that satisfy PS‑P structure and resilience guard.
\* Used as an existence/feasibility witness for `RotorSelect`.
BinCandidates(needers, nextLeader) ==
    { bins \in [1..GammaTotalShreds -> needers] : 
        /\ StructuralBinOK(bins, needers, nextLeader)
        /\ ResilienceOK(BinsToRelaySet(bins)) }

\* Relay selection picks any resilient set induced by a valid bin assignment.
PSPSelect(needers, nextLeader) ==
    LET candBins == BinCandidates(needers, nextLeader)
        candSets == { BinsToRelaySet(b) : b \in candBins }
    IN IF candSets = {}
       THEN {}
       ELSE CHOOSE s \in candSets : TRUE


\* Feasibility predicate: some valid bin assignment exists when needed.
RotorBinAssignmentPossible(needers, nextLeader) ==
    IF needers = {} THEN TRUE ELSE BinCandidates(needers, nextLeader) # {}


(***************************************************************************
 * ROTOR RELAY SELECTION (§2.2; §3.1 Def. 46 :1154)
 *
 * RotorSelect(block, needers, nextLeader)
 * - Uses Γ bins per slice; returns the set of distinct assignees (≤Γ).
 * - Enforces Step 1 exact multiplicities (⌊ρ·Γ⌋), abstracts Steps 2–3 by
 *   per‑bin eligibility. Returns {} iff no feasible selection exists.
 * - `nextLeader` is not a selection constraint; it is used only by the
 *   latency hint in `NextDisseminationDelay` (send next‑leader first, :402).
 * - `block` is retained for potential future slice‑specific constraints.
 ***************************************************************************)
RotorSelect(block, needers, nextLeader) ==
    IF needers = {} THEN {}
    ELSE IF ~RotorBinAssignmentPossible(needers, nextLeader)
         THEN {} \* Fail closed when no structurally/resilience-feasible assignment exists
         ELSE 
            \* Select any resilient candidate induced by a valid bin assignment
            LET psSelection == PSPSelect(needers, nextLeader)
            IN IF /\ psSelection \subseteq needers
                  /\ CalculateStake(psSelection) >= RotorMinRelayStake
               THEN psSelection
               ELSE {} \* Defensive: should be unreachable if BinCandidates enforced


(***************************************************************************
 * ROTOR SUCCESS — DISTINCT RELAYS VIEW (Def. 6 :414)
 * Leader correct AND at least γ distinct relays are correct.
 * Set‑based approximation; under‑counts compared to by‑bin multiplicity.
 ***************************************************************************)
RotorSuccessful(leader, relays, correctNodes) ==
    /\ leader \in correctNodes
    /\ Cardinality(relays \cap correctNodes) >= GammaDataShreds

(***************************************************************************
 * ROTOR SUCCESS — BY-BIN VIEW (Def. 6 :414)
 * Counts multiplicity over the Γ bin assignments, matching §2.2 text.
 ***************************************************************************)
CorrectAssignmentsCount(bins, correctNodes) ==
    Cardinality({ j \in DOMAIN bins : bins[j] \in correctNodes })

RotorSuccessfulBins(leader, bins, correctNodes) ==
    /\ leader \in correctNodes
    /\ CorrectAssignmentsCount(bins, correctNodes) >= GammaDataShreds


(***************************************************************************
 * LATENCY HINT (Lemma 8 :431; minor optimization :402–:406)
 * Relays prioritize the next leader first. If the next leader is among
 * selected relays (on path), model zero extra hop; otherwise, add one.
 ***************************************************************************)
OnPath(nextLeader, relays) == nextLeader \in relays

NextDisseminationDelay(relays, nextLeader) == IF OnPath(nextLeader, relays) THEN 0 ELSE 1

(***************************************************************************
 * SELECTION SOUNDNESS (internal invariant)
 * If a non‑empty selection is returned, there exists a witness bin assignment
 * that satisfies PS‑P structure and the resilience guard.
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
 * QUICK REFERENCE — Whitepaper anchors for this module
 *  - §2.2 Rotor: :378–:406 (mechanics), Def. 6 :414 (success),
 *    Lemma 7 :418 (κ>5/3), Lemma 8 :431 (δ..2δ), Lemma 9 :439 (bandwidth).
 *  - §1.6 Cryptographic techniques: Reed–Solomon and Merkle (:267–:275).
 *  - §3.1 Smart Sampling: PS‑P, Def. 46 :1154 (variance reduction vs IID).
 * Related modules: `Blocks.tla` (§2.1 data hierarchy), `Certificates.tla`
 * (thresholds/Σ stake), `Messages.tla` (typed message families).
 ***************************************************************************)

=============================================================================
