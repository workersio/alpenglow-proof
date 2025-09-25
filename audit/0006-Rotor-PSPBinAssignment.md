# Audit: Rotor.PSPBinAssignment (PS-P Bin Assignment)

## 1. Code Under Audit

```tla
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
            ELSE [j \in {} |-> CHOOSE v \in needers : TRUE]
```

Implementation location: `specs/tla/alpenglow/Rotor.tla:91`.

Referenced helpers and constants (same module unless noted):
- `PSPBinAssignmentPossible(needers, nextLeader)`: `specs/tla/alpenglow/Rotor.tla:79`
- `LargeStakeholdersInNeeders(needers)`: `specs/tla/alpenglow/Rotor.tla:56`
- `TotalDeterministicBins(needers)`: `specs/tla/alpenglow/Rotor.tla:61`
- `RemainingBins(needers)`: `specs/tla/alpenglow/Rotor.tla:72`
- `GammaTotalShreds` (Γ): `specs/tla/alpenglow/Rotor.tla:24`
- `Cardinality(·)` from FiniteSets; `CHOOSE` is standard TLA+ choice
- Stake primitives: `StakeMap`, `TotalStake` in Certificates: `specs/tla/alpenglow/Certificates.tla:34,65`
- Downstream: `PSPSelect` uses this to produce a relay set: `specs/tla/alpenglow/Rotor.tla:116`

## 2. Whitepaper Sections and References

- Definition 46 (Partition Sampling, PS-P): `alpenglow-whitepaper.md:1154`–`alpenglow-whitepaper.md:1160`
  - Step 1: For each node with ρᵢ > 1/Γ, fill ⌊ρᵢ·Γ⌋ deterministic bins: `alpenglow-whitepaper.md:1156`
  - Step 2: Partition remaining stakes into k = Γ − Σᵢ ⌊ρᵢ·Γ⌋ bins: `alpenglow-whitepaper.md:1157`
  - Step 3: From each bin, sample one node proportional to stake: `alpenglow-whitepaper.md:1158`
- Definition 45 (Partitioning formalization): `alpenglow-whitepaper.md:1143`–`alpenglow-whitepaper.md:1152`
- Minor optimization: relays prioritize the next leader: `alpenglow-whitepaper.md:386`
- Erasure coding constants (Γ, γ, κ) context: `alpenglow-whitepaper.md:267`; resilience bound κ > 5/3 (Lemma 7): `alpenglow-whitepaper.md:418`

## 3. Reasoning and Alignment with the Whitepaper

Intended behavior per paper (PS-P):
- Step 1 deterministically assigns exactly ⌊ρᵢ·Γ⌋ bins to each “large” node i (ρᵢ ≥ 1/Γ).
- Step 2 computes remaining bins k = Γ − Σᵢ ⌊ρᵢ·Γ⌋ and partitions residual stakes across these k bins.
- Step 3 samples one node per remaining bin, with probability proportional to residual stake in that bin.
- Duplicates across bins are allowed; PS‑P does not require Γ distinct nodes.

What the spec encodes:
- Structure: returns a bin assignment `bins ∈ [1..Γ -> needers]` when feasible; else returns an empty-domain function as a failure sentinel.
- Deterministic portion: for bins `j ≤ deterministicTotal`, picks `CHOOSE v ∈ largeStakeholders : TRUE` (commented as “round-robin” but not implemented), i.e., the same nondeterministically chosen large stakeholder for all deterministic bins.
- Next-leader prioritization: if `nextLeader ∈ remainingNeeders`, fixes `bins[deterministicTotal+1] = nextLeader`.
- Remaining bins: fills with `CHOOSE v ∈ remainingNeeders : TRUE` (uniform, not stake‑proportional; no partition witness).
- Feasibility guards: requires `PSPBinAssignmentPossible`, which includes `remainingBins ≤ Cardinality(remainingNeeders)`. Also requires `GammaTotalShreds ≤ Cardinality(needers)` to proceed; otherwise returns empty.

Key divergences from Definition 46:
- Exact multiplicities missing: Step 1 requires per‑validator multiplicity `Cardinality({ j : bins[j] = v }) = ⌊ρ_v·Γ⌋`. The spec only ensures (elsewhere) “≥ 1 bin per large stakeholder” via `PSPConstraint`; here it does not enforce counts, and the j‑invariant `CHOOSE` concentrates all deterministic bins on a single arbitrary large stakeholder.
- Remaining bins not stake‑proportional: Step 2/3’s partitioning and weighted sampling are abstracted away; the code uniformly `CHOOSE`s from `remainingNeeders`, losing the proportionality to residual stakes and any partitioning structure.
- Unnecessary uniqueness assumptions: Guards `GammaTotalShreds ≤ |needers|` and `remainingBins ≤ |remainingNeeders|` imply a one‑to‑one filling of bins by distinct nodes. PS‑P allows a node to appear in multiple bins; these guards can wrongly mark feasible PS‑P assignments as infeasible.
- Interaction with `TotalDeterministicBins`: that helper currently under‑approximates Σᵢ ⌊ρᵢ·Γ⌋ by `|largeStakeholders|` (see audit 0005). This inflates `remainingBins`, further distorting the Step 1/2 split and feasibility decisions.

What remains consistent:
- The threshold ρ ≥ 1/Γ for “large” is modeled via `DeterministicBinCount` and `LargeStakeholdersInNeeders`.
- Next-leader prioritization matches the whitepaper optimization (“send to next leader first”), albeit encoded as a fixed bin index rather than the weaker existential constraint.

## 4. Conclusion of the Audit

- PSPBinAssignment does not faithfully implement PS‑P (Definition 46):
  - It neither enforces nor constructs the exact per‑validator deterministic multiplicities ⌊ρᵢ·Γ⌋.
  - It omits the partitioning witness and stake‑proportional sampling for remaining bins.
  - It imposes non‑paper guards that forbid duplicates, rejecting feasible PS‑P outcomes.
- As written, it yields valid bin functions syntactically, but can produce assignments that do not correspond to any PS‑P result, and can reject valid PS‑P instantiations. This is a material divergence from the whitepaper abstraction.
- Safety is not directly harmed (the function can fail closed), but fidelity to the probabilistic guarantees and variance‑reduction properties of PS‑P is compromised.

## 5. Open Questions or Concerns

- Is the intent to keep a high‑level abstraction (existential/nondeterministic) or to model PS‑P precisely enough to reason about multiplicities and variance bounds (Lemma 47/Theorem 3)? The current form is too coarse for the latter.
- Should duplicates across bins be allowed in the model (as in PS‑P) or intentionally disallowed to model distinct relays only? If disallowed, the spec should document this deviation and justify its impact on resilience/latency claims.
- How should stake‑proportional sampling be abstracted? Minimal correctness would require at least a partition witness with eligibility (non‑zero share → eligible) rather than uniform `CHOOSE`.
- The comment says “round‑robin” for deterministic bins, but the code uses a j‑invariant `CHOOSE`. Is round‑robin intended to be modeled or is it purely an implementation hint?
- Does `BinsToRelaySet` collapsing multiplicities to a set interact correctly with resilience checks (`CalculateStake`)? It avoids double‑counting stake, but then uniqueness guards may not be necessary if multiplicity is allowed at the bin level.

## 6. Suggestions for Improvement

- Enforce exact deterministic multiplicities (Step 1):
  ```tla
  LargeMultiplicity(v) == DeterministicBinCount(v)
  PSPDeterministicOK(bins, needers) ==
      \A v \in needers :
          LET m == LargeMultiplicity(v)
          IN IF m = 0 THEN TRUE
             ELSE Cardinality({ j \in DOMAIN bins : bins[j] = v }) = m
  ```

- Construct deterministic bins explicitly (sketch):
  ```tla
  DeterministicBins(needers) ==
      LET large == { v \in needers : DeterministicBinCount(v) >= 1 }
          RECURSIVE Fill(_,_)
          Fill(S, idx) ==
              IF S = {} THEN [ i \in 1..0 |-> CHOOSE w \in needers : TRUE ]
              ELSE LET v == CHOOSE x \in S : TRUE
                       m == DeterministicBinCount(v)
                       this == [ i \in 1..m |-> v ]
                   IN [this EXCEPT !] \o Fill(S \ {v}, idx + m)
      IN (* concatenate per‑v repetitions into a length Σ ⌊ρ·Γ⌋ sequence *)
  ```
  Then place these values at positions `1..Σ ⌊ρ·Γ⌋` in `bins`.

- Model Step 2 partitioning abstractly and gate sampling by eligibility:
  ```tla
  \* Abstract partition witness: for each remaining bin j, a map of shares summing to 1
  PartitionOK(part, remain, cand) ==
      /\ DOMAIN part = 1..remain
      /\ \A j \in DOMAIN part :
            /\ part[j] \in [cand -> Real]
            /\ \A v \in cand : part[j][v] >= 0
            /\ (\E S \in SUBSET cand : TRUE) /\ (* nonempty *)
            /\ Sum(part[j]) = 1
  EligibleInBin(part, j) == { v \in DOMAIN part[j] : part[j][v] > 0 }

  \* Sample only from eligible validators for each remaining bin
  [ j \in (deterministicTotal+1)..GammaTotalShreds |->
      CHOOSE v \in EligibleInBin(part, j) : TRUE ]
  ```
  This avoids modeling probabilities while preserving the support (who can be chosen).

- Remove non-paper uniqueness guards:
  - Drop `GammaTotalShreds ≤ Cardinality(needers)` and `remainingBins ≤ Cardinality(remainingNeeders)` in feasibility, since PS‑P allows duplicates across bins.

- Strengthen structural constraints and selection wiring:
  - Require `StructuralBinOK(bins, ...)` to include `PSPDeterministicOK` (exact multiplicities per Step 1).
  - Have `PSPSelect`/`RotorSelect` pick from `BinCandidates` and return `BinsToRelaySet(bins)` only when such a `bins` witness exists (or otherwise return {}). This aligns the constructed selection with the structural constraints actually checked.

- Document explicitly any intentional deviations (e.g., forbidding duplicates) and analyze their impact relative to the whitepaper’s variance and resilience claims (Definition 46, Lemma 47, Theorem 3).

---

In summary, PSPBinAssignment currently simplifies away critical parts of PS‑P (exact deterministic multiplicities and stake‑proportional sampling) and adds uniqueness guards not present in the whitepaper. Adjusting it to (a) enforce exact Step‑1 multiplicities, (b) introduce an abstract partition witness for Step‑2/3 with eligibility‑based sampling, and (c) remove the non‑paper uniqueness guards will make the model faithful to Definition 46 while keeping it abstract and model‑checkable.

