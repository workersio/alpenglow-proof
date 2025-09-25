# Audit: RemainingBins (PS-P Remaining Bins)

## 1. Code Under Audit

```tla
RemainingBins(needers) ==
    LET deterministicTotal == TotalDeterministicBins(needers)
    IN IF deterministicTotal >= GammaTotalShreds 
       THEN 0 
       ELSE GammaTotalShreds - deterministicTotal
```

Implementation location: `specs/tla/alpenglow/Rotor.tla:72`.

Related context in the same module:
- `DeterministicBinCount(v) == (StakeMap[v] * GammaTotalShreds) \div TotalStake`: `specs/tla/alpenglow/Rotor.tla:51`
- `LargeStakeholdersInNeeders(needers) == { v ∈ needers : DeterministicBinCount(v) ≥ 1 }`: `specs/tla/alpenglow/Rotor.tla:56`
- `TotalDeterministicBins(needers)` (current approximation): `specs/tla/alpenglow/Rotor.tla:61`
- Use sites: `PSPBinAssignmentPossible` and `PSPBinAssignment`: `specs/tla/alpenglow/Rotor.tla:79`, `specs/tla/alpenglow/Rotor.tla:95`

External definitions referenced:
- `GammaTotalShreds` (Γ), `GammaDataShreds` (γ) constants and assumptions: `specs/tla/alpenglow/Rotor.tla:24`, `specs/tla/alpenglow/Rotor.tla:30`
- `StakeMap`, `TotalStake` from certificates/stake module: `specs/tla/alpenglow/Certificates.tla:34`, `specs/tla/alpenglow/Certificates.tla:65`

## 2. Whitepaper Section and References

- Erasure coding parameters and semantics (Γ, γ, κ): `alpenglow-whitepaper.md:265`–`alpenglow-whitepaper.md:267`
- Definition 45 (partitioning into bins): `alpenglow-whitepaper.md:1143`–`alpenglow-whitepaper.md:1152`
- Definition 46 (PS-P – Partition Sampling): `alpenglow-whitepaper.md:1154`
  - Step 1: deterministic allocation of ⌊ρᵢ·Γ⌋ bins for all nodes with ρᵢ > 1/Γ: `alpenglow-whitepaper.md:1156`
  - Step 2: compute remaining bin count k = Γ − Σᵢ ⌊ρᵢ·Γ⌋ and partition the remaining stakes across these k bins: `alpenglow-whitepaper.md:1157`
  - Step 3: sample one node per bin proportionally to stake: `alpenglow-whitepaper.md:1158`

## 3. Reasoning: Code vs. Whitepaper Claims

What the paper specifies (PS-P Step 1–2):
- For each node i with relative stake ρᵢ > 1/Γ, allocate deterministically ⌊ρᵢ·Γ⌋ bins to i.
- The exact number of remaining bins is k = Γ − Σᵢ ⌊ρᵢ·Γ⌋, where the sum is over all eligible nodes considered for sampling.

What the model intends to capture:
- `RemainingBins(needers)` is the TLA abstraction for the PS-P Step 2 value k, but scoped to the current eligible set `needers` (nodes that still need the slice), which is consistent with Rotor’s operational constraint of choosing relays from nodes that do not yet have the block.
- Algebraically, if `TotalDeterministicBins(needers)` equals Σᵢ∈needers ⌊ρᵢ·Γ⌋, then the definition of `RemainingBins` exactly matches Step 2: k = Γ − Σ⌊ρᵢ·Γ⌋, with the guard `IF deterministicTotal ≥ Γ THEN 0` ensuring non-negativity.

Where the current spec diverges:
- `TotalDeterministicBins(needers)` is not the sum Σᵢ ⌊ρᵢ·Γ⌋. Instead, it approximates this total as the count of “large stakeholders” (those with ⌊ρᵢ·Γ⌋ ≥ 1), capped at Γ: see `specs/tla/alpenglow/Rotor.tla:61`–`specs/tla/alpenglow/Rotor.tla:68`.
  - Consequence: deterministic bins are underestimated in general, often drastically (e.g., a single node with ρ = 0.4 and Γ = 100 should contribute 40 deterministic bins; the approximation contributes only 1).
  - This inflates `RemainingBins` above the true PS-P value k.
- This inflated `RemainingBins` is used in a feasibility pre-check `remainingBins ≤ Cardinality(remainingNeeders)` (`specs/tla/alpenglow/Rotor.tla:85`). That condition is not part of PS-P and can be false even when PS-P is perfectly feasible: PS-P permits the same small stakeholder to appear across multiple remaining bins; uniqueness is not required per bin across nodes. Thus the check is overly restrictive.

Impact on properties:
- Structural soundness: The algebraic shape of `RemainingBins` is fine; the issue is the upstream approximation. With an exact `TotalDeterministicBins`, `RemainingBins` would match Definition 46 Step 2.
- Safety: Overestimating remaining bins primarily biases the model toward declaring infeasibility, causing `PSPBinAssignment` to fall back to an empty assignment. This is conservative for safety (it does not create invalid relay sets) but can hide valid PS-P choices.
- Liveness/realism: The pre-check may spuriously block feasible assignments, making Rotor succeed less often in the model than the whitepaper guarantees for the same parameters (and stake distribution), potentially weakening liveness arguments that rely on Rotor’s success probabilities.

## 4. Audit Conclusion

- The `RemainingBins` definition is algebraically consistent with PS-P Step 2 provided `TotalDeterministicBins(needers)` equals Σᵢ∈needers ⌊ρᵢ·Γ⌋.
- In the current spec, `TotalDeterministicBins` is a coarse underestimate (count of large stakeholders), so `RemainingBins` does not reflect the whitepaper’s Definition 46 quantitatively. This can mischaracterize feasibility and selection behavior downstream.
- Verdict: Not fully faithful to the whitepaper due to the upstream approximation. The shape is correct; the input value is not.

## 5. Open Questions / Concerns

- Scope of PS-P: Should deterministic allocations be computed over all validators or only `needers`? The model uses `needers`, aligning with the operational constraint “choose relays from nodes that still need the slice”. This choice seems acceptable, but documenting this deviation from the paper’s global phrasing would aid readers.
- Overly strict feasibility pre-check: The condition `remainingBins ≤ Cardinality(remainingNeeders)` is not implied by Definition 46 and excludes perfectly valid PS-P outcomes (the same node may be sampled in multiple remaining bins). Is this constraint intentional as an additional modeling choice, or should it be removed?
- Large-stakeholder multiplicity: `PSPConstraint` only requires at least one bin for “large stakeholders”. Definition 46 Step 1 requires exactly ⌊ρᵢ·Γ⌋ bins. Should the constraint be tightened to enforce exact multiplicity for better fidelity?

## 6. Suggestions for Improvement

- Compute deterministic bins exactly:
  ```tla
  TotalDeterministicBins(needers) ==
      LET RECURSIVE SumDet(_)
          SumDet(S) ==
              IF S = {} THEN 0
              ELSE LET v == CHOOSE x \in S : TRUE IN
                   DeterministicBinCount(v) + SumDet(S \ {v})
      IN SumDet(needers)
  ```
  This implements Σᵢ∈needers ⌊ρᵢ·Γ⌋. A supporting lemma can record the bound Σ ⌊ρᵢ·Γ⌋ ≤ Γ to justify non-negativity of `RemainingBins`:
  ```tla
  THEOREM DeterministicBinsBound == TotalDeterministicBins(Validators) <= GammaTotalShreds
  ```
- Keep `RemainingBins` as-is; it becomes faithful once `TotalDeterministicBins` is exact.
- Remove or relax the non-paper feasibility guard `remainingBins ≤ Cardinality(remainingNeeders)`. If a guard is desired, prefer a stake-based check (e.g., residual stake adequacy) already captured by `ResilienceOK`.
- Tighten the structural constraint for large stakeholders to enforce exact multiplicity per Step 1:
  ```tla
  PSPConstraint(bins, needers) ==
      /\ DOMAIN bins = 1..GammaTotalShreds
      /\ \A j \in DOMAIN bins : bins[j] \in needers
      /\ \A v \in needers :
            Cardinality({ j \in DOMAIN bins : bins[j] = v }) = DeterministicBinCount(v)
            \/ DeterministicBinCount(v) = 0
  ```
  If exact equality is too strong for other abstractions, at minimum require `≥ DeterministicBinCount(v)`.
- Document in comments that PS-P is instantiated over `needers` (subsetting the validator set) for operational reasons, and that the above changes preserve the whitepaper’s intent while keeping the model abstract (no actual partitioning or randomness).

---

In summary, `RemainingBins` is the right abstraction for PS-P Step 2, but due to an approximate `TotalDeterministicBins` and an extra feasibility guard, the model diverges from the whitepaper. Computing the exact deterministic bin total and relaxing the extra guard will make `RemainingBins` and its uses faithfully match Definition 46 without sacrificing abstraction.

