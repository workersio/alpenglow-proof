# Audit: Rotor.TotalDeterministicBins

## 1. Code Under Audit

```
TotalDeterministicBins(needers) ==
    LET largeStakeholders == LargeStakeholdersInNeeders(needers)
    IN IF largeStakeholders = {} THEN 0
       ELSE \* For modeling simplicity, we approximate the total
            \* In a full implementation, this would sum DeterministicBinCount(v) for all v
            \* Here we use a conservative estimate that won't exceed GammaTotalShreds
            LET maxPossible == GammaTotalShreds
                conservativeEstimate == Cardinality(largeStakeholders)
            IN IF conservativeEstimate > maxPossible THEN maxPossible ELSE conservativeEstimate
```

Context in spec:
- `specs/tla/alpenglow/Rotor.tla:61` (definition)
- Uses `LargeStakeholdersInNeeders` and `DeterministicBinCount` from the same module:
  - `specs/tla/alpenglow/Rotor.tla:52` DeterministicBinCount(v) == (StakeMap[v] * GammaTotalShreds) \div TotalStake
  - `specs/tla/alpenglow/Rotor.tla:56` LargeStakeholdersInNeeders(needers) == { v \in needers : DeterministicBinCount(v) >= 1 }
- Constants: `GammaTotalShreds` from the model config
  - `specs/tla/alpenglow/MC.cfg:33` GammaTotalShreds = 6
- Stake primitives: `StakeMap`, `TotalStake` in Certificates
  - `specs/tla/alpenglow/Certificates.tla:34,65` (StakeMap, TotalStake)

Downstream functions using this result:
- `specs/tla/alpenglow/Rotor.tla:71` RemainingBins(needers) == GammaTotalShreds - TotalDeterministicBins(needers) (capped at 0)
- `specs/tla/alpenglow/Rotor.tla:79` PSPBinAssignmentPossible(...)
- `specs/tla/alpenglow/Rotor.tla:91` PSPBinAssignment(...)

## 2. Whitepaper Sections and References

- Section 3.1 Smart Sampling (PS-P): Definition 46, Steps 1–3
  - `alpenglow-whitepaper.md:1154` Definition 46 (PS-P)
  - `alpenglow-whitepaper.md:1156` Step 1: for each node with ρ_i > 1/Γ, fill ⌊ρ_i Γ⌋ deterministic bins; define residual stakes ρ'_i
  - `alpenglow-whitepaper.md:1157` Step 2: partition residual stakes into remaining k = Γ − Σ_i ⌊ρ_i Γ⌋ bins
  - `alpenglow-whitepaper.md:1158` Step 3: sample one node per bin proportionally to stake

- Erasure coding context (Γ, γ, κ) and Rotor overview
  - `alpenglow-whitepaper.md:64` Rotor algorithm mention (Section 2.2)
  - Resilience relation κ = Γ/γ discussed broadly; Lemma references appear elsewhere, but not essential for this function

## 3. Reasoning and Whitepaper Alignment

Intent per paper:
- Step 1 of PS-P deterministically reserves, for each “large” stakeholder i (ρ_i ≥ 1/Γ), exactly ⌊ρ_i Γ⌋ bins. The total deterministic bins is Σ_{i large} ⌊ρ_i Γ⌋. The number of bins left for probabilistic sampling is k = Γ − Σ ⌊ρ_i Γ⌋.

What the spec does:
- `DeterministicBinCount(v)` correctly models ⌊ρ_v Γ⌋ as integer division.
- `LargeStakeholdersInNeeders` correctly identifies “large” stakeholders as those with ⌊ρ_v Γ⌋ ≥ 1 (equivalently ρ_v ≥ 1/Γ).
- `TotalDeterministicBins` does not sum the per‑validator ⌊ρ_v Γ⌋. Instead, it approximates Σ ⌊ρ_v Γ⌋ as min(Γ, |largeStakeholders|).

Implications of the approximation:
- Under‑approximation. Since each large stakeholder contributes at least 1 to Σ ⌊ρ_v Γ⌋, we have |large| ≤ Σ ⌊ρ_v Γ⌋ ≤ Γ. Returning |large| therefore underestimates the true Σ ⌊ρ_v Γ⌋ unless every large stakeholder contributes exactly 1 bin. This is “conservative” in the sense of not exceeding Γ, but it is not correct per Definition 46.
- Overstated remaining bins. `RemainingBins` uses Γ − TotalDeterministicBins. When `TotalDeterministicBins` is underestimated, the model thinks there are more “remaining” bins than in the whitepaper. This shifts mass from deterministic allocations (Step 1) to probabilistic sampling (Steps 2–3).
- Downstream mismatch with multiplicity. `PSPBinAssignment` uses `deterministicTotal` to assign “deterministic bins” but distributes them via `CHOOSE v ∈ largeStakeholders : TRUE`. This selects the same v across all j (because the set is j‑invariant), concentrating all reserved bins into a single arbitrary large stakeholder and violating the per‑validator multiplicities ⌊ρ_v Γ⌋ mandated by Step 1. The structural check `PSPConstraint` later only enforces “≥ 1 bin per large” (not equality to ⌊ρ_v Γ⌋), and `RotorSelect` does not enforce `StructuralBinOK` at selection time.

Summary vs paper:
- Correct abstractions: the threshold for “large” (ρ ≥ 1/Γ) and the notion of deterministic bins exist and are tied to Γ.
- Deviations: the total count is under‑approximated, and the model does not ensure each large stakeholder receives exactly ⌊ρ_i Γ⌋ bins, as Definition 46 requires. This can distort the residual bin count and bin assignment semantics compared to the whitepaper.

## 4. Conclusion

- The current `TotalDeterministicBins` deviates from whitepaper Definition 46 Step 1 by returning `min(Γ, |largeStakeholders|)` instead of Σ_{v ∈ large} ⌊ρ_v Γ⌋. This is a conservative lower bound but is not semantically equivalent to the paper’s Step 1.
- Because `RemainingBins` depends on this value, the model may allocate too many “remaining” bins to sampling.
- Combined with `PSPBinAssignment` using a j‑invariant `CHOOSE` for deterministic slots and `PSPConstraint` only insisting on “≥ 1” (instead of exact multiplicities), the model can produce bin allocations that do not correspond to any PS‑P outcome in Definition 46.
- Unless constrained elsewhere, this is a material mismatch with the whitepaper abstraction for PS‑P. The invariant `RotorSelectSoundness` (specs/tla/alpenglow/MainProtocol.tla:1059 with RotorSelectSoundness definition at specs/tla/alpenglow/MainProtocol.tla:917) attempts to assert existence of a structurally valid bin explanation for any non‑empty selection, but `RotorSelect` itself does not enforce those constraints at construction time.

## 5. Open Questions and Concerns

- Exactness vs abstraction: Is the intent to keep PS‑P abstract while retaining correctness of constraints, or to model the exact multiplicities from Definition 46? The current approximation breaks exactness and may compromise constraint‑based reasoning unless invariants eliminate the spurious cases.
- CHOOSE stability: In `PSPBinAssignment`, `CHOOSE v ∈ largeStakeholders : TRUE` is constant in j and thus assigns all deterministic bins to the same v. Was a round‑robin or per‑v replication intended? The comment says “round‑robin” but code does not implement it.
- Constraint enforcement gap: `RotorSelect` does not check `StructuralBinOK` or `BinCandidates`. The spec asserts a posteriori that a structural witness exists (`RotorSelectSound`), but does not guarantee the produced set is structurally realizable from PS‑P.
- Minimum per‑v deterministic bins: `PSPConstraint` requires only “≥ 1 bin per large” rather than “exactly ⌊ρ_v Γ⌋ bins”, which is weaker than Definition 46.

## 6. Suggestions for Improvement

1) Make TotalDeterministicBins match Definition 46 Step 1:

```
TotalDeterministicBins(needers) ==
    LET large == LargeStakeholdersInNeeders(needers)
    IN IF large = {} THEN 0
       ELSE LET RECURSIVE Sum(_)
                Sum(S) == IF S = {} THEN 0
                           ELSE LET v == CHOOSE x \in S : TRUE
                                IN DeterministicBinCount(v) + Sum(S \ {v})
                total == Sum(large)
            IN IF total >= GammaTotalShreds THEN GammaTotalShreds ELSE total
```

2) Strengthen structural constraint to exact multiplicities for large stakeholders:

```
PSPConstraint(bins, needers) ==
    /\ DOMAIN bins = 1..GammaTotalShreds
    /\ \A j \in DOMAIN bins : bins[j] \in needers
    /\ \A v \in LargeStakeholders(needers) :
          Cardinality({ j \in DOMAIN bins : bins[j] = v }) = DeterministicBinCount(v)
```

3) Implement deterministic allocation per large stakeholder in PSPBinAssignment (sketch):

```
LET large == LargeStakeholdersInNeeders(needers)
    multiset == UNION { [i \in 1..DeterministicBinCount(v) |-> v] : v \in large }
IN [ j \in 1..GammaTotalShreds |->
       IF j \in DOMAIN multiset THEN multiset[j]
       ELSE (* fill remaining bins via proportional sampling among residual stakes *) CHOOSE w \in (needers \ large) : TRUE ]
```

4) Make RemainingBins consistent with the exact deterministic total:

```
RemainingBins(needers) ==
    LET d == TotalDeterministicBins(needers)
    IN IF d >= GammaTotalShreds THEN 0 ELSE GammaTotalShreds - d
```

5) Enforce structural validity at selection time:
- Have `RotorSelect` compute `bins` from PS‑P and return `BinsToRelaySet(bins)` only if `StructuralBinOK(bins, ...)` holds (and retain the stake threshold check). Alternatively, select from `BinCandidates` directly.

6) Add invariants specific to PS‑P Step 1:
- ∀ v ∈ LargeStakeholders(needers): DeterministicBinCount(v) = Cardinality({ j : bins[j] = v })
- Σ_v Cardinality({ j : bins[j] = v }) = min(Γ, Σ_v ⌊ρ_v Γ⌋)

Expected benefits:
- Aligns the model with the whitepaper’s PS‑P Step 1 exactly, preserves the abstraction fidelity, and avoids over‑allocating “remaining” bins.
- Eliminates the j‑invariant CHOOSE pitfall and ensures reproducible, well‑constrained bin explanations for selections, improving model checking power and preventing spurious behaviors.

