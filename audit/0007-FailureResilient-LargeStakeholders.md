# Audit: FailureResilient and LargeStakeholders

## 1. Code That You Are Auditing

```
FailureResilient(sample) ==
    LET stake == CalculateStake(sample)
    IN stake >= RotorMinRelayStake /\ (stake - RotorMaxFailedRelayStake) >= RotorMinRelayStake

\* Large stakeholders per PS-P Step 1: those with deterministic bin assignments
\* Updated to use proper bin count calculation
LargeStakeholders(S) == { v \in S : DeterministicBinCount(v) >= 1 }
```

- Definition locations:
  - `specs/tla/alpenglow/Rotor.tla:125` (FailureResilient)
  - `specs/tla/alpenglow/Rotor.tla:131` (LargeStakeholders)

- Referenced symbols and where they are defined:
  - `CalculateStake(set)`: `specs/tla/alpenglow/Certificates.tla:76`
  - `StakeMap`, `TotalStake`: `specs/tla/alpenglow/Certificates.tla:34`, `specs/tla/alpenglow/Certificates.tla:65`
  - `DeterministicBinCount(v)`: `specs/tla/alpenglow/Rotor.tla:52`
  - `RotorMinRelayStake`, `RotorMaxFailedRelayStake`: `specs/tla/alpenglow/Rotor.tla:23`, `specs/tla/alpenglow/Rotor.tla:26` (with constraints in `specs/tla/alpenglow/Rotor.tla:34`–`specs/tla/alpenglow/Rotor.tla:37`)

## 2. Whitepaper Sections and References Represented by the Code

- PS-P (Partition Sampling) algorithm — Definition 46 (Section 3.1)
  - Intro to PS-P: `alpenglow-whitepaper.md:1154`
  - Step 1 (deterministic assignment for “large” stakeholders): `alpenglow-whitepaper.md:1156`
  - Step 2 (partition remaining stakes): `alpenglow-whitepaper.md:1157`
  - Step 3 (sample one per bin): `alpenglow-whitepaper.md:1158`

- Rotor success condition — Definition 6 (Section 2.2)
  - Rotor is successful if the leader is correct and at least `γ` relays are correct: `alpenglow-whitepaper.md:414`
  - Resilience with κ = Γ/γ > 5/3 (Lemma 7) and intuition: `alpenglow-whitepaper.md:418`

- Fault tolerance assumptions (“20+20” narrative)
  - Assumption 1 (Byzantine < 20%): `alpenglow-whitepaper.md:107`
  - Assumption 2 (extra crash tolerance; Byzantine < 20%, up to 20% may crash, ≥60% correct): `alpenglow-whitepaper.md:122`

## 3. Reasoning: Code vs. Whitepaper Claims

- LargeStakeholders(S)
  - The whitepaper’s PS-P Step 1 deterministically assigns bins for “large” stakeholders: for each node with relative stake ρ_i > 1/Γ, fill ⌊ρ_i·Γ⌋ bins; residual stake becomes ρ'_i = ρ_i − (⌊ρ_i·Γ⌋/Γ) (< 1/Γ) for those nodes.
  - The model defines `DeterministicBinCount(v) == (StakeMap[v] * Γ) \div TotalStake`, i.e., ⌊ρ_v·Γ⌋ using integer division, and identifies large stakeholders via `DeterministicBinCount(v) >= 1`.
  - Boundary subtlety: The paper states “> 1/Γ” while the code uses “≥ 1 deterministic bin.” For ρ_i = 1/Γ, ⌊ρ_i·Γ⌋ = 1. Under the paper’s Step 2, k = Γ − ∑_i ⌊ρ_i·Γ⌋. Using “>” would leave a node with ρ_i = 1/Γ unassigned in Step 1 while still reducing k by 1 (since the sum includes all i), which is inconsistent. The model’s “≥ 1” via `DeterministicBinCount(v) >= 1` restores consistency with the ∑⌊ρ_i·Γ⌋ accounting and matches the intended semantics of Step 1.
  - Conclusion for this piece: `LargeStakeholders` correctly captures the PS-P Step 1 notion by using the bin-count test (⌊ρ_i·Γ⌋ ≥ 1), which is equivalent to ρ_i ≥ 1/Γ and aligns with the intended deterministic inclusion rule.

- FailureResilient(sample)
  - Rotor success per the paper is about correctness of relays: leader correct ∧ at least γ correct relays (Definition 6). The paper does not define a stake-based minimum for a relay set nor a stake-budget of allowable relay failures.
  - The TLA+ model introduces `RotorMinRelayStake` and `RotorMaxFailedRelayStake`. `FailureResilient(sample)` asserts that the chosen relay set has total stake ≥ `RotorMinRelayStake`, and even after losing up to `RotorMaxFailedRelayStake` (due to crashes/Byzantine/non-participation inside the set), the residual stake still meets `RotorMinRelayStake`.
  - This is a modeling strengthening, consistent with the “20+20” resilience narrative and Assumption 2’s framing of crash tolerance, but it is not a claim made explicitly in the whitepaper for Rotor’s base success semantics. It serves as a proxy for robust coverage: a sufficiently “stake-heavy” relay set should, with high probability (per Lemma 7’s concentration), contain ≥γ correct relays despite some stake going offline.
  - In the provided model instantiation (`specs/tla/alpenglow/MC.cfg:30`–`specs/tla/alpenglow/MC.cfg:36`), `TotalStake` is normalized to 100, `RotorMinRelayStake = 40`, and `RotorMaxFailedRelayStake = 10`; thus `FailureResilient(sample)` effectively enforces stake(sample) ≥ 50 so that stake(sample) − 10 ≥ 40.

## 4. Conclusion of the Audit

- LargeStakeholders(S): Correct and faithful to PS-P Step 1 when interpreting “large” as ⌊ρ_i·Γ⌋ ≥ 1 (ρ_i ≥ 1/Γ). The model’s formulation avoids a boundary inconsistency in Definition 46’s arithmetic and aligns with the intended deterministic inclusion rule.

- FailureResilient(sample): Intentional modeling strengthening beyond the whitepaper’s core Rotor success definition. It does not contradict the paper and is in line with its resilience objectives, but it is extra. The surrounding comments in `Rotor.tla` acknowledge this and fence it as an additional robustness constraint.

Overall, the abstractions match the whitepaper’s PS-P algorithm and Rotor’s success condition, with `FailureResilient` adding a reasonable, documented robustness layer for relay selection.

## 5. Open Questions or Concerns

- PS-P boundary (“> 1/Γ” vs “≥ 1/Γ”): The paper text uses “> 1/Γ”, while the bin-count test in code corresponds to “≥ 1/Γ”. Given the k = Γ − ∑⌊ρ_i·Γ⌋ formula, the “≥” interpretation appears necessary for consistency. It may be worth clarifying the inequality in the whitepaper text.

- Quantitative tie to γ/κ: `FailureResilient` constrains stake mass, not the number of correct relays γ. While stake concentration is a reasonable proxy under stake-weighted sampling, the model does not explicitly link `RotorMinRelayStake` to γ or κ. Is this intentional, or should parameters be calibrated (e.g., via a lemma) to imply P[≥γ correct relays] ≥ 1 − ε under given fault assumptions?

- Redundancy in FailureResilient: `stake >= RotorMinRelayStake` is implied by `(stake - RotorMaxFailedRelayStake) >= RotorMinRelayStake` with `RotorMaxFailedRelayStake >= 0`. The first conjunct is thus redundant unless kept for readability.

- Scope of enforcement: `ResilienceOK(sample) == FailureResilient(sample)` is used when characterizing feasible bin assignments (`BinCandidates`), and `RotorSelectSoundness` requires existence of a structurally valid `bins` that also satisfies `ResilienceOK`. `RotorSelect` itself doesn’t directly check the residual property, only the minimum stake. This is fine if the invariant is the enforcement point; otherwise consider applying `ResilienceOK` at selection time for symmetry.

## 6. Suggestions for Improvement

- Whitepaper alignment note in code:
  - Add a short comment by `LargeStakeholders` citing PS-P Step 1 (Definition 46) and clarifying that ⌊ρ_i·Γ⌋ ≥ 1 corresponds to ρ_i ≥ 1/Γ; this reconciles the strict “>” in the prose with the arithmetic used for k.

- Simplify FailureResilient for clarity:
  - Replace with `FailureResilient(sample) == CalculateStake(sample) >= RotorMinRelayStake + RotorMaxFailedRelayStake`. This is equivalent and highlights the single effective constraint.

- Parameter semantics:
  - Document the intended units for `RotorMinRelayStake`/`RotorMaxFailedRelayStake` (they match the stake units of `StakeMap`, normalized to 100 in the MC harness) and, if possible, relate them to γ and κ via an explanatory note.

- Minor consistency cleanups:
  - Consider using a single helper `LargeStakeholders(S)` and define `LargeStakeholdersInNeeders(needers) == LargeStakeholders(needers)` to reduce duplication.
  - If feasible for your model scope, strengthen the bin assignment constraint to reflect the exact deterministic count: for each large v, `Cardinality({ j : bins[j] = v }) = DeterministicBinCount(v)` (the current `>= 1` is weaker than PS-P Step 1). This may already be covered in adjacent work (see `audit/0005-Rotor-TotalDeterministicBins.md`).

