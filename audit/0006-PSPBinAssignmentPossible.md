# Audit: PSPBinAssignmentPossible

## 1. Code Under Audit

```tla
PSPBinAssignmentPossible(needers, nextLeader) ==
    LET largeStakeholders == LargeStakeholdersInNeeders(needers)
        remainingNeeders == needers \ largeStakeholders
        remainingBins == RemainingBins(needers)
        deterministicTotal == TotalDeterministicBins(needers)
    IN /\ deterministicTotal <= GammaTotalShreds
       /\ remainingBins <= Cardinality(remainingNeeders)
       /\ (nextLeader \in needers => 
           nextLeader \in largeStakeholders \/ nextLeader \in remainingNeeders)
```

Definition location: `specs/tla/alpenglow/Rotor.tla:79`

Related operators/constants in the same module:
- `LargeStakeholdersInNeeders`: `specs/tla/alpenglow/Rotor.tla:56`
- `TotalDeterministicBins`: `specs/tla/alpenglow/Rotor.tla:61`
- `RemainingBins`: `specs/tla/alpenglow/Rotor.tla:72`
- `GammaTotalShreds` (constant, Γ): `specs/tla/alpenglow/Rotor.tla:24`
- `EXTENDS Naturals, FiniteSets, Certificates`: `specs/tla/alpenglow/Rotor.tla:1`

Upstream stake definitions this depends on (via `Certificates`):
- `StakeMap`, `TotalStake`: `specs/tla/alpenglow/Certificates.tla:27, 51`

## 2. Whitepaper Source and References

- Erasure coding parameters (Γ, γ, κ) and Rotor context: `alpenglow-whitepaper.md:265`, `alpenglow-whitepaper.md:267`, `alpenglow-whitepaper.md:269`, `alpenglow-whitepaper.md:365`.
- Smart Sampling; PS-P definition (partition sampling) and steps 1–3:
  - Definition 45 (partitioning): `alpenglow-whitepaper.md:1143`
  - Definition 46 (PS-P, steps 1–3): `alpenglow-whitepaper.md:1154–1158`
- Rotor success condition reference: `alpenglow-whitepaper.md:414`.

The operator under audit is intended to check feasibility for the PS-P bin assignment, which implements Definition 46.

## 3. Reasoning: What The Code Does vs. What The Paper Requires

What PS-P (Def. 46) requires:
- Step 1: For each node with ρ_i > 1/Γ, allocate ⌊ρ_i·Γ⌋ deterministic bins; define remaining stake ρ'_i < 1/Γ.
- Step 2: Partition remaining stakes {ρ'_i} across the remaining k = Γ − Σ_i ⌊ρ_i·Γ⌋ bins using a partitioning algorithm P.
- Step 3: From each bin, sample one node proportional to its stake portion in that bin.

What PSPBinAssignmentPossible checks:
- Compute `largeStakeholders == {v ∈ needers : ⌊ρ_v·Γ⌋ ≥ 1}` via `DeterministicBinCount`.
- Use `TotalDeterministicBins(needers)` as an approximation to Σ_i ⌊ρ_i·Γ⌋. In the current spec this is under-approximated as `Cardinality(largeStakeholders)` (clamped by Γ) rather than the exact sum.
- Define `RemainingBins(needers) == Γ − TotalDeterministicBins(needers)` (zero if the total meets/exceeds Γ due to clamping).
- Require:
  1) `deterministicTotal ≤ Γ` — tautologically true given `TotalDeterministicBins` clamps at Γ.
  2) `remainingBins ≤ Cardinality(remainingNeeders)` — stronger than PS-P, which allows re-use of a node across multiple bins (bins sample independently). PS-P does not require the number of distinct “small” stakeholders to be at least the number of remaining bins.
  3) `(nextLeader ∈ needers ⇒ nextLeader ∈ largeStakeholders ∨ nextLeader ∈ remainingNeeders)` — tautology, because `remainingNeeders = needers \ largeStakeholders`.

Key observations:
- Under-approximation: `TotalDeterministicBins` uses the count of large stakeholders instead of Σ_i ⌊ρ_i·Γ⌋. Since Σ_i ⌊ρ_i·Γ⌋ ≥ |{i : ⌊ρ_i·Γ⌋ ≥ 1}|, this makes `RemainingBins` an over-approximation. As a result, the feasibility check can return false (i.e., “impossible”) even in cases where a valid PS-P assignment exists, reducing liveness without improving safety.
- Unnecessary cardinality constraint: `remainingBins ≤ |remainingNeeders|` is not implied by Definition 46. PS-P partitions stake into bins and samples from each bin; a single small-stake node can appear in multiple bins and be sampled multiple times. Requiring at least as many distinct small-stake validators as remaining bins is overly restrictive and misaligns with PS-P.
- Tautologies: two of the three conjuncts are vacuous given the surrounding definitions, so the predicate effectively reduces to the single cardinality check above, which itself is non-essential per PS-P.
- Stake arithmetic invariant: Because Σ_i ρ_i = 1, the number of large stakeholders (ρ_i ≥ 1/Γ) cannot exceed Γ. The spec’s clamp in `TotalDeterministicBins` therefore never hides an impossible “too many large stakeholders” case; that case cannot occur with a valid stake distribution. Nevertheless, the approximation still distorts the true k used in Step 2.

## 4. Conclusion

- Faithfulness: As written, `PSPBinAssignmentPossible` is not an accurate abstraction of the PS-P feasibility implied by Definition 46. It enforces a stronger-than-necessary distinctness condition on the remaining needers, and its other conjuncts are redundant.
- Safety vs. liveness: The predicate is a sufficient (and conservative) condition that may reject feasible cases (false negatives). This can cause the selection procedure to return the empty set when PS-P would allow a valid assignment. It does not appear to introduce a safety violation, but it misrepresents the whitepaper’s allowance for per-bin independent sampling with possible multiplicity.

## 5. Open Questions / Concerns

- Intentional restriction? Is the goal to model a variant of PS-P that forbids assigning the same “small” node to multiple bins? If so, this contradicts the paper’s Step 2–3 independence and should be documented as a deliberate deviation.
- Exact Step 1 counts: Should large stakeholders receive exactly ⌊ρ_i·Γ⌋ bins (as in Def. 46 Step 1), or is “≥ 1” intended? Current spec (`PSPConstraint`) enforces only ≥1 and the generator (`PSPBinAssignment`) does not ensure exact counts.
- Multiplicity vs. set semantics: The spec converts bins to a set of relays (`BinsToRelaySet` → `PSPSelect`), losing multiplicity. If multiplicity is dropped, how are γ distinct shreds reasoned about downstream, given that one relay mapped to multiple bins produces multiple shreds in the protocol?
- Feasibility gating interplay: `PSPBinAssignment` also contains an additional gate `GammaTotalShreds ≤ Cardinality(needers)` (not part of the audited operator). This is stricter than PS-P and may further reduce liveness.

## 6. Suggestions for Improvement

- Align Step 1 exactly:
  - Replace the approximation in `TotalDeterministicBins` with the exact sum:
    ```tla
    TotalDeterministicBins(needers) ==
      LET S == needers IN
      LET RECURSIVE Sum(_)
          Sum(T) == IF T = {} THEN 0
                     ELSE LET v == CHOOSE x \in T : TRUE IN
                          DeterministicBinCount(v) + Sum(T \ {v})
      IN Min(GammaTotalShreds, Sum(S))
    ```
  - Strengthen `PSPConstraint` to enforce per‑validator bin multiplicity: for all v, `Cardinality({j : bins[j] = v}) = DeterministicBinCount(v)` for large stakeholders.

- Relax feasibility to match Definition 46:
  - Remove `remainingBins ≤ Cardinality(remainingNeeders)` from `PSPBinAssignmentPossible`. A minimal, faithful feasibility check would simply require `needers # {}` (or nothing—PS-P is always constructible for any nonempty stake distribution over `needers`).
  - If keeping a feasibility predicate is desirable, make it a sanity check on stake arithmetic, e.g., `Σ_i ⌊ρ_i·Γ⌋ ≤ Γ` (always true by construction) and `RemainingBins ≥ 0`.

- Preserve multiplicity in downstream reasoning:
  - Keep bin assignments (functions over `1..Γ`) as first‑class where γ‑reconstruction or resilience is reasoned about. Avoid collapsing to sets too early; otherwise, invariants that speak about “γ distinct shreds” are not faithfully captured.

- Document deviations explicitly:
  - If the intent is a simplified abstraction, clearly state which aspects are conservative (may reject feasible cases) and why that is acceptable for the properties you aim to verify.

- Optional: next‑leader constraint
  - If there is a policy to prioritize the next leader, express it as a constraint over bins (e.g., “if nextLeader ∈ needers then it appears in at least one bin”), and check it where bin assignments are constructed rather than as a tautology in feasibility.

File references for context:
- `specs/tla/alpenglow/Rotor.tla:56` LargeStakeholdersInNeeders
- `specs/tla/alpenglow/Rotor.tla:61` TotalDeterministicBins (approximation)
- `specs/tla/alpenglow/Rotor.tla:72` RemainingBins
- `specs/tla/alpenglow/Rotor.tla:79` PSPBinAssignmentPossible (audited)
- `alpenglow-whitepaper.md:1154–1158` PS-P Definition 46 (steps 1–3)
- `alpenglow-whitepaper.md:265, 267, 269, 365` Erasure coding parameters and Rotor

```diff
Summary of required changes to match the whitepaper:
- [!] Compute exact Σ_i ⌊ρ_i·Γ⌋ (Step 1) instead of |LargeStakeholders|.
- [!] Drop the `remainingBins ≤ |remainingNeeders|` requirement.
- [!] Enforce per‑validator deterministic multiplicity in constraints or construction.
- [~] Keep/clarify next‑leader inclusion as a separate structural constraint.
```

