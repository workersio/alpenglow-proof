# Audit: Rotor.PSPConstraint

## 1. Code Under Audit

```tla
PSPConstraint(bins, needers) == 
    /\ DOMAIN bins = 1..GammaTotalShreds  \* Exactly Γ bins assigned
    /\ \A j \in DOMAIN bins : bins[j] \in needers  \* All assignments valid
    /\ \A v \in LargeStakeholders(needers) :  \* Large stakeholders get appropriate bins
        Cardinality({j \in DOMAIN bins : bins[j] = v}) >= 1
```

Definition location: `specs/tla/alpenglow/Rotor.tla:135`

Referenced operators/constants:
- `LargeStakeholders(S)`: `specs/tla/alpenglow/Rotor.tla:131`
- `DeterministicBinCount(v)`: `specs/tla/alpenglow/Rotor.tla:52`
- `GammaTotalShreds` (Γ): `specs/tla/alpenglow/Rotor.tla:24`
- `Cardinality`, `DOMAIN`: from `FiniteSets` / TLA+ core

Contextual use sites:
- `StructuralBinOK(bins, needers, nextLeader)`: `specs/tla/alpenglow/Rotor.tla:154`
- `BinCandidates(block, needers, nextLeader)`: `specs/tla/alpenglow/Rotor.tla:165`

## 2. Whitepaper Section and References

- Section 3.1 Smart Sampling
  - Definition 45 (partitioning): `alpenglow-whitepaper.md:1143`
  - Definition 46 (PS-P, steps 1–3): `alpenglow-whitepaper.md:1154–1158`
    1) For each node with relative stake ρᵢ > 1/Γ, fill ⌊ρᵢ·Γ⌋ bins with that node; set residual stake ρ′ᵢ < 1/Γ.
    2) Partition residual stakes into the remaining k = Γ − Σᵢ ⌊ρᵢ·Γ⌋ bins using a partitioning algorithm P.
    3) From each bin, sample one node proportional to their stake.
- Rotor/erasure coding parameters (Γ, γ, κ) context: `alpenglow-whitepaper.md:365`

## 3. Reasoning: What The Code Does vs. What The Paper Requires

Intended abstraction:
- `bins` is a total function over `1..Γ` into `needers`, modeling bin-based PS‑P selection for a slice. `PSPConstraint` is meant to capture structural validity aligned with the PS‑P scheme (Def. 46).

Checks enforced by `PSPConstraint`:
- Exactly Γ bins are assigned (`DOMAIN bins = 1..Γ`).
- Every bin maps to a node in `needers`.
- Every “large” stakeholder (defined by `DeterministicBinCount(v) ≥ 1`, i.e., ρᵢ ≥ 1/Γ) appears at least once among the Γ bins.

What Definition 46 requires:
- Step 1 deterministically allocates, for each large stakeholder i, exactly ⌊ρᵢ·Γ⌋ bins to i. This is a minimum obligation that must be satisfied in the final assignment; additional appearances of i are possible only via sampling in Step 3 from the remaining bins.

Gaps and deviations:
- Weaker multiplicity guarantee. The constraint only enforces “≥ 1” bin per large stakeholder, not “≥ ⌊ρᵢ·Γ⌋”. Whenever `DeterministicBinCount(v) > 1`, this permits bin assignments that violate Step 1 of PS‑P (e.g., a validator with ρ = 0.04 and Γ = 100 has ⌊ρ·Γ⌋ = 4 but the model would allow giving it only one bin total).
- No constraint on deterministic/residual separation. As a pure structural check this can be acceptable (abstraction), but to faithfully represent Step 1, the final mapping should ensure each large stakeholder reaches at least its deterministic count ⌊ρᵢ·Γ⌋. The current predicate does not.
- Sufficiency of other conjuncts. The first two conjuncts (domain size and membership) align with PS‑P’s “Γ bins from needers” intent, but do not address the Step 1 multiplicity requirement.

Net effect:
- The current predicate admits bin assignments that cannot be produced by the PS‑P procedure of Definition 46 because the deterministic allocation for large stakeholders may be undersatisfied.

## 4. Conclusion of the Audit

- Faithfulness: Not faithful to PS‑P Step 1. `PSPConstraint` guarantees only a single appearance for each large stakeholder rather than the required ⌊ρᵢ·Γ⌋ minimum.
- Safety vs. completeness: The predicate is permissive (it does not overconstrain), but consequently it allows structurally “valid” configurations that deviate from the whitepaper’s algorithmic guarantee for large stakeholders.
- Verdict: Requires strengthening to match Definition 46.

## 5. Open Questions or Concerns

- Exact vs. at‑least multiplicity: Should the final bin mapping enforce exactly ⌊ρᵢ·Γ⌋ for large stakeholders, or “at least” that many (allowing additional occurrences via residual sampling)? Strictly reading Step 1 + Step 3, “at least ⌊ρᵢ·Γ⌋” is the faithful structural requirement for the final mapping.
- Scope of large stakeholders: The operator uses `LargeStakeholders(needers)` (equivalent to `LargeStakeholdersInNeeders`), i.e., only validators that still need the slice. This operational scoping deviates from a global reading of PS‑P but matches Rotor’s constraint that relays come from needers. Is that intentional and documented?
- Interaction with other constraints: `StructuralBinOK` also includes `ExactBinAssignmentConstraint`. Duplication is harmless, but consider consolidating to a single location for clarity.

## 6. Suggestions for Improvement

- Enforce the Step 1 minimum multiplicity for each large stakeholder:
  ```tla
  PSPConstraint(bins, needers) ==
      /\ DOMAIN bins = 1..GammaTotalShreds
      /\ \A j \in DOMAIN bins : bins[j] \in needers
      /\ \A v \in LargeStakeholders(needers) :
            Cardinality({ j \in DOMAIN bins : bins[j] = v }) 
              >= DeterministicBinCount(v)
  ```
  Rationale: This aligns the final bin assignment with the whitepaper’s Step 1. Large stakeholders may still receive additional bins via Step 3 sampling, so “≥” is correct for the final mapping.

- Optional stronger check (if desired): cap the total multiplicity for each v at `DeterministicBinCount(v)` within the deterministically reserved portion, and leave the remaining bins unconstrained beyond membership. This is more involved and requires representing deterministic vs residual bins.

- Document scoping to `needers`: Call out that PS‑P is instantiated over the current `needers` set to reflect Rotor’s operational constraint “choose relays among nodes that still need the slice.”

- Add a counting lemma for readability and sanity:
  - `\A bins : DOMAIN bins = 1..Γ => \E! mapping : \sum_v Cardinality({ j : bins[j] = v }) = Γ` (implicit from function totality), and
  - `\A v : DeterministicBinCount(v) = 0 => Cardinality({ j : bins[j] = v }) >= 0` (trivial), to separate large/small cases.

File references for context:
- `specs/tla/alpenglow/Rotor.tla:135` PSPConstraint (audited)
- `specs/tla/alpenglow/Rotor.tla:131` LargeStakeholders
- `specs/tla/alpenglow/Rotor.tla:52` DeterministicBinCount
- `alpenglow-whitepaper.md:1154–1158` PS‑P (Definition 46)
- `alpenglow-whitepaper.md:1143` Partitioning (Definition 45)

