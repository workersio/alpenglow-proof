# Audit: Rotor.BinsToRelaySet, PSPSelect, RequiredResilientStake

## 1. Code Under Audit

```
BinsToRelaySet(bins) ==
    { bins[j] : j \in DOMAIN bins }

\* PS-P relay selection using bin-based approach
PSPSelect(needers, nextLeader) ==
    LET bins == PSPBinAssignment(needers, nextLeader)
    IN IF DOMAIN bins = {} THEN {} ELSE BinsToRelaySet(bins)

\* Minimum residual stake required after worst allowed relay failures
RequiredResilientStake == RotorMinRelayStake
```

Context in spec:
- `specs/tla/alpenglow/Rotor.tla:112` BinsToRelaySet
- `specs/tla/alpenglow/Rotor.tla:116` PSPSelect (wrapper over `PSPBinAssignment`)
- `specs/tla/alpenglow/Rotor.tla:121` RequiredResilientStake alias

Upstream and downstream references:
- `PSPBinAssignment(needers, nextLeader)` in `specs/tla/alpenglow/Rotor.tla:91` (constructs bins; may return empty-domain function on failure paths)
- `StructuralBinOK`, `PSPConstraint`, `ExactBinAssignmentConstraint` constrain bins (same module)
- `BinsToRelaySet` is used by `BinCandidates`, `RotorSelectSound` and resilience checks
- Stake and validator primitives from `Certificates.tla`: `StakeMap`, `TotalStake`, `CalculateStake`

## 2. Whitepaper Sections and References

- PS-P (Partition Sampling), Step 1–3 — Definition 46:
  - alpenglow-whitepaper.md:1154–1159
- Rotor success condition — Definition 6:
  - alpenglow-whitepaper.md:414
- Erasure coding parameters Γ (total shreds/relays), γ (data shreds): Section 2.2 context

## 3. Reasoning vs Whitepaper

What the paper prescribes:
- PS-P generates exactly Γ samples by partitioning stake into Γ bins and sampling one node per bin (Definition 46). A node may appear in multiple bins (especially large stakeholders after Step 1).
- Rotor is successful if leader is correct and at least γ of the corresponding relays are correct (Definition 6). The notion of “γ correct relays” refers to distinct relays.

Spec’s abstractions here:
- BinsToRelaySet(bins) maps a bin assignment `[1..Γ -> needers]` to the set of distinct relays assigned (collapsing multiplicity). This aligns with Definition 6: success depends on the number of distinct correct relays, not on how many bins a single relay holds.
- PSPSelect computes `bins` via `PSPBinAssignment` and returns a set of relays if `DOMAIN bins # {}`; otherwise returns `{}` as a failure signal. This design makes PSPSelect a thin adapter from bin-level PS-P to relay sets used elsewhere.
- RequiredResilientStake == RotorMinRelayStake exposes the minimum relay-set stake threshold as a named alias. The whitepaper does not define such a parameter explicitly; this is an additional robustness constraint used in the spec’s `FailureResilient` predicate.

Correctness observations:
- Set semantics for relays: Using a set for relays ensures we do not double count stake or the number of correct relays when the same node appears in multiple bins. This is conservative for success (duplicates do not inflate `|relays ∩ correctNodes|`) and matches Definition 6’s intent.
- Compatibility with structural constraints: When `bins` satisfies structural constraints (domain `1..Γ`, values in `needers`), `BinsToRelaySet(bins)` yields a subset of `needers`. This matches downstream expectations such as `SliceDelivered` and the rotor selection checks.
- Dependence on PSPBinAssignment: PSPSelect’s correctness and completeness hinge entirely on `PSPBinAssignment`. In the current spec, `PSPBinAssignment` returns an empty-domain function in certain conditions (e.g., “not enough needers”), causing PSPSelect to return `{}`. However, PS-P in the whitepaper does not require `|needers| ≥ Γ`; duplicates across bins are allowed. Therefore, this early failure mode is stricter than Definition 46 and can reject scenarios that PS-P would handle.

Modeling cautions:
- Multiplicity loss is intentional: After converting to a set, information about bin multiplicity is lost. This is appropriate for success and stake checks but means subsequent predicates cannot reason about how many bins each relay holds. If such reasoning is needed (e.g., risk concentration per relay), it must be done on `bins` prior to conversion.
- Selection constraints not enforced here: PSPSelect does not enforce `StructuralBinOK` or `ResilienceOK`; these are checked in other places (e.g., `BinCandidates`, `RotorSelectSound`). There is a gap between construction and enforcement if the code path uses PSPSelect directly.

## 4. Conclusion

- BinsToRelaySet correctly abstracts a bin assignment to a distinct-relay set, consistent with Definition 6’s “γ correct relays”.
- PSPSelect is a reasonable adapter but inherits shortcomings from PSPBinAssignment: returning `{}` when `|needers| < Γ` contradicts PS-P, which permits duplicates across bins. Also, PSPSelect itself does not ensure structural feasibility; that is only asserted a posteriori by invariants.
- RequiredResilientStake is an alias to a model parameter (RotorMinRelayStake); it is not anchored in the whitepaper and is documented in-code as an extra robustness condition.

## 5. Open Questions / Concerns

- Should PSPSelect enforce structural feasibility (e.g., pick from `BinCandidates`) rather than rely on a later invariant witness? Presently, a non-empty set might not correspond to any structurally valid bins.
- Do we intend PS-P to operate when `|needers| < Γ`? The paper allows duplicates; the current PSPBinAssignment sometimes fails in this case.
- Is there any place we must reason about multiplicity-induced risk concentration (one relay in many bins)? If so, collapsing to sets too early will hide that information.
- Is `RequiredResilientStake` used consistently with `FailureResilient` and rotor selection thresholds, or should we collapse to a single parameter to avoid ambiguity?

## 6. Suggestions for Improvement

- Bind PSPSelect to structural feasibility:
  - Option A: `PSPSelect(needers, nextLeader) == CHOOSE sel \in { BinsToRelaySet(bins) : bins \in BinCandidates(_, needers, nextLeader) } : TRUE` (or `{}` if the set is empty).
  - Option B: Keep PSPSelect as-is but have `RotorSelect` construct from `BinCandidates` and check `StructuralBinOK` directly.
- Align PSPBinAssignment with PS-P for `|needers| < Γ`:
  - Remove the “not enough needers ⇒ empty-domain function” branch; sampling per bin can select the same node multiple times. Always return a function on domain `1..GammaTotalShreds`.
- Document BinsToRelaySet explicitly:
  - Clarify in the comment that it produces the set of distinct relays and that success (Def. 6) and resilience checks are done over distinct relays, not per-bin multiplicities.
- If concentration risk needs modeling:
  - Add an optional predicate (e.g., `MaxBinsPerRelayOK(bins)`) to bound how many bins any single relay can hold, if desired for robustness analysis; otherwise, keep multiplicity abstract.
- Parameter clarity:
  - Either remove `RequiredResilientStake` (use `RotorMinRelayStake` directly) or clearly state it as an alias to avoid confusion.

Whitepaper alignment impact:
- Enforcing structural validity at selection time and allowing duplicates when `|needers| < Γ` will make PSPSelect consistent with Definition 46 while keeping BinsToRelaySet faithful to Definition 6 for success checks.

