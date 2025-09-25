## 1. Code Under Audit

```tla
SliceDelivered(slice, relays, correctNodes) ==
    /\ slice.leader \in correctNodes  \* Leader is correct
    /\ Cardinality(relays \cap correctNodes) >= GammaDataShreds  \* Enough correct relays
    /\ relays \subseteq slice.needers  \* Relays are from nodes that need the slice
```

## 2. Whitepaper Sections and References

- Success condition and resilience
  - `alpenglow-whitepaper.md:414`: Definition 6 — Rotor success (leader correct and at least γ correct relays).
  - `alpenglow-whitepaper.md:416`: Resilience statement — if Definition 6 holds, all correct nodes receive the block.
  - `alpenglow-whitepaper.md:418`: Lemma 7 — κ = Γ/γ > 5/3 resilience scaling and γ → ∞ discussion.

- Constants and parameterization
  - `specs/tla/alpenglow/Rotor.tla:22`: Constant `GammaDataShreds` (γ) is declared.
  - `specs/tla/alpenglow/Rotor.tla:29`: Assumptions include `GammaDataShreds \in Nat \ {0}` and `3 * GammaTotalShreds > 5 * GammaDataShreds` (κ > 5/3).

- Usage in the protocol
  - `specs/tla/alpenglow/MainProtocol.tla:424`: Success path requires a correct leader.
  - `specs/tla/alpenglow/MainProtocol.tla:433`: Checks `RotorSuccessful(block.leader, relays, CorrectNodes)`.
  - `specs/tla/alpenglow/MainProtocol.tla:434`: Invokes `SliceDelivered([leader |-> block.leader, needers |-> needers], relays, CorrectNodes)` before updating availability for all correct nodes.

## 3. Reasoning and Whitepaper Alignment

- Abstraction intent
  - The predicate encodes the sufficient conditions for successful dissemination as per Definition 6: a correct leader and ≥ γ correct relays.
  - It models the two-hop delivery by requiring relays to be chosen from `slice.needers`, matching the module’s internal selection workflow (Rotor selects from needers), though the whitepaper does not mandate this restriction explicitly.

- Relating to resilience claim
  - When combined with the `RotorDisseminateSuccess` action, `SliceDelivered` is used as a gate ensuring the model updates `blockAvailability` for all `CorrectNodes`, directly reflecting the “all correct nodes will receive the block” text (`alpenglow-whitepaper.md:416`).

- External operators and types
  - `Cardinality` is from `FiniteSets`; `GammaDataShreds` is a constant from Rotor; `correctNodes` is a parameter (typically instantiated as `CorrectNodes` from the main protocol); `slice` is a record with fields `leader` and `needers` (constructed at the call site in `MainProtocol.tla:434`).

- Duplication with `RotorSuccessful`
  - `RotorSuccessful(leader, relays, correctNodes)` already checks the first two conjuncts of `SliceDelivered`. In `RotorDisseminateSuccess`, both are checked, making the first two conjuncts redundant. This redundancy is safe but could be streamlined.

## 4. Audit Conclusion

- The predicate accurately captures the success preconditions from Definition 6 and is used in the correct place to realize the whitepaper’s resilience claim (updating availability for all correct nodes on success).
- The chosen abstraction (predicate-only, no explicit per-shred modeling) is appropriate for TLA+ and keeps focus on correctness thresholds (γ) rather than implementation detail.
- The restriction `relays \subseteq slice.needers` is a modeling choice consistent with how `RotorSelect` is parameterized in the spec; it does not contradict the whitepaper and improves internal consistency.

## 5. Open Questions or Concerns

- Redundant checks: Given `RotorDisseminateSuccess` also asserts `RotorSuccessful`, `SliceDelivered` restates two conditions. This is harmless but redundant.
- Naming vs. scope: The name “SliceDelivered” suggests per-slice semantics, yet it is used at block granularity in `MainProtocol`. This is an acceptable abstraction, but a brief comment linking this predicate to the block-level update could reduce ambiguity.
- Non-emptiness: The predicate does not assert `relays # {}` or `slice.needers # {}`. These are enforced at the call site, but adding an optional invariant or documentation note could make the intended preconditions clearer.

## 6. Suggestions for Improvement

- Refine responsibilities to avoid duplication:
  - Option A: Make `SliceDelivered` the single success predicate and drop the explicit `RotorSuccessful` check at the call site.
  - Option B: Keep `RotorSuccessful` at the call site and trim `SliceDelivered` to only encode the structural constraint `relays \subseteq slice.needers` (rename it to `RelaysFromNeeders`), paired with a comment citing the two-hop model.

- Add a brief comment at definition or call site clarifying that `SliceDelivered` abstracts the entire block dissemination once γ correct relays participate, even though the name references a slice.

- Optionally add a typing helper or comment indicating `slice.needers \subseteq Validators` and `relays \subseteq Validators` are guaranteed by `RotorSelect`, to surface assumptions for readers.

