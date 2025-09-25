# Audit: ShouldEmitParentReady

## 1. Code Under Audit

```tla
ShouldEmitParentReady(pool, slot, parentHash, parentSlot) ==
    /\ IsFirstSlotOfWindow(slot)
    /\ (HasNotarizationCert(pool, parentSlot, parentHash) \/
        HasNotarFallbackCert(pool, parentSlot, parentHash))
    /\ \A s \in (parentSlot+1)..(slot-1) : HasSkipCert(pool, s)
```

Defined at: `specs/tla/alpenglow/VoteStorage.tla:268`.

## 2. Whitepaper Mapping

- ParentReady definition (source of truth):
  - `alpenglow-whitepaper.md:546` — Definition 15: “ParentReady(s, hash(b)): Slot s is the first of its leader window, and Pool holds a notarization or notar-fallback certificate for a previous block b, and skip certificates for every slot s' since b, i.e., for slot(b) < s' < s.”
- Related, reinforces semantics and timing:
  - `alpenglow-whitepaper.md:943` (Lemma 33) — ParentReady schedules timeouts for the window.
  - `alpenglow-whitepaper.md:1016` (Lemma 40) — With timeouts for a window, the next window’s ParentReady eventually follows.

References in codebase used by this predicate:

- Window/slot helpers:
  - `specs/tla/alpenglow/Blocks.tla:192` — `IsFirstSlotOfWindow(slot)`.
- Certificate queries (same module as the predicate):
  - `specs/tla/alpenglow/VoteStorage.tla:221` — `HasNotarizationCert(pool, slot, blockHash)`.
  - `specs/tla/alpenglow/VoteStorage.tla:227` — `HasNotarFallbackCert(pool, slot, blockHash)`.
  - `specs/tla/alpenglow/VoteStorage.tla:233` — `HasSkipCert(pool, slot)`.
- Where this predicate is consumed:
  - Event emission: `specs/tla/alpenglow/MainProtocol.tla:669`–`specs/tla/alpenglow/MainProtocol.tla:688` — `EmitParentReady` uses `ShouldEmitParentReady` to set state and schedule timeouts.
  - Proposer (optimistic variant): `specs/tla/alpenglow/MainProtocol.tla:337`–`:357` — `HonestProposeBlockOptimistic` gates first-slot proposals on `ShouldEmitParentReady`.

## 3. Reasoning vs Whitepaper

Whitepaper Definition 15 requires, for ParentReady(s, hash(b)):

- First-of-window: “Slot s is the first of its leader window.”
  - Implemented by `IsFirstSlotOfWindow(slot)`.
- Certified predecessor: “Pool holds a notarization or notar-fallback certificate for a previous block b.”
  - Implemented by `HasNotarizationCert(pool, parentSlot, parentHash) \/ HasNotarFallbackCert(...)`.
- Filled gaps by skips: “skip certificates for every slot s' since b, i.e., slot(b) < s' < s.”
  - Implemented by `\A s \in (parentSlot+1)..(slot-1) : HasSkipCert(pool, s)`.

Correctness details and edge cases:

- Off-by-one and empty-range: The range `(parentSlot+1)..(slot-1)` matches `slot(b) < s' < s`. If `slot = parentSlot + 1`, the range is empty and the universal quantification is trivially true, which is consistent (no skips between adjacent slots).
- Choice of certificate type: The OR over notarization and notar-fallback exactly matches “notarization or notar-fallback certificate”.
- Window gating interaction: `EmitParentReady` uses this predicate to mark `ParentReady` and then `HandleParentReady` schedules timeouts for the entire window (cf. Lemma 33). The strict proposer path separately requires the state flag for first slots, consistent with Def. 15.
- Genesis handling: The spec seeds slot 1 with ParentReady by fiat (`specs/tla/alpenglow/MainProtocol.tla:157`–`:176`), so this predicate is not relied upon for the genesis transition, aligning with the paper’s abstract genesis.

## 4. Conclusion

The predicate `ShouldEmitParentReady` faithfully encodes Definition 15 from the whitepaper:

- It checks that s is the first slot of a leader window;
- It requires the pool to contain either a notarization or notar-fallback certificate for a previous block b;
- It requires skip certificates for exactly the intervening slots `slot(b) < s' < s`.

The usage sites (`EmitParentReady`, optimistic proposer gating) match the intended semantics: ParentReady is emitted when prerequisites hold and then drives timeout scheduling for the entire window.

Subject to the minor concern below about explicitly constraining `parentSlot < slot`, the implementation is correct relative to the whitepaper.

## 5. Open Questions / Concerns

- Missing explicit “previous” guard: Definition 15 says “previous block b”. The current predicate does not assert `parentSlot < slot`. In normal operation the chosen `parent` in proposer flows respects `parent.slot < slot`, but `EmitParentReady` quantifies `p ∈ blocks` without constraining `p.slot < s`. This allows a theoretical (though likely benign) satisfaction if a future-slot certificate existed; the skip-range becomes empty, and only the certificate check remains.
- Parent consistency: The predicate accepts any certified block `b` strictly before `s` that is bridged by skips. The whitepaper does not require choosing the “closest” such `b`, but that is the only one that can satisfy the skip-coverage if there were multiple certified blocks in different slots; nonetheless, the selection is nondeterministic in the model and could be made explicit if desired.
- Genesis as a parent: While genesis is treated specially and seeded, the predicate could technically be invoked with `parentSlot = 0`. This is harmless because no notarization/notar-fallback certificate can exist for genesis, but an explicit exclusion might aid readability.

## 6. Suggestions for Improvement

- Strengthen the predicate to reflect “previous block” explicitly:
  - Add `parentSlot < slot` to `ShouldEmitParentReady` for clarity and to match Definition 15 precisely.
  - Alternatively/additionally, restrict the emitter to previous blocks: change `EmitParentReady`’s quantification to `p ∈ blocks /\ p.slot < s`.
- Document the empty-range convention inline: a short comment that `(a)..(b)` is empty when `a > b`, making the off-by-one and adjacency case self-evident to readers unfamiliar with TLA+ ranges.
- Optional invariant for model assurance: assert that whenever `ShouldEmitParentReady(pool, s, h, ps)` holds, `ps < s` (or equivalently that the emitter selects `p.slot < s`). This provides an additional check during model checking runs and ties usage to the whitepaper’s “previous block” wording.

