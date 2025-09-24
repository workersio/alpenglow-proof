# Audit: ConflictingBlocks

1. Code that you are auditing

```
ConflictingBlocks(b1, b2) ==
    /\ b1.slot = b2.slot     \* Same slot
    /\ b1.hash # b2.hash     \* Different blocks!
```

Source: `specs/tla/alpenglow/Blocks.tla:78`

2. The whitepaper section and references that the code represents

- Block structure and fields (slot, parent, hash): `alpenglow-whitepaper.md:351` (Definition 3), `alpenglow-whitepaper.md:357` (Definition 4), `alpenglow-whitepaper.md:363` (Definition 5)
- Slots and leader windows (context for “same slot”): `alpenglow-whitepaper.md:53`, `alpenglow-whitepaper.md:222`
- Collision-resistant hashing assumption (using hash as unique identifier): `alpenglow-whitepaper.md:259`
- Uniqueness of notarized block per slot (safety lemmas): `alpenglow-whitepaper.md:851` (Lemma 23), `alpenglow-whitepaper.md:855` (Lemma 24)
- Safety goal (finalized blocks form a single chain): `alpenglow-whitepaper.md:930` (Theorem 1)

3. Reasoning behind the code and what the whitepaper claims

- Intent: The predicate captures the abstract notion of two distinct blocks for the same slot. It is a minimal, structural definition of a “slot conflict.”
- Same slot: `b1.slot = b2.slot` leverages the slot field defined in Definition 3. In Alpenglow, every block is associated with a natural-numbered slot.
- Different blocks: `b1.hash # b2.hash` uses the block hash (Definition 4) as the unique identifier. The whitepaper explicitly assumes collision-resistant hashing (SHA256), making equality on hash an appropriate proxy for block identity. See `alpenglow-whitepaper.md:259` and the Merkle-root definition of `hash(b)`.
- Relation to safety: The whitepaper proves that at most one block can be notarized per slot (Lemma 24), building on Lemma 23 and the “vote once per slot” property. The ConflictingBlocks predicate is a convenient way to express the undesirable condition that proofs must rule out. It also pairs with invariants like `UniqueBlocksPerSlot` and single-chain properties defined elsewhere in the spec (`specs/tla/alpenglow/Blocks.tla`), which correspond to Theorem 1’s safety statement.

4. Conclusion of the audit

- Correctness: The predicate faithfully represents the abstract condition “two different blocks in the same slot,” consistent with Definitions 3–4 and the collision-resistant hash assumption. It aligns with the whitepaper’s safety lemmas (23–24) that ensure this situation cannot occur for notarized/finalized blocks in a correct execution.
- Scope: The definition is intentionally minimal and free of implementation detail, appropriate for use as a helper in safety arguments and invariants. No semantic mismatch with the whitepaper was found.

5. Open questions or concerns

- Validity preconditions: The predicate itself does not assert `IsValidBlock(b1)`/`IsValidBlock(b2)`. In practice it is typically used under contexts where block validity is already established, so this is likely intentional. If used standalone in proofs, callers should ensure blocks are well-formed.
- Genesis considerations: The model’s `GenesisBlock` uses slot 0. If another block at slot 0 were introduced (which should be disallowed by construction), `ConflictingBlocks` would correctly flag the conflict. This seems fine, but consider whether proofs implicitly exclude slot 0 where necessary.
- Identity via hash: Using `hash` as the identifier relies on collision resistance (stated explicitly in the whitepaper). If a stronger “by construction unique” invariant over `blocks` is desired in the model, it could be added separately, but is not required for this helper predicate.

6. Suggestions for improvement

- Cross-reference in code: Add an inline comment in `Blocks.tla` pointing directly to Lemma 24 (and optionally Lemma 23) with file/line anchors for fast navigation.
- Optional invariant helpers: Consider adding a companion property for readability, e.g.,
  - `NoSlotConflicts(blocks) == \A b1, b2 \in blocks : b1.slot = b2.slot => b1.hash = b2.hash`
  This mirrors the existing `UniqueBlocksPerSlot(finalizedBlocks)` but at different scopes (e.g., all proposed, all notarized, all finalized).
- Naming clarity (optional): If preferred, rename to `SlotConflict(b1, b2)` to emphasize the semantics. The current name is already clear and consistent with style in `Certificates.tla` (see `ConflictingCertificates`).

