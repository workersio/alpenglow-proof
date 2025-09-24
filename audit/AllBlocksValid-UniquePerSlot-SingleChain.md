# Audit: AllBlocksValid, UniqueBlocksPerSlot, SingleChain

## 1. Code Under Audit

```
\* All blocks in the system must be valid
AllBlocksValid(blocks) ==
    \A b \in blocks : IsValidBlock(b)

\* No two different blocks can be finalized in the same slot
\* This is a key safety property!
UniqueBlocksPerSlot(finalizedBlocks) ==
    \A b1, b2 \in finalizedBlocks :
        b1.slot = b2.slot => b1.hash = b2.hash

\* All finalized blocks must form a single chain (no forks)
\* This is THE main safety property (Theorem 1 from whitepaper)
SingleChain(finalizedBlocks) ==
    \A b1, b2 \in finalizedBlocks :
        InSameChain(b1, b2, finalizedBlocks)
```

Dependencies in the same module:
- `specs/tla/alpenglow/Blocks.tla:67` — `IsValidBlock(b)`
- `specs/tla/alpenglow/Blocks.tla:129` — `InSameChain(b1, b2, allBlocks)` (uses `IsAncestor` defined at `specs/tla/alpenglow/Blocks.tla:105`)

Module-level type sources (imported sorts):
- `specs/tla/alpenglow/Messages.tla:13` — `Validators`
- `specs/tla/alpenglow/Messages.tla:14` — `Slots`
- `specs/tla/alpenglow/Messages.tla:15` — `BlockHashes`

Note: The audited formulas appear at `specs/tla/alpenglow/Blocks.tla:200+`.

## 2. Whitepaper Sections and References

- Block structure and ancestry:
  - `alpenglow-whitepaper.md:351` — Definition 3 (block)
  - `alpenglow-whitepaper.md:357` — Definition 4 (block hash)
  - `alpenglow-whitepaper.md:363` — Definition 5 (ancestor and descendant)
- Correctness overview and chain semantics:
  - `alpenglow-whitepaper.md:243` — Correctness: finalized blocks form a single chain; finalizing b finalizes all ancestors
  - `alpenglow-whitepaper.md:541` — When a block is finalized, all its ancestors are finalized first
- Safety (main theorem):
  - `alpenglow-whitepaper.md:930` — Theorem 1 (safety): later finalized blocks are descendants of earlier finalized blocks

Related spec linkage (for closure under ancestors on finalization):
- `specs/tla/alpenglow/MainProtocol.tla:263` — `finalized' = ... \union GetAncestors(block, blocks)`

## 3. Reasoning: What the Code Asserts vs. Whitepaper Claims

- AllBlocksValid
  - Code: `AllBlocksValid(blocks) == \A b \in blocks : IsValidBlock(b)`.
  - `IsValidBlock` checks field membership (`slot \in Slots`, `hash \in BlockHashes`, `parent \in BlockHashes`, `leader \in Validators`) and enforces non-genesis blocks do not self-parent (`b.slot > 0 => b.parent # b.hash`). See `specs/tla/alpenglow/Blocks.tla:67`.
  - Whitepaper alignment: Definition 3 (block) specifies contents including parent metadata; Definition 4 distinguishes block hashes; Definition 5 introduces ancestry. The validity predicate models structural well-formedness at this abstraction level (types and non-self-parenting for non-genesis). It intentionally does not require the parent to exist locally (consistent with asynchronous receipt), nor enforce slot monotonicity globally (that is captured by `ValidParentChild` and chain predicates elsewhere in the module).

- UniqueBlocksPerSlot
  - Code: No two finalized blocks at the same slot may differ in hash: `b1.slot = b2.slot => b1.hash = b2.hash`.
  - Whitepaper alignment: This is an equal-slot corollary of Theorem 1 (if two finalized blocks have the same slot, neither can be a proper ancestor of the other, hence they must be identical). The spec further supports uniqueness at the certificate level via lemmas (e.g., Lemma 24 — unique notarization), but for finalization the theorem suffices.

- SingleChain
  - Code: All finalized blocks pairwise lie on the same chain: `\A b1,b2 \in finalizedBlocks : InSameChain(b1,b2,finalizedBlocks)`.
  - `InSameChain` is defined as ancestor-or-descendant over a provided set (`allBlocks` parameter). In this use, the set is `finalizedBlocks`.
  - Whitepaper alignment: Theorem 1 states that if a block b is finalized at slot s, any later finalized block b' at slot s' ≥ s is a descendant of b. This exactly implies pairwise chain comparability of finalized blocks.
  - Important modeling note: Because `InSameChain` follows parent links only within the provided `allBlocks` set, using `finalizedBlocks` is sound only if finalized sets are closed under ancestry. The protocol enforces this: MainProtocol finalization action unions `GetAncestors(block, blocks)` into `finalized[v]` (see `specs/tla/alpenglow/MainProtocol.tla:263`), matching the whitepaper’s statement that finalizing a block finalizes all its ancestors (`alpenglow-whitepaper.md:541`). Thus, ancestor paths needed to witness comparability are present among finalized blocks, making this formulation correct.

## 4. Conclusion

- All three predicates faithfully capture the whitepaper’s abstractions:
  - `AllBlocksValid` matches structural well-formedness of blocks per Definitions 3–4 (and the non-self-parenting constraint for non-genesis).
  - `UniqueBlocksPerSlot` is a direct corollary of safety (Theorem 1) and is an appropriate, readable safety check at the finalization layer.
  - `SingleChain` captures the main safety theorem in a set-based form, relying on the finalized-ancestors closure enforced by the protocol.
- Cross-checks:
  - Dependencies (`IsValidBlock`, `InSameChain`, `IsAncestor`) are defined in the same module with expected semantics.
  - Finalization closure is implemented in `MainProtocol` in accordance with the whitepaper, ensuring the `SingleChain` check is meaningful when parameterized with `finalizedBlocks`.

Overall, the audited predicates correctly encode the safety assertions stated in the whitepaper and are consistent with the rest of the TLA+ spec.

## 5. Open Questions / Concerns

- Scope of `AllBlocksValid`:
  - The predicate does not require a block’s parent to exist in `blocks`. This is often intentional (asynchronous receipt); if a stronger invariant is desired (e.g., at quiescent points), consider an optional “parent-exists” check against `blocks \cup {GenesisBlock}`.

- Slot monotonicity at the validation layer:
  - Whitepaper says a child must have a higher slot than its parent. The spec enforces this via `ValidParentChild` and in proposer actions, not inside `IsValidBlock`. That separation is fine, but if you want a single “global well-formedness” predicate, you might add a complementary invariant over the extant edges in `blocks`.

- Redundancy between `SingleChain` and `UniqueBlocksPerSlot`:
  - Given blocks in equal slots cannot be ancestor/descendant, `SingleChain` implies `UniqueBlocksPerSlot`. Keeping the latter is still helpful for localized debugging and more precise counterexamples.

- Parameterization of `InSameChain`:
  - Current use with `finalizedBlocks` is correct because of finalized-ancestor closure. If reused elsewhere with a set that is not ancestor-closed, results could be misleading. Consider documenting this precondition near the definition.

## 6. Suggestions for Improvement

- Document finalized-closure precondition:
  - Near `SingleChain`, add a brief note that it presumes `finalizedBlocks` is closed under ancestry, as guaranteed by `FinalizeBlock`.

- Optional stronger validation bundle:
  - Add a convenience predicate that combines structure and local chain constraints:
    - e.g., `WellFormedChain(blocks) == AllBlocksValid(blocks) /\ \A c \in blocks \ {GenesisBlock} : \E p \in blocks : ValidParentChild(p,c)`
    - Use only in contexts where parent existence is expected (e.g., after repair or in steady state), not as a global invariant during dissemination.

- Clarify genesis conventions:
  - The spec models genesis as slot 0 and self-parenting. Consider adding a one-line comment in `IsValidBlock` referencing genesis conventions to help readers reconcile with the paper’s slot notation.

---

File pointers for quick navigation:
- Blocks invariants: `specs/tla/alpenglow/Blocks.tla:200`
- IsValidBlock: `specs/tla/alpenglow/Blocks.tla:67`
- InSameChain / IsAncestor: `specs/tla/alpenglow/Blocks.tla:129`, `specs/tla/alpenglow/Blocks.tla:105`
- Finalization closure: `specs/tla/alpenglow/MainProtocol.tla:263`
- Whitepaper Theorem 1: `alpenglow-whitepaper.md:930`
- Whitepaper Definitions 3–5: `alpenglow-whitepaper.md:351`, `alpenglow-whitepaper.md:357`, `alpenglow-whitepaper.md:363`

