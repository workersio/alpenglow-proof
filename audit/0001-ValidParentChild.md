# Audit: ValidParentChild(parent, child)

1. Code that you are auditing.

```tla
ValidParentChild(parent, child) ==
    /\ parent.hash = child.parent   \* Child references parent correctly
    /\ parent.slot < child.slot     \* Parent comes before child
```

2. The whitepaper section and references that the code represents.

- Block structure includes parent hash and parent slot information: alpenglow-whitepaper.md:355 (Definition 3).
- Ordering constraint: a child block must have a higher slot number than its parent: alpenglow-whitepaper.md:245.
- Ancestor/descendant relation is defined purely by following parent links: alpenglow-whitepaper.md:363 (Definition 5).
- Event emission includes the parent hash alongside the block hash, reinforcing the explicit parent reference: alpenglow-whitepaper.md:468.

Related TLA+ context:
- Block record fields `slot`, `hash`, `parent`, `leader`: specs/tla/alpenglow/Blocks.tla:42.
- Type universes for `Slots`, `BlockHashes`, `Validators`: specs/tla/alpenglow/Messages.tla:17.
- The predicate appears in chain-extension logic: specs/tla/alpenglow/Blocks.tla:86 and specs/tla/alpenglow/Blocks.tla:203.

3. The reasoning behind the code and what the whitepaper claims.

- Parent reference by hash:
  - Whitepaper Definition 3 states that a block’s data contains both the slot and hash of its parent. The predicate’s first conjunct `parent.hash = child.parent` precisely checks that the child’s embedded parent pointer matches the actual parent block’s hash. This aligns with the model where explicit parent links define the chain topology.
- Slot monotonicity across parent-child:
  - The “Correctness” text asserts “a child block has to have a higher slot number than its parent.” The predicate’s second conjunct `parent.slot < child.slot` enforces strict monotonicity. This is sufficient to preclude cycles and is compatible with the possibility of skipped slots (the spec allows non-consecutive slots between parent and child), also reflected elsewhere in the whitepaper via skip certificates.
- Ancestry defined via parent links:
  - Definition 5 defines ancestry by iterating parent links. Ensuring valid parent-child links via this predicate is the minimal structural invariant required to make ancestry well-defined. Stronger liveness/safety constraints (e.g., when a leader may build, notarization prerequisites, window/ParentReady logic) are enforced by higher-level protocol rules (Votor/Pool/ParentReady), not by this structural predicate.

4. The conclusion of the audit.

- The predicate `ValidParentChild` is correct and faithful to the whitepaper abstractions for parent-child linkage:
  - It enforces that the child’s parent pointer matches the parent’s hash (Definition 3) and that the child’s slot is strictly greater than the parent’s (Correctness statement).
  - It does not over-constrain the relation (e.g., it does not require consecutive slots), which is consistent with the presence of skip slots in the protocol.
  - It is properly scoped as a structural check; notarization/fallback/window rules are rightly handled elsewhere.

5. Any open questions or concerns.

- Type preconditions: The predicate as written assumes `parent` and `child` are well-formed blocks. While usage sites appear to guarantee this (e.g., `ExtendsChain` quantifies over a chain of blocks), the predicate itself does not assert `parent \in Block /\ child \in Block`. This is acceptable in TLA+ style but worth noting if reused in isolation.
- Uniqueness of hashes: The spec assumes each block hash uniquely identifies a block. That invariant is not stated here; it is typically assumed via the model or enforced elsewhere. If not captured in another invariant, consider adding an explicit uniqueness property (no two distinct blocks share a hash) to support reasoning that `parent.hash = child.parent` identifies a unique parent.
- Genesis edge case: The predicate is agnostic to genesis. This is fine; `IsValidBlock` in the same module prohibits non-genesis self-parenting and models genesis appropriately. Just ensure callers don’t try to treat a non-block as `parent`.
- Window/ParentReady constraints: The whitepaper requires additional conditions for the first slot in a leader window before proposing (ParentReady). Those are not part of structural validity and are expected to be enforced by Votor/Pool logic; confirm those modules integrate with chain extension points that use `ValidParentChild`.

6. Any suggestions for improvement.

- Optional type guards for defensive clarity (if helpful at call sites that aren’t obviously typed):
  - Extend the predicate to `ValidParentChild(parent, child) == /\ parent \in Block /\ child \in Block /\ parent.hash = child.parent /\ parent.slot < child.slot`.
  - Alternatively, keep `ValidParentChild` lean and introduce a separate `WellFormedParentChild(parent, child)` that includes type checks, leaving the current predicate unchanged for proofs that already assume well-formedness.
- Add a global uniqueness invariant for block hashes if not already present (e.g., “No two distinct blocks in the universe share the same `hash`”). This simplifies downstream reasoning that a hash pointer selects a unique parent.
- Cross-reference comment: Add a brief inline comment pointing to the whitepaper citations (Correctness and Definition 3) near this predicate to aid readers traversing spec <-> paper.
- Consider a convenience lemma: Prove that `ValidParentChild` implies strict acyclicity on chains (due to slot monotonicity), and that repeated application yields a strict partial order, connecting directly with the `IsAncestor` machinery already present in this module.

