# Audit: Ancestry and Chain Predicates (IsDescendant / GetAncestors / InSameChain)

## 1. Code Under Audit

```tla
IsDescendant(b1, b2, allBlocks) == 
    IsAncestor(b2, b1, allBlocks)

\* Get all ancestors of a block (its entire history)
GetAncestors(b, allBlocks) ==
    {ancestor \in allBlocks : IsAncestor(ancestor, b, allBlocks)}

\* Check if two blocks are in the same chain
InSameChain(b1, b2, allBlocks) ==
    \/ IsAncestor(b1, b2, allBlocks)
    \/ IsDescendant(b1, b2, allBlocks)
```

Context: these definitions live in `specs/tla/alpenglow/Blocks.tla:121`, `:125`, and `:129` and hinge on `IsAncestor` defined at `specs/tla/alpenglow/Blocks.tla:103`.

## 2. Whitepaper Sections and References

- Ancestor/descendant definition: `alpenglow-whitepaper.md:363` (Definition 5).
- Block and block-hash context: `alpenglow-whitepaper.md:351` (Def. 3), `:357` (Def. 4).
- Correctness statement (finalized blocks form a chain; ancestors of finalized are finalized): `alpenglow-whitepaper.md:243`.
- Safety theorem (single chain of finalized blocks): `alpenglow-whitepaper.md:930` (Theorem 1).

## 3. Reasoning and Correspondence to Whitepaper

- Dependency: All three predicates rely on `IsAncestor(b1, b2, allBlocks)` from `specs/tla/alpenglow/Blocks.tla:103`. In the spec, `IsAncestor` recursively follows `parent` links from `b2` backwards and succeeds if it reaches `b1`. It also returns true for `b1 = b2`, aligning with Definition 5’s note that a block is its own ancestor/descendant.

- IsDescendant: Defined as `IsAncestor(b2, b1, allBlocks)`. This is the direct inverse of ancestor and matches the definition in the paper: if `b'` is an ancestor of `b`, then `b` is a descendant of `b'`.

- GetAncestors: Set-comprehension over `allBlocks` selecting those `ancestor` that satisfy `IsAncestor(ancestor, b, allBlocks)`. It includes `b` itself, consistent with Definition 5 (“b is its own ancestor”). This is used to enforce “when a block is finalized, all ancestors are finalized” by unioning ancestors into `finalized` (see `specs/tla/alpenglow/MainProtocol.tla:263`). This operationalizes the correctness statement at `alpenglow-whitepaper.md:243`.

- InSameChain: Defined as `IsAncestor(b1, b2, allBlocks) \/ IsDescendant(b1, b2, allBlocks)`, which is equivalent to `IsAncestor(b1, b2) \/ IsAncestor(b2, b1)`. This encodes comparability by ancestry: two blocks are in the same chain iff one is an ancestor of the other. In `specs/tla/alpenglow/Blocks.tla:222`, this is used to define `SingleChain(finalizedBlocks)`, matching the single-chain safety requirement implied by Theorem 1 (`alpenglow-whitepaper.md:930`).

- Genesis modeling and termination: `IsAncestor` treats “hit genesis” as `b.parent = b.hash`. Genesis is defined self-parented (see `specs/tla/alpenglow/Blocks.tla:53`–`:58`), and non-genesis blocks are constrained to not be self-parented (see `IsValidBlock`, `:67`–`:74`). This sentinel condition ensures the recursion terminates at genesis, and is consistent with the paper’s notion of a notional genesis block (`alpenglow-whitepaper.md:243`).

- Usage in safety properties: The main safety invariant uses `IsAncestor` over the global block set to encode Theorem 1 (see `specs/tla/alpenglow/MainProtocol.tla:968` and `:1006`). The `SingleChain` helper in `Blocks.tla` rephrases the same idea in terms of `InSameChain` but is scoped to `finalizedBlocks`; this is sound because `FinalizeBlock` finalizes `GetAncestors(b, blocks)` ensuring ancestor-closure for finalized sets (`specs/tla/alpenglow/MainProtocol.tla:263`).

Collectively, these definitions faithfully implement Definition 5 and support the safety claims (single-chain finality) in the whitepaper.

## 4. Conclusion

- The audited predicates precisely capture the ancestor/descendant relation (Def. 5) and chain comparability needed for safety. Their usage across the spec (finalization and safety invariants) aligns with the whitepaper’s correctness statements and Theorem 1.
- `GetAncestors` includes the block itself, correctly supporting the “finalize ancestors first” update when finalizing a block.
- `InSameChain` encodes the intended notion of single-chain comparability for finalized blocks and is used appropriately.

## 5. Open Questions / Concerns

- Genesis sentinel coupling: The base case in `IsAncestor` relies on the modeling convention that genesis is self-parent (`b.parent = b.hash`). This is consistent with `GenesisBlock` but is a subtle coupling. If any other self-parented block were introduced (shouldn’t be possible under `IsValidBlock` and the provided actions), it would be treated as a termination point. Not a bug currently; worth documenting.

- Hash uniqueness assumption: `IsAncestor` selects a parent with `CHOOSE` from `{p \in allBlocks : p.hash = b.parent}` assuming uniqueness of `hash`. Honest and byzantine block creation both choose fresh hashes, so the model maintains uniqueness, but there is no explicit invariant stating that hashes are unique across `blocks`.

- Scope of `allBlocks` in `InSameChain`: `SingleChain(finalizedBlocks)` passes `finalizedBlocks` as the `allBlocks` universe. This is sound only if finalized sets are ancestor-closed (which `FinalizeBlock` enforces). If `InSameChain` were reused elsewhere with a non-closed set, it could give false negatives. Usage in this spec appears safe.

- Missing-parent paths: If `allBlocks` omits a parent (e.g., using a partial local view rather than the global `blocks`), `IsAncestor` will return `FALSE` via the `{}` parent set. This matches the mathematical definition (“reachable via existing parent links”) but requires care to use an ancestor-closed universe when the semantic intent requires it.

## 6. Suggestions for Improvement

- Add explicit hash uniqueness invariant (guards `CHOOSE` determinism):
  - `UniqueBlockHash == \A b1, b2 \in blocks : (b1.hash = b2.hash) => b1 = b2`.
  - Optionally add a sanity constraint at type level: `\A b \in blocks : b.hash \in BlockHashes` is already implied; uniqueness makes it explicit.

- Add finalized ancestor-closure invariant (documents and checks the intended closure property relied on by `SingleChain`):
  - `FinalizedAncestorClosure == \A v \in Validators : \A b \in finalized[v] : GetAncestors(b, blocks) \subseteq finalized[v]`.

- Clarify genesis termination in `IsAncestor`:
  - Either add a comment noting that `b.parent = b.hash` is used as the “genesis reached” sentinel, or replace with an explicit check `b.hash = GenesisHash` for readability and robustness.

- Minor naming/readability: consider defining `ComparableByAncestry(b1, b2, U) == IsAncestor(b1, b2, U) \/ IsAncestor(b2, b1, U)` and making `InSameChain == ComparableByAncestry` to emphasize the exact relation being tested.

## Cross-References in Spec

- Definitions audited:
  - `specs/tla/alpenglow/Blocks.tla:103` (IsAncestor — dependency)
  - `specs/tla/alpenglow/Blocks.tla:121` (IsDescendant)
  - `specs/tla/alpenglow/Blocks.tla:125` (GetAncestors)
  - `specs/tla/alpenglow/Blocks.tla:129` (InSameChain)

- Key usages:
  - `specs/tla/alpenglow/MainProtocol.tla:263` (FinalizeBlock updates finalized with GetAncestors)
  - `specs/tla/alpenglow/MainProtocol.tla:968` (SafetyInvariant uses IsAncestor per Theorem 1)
  - `specs/tla/alpenglow/Blocks.tla:222` (SingleChain uses InSameChain over finalized blocks)

