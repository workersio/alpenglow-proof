# Audit: IsAncestor (Blocks.tla)

## 1. Code Under Audit

```tla
IsAncestor(b1, b2, allBlocks) ==
    LET
        \* Recursively follow parent links
        RECURSIVE ReachableFrom(_)
        ReachableFrom(b) ==
            IF b = b1 THEN TRUE  \* Found the ancestor!
            ELSE IF b.parent = b.hash THEN FALSE  \* Hit genesis
            ELSE 
                \* Find the parent block and continue
                LET parentBlocks == {p \in allBlocks : p.hash = b.parent}
                IN IF parentBlocks = {} THEN FALSE
                   ELSE LET parent == CHOOSE p \in parentBlocks : TRUE
                        IN ReachableFrom(parent)
    IN b1 = b2 \/ ReachableFrom(b2)  \* A block is its own ancestor
```

Reference in repo: `specs/tla/alpenglow/Blocks.tla:105`.

## 2. Whitepaper Sections and References

- Definition 5 (ancestor and descendant): `alpenglow-whitepaper.md:363` — “An ancestor of a block b is any block that can be reached from b by the parent links… Note that b is its own ancestor and descendant.”
- Context: “Correctness” overview of finalized chains: `alpenglow-whitepaper.md:243`.
- Genesis modeling context: the spec treats genesis as a special start-of-chain block; in code it is represented as self-parented (see `GenesisBlock` in `specs/tla/alpenglow/Blocks.tla:52–60`). The whitepaper does not mandate a specific encoding for genesis; self-parent is a common modeling abstraction.

## 3. Reasoning and Conformance

- Intent alignment
  - The function checks whether there exists a path along parent pointers from `b2` back to `b1`, and allows a zero-length path via `b1 = b2`. This matches Definition 5 exactly.

- Structure and semantics
  - Self-ancestor: `b1 = b2 \/ …` models “b is its own ancestor.”
  - Recursive walk: `ReachableFrom(b)` follows `parent` by selecting `p \in allBlocks : p.hash = b.parent` and recursing.
  - Genesis stop: `b.parent = b.hash` treats genesis as a terminal and returns `FALSE` unless `b = b1` (handled by the earlier branch). This is consistent with the module’s `GenesisBlock` definition (self-parent) and with the idea that the search stops at genesis if the target wasn’t found.
  - Missing parent: if `allBlocks` lacks the parent, it returns `FALSE`. This makes ancestry relative to the provided universe `allBlocks`. In the repo, calls use `blocks` (global set of known blocks) or `finalizedBlocks`. The latter is kept closed under ancestry by construction (`FinalizeBlock` unions in `GetAncestors(block, blocks)`), so this relativization is safe in-context.

- External dependencies and assumptions
  - Block fields: relies on `hash` and `parent` fields of `Block` (defined in `specs/tla/alpenglow/Blocks.tla:42–59`).
  - Genesis convention: relies on the convention that only genesis has `parent = hash` (enforced by `IsValidBlock`: non-genesis `b.slot > 0 => b.parent # b.hash`).
  - Hash uniqueness: the `CHOOSE` over `parentBlocks` is well-defined if block hashes are unique within `allBlocks`. Uniqueness is ensured for the global `blocks` set by `HonestProposeBlock` (`hash` chosen fresh) but is not stated as a module-level invariant. In practice, all uses pass subsets of `blocks`, so this assumption holds operationally.
  - Acyclicity/termination: the recursion terminates given the system only grows blocks by extending existing ones with strictly increasing `slot` (`ValidParentChild` requires `parent.slot < child.slot`, and all block-add transitions respect it). There is no explicit cycle check inside `IsAncestor` itself.

- Conformance verdict
  - Under the repo’s standing invariants (unique hashes for `blocks`, parent slot strictly less than child, genesis self-parent), `IsAncestor` correctly models whitepaper Definition 5.

## 4. Conclusion of the Audit

- The implementation of `IsAncestor` matches the whitepaper’s Definition 5: it recognizes a block as its own ancestor and otherwise checks reachability along parent links.
- The function is correct relative to a universe `allBlocks` that contains the chain’s ancestry and has unique hashes, both of which are satisfied in this repo where callers pass `blocks` or a finalized set closed under ancestry.

## 5. Open Questions and Concerns

- Hash uniqueness not explicit in `Blocks.tla`
  - The module comments state hashes are unique, and `HonestProposeBlock` enforces it when constructing `blocks`, but there is no invariant like `UniqueBlockHashes(S) == \A x, y \in S : x.hash = y.hash => x = y`. Without it, `CHOOSE` over `parentBlocks` could be ambiguous for arbitrary `allBlocks`.

- Relativized ancestry may surprise
  - Semantics depend on `allBlocks`. If callers pass a set not closed under ancestry, `IsAncestor` may return `FALSE` even when ancestry holds in the wider system. In this repo, finalized sets are made ancestry-closed before use, but the function’s contract does not state this precondition.

- Genesis detection is by self-parent equality
  - This relies on the modeling choice that genesis is self-parented. It would be slightly clearer (and independent of `IsValidBlock`) to test `b.hash = GenesisHash` for genesis termination.

- Termination if model invariants are violated
  - The recursion has no visited-set guard. If a malicious or malformed `allBlocks` contains a cycle of parent links, evaluation could diverge. The protocol’s block-creation rules prevent this, but the function itself doesn’t defend against it.

## 6. Suggestions for Improvement

- Make hash uniqueness explicit
  - Add a reusable predicate and (optionally) assert it as an invariant where appropriate:
    ```tla
    UniqueBlockHashes(S) == \A b1, b2 \in S : b1.hash = b2.hash => b1 = b2
    ```
  - Use it in comments/contracts for `IsAncestor(b1, b2, allBlocks)` to clarify expectations on `allBlocks`.

- Clarify the universe requirement
  - Document that `allBlocks` should contain the entire ancestry of `b2` (e.g., pass `blocks` or an ancestry-closed subset). Optionally, define a variant `IsAncestorGlobal(b1, b2) == IsAncestor(b1, b2, blocks)` to avoid accidental misuse.

- Prefer explicit genesis test
  - Replace `b.parent = b.hash` with `b.hash = GenesisHash` in the genesis stop condition. This makes the intent independent of other invariants and reads more directly:
    ```tla
    ReachableFrom(b) ==
        IF b = b1 THEN TRUE
        ELSE IF b.hash = GenesisHash THEN FALSE
        ELSE …
    ```

- Strengthen structural invariant (acyclicity)
  - Consider stating a global invariant for `blocks`:
    ```tla
    AcyclicParents(S) == \A c \in S : \E p \in S : p.hash = c.parent => p.slot < c.slot
    ```
  - This, together with `UniqueBlockHashes`, guarantees termination of ancestry walks.

- Optional: defensive termination
  - If you want `IsAncestor` to be robust to malformed inputs, thread a `visited` set to prevent cycles:
    ```tla
    RECURSIVE ReachableFrom(_, _)
    ReachableFrom(b, visited) ==
        IF b \in visited THEN FALSE
        ELSE IF b = b1 THEN TRUE
        ELSE LET parents == {p \in allBlocks : p.hash = b.parent}
             IN parents # {} /\ ReachableFrom(CHOOSE p \in parents : TRUE, visited \cup {b})
    IN b1 = b2 \/ ReachableFrom(b2, {})
    ```

- Minor: remove duplication
  - The top-level `b1 = b2` is redundant because `ReachableFrom` already returns `TRUE` when `b = b1`. Keeping either is fine; removing the duplicate simplifies the definition slightly.

Overall, with the noted assumptions that are already upheld by the surrounding spec, the definition is faithful to the whitepaper and sound for its uses in invariants and helper predicates.

