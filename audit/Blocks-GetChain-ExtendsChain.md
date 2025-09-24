# Audit: GetChain and ExtendsChain (Blocks.tla)

- Spec code: `specs/tla/alpenglow/Blocks.tla:194`, `specs/tla/alpenglow/Blocks.tla:201`
- Dependencies referenced:
  - `IsAncestor(b1, b2, allBlocks)`: `specs/tla/alpenglow/Blocks.tla:105`
  - `GetAncestors(b, allBlocks)`: `specs/tla/alpenglow/Blocks.tla:125`
  - `ValidParentChild(parent, child)`: `specs/tla/alpenglow/Blocks.tla:86`

## 1. Code Under Audit

```tla
\* Get the complete chain from genesis to a block
GetChain(b, allBlocks) ==
    LET ancestors == GetAncestors(b, allBlocks)
    IN {a \in ancestors : 
        \* Include only blocks that are ancestors of all later blocks
        \A a2 \in ancestors : a2.slot <= a.slot => IsAncestor(a2, a, allBlocks)}

\* Check if a new block properly extends an existing chain
ExtendsChain(newBlock, existingChain) ==
    \E parent \in existingChain :
        /\ ValidParentChild(parent, newBlock)
        /\ \A other \in existingChain : other.slot < newBlock.slot
```

## 2. Whitepaper Sections and References

- Definition 5 (ancestor/descendant): `alpenglow-whitepaper.md:363`.
- Correctness (finalized blocks form a single chain; child has higher slot than parent): `alpenglow-whitepaper.md:243`–`:247`.
- Block creation and chain extension (leader windows, immediate parent linkage across slots):
  - Section 2.7: `alpenglow-whitepaper.md:721`–`:733`.
  - Algorithm 3: `alpenglow-whitepaper.md:759`–`:776` (esp. steps 2 and 15: “generate a block with parent … in slot s/s′”).

## 3. Reasoning vs. Whitepaper Claims

- GetChain
  - Intent: “complete chain from genesis to b.” Implementation computes `ancestors == GetAncestors(b, allBlocks)` then filters to `a` such that every `a2` in `ancestors` with `a2.slot <= a.slot` is an ancestor of `a`.
  - Given Definition 5 and the model’s block structure (single parent per block), the set of ancestors of any block b is a single path (no branching) from b to genesis. For any two ancestors `a2` and `a` with `a2.slot <= a.slot` on that path, `IsAncestor(a2, a, allBlocks)` holds by construction. Therefore the predicate inside the set-comprehension is always true for every `a ∈ ancestors`, assuming `allBlocks` contains the necessary ancestors.
  - Conclusion: `GetChain(b, allBlocks)` is equivalent to `GetAncestors(b, allBlocks)` in this model. The filter is redundant but not incorrect. This matches the whitepaper’s Definition 5 and the “single-parent lineage” abstraction.
  - Caveat: As with `GetAncestors`, results are relative to the chosen universe `allBlocks`. If `allBlocks` is not closed under ancestry, `IsAncestor` can return `FALSE` for genuine ancestors and the chain can appear truncated. In the protocol, calls that matter (e.g., finalization) make `finalized` ancestry-closed (`specs/tla/alpenglow/MainProtocol.tla:263`), which preserves correctness. This implicit precondition should be documented for callers of `GetChain`.

- ExtendsChain
  - Intent: “properly extends an existing chain.” The current predicate requires:
    - There exists some `parent ∈ existingChain` with `ValidParentChild(parent, newBlock)` (i.e., correct parent hash and `parent.slot < newBlock.slot`).
    - All `other ∈ existingChain` have `other.slot < newBlock.slot` (i.e., `newBlock`’s slot is strictly greater than every element in `existingChain`).
  - Issues vs. whitepaper:
    - Parent must be the tip: Algorithm 3 and Section 2.7 imply that each new block is generated with its immediate predecessor as parent (for the first slot of a window, parent in slot `s-1`; within the window, “generate a block with parent b in slot s′” for s′ = s+1, s+2, …; `alpenglow-whitepaper.md:731`, `:759`–`:776`). The current `∃ parent ∈ existingChain` allows choosing any ancestor, not necessarily the chain tip. It would accept, for example, a `newBlock` that references genesis as parent even when `existingChain` contains many later blocks, which does not model “properly extends this chain.”
    - Slot-only bound: `∀ other ∈ existingChain : other.slot < newBlock.slot` enforces that `newBlock.slot` is greater than all slots in the chain, but it does not enforce that the chosen `parent` is the unique maximum-slot element of `existingChain`. Thus, side-extension off an earlier ancestor would pass if `ValidParentChild` holds (it often would), contradicting the paper’s discipline of building on the tip (no forking in the extension predicate).
  - Model vs. paper on slot gaps: `ValidParentChild` only requires `parent.slot < child.slot` (strictly increasing), not “= parent.slot + 1”. The paper’s Algorithm 3 always advances slot-by-slot, so the stronger equality could be used if we want the chain operation to reflect that algorithmic discipline. Keeping the `<` abstraction is a permissible over-approximation for safety arguments, but then the extension predicate must still ensure the parent is the tip.

## 4. Conclusion of the Audit

- GetChain: Correct but redundant. It faithfully returns the path of ancestors of `b` given `allBlocks`, aligning with Definition 5. The inner predicate can be simplified away without changing semantics in this model. Document the ancestry-closure precondition on `allBlocks` to avoid misuse.
- ExtendsChain: Semantically too weak. It permits extensions that attach to any ancestor of the chain instead of the chain’s tip, which diverges from the whitepaper’s block creation discipline (Algorithm 3) and from the intended notion of “properly extends an existing chain.” Strengthen it to require using the tip as the parent, and (optionally) to enforce step-by-step slot increments if desired to mirror Algorithm 3.

## 5. Open Questions / Concerns

- Do we intentionally allow “extension” from non-tip ancestors in any adversarial modeling context? If not, `ExtendsChain` should be tightened.
- Should the model enforce `child.slot = parent.slot + 1` for chain operations (mirroring Algorithm 3), or is the current `parent.slot < child.slot` abstraction preferred for over-approximate safety proofs?
- Should we expose and require an “ancestry-closed” precondition on sets passed as `allBlocks` to `GetChain`/`GetAncestors` to avoid silent truncation when the universe is incomplete?

## 6. Suggestions for Improvement

- Simplify GetChain (and/or document closure):

```tla
GetChain(b, allBlocks) == GetAncestors(b, allBlocks)
\* Precondition (document): allBlocks is closed under ancestry of b.
```

- Strengthen ExtendsChain to require the tip as parent. Two variants below depending on whether we want to enforce step-by-step slots.

Variant A (no slot-equality requirement, but parent must be the tip):
```tla
Tip(chain) == CHOOSE x \in chain : \A y \in chain : x.slot >= y.slot

ExtendsChain(newBlock, existingChain) ==
    LET tip == Tip(existingChain) IN
        /\ ValidParentChild(tip, newBlock)
        /\ newBlock.slot > tip.slot
```

Variant B (align more strictly with Algorithm 3’s step-by-step slots):
```tla
Tip(chain) == CHOOSE x \in chain : \A y \in chain : x.slot >= y.slot

ExtendsChainStrict(newBlock, existingChain) ==
    LET tip == Tip(existingChain) IN
        /\ ValidParentChild(tip, newBlock)
        /\ newBlock.slot = tip.slot + 1
```

- Alternative formulation emphasizing ancestry of the entire chain (makes “extension” unambiguous even without selecting the tip explicitly):
```tla
ExtendsChainAllAncestors(newBlock, existingChain, allBlocks) ==
    /\ (\A b \in existingChain : IsAncestor(b, newBlock, allBlocks))
    /\ (\E parent \in existingChain : ValidParentChild(parent, newBlock))
```
This implies the chosen `parent` is the tip because only the tip can be the direct parent if all chain elements are ancestors of `newBlock`.

- Add a helper/lemma to capture the intended “chain” shape explicitly and aid proofs:
```tla
IsChain(chain, allBlocks) ==
    \A a, b \in chain : (a.slot <= b.slot) => IsAncestor(a, b, allBlocks)
```
Then assert `IsChain(GetChain(b, allBlocks), allBlocks)` where used; this is already true by construction.

- Documentation tip: Mention in `specs/tla/alpenglow/Blocks.tla:193` that “chain” is a set, not a sequence, and ordering-sensitive operations (like tip selection) must rely on `slot` or ancestry.

## File References

- Code audited: `specs/tla/alpenglow/Blocks.tla:194`, `specs/tla/alpenglow/Blocks.tla:201`.
- Dependencies: `specs/tla/alpenglow/Blocks.tla:86`, `specs/tla/alpenglow/Blocks.tla:105`, `specs/tla/alpenglow/Blocks.tla:125`.
- Whitepaper: `alpenglow-whitepaper.md:243`, `alpenglow-whitepaper.md:363`, `alpenglow-whitepaper.md:721`, `alpenglow-whitepaper.md:759`.

