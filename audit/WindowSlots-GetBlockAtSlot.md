# Audit: WindowSlots and GetBlockAtSlot (Blocks.tla)

1. Code that you are auditing

```
WindowSlots(slot) ==
    LET first == FirstSlotOfWindow(slot)
    IN {s \in Slots : 
        /\ s >= first 
        /\ s < first + WindowSize}

\* Returns the set of slot numbers owned by the leader of `slot`.

\* ============================================================================
\* CHAIN OPERATIONS
\* ============================================================================

\* Get the block at a specific slot in a chain
GetBlockAtSlot(slot, chain) ==
    LET blocksAtSlot == {b \in chain : b.slot = slot}
    IN IF blocksAtSlot = {} THEN GenesisBlock
       ELSE CHOOSE b \in blocksAtSlot : TRUE
```

2. The whitepaper section and references that the code represents

- Leader windows overview: `alpenglow-whitepaper.md:53`
- VRF leader schedule and public schedule per epoch: `alpenglow-whitepaper.md:222`
- WINDOWSLOTS helper (Algorithm 2, helpers): `alpenglow-whitepaper.md:676`, `alpenglow-whitepaper.md:678`, `alpenglow-whitepaper.md:682`
- Timeouts scheduled for all slots in WINDOWSLOTS(s) (Def. 17): `alpenglow-whitepaper.md:607`, with first-slot-only note: `alpenglow-whitepaper.md:613`
- Block creation across a leader window (Section 2.7): `alpenglow-whitepaper.md:721`
- Block and ancestry definitions underpinning chain lookups: Definition 3 (block) `alpenglow-whitepaper.md:351`; Definition 5 (ancestor/descendant) `alpenglow-whitepaper.md:363`; correctness single-chain statement `alpenglow-whitepaper.md:243`

Related TLA definitions this code depends on:

- `FirstSlotOfWindow`: `specs/tla/alpenglow/Blocks.tla:156`
- `WindowSize`: `specs/tla/alpenglow/Blocks.tla:22`
- `Slots`: `specs/tla/alpenglow/Messages.tla:18`
- `GenesisBlock`: `specs/tla/alpenglow/Blocks.tla:53`

3. Reasoning: what the code intends vs. whitepaper claims

- WindowSlots(slot)
  - Intent: Return all slots in the same leader window as `slot`.
  - Implementation: Computes `first = FirstSlotOfWindow(slot)` and returns `{ s ∈ Slots : s ≥ first ∧ s < first + WindowSize }`.
  - Whitepaper mapping: The helper WINDOWSLOTS(s) is used repeatedly (Algorithm 2 and Definition 17) to denote “all slot numbers of the leader window containing s”. The TLA set comprehension exactly captures a contiguous, size-`WindowSize` slice of `Slots` beginning at the window’s first slot, which matches the whitepaper’s intent that leaders “are in charge for a fixed amount of consecutive slots” (leader windows).
  - Edge case (slot 0): In this spec, `FirstSlotOfWindow(0) = 0` (see `specs/tla/alpenglow/Blocks.tla:156-158`). Therefore `WindowSlots(0)` includes slot 0 and up to `WindowSize - 1`. The whitepaper treats leader windows as production slots (starting at the first slot of a window), while genesis is a special block outside normal production. The main protocol typically intersects with `1..MaxSlot` when using `WindowSlots(s)` (e.g., `specs/tla/alpenglow/MainProtocol.tla:942`, `specs/tla/alpenglow/MainProtocol.tla:947`), effectively excluding slot 0 in those contexts. This is consistent with the whitepaper’s usage of WINDOWSLOTS only for production windows.

- GetBlockAtSlot(slot, chain)
  - Intent: Given a set `chain ⊆ Block`, return the block in `chain` that occupies `slot`; if none exists, return `GenesisBlock`.
  - Whitepaper mapping: The paper does not define a direct helper to “get the block at slot s.” It asserts that finalized blocks form a single chain of parent–child links and that each slot is either a skip or contains a block by the window leader. Within this TLA module, `GetBlockAtSlot` is a convenience for querying a chain’s element at a slot, not a primitive from the whitepaper.
  - Semantics: If multiple blocks exist in the same `slot` within `chain` (e.g., non-finalized conflicts), the function nondeterministically chooses one (`CHOOSE`). This matches the abstract model where conflicts can exist until resolved by voting; safety constraints prevent two different finalized blocks for the same slot.
  - Edge case (no block at slot): Returning `GenesisBlock` when no block exists at the given `slot` conflates “no block for this slot” with “genesis block.” The whitepaper treats empty/skip slots distinctly from genesis. In practice, callers should treat the absence of `b` with `b.slot = slot` differently from the genesis block (which has `slot = 0`). The current definition may be acceptable as a total function stub if never called for `slot > 0` in meaningful proofs; however, it is semantically surprising and could mask modeling errors if used naively.

4. Conclusion of the audit

- WindowSlots(slot): Correct and faithful to the whitepaper’s WINDOWSLOTS(s) abstraction for leader windows. The edge case including slot 0 is controlled by call sites that intersect with production slots. No issues with the abstraction itself.
- GetBlockAtSlot(slot, chain): Functionally well-typed and safe as a helper, but its fallback to `GenesisBlock` is not aligned with the whitepaper’s treatment of skip/empty slots vs. genesis. Since it is currently unused in the repo, there is no immediate safety risk; however, its semantics could be misleading if introduced in proofs that reason about skips or parent selection.

5. Open questions or concerns

- Should `WindowSlots(0)` be well-defined as including `0..WindowSize-1`? The paper never treats genesis as part of a leader window. Current usages tend to filter with `1..MaxSlot`, but codifying this expectation in the definition or via a typing guard may avoid misuse.
- The nondeterministic tie-breaker in `GetBlockAtSlot` is fine abstractly, but what invariant is expected of `chain`? If `chain` is intended to be a linear chain (no conflicting slots), the function could assert uniqueness to detect modeling errors early.
- Returning `GenesisBlock` for “no block at slot” is potentially confusing. Do we want an explicit way to represent “no block exists for this slot” at the block level (distinct from vote-level `NoBlock`)?

6. Suggestions for improvement

- Clarify production domain for window helpers
  - Option A: Guard `WindowSlots` to exclude slot 0 explicitly, e.g., by intersecting with `1..MaxSlot` at call sites (already done in critical places), or refine the definition to `s ≥ 1` if that’s invariant in the model.
  - Option B: Add a brief comment near `FirstSlotOfWindow` and/or `WindowSlots` noting genesis (slot 0) is not a production window and that consumers should avoid invoking with `slot = 0`.

- Make “no block at slot” explicit for chain queries
  - Replace `GetBlockAtSlot` with a predicate and a partial selection:
    - `HasBlockAtSlot(slot, chain) == \E b \in chain : b.slot = slot`
    - `BlockAtSlot(slot, chain) == CHOOSE b \in chain : b.slot = slot` with an `ASSUME HasBlockAtSlot(slot, chain)` or used only under such guards.
  - Alternatively, return a tagged union/option pattern using a record wrapper:
    - `GetBlockAtSlot(slot, chain) == IF ... THEN [some |-> TRUE, val |-> CHOOSE ...] ELSE [some |-> FALSE, val |-> CHOOSE b \in {GenesisBlock} : TRUE]` and document that `some=FALSE` indicates absence (keeping totality while avoiding semantic conflation with genesis).

- Optional assertion about chain linearity (if intended)
  - If callers expect at most one block per slot in `chain`, add an invariant or a helper assertion:
    - `UniqueBlocksPerSlot(chain) == \A b1, b2 \in chain : b1.slot = b2.slot => b1.hash = b2.hash` (similar to `UniqueBlocksPerSlot` already present for finalized blocks in `specs/tla/alpenglow/Blocks.tla:216`). If `GetBlockAtSlot` will be used over such chains, its nondeterminism becomes benign.

Overall, WindowSlots directly matches the whitepaper abstraction of leader windows. GetBlockAtSlot is a reasonable convenience but should avoid using GenesisBlock as a sentinel for “no block in this slot” to prevent subtle proof misinterpretations.

