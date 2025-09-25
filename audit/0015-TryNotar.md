# Audit: TryNotar

## 1. Code Under Audit

```tla
TryNotar(validator, block) ==
    LET 
        slot == block.slot
        isFirstSlot == IsFirstSlotOfWindow(slot)
        parentSlot == slot - 1
        
        canVote == 
            /\ ~HasState(validator, slot, "Voted")
            /\ \/ (isFirstSlot
                    /\ HasState(validator, slot, "ParentReady")
                    /\ validator.parentReady[slot] = block.parent)
               \/ (~isFirstSlot /\ parentSlot \in Slots /\ 
                   VotedForBlock(validator, parentSlot, block.parent))
    IN
        IF canVote THEN
            LET vote == CreateNotarVote(validator.id, slot, block.hash)
                newState1 == AddState(validator, slot, "Voted")
                newState2 == AddState(newState1, slot, "VotedNotar")
                poolWithVote == StoreVote(newState2.pool, vote)
            IN [newState2 EXCEPT 
                !.pool = poolWithVote,
                !.pendingBlocks[slot] = validator.pendingBlocks[slot] \ {block}]
        ELSE validator
```

Implementation location: `specs/tla/alpenglow/VotorCore.tla:107`.

Directly referenced helpers and constants:
- `HasState`, `AddState`, `VotedForBlock`: `specs/tla/alpenglow/VotorCore.tla:81`, `specs/tla/alpenglow/VotorCore.tla:85`, `specs/tla/alpenglow/VotorCore.tla:89`
- `IsFirstSlotOfWindow`: `specs/tla/alpenglow/Blocks.tla:192`
- `CreateNotarVote`: `specs/tla/alpenglow/Messages.tla:67`
- `StoreVote`, `GetVotesForSlot`: `specs/tla/alpenglow/VoteStorage.tla:84`, `specs/tla/alpenglow/VoteStorage.tla:142`
- Types/sets: `Slots`, `Validators`, `BlockHashes` from `specs/tla/alpenglow/Messages.tla:17`–`specs/tla/alpenglow/Messages.tla:28`

Related state and events (context):
- Votor state flags (Definition 18): `specs/tla/alpenglow/VotorCore.tla:31`–`specs/tla/alpenglow/VotorCore.tla:58`
- `HandleBlock` invokes `TryNotar`: `specs/tla/alpenglow/VotorCore.tla:209`
- `HandleBlockNotarized` calls `TryFinal`: `specs/tla/alpenglow/VotorCore.tla:239`

## 2. Whitepaper Sections and References

Primary mapping (Algorithm 2 — TRYNOTAR):
- Algorithm 2 (helper functions), lines 7–17: `alpenglow-whitepaper.md:686`–`alpenglow-whitepaper.md:706`
  - Line 8: guard “if Voted ∈ state[s] then return false”
  - Line 10–11: first slot vs not-first-slot parent readiness/notarized-parent
  - Line 12–14: broadcast NotarVote; add {Voted, VotedNotar(hash)}; clear pendingBlocks[s]
  - Line 15: “TRYFINAL(s, hash)” follow-up call after successful notar vote

Supporting definitions and context:
- Definition 18 (Votor state; ParentReady, Voted, VotedNotar, BlockNotarized, ItsOver, BadWindow, pendingBlocks): `alpenglow-whitepaper.md:607`–`alpenglow-whitepaper.md:626`
- Definition 15 (Pool events; ParentReady): `alpenglow-whitepaper.md:543`–`alpenglow-whitepaper.md:548`
- Algorithm 1 (event loop; Block, BlockNotarized, ParentReady handlers): `alpenglow-whitepaper.md:634`–`alpenglow-whitepaper.md:666`
- Window structure and first-slot semantics: `alpenglow-whitepaper.md:53`, `alpenglow-whitepaper.md:222`, `alpenglow-whitepaper.md:678`

## 3. Reasoning: Code vs. Whitepaper Claims

What the whitepaper specifies (Algorithm 2, TRYNOTAR):
- Precondition: do nothing if an initial vote (Notar or Skip) has already been cast in slot s.
- Gate to allow a notarization vote on block b in slot s:
  - If s is the first slot of the current leader window: ParentReady(hash_parent(b)) ∈ state[s]. This pins the parent hash to what ParentReady recorded.
  - Else (not first slot): the node must have already notarized the parent in slot s−1, i.e., VotedNotar(hash_parent(b)) ∈ state[s−1].
- Upon success, broadcast NotarVote(s, hash(b)); add both Voted and VotedNotar(hash(b)) to state[s]; clear pendingBlocks[s]; then immediately TRYFINAL(s, hash(b)). TRYFINAL will cast a FinalVote if BlockNotarized(hash(b)) ∈ state[s] and BadWindow ∉ state[s]. Calling TRYFINAL here handles both orderings: whether the BlockNotarized event arrived before or after this notar vote.

What the TLA+ code implements:
- No-prior-vote guard: `~HasState(validator, slot, "Voted")` aligns with “at most one initial vote per slot” (Lemma 20/Def. 12); multiplicity is also enforced when storing the vote via `StoreVote`.
- First-slot gating: `IsFirstSlotOfWindow(slot) /\
  HasState(validator, slot, "ParentReady") /\
  validator.parentReady[slot] = block.parent` faithfully encodes the ParentReady(hash_parent) requirement and additionally checks the hash equality the state remembered. This matches the paper’s intent to bind the first slot to the certified parent.
- Not-first-slot gating: `VotedForBlock(validator, slot-1, block.parent)` checks that this node cast a NotarVote for the parent at slot s−1. This is equivalent to `VotedNotar(hash_parent) ∈ state[s-1]` in the model because `TryNotar` always adds `VotedNotar` and stores the corresponding NotarVote in the Pool simultaneously.
- Effects on success: constructs `CreateNotarVote`, adds `Voted` and `VotedNotar`, and stores the vote via `StoreVote`. It also removes just this `block` from `pendingBlocks[slot]`.

Identified deviations and subtleties:
- Missing TRYFINAL call after successful notar vote.
  - Whitepaper Algorithm 2 line 15 calls `TRYFINAL(s, hash)` immediately after a notar vote. In the spec, `TryFinal` is only called when handling the BlockNotarized event (`HandleBlockNotarized`); `TryNotar` does not call `TryFinal`.
  - Consequence: If `BlockNotarized(s, hash)` was already emitted (and processed) before this node casts its notar vote, then the earlier `HandleBlockNotarized` attempt to `TryFinal` would have failed (no `VotedNotar` yet). With no subsequent callback, the node may never cast its FinalVote even though the conditions now hold (BlockNotarized ∧ VotedNotar ∧ ¬BadWindow). The whitepaper avoids this by calling TRYFINAL in both places (after BlockNotarized and after TryNotar success).
- pendingBlocks clearing granularity.
  - Algorithm 2 line 14 sets `pendingBlocks[s] ← ⊥` (clear all). The TLA code only removes the single `block` just voted on from the set: `pendingBlocks[slot] = pendingBlocks[slot] \ {block}`.
  - Functional impact: With multiple pending blocks for the same slot (e.g., equivocation), the remaining entries persist. Guards on `Voted` prevent any second notar/skip vote, so correctness is not affected; however, `CheckPendingBlocks` will repeatedly “reconsider” slot s and perform no-ops, which is a benign inefficiency at this abstraction.
- “VotedNotar(parent) in s−1” vs “vote recorded in Pool”.
  - The model uses `VotedForBlock(..)` to check the parent’s notarization rather than `HasState(_, s-1, "VotedNotar")`. In this spec, both are set together on local vote creation, so the conditions are equivalent for the node’s own history. This is a faithful implementation choice.

Other alignment checks:
- Types/guards: `parentSlot ∈ Slots` prevents underflow; `IsFirstSlotOfWindow` comes from the window structure in Blocks.tla; vote creation and storage follow Definition 11/12.
- Storage multiplicity: `StoreVote` enforces “at most one initial vote per slot” (Def. 12) — consistent with the Voted guard.

## 4. Audit Conclusion

- Core logic (guards and effects) matches Algorithm 2 lines 7–14 and the state of Definition 18:
  - No prior vote; first-slot ParentReady binding; non-first-slot requires notarizing the immediate parent; add `Voted` and `VotedNotar`; store `NotarVote`.
- Two deviations from the whitepaper were found:
  1) `TryNotar` does not call `TryFinal` after a successful notar vote. This can cause a node to miss issuing its FinalVote if the BlockNotarized event was processed earlier. The whitepaper explicitly calls TRYFINAL in both places to handle either ordering.
  2) After a successful notar vote, `pendingBlocks[s]` is not fully cleared (only the voted `block` is removed). While not a safety issue, it diverges from Algorithm 2 line 14 and can cause repeated no-op reconsideration of slot s.

Given the above, correctness with respect to safety is preserved, but progress on the slow finalization path can be delayed or (if BlockNotarized is not re-emitted) missed due to omission (1). This is a meaningful behavioral deviation from Algorithm 2.

## 5. Open Questions / Concerns

- Event re-emission assumptions: Is `BlockNotarized(s, hash)` guaranteed to be emitted (and handled) again after the node adds `VotedNotar(hash)`? In the current model, `EmitBlockNotarized` checks `~HasState(_, s, "BlockNotarized")` and thus will not repeat after the first handling. Without a `TryFinal` call inside `TryNotar`, FinalVote may never be cast in the “cert first, vote later” ordering.
- Parent slot gating on non-first slots: The condition uses only slot s−1 (per Algorithm 2). This is intentional, relying on per-window operation. If the implementation later extends to allow gaps (e.g., a skip at s−1 with a block at s), Algorithm 2 would need refinement; for now, this matches the paper.
- pendingBlocks abstraction: Whitepaper uses a single “⊥ or block” per slot, while the spec models a set. This is fine at the level of abstraction, but it explains the divergence in clearing behavior.

## 6. Suggestions for Improvement

- Call TryFinal after a successful notar vote in `TryNotar` (align with Alg. 2 line 15):
  - Sketch:
    ```tla
    IF canVote THEN
        LET vote == CreateNotarVote(validator.id, slot, block.hash)
            newState1 == AddState(validator, slot, "Voted")
            newState2 == AddState(newState1, slot, "VotedNotar")
            withVote == [newState2 EXCEPT !.pool = StoreVote(@.pool, vote)]
            cleared == [withVote EXCEPT !.pendingBlocks[slot] = {}]
        IN TryFinal(cleared, slot, block.hash)
    ELSE validator
    ```
  - This preserves the current semantics and ensures FinalVote is emitted whenever both prerequisites already hold.
- Clear all pending blocks for the slot upon any initial vote in that slot:
  - Replace `pendingBlocks[slot] = pendingBlocks[slot] \ {block}` with `pendingBlocks[slot] = {}` as in Algorithm 2 line 14. This avoids repeated no-op checks and matches the whitepaper exactly.
- Optional: switch the non-first-slot guard to the state flag, for readability parity with the paper:
  - `HasState(validator, slot-1, "VotedNotar") /\
     VotedForBlock(validator, slot-1, block.parent)`
  - This makes the correspondence to “VotedNotar(parent) ∈ state[s-1]” explicit without changing behavior.

File references for cross-checking:
- `specs/tla/alpenglow/VotorCore.tla:107` (TryNotar)
- `specs/tla/alpenglow/VotorCore.tla:141` (TryFinal)
- `specs/tla/alpenglow/VoteStorage.tla:84`, `specs/tla/alpenglow/VoteStorage.tla:142` (StoreVote, GetVotesForSlot)
- `specs/tla/alpenglow/Blocks.tla:192` (IsFirstSlotOfWindow)
- `alpenglow-whitepaper.md:686`, `alpenglow-whitepaper.md:698`, `alpenglow-whitepaper.md:705` (Algorithm 2 TRYNOTAR and TRYFINAL lines)

---

Overall, TryNotar is very close to the whitepaper’s Algorithm 2. Adding the immediate TryFinal call and clearing all pending blocks for the slot would make it match the text precisely and avoid edge-ordering gaps in finalization voting.

