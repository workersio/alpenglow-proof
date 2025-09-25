# Audit: CheckPendingBlocks

- File: `specs/tla/alpenglow/VotorCore.tla:189`
- Context: VotorCore — helper used by the event loop to retry pending block notarization attempts.

## 1. Code Under Audit

```tla
CheckPendingBlocks(validator) ==
    LET RECURSIVE CheckSlots(_,_)
        CheckSlots(val, slots) ==
            IF slots = {} THEN val
            ELSE
                LET s == CHOOSE x \in slots : TRUE
                    blocks == val.pendingBlocks[s]
                IN IF blocks = {} THEN CheckSlots(val, slots \ {s})
                   ELSE 
                       LET block == CHOOSE b \in blocks : TRUE
                           newVal == TryNotar(val, block)
                       IN CheckSlots(newVal, slots \ {s})
    IN CheckSlots(validator, {s \in Slots : validator.pendingBlocks[s] # {}})
```

## 2. Whitepaper Sections & References

- Algorithm 1 (Votor event loop): `alpenglow-whitepaper.md:634`
  - Block handler calling CHECKPENDINGBLOCKS on successful TRYNOTAR (lines 1–5).
  - ParentReady handler calling CHECKPENDINGBLOCKS (lines 12–15).
- Definition 15 (Pool events — ParentReady, BlockNotarized): `alpenglow-whitepaper.md:543`–`alpenglow-whitepaper.md:546`.
- Definition 17 (timeout schedule; follows ParentReady handler): `alpenglow-whitepaper.md:607`, formula at `alpenglow-whitepaper.md:609`.
- Definition 18 (Votor state; includes pendingBlocks): `alpenglow-whitepaper.md:615`–`alpenglow-whitepaper.md:632`.
- Algorithm 2 (TRYNOTAR): start at `alpenglow-whitepaper.md:676` (lines 7–17 show semantics; line 14 clears pending block).

Relevant spec cross-references:
- `Slots` universe and typing: `specs/tla/alpenglow/Messages.tla:18`–`:26`.
- `pendingBlocks` in validator state: `specs/tla/alpenglow/VotorCore.tla:57`–`:73`.
- `TryNotar`: `specs/tla/alpenglow/VotorCore.tla:107`–`:133`.
- Only first Block(...) event per slot is delivered to Votor (avoids multiple pending blocks): `specs/tla/alpenglow/MainProtocol.tla:113`–`:137` (uses `BlockSeen`).

## 3. Reasoning vs Whitepaper

Intended behavior per the whitepaper:
- CHECKPENDINGBLOCKS is invoked after (a) ParentReady(s, …) and (b) successful TRYNOTAR on a newly delivered block. Its purpose is to revisit pending block(s) whose preconditions may now be satisfied, and attempt notarization via TRYNOTAR.
- pendingBlocks is conceptually “one pending block per slot, initially ⊥” (Algorithm 1 line 5; Definition 18). TRYNOTAR success clears the pending entry (Algorithm 2 line 14).

What the TLA+ code does:
- Gathers the set of slots that currently have non-empty `pendingBlocks` in the argument `validator` and tail-recursively iterates through that set.
- For each such slot `s`, if `pendingBlocks[s]` is non-empty, it CHOOSEs one `block` from that set and calls `TryNotar(val, block)`, then proceeds to the next slot (removing `s` from `slots`).

Correctness in context:
- Single pending per slot: Although `pendingBlocks` is modeled as a set (`[Slots -> SUBSET Block]`), the system-level action `ReceiveBlock` ensures the Votor loop only processes the first complete block per slot (`BlockSeen` guard in `specs/tla/alpenglow/MainProtocol.tla:126`), so per-validator `pendingBlocks[s]` is effectively of cardinality 0 or 1. This matches the whitepaper’s “one pending block per slot” abstraction and makes the CHOOSE over `blocks` harmless in practice.
- Invocation points: CHECKPENDINGBLOCKS is called from (i) `HandleParentReady` before `SETTIMEOUTS` (matching Algorithm 1 line 14) and (ii) `HandleBlock` when `TryNotar` succeeds (matching Algorithm 1 line 3). These entry points align with the paper.
- TRYNOTAR semantics: On success, `TryNotar` adds `Voted` and `VotedNotar` to the slot, stores the vote, and removes the block from `pendingBlocks[slot]` (mirrors Algorithm 2 lines 12–14). This ensures idempotence and prevents a second notar vote for the same slot.

Potential subtlety (ordering/fixpoint):
- Dependencies across slots: For non-first slots, TRYNOTAR requires a notar vote in the previous slot (`VotedNotar(hash_parent) ∈ state[s-1]`). If CHECKPENDINGBLOCKS processes a later slot first, TRYNOTAR may fail due to the missing parent vote. The current implementation removes that slot from `slots` and does not revisit it within the same call, even if notarizing its parent later in the same call makes it eligible. The whitepaper intent (“re-evaluate pending”) suggests computing to a local fixpoint. The current code achieves eventual progress when CHECKPENDINGBLOCKS is re-invoked by an external event (e.g., a separate successful TRYNOTAR or another ParentReady), but it may miss immediate chaining opportunities in a single call.

Why this is acceptable but improvable:
- Given only one pending per slot and the subsequent invocation on successful TRYNOTAR in `HandleBlock`, most practical workflows will promptly retry later slots. However, in the specific path triggered only by `HandleParentReady` (no new Block or certificate arrivals), the lack of intra-call fixpoint means some later-slot pending blocks might wait until another triggering event (or timeout), which is slightly weaker than the “re-evaluate” spirit.

## 4. Conclusion

- Alignment: The function aligns with the whitepaper’s purpose of retrying pending blocks after preconditions may have changed, and its call sites match Algorithm 1. The model’s single-delivery policy (`BlockSeen`) keeps `pendingBlocks[s]` effectively singular, matching the whitepaper abstraction.
- Soundness: No safety violation is introduced by this procedure. TRYNOTAR preserves the invariant of at most one initial vote per slot and clears pending on success per Algorithm 2.
- Liveness nuance: The implementation does not compute a local fixpoint within a single CHECKPENDINGBLOCKS call. This can delay notarization for later slots whose eligibility depends on progress in earlier slots during the same pass. While subsequent events typically trigger another pass, tightening this would better reflect the whitepaper’s implied behavior.

## 5. Open Questions / Concerns

- Fixpoint semantics: Should CHECKPENDINGBLOCKS keep iterating as long as some TRYNOTAR succeeds for any pending block, to better match the “re-evaluate pending” intent? This would remove ordering sensitivity and avoid relying on external triggers for immediate chaining.
- Cardinality of pendingBlocks: The whitepaper models one pending block per slot (⊥ vs a block). The spec uses a set, though higher layers ensure single delivery. Do we want to enforce this at the type level (`Block \cup {NoBlock}`) to better match the paper and avoid accidental multi-pending in future changes?
- Comment reference accuracy: The code comment cites “Algorithm 1, lines 28–30,” but the current whitepaper’s Algorithm 1 is 25 lines. This appears to be a stale reference range; the intended references are lines 3 and 14 per the current numbering.

## 6. Suggestions for Improvement

- Compute a fixpoint within CHECKPENDINGBLOCKS:
  - Option A (preferred): Iterate while progress is possible.
    - Sketch:
      ```tla
      CheckPendingBlocks(validator) ==
          LET RECURSIVE Step(_)
              Step(val) ==
                  LET candidates == {<<s, b>> \in (Slots \times Block) :
                                      s \in Slots /\ b \in val.pendingBlocks[s] /\ TryNotar(val, b) # val}
                  IN IF candidates = {} THEN val
                     ELSE LET p == CHOOSE x \in candidates : TRUE
                              s == p[1]
                              b == p[2]
                              v2 == TryNotar(val, b)
                          IN Step(v2)
          IN Step(validator)
      ```
  - Option B: Keep the current structure but after a successful TRYNOTAR, re-run CHECKPENDINGBLOCKS on `newVal` (tail-recursive fixpoint) before removing `s` from `slots`.
- Prefer deterministic iteration from earlier to later slots to encourage parent-first progress:
  - Replace `CHOOSE x \in slots : TRUE` with `CHOOSE x \in slots : x = Min(slots)` and require `FiniteSets`.
- Tighten the type of `pendingBlocks` to reflect whitepaper:
  - Change to `[Slots -> (Block \cup {NoBlock})]` and update handlers accordingly (set to `NoBlock` instead of `{}`), or retain sets but add an invariant `\A s : Cardinality(pendingBlocks[s]) <= 1`.
- Update the comment reference above `CheckPendingBlocks` to correctly cite Algorithm 1 (lines 3, 14) in the current whitepaper.

---

Summary: The current implementation is functionally consistent with the whitepaper under the system’s single-delivery constraint, but can be strengthened by computing a fixpoint and clarifying the pendingBlocks cardinality and documentation references.

