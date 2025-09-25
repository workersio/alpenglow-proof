# Audit: HandleBlock (VotorCore)

## 1. Code Under Audit

Path: `specs/tla/alpenglow/VotorCore.tla:213`

```tla
HandleBlock(validator, block) ==
    LET slot == block.slot
        tryResult == TryNotar(validator, block)
    IN
        IF tryResult # validator THEN
            CheckPendingBlocks(tryResult)  \* Successfully voted; re-evaluate pending
        ELSE IF ~HasState(validator, slot, "Voted") THEN
            \* Store as pending to retry later
            [validator EXCEPT !.pendingBlocks[slot] = 
                validator.pendingBlocks[slot] \union {block}]
        ELSE validator
```

## 2. Whitepaper Sections and References

- Algorithm 1 — Votor, event loop (Block handler): `alpenglow-whitepaper.md:24` lines 1–5.
  - 1: upon Block(s, …)
  - 2: if TRYNOTAR(Block(...)) then
  - 3:   CHECKPENDINGBLOCKS()
  - 4: else if Voted ∉ state[s] then
  - 5:   pendingBlocks[s] ← Block(...)
- Definition 18 — Votor state objects (Voted, ParentReady, etc.): `alpenglow-whitepaper.md:23–24`.
- Context on Block event emission (Blokstor → Algorithm 1): `alpenglow-whitepaper.md:468`.

## 3. Reasoning: Mapping Code → Whitepaper

- Immediate notar attempt (Alg.1 L2): The operator first computes `tryResult == TryNotar(validator, block)`. Returning an updated validator encodes “TRYNOTAR succeeded,” while returning the unchanged record encodes failure (boolean-free idiom).

- Re-check pending after success (Alg.1 L3): On `tryResult # validator`, the code calls `CheckPendingBlocks(tryResult)`, matching CHECKPENDINGBLOCKS(). This is consistent with Alg.2’s CHECKPENDINGBLOCKS, which tries to (re)notarize any previously deferred block that may now satisfy preconditions.

- Defer when not yet voted (Alg.1 L4–L5): If notarization did not succeed and the validator has not yet cast its initial vote in this slot (`~HasState(validator, slot, "Voted")`), the block is stored for retry. The model uses a set: `pendingBlocks[slot] ∪ {block}`. The paper’s pseudocode stores a single block; using a set is a conservative generalization that preserves safety and supports potential multi-block availability while Algorithm 1 only delivers the first block in this spec (see MainProtocol’s `ReceiveBlock`).

- No-op otherwise: If the validator already voted in the slot, the handler ignores subsequent block deliveries, aligned with Alg.1 which only buffers when `Voted ∉ state[s]`.

Relevant internal references and their roles:
- `TryNotar` (same file, Alg.2 L7–17 mapping): checks first-slot/parent readiness or prior-slot vote on parent, and records a notar vote when legal.
- `CheckPendingBlocks` (same file, Alg.2 L28–30 mapping): iterates non-empty pending sets and re-attempts `TryNotar`.
- `HasState` (same file; Definition 18 mapping): presence of `Voted` governs whether buffering is allowed.
- `pendingBlocks` field (same file; initialized in `InitValidatorState`): abstracts the “pending” storage referenced in Alg.1 L5.

External module context (indirect via `TryNotar`): `Messages`, `VoteStorage`, and `Certificates` define vote messages, storage semantics, and certificate notions (Section 2.4), but are not invoked directly by `HandleBlock` beyond `TryNotar`/`CheckPendingBlocks`.

## 4. Conclusion

The `HandleBlock` operator faithfully implements Algorithm 1 (lines 1–5): it attempts notarization immediately, re-checks pending on success, and otherwise buffers the block only if the validator has not yet cast its initial vote in the slot. Using a set for `pendingBlocks[slot]` is a benign generalization that does not contradict the whitepaper and remains compatible with CHECKPENDINGBLOCKS semantics.

## 5. Open Questions / Concerns

- Finalization hook alignment (Alg.2 L15): The whitepaper’s TRYNOTAR calls TRYFINAL(s, hash) immediately after a successful notar vote. In the current spec, `TryNotar` does not invoke `TryFinal`, and `HandleBlock` does not either. Finalization is only attempted in `HandleBlockNotarized` when the Pool emits BlockNotarized. This creates a potential missed-finalization scenario: if BlockNotarized was processed earlier (so `BlockNotarized ∈ state[s]`) and later a notar vote succeeds via `HandleBlock`, the spec never re-invokes `TryFinal`, deviating from the paper’s opportunistic call. This is not a safety bug but could be a liveness/spec-precision issue relative to the whitepaper.

- Pending multiplicity vs delivery model: The spec allows multiple pending blocks per slot (`SUBSET Block`), but `ReceiveBlock` only delivers the first block per slot to the event loop (via `BlockSeen`). This is consistent but may be surprising to readers cross-referencing the paper’s “first complete block” language alongside the plural “pendingBlocks are blocks”. Clarifying commentary would help.

- Single-attempt per slot in CHECKPENDINGBLOCKS: The implementation tries one chosen pending block per slot per invocation (matching the paper’s single pending entry). If multiple are present, repeated triggers are required to process all. This is fine but worth an explicit note.

## 6. Suggestions for Improvement

- Add TRYFINAL after notar success: Either (a) call `TryFinal` from `TryNotar` after recording the vote, or (b) call `TryFinal` in `HandleBlock` when `tryResult # validator`. This would align with Algorithm 2 (line 15) and avoid dependence on receiving another `BlockNotarized` event after the local notar vote.

- Comment on pending set generalization: In `VotorCore.tla`, document that `pendingBlocks[slot]` is modeled as a set for generality, while `MainProtocol`’s `ReceiveBlock` delivers only the first block per slot to Algorithm 1 in this model. This reduces confusion for readers mapping to the whitepaper pseudocode.

- Optional guard for deduplication: The union already deduplicates identical blocks. Consider stating this explicitly in a comment to make idempotence obvious.

Overall, the audited operator matches the whitepaper’s intent and control flow for the Block event. The noted finalization hook is the only meaningful divergence from the pseudocode contract and can be fixed locally without impacting other invariants.

