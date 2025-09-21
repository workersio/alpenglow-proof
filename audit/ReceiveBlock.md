**Code Under Audit**

- `specs/tla/alpenglow/MainProtocol.tla:108`

```
ReceiveBlock(v, block) ==
    /\ v \in CorrectNodes
    /\ block \in blocks
    /\ block \in blockAvailability[v]
    /\ validators' = [validators EXCEPT ![v] = HandleBlock(validators[v], block)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, time, finalized, blockAvailability>>
```

**Whitepaper References**

- Blokstor emits the Block event: `alpenglow-whitepaper.md:468`.
- Algorithm 1 (event loop) — lines handling Block and subsequent calls:
  - Heading: `alpenglow-whitepaper.md:634`
  - Lines 1–3 (Block, TRYNOTAR, CHECKPENDINGBLOCKS): `alpenglow-whitepaper.md:637`, `alpenglow-whitepaper.md:638`, `alpenglow-whitepaper.md:639`.
- Votor state objects (Definition 18): `alpenglow-whitepaper.md:615`.
- TRYNOTAR helper (Algorithm 2): `alpenglow-whitepaper.md:686`.

Related spec context used by this action:

- Correct nodes set: `specs/tla/alpenglow/MainProtocol.tla:57`.
- Validator state machine (HandleBlock): `specs/tla/alpenglow/VotorCore.tla:211`.
- TRYNOTAR logic: `specs/tla/alpenglow/VotorCore.tla:105`.
- CHECKPENDINGBLOCKS: `specs/tla/alpenglow/VotorCore.tla:187`.
- Fairness on ReceiveBlock scheduling: `specs/tla/alpenglow/MainProtocol.tla:434`.

**Reasoning**

- Event gating matches Blokstor semantics.
  - The preconditions `/\ block \in blockAvailability[v]` and `/\ block \in blocks` ensure the node has locally “received” a well-formed, existing block before invoking Votor. This models “Blokstor emits the event Block(...) when it receives the first complete block b” (whitepaper Blockstor section).
  - The action is limited to honest validators via `/\ v \in CorrectNodes`, consistent with the spec’s separation of adversarial behavior into `ByzantineAction`.

- Handler aligns with Algorithm 1 lines 1–5.
  - The state update delegates to `HandleBlock(validators[v], block)` which implements Algorithm 1 lines 1–5: attempt TRYNOTAR, otherwise remember the block as pending if no initial vote has been cast yet; on success re-check pending blocks. See `VotorCore.HandleBlock` and its calls to `TryNotar` and `CheckPendingBlocks`.
  - Broadcasting is intentionally decoupled: Algorithm 1 uses “broadcast” verbs; in the spec, votes are stored locally and later broadcast via `BroadcastLocalVote`/`DeliverVote`. Keeping `messages` unchanged here faithfully models local handling vs. network dissemination in an asynchronous setting.

- Consistency with the rest of the protocol.
  - Blocks become available to nodes only via Rotor or Repair actions, which are the only actions that mutate `blockAvailability`. `ReceiveBlock` leaves `blockAvailability` unchanged, as the event is defined to fire after storage, not to perform storage.
  - `HandleBlock`’s `TryNotar` matches Algorithm 2 guard: no prior initial vote in the slot, and either ParentReady at the first slot of the window or a notar vote for the parent at the previous slot. On success it sets `Voted` and `VotedNotar` and removes the block from pending; otherwise, if `Voted` is not set, it adds the block to pending. This mirrors the whitepaper narrative.

**Conclusion**

- The `ReceiveBlock` action correctly captures the whitepaper’s “upon Block(...) do” entry point (Algorithm 1) by:
  - Firing only for locally stored blocks (Blokstor semantics),
  - Updating only the local validator state via the specified Votor handler,
  - Not mutating network or global structures beyond the local state, which matches the algorithm’s intent.
- No safety or liveness violations are introduced by this action as written; it composes with fairness (`WF_vars(∃ b : ReceiveBlock(v,b))`) to guarantee eventual processing once a block is available.

**Open Questions / Concerns**

- First-block vs. multiple-blocks semantics.
  - The whitepaper states the Block event is emitted on the first complete block per slot. The model allows `ReceiveBlock` to run for any `block ∈ blockAvailability[v]` (including multiple blocks per slot if learned via Rotor/Repair). This is benign because `HandleBlock` won’t re-cast initial votes (`Voted` guard) and extra invocations are no-ops; however, it is a slight deviation from the “first-only” wording.

- Pending block cardinality.
  - Whitepaper defines a single `pendingBlocks[s]` value; the spec generalizes to a set (`pendingBlocks: [Slots -> SUBSET Block]`) and in `CheckPendingBlocks` attempts one pending block per slot per call. With fairness, this still suffices, but it is a small abstraction gap worth documenting.

- Explicit validity check.
  - `ReceiveBlock` trusts `block ∈ blocks` to imply well-formedness. Today all block-creation actions enforce validity, so this is safe; adding an explicit `IsValidBlock(block)` guard would make the dependency clearer.

**Suggestions**

- Optional: Align event exactness with whitepaper by guarding against re-emitting Block for the same slot, e.g., record a per-slot “BlockSeen” flag in validator state or treat `pendingBlocks[s]` as single-valued and ignore subsequent `ReceiveBlock` for the same slot. This strengthens fidelity without changing behavior.

- Optional: Add an `IsValidBlock(block)` conjunct to `ReceiveBlock` to make the reliance on prior validity checks explicit and robust to future changes.

- Documentation: Add comments near `ReceiveBlock` clarifying that network broadcasts are decoupled into separate actions (`BroadcastLocalVote`, `DeliverVote`), mapping the “broadcast” verbs in Algorithm 1 to these actions.

