# Audit: ByzantineProposeBlock

1. Code being audited

```tla
ByzantineProposeBlock(leader, slot, parent) ==
    /\ leader = Leader(slot)
    /\ leader \in byzantineNodes
    /\ parent \in blocks
    /\ slot > parent.slot
    /\ slot <= MaxSlot
    /\ Cardinality(blocks) < MaxBlocks
    /\ LET newBlock == [
           slot |-> slot,
           hash |-> CHOOSE h \in BlockHashes :
                    h \notin {b.hash : b \in blocks},
           parent |-> parent.hash,
           leader |-> leader
       ]
       IN /\ blocks' = blocks \union {newBlock}
          /\ \E targets \in SUBSET Validators :
                blockAvailability' =
                    [w \in Validators |->
                        IF w \in targets THEN blockAvailability[w] \union {newBlock}
                        ELSE blockAvailability[w]]
          /\ UNCHANGED <<validators, messages, byzantineNodes, time, finalized>>
```

- Location: `specs/tla/alpenglow/MainProtocol.tla:202`
- Related definitions:
  - `Leader(slot)`: `specs/tla/alpenglow/Blocks.tla:149`
  - Constants/sets `Validators`, `Slots`, `BlockHashes`: `specs/tla/alpenglow/Messages.tla:17`
  - Variables `blocks`, `byzantineNodes`, `blockAvailability`, `validators`, `messages`, `time`, `finalized`: `specs/tla/alpenglow/MainProtocol.tla:84`–`98`
  - `blockAvailability` initialization: `specs/tla/alpenglow/MainProtocol.tla:98`
  - Bounded parameters `MaxSlot`, `MaxBlocks`: `specs/tla/alpenglow/MainProtocol.tla:20`–`34`

2. Whitepaper sections and references represented

- Adversary model (Byzantine behavior): Section “Adversary” (around Page 8), Assumption 1 (Byzantine <20% stake).
- Block creation by the leader and leader windows: Section 2.7 “Block Creation” (Pages 26–27) and algorithmic description (Algorithm 3).
- Data dissemination and partial availability: Section 2.2 “Rotor” overview (early discussion of dissemination) and Section 2.3 “Blokstor” (Pages ~18 and 458–470) describing storage of received blocks and emitting Block events.
- Ordering by slots and parent relation: Whitepaper description (line ~245): “child block has to have a higher slot number than its parent.”
- Safety and notarization uniqueness are indirectly relevant (Section 2.9) since this action is the source of potential equivocation (multiple blocks per slot), which later invariants must withstand.

3. Reasoning: mapping intention to whitepaper claims

- Leader-only proposals. The guard `leader = Leader(slot)` ensures only the designated slot leader can propose. This matches the leader schedule abstraction in §2.7 and the assumption that each slot has a designated leader selected by a (threshold) VRF. Reference: `Leader(slot)` in `Blocks.tla`.
- Byzantine capability. Requiring `leader \in byzantineNodes` cleanly separates adversarial actions. The whitepaper allows Byzantine nodes to misbehave arbitrarily; this action models two key misbehaviors:
  - Equivocation: CHOOSE selects a fresh `hash` not used before, and there is no restriction preventing multiple calls for the same `(leader, slot)`, enabling multiple distinct blocks in one slot.
  - Withholding/partial dissemination: the `targets \in SUBSET Validators` controls which nodes learn the block (i.e., have it in their “Blokstor” equivalent). The empty set is allowed (total withholding), as is any subset (selective sharing), consistent with an adversary who can send, delay, or drop messages.
- Valid parent and slot monotonicity. The guards `parent \in blocks` and `slot > parent.slot` enforce a valid ancestry relation consistent with the paper’s “child must have a higher slot number than its parent” (the paper does not require `slot = parent.slot + 1`, only strictly greater).
- Bounded state. `slot <= MaxSlot` and `Cardinality(blocks) < MaxBlocks` are model checking constraints and do not affect protocol semantics.
- State updates reflect dissemination vs. receipt. Adding `newBlock` to the global `blocks'` reflects the block’s existence in the system. Updating `blockAvailability'` only for `targets` represents which validators actually reconstructed the block (the Blokstor abstraction). Correct nodes may only process a block after it is available locally (`ReceiveBlock` checks `block \in blockAvailability[v]`, see `specs/tla/alpenglow/MainProtocol.tla:108`–`113`). This matches the whitepaper’s “Block” event emitted by Blokstor once a block is complete (Definition 10).
- Isolation from voting/certificates. The action leaves `validators`, `messages`, and `finalized` unchanged. That is correct: proposing a block does not itself cast votes or generate certificates. Voting is triggered by `ReceiveBlock` and subsequent Votor logic (§2.4–2.6), not by the leader’s local minting.
- Interplay with Rotor. For correct leaders, dissemination is modeled separately via `RotorDisseminateSuccess`/`RotorDisseminateFailure` (e.g., `specs/tla/alpenglow/MainProtocol.tla:240` and `:258`). For Byzantine leaders, this action’s `targets` update directly models adversarial dissemination choices. `RotorDisseminateSuccess` requires a correct leader, preventing unrealistic wide distribution by Byzantine leaders.

4. Conclusion of the audit

- The action accurately abstracts Byzantine leader behavior permitted by the whitepaper’s adversary model: minting multiple blocks for the same slot (equivocation) and sharing with arbitrary subsets of validators (withholding/partial release).
- Guards correctly enforce leader schedule adherence and valid ancestry while allowing the looser “slot strictly increases” relation consistent with the paper.
- The separation between “existence of blocks” (`blocks'`) and “local availability” (`blockAvailability'`) is consistent with the Blokstor/Rotor model: correct nodes only act on blocks they reconstructed.
- The action aligns with and stress-tests downstream safety lemmas (e.g., notarization uniqueness, finalization chain safety) without violating them on its own.

5. Open questions or concerns

- Domain guard for `slot`. The guard lacks an explicit `slot \in Slots`. In practice, `Next` quantifies `s \in 1..MaxSlot`, and models typically set `Slots` accordingly, but adding the explicit check would make the action robust against misconfigured models.
- Leader’s own availability. Unlike `HonestProposeBlock`, the Byzantine variant does not automatically add the new block to the leader’s `blockAvailability`. This is intentional (a Byzantine may withhold from anyone, including itself), but if you prefer to model “the proposer always has the data,” you could add an optional inclusion `leader \in targets` in explanatory comments.
- Multiple dissemination paths. A Byzantine-minted block could later be partially disseminated again via `RotorDisseminateFailure` (which does not require a correct leader). This is consistent (more nodes can learn about that block later), but be aware of the overlap.
- Freshness of `hash`. Ensure the TLC model provides a sufficiently large `BlockHashes` domain to avoid exhausting choices when exploring many equivocations under the `MaxBlocks` bound.

6. Suggestions for improvement

- Add an explicit domain guard: `slot \in Slots`. This clarifies typing and avoids relying on model instantiation to align `Slots` with `1..MaxSlot`.
- Comment cross-references. Add inline comments citing: Adversary model (Assumption 1), Section 2.7 (leader schedule, windows), and Section 2.3 (Blokstor) to ease reader mapping from code to paper.
- Optional: Name the subset variable descriptively, e.g., `recipients` instead of `targets`, to better convey “who learns the block”.
- Optional: If you want to explicitly model total withholding, a separate `ByzantineProposeBlockWithhold` that leaves `blockAvailability' = blockAvailability` can make scenarios more discoverable in TLC traces; functionally, the current `targets = {}` already captures this.

```
File pointers
- specs/tla/alpenglow/MainProtocol.tla:202
- specs/tla/alpenglow/Blocks.tla:149
- specs/tla/alpenglow/Messages.tla:17
- specs/tla/alpenglow/MainProtocol.tla:98
- specs/tla/alpenglow/MainProtocol.tla:108
- specs/tla/alpenglow/MainProtocol.tla:240
- specs/tla/alpenglow/MainProtocol.tla:258
```

Whitepaper anchors
- Adversary model and Assumption 1 (< ~Page 8, includes <20% Byzantine stake)
- 2.7 Block Creation (Pages 26–27, Algorithm 3)
- 2.2 Rotor (early subsection on dissemination)
- 2.3 Blokstor (Pages ~18, 458–470)
- Slot/parent monotonic relation (~line 245 in the text body)

