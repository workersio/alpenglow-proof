**Code Under Audit**

- `specs/tla/alpenglow/MainProtocol.tla:319`

```
BroadcastLocalVote ==
    /\ \E v \in CorrectNodes, s \in 1..MaxSlot :
         LET localVotes == validators[v].pool.votes[s][v]
         IN localVotes # {}
    /\ LET vSel == CHOOSE vv \in CorrectNodes :
                      \E s \in 1..MaxSlot : validators[vv].pool.votes[s][vv] # {}
           sSel == CHOOSE ss \in 1..MaxSlot : validators[vSel].pool.votes[ss][vSel] # {}
           vt == CHOOSE x \in validators[vSel].pool.votes[sSel][vSel] : TRUE
       IN 
          /\ vt \notin messages
          /\ \E w \in Validators : vt \notin validators[w].pool.votes[vt.slot][vt.validator]
          /\ messages' = messages \union {vt}
    /\ UNCHANGED <<validators, blocks, byzantineNodes, time, finalized, blockAvailability>>
```

**Whitepaper References**

- Broadcast semantics (send to all nodes)
  - `alpenglow-whitepaper.md:207`
- Algorithm 1 (event loop): broadcast of fallback votes
  - NotarFallbackVote: `alpenglow-whitepaper.md:659`
  - SkipFallbackVote: `alpenglow-whitepaper.md:665`
- Algorithm 2 (helpers): broadcast of initial/final votes
  - NotarVote: `alpenglow-whitepaper.md:692`
  - FinalVote: `alpenglow-whitepaper.md:702`
  - SkipVote (TRYSKIPWINDOW): `alpenglow-whitepaper.md:708`
- Pool definitions and storage rules
  - Section 2.5 Pool: `alpenglow-whitepaper.md:509`
  - Definition 12 (storing votes): `alpenglow-whitepaper.md:513`
  - Definition 13 (certificates; “broadcast when newly added to Pool” for certs): `alpenglow-whitepaper.md:520`, `alpenglow-whitepaper.md:523`
- Liveness after GST (retransmission guidance)
  - Standstill rebroadcast routine (rebroadcast own votes and certificates): `alpenglow-whitepaper.md:1231`
- Bandwidth section (common-case messaging: votes and certificates): `alpenglow-whitepaper.md:1271`

Related spec context used by this action:

- Correct nodes and constants
  - `CorrectNodes`: `specs/tla/alpenglow/MainProtocol.tla:57`
  - `MaxSlot`: `specs/tla/alpenglow/MainProtocol.tla:26`
  - `Validators`, `Slots`: `specs/tla/alpenglow/Messages.tla:17`, `specs/tla/alpenglow/Messages.tla:18`
- Pool structure and vote storage
  - `PoolState.votes`: `specs/tla/alpenglow/VoteStorage.tla:20`
  - `StoreVote`/`CanStoreVote`: `specs/tla/alpenglow/VoteStorage.tla:74`
- Network dissemination counterparts
  - `DeliverVote`: `specs/tla/alpenglow/MainProtocol.tla:293`
  - `messages` typing and invariant: `specs/tla/alpenglow/MainProtocol.tla:566`

**Reasoning**

- Intent and abstraction
  - The whitepaper’s Algorithms 1–2 use “broadcast … vote” steps whenever a node casts an initial, fallback, or final vote. The model decouples “casting” from “network dissemination”: votes are first stored locally in the validator’s Pool (VotorCore handlers), then `BroadcastLocalVote` injects them into the network (`messages`), and finally `DeliverVote` propagates them to all validators’ Pools. This realizes the “broadcast to all other nodes” semantics in an asynchronous setting without per-recipient channels.

- Enabling condition (existence of a local vote)
  - `∃ v ∈ CorrectNodes, s ∈ 1..MaxSlot : validators[v].pool.votes[s][v] ≠ {}` establishes there is at least one locally stored self-vote by some correct validator. This aligns with “nodes will then vote …” (Section 2.4/2.6) and ensures only honest votes are disseminated by this step; adversarial injection is modeled separately by `ByzantineAction`.

- Selection and gating
  - The `CHOOSE` chain selects a particular correct validator `vSel`, a slot `sSel`, and a specific vote `vt` from `validators[vSel].pool.votes[sSel][vSel]`. By construction, `vt` is a proper `Vote` record (Messages module) created via the VotorCore handlers using `Create*Vote` and stored via `StoreVote`.
  - Guards ensure efficiency and utility:
    - `vt ∉ messages` prevents duplicate insertion into the network set.
    - `∃ w ∈ Validators : vt ∉ validators[w].pool.votes[vt.slot][vt.validator]` ensures the broadcast is still useful (at least one node does not yet have this specific vote recorded in its Pool). This models “rebroadcast until everyone has it,” but only for the node’s own votes (consistent with the standstill guidance to send “own votes” at `alpenglow-whitepaper.md:1231`).

- Effect and unchanged frame
  - The action adds exactly `vt` to `messages` and does not modify Pools; propagation is handled by `DeliverVote`, which removes one vote from the network and stores it in every validator’s Pool via `StoreVote`. This pair of actions faithfully captures the paper’s broadcast-and-receive behavior with a simple set-based network abstraction.

- Coverage of whitepaper broadcast points
  - All vote kinds mentioned in Algorithms 1–2 are produced locally by their respective handlers (NotarVote in `TRYNOTAR`, FinalVote in `TRYFINAL`, SkipVote in `TRYSKIPWINDOW`, NotarFallback/SkipFallback in SafeToNotar/Skip handlers). `BroadcastLocalVote` is agnostic to type and will disseminate whichever self-vote exists and is still missing somewhere, matching the whitepaper’s “broadcast … vote” lines.

- Fairness and eventual delivery
  - Combined with weak fairness on `BroadcastLocalVote` and `DeliverVote` (MainProtocol `Fairness`), any locally stored vote that remains useful (missing at some node) will eventually be inserted into `messages` and then stored by all nodes. This aligns with the §2.10 liveness assumption that after GST, honest messages keep flowing.

**Conclusion**

- The action correctly abstracts the whitepaper’s broadcast of votes:
  - It selects self-votes of correct nodes from the Pool and injects them into the network only when useful, preventing redundant traffic.
  - It composes properly with `DeliverVote` to realize “broadcast to all nodes” semantics and with the VotorCore handlers that create local votes.
  - It preserves typing and does not alter unrelated state, maintaining the spec’s invariants.

Overall, `BroadcastLocalVote` matches the whitepaper’s intent for vote dissemination and integrates cleanly with Pool semantics (Definition 12) and the event loop (Algorithms 1–2).

**Open Questions / Concerns**

- Fairness gating vs. GST
  - The current spec applies weak fairness to `BroadcastLocalVote` unconditionally. The whitepaper’s liveness relies on post-GST eventual delivery. Consider gating the fairness obligation by `AfterGST` to match the model assumption (see also gaps report). This does not change safety, but improves fidelity to §2.10.

- “Own votes” vs. relaying others’ votes
  - The action only broadcasts votes from `validators[v].pool.votes[s][v]` (self-votes). This is consistent with Algorithm 1/2 and standstill guidance (rebroadcast own votes). If a design ever required validators to relay third-party votes, this action would need to be generalized (e.g., allow `validators[v].pool.votes[s][u]` for `u ≠ v` with appropriate safeguards). The whitepaper does not require such relaying in normal operation.

- Pool multiplicity semantics (cross-type “count once per slot”)
  - Definition 12 says “the first received notarization or skip vote” per validator and slot, implying mutual exclusion between initial vote types. The current Pool rules enforce per-type caps but not cross-type mutual exclusion. While this is orthogonal to `BroadcastLocalVote` (which only handles self-votes of correct nodes, produced once), it affects global stake accounting against Definition 16 and could influence when fallback votes are produced/relayed for Byzantine behavior.

**Suggestions for Improvement**

- Align fairness with §2.10
  - Change `WF_vars(BroadcastLocalVote)` to `WF_vars(IF AfterGST THEN BroadcastLocalVote ELSE UNCHANGED vars)` (and similarly for other message/event actions) to reflect that eventual delivery is only guaranteed after GST.

- Optional: clarify intent with a brief comment
  - Add a note that only self-votes are disseminated here (“rebroadcast own votes”), mapping explicitly to Algorithm 1/2 “broadcast … vote” lines and §2.10 standstill guidance.

- Consider strengthening Pool’s Definition 12 encoding
  - Enforce “first received notarization or skip (but not both)” per validator/slot in `CanStoreVote`, so that stake is counted at most once per slot per validator across initial-vote types, matching the text used by Definition 16.

**Cross-File References (for this block)**

- Main action under audit: `specs/tla/alpenglow/MainProtocol.tla:319`
- Network propagation of votes: `specs/tla/alpenglow/MainProtocol.tla:293`
- Pool structure and vote storage: `specs/tla/alpenglow/VoteStorage.tla:20`, `specs/tla/alpenglow/VoteStorage.tla:74`
- Vote types and fields (record structure): `specs/tla/alpenglow/Messages.tla:29`, `specs/tla/alpenglow/Messages.tla:45`
- Correct-nodes set: `specs/tla/alpenglow/MainProtocol.tla:57`

