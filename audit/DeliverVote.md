**Code Under Audit**

- `specs/tla/alpenglow/MainProtocol.tla:293`

```
DeliverVote ==
    /\ \E vote \in messages : vote \in Vote
    /\ LET vmsg == CHOOSE vv \in messages : vv \in Vote
       IN /\ messages' = messages \ {vmsg}
          /\ validators' = [w \in Validators |->
                               [validators[w] EXCEPT
                                   !.pool = StoreVote(@, vmsg)]]
    /\ UNCHANGED <<blocks, byzantineNodes, time, finalized, blockAvailability>>
```

**Whitepaper References**

- Definition 11 (messages) — vote and certificate message families
  - `alpenglow-whitepaper.md:478`
- Definition 12 (storing votes) — Pool multiplicity rules per slot/validator
  - `alpenglow-whitepaper.md:513`
- 2.5 Pool — nodes memorize votes/certificates in a local Pool
  - `alpenglow-whitepaper.md:520`
- Standstill re-transmission (eventual delivery after GST context)
  - `alpenglow-whitepaper.md:1231`

Related spec context used by this action:

- Vote definition and validation
  - `Vote` structure: `specs/tla/alpenglow/Messages.tla:52`
  - `IsValidVote`: `specs/tla/alpenglow/Messages.tla:162`
- Pool storage (Definition 12)
  - `CanStoreVote`: `specs/tla/alpenglow/VoteStorage.tla:54`
  - `StoreVote`: `specs/tla/alpenglow/VoteStorage.tla:84`
  - Invariant `MultiplicityRulesRespected`: `specs/tla/alpenglow/VoteStorage.tla:318`
- Network producers/consumers of votes
  - `BroadcastLocalVote`: `specs/tla/alpenglow/MainProtocol.tla:319`
  - `ByzantineAction`: `specs/tla/alpenglow/MainProtocol.tla:167`
  - Fairness on delivery: `specs/tla/alpenglow/MainProtocol.tla:421`

**Reasoning**

- Purpose and abstraction
  - Models dissemination and storage of vote messages: removes a single vote from `messages` and stores it in every validator’s Pool using `StoreVote`.
  - Leaves unrelated state unchanged, reflecting that vote delivery does not alter blocks, time, finalized sets, or availability directly.

- Alignment with Definition 12 (Pool multiplicity)
  - `StoreVote` enforces per-slot/per-validator limits: exactly one `NotarVote` and one `SkipVote`, up to 3 `NotarFallbackVote`, exactly one `SkipFallbackVote`, and one `FinalVote`. This matches Definition 12’s storage rules.
  - Because `StoreVote` is applied to each `validators[w].pool`, delivery respects multiplicity for all nodes independently.

- Network and eventual delivery
  - `DeliverVote` chooses any vote message in-flight (`CHOOSE vv \in messages : vv \in Vote`), removes it, and stores it globally. With weak fairness on `DeliverVote`, all vote messages are eventually delivered. This models the paper’s “broadcast to all other nodes” at an abstract level.
  - Votes in `messages` originate from either `BroadcastLocalVote` (honest rebroadcast of locally stored votes) or `ByzantineAction` (adversarial injection) and are therefore valid by construction (`IsValidVote` is enforced for Byzantine injection, and honest votes are created via the `Create*` helpers).

- Count-once stake semantics preserved
  - While a Byzantine validator might emit both a `NotarVote` and a `SkipVote` for the same slot, `StoreVote` permits storing the first instance of each type. The stake aggregation functions used for certificates and fallback events (e.g., `NotarStake`, `SkipStake`, `TotalNotarStake`, `MaxNotarStake`) count validators once within each relevant set, preserving the “count once per slot” rule of §2.4.

- Nondeterminism and granularity
  - Delivering to all validators at once is an intentional abstraction that compresses per-recipient delivery steps into one transition. It is safe for the proof obligations in this model, and fairness ensures no message is starved.

**Conclusion**

- The action correctly implements the whitepaper’s Pool storage behavior for votes (Definition 12) and abstracts “broadcast to all nodes” by applying `StoreVote` to every validator upon delivery.
- Combined with fairness and the network producers (`BroadcastLocalVote`, `ByzantineAction`), the model reflects eventual delivery after GST and maintains Pool multiplicity invariants.
- No safety issues were found with respect to the whitepaper-defined abstractions; the action meshes with certificate generation and fallback-event logic via the Pool state.

**Open Questions / Concerns**

- Validity check at delivery
  - `DeliverVote` does not assert `IsValidVote(vmsg)` in its guard. Today, all votes entering `messages` are valid (honest broadcasts or `ByzantineAction` which enforces `IsValidVote`), but adding the check would make the module more robust to future extensions that might introduce other message sources.

- Strong broadcast abstraction
  - Delivering to all validators in a single step is a strong abstraction relative to per-recipient network delivery. It is acceptable here (liveness relies on fairness and standstill re-transmission), but if the model later needs to reason about partial delivery patterns for votes, a per-recipient delivery action may be warranted.

**Suggestions for Improvement**

- Optional: Gate delivery on validity
  - Strengthen the guard to `\E vote \in messages : vote \in Vote /\ IsValidVote(vote)` for symmetry with certificate delivery (if similarly tightened) and extra resilience.

- Optional: Refine delivery granularity
  - If modeling partial deliveries becomes important, replace the “deliver to all” update with a per-recipient variant `DeliverVoteTo(w)` and then quantify over `w`. This preserves correctness while enabling fine-grained network schedule reasoning.

**Cross-File References**

- Main action under audit: `specs/tla/alpenglow/MainProtocol.tla:293`
- Vote type and validity: `specs/tla/alpenglow/Messages.tla:52`, `specs/tla/alpenglow/Messages.tla:162`
- Pool storage rules and invariant: `specs/tla/alpenglow/VoteStorage.tla:54`, `specs/tla/alpenglow/VoteStorage.tla:84`, `specs/tla/alpenglow/VoteStorage.tla:318`
- Vote producers and delivery fairness: `specs/tla/alpenglow/MainProtocol.tla:319`, `specs/tla/alpenglow/MainProtocol.tla:167`, `specs/tla/alpenglow/MainProtocol.tla:421`

