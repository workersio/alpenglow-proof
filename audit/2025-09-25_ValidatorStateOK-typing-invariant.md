# Audit: VotorCore.ValidatorStateOK (typing invariant)

1. Code that you are auditing.

```tla
ValidatorStateOK(validator) ==
    /\ validator.id \in Validators
    /\ validator.state \in [Slots -> SUBSET StateObject]
    /\ validator.parentReady \in [Slots -> BlockHashes \cup {NoBlock}]
    /\ validator.pendingBlocks \in [Slots -> SUBSET Block]
    /\ PoolTypeOK(validator.pool)
    /\ validator.clock \in Nat
    /\ validator.timeouts \in [Slots -> Nat]
```

File: `specs/tla/alpenglow/VotorCore.tla:324`.

2. The whitepaper section and references that the code represents.

- Votor state — Definition 18: per-slot state objects, pendingBlocks; `alpenglow-whitepaper.md:615`, `alpenglow-whitepaper.md:632`.
- Pool events — Definition 15: ParentReady, BlockNotarized; `alpenglow-whitepaper.md:543`, `alpenglow-whitepaper.md:546`.
- Fallback events — Definition 16: conditions for BadWindow-related actions; `alpenglow-whitepaper.md:554`.
- Timeout model — Definition 17: local clock, timeout schedule; `alpenglow-whitepaper.md:607`, with context `alpenglow-whitepaper.md:602`, `alpenglow-whitepaper.md:613`.
- Votes/Certificates and Pool — Definitions 12–13 and Table 6: justify `PoolState` and Pool typing; `alpenglow-whitepaper.md:513`, `alpenglow-whitepaper.md:520`, `alpenglow-whitepaper.md:500`.
- Blocks and basic domains (Slots, Validators): structural context for `Block`; §2.1 and §1.1; see `specs/tla/alpenglow/Blocks.tla:47` and `specs/tla/alpenglow/Messages.tla:16`.

3. Reasoning: mapping each field to the whitepaper.

- `validator.id \in Validators`
  - Identity of the local validator. Validators are the node set used throughout §2. This is the root domain assumption in Messages.
  - Cross-ref: `specs/tla/alpenglow/Messages.tla:16`.

- `validator.state \in [Slots -> SUBSET StateObject]`
  - Matches Definition 18’s “state per slot initialized to ∅; objects can be permanently added”. The spec models state as a set of tags; parameter payloads (e.g., hash in `ParentReady(h)` or `VotedNotar(h)`) are stored in companion fields or recoverable from Pool.
  - Cross-refs: StateObject definition `specs/tla/alpenglow/VotorCore.tla:41`; helper use sites `:81`, `:85`.

- `validator.parentReady \in [Slots -> BlockHashes ∪ {NoBlock}]`
  - Carries the hash argument for the `ParentReady` state (Definition 15). Initialized to `NoBlock`, set when `ParentReady(s, h)` is handled; used by TRYNOTAR for first-slot voting.
  - Cross-refs: `HandleParentReady` computes and stores this, aligning with Definition 17 timeouts; `specs/tla/alpenglow/VotorCore.tla:255-268`.

- `validator.pendingBlocks \in [Slots -> SUBSET Block]`
  - Tracks blocks to retry TRYNOTAR on when preconditions were not yet met. Whitepaper describes a single optional pending block per slot; the spec generalizes to a set to accommodate multiple deliveries, which preserves the abstraction (retries) while being more permissive.
  - Cross-refs: CHECKPENDINGBLOCKS iterates pending sets; `specs/tla/alpenglow/VotorCore.tla:189-201`. Block type: `specs/tla/alpenglow/Blocks.tla:47`.

- `PoolTypeOK(validator.pool)`
  - Ensures Pool is well-typed: votes indexed by slot and validator and certificates are well-formed. This encodes the Pool structure from Definitions 12–13 and underpins events in Definition 15–16.
  - Cross-refs: `specs/tla/alpenglow/VoteStorage.tla:24-33` and PoolTypeOK `:268-274`.

- `validator.clock \in Nat` and `validator.timeouts \in [Slots -> Nat]`
  - Align with the local-clock, per-slot timeout schedule (Definition 17). The values are absolute local times; 0 denotes “not scheduled” in this model.
  - Cross-refs: timeout scheduling formula implemented in `HandleParentReady` and processed by `AdvanceClock`; `specs/tla/alpenglow/VotorCore.tla:255-268`, `:306-318`.

4. Conclusion of the audit.

- The typing predicate `ValidatorStateOK` is consistent with the whitepaper’s abstractions for Votor’s local state (Definition 18), ParentReady payload (Definition 15), Pool structure and events (Definitions 12–16), and the timeout model (Definition 17). It correctly delegates Pool well-formedness to `PoolTypeOK` and enforces that all per-slot memories and timers are defined over `Slots` with appropriate codomains.
- The generalization from a single pending block per slot to a set does not contradict the whitepaper abstraction and is handled safely by CHECKPENDINGBLOCKS and the voting guards.

5. Open questions or concerns.

- State object enumeration vs. paper list
  - The model’s `StateObject` includes `"Voted"` and `"BlockSeen"` (file `specs/tla/alpenglow/VotorCore.tla:41-49`). Definition 18 in the whitepaper enumerates `ParentReady`, `VotedNotar(h)`, `BlockNotarized(h)`, `ItsOver`, `BadWindow` but does not explicitly list `Voted` or `BlockSeen`.
  - `Voted` is referenced by Algorithm 1/2 pseudocode to gate re-voting, so its inclusion is faithful to the algorithm, even if omitted in Def. 18’s list. `BlockSeen` is a modeling aid to ignore duplicate Block events; it is not explicitly called out in the paper.
  - Impact on this audit: `ValidatorStateOK` allows any subset of `StateObject`, so admitting these two tags is a slight extension of Def. 18’s set. It does not violate safety but should be acknowledged as a spec-level convenience.

- Parameterized flags encoded via companion fields
  - The paper writes `ParentReady(h)` and `VotedNotar(h)`; the model keeps boolean tags in `state` and stores/derives the hash via `parentReady[slot]` or Pool queries. This is a common abstraction split, but it means `state` alone does not carry the hash argument. Readers should rely on the companion fields when tracing conditions.

- Domain of `Slots` vs. production slots
  - The predicate types fields over all `Slots`. The system often reasons about production slots `1..MaxSlot`; genesis `0` is present in `Slots` by assumption. This is fine, but some code paths explicitly intersect with `1..MaxSlot` (e.g., MainProtocol invariants). It may help to document that slot 0 is inert for Votor state.

6. Suggestions for improvement.

- Document the two extra state tags
  - Add a short comment near `StateObject` clarifying that `Voted` (used by Alg. 1–2) and `BlockSeen` (event de-duplication) are modeling conveniences beyond the minimal Def. 18 list.

- Optional: strengthen a readability invariant
  - Define `ParentReadyImpliesHashSet(s) == ("ParentReady" \in state[s]) => parentReady[s] \in BlockHashes` as a helper lemma, and similarly note that `BlockNotarized`’s corresponding block hash is learned via Pool events. This would guide readers without changing behavior.

- Pending blocks note
  - Briefly state in comments that `pendingBlocks[s]` may contain multiple candidates due to nondeterministic delivery, but TRYNOTAR and CHECKPENDINGBLOCKS ensure only one initial vote per slot (Pool multiplicity rules) and eventually clear the set.

- Cross-module linkage
  - In MainProtocol’s `TypeInvariant`, consider adding `AllCertificatesValid(validators[v].pool.certificates[s])` where appropriate (it already checks multiplicity and uniqueness) to make explicit the Table 6 alignment. This is orthogonal to `ValidatorStateOK` but reinforces correctness boundaries.

Overall assessment: PASS (correct by abstraction). The typing invariant accurately reflects the whitepaper’s Votor state and related structures, with clearly identifiable and benign modeling extensions.

