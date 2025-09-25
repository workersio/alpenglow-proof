# Audit: IsValidVote (Messages.tla)

1. Code that you are auditing.

```tla
IsValidVote(vote) ==
    /\ vote.type \in VoteType
    /\ vote.validator \in Validators
    /\ vote.slot \in Slots
    /\ (IsNotarVote(vote) => vote.blockHash \in BlockHashes)
    /\ (IsSkipVote(vote) \/ vote.type = "FinalVote" => vote.blockHash = NoBlock)
```

Source: `specs/tla/alpenglow/Messages.tla:163`

2. The whitepaper section and references that the code represents.

- Definition 11 (messages): `alpenglow-whitepaper.md:478`
- Table 5 (vote types and payloads): `alpenglow-whitepaper.md:489`
- Table 6 (certificate thresholds per vote family): `alpenglow-whitepaper.md:499`
- Definition 12 (Pool stores initial/fallback/final votes, one-per rules): `alpenglow-whitepaper.md:513`
- Algorithm references that emit votes (context for payloads):
  - FinalVote(s): `alpenglow-whitepaper.md:700`
  - NotarVote(s, hash(b)): `alpenglow-whitepaper.md:692`
  - SkipVote(s) and SkipFallbackVote(s): `alpenglow-whitepaper.md:707`, `alpenglow-whitepaper.md:665`

3. The reasoning behind the code and what the whitepaper claims.

- Vote typing:
  - The predicate ensures `vote.type ∈ VoteType`, `vote.validator ∈ Validators`, and `vote.slot ∈ Slots`, aligning with the abstract model where votes are typed by one of five kinds, cast by known validators, and indexed by a slot (Definition 11; Section 1.5 establishes Validators and slotting).
- Block reference discipline (core to Table 5):
  - Approval-family votes (NotarVote, NotarFallbackVote) must carry a real block hash: enforced by `IsNotarVote(vote) => vote.blockHash ∈ BlockHashes`. This matches Table 5, where these messages are `... (slot(b), hash(b))`.
  - Skip-family votes (SkipVote, SkipFallbackVote) and FinalVote must not carry a block hash: enforced by `(IsSkipVote(vote) ∨ vote.type = "FinalVote") => vote.blockHash = NoBlock`. Table 5 lists these as `... (s)` without a block hash; the model uses `NoBlock` as a sentinel, with the separate assumption `NoBlock ∉ BlockHashes` to keep domains disjoint (Messages.tla constants).
- Union field in Vote record model:
  - The `Vote` record schema allows `blockHash ∈ BlockHashes ∪ {NoBlock}` (Messages.tla). IsValidVote further narrows it to the correct side of the union based on vote family, exactly mirroring Table 5’s payloads.
- Protocol usage sanity:
  - Network ingress only accepts votes satisfying this predicate (DeliverVote in `specs/tla/alpenglow/MainProtocol.tla:542`).
  - Certificates defensively check `∀ v ∈ cert.votes : IsValidVote(v)` (`specs/tla/alpenglow/Certificates.tla:284`). This ensures downstream aggregation never relies on malformed votes.

4. The conclusion of the audit.

- Correctness: The predicate faithfully captures the whitepaper’s message payload rules (Table 5) and basic typing. Approval votes require a real block hash; skip and finalization votes forbid it via a distinguished `NoBlock` value.
- Completeness at the intended abstraction: For message validity as an abstract, format-level property, the constraints are sufficient and aligned with how votes are emitted in the algorithms (lines cited above). Multiplicity, per-slot uniqueness, and safety preconditions are correctly modeled elsewhere (Definition 12; algorithm guards), not in this predicate.

5. Any open questions or concerns.

- Redundancy vs. Vote schema: Call sites often check `vote ∈ Vote` together with `IsValidVote(vote)` (e.g., DeliverVote). This is consistent, but the division of responsibilities could be documented: `Vote` ensures structural typing; `IsValidVote` enforces semantic payload constraints. Today, both are used together at ingress, which is fine.
- Extensibility: If additional vote types are introduced in the future, the complement form `(¬IsNotarVote) ⇒ blockHash = NoBlock` might be preferable for future-proofing; the current explicit disjunction correctly matches today’s five types.

6. Any suggestions for improvement.

- Add a helper for symmetry: `IsFinalVote(v) == v.type = "FinalVote"` to mirror the other family predicates and improve readability where direct string equality is used.
- Optional lemma for clarity (already implied):
  - `∀ v : IsNotarVote(v) ⇒ v.blockHash ∈ BlockHashes`.
  - `∀ v : IsSkipVote(v) ∨ IsFinalVote(v) ⇒ v.blockHash = NoBlock`.
  These can aid proofs by making payload discipline available without unfolding IsValidVote.
- Document the contract near DeliverVote: explicitly state that ingress requires both `v ∈ Vote` and `IsValidVote(v)` to accept only well-typed, semantically-valid votes.

```text
Files referenced
- specs/tla/alpenglow/Messages.tla:163
- specs/tla/alpenglow/MainProtocol.tla:542
- specs/tla/alpenglow/Certificates.tla:284
- alpenglow-whitepaper.md:478
- alpenglow-whitepaper.md:489
- alpenglow-whitepaper.md:499
- alpenglow-whitepaper.md:513
- alpenglow-whitepaper.md:665
- alpenglow-whitepaper.md:692
- alpenglow-whitepaper.md:700
```

