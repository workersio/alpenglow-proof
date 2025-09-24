**Code Under Audit**

```
CreateFinalizationCert(votes, slot) ==
    [type |-> "FinalizationCert",
     slot |-> slot,
     blockHash |-> NoBlock,
     votes |-> {v \in votes : 
        v.type = "FinalVote" /\ v.slot = slot}]
```

**Whitepaper References**

- Definition 11 (messages): finalization vote `FinalVote(s)` — `alpenglow-whitepaper.md:478`, Table 5 at `alpenglow-whitepaper.md:495`.
- Table 6 (certificates): Finalization Cert aggregates `FinalVote`, threshold Σ ≥ 60% — `alpenglow-whitepaper.md:501`–`:507`.
- Definition 12 (storing votes): store the first finalization vote per node and slot — `alpenglow-whitepaper.md:513`.
- Definition 13 (certificates): single certificate of each type per block/slot in Pool — `alpenglow-whitepaper.md:520`.
- Definition 14 (finalization): a finalization certificate on slot `s` finalizes the unique notarized block in `s` — `alpenglow-whitepaper.md:536`.

Related spec context:

- FinalVote carries no block hash (slot-scoped) — `specs/tla/alpenglow/Messages.tla:96`–`:100`; `NoBlock` is a distinguished non-block value — `specs/tla/alpenglow/Messages.tla:20`–`:27`.
- Creation precondition: 60% stake on FinalVote in slot — `specs/tla/alpenglow/Certificates.tla:138`–`:142` (CanCreateFinalizationCert).
- Certificate validity enforces `blockHash = NoBlock` for FinalizationCert — `specs/tla/alpenglow/Certificates.tla:203`–`:205`.
- Pool uniqueness: at most one FinalizationCert per slot — `specs/tla/alpenglow/VoteStorage.tla:115`–`:117`.
- This constructor is used by generation logic — `specs/tla/alpenglow/VoteStorage.tla:204`–`:206`.

**Reasoning**

- Abstraction and scope: In the slow path, finalization is slot-scoped. Finalization votes are of the form `FinalVote(s)` and do not carry a block hash (Table 5). The finalization certificate aggregates these votes and is itself tied to a slot, not a block (Table 6, Definition 14). Setting `blockHash |-> NoBlock` in the certificate object therefore matches the abstraction that slow-path finalization is decided “for the slot” and relies on the unique notarized block within that slot to determine the finalized block.
- Vote filtering: The constructor includes only votes `v` with `v.type = "FinalVote"` and `v.slot = slot`. This aligns with Table 6 (certificate uses FinalVote) and keeps the certificate’s vote set semantically clean and slot-consistent.
- Threshold enforcement: The constructor itself is a pure record builder; threshold logic is handled separately:
  - `CanCreateFinalizationCert(votes, slot)` computes Σ over unique validators (count-once-per-slot; Definition 12) via `StakeFromVotes` — `specs/tla/alpenglow/Certificates.tla:138`–`:142`, `:63`–`:66`.
  - `IsValidCertificate` re-checks that a FinalizationCert has `blockHash = NoBlock` and meets the 60% threshold — `specs/tla/alpenglow/Certificates.tla:203`–`:205`.
- Pool rules and generation: Pool will generate this certificate when the precondition holds and ensures at most one FinalizationCert per slot (Definition 13) — `specs/tla/alpenglow/VoteStorage.tla:181`–`:207`, `:115`–`:117`.
- Link to finalized block: Per Definition 14, once a FinalizationCert for slot `s` exists, the finalized block is “the unique notarized block in slot `s`”. The constructor correctly omits any block hash, leaving the link to the notarized block to be inferred from Pool’s notarization state.

**Conclusion**

- The constructor matches the whitepaper’s abstraction exactly:
  - Slot-scoped certificate with `blockHash = NoBlock` is correct for slow-path finalization.
  - The vote set is filtered to FinalVote(s) for the same slot, as required.
  - Threshold and uniqueness are enforced by surrounding predicates (`CanCreateFinalizationCert`, `IsValidCertificate`, Pool’s storage rules), consistent with Definitions 12–14 and Table 6.
- No mismatches with the whitepaper were found in this constructor.

**Open Questions / Concerns**

- Validation completeness: `IsValidCertificate` checks threshold and `blockHash = NoBlock`, but does not assert that every `v \in cert.votes` satisfies `v.type = "FinalVote"` and `v.slot = cert.slot`. Today this is ensured indirectly by using this constructor, but if certificates are ever accepted from the network, an explicit check would harden the model.
- Acceptance path: `StoreCertificate` only enforces uniqueness (Definition 13) and does not call `IsValidCertificate`. If the spec intends to model receiving certificates from untrusted peers, consider validating certificates on ingest to keep invariants local to the storage path.
- Traceability: While slot-only finalization is faithful to the paper, some readers may expect an explicit link to the notarized block. The link is implied by Definition 14 and Pool’s notarization state; documenting this in a comment near the constructor could improve clarity.

**Suggestions for Improvement**

- Strengthen certificate validity:
  - Amend `IsValidCertificate` to enforce vote-type/slot consistency, e.g., for FinalizationCert: `\A v \in cert.votes : v.type = "FinalVote" /\ v.slot = cert.slot`.
  - Optional: ensure `cert.votes \subseteq GetVotesForSlot(pool, cert.slot)` when validating in a Pool context.
- Validate on store: Update `StoreCertificate` to require `IsValidCertificate(cert)` in addition to uniqueness if modeling network receipt.
- Clarify intent in code comments: Add a brief note referencing Definition 14 next to `blockHash |-> NoBlock` to remind readers that the finalized block is the unique notarized block for the slot.

**Key Code References**

- Constructor audited — `specs/tla/alpenglow/Certificates.tla:178`.
- Preconditions and validity — `specs/tla/alpenglow/Certificates.tla:138`, `specs/tla/alpenglow/Certificates.tla:203`.
- Vote/message types — `specs/tla/alpenglow/Messages.tla:96`, `specs/tla/alpenglow/Messages.tla:141`–`:155`.
- Pool uniqueness and generation — `specs/tla/alpenglow/VoteStorage.tla:115`, `specs/tla/alpenglow/VoteStorage.tla:181`–`:207`.
