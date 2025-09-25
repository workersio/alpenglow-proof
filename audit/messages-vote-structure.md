# Audit: VoteType and Vote structure (Messages.tla)

1. Code that you are auditing

```tla
VoteType == {
    "NotarVote",           \* Initial approval vote for a block
    "NotarFallbackVote",   \* Fallback approval (up to 3 allowed per validator)
    "SkipVote",            \* Initial vote to skip a slot
    "SkipFallbackVote",    \* Fallback skip vote
    "FinalVote"            \* Second-round finalization vote
}

\* Structure of a vote message
Vote == [
    type: VoteType,                           \* Which of the 5 vote types
    validator: Validators,                    \* Who is voting
    slot: Slots,                             \* Which slot this vote is for
    blockHash: BlockHashes \union {NoBlock}  \* What block (NoBlock for skips)
]
```

2. Whitepaper section and references represented by this code

- Messages overview and tables: alpenglow-whitepaper.md:478 (Definition 11)
- Voting message types (Table 5): alpenglow-whitepaper.md:490
- Certificate types and thresholds (Table 6): alpenglow-whitepaper.md:501
- Pool storage rules for votes (Definition 12): alpenglow-whitepaper.md:513
- Certificate generation/storage (Definition 13): alpenglow-whitepaper.md:520
- Finalization definition and slow vs fast semantics (Definition 14): alpenglow-whitepaper.md:536
- Pool events and fallback preconditions (Definition 15/16): alpenglow-whitepaper.md:543, alpenglow-whitepaper.md:554

3. Reasoning: how the code maps to the whitepaper

- Vote family (Table 5): The five variants in `VoteType` match the whitepaper’s voting messages exactly: `NotarVote`, `NotarFallbackVote`, `SkipVote`, `SkipFallbackVote`, `FinalVote` (Table 5).
- Vote payload fields:
  - `validator: Validators` and `slot: Slots` identify who votes and for which slot, as assumed throughout §2.4–§2.6 and Algorithms 1–2.
  - `blockHash: BlockHashes ∪ {NoBlock}` captures that only notarization-type votes reference a block hash (Table 5), while skip and finalization votes are slot-scoped and thus carry `NoBlock`.
    - This conforms to Table 5 where `FinalVote(s)` and `SkipVote(s)`/`SkipFallbackVote(s)` carry only a slot `s`.
- Type discipline across modules (Messages.tla): Beyond the audited snippet, `IsValidVote` constrains these fields to whitepaper semantics: notarization votes require `blockHash ∈ BlockHashes`, while skip and finalization votes require `blockHash = NoBlock` (specs/tla/alpenglow/Messages.tla:163).
- Interaction with Pool rules (Definition 12): Multiplicity constraints (one initial vote per slot, up to 3 notar-fallback, first skip-fallback, first finalization) are enforced in VoteStorage (CanStoreVote/StoreVote), matching Def. 12.
- Certificates (Table 6) consume `Vote` objects per-type with threshold Σ checks (≥80% fast; ≥60% for others) in Certificates.tla, consistent with §2.4.

4. Cross-file references and usages (context)

- Definitions of referenced symbols in-scope:
  - `Validators, Slots, BlockHashes, NoBlock` are constants in Messages (specs/tla/alpenglow/Messages.tla:16).
- Message construction used by Votor (Algorithms 1–2):
  - `CreateNotarVote` used in TRYNOTAR (specs/tla/alpenglow/VotorCore.tla:122)
  - `CreateFinalVote` used in TRYFINAL (specs/tla/alpenglow/VotorCore.tla:148)
  - `CreateSkipVote` used in TRYSKIPWINDOW (specs/tla/alpenglow/VotorCore.tla:174)
  - `CreateNotarFallbackVote` used in SafeToNotar handler (specs/tla/alpenglow/VotorCore.tla:280)
  - `CreateSkipFallbackVote` used in SafeToSkip handler (specs/tla/alpenglow/VotorCore.tla:296)
- Pool storage and aggregation over `Vote`:
  - Pool stores votes per-slot/per-validator (SUBSET Vote) (specs/tla/alpenglow/VoteStorage.tla:25)
  - Aggregation and thresholding read votes per slot (e.g., GetVotesForSlot) (specs/tla/alpenglow/VoteStorage.tla:142)
- System typing relies on this vote shape:
  - `messages ⊆ (Vote ∪ Certificate)` in the main type invariant (specs/tla/alpenglow/MainProtocol.tla:985)

5. Conclusion of the audit

- The `VoteType` and `Vote` record align with the whitepaper’s Definition 11 and Tables 5–6. In particular:
  - All five vote types are present, named consistently with the paper.
  - Slot-only votes (Skip, SkipFallback, Final) are modeled via `blockHash = NoBlock`, matching Table 5’s slot-only signatures.
  - Notarization-type votes require a block hash, matching NotarVote/NotarFallbackVote definitions.
- Surrounding helpers (`IsValidVote`, creators, and Pool multiplicity rules) enforce the typing and one-per-slot semantics required by Definitions 12–16.
- Therefore, the abstraction faithfully represents the message-level structure required by §2.4–§2.6 and is consistent with certificate construction in §2.4 and finalization in §2.5.

6. Open questions or concerns

- TLA+ operator typo: The snippet (and Messages.tla) uses `\union` for binary union (e.g., `BlockHashes \union {NoBlock}`), while TLA+ uses `\cup` for binary union and `UNION S` for big union. This likely won’t parse in TLC/Apalache.
  - Instances: specs/tla/alpenglow/Messages.tla:57 and :154; also MainProtocol uses `\union` in the type invariant (specs/tla/alpenglow/MainProtocol.tla:985).
- Consistency of slot-only votes: Ensure all creators for slot-only votes set `blockHash = NoBlock`. Messages.tla currently does so for Skip and Final votes; this is correct (specs/tla/alpenglow/Messages.tla:86, :94, :101).
- String-typed tags: `VoteType` uses string literals. While common in TLA+, this can be error-prone if typos slip in across modules. Consider symbolic constants to reduce risk.

7. Suggestions for improvement

- Replace `\union` with `\cup` for binary set union in all TLA modules to ensure parser compatibility:
  - Messages.tla: `blockHash: BlockHashes \cup {NoBlock}` in both `Vote` and `Certificate` records.
  - MainProtocol.tla: `messages \subseteq (Vote \cup Certificate)` in `TypeInvariant`.
- Add a local type lemma documenting vote well-formedness, if you want explicit checking in invariants, e.g., `\A v \in messages : v \in Vote => IsValidVote(v)` (optional; `TransitCertificatesValid` already covers certs).
- Optionally define `NotarVoteT`, `SkipVoteT`, etc., as named constants bound to the string tags to avoid accidental typos across modules.
- Keep comments cross-linked to the paper (as already present) for quick audits; confirm Table 5/6 alignment if message families change in future revisions.

Overall, the abstraction matches the paper’s message definitions and integrates correctly with Pool and certificate logic. Fixing the minor `\union` operator issue will make the spec parser-safe.

