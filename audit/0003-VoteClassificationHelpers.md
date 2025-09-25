# Audit: Vote Classification Helpers (Messages.tla)

1. Code that you are auditing.

```tla
IsNotarVote(vote) ==
    vote.type \in {"NotarVote", "NotarFallbackVote"}

\* Does this vote skip the slot (initial or fallback)?
IsSkipVote(vote) ==
    vote.type \in {"SkipVote", "SkipFallbackVote"}

\* Initial votes are the ones counted once per slot (Definition 12 / Lemma 20).
IsInitialVote(vote) ==
    vote.type \in {"NotarVote", "SkipVote"}

\* Is this a fallback vote (safety mechanism)?
IsFallbackVote(vote) ==
    vote.type \in {"NotarFallbackVote", "SkipFallbackVote"}

\* Does this vote support a specific block?
IsVoteForBlock(vote, blockHash) ==
    /\ IsNotarVote(vote)
    /\ vote.blockHash = blockHash
```

Source: `specs/tla/alpenglow/Messages.tla:112`

2. The whitepaper section and references that the code represents.

- Definition 11 (messages): `alpenglow-whitepaper.md:478`
- Table 5 (vote types): `alpenglow-whitepaper.md:492`
- Table 6 (certificate thresholds by vote family): `alpenglow-whitepaper.md:503`
- Definition 12 (storing votes; “count-once-per-slot” rule): `alpenglow-whitepaper.md:513`
- Lemma 20 (one notarization-or-skip initial vote per slot): `alpenglow-whitepaper.md:820`
- Definition 16 (fallback events reference notar(b) and skip(s) computed from initial votes): `alpenglow-whitepaper.md:554`

3. The reasoning behind the code and what the whitepaper claims.

- IsNotarVote groups the “approval” family: NotarVote and NotarFallbackVote. Table 5 defines these as votes that reference a specific block b. This abstraction matches the whitepaper’s split between initial approval and its fallback counterpart used after SafeToNotar.
- IsSkipVote groups the “skip” family: SkipVote and SkipFallbackVote. Table 5 defines these votes for a slot s without referencing any block. The helper aligns with that family grouping and is used where skip semantics are needed (e.g., certificate checks).
- IsInitialVote captures exactly the first-vote-per-slot types: NotarVote or SkipVote. This directly models Definition 12’s “first received notarization or skip vote” and underpins Lemma 20 (unique initial vote per slot per validator). Other modules use this to enforce and prove one initial vote per slot (see MainProtocol’s VoteUniqueness).
- IsFallbackVote captures the safety follow-ups: NotarFallbackVote and SkipFallbackVote. These are emitted only after the SafeToNotar/SafeToSkip conditions of Definition 16. Correctly excluding FinalVote from fallback classification avoids conflating second-round finalization with fallback mechanisms.
- IsVoteForBlock constrains “support for a block” to the approval family and matches on block hash. That mirrors Table 5 (only notarization-type votes carry a block hash) and is consistent with IsValidVote, which enforces blockHash ∈ BlockHashes for approval votes and blockHash = NoBlock for skip/final votes in `Messages.tla:167`–`Messages.tla:168`.

Cross-file usage sanity:
- Certificates: skip logic calls IsSkipVote and approval logic filters by explicit types; the family splits match Table 6 (`specs/tla/alpenglow/Certificates.tla:166`, `specs/tla/alpenglow/Certificates.tla:208`).
- Vote validation: IsValidVote relies on these helpers to enforce proper blockHash domains (`specs/tla/alpenglow/Messages.tla:167`).
- Vote uniqueness proof: IsInitialVote is used in VoteUniqueness (Lemma 20) to count “one per slot” (`specs/tla/alpenglow/MainProtocol.tla:793`).
- Pool stake for SafeToNotar/SafeToSkip: NotarStake/SkipStake compute over initial votes only, which corresponds to Definition 16’s notar(b) and skip(s) (`specs/tla/alpenglow/VoteStorage.tla:174`, `specs/tla/alpenglow/VoteStorage.tla:182`).

4. The conclusion of the audit.

- Correctness: The classification predicates are faithful to the whitepaper’s message taxonomy (Table 5), certificate groupings (Table 6), and the pool/uniqueness rules (Definition 12, Lemma 20). They cleanly separate approval vs skip, initial vs fallback, and block-referencing vs non-block votes.
- Integration: Downstream modules use these helpers consistently. Notably, SafeToNotar/SafeToSkip computations only examine initial votes, preventing circularity with fallback votes and matching Definition 16.
- Abstraction level: The predicates capture the intended abstract categories without implementation detail leakage, matching the TLA+ modeling intent.

5. Any open questions or concerns.

- Naming clarity: “IsNotarVote” includes NotarFallbackVote (as comments state). While correct, the name can be misread as “initial notarization only.” This is mitigated by comments, but could be made crisper.
- Deduplication overlap: Certificates.tla re-implements block/type filtering inline (e.g., VotesFor) instead of reusing IsVoteForBlock, which is fine but slightly duplicates intent. Not an error; just something to keep consistent.
- Explicit final classification: There is no IsFinalVote helper; the code uses direct type equality. This is consistent today but adds minor inconsistency vs the other families.

6. Any suggestions for improvement.

- Add IsFinalVote(v) == v.type = "FinalVote" for symmetry and readability in places like Certificates and validation.
- Add invariants/lemmas documenting domains:
  - For all votes v: IsNotarVote(v) => v.blockHash ∈ BlockHashes.
  - For all votes v: IsSkipVote(v) ∨ v.type = "FinalVote" => v.blockHash = NoBlock.
  These are already enforced by IsValidVote but stating them as separate lemmas can improve proof clarity.
- Consider renaming IsNotarVote to IsApprovalVote (or add an alias) to avoid ambiguity for new readers; keep the original as a convenience synonym if widely used.
- Optionally refactor Certificates’ filtering to reuse IsVoteForBlock where appropriate for consistency, while keeping the existing explicit forms for clarity where needed.

```text
Files referenced
- specs/tla/alpenglow/Messages.tla:112
- specs/tla/alpenglow/Messages.tla:167
- specs/tla/alpenglow/Certificates.tla:166
- specs/tla/alpenglow/Certificates.tla:208
- specs/tla/alpenglow/MainProtocol.tla:793
- specs/tla/alpenglow/VoteStorage.tla:174
- specs/tla/alpenglow/VoteStorage.tla:182
- alpenglow-whitepaper.md:478
- alpenglow-whitepaper.md:492
- alpenglow-whitepaper.md:503
- alpenglow-whitepaper.md:513
- alpenglow-whitepaper.md:554
- alpenglow-whitepaper.md:820
```

