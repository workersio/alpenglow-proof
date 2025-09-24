# Audit: Certificates.CanCreateNotarFallbackCert

1. Code that you are auditing

```
CanCreateNotarFallbackCert(votes, slot, blockHash) ==
    LET relevantVotes == {v \in votes :
        /\ v.type \in {"NotarVote", "NotarFallbackVote"}
        /\ v.slot = slot
        /\ v.blockHash = blockHash}
    IN MeetsThreshold(StakeFromVotes(relevantVotes), 60)
```

Reference location: `specs/tla/alpenglow/Certificates.tla:111`–`specs/tla/alpenglow/Certificates.tla:116`

Related operators used here:
- `StakeFromVotes`: `specs/tla/alpenglow/Certificates.tla:64`
- `MeetsThreshold`: `specs/tla/alpenglow/Certificates.tla:68`
- `UniqueValidators` (used by `StakeFromVotes`): `specs/tla/alpenglow/Certificates.tla:60`
- `CalculateStake` and `TotalStake` (aggregators): `specs/tla/alpenglow/Certificates.tla:49`, `specs/tla/alpenglow/Certificates.tla:38`

External types/constants referenced via module context:
- Vote structure and vote types: `specs/tla/alpenglow/Messages.tla:32`–`specs/tla/alpenglow/Messages.tla:79`
- Certificate type universe: `specs/tla/alpenglow/Messages.tla:129`–`specs/tla/alpenglow/Messages.tla:152`
- `Validators`, `Slots`, `BlockHashes`, `NoBlock` constants: `specs/tla/alpenglow/Messages.tla:15`–`specs/tla/alpenglow/Messages.tla:28`
- Stake map assumption: `specs/tla/alpenglow/Certificates.tla:20`–`specs/tla/alpenglow/Certificates.tla:26`

Usage sites (for context):
- Certificate generation uses this predicate: `specs/tla/alpenglow/VoteStorage.tla:196`–`specs/tla/alpenglow/VoteStorage.tla:197`

2. The whitepaper section and references that the code represents

- Section 2.4 “Votes and Certificates” introduces voting/certificates at high level: `alpenglow-whitepaper.md:476`
- Table 6 (Definition 11): “Notar-Fallback Cert.” row specifies aggregated votes and threshold:
  - Row: “Notar-Fallback Cert. | NotarVote or NotarFallbackVote | Σ ≥ 60%”: `alpenglow-whitepaper.md:503`
  - Table header defining Σ as cumulative stake: `alpenglow-whitepaper.md:507`
- Pool storage (Definition 12) establishing per-slot storage and multiplicity, used to justify counting once per slot: `alpenglow-whitepaper.md:513`
- Count-once reminder in Definition 16 preface: “stake of any node can be counted only once per slot”: `alpenglow-whitepaper.md:554`
- Implication note: Fast-finalization implies Notarization implies Notar-Fallback (certificate cascade): `alpenglow-whitepaper.md:534`

3. Reasoning behind the code and what the whitepaper claims

- Vote selection matches Table 6:
  - `relevantVotes` includes exactly those votes with `v.type ∈ {NotarVote, NotarFallbackVote}` and scoped to the specific `(slot, blockHash)`. This directly realizes the “Aggregated Votes” column for Notar‑Fallback Certificates (Table 6).

- Threshold check encodes “Σ ≥ 60%” precisely:
  - `MeetsThreshold(StakeFromVotes(relevantVotes), 60)` computes stake over the chosen votes and checks it against 60% of total stake using integer arithmetic: `stake * 100 ≥ TotalStake * 60` (`specs/tla/alpenglow/Certificates.tla:68`). This avoids division/rounding and is monotonic.

- Count-once per slot is enforced during aggregation:
  - `StakeFromVotes` delegates to `CalculateStake(UniqueValidators(votes))`, i.e., it sums stake over the set of unique validators present in `relevantVotes` (`specs/tla/alpenglow/Certificates.tla:60`, `specs/tla/alpenglow/Certificates.tla:64`).
  - Since `relevantVotes` may include both `NotarVote` and `NotarFallbackVote` from the same validator for the same `(slot, blockHash)`, `UniqueValidators` ensures that validator’s stake is counted only once. This implements the paper’s “count only once per slot” principle (`alpenglow-whitepaper.md:554`) in the context where votes are aggregated for certificates (and aligns with the Pool multiplicity in Definition 12, `alpenglow-whitepaper.md:513`).

- Slot and block scoping are correct:
  - Filtering by `v.slot = slot` and `v.blockHash = blockHash` ensures Σ is computed for a single block within a specific slot, exactly as intended by Table 6.

- Relationship to the broader protocol:
  - The conditions for when correct nodes emit notar‑fallback votes (SafeToNotar) are modeled elsewhere (e.g., `CanEmitSafeToNotar` in `specs/tla/alpenglow/VoteStorage.tla:280`–`specs/tla/alpenglow/VoteStorage.tla:293`). Certificate creation itself is purely threshold‑based per Table 6, which this operator captures. Correct nodes will only contribute notar‑fallback votes under safe conditions, but the certificate predicate does not embed those preconditions, consistent with the whitepaper’s separation of concerns (Tables define formation thresholds; events define when to emit fallback votes).

- Consistency with “fast implies notarization implies notar‑fallback”:
  - In `VoteStorage.GenerateCertificate` (`specs/tla/alpenglow/VoteStorage.tla:176`–`specs/tla/alpenglow/VoteStorage.tla:205`), whenever the fast or notarization conditions hold, the corresponding downstream certificates, including Notar‑Fallback, are created together. This realizes the paper’s implication note (`alpenglow-whitepaper.md:534`).

4. Conclusion of the audit

- The operator precisely encodes Table 6 for the Notar‑Fallback Certificate:
  - Aggregated votes: `NotarVote ∪ NotarFallbackVote` scoped to `(slot, blockHash)`.
  - Threshold: Σ ≥ 60% of total stake.
  - Deduplication: stake is counted once per validator per slot/block via `UniqueValidators` → `StakeFromVotes`, matching the paper’s “count once per slot”.

- The operator composes cleanly with the surrounding spec:
  - Types and vote fields are provided by `Messages.tla`.
  - Total stake and stake sums are defined in the same module and assume strictly positive per‑validator stake.
  - It is used correctly by `VoteStorage.GenerateCertificate`, which ensures the expected certificate cascade under stronger thresholds.

Overall, the implementation conforms to the whitepaper and correctly abstracts the intended certificate condition without embedding orthogonal event‑emission preconditions.

5. Open questions or concerns

- Scope of “count once per slot” in Table 6: The TLA+ implementation counts each validator once within the selected `(slot, blockHash)` and across the union of {NotarVote, NotarFallbackVote}. This matches the paper’s repeated “count once per slot” guidance. If the authors intended Σ in Table 6 to count multiple fallback votes from the same validator toward the same certificate (unlikely and unsafe), the current model intentionally disallows it (which seems correct).

- Adversarial fallback votes: `CanStoreVote` permits storing up to 3 notar‑fallback votes per validator per slot (Definition 12). Since `StakeFromVotes` deduplicates by validator, adversarially sending multiple fallback votes does not inflate stake in Σ. This seems intended, but is worth documenting next to the operator as a non‑obvious safety property.

- Preconditions on fallback voting (SafeToNotar): These are modeled in event logic, not in the certificate predicate. This separation matches the whitepaper, but readers might expect an explicit cross‑reference here. A short note could reduce specification‑reader confusion.

6. Suggestions for improvement

- Add a brief comment above the operator pointing to Definition 12 and the deduplication path (`UniqueValidators` → `StakeFromVotes`) to make the “count once” rationale explicit.

- Optional readability helper: Introduce a tiny combinator to capture the common scoping pattern and reduce boilerplate across `CanCreate*` operators, e.g.,
  - `VotesFor(slot, blockHash, types) == {v \in votes : v.slot = slot /\ v.blockHash = blockHash /\ v.type \in types}`
  This would make each `CanCreate*` read in a nearly tabular form mirroring Table 6.

- Consider adding an invariant capturing the certificate cascade the paper notes:
  - Given a `FastFinalizationCert` for `(slot, block)`, a `NotarizationCert` exists (already modeled by `FastFinalizationImpliesNotarization`: `specs/tla/alpenglow/Certificates.tla:217`).
  - Optionally, add that when a `NotarizationCert` exists, a `NotarFallbackCert` also exists in the same slot/block in Pool state (this is operationally enforced by `GenerateCertificate` and would be useful to surface as a property for readers/tools).

- Document the precondition that call sites should pass Pool‑sourced votes. While `StakeFromVotes` is defensive against duplicates, clarifying this aids spec hygiene and aligns with Definition 12.

