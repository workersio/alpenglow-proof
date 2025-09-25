# GenerateCertificate (VoteStorage.tla) — Audit

## 1. Code Under Audit

```tla
GenerateCertificate(pool, slot) ==
    LET votes == GetVotesForSlot(pool, slot)
        \* Candidate blocks are discovered via NotarVote only. Per Def. 16,
        \* notar-fallback votes arise only after sufficient notar stake is
        \* observed, so there won't be fallback-only blocks with zero NotarVote.
        notarBlocks == {vote.blockHash : vote \in {vt \in votes : vt.type = "NotarVote"}}
        BlockCertFor(block) ==
            IF CanCreateFastFinalizationCert(votes, slot, block) THEN
                {
                    CreateFastFinalizationCert(votes, slot, block),
                    CreateNotarizationCert(votes, slot, block),
                    CreateNotarFallbackCert(votes, slot, block)
                }
            ELSE IF CanCreateNotarizationCert(votes, slot, block) THEN
                {
                    CreateNotarizationCert(votes, slot, block),
                    CreateNotarFallbackCert(votes, slot, block)
                }
            ELSE IF CanCreateNotarFallbackCert(votes, slot, block) THEN
                {CreateNotarFallbackCert(votes, slot, block)}
            ELSE {}
        blockCerts ==
            UNION {BlockCertFor(block) : block \in notarBlocks}
        \* Gate SkipCert creation: do not emit if any block certificate is creatable
        skipCert == IF (blockCerts = {}) /\ CanCreateSkipCert(votes, slot)
                     THEN {CreateSkipCert(votes, slot)}
                     ELSE {}
        finalCert == IF CanCreateFinalizationCert(votes, slot)
                      THEN {CreateFinalizationCert(votes, slot)}
                      ELSE {}
    IN blockCerts \cup skipCert \cup finalCert
```

Context/definition location: `specs/tla/alpenglow/VoteStorage.tla:184`.

Related operator call site: `specs/tla/alpenglow/MainProtocol.tla:229` within `GenerateCertificateAction`.

## 2. Whitepaper Sections and References

- Messages and certificates (Definition 11; Tables 5–6): `alpenglow-whitepaper.md:478`, `alpenglow-whitepaper.md:491`, `alpenglow-whitepaper.md:501`–`507`.
- Pool (Definition 12 — storing votes): `alpenglow-whitepaper.md:509`–`513`.
- Certificates (Definition 13 — generation, storage, broadcast, uniqueness): `alpenglow-whitepaper.md:520`–`534`.
- Finalization (Definition 14 — fast vs slow): `alpenglow-whitepaper.md:536`–`539`.
- Pool events (Definition 15 — BlockNotarized, ParentReady): `alpenglow-whitepaper.md:543`–`546`.
- Fallback events and safety gates (Definition 16 — SafeToNotar, SafeToSkip): `alpenglow-whitepaper.md:556` and page markers “Page 22” (formulas for safety conditions).
- Section 2.6 overview (parallel fast/slow paths): `alpenglow-whitepaper.md:476`–`507`, `alpenglow-whitepaper.md:540`–`560`.

## 3. Reasoning vs. Whitepaper Claims

What the operator does:

- Aggregates all votes for slot `s` from the local Pool: `votes == GetVotesForSlot(pool, slot)`; this is the Pool-sourced vote set required by Definition 12 (count-once per slot per validator) that downstream “CanCreate*” guards assume. Definition: `specs/tla/alpenglow/VoteStorage.tla:142`.
- Discovers candidate blocks only from NotarVote messages: `notarBlocks == {… : vt.type = "NotarVote"}`. Rationale given in the comment: per Definition 16, notar-fallback votes follow observation of sufficient notar stake, so “fallback-only” blocks should not arise among correct nodes.
- For each candidate block, computes a certificate cascade (Table 6, Def. 13):
  - If fast-path (≥80%) holds, produce all three: FastFinalizationCert, NotarizationCert, NotarFallbackCert. This encodes the paper’s implication “fast ⇒ notar ⇒ fallback”. Guards/constructors are defined in `specs/tla/alpenglow/Certificates.tla:134`, `:216`, `:223`, `:230`.
  - Else if notarization (≥60%), produce NotarizationCert and NotarFallbackCert. Guard at `:148`; constructors at `:223`, `:230`.
  - Else if only fallback (≥60% using NotarVote ∪ NotarFallbackVote), produce NotarFallbackCert; guard at `:165`; constructor at `:230`.
- Unions per-block results into `blockCerts` (a set of zero or more certificates for the slot).
- Gates SkipCert creation: create SkipCert only when no block certificate is creatable, and skip stake meets ≥60%: `skipCert == IF (blockCerts = {}) /
  CanCreateSkipCert(votes, slot) THEN {CreateSkipCert(votes, slot)} ELSE {}`. Guard/constructor are defined at `specs/tla/alpenglow/Certificates.tla:177`, `:243`. This enforces the intended skip-vs-block mutual exclusion from §2.6: a slot is either skipped or a block is (fallback-)notarized.
- Independently adds FinalizationCert if enough FinalVote stake exists: `finalCert == IF CanCreateFinalizationCert(votes, slot) THEN {CreateFinalizationCert(votes, slot)} ELSE {}` (guard/constructor at `specs/tla/alpenglow/Certificates.tla:190`, `:252`). Per Definition 14, slow finalization requires NotarizationCert(s, b) in addition to FinalizationCert(s). The operator’s job is to emit creatable certificates; the finalization rule is enforced where certificates are consumed (`FinalizeBlock` in `MainProtocol.tla`).
- Returns the union `blockCerts ∪ skipCert ∪ finalCert`, i.e., all certificates that can be assembled from locally stored votes at this moment, as mandated by Definition 13.

External references resolved (all in module `Certificates` unless noted):

- Vote aggregation from Pool: `GetVotesForSlot` — `specs/tla/alpenglow/VoteStorage.tla:142`.
- Guards: `CanCreateFastFinalizationCert:134`, `CanCreateNotarizationCert:148`, `CanCreateNotarFallbackCert:165`, `CanCreateSkipCert:177`, `CanCreateFinalizationCert:190`.
- Constructors: `CreateFastFinalizationCert:216`, `CreateNotarizationCert:223`, `CreateNotarFallbackCert:230`, `CreateSkipCert:243`, `CreateFinalizationCert:252`.
- Vote/certificate typing and constants (VoteType, CertificateType, NoBlock): `specs/tla/alpenglow/Messages.tla`.

Whitepaper alignment:

- Thresholds and vote families exactly follow Table 6 (fast 80%; others 60%). Computation in guards uses “count-once per slot” stake via `StakeFromVotes` and `UniqueValidators` (Def. 12), see `Certificates.tla` stake helpers.
- Certificate production policy follows Definition 13: produce when thresholds are met; uniqueness and broadcast handled by Pool logic (`CanStoreCertificate` and `GenerateCertificateAction` in `MainProtocol.tla`).
- Skip vs block mutual exclusion is respected at generation time (don’t create SkipCert if any block certificate is creatable), reflecting §2.6’s intent.
- Finalization semantics match Definition 14 at the consumption site: `FinalizeBlock` checks presence of either fast cert (finalize immediately) or both slow-path certificates.

## 4. Conclusion

- The operator correctly encodes the certificate-generation rules from the whitepaper:
  - Thresholds and vote relevance (Table 6) are implemented in `Certificates.tla` and used here.
  - The cascade “fast ⇒ notar ⇒ fallback” is produced when fast-path holds, matching the paper’s implication (Def. 13 note).
  - Skip is produced only when no block certificate is creatable, capturing the mutual-exclusion intent of §2.6.
  - Finalization certificates are aggregated independently; finalization itself is enforced by Definition 14 in the main protocol.
- The operator relies on Pool-sourced votes (Definition 12) so that stake is counted once per validator per slot. This is satisfied by `GetVotesForSlot` and the guards’ `StakeFromVotes`.
- Overall, the logic is faithful to Definitions 12–14 and Tables 5–6, and integrates coherently with `GenerateCertificateAction` and `FinalizeBlock` in `MainProtocol.tla`.

## 5. Open Questions / Concerns

- Candidate discovery excludes fallback-only blocks: `notarBlocks` considers blocks with at least one NotarVote, ignoring blocks that (transiently) have only NotarFallbackVote in the local Pool. Table 6 allows Notar-Fallback certificates to be assembled from NotarVote ∪ NotarFallbackVote. While Definition 16 argues that correct nodes emit fallback only after observing sufficient notar stake, message delivery could cause a node to see fallback votes before any NotarVote. In that case, the current code would refrain from creating a valid NotarFallbackCert that it could otherwise assemble. This is a liveness conservatism (not a safety issue) and worth a conscious choice.
- Skip gating looks only at “creatable now” block certificates, not at already stored ones. In practice Pool does not prune votes, so if a block cert is stored the vote thresholds typically still hold and `blockCerts ≠ {}`. If ever votes lag but a block cert is stored, the current guard could, in theory, attempt SkipCert creation. That is then filtered by downstream selection logic and by mutual exclusivity implied by thresholds (a 60% notarization cannot coexist with a 60% skip under Lemma 20’s one-initial-vote rule). Still, an explicit cross-type exclusion at store time could make this airtight.
- FinalizationCert production is independent of block certificates. This is consistent with Def. 14 (finalization requires both), but an optional guard “FinalizationCert only when a NotarizationCert(s, b) exists/is creatable” could reduce churn if FinalVote messages appear before notarization is locally assembled.

## 6. Suggestions for Improvement

- Consider discovering fallback candidates from both notar and fallback votes:
  - Replace `notarBlocks == {… : vt.type = "NotarVote"}` with
    `notarBlocks == {v.blockHash : v ∈ votes ∧ v.type ∈ {"NotarVote","NotarFallbackVote"}}`.
  - This preserves safety and can improve liveness in out-of-order delivery.
- Optionally gate FinalizationCert creation on notarization knowledge:
  - E.g., require `blockCerts ≠ {}` with a notarization for some block in `slot`, or `HasNotarizationCert(pool, slot, b)` for some `b`.
- Strengthen store-time exclusion (defensive): update `CanStoreCertificate` to reject `SkipCert` when any notar-related certificate exists for the same slot, making Skip-vs-Block mutual exclusion explicit rather than emergent from thresholds. The spec already defines the intended exclusion as `SkipVsBlockCertExclusion` in `Certificates.tla:444` (approx.); enforcing it at store time would localize the property.
- Add a comment/assumption next to `GenerateCertificate` stating that `votes` must be Pool-sourced (as is done in `Certificates.tla` guards) to emphasize count-once semantics.
- Minor: In `MainProtocol.tla:229`, the prioritization prefers NotarizationCert among candidates. Consider preferring FastFinalizationCert first (if present), then NotarizationCert, to disseminate the strongest certificate earlier.

## Appendix: Definition/Operator Cross-References

- `GetVotesForSlot` — `specs/tla/alpenglow/VoteStorage.tla:142`.
- Guards — `specs/tla/alpenglow/Certificates.tla:134`, `:148`, `:165`, `:177`, `:190`.
- Constructors — `specs/tla/alpenglow/Certificates.tla:216`, `:223`, `:230`, `:243`, `:252`.
- Types/constants — `specs/tla/alpenglow/Messages.tla` (Vote, VoteType, CertificateType, NoBlock).
- Consumption sites — `specs/tla/alpenglow/MainProtocol.tla:229` (GenerateCertificateAction), `specs/tla/alpenglow/MainProtocol.tla:248`+ (FinalizeBlock).

