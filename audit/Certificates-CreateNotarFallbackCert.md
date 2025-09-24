# Audit: `CreateNotarFallbackCert`

## 1. Code Under Audit

```tla
CreateNotarFallbackCert(votes, slot, blockHash) ==
    [type |-> "NotarFallbackCert",
     slot |-> slot,
     blockHash |-> blockHash,
     votes |-> {v \in votes : 
        v.type \in {"NotarVote", "NotarFallbackVote"} /\ 
        v.slot = slot /\ v.blockHash = blockHash}]
```

Reference in repo: `specs/tla/alpenglow/Certificates.tla:163`.

## 2. Whitepaper Mapping

- Table 5 (vote messages):
  - Notarization vote `NotarVote(s, hash(b))`: `alpenglow-whitepaper.md:491`.
  - Notar‑Fallback vote `NotarFallbackVote(s, hash(b))`: `alpenglow-whitepaper.md:492`.
- Table 6 (certificate messages): Notar‑Fallback Certificate aggregates NotarVote or NotarFallbackVote with Σ ≥ 60%: `alpenglow-whitepaper.md:503`.
- Pool storage (count‑once semantics): Definition 12 — store first notar/skip, up to 3 notar‑fallback, etc.: `alpenglow-whitepaper.md:513`.
- Certificate generation and uniqueness: Definition 13 (generate when enough votes; single certificate per type for slot/block): `alpenglow-whitepaper.md:522`, `alpenglow-whitepaper.md:532`.
- Implication chain: 80% ⇒ Notarization (60%) ⇒ Notar‑Fallback (60%): `alpenglow-whitepaper.md:534`.
- ParentReady uses notarization or notar‑fallback cert for parent: `alpenglow-whitepaper.md:546`.
- SafeToNotar requires notar‑fallback cert for parent (non‑first slot): `alpenglow-whitepaper.md:569`.
- Algorithm 1/2 broadcast of `NotarFallbackVote`: `alpenglow-whitepaper.md:659`.

Related TLA+ definitions this operator composes with:
- Vote/certificate types and shapes: `specs/tla/alpenglow/Messages.tla:43`, `specs/tla/alpenglow/Messages.tla:52`, `specs/tla/alpenglow/Messages.tla:143`.
- Creation condition for this certificate: `CanCreateNotarFallbackCert`: `specs/tla/alpenglow/Certificates.tla:111`.
- Stake aggregation obeying count‑once: `UniqueValidators`, `StakeFromVotes`, `MeetsThreshold`: `specs/tla/alpenglow/Certificates.tla:60`, `specs/tla/alpenglow/Certificates.tla:64`, `specs/tla/alpenglow/Certificates.tla:68`.
- Validation: `IsValidCertificate` enforces 60% for NotarFallbackCert: `specs/tla/alpenglow/Certificates.tla:186`.
- Pool generation path: `GenerateCertificate` calls this creator after checking the condition: `specs/tla/alpenglow/VoteStorage.tla:189`, `specs/tla/alpenglow/VoteStorage.tla:196`.
- Pool uniqueness across notarization‑type certs in a slot: `specs/tla/alpenglow/VoteStorage.tla:109`.
- Downstream usage: queries and events
  - `HasNotarFallbackCert`: `specs/tla/alpenglow/VoteStorage.tla:220`.
  - `ShouldEmitParentReady` uses Notarization OR Notar‑Fallback: `specs/tla/alpenglow/VoteStorage.tla:260`.
  - `CanEmitSafeToNotar` requires parent’s Notar‑Fallback (non‑first slot): `specs/tla/alpenglow/VoteStorage.tla:287`.

## 3. Reasoning vs Whitepaper

- Aggregation set matches Table 6. The `votes` field is precisely the subset for the target `(slot, blockHash)` with types in {NotarVote, NotarFallbackVote}, exactly mirroring “NotarVote or NotarFallbackVote” from Table 6 (`alpenglow-whitepaper.md:503`).
- Threshold semantics are delegated to conditions/validation. This constructor does not itself check Σ ≥ 60%. Instead:
  - `CanCreateNotarFallbackCert` builds the same `relevantVotes` set and checks `MeetsThreshold(..., 60)` (`specs/tla/alpenglow/Certificates.tla:111`).
  - `IsValidCertificate` independently enforces `60%` for any constructed NotarFallbackCert (`specs/tla/alpenglow/Certificates.tla:186`).
  - `GenerateCertificate` only calls this constructor when the condition holds (`specs/tla/alpenglow/VoteStorage.tla:196`).
  This separation matches TLA idioms: creators are pure; guards enforce conditions elsewhere, preserving abstraction.
- Count‑once‑per‑slot is preserved. Although a validator may have both NotarVote and up to three NotarFallbackVotes in Pool (Definition 12, `alpenglow-whitepaper.md:513`), stake is aggregated via `UniqueValidators` in `StakeFromVotes`, preventing double counting across the union of initial and fallback votes (`specs/tla/alpenglow/Certificates.tla:64`).
- Integration with events aligns with the paper:
  - `ParentReady(s, hash(b))` triggers when Pool holds a notarization OR notar‑fallback certificate for some previous block and all intermediate skip certs exist (`alpenglow-whitepaper.md:546`). Implemented in `ShouldEmitParentReady` (`specs/tla/alpenglow/VoteStorage.tla:260`).
  - `SafeToNotar` (non‑first slot) requires the parent’s Notar‑Fallback certificate (`alpenglow-whitepaper.md:569`), implemented by `CanEmitSafeToNotar` (`specs/tla/alpenglow/VoteStorage.tla:287`).
- Candidate blocks for certificate generation come from NotarVote presence. `GenerateCertificate` enumerates `notarBlocks` using only `NotarVote` (`specs/tla/alpenglow/VoteStorage.tla:199`). This is consistent with Algorithm 2/Def.16: notar‑fallback voting is only enabled after observing sufficient notarization stake and thus presupposes some NotarVote activity (`alpenglow-whitepaper.md:565`–`alpenglow-whitepaper.md:569`). Therefore, NotarFallbackCerts won’t arise for blocks with zero NotarVotes, which matches the protocol’s intent.
- Uniqueness across notarization‑type certificates is enforced. Pool forbids storing two notarization‑type certs (Fast/Notarization/Notar‑Fallback) for different blocks in the same slot (`specs/tla/alpenglow/VoteStorage.tla:109`), aligning with Definition 13’s uniqueness clause (`alpenglow-whitepaper.md:532`).

## 4. Conclusion of the Audit

- The constructor `CreateNotarFallbackCert` is faithful to the whitepaper:
  - It aggregates exactly the allowed vote types tied to the same `(slot, block)`.
  - Threshold and count‑once semantics are correctly handled by the surrounding predicates (`CanCreateNotarFallbackCert`, `IsValidCertificate`) and stake helpers.
  - Its usage in Pool/certificate generation and in downstream events matches Definitions 13, 15, and 16.
- No mismatches against the whitepaper abstractions were found for this operator.

Result: Correct and complete at the intended abstraction level.

## 5. Open Questions / Concerns

- Constructor precondition not explicit. The creator can be called on any `votes` set; correctness relies on callers checking `CanCreateNotarFallbackCert` first or validating via `IsValidCertificate`. This is conventional in TLA+, but a short comment/lemma stating the intended precondition would reduce misuse.
- Centralization of thresholds. Literal `60` appears across multiple definitions. A named constant (e.g., `DefaultThreshold == 60`) would minimize drift if the spec evolves.
- Block enumeration driven by NotarVote only. While consistent with Def.16, it is an implicit assumption that notar‑fallback votes never appear without at least one NotarVote for that block in the slot. This follows from the SafeToNotar preconditions in the paper, but a brief comment in `GenerateCertificate` could document this assumption.

## 6. Suggestions for Improvement

- Add a lemma documenting constructor validity under its guard:
  - `\A votes, s, b : CanCreateNotarFallbackCert(votes, s, b) => IsValidCertificate(CreateNotarFallbackCert(votes, s, b)).`
- Optionally add a readability lemma mirroring the paper’s implication chain:
  - `\A votes, s, b : CanCreateNotarizationCert(votes, s, b) => CanCreateNotarFallbackCert(votes, s, b).`
- Introduce named constants for thresholds (e.g., `FastThreshold == 80`, `DefaultThreshold == 60`) and reference them in all predicates and validators.
- Add a brief comment on `CreateNotarFallbackCert` noting that `votes` are Pool‑sourced (Definition 12) so that count‑once and multiplicity semantics hold in practice.

