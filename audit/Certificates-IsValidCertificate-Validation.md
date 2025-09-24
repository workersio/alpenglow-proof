# Audit: Certificates.tla — IsValidCertificate

1. Code that you are auditing

```
IsValidCertificate(cert) ==
    LET stake == StakeFromVotes(cert.votes)
    IN /\ cert.type \in CertificateType
       /\ cert.slot \in Slots
       /\ CASE cert.type = "FastFinalizationCert" -> 
               /\ cert.blockHash \in BlockHashes
               /\ MeetsThreshold(stake, 80)  \* 80% for fast path
          [] cert.type \in {"NotarizationCert", "NotarFallbackCert"} ->
               /\ cert.blockHash \in BlockHashes
               /\ MeetsThreshold(stake, 60)  \* 60% for notarization
          [] cert.type = "SkipCert" ->
               /\ cert.blockHash = NoBlock
               /\ MeetsThreshold(stake, 60)  \* 60% for skip
          [] cert.type = "FinalizationCert" ->
               /\ cert.blockHash = NoBlock
               /\ MeetsThreshold(stake, 60)  \* 60% for finalization
          [] OTHER -> FALSE
```

Location: `specs/tla/alpenglow/Certificates.tla:190`

2. The whitepaper section and references that the code represents

- Vote and certificate taxonomy: `alpenglow-whitepaper.md:478` (Definition 11; Tables 5–6)
- Certificate thresholds (Table 6): `alpenglow-whitepaper.md:507`
- “Count once per slot” storage rule (Definition 12): `alpenglow-whitepaper.md:513`
- Fast⇒Notarization implication (from Table 6 conditions): `alpenglow-whitepaper.md:534`
- High-level latency and dual-path framing (80%/60%): `alpenglow-whitepaper.md:16`, `:126`

Related TLA references used by this code:

- `StakeFromVotes` and `MeetsThreshold`: `specs/tla/alpenglow/Certificates.tla:64`, `:68`
- `CertificateType`, `Certificate`, `Vote`, `Slots`, `BlockHashes`, `NoBlock`: `specs/tla/alpenglow/Messages.tla:18`, `:55`, `:85`, `:141`, `:151`
- Call sites that rely on this predicate: `specs/tla/alpenglow/MainProtocol.tla:560`, `:878`

3. Reasoning: what the code does vs. what the paper claims

- Intended semantics from Table 6
  - Fast-Finalization Cert: aggregate NotarVote for a specific block (slot s, block b) reaching ≥80% stake.
  - Notarization Cert: aggregate NotarVote for (s, b) reaching ≥60% stake.
  - Notar-Fallback Cert: aggregate NotarVote or NotarFallbackVote for (s, b) reaching ≥60% stake.
  - Skip Cert: aggregate SkipVote or SkipFallbackVote for slot s reaching ≥60% stake.
  - Finalization Cert: aggregate FinalVote for slot s reaching ≥60% stake.
- “Count once per slot” (Def. 12) says each validator’s stake is counted at most once per slot when aggregating votes.

Behavior of the TLA code under audit:

- It checks that `cert.type` is known, `cert.slot ∈ Slots`, and that `cert.blockHash` is in `BlockHashes` for block-carrying certs or equals `NoBlock` for slot-only certs. These parts align with Tables 5–6 and the Messages typing.
- It computes `stake == StakeFromVotes(cert.votes)`, which sums stake over the unique set of validators present in `cert.votes` (via `UniqueValidators`). This enforces the “count once” aspect for the votes included in the certificate.
- It then applies a single threshold check per branch (80% for fast; 60% for all others).

Gaps/mismatches relative to the paper:

- Missing relevance filtering. The stake is computed over all votes in `cert.votes`, without constraining to the vote types and identifiers appropriate for the certificate:
  - For Notarization/Notar-Fallback/Fast-Finalization, the aggregated stake must come from votes for the same block `(slot = cert.slot ∧ blockHash = cert.blockHash)` and of the correct type(s). The current code does not enforce either the slot, block, or type constraint on the votes before counting stake.
  - For Skip and Finalization, the aggregated stake must come from votes for the same slot and of the correct type(s) where `blockHash = NoBlock`. The current code does not enforce the vote types nor `v.slot = cert.slot` on the contents.
- Consequence: A malformed or adversarial certificate could include a mixture of vote types and/or votes for different slots/blocks, and still pass the threshold if the union of validators across those irrelevant votes meets 60% (or 80%). This violates Table 6, which defines thresholds over the relevant vote family for a given (s,b) (or for slot s alone for skip/finalize).
- Cross-slot leakage. “Count once per slot” (Def. 12) is respected only within the set `cert.votes`, but since `IsValidCertificate` does not ensure all votes in `cert.votes` have `v.slot = cert.slot`, the counting could inadvertently include votes from other slots, which is outside the intended aggregation domain.
- Type-specific constraints missing. Table 6 distinguishes which vote families contribute to which certificate. The `IsValidCertificate` predicate should reflect these families; presently it does not ensure that:
  - Fast/Notar: only NotarVote are counted and for the same (s,b).
  - Notar-Fallback: NotarVote or NotarFallbackVote for the same (s,b).
  - Skip: SkipVote or SkipFallbackVote for the same s.
  - Finalization: FinalVote for the same s.

4. Conclusion of the audit

- The threshold constants and high-level shape (blockHash vs. NoBlock) match the whitepaper (Table 6). However, the `IsValidCertificate` predicate is too weak: it does not constrain the `cert.votes` to the correct vote family, slot, or block. As a result, it can accept ill-formed certificates that the whitepaper does not permit, undermining both safety and the intended semantics of Table 6 and Definition 12.
- Because `IsValidCertificate` is used to gate `DeliverCertificate` (`specs/tla/alpenglow/MainProtocol.tla:560`) and as a global message invariant (`:878`), this weakness can allow adversarial certificates into the Pool in the model, potentially invalidating properties that rely on well-formed aggregation.

5. Open questions or concerns

- Should `IsValidCertificate` also require `\A v ∈ cert.votes : v.slot = cert.slot` explicitly (I believe yes), making the count-once-per-slot property structurally enforced per certificate?
- For Notar-Fallback certificates, does the implementation intend to allow mixing `NotarVote` and `NotarFallbackVote` in the same aggregate (Table 6 says yes)? If so, modeling this via a union of vote families is correct; but we must still enforce `(v.blockHash = cert.blockHash ∧ v.slot = cert.slot)`.
- Should `IsValidCertificate` assert vote well-typedness (`\A v ∈ cert.votes : IsValidVote(v)`), or is `cert ∈ Certificate` at call sites deemed sufficient? Today, `DeliverCertificate` ensures `cert ∈ Certificate`, but the invariant `\A c ∈ messages : c ∈ Certificate ⇒ IsValidCertificate(c)` hints we might want a defensive check too.
- Finalization certificates in the paper conceptually finalize “the unique notarized block in slot s.” The TLA model handles this by emitting `BlockNotarized` events separately. Do we want `IsValidCertificate` to be purely structural (as proposed) and keep finalization-notarization linkage in higher-level invariants, or should the validity predicate encode a dependency on the existence of a notarization certificate for s? I suggest keeping it structural here.

6. Suggestions for improvement

- Enforce relevance filtering per certificate type when computing stake. Sketch:

```
IsValidCertificate(cert) ==
  LET RelevantVotes ==
        CASE cert.type = "FastFinalizationCert" ->
               { v \in cert.votes : v.type = "NotarVote" /\ v.slot = cert.slot /\ v.blockHash = cert.blockHash }
          [] cert.type = "NotarizationCert" ->
               { v \in cert.votes : v.type = "NotarVote" /\ v.slot = cert.slot /\ v.blockHash = cert.blockHash }
          [] cert.type = "NotarFallbackCert" ->
               { v \in cert.votes : v.type \in {"NotarVote","NotarFallbackVote"} /\ v.slot = cert.slot /\ v.blockHash = cert.blockHash }
          [] cert.type = "SkipCert" ->
               { v \in cert.votes : v.type \in {"SkipVote","SkipFallbackVote"} /\ v.slot = cert.slot /\ v.blockHash = NoBlock }
          [] cert.type = "FinalizationCert" ->
               { v \in cert.votes : v.type = "FinalVote" /\ v.slot = cert.slot /\ v.blockHash = NoBlock }
          [] OTHER -> {}
      stake == StakeFromVotes(RelevantVotes)
  IN /\ cert.type \in CertificateType
     /\ cert.slot \in Slots
     /\ CASE cert.type = "FastFinalizationCert" ->
             /\ cert.blockHash \in BlockHashes
             /\ MeetsThreshold(stake, 80)
        [] cert.type \in {"NotarizationCert","NotarFallbackCert"} ->
             /\ cert.blockHash \in BlockHashes
             /\ MeetsThreshold(stake, 60)
        [] cert.type = "SkipCert" ->
             /\ cert.blockHash = NoBlock
             /\ MeetsThreshold(stake, 60)
        [] cert.type = "FinalizationCert" ->
             /\ cert.blockHash = NoBlock
             /\ MeetsThreshold(stake, 60)
        [] OTHER -> FALSE
```

- Optionally add a defensive typing check: `\A v ∈ cert.votes : IsValidVote(v)`.
- Consider adding an invariant to the model capturing certificate well-formedness, e.g., `CertificateWellFormed(cert)` defined by the relevance filters above, and assert `\A s, c ∈ pool.certificates[s] : CertificateWellFormed(c)`.
- Document in `Certificates.tla` that `IsValidCertificate` implements Table 6 over per-(slot, block) vote families and enforces the count-once-per-slot rule by using `UniqueValidators`.

Overall, tightening `IsValidCertificate` as shown above aligns the spec with the whitepaper’s Table 6 and Definition 12 and prevents acceptance of malformed certificates that mix unrelated votes.

