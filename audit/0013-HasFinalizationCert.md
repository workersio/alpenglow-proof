1. Code Under Audit

Path: specs/tla/alpenglow/VoteStorage.tla:244

```
HasFinalizationCert(pool, slot) ==
    \E cert \in pool.certificates[slot] :
        cert.type = "FinalizationCert"
```

2. Whitepaper Mapping

- Definition 14 (finalization): alpenglow-whitepaper.md:538
  - “If a finalization certificate on slot s is in Pool, the unique notarized block in slot s is finalized (slow-finalized).”
- Definition 14 (fast finalization): alpenglow-whitepaper.md:539
- Definition 13 (certificate storage semantics; uniqueness per type/slot): alpenglow-whitepaper.md:532
- Operational note (joining/rebooting nodes require slow-finalization pair): alpenglow-whitepaper.md:1229

3. Reasoning and Spec Context

- Purpose and abstraction
  - The predicate abstracts the slow-finalization condition in Def.14 to a Pool-level check: “does Pool contain a FinalizationCert for this slot?”
  - FinalizationCert is slot-scoped (blockHash = NoBlock by construction), so the block identity must be recovered via the unique notarized block for the slot.

- Related definitions and guarantees in the spec
  - Certificate construction and validity
    - CanCreateFinalizationCert: specs/tla/alpenglow/Certificates.tla:190 enforces ≥60% FinalVote stake.
    - CreateFinalizationCert: specs/tla/alpenglow/Certificates.tla:252 sets blockHash = NoBlock (slot-scoped slow path).
    - IsValidCertificate: specs/tla/alpenglow/Certificates.tla:268 checks type, slot, and threshold (DefaultThreshold = 60%).
  - Pool storage rules (Definition 13 formalized)
    - CanStoreCertificate/StoreCertificate: specs/tla/alpenglow/VoteStorage.tla ensure only one FinalizationCert per slot and that stored certs are valid.
    - CertificateUniqueness (invariant): specs/tla/alpenglow/VoteStorage.tla:331 forces per-type uniqueness within a slot.
  - Slow-finalization use site
    - FinalizeBlock combines slot-level finalization with block identity via notarization: specs/tla/alpenglow/MainProtocol.tla:255
      - Guard: HasFastFinalizationCert(pool, s, h) OR (HasNotarizationCert(pool, s, h) AND HasFinalizationCert(pool, s)).
      - This directly mirrors Def.14: fast path finalizes block h; slow path requires FinalizationCert(s) plus the notarized block h in slot s.

- External references and their roles
  - Certificate types and records: specs/tla/alpenglow/Messages.tla define CertificateType contains "FinalizationCert" and Certificate structure.
  - Pool state layout: specs/tla/alpenglow/VoteStorage.tla defines pool.certificates as [Slots -> SUBSET Certificate].
  - Invariants around certificates (supporting assumptions for this predicate):
    - No conflicting certificates per slot/type (CertificateUniqueness).
    - Skip-vs-block cert exclusion (SkipVsBlockCertExclusion) in specs/tla/alpenglow/Certificates.tla ensures mutual exclusivity.

4. Conclusion

- Correctness w.r.t. whitepaper
  - The predicate precisely captures the slot-scoped condition “a finalization certificate on slot s is in Pool” from Definition 14.
  - Its use in FinalizeBlock together with HasNotarizationCert(pool, s, h) implements “the unique notarized block in slot s is finalized,” matching the slow-finalization rule.
  - Pool’s storage and validity checks ensure that matching certificates are well-formed and unique, so existence is a sound abstraction for the slow-path trigger.

5. Open Questions / Concerns

- Observation vs. derivation timing
  - A node may receive a FinalizationCert(s) before it receives the corresponding NotarizationCert(s, h). FinalizeBlock therefore waits for both, which is conservative and consistent with the operational note at alpenglow-whitepaper.md:1229. This is fine, but it means slow-finalization can be delayed by message ordering.

- Explicit invariant linking FinalizationCert to notarization presence
  - The model enforces how FinalVotes are emitted (after BlockNotarized) and how FinalizationCert is constructed, but there is no explicit invariant stating “FinalizationCert(s) in Pool implies there exists NotarizationCert(s, h) in the same Pool” (as opposed to relying on network eventuality). The finalize guard compensates for this; adding the invariant would strengthen the spec.

6. Suggestions for Improvement

- Add a helper predicate to encode the slow-finalization guard directly
  - Example: in VoteStorage.tla
    - CanFinalizeSlow(pool, s, h) == HasFinalizationCert(pool, s) /\ HasNotarizationCert(pool, s, h)
  - Then FinalizeBlock can reference a single guard for readability.

- Strengthen invariants to reflect Def.14 pairing
  - Add: FinalizationImpliesNotarizationPresent(pool, s) == (\E c \in pool.certificates[s]: c.type = "FinalizationCert") => (\E n \in pool.certificates[s]: n.type = "NotarizationCert")
  - Optionally: UniqueNotarization already covers uniqueness of the notarized block; this new invariant would ensure presence when FinalizationCert is present.

- Consider adding AllCertificatesValid as a model invariant
  - specs/tla/alpenglow/Certificates.tla provides AllCertificatesValid; including it in the TLC model (MC.cfg) would assert that only valid certificates are ever stored.

- Clarify intent with a brief comment near HasFinalizationCert
  - Note that it is a slot-level check and is intentionally combined with HasNotarizationCert to choose the finalized block per Def.14.

