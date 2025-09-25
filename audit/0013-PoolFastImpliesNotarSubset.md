**Code Under Audit**

```
PoolFastImpliesNotarSubset(pool, s, h) ==
    LET certs == pool.certificates[s]
    IN \A fastCert \in certs :
        (fastCert.type = "FastFinalizationCert" /\ fastCert.blockHash = h)
            => \E notarCert \in certs :
                FastFinalizationImpliesNotarization(fastCert, notarCert)
```

Related definitions and structure for context:
- `specs/tla/alpenglow/VoteStorage.tla:349` (this operator)
- `specs/tla/alpenglow/Certificates.tla:332` `FastFinalizationImpliesNotarization`
- `specs/tla/alpenglow/VoteStorage.tla:19` `PoolState` structure (`certificates` field)
- `specs/tla/alpenglow/VoteStorage.tla:160` `GenerateCertificate` (fast ⇒ also creates notar+fallback)

**Whitepaper References**

- Table 6 thresholds: `alpenglow-whitepaper.md:498` (Fast 80%, Notar 60%)
- Pool definitions (Defs. 12–13): `alpenglow-whitepaper.md:513`, `alpenglow-whitepaper.md:520`
- Explicit note: “if a correct node generated the Fast-Finalization Certificate, it also generated the Notarization Certificate, which in turn implies it generated the Notar-Fallback Certificate.” `alpenglow-whitepaper.md:534`
- Finalization (Def. 14): `alpenglow-whitepaper.md:536`
- Fallback events and safety context (Defs. 15–16): `alpenglow-whitepaper.md:542`, `alpenglow-whitepaper.md:556`

**Reasoning**

- Intent of operator: Within a single node’s Pool (for slot `s`), a Fast-Finalization certificate for block `h` should imply that there exists a corresponding Notarization certificate for the same block, with notarization votes being a subset of fast-finalization votes. This matches the whitepaper’s Table 6 and the page 21 note (fast ⇒ notar ⇒ fallback).
- Mechanically, the operator ranges over certificates stored in `pool.certificates[s]`. For any `fastCert` with `type = "FastFinalizationCert"` and `blockHash = h`, it requires existence of some `notarCert` with `FastFinalizationImpliesNotarization(fastCert, notarCert)`.
- The referenced predicate `FastFinalizationImpliesNotarization` is defined as:
  - `specs/tla/alpenglow/Certificates.tla:332`:
    - `(fastCert.type = "FastFinalizationCert" /\ notarCert.type = "NotarizationCert" /\ slots equal /\ hashes equal) => notarCert.votes ⊆ fastCert.votes`.
  - Semantics: it is an implication whose antecedent requires the notarization-cert typing and same slot/hash, and whose consequent enforces vote-subset inclusion.
- Generation logic supports the claim: `GenerateCertificate` constructs all three certificates when the 80% fast path holds (`CreateFastFinalizationCert`, `CreateNotarizationCert`, `CreateNotarFallbackCert`), and for 60% also creates notarization+fallback. See `specs/tla/alpenglow/VoteStorage.tla:176–205`.
- Pool storage enforces cross-type same-block coherence for notar-related certificates in a slot (cannot mix notar types for different blocks): `specs/tla/alpenglow/VoteStorage.tla:84–109`.

**Audit Conclusion**

- The specification as written does not actually enforce the intended “existence of a Notarization certificate when a Fast-Finalization certificate exists” due to a vacuity issue:
  - In `PoolFastImpliesNotarSubset`, the existential quantifier chooses `notarCert ∈ certs` with the property `FastFinalizationImpliesNotarization(fastCert, notarCert)`.
  - But `FastFinalizationImpliesNotarization` itself is an implication: `(type/slot/hash constraints) => (subset)`. If a non-notarization certificate is picked (e.g., `SkipCert`), the antecedent is false and the implication is trivially true. Hence the existential is satisfied even when no Notarization certificate is present. This makes the operator too weak and potentially always true once there is any certificate in the set.
- The same vacuity pattern appears in `specs/tla/alpenglow/Certificates.tla:418–427` (`FastPathImplication`), which uses `∃ notarCert : FastFinalizationImpliesNotarization(fastCert, notarCert)` guarded only by `fastCert.type = "FastFinalizationCert" => ...`. Thus, neither place currently proves existence of an actual `NotarizationCert` in the set.
- The whitepaper’s statement (page 21 note) requires existence: a node that generated the Fast-Finalization certificate also generated the Notarization certificate. The TLA+ must reflect that existence explicitly when speaking about a single Pool’s certificate set.
- Positives:
  - `GenerateCertificate` does create both certificates when the fast path holds, aligning with Table 6 (80% implies 60%).
  - Pool storage (`CanStoreCertificate`) keeps notar-related types on the same block hash within a slot, preventing cross-type equivocation.

**Open Questions / Concerns**

- Vacuity in existence: As described, `PoolFastImpliesNotarSubset` and `FastPathImplication` can be satisfied without any actual `NotarizationCert` in the set. This weakens the spec relative to the whitepaper’s requirement.
- Model checking coverage: The provided `specs/tla/alpenglow/MC.cfg` does not list either `PoolFastImpliesNotarSubset` or the `FastPathImplication` as invariants, so TLC will not catch issues in these implications. Consider adding a non-vacuous invariant.
- Timing vs. existence: The comment in `Certificates.tla` notes that different nodes may include different concrete vote sets due to timing. That is fine, but the existence claim is per-node (per-Pool) once a fast cert is generated. The spec should assert that per-Pool existence, not merely a conditional implication that can be vacuously true.

**Suggestions for Improvement**

- Strengthen the existential to require the certificate type and matching block explicitly in the operator being audited:
  - Replace the body with, e.g.:
    - `∃ notarCert ∈ certs : /\ notarCert.type = "NotarizationCert" /\ notarCert.blockHash = h /\ notarCert.slot = fastCert.slot /\ notarCert.votes ⊆ fastCert.votes`.
  - Keep or drop the call to `FastFinalizationImpliesNotarization` as preferred; if kept, remove the implication from that predicate (see next bullet) or additionally assert the typing constraints alongside it.
- Make `FastFinalizationImpliesNotarization` a conjunctive relation instead of an implication, so it encodes the intended structural relation directly and avoids vacuity:
  - Proposed form: `/\ fastCert.type = "FastFinalizationCert" /\ notarCert.type = "NotarizationCert" /\ fastCert.slot = notarCert.slot /\ fastCert.blockHash = notarCert.blockHash /\ notarCert.votes ⊆ fastCert.votes`.
  - Then, `∃ notarCert : FastFinalizationImpliesNotarization(...)` correctly asserts existence of a notarization certificate with subset votes.
- Mirror this fix in `Certificates.tla:418–427` (`FastPathImplication`) to avoid the same issue.
- Add a TLC invariant to `MC.cfg` that checks the strengthened property per slot per pool, e.g.:
  - `\A s \in Slots : FastPathImplication(pool.certificates[s])` (with the non-vacuous definition), or a specialized pool-scoped invariant for the current state.
- Optional: tie existence to the generation rule for added clarity (cross-reference `GenerateCertificate`), or add a lemma connecting `HasFastFinalizationCert(pool, s, h)` to `HasNotarizationCert(pool, s, h)` with the subset condition.

**Conclusion**

The audited operator’s intent aligns with the whitepaper’s fast ⇒ notar claim, but its current formulation is logically too weak due to a vacuous existential over an implication. Strengthening the existential (or redefining the helper predicate without `=>`) will bring the TLA+ spec in line with the whitepaper’s requirement and make the property suitable as a meaningful invariant.

