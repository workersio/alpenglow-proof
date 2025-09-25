# Audit: CertificateUniqueness(pool)

## 1. Code Under Audit

Path: `specs/tla/alpenglow/VoteStorage.tla:336`

```
CertificateUniqueness(pool) ==
    \A s \in Slots :
        \A c1, c2 \in pool.certificates[s] :
            (c1.type = c2.type /\ c1.slot = c2.slot) =>
            (c1.type \in {"SkipCert", "FinalizationCert"} \/ c1.blockHash = c2.blockHash)
```

Context:
- Module extends `Messages`, `Blocks`, `Certificates` (see `specs/tla/alpenglow/VoteStorage.tla:11`).
- Pool certificates are stored by slot: `certificates: [Slots -> SUBSET Certificate]` (see `specs/tla/alpenglow/VoteStorage.tla:24`).
- Certificate structure and types are defined in `Messages` (see `specs/tla/alpenglow/Messages.tla:116` and `specs/tla/alpenglow/Messages.tla:100`).

External references used by this definition:
- `Slots` (constant): `specs/tla/alpenglow/Messages.tla:16`–`specs/tla/alpenglow/Messages.tla:28`.
- `Certificate` record fields: `type`, `slot`, `blockHash` (shape in `specs/tla/alpenglow/Messages.tla:116`–`specs/tla/alpenglow/Messages.tla:121`).
- Certificate type literals: `"SkipCert"`, `"FinalizationCert"`, and the notarization-family types from Table 6 (see below).

Related storage guard for context:
- `CanStoreCertificate` implements per-slot, per-type uniqueness and cross-type block consistency for notarization-family certs (see `specs/tla/alpenglow/VoteStorage.tla:109`–`specs/tla/alpenglow/VoteStorage.tla:124`).

## 2. Whitepaper Sections and References

- Table 6 (certificate types, thresholds): `alpenglow-whitepaper.md:507`.
- Definition 13 (certificates): `alpenglow-whitepaper.md:520`.
- Uniqueness statement (Definition 13): “A single (received or constructed) certificate of each type corresponding to the given block/slot is stored in Pool.” `alpenglow-whitepaper.md:532`.

## 3. Reasoning: Code vs. Whitepaper Claims

What the whitepaper requires (source of truth):
- Definition 13 states a storage uniqueness rule: for each slot, Pool stores exactly one certificate of each type that corresponds to the given block/slot. Concretely:
  - For block-scoped types (FastFinalization, Notarization, NotarFallback), per slot there is at most one certificate of a given type for a given block.
  - For slot-scoped types (Skip, Finalization), per slot there is at most one certificate of that type (no block hash).

What the invariant enforces:
- The predicate ranges over `pool.certificates[s]` and says: for any two certificates in that slot with the same `type` and `slot`, either the type is `SkipCert` or `FinalizationCert` (where `blockHash` is irrelevant), or else their `blockHash` must be equal.

Consequences of the current predicate:
- Prevents within-slot, same-type certificates from pointing to different blocks. This bans cross-block conflicts for a given type and slot (good, and consistent with safety intent).
- Does not enforce “single”/cardinality. The set could contain two distinct certificates of the same `type`, same `slot`, and same `blockHash` but with different `votes` sets; this invariant permits that. This is weaker than Definition 13’s “a single certificate … is stored”.
- For `SkipCert` and `FinalizationCert`, the right-hand disjunction makes the constraint vacuous for those types. The invariant does not prohibit having two skip or two finalization certificates in the same slot, again weaker than Definition 13.
- The antecedent uses `c1.slot = c2.slot` even though membership is already restricted to `pool.certificates[s]`. If a malformed certificate with mismatched `slot` were present in the slot’s bucket, this predicate may not trigger for some pairs; there is no separate invariant that all `c ∈ pool.certificates[s]` satisfy `c.slot = s`.

Where the stronger behavior comes from today:
- The operational guard `CanStoreCertificate` enforces a stronger property during insertion:
  - At most one `SkipCert` and one `FinalizationCert` per slot (`~∃ c : c.type = cert.type`).
  - For notarization-family types, at most one per `(type, blockHash)` and cross-type block consistency within a slot (all notarization-family certs share the same `blockHash`). See `specs/tla/alpenglow/VoteStorage.tla:115`–`specs/tla/alpenglow/VoteStorage.tla:123`.
- MainProtocol wires this invariant as `PoolCertificateUniqueness` (`specs/tla/alpenglow/MainProtocol.tla:899`), but it does not add a cardinality check, nor a slot-bucket consistency invariant.

Verdict on alignment:
- The audited invariant partially captures uniqueness (no cross-block disagreements for a given type/slot), but it does not realize the whitepaper’s “single certificate of each type” requirement as an invariant. It relies on the store-time guard to ensure single-ness. For a critical protocol, it is preferable to reflect Definition 13 directly as a state invariant as well.

## 4. Conclusion of the Audit

- Correctness: The property is directionally correct for preventing conflicting block hashes among same-type certificates in a slot, but it is strictly weaker than the whitepaper’s Definition 13 (single certificate per type per block/slot). As written, the invariant allows multiple same-type certificates for the same `(slot, blockHash)` (e.g., with different `votes` sets), and allows duplicates for `SkipCert` and `FinalizationCert`.
- Dependence on operational guards: The stronger uniqueness is currently enforced by `CanStoreCertificate` at insertion time. While acceptable, relying solely on insertion guards reduces robustness of model checking if future code paths mutate `pool.certificates` without those guards. The invariant should stand on its own and encode the cardinality constraints explicitly.
- Whitepaper fidelity: Partial. The invariant should be strengthened to fully represent Definition 13.

## 5. Open Questions or Concerns

- Should Pool store all three notarization-family certificates (fast/notar/fallback) when all are constructible, or only the strongest/most advanced? The whitepaper states the implication chain (fast ⇒ notar ⇒ fallback) but does not mandate storing all three simultaneously. The current model stores all (consistent, but worth confirming design intent).
- Slot-bucket coherence: There is no invariant that `∀ s, ∀ c ∈ pool.certificates[s] : c.slot = s`. Storage code respects this, but a dedicated invariant would catch accidental mis-bucketing.
- Global validity checks: MainProtocol asserts `SkipVsBlockCertExclusion` over Pool sets (`specs/tla/alpenglow/MainProtocol.tla:870`). It does not assert `AllCertificatesValid` or `NoConflictingCertificates` from `Certificates.tla`. Adding them would strengthen safety checks.

## 6. Suggestions for Improvement

Strengthen the invariant to match Definition 13 explicitly. For example:

```
NotarTypes == {"FastFinalizationCert", "NotarizationCert", "NotarFallbackCert"}

CertificateUniqueness_Strict(pool) ==
  \A s \in Slots :
    /\ \A t \in {"SkipCert", "FinalizationCert"} :
         Cardinality({c \in pool.certificates[s] : c.type = t}) <= 1
    /\ \A t \in NotarTypes :
         \A b \in BlockHashes :
           Cardinality({c \in pool.certificates[s] : /\ c.type = t /\ c.blockHash = b}) <= 1
    /\ LET notarBs == {c.blockHash : c \in pool.certificates[s] /\ c.type \in NotarTypes}
       IN Cardinality(notarBs) <= 1
```

Add slot-bucket coherence and structural validity as invariants:

```
BucketSlotConsistency(pool) ==
  \A s \in Slots : \A c \in pool.certificates[s] : c.slot = s

PoolCertificatesWellFormed(pool) ==
  \A s \in Slots : AllCertificatesValid(pool.certificates[s])
```

Optionally, replace the audited predicate with equality-based uniqueness, which is even stronger and easiest to read:

```
CertificateUniqueness_Eq(pool) ==
  \A s \in Slots :
    \A c1, c2 \in pool.certificates[s] :
      (c1.type = c2.type) => c1 = c2
```

This forbids multiple certificates of the same type per slot altogether, and in particular disallows two notarization certificates for different blocks or with different vote sets. If the intent is “one per type per slot,” this directly matches the whitepaper sentence at `alpenglow-whitepaper.md:532`. If you intend “one per (type, block)” for notarization-family types, keep the `_Strict` variant above instead.

Finally, consider asserting these invariants in `MainProtocol` alongside the existing ones (file: `specs/tla/alpenglow/MainProtocol.tla:899`), to ensure MC checks them across the whole protocol.

