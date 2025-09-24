# Audit: CreateSkipCert

## 1. Code Under Audit

```
CreateSkipCert(votes, slot) ==
    [type |-> "SkipCert",
     slot |-> slot,
     blockHash |-> NoBlock,
     votes |-> {v \in votes : 
        v.type \in {"SkipVote", "SkipFallbackVote"} /\ v.slot = slot}]
```

## 2. Whitepaper Sections and References

- Table 5 (vote messages): `alpenglow-whitepaper.md:493`, `alpenglow-whitepaper.md:494`, `alpenglow-whitepaper.md:495`.
- Table 6 (certificate thresholds; Skip Cert row): `alpenglow-whitepaper.md:504`.
- Definition 12 (storing votes; count-once-per-slot semantics): `alpenglow-whitepaper.md:513`.
- Definition 13 (certificates: generate/store/broadcast when enough votes): `alpenglow-whitepaper.md:520`.

Related spec definitions for context:
- `NoBlock` constant and vote/certificate schemas: `specs/tla/alpenglow/Messages.tla:20`, `specs/tla/alpenglow/Messages.tla:56`, `specs/tla/alpenglow/Messages.tla:153`.
- Certificate types (includes `"SkipCert"`): `specs/tla/alpenglow/Messages.tla:141`.
- Validation rule enforcing `SkipCert.blockHash = NoBlock` and 60% threshold: `specs/tla/alpenglow/Certificates.tla:200`.
- Creation condition for Skip cert (threshold check): `specs/tla/alpenglow/Certificates.tla:125`.
- Use site in aggregator: `specs/tla/alpenglow/VoteStorage.tla:201`.

## 3. Reasoning and Mapping to Whitepaper

- Object shape and semantics
  - The constructed object’s `type` is `"SkipCert"`, matching Table 6’s certificate taxonomy (`Messages.tla` defines the set of certificate types).
  - `blockHash |-> NoBlock` explicitly encodes that skip certificates do not pertain to any block. This aligns with Table 5 where skip votes are per-slot and carry no block reference.
  - `slot |-> slot` associates the certificate with the slot being skipped.

- Aggregated votes included
  - The `votes` field filters the provided `votes` input to only those with `v.type ∈ {"SkipVote", "SkipFallbackVote"}` and `v.slot = slot`.
  - This matches Table 6 for Skip certificates: aggregated votes are “SkipVote or SkipFallbackVote,” and they are for the same slot.

- Threshold and validation context
  - This constructor does not itself check the 60% threshold; that is handled by `CanCreateSkipCert` and validated by `IsValidCertificate`.
  - `IsValidCertificate` requires for `"SkipCert"`: `blockHash = NoBlock` and `MeetsThreshold(StakeFromVotes(cert.votes), 60)`, ensuring the certificate is only considered valid if the 60% condition holds and block-less semantics are respected.
  - `StakeFromVotes` counts each validator at most once (by taking unique validators), implementing the Definition 12 “count-once-per-slot” principle for certificate aggregation.

- Integration point
  - The generator `GenerateCertificate` constructs `{CreateSkipCert(votes, slot)}` only when `CanCreateSkipCert(votes, slot)` holds, so in normal flows this constructor is used exactly under the whitepaper’s threshold condition (Definition 13).

## 4. Conclusion of the Audit

`CreateSkipCert` is faithful to the whitepaper abstraction for Skip Certificates:
- Aggregates exactly the allowed vote kinds (Skip and Skip-Fallback) for the specific slot.
- Encodes skip semantics via `blockHash = NoBlock` and correct `type` tag.
- Relies on surrounding guards/validators to enforce the 60% threshold with count-once stake aggregation, as per Table 6 and Definition 12.

No discrepancies were found between this constructor and the whitepaper’s description of Skip Certificates.

## 5. Open Questions or Concerns

- Redundancy of per-validator votes in the `votes` field:
  - A validator may have both a `SkipVote` and a `SkipFallbackVote` stored for the same slot (per Definition 12). The constructor includes both if present. This does not affect correctness because `StakeFromVotes` de-duplicates by validator for threshold checks, but it may bloat certificates or obscure the “count-once” intent.

- Mutual exclusion at the slot level:
  - This constructor (and its condition) does not by itself preclude coexisting skip and notarization certificates for the same slot. The whitepaper’s safety arguments ensure such coexistence cannot arise among correct nodes, but the spec relies on global dynamics rather than a local guard in this constructor. This is acceptable for an abstraction, yet a global invariant could make the intent explicit.

## 6. Suggestions for Improvement

- Use helper predicate for readability:
  - Replace `v.type ∈ {"SkipVote", "SkipFallbackVote"}` with `IsSkipVote(v)` (`specs/tla/alpenglow/Messages.tla:115`). Functionally identical, improves clarity and reduces duplication.

- Optionally canonicalize the `votes` component:
  - To reflect the “count once per slot” abstraction in the certificate payload itself (not only in validation), consider storing at most one vote per validator (e.g., the earliest available or prefer fallback if present). This is a modeling choice and not required for correctness, but can simplify reasoning and reduce certificate size.

- Document preconditions (typing):
  - Add a note or assumption that the parameter `votes ⊆ Vote` and `slot ∈ Slots`, mirroring `Messages.tla` types. The surrounding modules ensure this, but an explicit comment can help future readers.

