# Audit: CreateNotarizationCert

1. Code that you are auditing.

```
CreateNotarizationCert(votes, slot, blockHash) ==
    [type |-> "NotarizationCert",
     slot |-> slot,
     blockHash |-> blockHash,
     votes |-> {v \in votes : 
        v.type = "NotarVote" /\ v.slot = slot /\ v.blockHash = blockHash}]
```

2. The whitepaper section and references that the code represents.

- 2.4 Votes and Certificates (overview): `alpenglow-whitepaper.md:474`
- Table 5 (vote messages): `alpenglow-whitepaper.md:489`
- Table 6 (certificate types, thresholds): `alpenglow-whitepaper.md:499`
  - Notarization Cert: Aggregated votes = NotarVote; Condition Σ ≥ 60%
- Definition 12 (storing votes, multiplicity): `alpenglow-whitepaper.md:513`
- Definition 13 (certificate generation, broadcast, uniqueness): `alpenglow-whitepaper.md:520`, `alpenglow-whitepaper.md:532`
- Implication (fast → notarization → notar-fallback): `alpenglow-whitepaper.md:534`

3. Reasoning behind the code and what the whitepaper claims.

- Purpose: Construct a Notarization certificate object for a given `slot` and `blockHash` by aggregating first-round approval votes.
- Vote selection: Includes exactly those votes `v` where `v.type = "NotarVote"`, `v.slot = slot`, and `v.blockHash = blockHash`. This matches Table 6 which specifies Notarization Cert aggregates only NotarVote (not notar-fallback).
- Threshold handling: This constructor does not itself check thresholds; threshold checks are performed by `CanCreateNotarizationCert(votes, slot, blockHash)` (specs/tla/alpenglow/Certificates.tla:97) which applies Σ ≥ 60% using `StakeFromVotes` with unique validators, aligning with Definition 12’s “count-once-per-slot” rule. Validation also occurs via `IsValidCertificate` (specs/tla/alpenglow/Certificates.tla:190) which re-checks thresholds based on the certificate’s `votes` field.
- Count-once-per-slot: The pool’s storage rules enforce at most one initial vote (NotarVote or SkipVote) per validator per slot (specs/tla/alpenglow/VoteStorage.tla:138–140), and stake computation uses unique validators (specs/tla/alpenglow/Certificates.tla:25–41), ensuring no double-counting, as required by Definition 12.
- Certificate usage: Certificates are created by `GenerateCertificate` only when corresponding `CanCreate*` predicates hold (specs/tla/alpenglow/VoteStorage.tla:181–207). When a fast-finalization (80%) condition holds, the implementation constructs FastFinalization, Notarization, and Notar-Fallback certificates together (lines 185–190), matching the implication in the whitepaper (fast ⇒ notarization ⇒ notar-fallback).
- Certificate uniqueness: Pool storage enforces a single certificate per type and block/slot, and ties all notar-type certificates in a slot to the same block (specs/tla/alpenglow/VoteStorage.tla:109–122), matching Definition 13’s uniqueness clause.

4. Conclusion of the audit.

- The definition of `CreateNotarizationCert` is correct with respect to the whitepaper’s abstraction: it aggregates exactly the NotarVote messages for a specific `(slot, blockHash)` and leaves threshold enforcement to the `CanCreateNotarizationCert` predicate and `IsValidCertificate`.
- The surrounding specification enforces the “count-once-per-slot” stake rule and certificate uniqueness, and it ensures the fast-path implication by co-creating the appropriate certificates when Σ ≥ 80%.
- Overall, the constructor and its integration conform to Table 6, Definitions 12–13, and the fast-path implication statement.

5. Open questions or concerns.

- Explicit lemma linkage: The spec relies on usage discipline (calling the constructor after `CanCreateNotarizationCert`). It would be helpful to have a proven lemma that: `CanCreateNotarizationCert(votes, s, h) => IsValidCertificate(CreateNotarizationCert(votes, s, h))` to connect the creation predicate and the validator succinctly.
- Vote set size vs. minimality: The constructor includes all matching NotarVote for `(slot, blockHash)`. This is acceptable (Table 6 allows any subset meeting Σ), but if minimality matters for some analysis, a variant selecting a minimal sufficient subset could be considered (purely optional for the abstraction).
- Byzantine votes: The abstraction permits Byzantine votes within the `votes` set. This is consistent with the paper; thresholds count overall stake, and Assumption 1 (<20% Byzantine stake) protects safety. Nothing to change, but worth noting.

6. Suggestions for improvement.

- Add a proof obligation or theorem: introduce a property linking creation conditions and validation, e.g.,
  - `THEOREM CanCreateNotarizationCert(votes, s, h) => IsValidCertificate(CreateNotarizationCert(votes, s, h))`.
- Minor clarity improvements:
  - Consider renaming the constructor’s parameter `votes` to `allVotesForSlot` where it’s passed from the pool, to signal the expected input domain (non-semantic, readability only).
  - Add a short comment next to the constructor referencing Table 6 line numbers for fast lookup (e.g., `alpenglow-whitepaper.md:499`).

References in codebase for context

- Definition: `specs/tla/alpenglow/Certificates.tla:156`
- Creation predicate: `specs/tla/alpenglow/Certificates.tla:97`
- Certificate validation: `specs/tla/alpenglow/Certificates.tla:190`
- Usage (generation): `specs/tla/alpenglow/VoteStorage.tla:181`
- Pool uniqueness rules: `specs/tla/alpenglow/VoteStorage.tla:109`
- Vote/message types: `specs/tla/alpenglow/Messages.tla:143`

