# Audit: PoolTypeOK (Pool typing invariant)

## 1. Code Audited

```
PoolTypeOK(pool) ==
    /\ DOMAIN pool.votes = Slots
    /\ \A s \in Slots : DOMAIN pool.votes[s] = Validators
    /\ \A s \in Slots : pool.certificates[s] \subseteq Certificate
```

Reference location: `specs/tla/alpenglow/VoteStorage.tla:321`

Related type declarations for Pool: `specs/tla/alpenglow/VoteStorage.tla:24`, `specs/tla/alpenglow/VoteStorage.tla:31`

Constants used by the code:
- `Slots`: `specs/tla/alpenglow/Messages.tla:18`
- `Validators`: `specs/tla/alpenglow/Messages.tla:17`
- `Certificate`: `specs/tla/alpenglow/Messages.tla:151`

Where this invariant is consumed: `specs/tla/alpenglow/VotorCore.tla:329` (in `ValidatorStateOK`)

## 2. Whitepaper Sections and References

- Pool overview: `alpenglow-whitepaper.md:509` (Section 2.5 Pool)
- Pool definition — “memorizes all votes and certificates for every slot”: `alpenglow-whitepaper.md:511`
- Definition 12 (storing votes per slot and per node): `alpenglow-whitepaper.md:513`
- Definition 13 (certificates: generate, store, broadcast): `alpenglow-whitepaper.md:520`
- Single certificate per type per block/slot: `alpenglow-whitepaper.md:532`
- Votes and Certificates section (context): `alpenglow-whitepaper.md:474`

## 3. Reasoning and Alignment

- Intent of the code
  - `PoolTypeOK` asserts the Pool’s per-slot maps are total and correctly typed:
    - Votes map: `DOMAIN pool.votes = Slots` and, for each slot, `DOMAIN pool.votes[s] = Validators`.
    - Certificates set per slot: `pool.certificates[s] \subseteq Certificate`.

- Mapping to whitepaper abstractions
  - Section 2.5 states Pool “memorizes all votes and certificates for every slot” (per-slot totality). The invariant’s domain checks enforce per-slot totality for `votes`, and per-slot availability for `certificates`.
  - Definition 12 requires Pool to store votes “for every slot and every node.” The nested domain equalities (`Slots` outer, `Validators` inner) directly encode this shape, independent of the multiplicity caps (which are enforced separately by `CanStoreVote` and `MultiplicityRulesRespected`). See `specs/tla/alpenglow/VoteStorage.tla:54` and `specs/tla/alpenglow/VoteStorage.tla:326`.
  - Definition 13 requires Pool to store certificates per slot. Constraining `pool.certificates[s]` to `\subseteq Certificate` ensures all stored objects are certificate-shaped, matching Table 6’s family. Certificate creation and storage also enforce validity: `StoreCertificate` calls `IsValidCertificate` before insertion (`specs/tla/alpenglow/VoteStorage.tla:115`).

- External references and typing closure
  - `Slots`, `Validators`, and `Certificate` are declared in `Messages.tla` (see the file references above). `PoolState` is declared to have exactly the same structure: `votes: [Slots -> [Validators -> SUBSET Vote]]` and `certificates: [Slots -> SUBSET Certificate]` (`specs/tla/alpenglow/VoteStorage.tla:24`). `InitPool` constructs values with those domains (`:31`).
  - The model’s message delivery actions only admit well-formed votes and certificates (`IsValidVote`, `IsValidCertificate`) before storage (`specs/tla/alpenglow/MainProtocol.tla:520`, `:560`), which keeps pool contents type-correct operationally.

## 4. Conclusion

- The `PoolTypeOK` invariant is directionally correct and aligns with the whitepaper’s Section 2.5 abstractions:
  - It enforces per-slot totality for vote storage across all validators (Def. 12’s “for every slot and every node”).
  - It ensures per-slot certificate sets contain only certificate-shaped elements (Def. 13 / Table 6).
- Together with `PoolState`’s type, `InitPool`, and the guarded store operations, the code maintains the intended Pool structure described in the whitepaper.

## 5. Open Questions / Concerns

- Missing equality on certificate domain
  - `PoolTypeOK` does not assert `DOMAIN pool.certificates = Slots`. While `\A s \in Slots : pool.certificates[s] \subseteq Certificate` implies totality over `Slots`, equality would forbid extraneous keys and match `PoolState`’s stronger type.

- Missing value-typing on votes
  - `PoolTypeOK` does not assert `\A s \in Slots : \A v \in Validators : pool.votes[s][v] \subseteq Vote`. This is implied by the declared `PoolState` type and preserved operationally by `DeliverVote`, but adding it to the invariant would make `MultiplicityRulesRespected` robust even if other code wrote to the pool.

- Redundancy vs. record type
  - The invariant partially re-states `PoolState` but not fully. This is fine, but it creates a gap where the record type is stronger than the invariant. Consider consistency (see Suggestions).

## 6. Suggestions for Improvement

- Strengthen the invariant for completeness and self-containment:
  - Add certificate domain equality:
    - `DOMAIN pool.certificates = Slots`
  - Add vote value typing:
    - `\A s \in Slots : \A v \in Validators : pool.votes[s][v] \subseteq Vote`

- Alternatively, collapse to the record-type membership:
  - Replace or augment with `pool \in PoolState` (captures both domains and value ranges concisely) while keeping `MultiplicityRulesRespected` and `CertificateUniqueness` as separate invariants.

- Optional additional invariants (whitepaper fidelity checks):
  - Apply `AllCertificatesValid(pool.certificates[s])` and `NoConflictingCertificates(pool.certificates[s])` per slot (Table 6, Def. 13). These are already provided in `Certificates.tla` and can be included alongside `PoolTypeOK` for stronger safety typing.

Overall, the current invariant matches the paper’s abstractions and is sound; the above refinements would make it exact and defensive.

