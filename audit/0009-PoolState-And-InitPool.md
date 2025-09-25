# Audit: PoolState and InitPool (VoteStorage pool structure)

## 1. Code That You Are Auditing

```tla
EXTENDS Naturals, FiniteSets, Messages, Blocks, Certificates

PoolState == [
    votes: [Slots -> [Validators -> SUBSET Vote]],  \* Votes by slot and validator
    certificates: [Slots -> SUBSET Certificate]      \* Certificates by slot
]

\* Initialize an empty pool
InitPool == [
    votes |-> [s \in Slots |-> [v \in Validators |-> {}]],
    certificates |-> [s \in Slots |-> {}]
]
```

Reference in repo (identical definitions): `specs/tla/alpenglow/VoteStorage.tla:24`–`specs/tla/alpenglow/VoteStorage.tla:33`.

Referenced modules providing types and constants:
- `specs/tla/alpenglow/Messages.tla:16`–`specs/tla/alpenglow/Messages.tla:28` (constants `Validators`, `Slots`, etc.)
- `specs/tla/alpenglow/Messages.tla:52`–`specs/tla/alpenglow/Messages.tla:58` (record type `Vote`)
- `specs/tla/alpenglow/Messages.tla:136`–`specs/tla/alpenglow/Messages.tla:153` (record type `Certificate`)
- `specs/tla/alpenglow/Certificates.tla` (certificate guards/validation used elsewhere; not directly needed here)
- `specs/tla/alpenglow/Blocks.tla` (block structure; not used by this snippet but extended consistently)

## 2. Whitepaper Sections and References

- Section 2.5 “Pool” (storage, certificates, events):
  - Definition 12 (storing votes): `alpenglow-whitepaper.md:513`–`alpenglow-whitepaper.md:517`.
  - Definition 13 (certificates): `alpenglow-whitepaper.md:520`, `alpenglow-whitepaper.md:532`.
  - Definition 15 (events): `alpenglow-whitepaper.md:543`–`alpenglow-whitepaper.md:548`.
  - Definition 16 (fallback events, “count once per slot” reminder): `alpenglow-whitepaper.md:554`.
- Section 2.4 (vote and certificate message families referenced by Pool): `alpenglow-whitepaper.md:68`.

## 3. Reasoning: Mapping Code to Whitepaper Claims

- Pool as a local store per validator (Sec. 2.5): The record `PoolState` provides two stores:
  - `votes: [Slots -> [Validators -> SUBSET Vote]]` matches “Pool stores received votes for every slot and every node” (Def. 12). The inner `SUBSET Vote` captures the set nature and supports Def. 12 multiplicity constraints enforced by Pool logic (outside this snippet; see `VoteStorage.tla`).
  - `certificates: [Slots -> SUBSET Certificate]` captures “Pool generates, stores and broadcasts certificates” with uniqueness per type/block/slot (Def. 13). Representing certificates slot-indexed mirrors the slot-scoped semantics of certificates in the paper.

- Initialization: `InitPool` puts empty sets at every `[slot][validator]` for votes and empty sets for `certificates[slot]`. This aligns with a clean initial Pool prior to any messages and is consistent with the whitepaper’s algorithmic start state.

- Type alignment with message definitions (Sec. 2.4): The snippet EXTENDS `Messages` so that `Vote` and `Certificate` refer to the canonical record shapes used system-wide. `Slots` and `Validators` come from the same module, ensuring consistent domains.

- Abstraction level: The whitepaper’s Def. 12/13 prescribe constraints (e.g., “first initial vote”, “≤3 fallback”, “single certificate per type per block/slot”). Those constraints are not encoded into the PoolState type itself but are enforced by Pool operations (`CanStoreVote`, `StoreVote`, `CanStoreCertificate`, `StoreCertificate`) in `VoteStorage.tla`. This is appropriate for TLA+: the state captures structure; actions and invariants capture rules.

## 4. Conclusion of the Audit

- The Pool structure and its initialization accurately reflect the whitepaper’s Pool abstraction:
  - Votes are stored per slot and per node (validator) with capacity for sets of `Vote` records (Def. 12).
  - Certificates are stored per slot as sets of `Certificate` records (Def. 13), enabling the one-per-type-per-block/slot uniqueness rule to be enforced by actions.
  - The initialization produces an empty Pool consistent with protocol start.
- The snippet’s EXTENDS list is consistent with the system’s shared types. While `Blocks` is not used directly by the snippet, its inclusion is harmless and consistent with the broader module structure (`VoteStorage.tla`).

Overall, the state shape and initialization conform to the whitepaper abstractions and are consistent with the rest of the TLA+ spec.

## 5. Open Questions or Concerns

- Slot/validator alignment inside sets:
  - `votes[s][v] ⊆ Vote` does not by type alone ensure that every vote in that set has `vote.slot = s` and `vote.validator = v`. The whitepaper’s intent implies this alignment. It is usually enforced by the storing actions; consider asserting it as an invariant for clarity.
  - Similarly, `certificates[s] ⊆ Certificate` does not by type alone ensure `cert.slot = s`; this is again expected to be maintained by construction but could be captured as an explicit invariant.

- Unused extension: `Blocks` is extended but not referenced in these two definitions. This is likely for cohesion because the broader `VoteStorage` module uses block-related predicates for events. Not an error, just a note.

## 6. Suggestions for Improvement

- Add explicit Pool typing/slot-alignment invariants (lightweight but clarifying):

  - Vote alignment per slot and validator:
    ```tla
    PoolVotesSlotValidatorAligned(pool) ==
      \A s \in Slots : \A v \in Validators :
        \A vt \in pool.votes[s][v] : vt.slot = s /\ vt.validator = v
    ```

  - Certificate alignment per slot:
    ```tla
    PoolCertificatesSlotAligned(pool) ==
      \A s \in Slots : \A c \in pool.certificates[s] : c.slot = s
    ```

  These complement existing checks like `PoolTypeOK` and `CertificateUniqueness` in `specs/tla/alpenglow/VoteStorage.tla`.

- Optional: Reference alignment invariants from the top-level spec as invariants to be checked by TLC. This makes the Pool’s intended discipline explicit and helps catch accidental mis-stores in future changes.

- Documentation cross-link: Next to `PoolState` in `VoteStorage.tla`, consider adding a brief comment “see Def. 12/13” with page/section markers to mirror the citations used elsewhere in the repo for easier traceability.

