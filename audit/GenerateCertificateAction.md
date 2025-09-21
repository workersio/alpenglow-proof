**Code Under Audit**

- `specs/tla/alpenglow/MainProtocol.tla:133`

```
GenerateCertificateAction(v, slot) ==
    /\ v \in CorrectNodes
    /\ slot \in Slots
    /\ slot <= MaxSlot
    /\ LET pool == validators[v].pool
           certs == GenerateCertificate(pool, slot)
           candidates == {c \in certs :
                             \/ c \notin messages
                             \/ (\E w \in Validators : CanStoreCertificate(validators[w].pool, c))}
       IN /\ candidates # {}
          /\ LET cert == CHOOSE c \in candidates : TRUE
             IN /\ messages' = messages \union {cert}
                /\ validators' = [validators EXCEPT ![v].pool = StoreCertificate(validators[v].pool, cert)]
    /\ UNCHANGED <<blocks, byzantineNodes, time, finalized, blockAvailability>>
```

**Whitepaper References**

- Definition 11 (messages) and Table 6 (certificate types and thresholds)
  - `alpenglow-whitepaper.md:478` (Definition 11)
  - `alpenglow-whitepaper.md:507` (Table 6)
- Definition 12 (storing votes; count-once per slot)
  - `alpenglow-whitepaper.md:513`
- Definition 13 (certificates: generate, store, broadcast; uniqueness)
  - `alpenglow-whitepaper.md:520`
  - Broadcast when newly added: `alpenglow-whitepaper.md:523`
  - Single certificate per type for a block/slot: page 21 note
- Definition 15 (Pool events) — downstream use of notarization/skip certs
  - `alpenglow-whitepaper.md:543`
- Standstill re-transmission (rebroadcast policy)
  - `alpenglow-whitepaper.md:1231`, `alpenglow-whitepaper.md:1262`
- Bandwidth optimization (only one finalization certificate should be broadcast)
  - `alpenglow-whitepaper.md:1271`

Related spec context used by this action:

- Certificate creation and storage
  - `GenerateCertificate` (builds all creatable certs for a slot): `specs/tla/alpenglow/VoteStorage.tla:181`
  - `CanStoreCertificate` (per-slot/per-type uniqueness, notar-family same hash): `specs/tla/alpenglow/VoteStorage.tla:109`
  - `StoreCertificate` (adds to pool if permitted): `specs/tla/alpenglow/VoteStorage.tla:127`
- Types and constants
  - `Validators`, `Slots`: `specs/tla/alpenglow/Messages.tla:17`, `specs/tla/alpenglow/Messages.tla:18`
- Dissemination helpers for comparison
  - `DeliverCertificate` (propagates to all validators’ pools): `specs/tla/alpenglow/MainProtocol.tla:306`
  - `BroadcastLocalVote` (vote rebroadcast gating): `specs/tla/alpenglow/MainProtocol.tla:319`
- Validator state with `pool`
  - `ValidatorState == [...] pool: PoolState`: `specs/tla/alpenglow/VotorCore.tla:53`
- Certificate validation (thresholds; supporting invariant helpers)
  - `IsValidCertificate`: `specs/tla/alpenglow/Certificates.tla:190`

**Reasoning**

- Purpose and scope
  - Models the Pool behavior from Definition 13: once enough votes accumulate (per Table 6), a correct node assembles the corresponding certificate(s), stores the certificate in its Pool, and broadcasts it to other nodes.

- Preconditions
  - `v \in CorrectNodes`, `slot \in Slots`, `slot <= MaxSlot` restrict the action to honest validators and a bounded exploration horizon. This aligns with the spec’s separation of honest vs. adversarial behavior (Byzantine certificate injection is not modeled).

- Certificate generation (Definition 13)
  - `certs == GenerateCertificate(pool, slot)` computes all certificates currently creatable from votes stored in `pool` for `slot`. The helper covers all rows of Table 6: fast-finalization (≥80%), notarization/fallback/skip/finalization (≥60%), and, if fast-finalization is possible, it also returns the implied notarization and notar-fallback certificates (whitepaper note on fast→notar→fallback implication).

- Uniqueness and storage (Definition 13)
  - Storage uses `StoreCertificate`, which enforces per-slot per-type uniqueness and, critically, that all notarization-family certificates in a slot share the same `blockHash`. This matches the whitepaper’s “single certificate of each type for a given block/slot” and supports Lemma 24 (unique notarization per slot) used elsewhere in the spec.

- Broadcast semantics (Definition 13)
  - The action adds a selected certificate to `messages` and updates the local `pool`. Combined with `DeliverCertificate`, which applies `StoreCertificate` for all validators simultaneously, this models “when newly added to Pool, broadcast to all nodes” and eventual delivery in §2.5/§2.10.

- Candidate selection and nondeterminism
  - `candidates` filters `certs` to those that are currently useful for dissemination; `CHOOSE` selects one to keep network steps small. Over time, fairness on `GenerateCertificateAction` allows all creatable certificate types (e.g., both Notarization and Notar-Fallback when fast is possible) to be assembled and disseminated.

**Conclusion**

- The action captures the core of Definition 13:
  - It generates certificates precisely when the vote thresholds are met, using the count-once rule from Definition 12.
  - It stores certificates subject to uniqueness constraints and disseminates them over the network.
  - It correctly leaves unrelated state unchanged and relies on `DeliverCertificate` to propagate certificates to all validators’ Pools.

- With one important caveat (see concerns), the abstraction matches the whitepaper’s intent and integrates properly with downstream events (Definition 15) and finalization (Definition 14).

**Open Questions / Concerns**

- Broadcast gating uses OR instead of AND.
  - `candidates == { c \in certs : c \notin messages \/ (\E w : CanStoreCertificate(..., c)) }` enables rebroadcast whenever the certificate is not currently in `messages` even if no validator can store it anymore. This can cause perpetual re-insertion of already-propagated certificates into `messages`, diverging from Definition 13’s “broadcast when newly added to Pool,” and bloating the state space. `BroadcastLocalVote` correctly uses an AND guard (`vt \notin messages /\ \E w : vt \notin validators[w].pool...`).

- Re-broadcast vs “newly added to Pool”.
  - Definition 13 specifies broadcasting upon newly adding a certificate to the local Pool. The current action may broadcast certificates that were already stored locally (it does not require `CanStoreCertificate(validators[v].pool, c)`). Given `DeliverCertificate` updates all validators at once, rebroadcasting is unnecessary for liveness and deviates from the whitepaper’s trigger. If standstill re-transmission is desired, it should be modeled explicitly (cf. `alpenglow-whitepaper.md:1231`).

- Deliver without validity check.
  - `DeliverCertificate` does not check `IsValidCertificate`. While certificates constructed by `GenerateCertificate` are valid by construction, the model could be tightened to admit only valid certificates in transit, as noted in the gaps doc and consistent with Definition 13.

- Choice of which certificate to broadcast first.
  - When fast-finalization is possible, `GenerateCertificate` also returns Notarization and Notar-Fallback certificates. Broadcasting (and storing) a Notarization certificate promptly can help enable `ParentReady` (Definition 15) on other nodes. The current nondeterministic choice will eventually cover all, but a priority heuristic could simplify reasoning.

**Suggestions for Improvement**

- Tighten broadcast guard to match Definition 13 and avoid infinite rebroadcasts:
  - Change the candidate filter to require both conditions (AND) and ensure we only broadcast when the local Pool can newly store the certificate:
    - Replace `\/` with `/\` and add a local-store check:
      - `candidates == { c \in certs : c \notin messages /\ (\E w \in Validators : CanStoreCertificate(validators[w].pool, c)) /\ CanStoreCertificate(validators[v].pool, c) }`
    - This mirrors `BroadcastLocalVote` and the “newly added to Pool” clause in Definition 13.

- Gate delivery on validity (optional but recommended):
  - In `DeliverCertificate`, require `IsValidCertificate(cmsg)` in the guard. This aligns with the whitepaper and reduces accidental admission of malformed certificates:
    - `\E cert \in messages : cert \in Certificate /\ IsValidCertificate(cert)`

- Prefer Notarization when fast path is present (optional):
  - When `GenerateCertificate` returns multiple certificate types for a slot, prefer broadcasting a Notarization certificate first to unlock `BlockNotarized`/`ParentReady` for peers sooner; then broadcast finalization certificates. This is a heuristic only; correctness does not require it.

- Consider gating fairness after GST (global, not specific to this action):
  - To reflect §2.10’s assumption that “after GST honest messages keep flowing,” gate the weak fairness on `GenerateCertificateAction` (and similar network actions) with `AfterGST`.

**Cross-File References (for this block)**

- Main action under audit: `specs/tla/alpenglow/MainProtocol.tla:133`
- Vote aggregation and certificate creation: `specs/tla/alpenglow/VoteStorage.tla:181`
- Certificate storage rules (uniqueness): `specs/tla/alpenglow/VoteStorage.tla:109`
- Store to Pool: `specs/tla/alpenglow/VoteStorage.tla:127`
- Network propagation: `specs/tla/alpenglow/MainProtocol.tla:306`
- Vote rebroadcast guard (reference pattern): `specs/tla/alpenglow/MainProtocol.tla:319`
- Types: `specs/tla/alpenglow/Messages.tla:17`, `specs/tla/alpenglow/Messages.tla:18`
- Certificate validity predicate: `specs/tla/alpenglow/Certificates.tla:190`

