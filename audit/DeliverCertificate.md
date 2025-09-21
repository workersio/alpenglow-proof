**Code Under Audit**

- `specs/tla/alpenglow/MainProtocol.tla:306`

```
DeliverCertificate ==
    /\ \E cert \in messages : cert \in Certificate
    /\ LET cmsg == CHOOSE cc \in messages : cc \in Certificate
       IN /\ messages' = messages \ {cmsg}
          /\ validators' = [w \in Validators |->
                               [validators[w] EXCEPT
                                   !.pool = StoreCertificate(@, cmsg)]]
    /\ UNCHANGED <<blocks, byzantineNodes, time, finalized, blockAvailability>>
```

**Whitepaper References**

- Definition 11 (messages; certificate types and thresholds)
  - `alpenglow-whitepaper.md:478` (messages)
  - `alpenglow-whitepaper.md:507` (Table 6)
- Definition 13 (certificates: generate, store, broadcast; uniqueness)
  - `alpenglow-whitepaper.md:520`
  - Broadcast when newly added to Pool: `alpenglow-whitepaper.md:523`
  - Single certificate per type for given block/slot: `alpenglow-whitepaper.md:532`
- Partial synchrony and eventual delivery context (retransmit on standstill)
  - `alpenglow-whitepaper.md:1231`, `alpenglow-whitepaper.md:1262`, `alpenglow-whitepaper.md:1271`

**Reasoning**

- Purpose and scope
  - Implements the network dissemination of certificates described in Definition 13 by removing a certificate message from the in-flight set `messages` and storing it into every validator’s Pool.

- Preconditions and selection
  - Guard ensures some `cert` in `messages` is a `Certificate`; `cmsg` selects one such certificate non-deterministically. This keeps the model small-step while permitting fairness to deliver all certificates eventually.

- State updates and invariants
  - Network: `messages' = messages \\ {cmsg}` models consumption of a single certificate message.
  - Pools: Each `validators[w].pool` is updated via `StoreCertificate`, which enforces Definition 13’s uniqueness rules:
    - At most one `SkipCert` and one `FinalizationCert` per slot.
    - All notarization-family certs (`NotarizationCert`, `NotarFallbackCert`, `FastFinalizationCert`) for a slot share the same `blockHash` (cross-type uniqueness on the block).
  - Unchanged variables: `blocks`, `byzantineNodes`, `time`, `finalized`, `blockAvailability` remain unchanged, matching the whitepaper where certificate delivery only affects Pool and subsequent events derived from Pool contents.

- Integration with the protocol
  - After storage, event actions (e.g., `EmitBlockNotarized`, `EmitParentReady`) observe the updated Pool to drive Votor per Definitions 15–16. Fairness includes `WF_vars(DeliverCertificate)`, aligning with the paper’s eventual delivery assumption after GST.

- Abstraction choice
  - Delivery stores to all validators’ Pools in one atomic step. While real networks deliver to nodes individually, this TLA+ abstraction preserves safety and suffices for liveness under weak fairness, deferring per-hop retransmission details to the standstill discussion (§3.3) and avoiding unnecessary state explosion.

**Conclusion**

- The action correctly models Definition 13’s dissemination of certificates: when a certificate is in transit, it is consumed from `messages` and stored into validators’ Pools subject to uniqueness and notar-family consistency. Together with fairness, this matches the whitepaper’s “broadcast and eventual delivery” intent and enables downstream Pool-driven events and finalization logic.

**Open Questions or Concerns**

- Validity check elided at delivery.
  - `DeliverCertificate` admits any `cmsg \in Certificate` without checking `IsValidCertificate(cmsg)`. In this model, only `GenerateCertificateAction` injects certificates into `messages`, and those are valid by construction; there is no Byzantine certificate injection action. Still, a validation guard would make the action robust to future changes.

- Rebroadcast on receipt vs. global delivery.
  - Definition 13 says “when a received or constructed certificate is newly added to Pool, broadcast it.” The spec abstracts this by a global delivery step (no additional rebroadcast on receipt). This is acceptable as a high-level abstraction; if hop-by-hop or standstill retransmission needs modeling, it should be introduced explicitly rather than piggybacked here.

- Delivery granularity and fairness.
  - The non-deterministic `CHOOSE` plus fairness ensures eventual delivery, but some models benefit from delivering to a subset of validators per step to reflect asynchrony more literally. This is not required for correctness, only a modeling style choice.

**Suggestions for Improvement**

- Gate on certificate validity (defensive but optional):
  - Strengthen the guard to `\E cert \in messages : cert \in Certificate /\ IsValidCertificate(cert)`, and choose accordingly. This future-proofs the action if certificate injection is extended.

- Optional: refine delivery granularity (modeling choice):
  - Introduce a `DeliverCertificateTo(w)` that stores into a single validator `w`, iterating under fairness. Use the existing `StoreCertificate` uniqueness to keep idempotency. Only if finer-grained asynchrony is needed for a specific analysis.

- Optional: add an invariant tying transit certificates to validity:
  - E.g., `\A c \in messages : c \in Certificate => IsValidCertificate(c)` to document the intended source of certificates.

**Cross-File References**

- Deliver action under audit: `specs/tla/alpenglow/MainProtocol.tla:306`
- Pool certificate storage rules: `specs/tla/alpenglow/VoteStorage.tla:109`
- Store certificate function: `specs/tla/alpenglow/VoteStorage.tla:127`
- Certificate validity predicate: `specs/tla/alpenglow/Certificates.tla:190`
- Validator state with `pool`: `specs/tla/alpenglow/VotorCore.tla:19`
- Certificate types and record: `specs/tla/alpenglow/Messages.tla:141`, `specs/tla/alpenglow/Messages.tla:150`
- Type invariant over `messages`: `specs/tla/alpenglow/MainProtocol.tla:605`
- Fairness includes delivery: `specs/tla/alpenglow/MainProtocol.tla:422`

