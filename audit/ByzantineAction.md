**Code Under Audit**

- `specs/tla/alpenglow/MainProtocol.tla:167`

```
ByzantineAction(v) ==
    /\ v \in byzantineNodes
    /\ \E vote \in Vote : 
        /\ IsValidVote(vote)
        /\ vote.validator = v
        /\ messages' = messages \union {vote}
    /\ UNCHANGED <<validators, blocks, byzantineNodes, time, finalized, blockAvailability>>
```

**Whitepaper References**

- Assumption 1 (fault tolerance: <20% Byzantine stake)
  - `alpenglow-whitepaper.md:103`–`alpenglow-whitepaper.md:109`
- Adversary model (arbitrary misbehavior, collusion; authenticity via signatures)
  - `alpenglow-whitepaper.md:226`
- Definition 11 (messages; vote objects and signatures)
  - `alpenglow-whitepaper.md:478` (intro), `alpenglow-whitepaper.md:500`–`alpenglow-whitepaper.md:507` (Tables 5–6)
- Definition 12 (storing votes; count-once per slot)
  - `alpenglow-whitepaper.md:513`–`alpenglow-whitepaper.md:518`

Related spec context used by this action:

- Vote type and validation
  - `Vote` structure: `specs/tla/alpenglow/Messages.tla:52`
  - `IsValidVote`: `specs/tla/alpenglow/Messages.tla:162`
- Network set and variables
  - State vector including `messages`, `byzantineNodes`: `specs/tla/alpenglow/MainProtocol.tla:41`
- Vote dissemination/storage
  - `DeliverVote` (store to all Pools): `specs/tla/alpenglow/MainProtocol.tla:336`
  - Per-slot/validator multiplicity (Definition 12): `specs/tla/alpenglow/VoteStorage.tla:54`
  - `StoreVote`: `specs/tla/alpenglow/VoteStorage.tla:84`
- Stake accounting helpers
  - `CalculateStake`, `TotalStake`: `specs/tla/alpenglow/Certificates.tla:26`, `specs/tla/alpenglow/Certificates.tla:41`
- Fault-tolerance check in Init (enforces Assumption 1 in-model)
  - `ByzantineStakeOK`: `specs/tla/alpenglow/MainProtocol.tla:80`

**Reasoning**

- Intent
  - Models adversarial capability under Assumption 1: any validator flagged Byzantine may inject arbitrarily many syntactically valid votes into the network (`messages`). This captures “arbitrary misbehavior,” including sending votes early/late, equivocating across vote types, and emitting fallback or finalization votes without preconditions.

- Authenticity and non-forgery
  - The guard `vote.validator = v` ensures a Byzantine node can only inject votes bearing its own identity, reflecting the signature requirement from Table 5 (Definition 11). There is no ability to forge other validators’ votes, matching the cryptographic authenticity assumption.

- Syntactic validity only
  - `IsValidVote` checks type, slot membership, and block-hash vs. NoBlock well-formedness (no semantic timing/window constraints). This is appropriate: the whitepaper restricts honest behavior, but the adversary may emit any message consistent with the format.

- Interaction with storage and thresholds (Definition 12)
  - After injection, `DeliverVote` stores votes into every validator’s Pool via `StoreVote`, which enforces the per-slot/per-validator multiplicity limits (“first notar or skip; up to 3 notar-fallback; first skip-fallback; first final”). Byzantine equivocation across initial vote types is therefore modelled as “counted once per type per validator,” while honest nodes are further constrained by VotorCore to a single initial vote (Lemma 20 is stated for correct nodes only in the spec).

- Safety/liveness impact
  - Safety: Certificates still require stake thresholds and are created only by correct nodes via `GenerateCertificateAction`; Byzantine nodes cannot inject certificates directly. Under `ByzantineStakeOK` the adversary alone cannot reach ≥60% or ≥80% to fabricate certificates.
  - Liveness: Byzantine vote spam is bounded by multiplicity rules at storage. Timing/non-delivery is already handled by the network nondeterminism and weak fairness on delivery actions.

- Scope boundaries (certificates)
  - The action deliberately excludes certificate injection. This aligns with Definition 13 (“broadcast when newly added to Pool”) and avoids needing to validate thresholds on ingress. Certificates enter `messages` only via honest `GenerateCertificateAction`.

**Conclusion**

- The action accurately represents the adversary model in the whitepaper and preserves key abstractions:
  - Allows arbitrary, self-signed valid votes from Byzantine validators (Adversary; Definition 11).
  - Respects non-forgery and authentic identities via `vote.validator = v` (Table 5 signatures).
  - Defers semantic constraints to honest logic; storage multiplicity (Definition 12) prevents unbounded adversarial amplification.
  - Maintains safety by not permitting direct certificate injection; thresholds are only achieved by honest aggregation.

Overall, the abstraction matches the whitepaper’s intent for modelling Byzantine behavior and integrates correctly with dissemination and Pool semantics.

**Open Questions / Concerns**

- Slot bounding in adversarial votes
  - `ByzantineAction` does not itself bound `vote.slot` by `MaxSlot`. This is harmless if `Slots = 1..MaxSlot` in the model, but if `Slots` is larger, votes beyond `MaxSlot` inflate state without effect. Confirm that the model configuration binds `Slots` to a finite range.

- Votes for non-existent block hashes
  - A Byzantine can inject a notarization vote for a `blockHash` not in `blocks`. These votes will be stored but cannot lead to certificates without honest participation (impossible under <20% stake) and cannot trigger events/finalization that require `b \in blocks`. This is safe but increases state. If desired, one could type-check against known blocks at the cost of generality.

- Double counting across skip/notar terms
  - Definition 16 recalls “count-once per slot.” The spec implements this for notarization across blocks (`TotalNotarStake`) and for skip separately; the SafeToSkip inequality uses `skip + totalNotar - maxNotar`, which is faithful to the paper and avoids unsafe inflation that could permit fast finalization of a conflicting block. No change needed, but this nuance is worth noting when reasoning about fallback triggers under adversarial equivocation.

**Suggestions for Improvement**

- Make the slot bound explicit (model hygiene)
  - Option A: strengthen `IsValidVote` to require `vote.slot \in 1..MaxSlot` in this model instance; or
  - Option B: add `/\ vote.slot <= MaxSlot` to `ByzantineAction`. This keeps the state space tight without changing protocol semantics.

- Optional: add an explicit comment linking to the adversary definition
  - E.g., in `MainProtocol.tla` above `ByzantineAction`, reference “Whitepaper §1.5 Adversary; Assumption 1” to help readers map the action to the paper.

- Maintain the no-certificate-injection boundary
  - If future work adds adversarial certificate injection for robustness testing, gate delivery with `IsValidCertificate` and Pool storage rules to preserve Definition 13’s thresholds and uniqueness.

**Cross-File References (for this block)**

- Main action under audit: `specs/tla/alpenglow/MainProtocol.tla:167`
- Vote type/validation: `specs/tla/alpenglow/Messages.tla:52`, `specs/tla/alpenglow/Messages.tla:162`
- Vote storage multiplicity: `specs/tla/alpenglow/VoteStorage.tla:54`
- Network delivery of votes: `specs/tla/alpenglow/MainProtocol.tla:336`
- Stake calculations and resilience assumption check: `specs/tla/alpenglow/Certificates.tla:26`, `specs/tla/alpenglow/MainProtocol.tla:80`

