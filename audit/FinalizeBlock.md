**Code Under Audit**

- `specs/tla/alpenglow/MainProtocol.tla:152`

```
FinalizeBlock(v, block) ==
    /\ v \in CorrectNodes
    /\ block \in blocks
    /\ LET pool == validators[v].pool
           slot == block.slot
       IN \/ HasFastFinalizationCert(pool, slot, block.hash)
          \/ (HasNotarizationCert(pool, slot, block.hash) /\ 
              HasFinalizationCert(pool, slot))
    /\ finalized' = [finalized EXCEPT ![v] = finalized[v] \union {block}]
    /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, time, blockAvailability>>
```

**Whitepaper References**

- Definition 14 (finalization): two ways to finalize, fast and slow
  - `alpenglow-whitepaper.md:536`
  - Slow path: unique notarized block finalized when finalization cert exists — `alpenglow-whitepaper.md:538`
  - Fast path: fast-finalization certificate on block b finalizes b — `alpenglow-whitepaper.md:539`
  - Ancestors finalized first — `alpenglow-whitepaper.md:541`
- Lemma 24: at most one block can be notarized in a given slot
  - `alpenglow-whitepaper.md:855`
- Lemma 25: finalized implies notarized
  - `alpenglow-whitepaper.md:866`

Related spec context used by this action:

- Certificate queries used in the guard
  - `HasNotarizationCert` — `specs/tla/alpenglow/VoteStorage.tla:214`
  - `HasFastFinalizationCert` — `specs/tla/alpenglow/VoteStorage.tla:231`
  - `HasFinalizationCert` — `specs/tla/alpenglow/VoteStorage.tla:237`
- Thresholds and creation conditions (Table 6)
  - `CanCreateFastFinalizationCert` (≥80% NotarVote) — `specs/tla/alpenglow/Certificates.tla:83`
  - `CanCreateNotarizationCert` (≥60% NotarVote) — `specs/tla/alpenglow/Certificates.tla:97`
  - `CanCreateFinalizationCert` (≥60% FinalVote) — `specs/tla/alpenglow/Certificates.tla:138`
- Unique notarization (Lemma 24) and safety invariants
  - `UniqueNotarization` — `specs/tla/alpenglow/MainProtocol.tla:483`
  - `SafetyInvariant` (single chain) — `specs/tla/alpenglow/MainProtocol.tla:447`
  - `NoConflictingFinalization` — `specs/tla/alpenglow/MainProtocol.tla:456`
- Finalized implies notarized (Lemma 25) expressed as an invariant
  - `FinalizedImpliesNotarized` — `specs/tla/alpenglow/MainProtocol.tla:510`

**Reasoning**

- Intent
  - This action models Definition 14. A correct validator finalizes a block either via: (a) a fast-finalization certificate on that block (≥80% NotarVote), or (b) the slow path: a finalization certificate for the slot together with notarization of the specific block (both ≥60% thresholds, per Table 6).

- Guards align with Definition 14
  - Fast path: `HasFastFinalizationCert(pool, slot, block.hash)` matches “fast-finalization certificate on block b finalizes b.”
  - Slow path: `(HasNotarizationCert(pool, slot, block.hash) /\ HasFinalizationCert(pool, slot))` encodes “finalization certificate exists for slot s and the unique notarized block in slot s is finalized.” Explicitly checking the notarized block hash is consistent with the uniqueness condition (Lemma 24).

- Preconditions and scope
  - Only correct validators perform finalization (`v \in CorrectNodes`), and only known blocks can be finalized (`block \in blocks`). This fits the whitepaper’s focus on correct-node behavior; adversarial behavior is modeled elsewhere.

- Interplay with supporting invariants
  - Lemma 24 is captured by `UniqueNotarization` and cross-validator agreement by `GlobalNotarizationUniqueness`, ensuring the slow path selects a unique block per slot.
  - Lemma 25 is captured by `FinalizedImpliesNotarized`, which is consistent with both fast (80% ⇒ 60%) and slow paths.

**Conclusion**

- The guards correctly capture Definition 14’s fast and slow finalization paths and respect certificate semantics and uniqueness. The action adds the finalized block to the validator’s local set and leaves unrelated state unchanged, which is appropriate.
- However, the implementation does not model the “ancestors finalized first” clause of Definition 14: it finalizes only `block`, not its ancestors.
- Additionally, there is no weak fairness on `FinalizeBlock`, so even if the guard remains enabled, temporal liveness properties like `EventualFinalization` may be vulnerable to execution paths that starve this action.

**Open Questions / Concerns**

- Ancestor-closure is not enforced.
  - Whitepaper: “Whenever a block is finalized (slow or fast), all ancestors of the block are finalized first” (`alpenglow-whitepaper.md:541`). Current action updates `finalized[v]` with `{block}` only. This is a semantic drift with respect to Definition 14.

- Missing fairness for finalization.
  - `FinalizeBlock` is a disjunct of `Next` but lacks a `WF_vars(...)` clause. This can permit infinite runs where certificates persist but no finalization step fires, weakening liveness claims in §2.10.

- No availability check for delivery.
  - Finalization does not require `block \in blockAvailability[v]`. The whitepaper allows repair/collection around notarization and finalization, but if the model is intended to reflect “execution-layer delivery after finalization,” you may want to ensure the block is locally available before or immediately after finalization (see also §2.8 and `RepairBlock`).

**Suggestions for Improvement**

- Enforce ancestor closure on finalization (align with Definition 14):
  - Replace the update with the ancestry-closed set using `GetAncestors` from `Blocks`:
    - `finalized' = [finalized EXCEPT ![v] = finalized[v] \union GetAncestors(block, blocks)]`
  - This satisfies the “ancestors finalized first” requirement directly.

- Add weak fairness for finalization (liveness hygiene):
  - In `Fairness`, add: `WF_vars(\E v \in Validators, b \in blocks : FinalizeBlock(v, b))`.
  - Optionally gate post-GST, consistent with other fairness suggestions in the repo’s gaps doc.

- Optional: tie-in availability at or before finalization.
  - Either require `block \in blockAvailability[v]` in `FinalizeBlock` or add a post-finalization fetch step to ensure the execution layer can consume finalized blocks deterministically.

**Cross-File References (for this block)**

- Main action under audit: `specs/tla/alpenglow/MainProtocol.tla:152`
- Certificate queries used in the guard: `specs/tla/alpenglow/VoteStorage.tla:214`, `specs/tla/alpenglow/VoteStorage.tla:231`, `specs/tla/alpenglow/VoteStorage.tla:237`
- Threshold logic (Table 6) and count-once rule: `specs/tla/alpenglow/Certificates.tla:83`, `specs/tla/alpenglow/Certificates.tla:97`, `specs/tla/alpenglow/Certificates.tla:138`
- Ancestry helpers for ancestor-closure suggestion: `specs/tla/alpenglow/Blocks.tla:105`, `specs/tla/alpenglow/Blocks.tla:125`
- Safety invariants referenced: `specs/tla/alpenglow/MainProtocol.tla:447`, `specs/tla/alpenglow/MainProtocol.tla:456`, `specs/tla/alpenglow/MainProtocol.tla:483`, `specs/tla/alpenglow/MainProtocol.tla:510`

