**1. Code Under Audit**

```
MultiplicityRulesRespected(pool) ==
    \A s \in Slots, v \in Validators :
        LET votes == pool.votes[s][v]
        IN /\ Cardinality({vt \in votes : vt.type \in {"NotarVote", "SkipVote"}}) <= 1
           /\ Cardinality({vt \in votes : vt.type = "NotarFallbackVote"}) <= 3
           /\ Cardinality({vt \in votes : vt.type = "SkipFallbackVote"}) <= 1
           /\ Cardinality({vt \in votes : vt.type = "FinalVote"}) <= 1
```

Source: `specs/tla/alpenglow/VoteStorage.tla:327`


**2. Whitepaper Sections & References**

- Definition 12 (storing votes): per-slot, per-node multiplicity rules — “first notarization or skip; up to 3 notar-fallback; first skip-fallback; first finalization” (alpenglow-whitepaper.md:513).
- Message types (Definition 11, Tables 5–6): enumerates vote types used in multiplicity checks (alpenglow-whitepaper.md:478, alpenglow-whitepaper.md:500).
- Lemma 20: a correct node casts at most one notarization or skip vote per slot; supports the ≤1 initial vote constraint (alpenglow-whitepaper.md:820).


**3. Reasoning (Spec ↔ Whitepaper)**

- Per-slot, per-validator scope:
  - The predicate quantifies over `s \in Slots` and `v \in Validators` and checks `pool.votes[s][v]` (stored votes for that validator and slot). This matches “Pool stores received votes for every slot and every node” (Def. 12).

- Initial vote multiplicity (≤1 between NotarVote and SkipVote):
  - The set `{vt \in votes : vt.type \in {"NotarVote", "SkipVote"}}` counts initial votes regardless of which one it is. The ≤1 constraint is exactly “The first received notarization or skip vote” (Def. 12) and aligns with Lemma 20’s non-equivocation across initial votes for a slot.

- Fallback votes:
  - NotarFallbackVote ≤ 3: directly reflects “up to 3 received notar-fallback votes” (Def. 12).
  - SkipFallbackVote ≤ 1: matches “the first received skip-fallback vote” (Def. 12).

- Finalization votes:
  - FinalVote ≤ 1: matches “the first received finalization vote” (Def. 12).

- Message type universe is consistent:
  - The types referenced here are defined in `Messages.tla` and correspond to Definition 11/Tables 5–6 in the whitepaper; see `specs/tla/alpenglow/Messages.tla:44`.

- Role in the model:
  - This predicate is an invariant-style check over the stored `PoolState`; it is complemented by the storage guard `CanStoreVote` that enforces these limits when adding new votes, ensuring the invariant is preserved by transitions.
  - It is consumed by the main protocol invariant `PoolMultiplicityOK` to assert per-node Pools adhere to whitepaper’s multiplicity (see `specs/tla/alpenglow/MainProtocol.tla:896`).


**4. Conclusion**

- The predicate precisely encodes the whitepaper’s Definition 12 multiplicity constraints for vote storage per-slot and per-validator:
  - ≤1 initial vote across NotarVote/SkipVote
  - ≤3 NotarFallbackVote
  - ≤1 SkipFallbackVote
  - ≤1 FinalVote
- Quantification over all slots and validators and the use of set `Cardinality` ensure these constraints hold globally across the Pool.
- The code aligns with message types and semantics defined in the whitepaper and `Messages.tla`, and is coherently integrated into invariants in `MainProtocol.tla`.


**5. Open Questions / Concerns**

- Notar-fallback block consistency:
  - Definition 12 specifies multiplicity only, not whether a validator’s up-to-3 notar-fallback votes in a slot must all target the same block. The model allows heterogeneity by type-only counting. If the protocol requires those fallback votes to be for a single block (e.g., the one tied to `SafeToNotar(s, b)`), consider an additional invariant constraining all stored NotarFallbackVote for a fixed `(s, v)` to share the same `blockHash`.

- Relationship with initial vote:
  - The fallback event predicates (Definition 16; modeled as `CanEmitSafeToNotar` / `CanEmitSafeToSkip` in `VoteStorage.tla`) constrain when such votes may be created. The multiplicity invariant does not itself enforce “only after initial vote” conditions; it’s purely about counts. This is acceptable as long as transition guards handle sequencing, but worth keeping in mind when reading this invariant in isolation.

- Idempotent duplicates:
  - Since `PoolState.votes[slot][validator]` is a set, re-receiving an identical message does not increase multiplicity. This is fine and desirable, but means the “≤ 3” bound for notar-fallback is about distinct vote instances (e.g., potentially with different `blockHash` or signatures), not raw message deliveries.


**6. Suggestions for Improvement**

- Optional structural strengthening:
  - Add a helper invariant stating that for any `(s, v)`, all stored NotarFallbackVote share the same `blockHash` if that is an intended property of Algorithm 1/Definition 16.
  - Similarly, specify whether SkipFallbackVote is only admissible following an initial NotarVote (as suggested by the `CanEmitSafeToSkip` precondition in `specs/tla/alpenglow/VoteStorage.tla:308`).

- Readability/DRY:
  - Consider rewriting the initial-vote constraint using the existing classification helpers: `IsInitialVote` from `Messages.tla`, e.g., `Cardinality({vt \in votes : IsInitialVote(vt)}) <= 1`. This keeps the invariant resilient to any future extensions to initial vote definitions.

- Cross-check invariant set:
  - Keep `MultiplicityRulesRespected` colocated with `PoolTypeOK` and `CertificateUniqueness` (already done) and ensure `MainProtocol` asserts all three for each node’s Pool, which it currently does.

