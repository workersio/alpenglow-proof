# Audit: StoreVote (Definition 12 — Vote Storage)

## 1. Code Under Audit

```
StoreVote(pool, vote) ==
    IF CanStoreVote(pool, vote) THEN
        LET 
            slot == vote.slot
            validator == vote.validator
            existingVotes == pool.votes[slot][validator]
        IN
            [pool EXCEPT !.votes[slot][validator] = existingVotes \union {vote}]
    ELSE
        pool 
```

Spec location: `specs/tla/alpenglow/VoteStorage.tla:84`

## 2. Whitepaper Mapping

- Definition 12 (storing votes): `alpenglow-whitepaper.md:513` (page 20)
- Definition 13 (certificates context; pool behavior): `alpenglow-whitepaper.md:520`–`:532` (pages 20–21)
- MainProtocol links this rule to delivery handling: `specs/tla/alpenglow/MainProtocol.tla:530`–`:547`

Relevant excerpt (Def. 12): “Pool stores received votes for every slot and every node as follows: the first received notarization or skip vote; up to 3 received notar-fallback votes; the first received skip-fallback vote; and the first received finalization vote.”

## 3. Context and References in the Spec

- Pool state shape/type:
  - `PoolState` is a total function: `votes: [Slots -> [Validators -> SUBSET Vote]]`, `certificates: [Slots -> SUBSET Certificate]` — `specs/tla/alpenglow/VoteStorage.tla:17`
  - `InitPool` populates domains for all `Slots` and `Validators` — `specs/tla/alpenglow/VoteStorage.tla:28`
- Guard that StoreVote relies on:
  - `CanStoreVote(pool, vote)` implements Definition 12 multiplicities — `specs/tla/alpenglow/VoteStorage.tla:54`
- Type and validity of votes:
  - `Vote` record and `VoteType` definitions — `specs/tla/alpenglow/Messages.tla:26`
  - `IsValidVote(vote)` — `specs/tla/alpenglow/Messages.tla:79`
- Call sites ensuring validity and usage:
  - Network delivery: `DeliverVote` checks `IsValidVote` and calls `StoreVote` for each validator — `specs/tla/alpenglow/MainProtocol.tla:533`–`:547`
  - Local voting paths: `TryNotar`, `TryFinal`, `TrySkipWindow` create votes via constructors and call `StoreVote` — `specs/tla/alpenglow/VotorCore.tla:117`, `:141`, `:167`
- Invariants that this operation must preserve:
  - `MultiplicityRulesRespected(pool)` matches Definition 12 caps — `specs/tla/alpenglow/VoteStorage.tla:198`
  - `PoolTypeOK(pool)` ensures domains stay intact — `specs/tla/alpenglow/VoteStorage.tla:188`

## 4. Reasoning vs. Whitepaper Claims

Intent and abstraction
- The function is a pure state transformer that attempts to add a single vote into the per-slot, per-validator bin of the Pool and otherwise leaves the Pool unchanged. It is intentionally oblivious to certificate creation or other state.

Correctness w.r.t. Definition 12 (multiplicity)
- Responsibility split is clear and sound:
  - `CanStoreVote(pool, vote)` enforces all multiplicity constraints exactly as stated in Def. 12:
    - First initial vote: forbid storing a second `NotarVote` or `SkipVote` for the same (slot, validator).
    - Up to 3 `NotarFallbackVote` per (slot, validator).
    - At most one `SkipFallbackVote` and one `FinalVote` per (slot, validator).
  - `StoreVote` only performs the addition when the guard holds. Otherwise Pool is unchanged.
- Set semantics (`existingVotes ∪ {vote}`) ensure idempotence in the face of duplicate deliveries (common in eventually reliable networks). Attempting to re-store the same vote has no effect.

Typing and domain safety
- Because `InitPool` defines `pool.votes` over all `Slots` and `Validators`, the function lookup `pool.votes[slot][validator]` is well-defined when `vote.slot ∈ Slots` and `vote.validator ∈ Validators`.
- All code paths that call `StoreVote` either:
  - Construct votes via `Create*` helpers with correct typing (VotorCore), or
  - Validate network votes with `IsValidVote` before calling `StoreVote` (MainProtocol).
  This matches the abstraction level of the whitepaper (signatures/authentication abstracted away) and maintains domain-correctness for lookups.

Conformance to stake-counting discipline
- The Pool stores votes keyed by (slot, validator) as sets, while stake computations (e.g., `NotarStake`, `SkipStake`) derive validator sets from stored votes. This realizes the “stake counted once per slot” discipline referenced under Definition 16 and used throughout §2.4–2.5.

Isolation from certificate rules (Definition 13)
- `StoreVote` does not directly generate certificates; aggregation is handled by `GenerateCertificate` and storage by `StoreCertificate`. This separation matches the whitepaper, where the Pool stores votes subject to multiplicities, and certificate generation/broadcast happens when thresholds are met (Table 6, Def. 13).

Monotonicity and invariants
- The update is monotonic: it only adds an element to a set; it never removes. Under the guard, this preserves `MultiplicityRulesRespected(pool)` by construction.
- The function does not alter domains (`Slots`, `Validators`) or other Pool fields, preserving `PoolTypeOK(pool)`.

## 5. Conclusion

- The implementation of `StoreVote` correctly and completely realizes the vote-storage rule of Definition 12 (whitepaper §2.5, page 20) at the TLA+ abstraction level.
- The reliance on `CanStoreVote` for multiplicities, set-based idempotence for duplicates, and call-site validation for typing together provide a faithful and safe encoding of the whitepaper’s Pool behavior.

Verdict: Pass — conforms to the whitepaper.

## 6. Open Questions / Concerns

- Domain guarding in isolation: `StoreVote` assumes `vote.slot ∈ Slots` and `vote.validator ∈ Validators`. This is guaranteed at call sites, but the function itself would be partial if misused. Acceptable at this abstraction, but worth documenting explicitly.
- Duplicate initial votes: The guard forbids storing any initial vote (`NotarVote` or `SkipVote`) once one exists. Even if the duplicate is identical, the guard blocks re-storage (a no-op anyway due to sets). This matches “first received …” but could be clarified as a deliberate choice to keep the guard strict.
- Fallback multiplicity semantics: Def. 12 allows “up to 3 received notar-fallback votes” per (slot, node). The spec enforces this count per validator per slot, regardless of the supported block. This matches the literal text; if the intent were per-block, the guard would need to be scoped to `(slot, validator, blockHash)`.
- Abstraction of authenticity: `IsValidVote` does not model signatures; the adversary model restricts injected votes to Byzantine validators. This is consistent with the paper’s trusted-identity assumption but should remain clearly stated in spec commentary.

## 7. Suggestions for Improvement

- Self-contained typing guard (optional): Either document or embed a light pre-check in `StoreVote` such as `IF IsValidVote(vote) THEN … ELSE pool` to make the function robust if reused elsewhere. Current call sites already ensure this.
- Clarify fallback scope in comments: Add a note near `CanStoreVote` stating that the “up to 3 notar-fallback votes” are per (slot, validator) across all blocks, which is how the current predicate is written.
- Add preservation lemma (for TLC model checking):
  - Example: `StoreVotePreservesMultiplicity == ∀ p ∈ PoolState, v ∈ Vote : MultiplicityRulesRespected(p) ⇒ MultiplicityRulesRespected(StoreVote(p, v))` under the `CanStoreVote` guard and `IsValidVote(v)`.
- Explicit idempotence note: In `StoreVote`’s comment, mention that set union makes replays harmless. This helps readers connect model behavior with network retransmissions.
- Tighten specification cross-links: In `VoteStorage.tla`, reference the exact whitepaper lines (e.g., `alpenglow-whitepaper.md:513`) in comments near `CanStoreVote` and `StoreVote` for quick lookup (some are present; ensure both are covered).

## 8. Traceability: Key File References

- StoreVote definition: `specs/tla/alpenglow/VoteStorage.tla:84`
- Multiplicity guard: `specs/tla/alpenglow/VoteStorage.tla:54`
- Pool state/type: `specs/tla/alpenglow/VoteStorage.tla:17`, `:28`
- Vote typing/validity: `specs/tla/alpenglow/Messages.tla:26`, `:79`
- Network delivery using StoreVote: `specs/tla/alpenglow/MainProtocol.tla:533`–`:547`
- Local voting paths using StoreVote: `specs/tla/alpenglow/VotorCore.tla:117`, `:141`, `:167`
- Whitepaper Definition 12: `alpenglow-whitepaper.md:513`

