# Audit: CreateNotarFallbackVote

## 1. Code Under Audit

```tla
CreateNotarFallbackVote(validator, slot, blockHash) ==
    [type |-> "NotarFallbackVote",
     validator |-> validator,
     slot |-> slot,
     blockHash |-> blockHash]
```

Implementation location: `specs/tla/alpenglow/Messages.tla:75`.

Related type and helpers in the same file:
- `VoteType` includes `"NotarFallbackVote"`: `specs/tla/alpenglow/Messages.tla:44`
- `Vote` record schema: `specs/tla/alpenglow/Messages.tla:53`
- Fallback classification helpers: `IsNotarVote`, `IsFallbackVote`: `specs/tla/alpenglow/Messages.tla:112`, `specs/tla/alpenglow/Messages.tla:123`
- Validation: `IsValidVote`: `specs/tla/alpenglow/Messages.tla:163`

Known usages and downstream rules:
- Votor emits this vote upon SafeToNotar: `specs/tla/alpenglow/VotorCore.tla:276`, `specs/tla/alpenglow/VotorCore.tla:280`.
- Pool multiplicity (up to 3 per validator per slot): `specs/tla/alpenglow/VoteStorage.tla:68`, `specs/tla/alpenglow/VoteStorage.tla:70`.
- Notar-Fallback certificates accept mixed initial/fallback votes: `specs/tla/alpenglow/Certificates.tla:165`–`specs/tla/alpenglow/Certificates.tla:168`.

## 2. Whitepaper Section and References

Primary mapping (messages and votes):
- Definition 11 (messages): `alpenglow-whitepaper.md:478`
- Table 5 (vote types), row “Notar-Fallback Vote — NotarFallbackVote(slot(b), hash(b))”: `alpenglow-whitepaper.md:492`

Threshold and certificate context:
- Table 6, row “Notar-Fallback Cert. — NotarVote or NotarFallbackVote — Σ ≥ 60%”: `alpenglow-whitepaper.md:503`
- “fast ⇒ notar ⇒ fallback” implication: `alpenglow-whitepaper.md:534`

Pool/storage and event context:
- Definition 12 (storing votes): includes “up to 3 notar-fallback votes”: `alpenglow-whitepaper.md:515`–`alpenglow-whitepaper.md:517`
- Definition 15 (Pool events) including ParentReady: `alpenglow-whitepaper.md:540`–`alpenglow-whitepaper.md:548`
- Definition 16 (fallback events) and SafeToNotar narrative: `alpenglow-whitepaper.md:554`, conditions elaborated on Page 22: `alpenglow-whitepaper.md:603`
- Algorithm hooks: “upon SafeToNotar(s, hash(b)) do”: `alpenglow-whitepaper.md:656`

## 3. Reasoning: Code vs. Whitepaper Claims

What the paper specifies:
- Table 5 defines a Notar-Fallback Vote as `NotarFallbackVote(slot(b), hash(b))`, signed by the voter. It carries exactly the slot and the block hash of b (no additional fields).
- Table 6 defines the Notar-Fallback Certificate as aggregating NotarVote or NotarFallbackVote, with threshold Σ ≥ 60% of total stake; validators are counted once per slot.
- Definition 12 constrains Pool to store up to 3 notar-fallback votes per validator per slot, while still only one initial vote (notarization or skip).
- Definition 16 defines SafeToNotar(s, b): after the node has already cast its initial vote in slot s (but not for b), and the observed notarization stake for b meets either notar(b) ≥ 40% or (skip(s) + notar(b) ≥ 60% and notar(b) ≥ 20%). On first slot of a window the event can be issued immediately; otherwise, it additionally requires a notar-fallback certificate for the parent block.

What the code implements:
- The constructor `CreateNotarFallbackVote` returns a `Vote` record with fields `type = "NotarFallbackVote"`, `validator`, `slot`, `blockHash`, matching Table 5’s object shape and the `Vote` schema in `Messages.tla`.
- The vote is created and stored only in the SafeToNotar handler: `HandleSafeToNotar` calls `CreateNotarFallbackVote(...)` and `StoreVote` after first attempting to issue any missed skip votes (`TrySkipWindow`), then marks the slot with `BadWindow` as per Algorithm 1: `specs/tla/alpenglow/VotorCore.tla:276`–`specs/tla/alpenglow/VotorCore.tla:284`.
- Pool multiplicity is exactly as per Definition 12: up to 3 `NotarFallbackVote` per validator per slot (and only the first initial vote): `specs/tla/alpenglow/VoteStorage.tla:54`–`specs/tla/alpenglow/VoteStorage.tla:80`.
- Certificates count validators once per slot and accept both initial and fallback notar votes for Notar-Fallback certificates: `CanCreateNotarFallbackCert` filters votes to types {NotarVote, NotarFallbackVote} for `(slot, blockHash)`, then applies Σ ≥ 60%: `specs/tla/alpenglow/Certificates.tla:165`–`specs/tla/alpenglow/Certificates.tla:168`. Defensive validation also enforces the same relevance and threshold: `specs/tla/alpenglow/Certificates.tla:246`–`specs/tla/alpenglow/Certificates.tla:260`.
- Importantly, the SafeToNotar conditions (Definition 16) in the model compute notar(b) and skip(s) using only initial votes (NotarVote and SkipVote), not fallback votes. See `NotarStake`, `SkipStake`, `TotalNotarStake`, `MaxNotarStake` operating solely on initial votes: `specs/tla/alpenglow/VoteStorage.tla:147`, `specs/tla/alpenglow/VoteStorage.tla:155`, `specs/tla/alpenglow/VoteStorage.tla:162`, `specs/tla/alpenglow/VoteStorage.tla:169`. This aligns precisely with Definition 16’s use of notar(b) and skip(s) and prevents circularity.

Abstraction notes:
- Signatures and aggregate signatures are abstracted at the set-of-votes level; stake-weighting is performed by `StakeMap` and `StakeFromVotes` in `Certificates.tla` (Σ over unique validators). This is consistent with §1.6 and Table 6’s Σ semantics.
- The constructor does not embed any event logic; enforcement of Definition 16 (when this vote may be produced) is explicitly in `CanEmitSafeToNotar` within Pool logic and in Votor’s event handler.

Conclusion of reasoning:
- The constructor returns exactly the data shape specified by Definition 11, and its use sites enforce the whitepaper’s conditions (Definition 16) and storage multiplicity (Definition 12). Certificate construction and validation match Table 6, counting validators once and accepting mixed initial/fallback notar votes for fallback certificates.

## 4. Audit Conclusion

- Conformance: Correct and complete. `CreateNotarFallbackVote` faithfully represents the Notar-Fallback Vote object from Table 5 and integrates with Votor, Pool, and Certificates in accordance with Definitions 12, 15–16 and Table 6.
- Soundness: The model avoids counting fallback votes in the SafeToNotar trigger, respects multiplicity (≤3) per validator per slot, and aggregates fallback votes with initial notar votes only for fallback certificates, exactly as prescribed.

## 5. Open Questions / Concerns

- Constructor typing vs. guard placement: The constructor itself does not assert `slot ∈ Slots` or `blockHash ∈ BlockHashes`; these are enforced by `IsValidVote` and by guarded call sites (`HandleSafeToNotar`). This is idiomatic TLA+, but a typed wrapper could reduce accidental misuse in future extensions.
- Block presence prior to fallback voting: The whitepaper requires that, if not the first slot of a window, the node identifies the parent and observes a notar-fallback certificate for the parent before SafeToNotar; also that b is present in storage before emitting SafeToNotar for b. The TLA model encodes these as preconditions in `CanEmitSafeToNotar` and in the event flow; the constructor itself is agnostic. This is acceptable but worth keeping explicit in comments near handlers.
- “Up to 3” fallback votes per validator: The Pool implements the exact “up to 3” rule. While this matches Definition 12, it may be useful to document why three is sufficient (whitepaper intent: allow safety-vote evolution while preventing unbounded storage or spam) and confirm no other module assumes a different bound.

## 6. Suggestions for Improvement

- Add a block-typed wrapper to encode slot–hash consistency by construction:
  ```tla
  CreateNotarFallbackVoteForBlock(v, b) ==
      CreateNotarFallbackVote(v, b.slot, b.hash)
  ```
  Use it at the call site where `b` is known, improving readability and reducing pairing errors.

- State the abstraction boundary near constructors (single-line comment): clarify that signatures are abstracted away and certificates are set-of-votes with stake weights, per §1.6, to preempt confusion when comparing to Table 5’s signed objects.

- Optional invariant strengthening (aid for model checking): assert that locally created fallback votes are only produced under `CanEmitSafeToNotar` and for the specific `(slot, blockHash)` passed by the event. This is already enforced by control flow; making it explicit can help proofs:
  ```tla
  THEOREM SafeToNotarProducesValidFallback ==
      \A val, s, h : (* SafeToNotar guard holds at (val, s, h) *) =>
          IsValidVote(CreateNotarFallbackVote(val.id, s, h))
  ```

---

Overall, `CreateNotarFallbackVote` is faithful to the whitepaper’s Definition 11 and is used exactly where Definition 16 allows. Storage limits (Def. 12) and certificate thresholds (Table 6) are correctly integrated. No functional mismatches identified.

