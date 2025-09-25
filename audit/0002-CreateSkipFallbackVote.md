# Audit: CreateSkipFallbackVote

1. Code that you are auditing.

```tla
CreateSkipFallbackVote(validator, slot) ==
    [type |-> "SkipFallbackVote",
     validator |-> validator,
     slot |-> slot,
     blockHash |-> NoBlock]
```

Defined in `specs/tla/alpenglow/Messages.tla:90`.

Referenced by the fallback handler in `specs/tla/alpenglow/VotorCore.tla:296`.

2. The whitepaper section and references that the code represents.

- Vote type definition: Table 5 lists “Skip-Fallback Vote | SkipFallbackVote(s)” (alpenglow-whitepaper.md:494).
- Algorithm 1 fallback action: upon SafeToSkip(s), broadcast SkipFallbackVote(s) (alpenglow-whitepaper.md:665).
- Fallback events: SafeToSkip(s) definition and rationale (alpenglow-whitepaper.md:552, alpenglow-whitepaper.md:554).
- Certificate threshold where skip and skip-fallback votes aggregate for SkipCert (Table 6) (alpenglow-whitepaper.md:504).
- Pool storage multiplicity: “the first received skip-fallback vote” (Definition 12) (alpenglow-whitepaper.md:517).

3. The reasoning behind the code and what the whitepaper claims.

- Abstraction intent:
  - SkipFallbackVote is a vote message used after the SafeToSkip(s) event proves that no block in slot s can be fast-finalized. The whitepaper shows that nodes then broadcast SkipFallbackVote(s) (Alg. 1, lines 21–25) and that SkipVote/SkipFallbackVote together can form a Skip Certificate (Table 6).

- Message shape and typing:
  - The spec’s Vote record includes fields: `type`, `validator`, `slot`, and `blockHash` where skip-style votes carry `NoBlock` instead of a real block hash, and Notar-style votes carry a real hash (Messages typing). The constructor sets `type = "SkipFallbackVote"`, fills `validator` and `slot`, and sets `blockHash = NoBlock`, matching the skip semantics and the validity predicate `IsValidVote` requiring `IsSkipVote(v) => v.blockHash = NoBlock` (specs/tla/alpenglow/Messages.tla:163, specs/tla/alpenglow/Messages.tla:168).

- Protocol placement and usage:
  - The handler `HandleSafeToSkip` invokes `CreateSkipFallbackVote` after calling `TrySkipWindow` and provided the slot is not over (no `ItsOver`) (specs/tla/alpenglow/VotorCore.tla:288–300). This mirrors Algorithm 1 lines 21–25: first attempt to skip unvoted slots, then broadcast SkipFallbackVote(s), and mark `BadWindow` (whitepaper lines alpenglow-whitepaper.md:665).

- Storage and aggregation consistency:
  - Pool multiplicity rules store only the first skip-fallback vote per validator per slot (Definition 12: alpenglow-whitepaper.md:517) via `CanStoreVote` case for `SkipFallbackVote` (specs/tla/alpenglow/VoteStorage.tla:72–74).
  - Skip certificates can be constructed from any mix of `SkipVote` and `SkipFallbackVote` at ≥60% stake (Table 6) and the spec encodes this in `CanCreateSkipCert` and `CreateSkipCert`, with `CanonicalizeSkipVotes` ensuring one counted vote per validator in the slot (specs/tla/alpenglow/Certificates.tla:177, specs/tla/alpenglow/Certificates.tla:207, specs/tla/alpenglow/Certificates.tla:243–247).

- Safety alignment (fallback preconditions):
  - Emission of SafeToSkip requires: already voted in slot s, not already skipped, and `skip(s) + Σ_b notar(b) − max_b notar(b) ≥ 40%` (alpenglow-whitepaper.md:552–554). The spec captures these checks in `CanEmitSafeToSkip` (specs/tla/alpenglow/VoteStorage.tla:306–319) and suppresses re-emission via `BadWindow` (specs/tla/alpenglow/MainProtocol.tla:655–656; VotorCore adds `BadWindow` when broadcasting the fallback vote).

4. The conclusion of the audit.

- The constructor `CreateSkipFallbackVote` correctly models the Skip-Fallback vote described in the whitepaper:
  - The message type and parameters match Table 5 (uses slot; validator identity is implicit in real systems via signatures and is explicit here for accounting).
  - The choice `blockHash = NoBlock` is consistent with the spec’s typing rule that skip-family votes carry no block hash and with how Skip certificates are defined and validated.
  - Its usage site in `HandleSafeToSkip` lines up with Algorithm 1: emits skip-fallback only after attempting to skip unvoted slots, and marks `BadWindow` to prevent repeated fallback behavior.
  - Pool multiplicity and certificate creation integrate SkipFallbackVote as per Definitions 12–13 and Table 6, maintaining “count once per slot” semantics in aggregation.

Therefore, the code is faithful to the whitepaper’s abstractions and safety conditions for skip-fallback voting.

5. Any open questions or concerns.

- StoreVote validity gating: `StoreVote` accepts any vote that passes multiplicity checks but does not also check `IsValidVote` at store time. This is defensible given later validation at certificate time, but it may be worth clarifying whether malformed skip-fallback votes (e.g., wrong `blockHash`) should be dropped earlier.
- Re-emission suppression consistency: The emission guard in the top-level protocol prevents repeated SafeToSkip handling when `BadWindow` is set (specs/tla/alpenglow/MainProtocol.tla:656). This agrees with VotorCore’s `BadWindow` placement, but it might be useful to add an invariant that a validator cannot store more than one SkipFallbackVote for a given slot (already enforced by `CanStoreVote`) and cannot broadcast more than once (enforced structurally by `BadWindow`).
- Validator identity: The whitepaper tables omit an explicit `validator` field (implied by signatures). The TLA+ model includes it explicitly. This is a harmless abstraction refinement, but a comment cross-referencing the whitepaper’s signature-based identity would aid readers.

6. Any suggestions for improvement.

- Add a creation-time validity invariant: Consider asserting `IsValidVote(CreateSkipFallbackVote(v, s))` as a lemma or including a unit property to increase confidence that creation helpers always satisfy `IsValidVote`.
- Optional defensive check: Gate `StoreVote` with `IsValidVote(vote)` so that obviously malformed votes are not stored (this would not change the behavior of votes created by the provided helpers but would document a stronger Pool contract against adversarial inputs).
- Documentation tweak: In `Messages.tla`, add a brief comment near `CreateSkipFallbackVote` pointing to whitepaper Algorithm 1 lines 21–25 and Definition 16, to make the call path even clearer to auditors.

