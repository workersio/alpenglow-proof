# Audit: CanEmitSafeToNotar — SafeToNotar fallback event (Definition 16)

Status: PASS (matches whitepaper Definition 16 with correct gating and thresholds)

## 1. Code Under Audit

```
CanEmitSafeToNotar(pool, slot, blockHash, parentHash, alreadyVoted, votedForBlock) ==
    /\ alreadyVoted      \* Must have voted in slot
    /\ ~votedForBlock    \* But not for this block
    /\ LET notar == NotarStake(pool, slot, blockHash)
           skip == SkipStake(pool, slot)
           parentReady == 
                \* Per Def. 16, parent must have a notar-fallback cert unless this is the
                \* first slot of a window. The parent's slot may be < s-1 (skipped slots),
                \* so search all prior Slots while staying within the Pool's domain.
                \* The check is specific to NotarFallbackCert (per whitepaper text).
                IsFirstSlotOfWindow(slot) \/
                    (\E ps \in Slots : ps < slot /\ HasNotarFallbackCert(pool, ps, parentHash))
       IN parentReady /\
          (MeetsThreshold(notar, 40)
           \/ (MeetsThreshold(skip + notar, DefaultThreshold) /\ MeetsThreshold(notar, 20)))
```

Source: `specs/tla/alpenglow/VoteStorage.tla:283`

## 2. Whitepaper Sections and References

- Definition 16 (fallback events) — SafeToNotar: `alpenglow-whitepaper.md:554`–`:571` (pages 21–22)
  - Formula (p. 22): notar(b) ≥ 40% OR (skip(s) + notar(b) ≥ 60% AND notar(b) ≥ 20%).
  - Emission preconditions: node already voted in slot s, but not to notarize b.
  - Parent requirement: if s is first slot of window, emit; otherwise, emit when Pool contains the notar-fallback certificate for the parent as well (after retrieving b to learn its parent).
- Definition 15 (Pool events) — ParentReady context: `alpenglow-whitepaper.md:543`–`:548` (p. 21)
- Definition 12 (count-once-per-slot rule): referenced by Def. 16; see broader §2.5 around `alpenglow-whitepaper.md:516` and preceding content.

Repository cross-references used by this operator:
- Thresholds and stake arithmetic:
  - `specs/tla/alpenglow/Certificates.tla:48` — `DefaultThreshold == 60`.
  - `specs/tla/alpenglow/Certificates.tla:95` — `MeetsThreshold(stake, thresholdPercent)` uses Σ_total and integer math.
- Vote-derived stake helpers (initial votes only):
  - `specs/tla/alpenglow/VoteStorage.tla:147` — `NotarStake(pool, slot, blockHash)` counts NotarVote validators once.
  - `specs/tla/alpenglow/VoteStorage.tla:155` — `SkipStake(pool, slot)` counts SkipVote validators once.
  - `specs/tla/alpenglow/VoteStorage.tla:31` — Pool initialization layout for `votes`.
- Parent gating and slot/window helpers:
  - `specs/tla/alpenglow/VoteStorage.tla:227` — `HasNotarFallbackCert(pool, slot, blockHash)`.
  - `specs/tla/alpenglow/Blocks.tla:192` — `IsFirstSlotOfWindow(slot)`.
  - `specs/tla/alpenglow/Messages.tla:18`–`:26` — `Slots` typing and prefix-closure.
- Where this operator is used and block retrieval requirement is enforced:
  - `specs/tla/alpenglow/MainProtocol.tla:623`–`:631` — `EmitSafeToNotar` requires `b \in blockAvailability[v]` (repair/retrieval) and calls `CanEmitSafeToNotar` with `alreadyVoted` and `votedForB`.

## 3. Reasoning and Mapping to the Whitepaper

- “Already voted in s, but not to notarize b”
  - Implemented by parameters `alreadyVoted` and `~votedForBlock`.
  - At call sites this is computed from validator state/votes (cf. `MainProtocol.tla:623`–`:631`).

- Parent requirement
  - Whitepaper: if `s` is the first slot of the leader window, SafeToNotar may be emitted immediately; otherwise, after retrieving block b to identify its parent, emit only when Pool holds the notar-fallback certificate for the parent.
  - Code: `parentReady == IsFirstSlotOfWindow(slot) \/ (\E ps \in Slots : ps < slot /\ HasNotarFallbackCert(pool, ps, parentHash))`.
    - The existential over `ps < slot` accommodates skipped slots (parent slot can be < s-1) and matches Pool’s `Slots` domain.
    - Use of `HasNotarFallbackCert` (not notarization cert) matches the whitepaper’s specific requirement.
  - Block retrieval is modeled outside this operator: `EmitSafeToNotar` requires `b \in blockAvailability[v]` before invoking this predicate, aligning with the “retrieve b first” clause.

- Threshold inequality
  - Whitepaper formula: notar(b) ≥ 40% OR (skip(s) + notar(b) ≥ 60% AND notar(b) ≥ 20%).
  - Code: `MeetsThreshold(notar, 40) \/ (MeetsThreshold(skip + notar, DefaultThreshold) /\ MeetsThreshold(notar, 20))`.
    - `DefaultThreshold == 60` (Certificates.tla), so this matches exactly.
    - `MeetsThreshold` uses Σ_all stake normalization; no floating-point issues (integer arithmetic).

- What is counted in notar(b) and skip(s)
  - `NotarStake` counts validators who cast an initial `NotarVote` for `(slot, blockHash)`; it deduplicates by validator (enforcing “count once per slot”).
  - `SkipStake` counts validators who cast an initial `SkipVote` for `slot`; also deduplicated by validator.
  - This matches Def. 16’s use of initial vote tallies. Fallback votes are intentionally excluded from these functions to avoid circularity and to adhere to the formula’s semantics.
  - Double-counting across `skip + notar` is prevented by the Pool’s multiplicity rules (Def. 12), enforced by `CanStoreVote`: a validator cannot have both initial skip and initial notarization in the same slot.

- Domain and uniqueness assumptions
  - `Slots` is prefix-closed; quantifying `ps < slot` is well-defined.
  - Block hashes are unique across the block set (see `Blocks.tla:279` `UniqueBlockHashes` and its usage), ensuring that checking `HasNotarFallbackCert(pool, ps, parentHash)` implicitly targets the correct parent slot.

## 4. Conclusion

The operator `CanEmitSafeToNotar` correctly and faithfully implements Whitepaper Definition 16 (SafeToNotar) with:
- Accurate emission preconditions (already voted in s, not for b).
- Correct parent gating: immediate in the first slot of a window; otherwise requires a notar-fallback certificate for the parent, consistent with the text.
- Exact threshold inequality with proper normalization to total stake.
- Proper use of initial-vote-only tallies for `notar(b)` and `skip(s)`, combined with multiplicity rules to enforce count-once-per-slot and prevent double-counting in `skip + notar`.

No correctness discrepancies with the whitepaper were found.

## 5. Open Questions / Concerns

- Does “skip(s)” in Def. 16 include SkipFallbackVote stake?
  - The whitepaper states “skip votes,” which could be interpreted as initial skips only. The code uses only `SkipVote` (initial) in `SkipStake`, which matches the intended, non-circular reading for SafeToNotar. This design choice should be documented explicitly to avoid ambiguity.

- Parent certificate type requirement
  - The whitepaper explicitly requires a notar-fallback certificate for the parent (not a notarization certificate). The code adheres to this. This can delay SafeToNotar slightly if only a NotarizationCert is present and the NotarFallbackCert has not yet been constructed; the model separately ensures certificates are generated once thresholds are met. This is consistent with the spec, but worth calling out as an intentional gate.

- Parent slot quantification
  - The existential `\E ps < slot` relies on hash uniqueness for correctness. Given `UniqueBlockHashes` is maintained, this is fine. If that invariant were relaxed, the check would need the exact parent slot.

## 6. Suggestions for Improvement

- Clarify in comments that `SkipStake` and `NotarStake` intentionally consider only initial votes (SkipVote, NotarVote) for Def. 16 inequalities. Add a short cross-reference to the whitepaper to prevent misinterpretations.

- Optional invariant: add a lightweight property tying together the multiplicity rule and the SafeToNotar arithmetic, e.g., “for all slots, no validator contributes to both `SkipStake` and `NotarStake(_,_,_)`,” to make the “no double-counting across skip+notar” guarantee explicit.

- Optional readability: name the parent gating predicate (e.g., `ParentFallbackReady(pool, slot, parentHash)`) and reuse it where applicable to centralize the Def. 16 gating logic and keep intent clear.

File references for context:
- Operator under audit: `specs/tla/alpenglow/VoteStorage.tla:283`
- Thresholds: `specs/tla/alpenglow/Certificates.tla:48`, `specs/tla/alpenglow/Certificates.tla:95`
- Stake helpers: `specs/tla/alpenglow/VoteStorage.tla:147`, `specs/tla/alpenglow/VoteStorage.tla:155`
- Parent gating pieces: `specs/tla/alpenglow/VoteStorage.tla:227`, `specs/tla/alpenglow/Blocks.tla:192`
- Usage site (ensures block retrieval and state guards): `specs/tla/alpenglow/MainProtocol.tla:623`, `specs/tla/alpenglow/MainProtocol.tla:631`

