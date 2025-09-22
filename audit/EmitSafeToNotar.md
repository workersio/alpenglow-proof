# Audit: EmitSafeToNotar

## 1. Code Under Audit

```
EmitSafeToNotar ==
    /\ \E v \in CorrectNodes, s \in 1..MaxSlot, b \in blocks :
         /\ b.slot = s
         /\ b \in blockAvailability[v]
         /\ LET alreadyVoted == HasState(validators[v], s, "Voted")
                votedForB == VotedForBlock(validators[v], s, b.hash)
            IN CanEmitSafeToNotar(validators[v].pool, s, b.hash, b.parent, alreadyVoted, votedForB)
         /\ ~HasState(validators[v], s, "BadWindow")
         /\ validators' = [validators EXCEPT ![v] = HandleSafeToNotar(@, s, b.hash)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, time, finalized, blockAvailability>>
```

Context and referenced definitions:

- `CorrectNodes`, `MaxSlot`, `blockAvailability`, `validators`, `blocks`: `specs/tla/alpenglow/MainProtocol.tla`.
- `HasState`, `VotedForBlock`, `HandleSafeToNotar`: `specs/tla/alpenglow/VotorCore.tla`.
- `CanEmitSafeToNotar`: `specs/tla/alpenglow/VoteStorage.tla`.

Key referenced implementations:

- `HasState(v, s, "Voted")` and `VotedForBlock(...)`: Votor state helpers (Definition 18 / Algorithm 1/2 alignment).
- `HandleSafeToNotar`: casts notar-fallback vote and sets `BadWindow` after `TrySkipWindow` (Algorithm 1, lines 16–20).
- `CanEmitSafeToNotar(pool, slot, blockHash, parentHash, alreadyVoted, votedForBlock)`:
  - Enforces Definition 16 thresholds: `notar(b) ≥ 40%` OR `(skip(s)+notar(b) ≥ 60% and notar(b) ≥ 20%)`.
  - Requires parent condition: if not first slot of the window, `HasNotarFallbackCert(pool, slot-1, parentHash)` (see concerns below).


## 2. Whitepaper Sections and References

- Definition 10 (Blokstor): storing/repairing blocks; must store `b` before emitting SafeToNotar.
- Definition 15 (Pool events): `ParentReady` criteria.
- Definition 16 (fallback events): SafeToNotar and SafeToSkip thresholds and prerequisites.
- Definition 18 (Votor state): `Voted`, `BadWindow`, `ItsOver` state objects.
- Algorithm 1 (event loop): handling of `SafeToNotar` (lines 16–20) and setting `BadWindow`.
- Definition 12 (storing votes): multiplicity; count-once rule used by stake counters.

Relevant excerpts (page references from `alpenglow-whitepaper.md`):

- Def. 16, p. 21–22: SafeToNotar prerequisites and inequality.
- Parent condition (Def. 16): if not first slot of window, emit after Pool contains notar-fallback certificate for the parent; also, `b` must be locally stored (Blokstor/repair) before emitting.
- Def. 12: Pool stores only the first notar or skip; up to 3 notar-fallback; first skip-fallback; first finalization.
- Alg. 1 lines 16–20: on `SafeToNotar`, call `TRYSKIPWINDOW(s)`; if `ItsOver ∉ state[s]` then broadcast `NotarFallbackVote(s, h(b))` and add `BadWindow`.


## 3. Reasoning vs. Whitepaper

What the code checks and why:

- Slot/block availability:
  - `b.slot = s` and `s ∈ 1..MaxSlot` scope the slot; `b ∈ blockAvailability[v]` enforces “Blokstor must store b before emitting SafeToNotar” (Def. 10, p. 19–20).

- “Node already voted in s, but not to notarize b” (Def. 16):
  - `alreadyVoted == HasState(..., "Voted")` ensures an initial vote (notar or skip) exists for slot `s`.
  - `votedForB == VotedForBlock(..., b.hash)` ensures the initial vote was not for `b`.
  - These are passed to and used by `CanEmitSafeToNotar`.

- Definition 16 inequality and stake accounting:
  - `CanEmitSafeToNotar` computes:
    - `notar(b)`: stake from `NotarVote` for `b` only (correctly excludes fallback votes),
    - `skip(s)`: stake from `SkipVote` in `s` (initial skips only),
    - Applies thresholds: `notar(b) ≥ 40%` OR `(skip(s) + notar(b) ≥ 60% ∧ notar(b) ≥ 20%)`.
  - Stake computations use “count-once per slot” via unique validator sets (Def. 12).

- Parent precondition for non-first slot (Def. 16):
  - The code intends to require the parent’s notar-fallback certificate before emitting SafeToNotar when `s` is not the first slot in its window.
  - Implementation detail: `CanEmitSafeToNotar` checks `HasNotarFallbackCert(pool, slot-1, parentHash)` (see mismatch in Section 5).

- Handler side-effects (Alg. 1 lines 16–20):
  - `HandleSafeToNotar` first calls `TrySkipWindow` (skips unvoted slots in the window), then broadcasts a notar-fallback vote and adds `BadWindow`, provided `ItsOver ∉ state[s]`.
  - The action `EmitSafeToNotar` itself guards with `~HasState(..., "BadWindow")` to avoid re-emitting after a fallback/skip was already cast in `s`. While stricter than the whitepaper’s event-generation text, it preserves safety and matches Algorithm 1 behavior (post-event `BadWindow` prevents finalization in this slot).


## 4. Conclusion

- Thresholds and initial-vote prerequisite match Definition 16 precisely, with correct “count-once” stake semantics.
- Requirement that `b` be in `blockAvailability[v]` aligns with Blokstor/repair prerequisites before emitting SafeToNotar.
- Event handling and state updates (`TrySkipWindow`, add `BadWindow`, create notar-fallback vote) match Algorithm 1 (lines 16–20).
- Material mismatch identified: parent certificate check uses `slot-1` rather than the actual parent’s slot. This can incorrectly block SafeToNotar after skipped slots.
- Minor divergence: gating on `~BadWindow` at emission time is stricter than the whitepaper’s event-generation description but consistent with Algorithm 1 and safe (prevents redundant re-emission).


## 5. Open Questions / Concerns

- Parent slot mismatch (Significant):
  - Whitepaper (Def. 16) requires “Pool contains the notar-fallback certificate for the parent” when `s` is not the first slot of its window.
  - The implementation in `CanEmitSafeToNotar` checks `HasNotarFallbackCert(pool, slot-1, parentHash)`.
  - Since a child block’s parent may be at any earlier slot (`parent.slot < s`), not necessarily `s-1` (whitepaper §2.1; also `ValidParentChild` only requires `<`, not `= s-1`), this check fails whenever the immediate predecessor slot is skipped.
  - Example: parent at slot 4, current slot `s=6`, with a skip cert for slot 5. Pool would hold the parent’s notar-fallback cert at slot 4, not slot 5; the current check at slot 5 incorrectly blocks SafeToNotar.

- Parent certificate type:
  - The code demands a notar-fallback certificate for the parent, which matches the letter of Def. 16. ParentReady (Def. 15) accepts either notarization or notar-fallback; here, only notar-fallback is allowed. This is faithful to Def. 16 but potentially conservative; confirm this is intended.

- `~BadWindow` emission guard:
  - Not explicitly stated in Def. 16, but harmless. It may prevent emitting multiple notar-fallback votes (whitepaper allows Pool to store up to 3 received notar-fallback votes). If multiple emissions were intended (e.g., for robustness), consider relaxing this guard; otherwise document the choice.


## 6. Suggestions for Improvement

- Fix parent certificate gating in `CanEmitSafeToNotar` (recommended):
  - Replace the `slot-1` check with an existence check over prior slots:
    - Parent-aware, pool-only formulation:
      - `parentReady == IsFirstSlotOfWindow(slot) \/ (\E ps \in Slots : ps < slot /\ HasNotarFallbackCert(pool, ps, parentHash))`.
    - Alternatively, if you prefer exactness and MainProtocol is allowed to pass more context, change the function signature to accept `parentSlot` and pass the actual `slot(parent(b))` from `EmitSafeToNotar`.

- Consider documenting (or adjusting) the `~BadWindow` guard at emission time:
  - If the intent is to limit each correct node to at most one notar-fallback emission per slot, keep it and note the rationale.
  - If multiple emissions are desired (whitepaper’s Pool accepts up to 3 received notar-fallback votes), rely on `VoteStorage.CanStoreVote` multiplicity and drop this guard.

- Add a model check scenario for skipped immediate predecessor slot:
  - Construct a trace where `slot(parent(b)) < s-1` and ensure `SafeToNotar` still emits once stake thresholds are met and parent’s notar-fallback is in Pool.

- Optional: Align parent certificate type with ParentReady (if intended):
  - If the intention is to allow `HasNotarizationCert` for parent in this context, generalize the check to `HasNotarizationCert ∨ HasNotarFallbackCert`. The whitepaper for SafeToNotar specifically asks for notar-fallback, so this is a design choice, not a requirement.

---

Prepared for: Alpenglow TLA+ spec audit
Scope: `EmitSafeToNotar` in `specs/tla/alpenglow/MainProtocol.tla` and its dependencies
Date: {{DATE}}

