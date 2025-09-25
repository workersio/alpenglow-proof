# Audit: HandleSafeToNotar (Algorithm 1, lines 16–20)

1. Code that you are auditing

```
HandleSafeToNotar(validator, slot, blockHash) ==
    LET skipResult == TrySkipWindow(validator, slot)
    IN
        IF ~HasState(skipResult, slot, "ItsOver") THEN
            LET vote == CreateNotarFallbackVote(skipResult.id, slot, blockHash)
                newValidator == AddState(skipResult, slot, "BadWindow")
                poolWithVote == StoreVote(newValidator.pool, vote)
            IN [newValidator EXCEPT !.pool = poolWithVote]
        ELSE skipResult
```

Defined at: `specs/tla/alpenglow/VotorCore.tla` (event handlers section)

2. Whitepaper section and references that the code represents

- Definition 16 (fallback events): alpenglow-whitepaper.md:554–:569 (pp. 21–22)
  - SafeToNotar(s, hash(b)) prerequisites and inequality:
    - Node already voted in slot s, but not to notarize b
    - notar(b) ≥ 40% OR (skip(s)+notar(b) ≥ 60% AND notar(b) ≥ 20%)
    - If s is not the first slot of the window, emit only after Pool contains a notar-fallback certificate for the parent block
  - Block availability before emitting SafeToNotar (repair procedure): :470, :569
- Algorithm 1 (Votor, event handlers): alpenglow-whitepaper.md:651–:665
  - Lines 16–20 for SafeToNotar(s, hash(b)):
    - TRYSKIPWINDOW(s)
    - If ItsOver ∉ state[s]: broadcast NotarFallbackVote(s, hash(b)); state[s] ← state[s] ∪ {BadWindow}
- Definition 12 (storing votes): alpenglow-whitepaper.md:513–:518 (multiplicity limits; up to 3 NotarFallback votes)
- Definition 18 (Votor state): alpenglow-whitepaper.md:615–:630 (state items: ItsOver, BadWindow, etc.)
- Lemma 22 (no mixing finalization with fallback in same slot): alpenglow-whitepaper.md:845–:849

3. Reasoning behind the code and what the whitepaper claims

- Separation of concerns (emit vs. handle):
  - The emitter `EmitSafeToNotar` (in `MainProtocol.tla`) enforces Definition 16’s guards before calling this handler: node already voted in s, not for b; inequality threshold; parent’s notar-fallback if s is not first slot; and local availability of block b.
  - This handler assumes those preconditions and performs the Algorithm 1 side effects.

- Step-by-step mapping to Algorithm 1, lines 16–20:
  - TRYSKIPWINDOW(s): `skipResult == TrySkipWindow(validator, slot)` ensures all unvoted slots in the same window are first-voted-to-skip and marked BadWindow, matching line 17.
  - If ItsOver ∉ state[s]: `~HasState(skipResult, slot, "ItsOver")` prevents casting fallback after a finalization vote, per lines 18–19 and Lemma 22.
  - Broadcast NotarFallbackVote(s, hash(b)): `CreateNotarFallbackVote(...)` with `StoreVote(...)` records the notar-fallback vote in Pool obeying Definition 12 multiplicity limits.
  - state[s] ← state[s] ∪ {BadWindow}: `AddState(..., "BadWindow")` marks that a fallback/skip activity occurred in this slot, which (together with `TryFinal` requiring `~BadWindow`) prevents later finalization voting in the same slot, as required by Lemma 22.

- External references in this operator and their semantics:
  - `TrySkipWindow`: `specs/tla/alpenglow/VotorCore.tla` — casts `SkipVote` on all unvoted slots in current window and marks `BadWindow` for each, also clearing `pendingBlocks` for them. Implements Algorithm 2, lines 22–27.
  - `HasState`, `AddState`: `specs/tla/alpenglow/VotorCore.tla` — state membership and additive updates over per-slot flags (Definition 18).
  - `CreateNotarFallbackVote`: `specs/tla/alpenglow/Messages.tla` — constructs the fallback vote message (Definition 11 / Table 5).
  - `StoreVote`: `specs/tla/alpenglow/VoteStorage.tla` — records vote in Pool subject to Definition 12 multiplicity rules (first initial vote, up to 3 notar-fallback, etc.).

- Safety and liveness alignment:
  - Safety: The handler never issues a fallback vote after `ItsOver`, and it sets `BadWindow` when a fallback vote is cast, thereby preventing a subsequent finalization vote in the same slot (enforced by `TryFinal` requiring `~BadWindow`). This encodes both directions of Lemma 22.
  - Liveness: `TrySkipWindow` ensures windows make progress by placing skip votes for missed initial votes; emitting a notar-fallback when SafeToNotar holds ensures the protocol quickly accumulates threshold for notar/slow-finalization path when the 80% fast path is not possible.

4. Conclusion of the audit

- HandleSafeToNotar correctly and precisely implements Algorithm 1 (lines 16–20) under Definition 16’s preconditions, which are enforced at emission time in `EmitSafeToNotar`.
- State updates `BadWindow` and the guard against `ItsOver` match Lemma 22’s constraints, preventing any mixing of fallback and finalization votes in the same slot.
- Vote creation and storage are delegated to modules that encode Definition 11/12, preserving type/multiplicity correctness.
- The design cleanly separates event-condition checking (in `MainProtocol.tla`) from side effects (in `VotorCore.tla`), consistent with the whitepaper’s structure.

5. Open questions or concerns

- Parent certificate type for emission: Definition 16 text explicitly requires a notar-fallback certificate for the parent (not “notarization or notar-fallback”). The model’s `GenerateCertificate` always emits a `NotarFallbackCert` whenever a `NotarizationCert` is creatable, so `CanEmitSafeToNotar`’s check for `HasNotarFallbackCert` is satisfied if a notarization exists. This is consistent, but worth noting as an implicit modeling choice aligning with the paper’s cascading implication.
- Redundancy vs. multiplicity: The handler emits at most one notar-fallback per validator per slot due to the `BadWindow` guard in `EmitSafeToNotar`, while the Pool allows up to 3 notar-fallback votes (Definition 12). This is fine (the multiplicity limit defends against adversarial behavior and late duplicates), but means honest nodes will typically use only one of the allowed three.

6. Suggestions for improvement

- Add a simple invariant capturing Lemma 22 directly at the validator level, e.g.: for all validators v and slots s, `HasState(v, s, "ItsOver") => ~HasState(v, s, "BadWindow")` and vice versa. The behavior already enforces this, but an explicit invariant would improve proof clarity.
- Optionally annotate `HandleSafeToNotar` with a comment citing Algorithm 1, lines 16–20 and Definition 16 to mirror the in-file references seen elsewhere (the EmitSafeToNotar site already cites them).
- Consider (non-functional) logging/trace variable for emitted fallback vote types to aid debugging/tracing in model checking runs, without changing semantics.

