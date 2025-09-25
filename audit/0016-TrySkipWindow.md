# Audit: TrySkipWindow — Skip Unvoted Slots in Window

## 1. Code That You Are Auditing

```tla
TrySkipWindow(validator, slot) ==
    LET windowSlots == WindowSlots(slot)
        slotsToSkip == {s \in windowSlots : 
                        s \in Slots /\ ~HasState(validator, s, "Voted")}
    IN
        IF slotsToSkip # {} THEN
            LET RECURSIVE SkipSlots(_,_)
                SkipSlots(val, slots) ==
                    IF slots = {} THEN val
                    ELSE 
                        LET s == CHOOSE x \in slots : TRUE
                            vote == CreateSkipVote(val.id, s)
                            newVal1 == AddState(val, s, "Voted")
                            newVal2 == AddState(newVal1, s, "BadWindow")
                            poolWithVote == StoreVote(newVal2.pool, vote)
                            updatedVal == [newVal2 EXCEPT 
                                          !.pool = poolWithVote,
                                          !.pendingBlocks[s] = {}]
                        IN SkipSlots(updatedVal, slots \ {s})
            IN SkipSlots(validator, slotsToSkip)
        ELSE validator
```

Reference in repo: `specs/tla/alpenglow/VotorCore.tla:163`.

## 2. Whitepaper Sections and References

- Algorithm 2 — helper functions: `alpenglow-whitepaper.md:676`
- TRYSKIPWINDOW(s) pseudo-code (lines 22–27): `alpenglow-whitepaper.md:705`
- Definition 18 (Votor state) — Voted, BadWindow, pendingBlocks: `alpenglow-whitepaper.md:615`, `alpenglow-whitepaper.md:630`
- Definition 17 (Timeout, WINDOWSLOTS): `alpenglow-whitepaper.md:607`
- Definition 12 (storing votes) — multiplicity constraints: `alpenglow-whitepaper.md:513`

Related spec references used by this definition:
- `WindowSlots` window computation: `specs/tla/alpenglow/Blocks.tla:211`
- `Slots` constant: `specs/tla/alpenglow/Messages.tla:18`
- `HasState`, `AddState`, `pendingBlocks` structure: `specs/tla/alpenglow/VotorCore.tla:81`, `specs/tla/alpenglow/VotorCore.tla:85`, `specs/tla/alpenglow/VotorCore.tla:59`
- `CreateSkipVote` constructor: `specs/tla/alpenglow/Messages.tla:82`
- `StoreVote` with Definition 12 multiplicity: `specs/tla/alpenglow/VoteStorage.tla:84`

## 3. Reasoning (Spec vs. Whitepaper)

What the paper specifies (Alg. 2, lines 22–27):
- For k ∈ WINDOWSLOTS(s): if Voted ∉ state[k], broadcast SkipVote(k); set state[k] ← state[k] ∪ {Voted, BadWindow}; clear pendingBlocks[k]. This bulk-skips all unvoted slots in the current leader window. The routine is triggered by Timeout(s) and before fallback votes (Alg. 1 lines 6–8, 16–25).

How the spec matches:
- Window scope: `windowSlots == WindowSlots(slot)` correctly selects all slots in s’s window; implementation additionally ensures k ∈ Slots and excludes genesis (via `WindowSlots` restricting to s ≥ 1).
- Skip eligibility: `slotsToSkip == { s ∈ windowSlots : s ∈ Slots ∧ ¬HasState(validator, s, "Voted") }` directly matches the “if Voted ∉ state[k]” guard.
- Vote emission and state updates: For each chosen `s`, the spec constructs a skip vote (`CreateSkipVote(val.id, s)`), sets `Voted` and `BadWindow` for that slot, stores the vote (`StoreVote`), and clears `pendingBlocks[s]` to “won’t vote notar after skip,” exactly as per Alg. 2 lines 25–27 and the Definition 18 description of BadWindow.
- Multiplicity safety: The call order `AddState(..., "Voted")` followed by `StoreVote` aligns with Lemma 20’s intent and Definition 12; even if re-entered, the `~HasState(..., "Voted")` filter yields idempotence, and `StoreVote` enforces “one initial vote per slot”.
- Trigger context: This helper is invoked by Timeout(s) and both fallback handlers prior to casting fallback votes: see `HandleTimeout`, `HandleSafeToNotar`, `HandleSafeToSkip` in `specs/tla/alpenglow/VotorCore.tla:236`, `:277`, `:293`, matching Alg. 1 lines 6–8, 16–25 in the whitepaper.

Subtleties and invariants considered:
- Slot domain: `WindowSlots` ensures only production slots (≥1) are considered, avoiding genesis, consistent with the paper’s scheduling narrative.
- Local vs pool state: The guard uses local `state` (self-voting history) per Definition 18, not pool contents; this is correct since the restriction is about the node’s own initial vote.
- BadWindow semantics: The whitepaper defines BadWindow as present in a slot where the node cast skip, skip-fallback, or notar-fallback; setting it here for each skipped slot is precise and later used by `TryFinal` to prevent finalization when any fallback path was taken for that slot.
- Termination: Finite set recursion over `slotsToSkip` is well-founded; repeated calls are safe and no-ops after first application because flags are set.

## 4. Conclusion of the Audit

- The TLA+ definition `TrySkipWindow` accurately implements Algorithm 2 (TRYSKIPWINDOW) lines 22–27 and adheres to Definitions 12, 17, and 18. The guards, state transitions, vote construction, and pending-block clearing match the whitepaper’s abstraction. Cross-module references (`WindowSlots`, `CreateSkipVote`, `StoreVote`, `HasState`/`AddState`) are correct and typed.
- No correctness violations found relative to the whitepaper; the routine is idempotent and composes correctly with Timeout and fallback handlers.

## 5. Open Questions or Concerns

- Event/broadcast linkage: The helper stores votes locally; broadcasting is modeled separately (`BroadcastLocalVote` in MainProtocol). This separation matches the model’s structure, but readers may benefit from a brief note near `TrySkipWindow` acknowledging that emission to the network is handled elsewhere.
- Window domain vs model bounds: The helper uses `Slots` from constants, not `1..MaxSlot` (used in the main system driver). This is fine within module typing, but it’s worth confirming that verification scenarios consistently restrict to the intended finite prefix when `MaxSlot` is in play.

## 6. Suggestions for Improvement

- Add a small lemma to document the intended effect and idempotence, aiding proofs and reader confidence. For example:
  - “After `TrySkipWindow(v, s)`, for all k ∈ WindowSlots(s) with ¬HasState(v, k, "Voted") initially, the resulting state satisfies HasState(v, k, "Voted") ∧ HasState(v, k, "BadWindow") and `pendingBlocks[k] = {}`.”
  - “`TrySkipWindow` is idempotent: applying it twice yields the same state (modulo pool multiplicity rules), leveraging Definition 12 and the Voted guard.”
- Inline cross-reference comment: Add a one-line comment in `TrySkipWindow` with the whitepaper anchor “Alg. 2 lines 22–27” and the definition anchors (Def. 18 for `BadWindow`, Def. 12 for `StoreVote`) to ease maintenance.
- Optional type guard: Prepend an assertion comment or assumption that `validator.id ∈ Validators` (already implied by `ValidatorStateOK`) to make the typing of `CreateSkipVote` calls explicit for readers auditing the module in isolation.

