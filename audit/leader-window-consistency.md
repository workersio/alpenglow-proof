# Audit: Leader Window Consistency and Helpers

- Scope: `specs/tla/alpenglow/Blocks.tla:149`
- Focus: `Leader(slot)`, `FirstSlotOfWindow`, `IsFirstSlotOfWindow`, `LeaderScheduleWindowConsistency`, and related assumptions.

## 1. Code That You Are Auditing

Source (Blocks module): `specs/tla/alpenglow/Blocks.tla:149`

```tla
Leader(slot) ==
    LeaderSchedule[slot]

\* Whitepaper §1.1 and §2.7: each slot has a pre-announced leader chosen
\* via a stake-weighted VRF.

\* Get the first slot of the window containing 'slot'
FirstSlotOfWindow(slot) ==
    IF slot = 0 THEN 0
    ELSE ((slot - 1) \div WindowSize) * WindowSize + 1

\* Check if this slot is the first in its window
IsFirstSlotOfWindow(slot) ==
    slot = FirstSlotOfWindow(slot)

LeaderScheduleWindowConsistency ==
    \A s \in Slots : LeaderSchedule[s] = LeaderSchedule[FirstSlotOfWindow(s)]
        \* Leaders stay fixed across window (§2.7, lines 700-760)

ASSUME LeaderScheduleWindowConsistency
```

Key external references used by this code:

- `LeaderSchedule` (constant, VRF-based slot→leader map): `specs/tla/alpenglow/Blocks.tla:20`
- `WindowSize` (constant, >0): `specs/tla/alpenglow/Blocks.tla:20`
- `Slots`, `Validators` (universe sets): `specs/tla/alpenglow/Messages.tla:14`

Model concretizations (for TLC harness):

- `WindowSize = 2`: `specs/tla/alpenglow/MC_lg.cfg:28`
- `Slots = {0, 1, 2}`: `specs/tla/alpenglow/MC_lg.cfg:39`
- `LeaderSchedule <- MC_LeaderSchedule`: `specs/tla/alpenglow/MC_lg.cfg:43`
- Example schedule: `specs/tla/alpenglow/MC.tla:23`

Downstream usage (sanity):

- Leaders must match `Leader(slot)` when proposing: `specs/tla/alpenglow/MainProtocol.tla:297`
- Window-aware logic (timeouts, proofs) depends on `IsFirstSlotOfWindow`/`WindowSlots`.

## 2. Whitepaper Sections and References Represented

- Leader schedule and windows (VRF, fixed-consecutive-slot responsibility):
  - `alpenglow-whitepaper.md:215` (Leader; per-slot leader; fixed window)
  - `alpenglow-whitepaper.md:222` (VRF before each epoch; public schedule)
- First-slot semantics (ParentReady only for first in a window):
  - `alpenglow-whitepaper.md:613`
- Window iteration utilities and usage (WINDOWSLOTS, settimeouts, skip loops):
  - `alpenglow-whitepaper.md:678`
  - `alpenglow-whitepaper.md:681`
  - `alpenglow-whitepaper.md:706`
- Algorithm 3 (block creation for a leader window):
  - `alpenglow-whitepaper.md:759`
- Empirical parameter (example window size):
  - `alpenglow-whitepaper.md:1257` (table row: Blocks per leader window w = 4)

## 3. Reasoning: What The Code Encodes vs. What The Paper Claims

- Abstraction of leader schedule
  - Code: `Leader(slot) == LeaderSchedule[slot]` treats the schedule as a given total function `Slots → Validators`.
  - Paper: Leader is determined by a threshold/stake-weighted VRF before each epoch; the schedule is public and per-slot (`:215`, `:222`).
  - Alignment: Abstracting the VRF machinery into an uninterpreted function is appropriate for this level; properties of the schedule (e.g., window constancy) must be assumed or derived separately.

- Window arithmetic and first-slot predicate
  - Code: `FirstSlotOfWindow` computes the first index of the window containing `slot` as a 1-based partition for `slot ≥ 1`, with a special case for `slot = 0` mapping to `0`.
    - For `WindowSize = W`, slots `1..W` map to first slot `1`; `W+1..2W` map to `W+1`, etc. Slot `0` is a singleton base case.
  - Paper: Leaders are “in charge for a fixed amount of consecutive slots” (window) and first-slot semantics are special (ParentReady gating; `:613`).
  - Alignment: The function precisely encodes fixed-size consecutive windows and the first-slot test needed by Algorithm 1/3.

- Window-constant leader property
  - Code: `LeaderScheduleWindowConsistency == ∀ s ∈ Slots : LeaderSchedule[s] = LeaderSchedule[FirstSlotOfWindow(s)]`, then `ASSUME`d.
  - Paper: A leader remains responsible for all slots in its window (fixed-length, consecutive). Implicitly, the mapping from slots to leaders is constant across the window (`:215`–`:222`), and algorithms treat windows as a unit (`:678`, `:759`).
  - Alignment: The assumption captures the intended semantics directly and is used by multiple parts of the protocol (timeouts across the window, optimistic building, liveness proof binders).

- Genesis / slot 0 special-casing
  - Code: `FirstSlotOfWindow(0) = 0` creates a singleton “window” for genesis. Other windows begin at 1 and increment by `WindowSize`.
  - Paper: The text treats the protocol from the first operational window; genesis specifics are not normative. `MainProtocol` seeds ParentReady at slot 1 to start the first real window.
  - Alignment: Treating slot 0 specially is a modeling convenience that preserves the semantics of the first real window without changing window behavior for `slot ≥ 1`.

## 4. Conclusion of the Audit

- The snippet correctly abstracts the whitepaper’s notion of leader windows:
  - Per-slot leaders determined by a (pre-announced) schedule (VRF-based in the paper) are modeled via `LeaderSchedule`.
  - Fixed-size consecutive windows are computed by `FirstSlotOfWindow`, with `IsFirstSlotOfWindow` for first-slot gating.
  - The “same leader across a window” rule is captured by the `LeaderScheduleWindowConsistency` assumption, matching the paper’s window semantics and enabling subsequent protocol logic (timeouts across window; Algorithm 3).
- Boundary behavior is consistent with the rest of the spec and the paper’s intent:
  - Slot `0` is handled as a convenient base case; slot `1` is the first operational window’s start (ParentReady seeded in init of `MainProtocol`).
- Overall, the code accurately reflects the whitepaper’s abstractions for leader windows at the intended level, with the appropriate choice to keep VRF/stake details out of this module.

## 5. Open Questions or Concerns

- Assumed vs. derived window-constancy
  - The property is `ASSUME`d. While faithful to the paper, relying on an assumption can mask misconfigurations. In some contexts, deriving it from the construction of `LeaderSchedule` (see Suggestions) would strengthen the model.

- Domain safety for `FirstSlotOfWindow`
  - The formula indexes `LeaderSchedule[FirstSlotOfWindow(s)]`. This is safe if `FirstSlotOfWindow(s) ∈ Slots` for all `s ∈ Slots` (true when `Slots` is a contiguous initial segment of `Nat`). Consider asserting or documenting this explicitly.

- Window base index choice
  - The window arithmetic is 1-based for `slot ≥ 1` and special-cases `0`. This is coherent with `MainProtocol` but should be consistently assumed elsewhere (e.g., any module that manually reasons about windows).

- Reference granularity
  - The comment mentions “§2.7, lines 700–760”; in the repo’s markdown, relevant anchors are around `:678` and `:759`. Consider tightening cross-references for precision.

## 6. Suggestions for Improvement

- Prefer constructive schedule over assumption
  - Define a window-level leader function and build `LeaderSchedule` from it, eliminating the need to `ASSUME` window-constancy, e.g.:
    ```tla
    WindowIndex(slot) == IF slot = 0 THEN 0 ELSE (slot - 1) \div WindowSize
    WindowLeader == [k \in Nat |-> CHOOSE v \in Validators : TRUE]
    LeaderSchedule == [s \in Slots |-> WindowLeader[WindowIndex(s)]]
    ```
    Then `\A s ∈ Slots : Leader(s) = Leader(FirstSlotOfWindow(s))` becomes a theorem, not an assumption.

- Add a domain-closure assumption for slots
  - To ensure safe indexing throughout, add (in `Messages.tla` or a higher module):
    ```tla
    ASSUME \A s \in Slots : 0..s \subseteq Slots
    ```
    or simply define `Slots == 0..MaxSlot` where applicable.

- Provide a helper `WindowIndex`
  - Encapsulate the window index to avoid duplicating the `((slot-1) \div W)` idiom and to make window-based proofs clearer.

- Tighten whitepaper references in comments
  - Update inline comments to point to concrete line anchors present in `alpenglow-whitepaper.md` (e.g., `:215`, `:613`, `:678`, `:759`) for easy navigation.

- Optional: assert type/totality facts
  - Add type invariants such as `WindowSize ∈ Nat \ {0}` (already present), `LeaderSchedule ∈ [Slots → Validators]` (present), and optionally `FirstSlotOfWindow(s) ∈ Slots` to make model-checking failures crisper if configurations drift.

