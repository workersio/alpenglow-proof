# Audit: VotorCore.ValidatorState structure

1. Code that you are auditing.

```tla
ValidatorState == [
    id: Validators,                                  \* Validator identifier
    state: [Slots -> SUBSET StateObject],           \* State flags per slot
    parentReady: [Slots -> BlockHashes \cup {NoBlock}], \* Parent hash per slot
    pendingBlocks: [Slots -> SUBSET Block],         \* Blocks to retry
    pool: PoolState,                                \* Vote/certificate storage
    clock: Nat,                                     \* Local clock
    timeouts: [Slots -> Nat]                        \* Scheduled timeouts
]
```

File reference: `specs/tla/alpenglow/VotorCore.tla:55`

2. The whitepaper section and references that the code represents.

- §2.5, Definition 18 (Votor state): slot-scoped state objects and memory; `state[slot]` and the presence of ParentReady/Voted/VotedNotar/BlockNotarized/ItsOver/BadWindow. `alpenglow-whitepaper.md:615`.
- §2.5, Definition 15 (Pool events): ParentReady and BlockNotarized events that drive state; `alpenglow-whitepaper.md:543-552`.
- §2.5, Definition 16 (Fallback events): conditions that mark BadWindow; `alpenglow-whitepaper.md:554-569`.
- §2.5, Definition 17 (Timeout): timeout scheduling formula; local clock; `alpenglow-whitepaper.md:602-613`.
- Algorithm 1 (Votor event loop): Block, Timeout, BlockNotarized, ParentReady, SafeToNotar, SafeToSkip; use of `pendingBlocks` and clearing on actions; `alpenglow-whitepaper.md:632-660`.
- Algorithm 2 (helpers): TRYNOTAR/TRYFINAL/TRYSKIPWINDOW/CHECKPENDINGBLOCKS semantics that interact with these fields; `alpenglow-whitepaper.md:660-760`.
- §2.4 (Votes & Certificates: Types/thresholds) and §2.5 (Pool): justifying `pool: PoolState`; `alpenglow-whitepaper.md:509-532`.
- §2.1 (Blocks): type of `Block`; `alpenglow-whitepaper.md:351-363`.

3. The reasoning behind the code and what the whitepaper claims.

- id: Validators
  - Meaning: identity of the validator whose local Votor state this record represents.
  - Source: Validators are a global set of nodes; `Messages.tla:16-20` establishes the type; the whitepaper treats nodes/validators as principals throughout §2.

- state: [Slots -> SUBSET StateObject]
  - Meaning: per-slot set of state flags the validator has “permanently added” (Definition 18). Implemented as a set of tags rather than parameterized objects, with associated values stored elsewhere (see `parentReady` and Pool queries).
  - Source: Definition 18 enumerates ParentReady, VotedNotar(h), BlockNotarized(h), ItsOver, BadWindow; `alpenglow-whitepaper.md:615-632`.
  - Implementation note: Parameterized flags (ParentReady(h), VotedNotar(h)) are tracked by combining a boolean tag in `state` with the corresponding hash in either `parentReady[slot]` or a Pool lookup (e.g., `VotedForBlock`). This preserves the abstraction while simplifying the state set.

- parentReady: [Slots -> BlockHashes ∪ {NoBlock}]
  - Meaning: records the parent hash tied to the ParentReady flag for the first slot of a leader window. Initialized to `NoBlock` and set when `ParentReady(s, hash(b))` is emitted (Definition 15) for the first slot s of a window, consistent with Definition 17 scheduling.
  - Source: Definition 15 (ParentReady) and its first-slot restriction; Definition 17 uses this to set timeouts; `alpenglow-whitepaper.md:545-552, 602-613`.
  - Usage in code: TRYNOTAR for first-slot requires `ParentReady ∈ state[s]` and `parentReady[s] = block.parent`; `specs/tla/alpenglow/VotorCore.tla:113-119`.

- pendingBlocks: [Slots -> SUBSET Block]
  - Meaning: blocks to retry per slot when initial preconditions fail; aligns with “pendingBlocks are blocks which will be revisited to call TRYNOTAR()” (Algorithm 1 lines 1–5, 28–30).
  - Source: Algorithm 1; `alpenglow-whitepaper.md:632-660`.
  - Implementation note: The spec generalizes the whitepaper’s single optional pending block per slot to a set of pending blocks per slot, to model receipt of multiple competing proposals for the same slot. See concerns below about clearing semantics.

- pool: PoolState
  - Meaning: per-validator vote/certificate storage and event generator (Definitions 12, 13, 15, 16). `PoolState` captures votes/certificates per slot and enforces multiplicity and uniqueness rules.
  - Sources: Definitions 12–16; `alpenglow-whitepaper.md:511-569`.
  - Cross-refs: `specs/tla/alpenglow/VoteStorage.tla:24-33` defines `PoolState`; multiplicity rules `:54-80`; certificate uniqueness `:109-120` and `:116-120` (notar types must share one block per slot).

- clock: Nat and timeouts: [Slots -> Nat]
  - Meaning: the validator’s local time and per-slot scheduled timeout instants, respectively.
  - Source: “Time” and “Timeout” text and Definition 17; schedule `Timeout(i)` at `clock() + Δ_timeout + (i - s + 1) * Δ_block` for `i ∈ WINDOWSLOTS(s)`; `alpenglow-whitepaper.md:211, 224, 602-613`.
  - Cross-refs: `HandleParentReady` computes timeouts exactly per the formula using `DeltaTimeout` and `DeltaBlock`; `specs/tla/alpenglow/VotorCore.tla:171-186`.

4. The conclusion of the audit.

- The `ValidatorState` record captures the validator-local state required by the whitepaper’s Votor (Definitions 15–18) with correct typing and module boundaries:
  - Identity, per-slot state flags, parent hash for ParentReady, pending block(s) to retry, Pool for votes/certificates, and time/timeout bookkeeping.
  - Types align with imported modules: `Validators, Slots, BlockHashes, NoBlock` (`Messages.tla:16-28`), `Block` (`Blocks.tla:47-52`), `PoolState` (`VoteStorage.tla:24-27`), and `Nat` (Naturals).
  - The surrounding module uses these fields in ways that match Algorithm 1–2: TRYNOTAR/TRYFINAL/TRYSKIPWINDOW/timeout scheduling mirror the whitepaper guards and effects.

- Two deliberate representation choices differ from the whitepaper’s presentation but preserve behavior:
  1) Parameterized state objects (e.g., `ParentReady(h)`, `VotedNotar(h)`) are decomposed into a boolean tag in `state` plus the associated hash in `parentReady[slot]` or via Pool queries. This is behaviorally equivalent under the module’s invariants (ParentReady arises solely from Pool and Pool enforces notarization uniqueness per slot; `VoteStorage.tla:109-120`).
  2) `pendingBlocks` is a set per slot rather than a single optional block. The model attempts to notarize one pending block when conditions change and prevents further initial votes once `Voted ∈ state[s]`, keeping any remaining pending entries inert. This generalization does not enable incorrect voting but see cleanup semantics below.

Overall, the structure is faithful to the whitepaper’s abstractions and sufficiently typed to support Votor’s guards and transitions.

5. Any open questions or concerns.

- Pending blocks clearing semantics vs. paper:
  - Whitepaper Algorithm 2, line 14 and Algorithm 1, line 27 set `pendingBlocks[s] ← ⊥` after a successful notar vote or skip, respectively (`alpenglow-whitepaper.md:742-760`). In the current spec, TRYNOTAR removes only the specific block from `pendingBlocks[s]` rather than clearing the entire set; `specs/tla/alpenglow/VotorCore.tla:120-127`. While harmless (further initial votes are prevented by `Voted`), stale entries may persist and complicate invariants or liveness reasoning.

- Linkage between `state` flags and their parameters:
  - `VotedNotar(h)` and `BlockNotarized(h)` are represented as unparameterized flags in `state`. Correctness relies on using the event-provided `blockHash` and Pool queries (`VotedForBlock`) to bind these flags to the right `h`. This is sound if Pool enforces a single notarized block per slot (it does), but the invariant is implicit.

- Monotonic clock progression is not enforced:
  - `AdvanceClock` writes `clock := newTime` without checking monotonicity. The whitepaper assumes a local, monotonic time source (§2, “Time”); the model would benefit from guarding or asserting `newTime ≥ clock`.

- Domain discipline for `pendingBlocks`:
  - The model writes blocks to `pendingBlocks[s]` only for their own slot, but there is no explicit invariant `∀ b ∈ pendingBlocks[s]: b.slot = s`. Adding it would document and enforce intended usage.

- Unused state flag:
  - `"BlockSeen"` exists in `StateObject` but is not referenced in the handlers. If intentional (future extension), consider documenting its status; otherwise remove to reduce confusion.

6. Any suggestions for improvement.

- Align pending clearing with the whitepaper:
  - On successful TRYNOTAR, clear all `pendingBlocks[slot]` to `{}` (empty set) to mirror `⊥` in the paper; similarly already done in TRYSKIPWINDOW. This maintains a closer 1:1 mapping and simplifies invariants like “no pending after initial vote”.

- Add explicit invariants binding unparameterized flags to Pool state:
  - Example invariants in `VotorCore.tla`:
    - If `HasState(v, s, "BlockNotarized")` then `\E h ∈ BlockHashes : HasNotarizationCert(v.pool, s, h)`.
    - If `HasState(v, s, "VotedNotar")` then `\E h ∈ BlockHashes : VotedForBlock(v, s, h)`.
  - These make the equivalence to `BlockNotarized(h)`/`VotedNotar(h)` explicit.

- Guard clock advancement:
  - In `AdvanceClock`, assert or require `newTime ≥ validator.clock`. Optionally add an invariant that `timeouts[s] = 0 ∨ timeouts[s] > clock` to document “not scheduled or in the future” property after scheduling (Definition 17 guarantee; `alpenglow-whitepaper.md:613`).

- Document domain invariants for pending blocks:
  - Add `∀ s ∈ Slots: ∀ b ∈ validator.pendingBlocks[s]: b.slot = s`. This makes it easier to reason about `CHECKPENDINGBLOCKS` correctness.

- Optional: represent ParentReady with parameter
  - To mirror Definition 18 exactly, you could represent `ParentReady(h)` directly in `state` (e.g., as a tuple) and drop `parentReady[slot]`. The current split is fine; this is purely stylistic.

- Optional: memory hygiene
  - Consider clearing `pendingBlocks[s]` on `ItsOver` and when the window completes, to avoid accumulating inert entries in long-running simulations.

Cross-module references for this structure:

- `Messages.tla:16-28` — `Validators`, `Slots`, `BlockHashes`, `NoBlock`
- `Blocks.tla:47-52` — `Block`
- `VoteStorage.tla:24-33` — `PoolState`; related rules: multiplicity (`:54-80`), certificate uniqueness (`:109-120`)
- `VotorCore.tla:65-74` — `InitValidatorState` aligns types/initial values with the whitepaper’s initial state (`state[·] = ∅`, `parentReady = NoBlock`, `pendingBlocks = ∅`, timers unset)

Whitepaper anchors used in this audit:

- `alpenglow-whitepaper.md:509-569` — Pool (Defs. 12–16)
- `alpenglow-whitepaper.md:602-613` — Timeouts (Def. 17)
- `alpenglow-whitepaper.md:615-632` — Votor state (Def. 18)
- `alpenglow-whitepaper.md:632-660` — Algorithm 1 (event loop)
- `alpenglow-whitepaper.md:660-760` — Algorithm 2 (helpers)
- `alpenglow-whitepaper.md:351-363` — Blocks (Def. 3–5)

