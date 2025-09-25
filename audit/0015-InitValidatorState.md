**InitValidatorState (VotorCore)**

1. Code Under Audit

```tla
InitValidatorState(validatorId) == [
    id |-> validatorId,
    state |-> [s \in Slots |-> {}],
    parentReady |-> [s \in Slots |-> NoBlock],
    pendingBlocks |-> [s \in Slots |-> {}],
    pool |-> InitPool,
    clock |-> 0,
    timeouts |-> [s \in Slots |-> 0]
]
```

2. Whitepaper Mapping (Sections & Anchors)

- Votor state objects and empty initialization: Definition 18 — state per slot starts empty; lists ParentReady, Voted, VotedNotar, BlockNotarized, ItsOver, BadWindow (alpenglow-whitepaper.md:615).
- Pending block initialization: “pendingBlocks initialized to bottom (⊥)” (alpenglow-whitepaper.md:632).
- Pool events (ParentReady) that drive readiness and timeout scheduling (alpenglow-whitepaper.md:543).
- Local clocks and timeout scheduling across a leader window: narrative and Definition 17 (alpenglow-whitepaper.md:602, alpenglow-whitepaper.md:607).
- Pool semantics the validator starts with (votes/certificates, Def. 12–13) (alpenglow-whitepaper.md:513, alpenglow-whitepaper.md:520).

Related spec references in this repo for context:

- State object universe and ValidatorState record (specs/tla/alpenglow/VotorCore.tla:41, specs/tla/alpenglow/VotorCore.tla:55).
- This initializer definition location (specs/tla/alpenglow/VotorCore.tla:66).
- Messages constants used here: `Slots`, `NoBlock` (specs/tla/alpenglow/Messages.tla:16, specs/tla/alpenglow/Messages.tla:24, specs/tla/alpenglow/Messages.tla:28).
- Pool state and `InitPool` (specs/tla/alpenglow/VoteStorage.tla:30).
- Block record type used in `pendingBlocks` (specs/tla/alpenglow/Blocks.tla:47).
- Window slots exclude slot 0 (used later for timeout scheduling) (specs/tla/alpenglow/Blocks.tla:211).
- How this initializer is used at system boot (slot 1 ParentReady by fiat) (specs/tla/alpenglow/MainProtocol.tla:165, specs/tla/alpenglow/MainProtocol.tla:167).

3. Reasoning: What the Code Encodes vs. Whitepaper Claims

- id |-> validatorId
  - Purpose: Identify the validator whose local state this record models.
  - Typing: `validatorId ∈ Validators` is ensured by callers (MainProtocol initializes over `v ∈ Validators`). Matches the pervasive use of validator IDs in messages and votes.

- state |-> [s ∈ Slots |-> {}]
  - Whitepaper: Definition 18 states per-slot state starts empty; then opaque objects like ParentReady, Voted, VotedNotar(hash(b)), BlockNotarized(hash(b)), ItsOver, BadWindow may be added.
  - Model choice: Here, the per-slot “state” is a set of flag-like tags from `StateObject`. The parameter payloads (e.g., the hash arguments in ParentReady or VotedNotar) are modeled outside this set (see parentReady below and pool lookups). This preserves the guard logic of Algorithm 1/2 while keeping the set closed over a fixed universe (specs/tla/alpenglow/VotorCore.tla:41, specs/tla/alpenglow/VotorCore.tla:55).

- parentReady |-> [s ∈ Slots |-> NoBlock]
  - Whitepaper: ParentReady(s, hash(b)) indicates readiness to notarize blocks in the first slot of a window whose parent is b (Definition 15). Definition 18 bundles this info into the `ParentReady(hash(b))` object in state.
  - Model choice: Split representation: a boolean-ish tag `"ParentReady"` inside `state[s]` plus a separate per-slot map `parentReady[s]` holding the actual parent hash (or `NoBlock` as sentinel). Guards that require both the fact and the parent (e.g., TryNotar’s first-slot case) conjunct on the flag and check `parentReady[s]` equals the candidate’s `parent` (specs/tla/alpenglow/VotorCore.tla:115–118). This is a standard TLA+ technique to avoid mixing parameterized tags into a fixed enum.
  - Initialization to `NoBlock` cleanly expresses “no readiness recorded yet” and respects `NoBlock ∉ BlockHashes` (specs/tla/alpenglow/Messages.tla:28).

- pendingBlocks |-> [s ∈ Slots |-> {}]
  - Whitepaper: Def. 18 uses a single pending block per slot with ⊥ sentinel (alpenglow-whitepaper.md:632).
  - Model choice: Use a set of `Block` per slot, initialized empty. Combined with MainProtocol’s `BlockSeen` guard (only first “Block(...)” event per slot is consumed; specs/tla/alpenglow/MainProtocol.tla:186, specs/tla/alpenglow/VotorCore.tla:48), this set will be empty or singleton in normal operation, preserving the intended semantics. The set form accommodates potential extensions where multiple candidates need revisiting without complicating the type.
  - CheckPendingBlocks processes at most one pending block per slot per pass (consistent with Algorithm 1’s single reference), and TryNotar removes a block from the set when a vote is cast (specs/tla/alpenglow/VotorCore.tla:200–204, specs/tla/alpenglow/VotorCore.tla:121–129).

- pool |-> InitPool
  - Whitepaper: Pool definitions (Def. 12 and 13) prescribe how votes and certificates are stored/generated; starting empty is implied by the initial system state. `InitPool` creates an empty vote and certificate store (specs/tla/alpenglow/VoteStorage.tla:30), consistent with Def. 12–13 (alpenglow-whitepaper.md:513, alpenglow-whitepaper.md:520).
  - This aligns with downstream invariants (`PoolTypeOK`, multiplicity rules, certificate uniqueness).

- clock |-> 0; timeouts |-> [s ∈ Slots |-> 0]
  - Whitepaper: Nodes maintain local clocks and schedule timeouts only when `ParentReady` is emitted (alpenglow-whitepaper.md:602, alpenglow-whitepaper.md:607). Initializing both to zero encodes “no timeouts scheduled yet, local time at origin”.
  - Semantics: `AdvanceClock` considers only `timeouts[s] > 0` as scheduled (specs/tla/alpenglow/VotorCore.tla:224–233). Timeout values are later set per Def. 17: `clock + Δ_timeout + (i - s + 1) * Δ_block` within `HandleParentReady` (specs/tla/alpenglow/VotorCore.tla:173–189). `WindowSlots` returns slots ≥ 1 (specs/tla/alpenglow/Blocks.tla:211), preventing any “past scheduling” for slot 0, consistent with the whitepaper note.

Overall, the initializer builds a well-typed `ValidatorState` (see `ValidatorStateOK` at specs/tla/alpenglow/VotorCore.tla:240) that is faithful to the abstract state described in Definition 18, with parameter payloads moved into companion fields or recoverable from the Pool.

4. Conclusion of Audit

- Correctness vs. whitepaper:
  - Initializes per-slot state to empty as required by Definition 18.
  - Captures `ParentReady(hash(b))` semantics via a split: tag in `state[s]` and hash in `parentReady[s]`, which is equivalent for guards used in Algorithms 1–2.
  - Models pending blocks with an empty set per slot, a conservative generalization of the paper’s single-⊥ slot; combined with `BlockSeen`, behavior matches Algorithm 1’s intent.
  - Starts `Pool` empty per Def. 12–13; schedules timeouts later per Def. 17 using the initialized `clock`/`timeouts`.
  - Types and invariants line up with `ValidatorState` and `ValidatorStateOK`.
- Verdict: The initializer is faithful to the whitepaper at the abstraction level of state shape and initialization, with two intentional representation choices (parameterized state objects split into flags + maps; pendingBlocks as a set) that preserve semantics used elsewhere in the spec.

5. Open Questions / Concerns

- Parameter payloads in state objects:
  - Whitepaper denotes `ParentReady(hash(b))`, `VotedNotar(hash(b))`, and `BlockNotarized(hash(b))` with arguments; the spec models these as flags without embedded hashes. The current guards recover the needed information from `parentReady[s]` and from the Pool (e.g., `VotedForBlock`), and `HandleBlockNotarized` supplies the correct hash to `TryFinal`. This is sound under the current call graph, but it makes certain invariants that quantify over “the hash inside the state object” less direct to express.

- Pending block cardinality vs. Algorithm 1:
  - The whitepaper shows a single assignment `pendingBlocks[s] ← Block(...)` and an explicit ⊥. The spec uses a set per slot, and `CheckPendingBlocks` processes at most one element per slot per pass. Given `BlockSeen` gating, sets should be empty or singleton, but this invariant is not asserted in code. If future changes allowed multiple Block events per slot, this could introduce nondeterminism in which pending block is retried first.

- Sentinel coupling for ParentReady:
  - The intended invariant is: `HasState(v,s,"ParentReady")` iff `v.parentReady[s] ≠ NoBlock`. This coupling is respected by handlers, but it is not explicitly captured as an invariant; accidental divergence (e.g., setting one without the other) would be a model bug that could be caught by a simple invariant.

6. Suggestions for Improvement

- Add lightweight invariants to document representation choices:
  - ParentReadyConsistency: `∀ s ∈ Slots: HasState(v,s,"ParentReady") ⇔ v.parentReady[s] ≠ NoBlock`.
  - PendingBlocksSingleton (if desired): `∀ s ∈ Slots: Cardinality(v.pendingBlocks[s]) ≤ 1` (or switch to a partial function with an explicit ⊥ sentinel to mirror the paper more literally).

- Optional: Introduce typed aliases or comments for time values (e.g., `TimeoutTS == Nat`) to make the intent of `0` as “unscheduled” clearer alongside the `AdvanceClock` guard `timeouts[s] > 0`.

- Optional: If future proofs need to refer to the specific notarized block within `state[s]`, consider storing the hash alongside the flag in a separate map (e.g., `notarizedHash[s]`) and/or proving that `BlockNotarized` implies existence of a matching certificate in `pool.certificates[s]` with that hash.

- Documentation cross-link: In comments near `InitValidatorState`, cite Definition 18 explicitly and mention the split representation for parameterized state objects (the module header already points to §2.4; an inline note here would help readers who jump to the initializer).

— End of audit —

