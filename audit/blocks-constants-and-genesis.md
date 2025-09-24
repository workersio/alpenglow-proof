**Code Block**

```tla
CONSTANTS
    GenesisHash,     \* Hash of the genesis block (§2.1)
    WindowSize,      \* Number of consecutive slots per leader window (§2.7)
    LeaderSchedule   \* VRF-based leader map announced each epoch (§1.1)

ASSUME
    /\ GenesisHash \in BlockHashes
    /\ WindowSize \in Nat \ {0}  \* Window size must be positive (§2.7)
    /\ LeaderSchedule \in [Slots -> Validators]  \* VRF output (§1.1)

Block == [
    slot: Slots,
    hash: BlockHashes,
    parent: BlockHashes,
    leader: Validators
]

\* Definition 3: every block records its creation slot, unique hash,
\* parent hash, and the leader that proposed it.

\* The very first block in the chain (has no real parent)
GenesisBlock == [
    slot |-> 0,
    hash |-> GenesisHash,
    parent |-> GenesisHash,  \* Genesis is its own parent
    leader |-> CHOOSE v \in Validators : TRUE  \* Arbitrary leader
]
```

References in repo: `specs/tla/alpenglow/Blocks.tla:21`–`specs/tla/alpenglow/Blocks.tla:60`.


**Whitepaper Mapping**

- §1.1 Leader schedule: `alpenglow-whitepaper.md:53`, `:222`.
- §2.1 Definitions 3–5 (block, hash, ancestor/descendant): `alpenglow-whitepaper.md:351`, `:357`, `:363`.
- §2.7 Leader windows, Algorithm 3: `alpenglow-whitepaper.md:169`, `:731`, `:759`.
- Correctness (finalized blocks form a single chain): `alpenglow-whitepaper.md:243`.


**Cross-Module References**

- Imports types from `specs/tla/alpenglow/Messages.tla`:
  - `Validators`, `Slots`, `BlockHashes` (cf. `Messages.tla:17`–`Messages.tla:26`).
- Model configuration provides concrete values:
  - `specs/tla/alpenglow/MC.cfg`: assigns `GenesisHash`, `WindowSize`, and `LeaderSchedule <- MC_LeaderSchedule`.
  - `specs/tla/alpenglow/MC.tla`: defines `MC_LeaderSchedule` and `MC_StakeMap`.
- Related assumptions and helpers in the same module (context):
  - Window consistency: `LeaderScheduleWindowConsistency` (`Blocks.tla:164`–`Blocks.tla:168`).
  - Window arithmetic: `FirstSlotOfWindow`, `IsFirstSlotOfWindow` (`Blocks.tla:150`–`Blocks.tla:163`).
  - Genesis-as-self-parent sentinel used by ancestry: `IsAncestor` treats `b.parent = b.hash` as genesis (`Blocks.tla:95`–`Blocks.tla:112`).


**Reasoning vs Whitepaper**

- Constants and types
  - `LeaderSchedule \in [Slots -> Validators]` abstracts the threshold-VRF leader selection (whitepaper §1.1). A total function over `Slots` captures the “publicly known leader per slot” requirement.
  - `WindowSize \in Nat \ {0}` encodes the invariant that each leader controls a non-empty consecutive window (§2.7). The module later assumes `LeaderScheduleWindowConsistency` to ensure the same leader for all slots in a window, matching Algorithm 3’s window semantics.
  - `GenesisHash \in BlockHashes` aligns with Definition 4, which defines the block hash as a Merkle root; treating it as an abstract element of `BlockHashes` is the correct abstraction level.

- Block record (Definition 3)
  - The record fields `slot`, `hash`, `parent`, `leader` capture the consensus-relevant abstraction of a block. While the whitepaper defines a block as a sequence of slices, the spec intentionally abstracts away data-plane slices, preserving only the identifiers needed for safety (slot/parent/hash) and proposer identity (leader). This is consistent with TLA+-level abstraction.

- Genesis block representation
  - `slot |-> 0` sets a canonical genesis slot. This is conventional and compatible with the whitepaper’s slot semantics; the model configuration ensures `0 \in Slots` in practice (see `MC.cfg`), though this is not explicitly assumed in the module.
  - `parent |-> GenesisHash` and `hash |-> GenesisHash` make genesis a self-parented sentinel, which integrates cleanly with ancestry/chain predicates (Definition 5). The ancestry function in this module explicitly treats `b.parent = b.hash` as the termination condition when walking parents, matching the “notional genesis” language.
  - `leader |-> CHOOSE v \in Validators : TRUE` makes the genesis leader arbitrary. Since genesis is only a sentinel for ancestry and initialization, its leader value is irrelevant to protocol behavior and proofs. This is a sound abstraction, provided the rest of the spec never relies on `Leader(0) = GenesisBlock.leader`.


**Conclusion**

- The constants’ type assumptions and the `Block`/`GenesisBlock` abstractions are consistent with the whitepaper’s Definitions 3–5 and §1.1/§2.7. The module-level window consistency assumption (nearby) matches the leader-window semantics required by Algorithm 3.
- No safety or liveness contradiction is introduced by these definitions; they integrate with later invariants (e.g., ancestry, single-chain) and with block-creation actions that ensure hash uniqueness.


**Open Questions / Concerns**

- Genesis slot membership
  - The module fixes `GenesisBlock.slot = 0`, but does not explicitly assume `0 \in Slots`. Configs include 0, yet a general model might not. If `AllBlocksValid` or similar invariants include `GenesisBlock`, a model without `0 \in Slots` would violate type invariants.

- Genesis leader vs schedule
  - If any property elsewhere assumes `Leader(b.slot) = b.leader` for all blocks, genesis would not satisfy this unless `LeaderSchedule[0]` is constrained to match `GenesisBlock.leader`. Current code appears to avoid relying on this, but it would help to make the intended scope explicit.

- Window semantics locality
  - The window constraint is captured by a separate assumption `LeaderScheduleWindowConsistency`. An implementer reading only this snippet might miss that the window property is assumed (not derived). That’s fine at this abstraction level, but worth calling out where `WindowSize` is introduced.

- Defaulting to genesis in lookups
  - In context, `GetBlockAtSlot` returns `GenesisBlock` if no block exists at `slot`. This is convenient but can blur the distinction between “no block at slot” vs “genesis”. Audit downstream usage to ensure no logic conflates these cases (e.g., voting predicates, certificates).


**Suggestions**

- Add an explicit slot-domain assumption
  - `ASSUME 0 \in Slots` (or define a `GenesisSlot` constant and assume it is in `Slots`) to make the genesis typing obligation explicit and robust across models.

- Clarify genesis-schedule relation
  - Add a comment or lemma stating that properties relating `Leader(slot)` to `block.leader` exclude genesis, or alternatively assume `LeaderSchedule[0] = GenesisBlock.leader` if that simplifies reasoning.

- Localize window assumption near constants
  - Optionally move or restate `LeaderScheduleWindowConsistency` adjacent to the constants block to reinforce that the window property is an assumption about the schedule, not a derived property.

- Optional: strengthen type lemma
  - Provide `IsValidBlock(GenesisBlock)` proof/lemma if `IsValidBlock` is intended to include genesis; otherwise, document that `IsValidBlock` applies only to non-genesis blocks and add a separate `IsGenesis` predicate. This keeps invariants precise.

