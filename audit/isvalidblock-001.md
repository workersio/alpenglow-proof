## 1. Code Under Audit

```tla
IsValidBlock(b) ==
    /\ b.slot \in Slots
    /\ b.hash \in BlockHashes
    /\ b.parent \in BlockHashes
    /\ b.leader \in Validators
    /\ b.slot > 0 => b.parent # b.hash  \* Non-genesis blocks can't self-reference
```

Context: Defined in `specs/tla/alpenglow/Blocks.tla:67`.

Related type/scope definitions used here:
- `Slots`, `BlockHashes`, `Validators` are constants from `specs/tla/alpenglow/Messages.tla:16`–`:21`, with assumptions at `specs/tla/alpenglow/Messages.tla:23`–`:27`.
- `GenesisBlock` is defined in `specs/tla/alpenglow/Blocks.tla:53`–`:58` (slot 0, self-parented with `GenesisHash`).

## 2. Whitepaper Sections and References

- Block definition and inclusion of parent slot/hash:
  - `alpenglow-whitepaper.md:351` — Definition 3 (block)
  - `alpenglow-whitepaper.md:355` — Block data contains parent slot/hash
- Block hash notion (abstract set of possible block identifiers):
  - `alpenglow-whitepaper.md:357` — Definition 4 (block hash)
- Ancestry/parent linkage semantics (non-self-parenting implied for non-genesis):
  - `alpenglow-whitepaper.md:363` — Definition 5 (ancestor/descendant)
- Chain starts at a (notional) genesis block:
  - `alpenglow-whitepaper.md:243` — Correctness paragraph (genesis and parent link chain)
- Leaders and leader windows (justifying `leader \in Validators` field):
  - `alpenglow-whitepaper.md:53` — Slots, designated leaders, leader windows, VRF schedule

## 3. Reasoning and Mapping to Whitepaper

- `/\ b.slot \in Slots`
  - Matches the paper’s slotting model where every block is associated with a slot (Definition 3; introductory §1.1 at `:53`). Ensures well-typed slot number.

- `/\ b.hash \in BlockHashes`
  - Abstracts the Merkle-root hash defined in Definition 4. The spec models the space of all valid block hashes as `BlockHashes` and checks membership only (no computation here, by design at the level of abstraction).

- `/\ b.parent \in BlockHashes`
  - Mirrors Definition 3’s inclusion of the parent hash in block data. This predicate is intentionally local (type-level); the relationship between `b.parent` and existing blocks is validated elsewhere (e.g., `ValidParentChild` in `Blocks.tla:86`).

- `/\ b.leader \in Validators`
  - While the whitepaper does not include an explicit `leader` field in the block object, slices carry leader signatures and each slot has a designated leader (`:53`). Modeling `leader` as a field is an acceptable abstraction to record the producer identity and is type-checked here.

- `/\ b.slot > 0 => b.parent # b.hash`
  - Ensures non-genesis blocks do not self-parent, consistent with the chain semantics (Definition 5). This dovetails with `GenesisBlock` in the spec (`Blocks.tla:53`–`:58`), where genesis is self-parented and has slot 0. The predicate does not force genesis self-parenting; it merely disallows self-parenting for `slot > 0`, which is sufficient for non-genesis safety.

Overall, `IsValidBlock` is a structural “well-typed” predicate. The spec deliberately separates format/type checks from relational checks (e.g., parent precedence, leader schedule compliance):
- Parent-child ordering: `ValidParentChild` (`Blocks.tla:86`–`:88`).
- Leader schedule adherence: enforced by transition predicates in `MainProtocol.tla` (e.g., `HonestProposeBlock` requires `leader = Leader(slot)` at `specs/tla/alpenglow/MainProtocol.tla:298`).

This separation aligns with the paper’s abstractions: block contents (Def. 3–4) vs. protocol dynamics (leader schedule, Algorithm 3).

## 4. Conclusion of the Audit

- The predicate correctly captures type-level validity for blocks consistent with the whitepaper’s Definitions 3–5 and the existence of a designated leader per slot.
- It purposefully avoids chain/contextual validations (e.g., parent existence in the current block set, leader schedule compliance), which are handled elsewhere in the spec. This modularity is appropriate for TLA+.
- The special-case for non-genesis (no self-parenting when `slot > 0`) is consistent with the paper’s chain semantics and with the model’s `GenesisBlock` definition.

Therefore, within its intended scope (format/typing), `IsValidBlock` is correct and faithful to the whitepaper abstractions.

## 5. Open Questions / Concerns

- Genesis typing across models: The global assumptions do not require `0 \in Slots` (`Messages.tla:25`). Yet the model uses `slot = 0` for `GenesisBlock` and returns `GenesisBlock` in helpers like `GetBlockAtSlot` (`Blocks.tla:190`). In practice, the TLC model config (`MC.cfg:...`) includes `0` in `Slots`, but it would be safer to document/assume `0 \in Slots` at the spec level.

- Genesis constraints in `IsValidBlock`: As written, any block with `slot = 0` that is not self-parented still satisfies `IsValidBlock`. The spec defines a canonical `GenesisBlock`, but `IsValidBlock` does not enforce that “if `slot = 0` then `b.hash = b.parent = GenesisHash`.” This is acceptable if `IsValidBlock` is intentionally only a typing predicate, but worth documenting.

- Hash uniqueness: Comments mention “unique hash” (`Blocks.tla:49`), but no global invariant ensures all blocks have distinct `hash` values. This is typical to leave to other invariants, but if the paper assumes cryptographic uniqueness, an explicit invariant may improve clarity.

- Leader schedule conformance: `IsValidBlock` does not enforce `b.leader = Leader(b.slot)`. This is enforced in `MainProtocol.tla` (e.g., `HonestProposeBlock` at `:298`), but it may be helpful to define and reference a dedicated predicate (e.g., `LeaderMatchesSchedule(b)`) to make proofs more modular.

- Parent existence within current state: `IsValidBlock` only checks membership of `b.parent` in `BlockHashes`, not that the referenced parent block exists in the known set. The spec handles parent-child relationships with `ValidParentChild` and in transition rules; this separation is fine but should be explicit in commentary.

## 6. Suggestions for Improvement

- Clarify scope in a comment: Rename the comment to “Check if a block is well-typed” (it already does this) and consider renaming the predicate to `IsWellTypedBlock` to avoid overloading “valid” with relational properties handled elsewhere.

- Optional stronger genesis guard (if desired):
  - Add an auxiliary predicate `IsGenesis(b) == b.slot = 0 /\ b.hash = GenesisHash /\ b.parent = GenesisHash` and either document that `IsValidBlock` does not enforce it, or extend `IsValidBlock` with `(b.slot = 0) => IsGenesis(b)`.
  - Alternatively, assert `0 \in Slots` at the module where `GenesisBlock` is defined.

- Add an explicit uniqueness invariant (if needed for proofs):
  - `DistinctHashes(blocks) == \A b1, b2 \in blocks : (b1 # b2) => b1.hash # b2.hash`
  - Use it as an invariant where appropriate (e.g., in model configs), aligning with the “unique hash” comment (`Blocks.tla:49`).

- Encapsulate leader-schedule consistency for reuse in proofs:
  - Define `LeaderMatchesSchedule(b) == b.leader = Leader(b.slot)` and reference it from transitions and lemmas; keep it out of `IsValidBlock` to preserve the typing vs. relation separation.

- Document parent existence expectations:
  - In `Blocks.tla`, near `IsValidBlock`, add a short note that parent existence and ordering are validated by `ValidParentChild` and higher-level protocol steps (as currently practiced).

