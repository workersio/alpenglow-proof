**Code Being Audited**

```
HasState(validator, slot, stateObj) ==
    stateObj \in validator.state[slot]

\* Add state object to validator's slot
AddState(validator, slot, stateObj) ==
    [validator EXCEPT !.state[slot] = validator.state[slot] \union {stateObj}]

\* Check if validator voted for a specific block
VotedForBlock(validator, slot, blockHash) ==
    \E vote \in GetVotesForSlot(validator.pool, slot) :
        /\ vote.validator = validator.id
        /\ vote.type = "NotarVote"
        /\ vote.blockHash = blockHash
```

- Source: specs/tla/alpenglow/VotorCore.tla:81, specs/tla/alpenglow/VotorCore.tla:85, specs/tla/alpenglow/VotorCore.tla:89
- Related references:
  - `GetVotesForSlot`: specs/tla/alpenglow/VoteStorage.tla:142
  - Vote type literal "NotarVote": specs/tla/alpenglow/Messages.tla:45
  - Validator carries `id` and `pool`: specs/tla/alpenglow/VotorCore.tla:56, specs/tla/alpenglow/VotorCore.tla:60

**Whitepaper Mapping**

- Definition 18 (Votor state; slot-local flags): alpenglow-whitepaper.md:615–621, alpenglow-whitepaper.md:630
- Algorithm 2 (helper functions):
  - Notarization precondition (parent readiness / prior vote): alpenglow-whitepaper.md:690–693
  - Finalization precondition (requires BlockNotarized, VotedNotar, not BadWindow): alpenglow-whitepaper.md:700–703
- Definition 12 (Pool vote storage; count-once): alpenglow-whitepaper.md:513–517
- Definition 15 (Pool events; BlockNotarized, ParentReady): alpenglow-whitepaper.md:543–546

**Reasoning and Conformance**

- HasState and AddState
  - Purpose: Minimal helpers to query/update the slot-local state set per Definition 18.
  - Typing: `validator.state` is declared as `[Slots -> SUBSET StateObject]` (specs/tla/alpenglow/VotorCore.tla:57), so `validator.state[slot]` is a set and membership/union are well-typed when `slot \in Slots`. The module’s `ValidatorStateOK` invariant enforces this domain (specs/tla/alpenglow/VotorCore.tla:324).
  - Whitepaper alignment: Matches Definition 18’s model where state is a growing set of flags per slot. Note: in the spec, some state flags are unparameterized (see “Concerns”).

- VotedForBlock
  - Purpose: Checks whether the node previously cast an initial notarization vote (NotarVote) for a specific block in a given slot.
  - Mechanics: Queries the local Pool’s votes for the slot (Definition 12), then matches a vote record with `validator = validator.id`, `type = "NotarVote"`, and `blockHash = blockHash`.
  - Why NotarVote (and not NotarFallbackVote): The whitepaper’s finalization gate requires “VotedNotar(hash(b)) \in state[s]” (Algorithm 2, line 19 equivalence; alpenglow-whitepaper.md:700–703). That is the initial notarization vote, not a fallback vote. Using `type = "NotarVote"` captures exactly this requirement.
  - Use sites confirm intent:
    - In TryNotar, the “later slot” branch checks the parent with `VotedForBlock(validator, slot-1, parentHash)` (specs/tla/alpenglow/VotorCore.tla:116–121), mirroring Algorithm 2 line 11.
    - In TryFinal, finalization requires `BlockNotarized` and `VotedForBlock(validator, slot, blockHash)` and not `BadWindow` (specs/tla/alpenglow/VotorCore.tla:141–152), mirroring Algorithm 2 lines 18–21.
  - Whitepaper alignment via Pool:
    - Definition 12’s “count-once per slot” rule is enforced by `StoreVote/CanStoreVote` (specs/tla/alpenglow/VoteStorage.tla:54–85), so inspecting Pool state is sound and avoids double counting or ambiguity.
    - The spec stores the node’s own vote in the Pool in the same atomic step in which it sets state flags (TryNotar; specs/tla/alpenglow/VotorCore.tla:122–129). Therefore, using Pool to witness “I voted for this block” is equivalent to the paper’s state predicate `VotedNotar(hash(b)) \in state[s]`.

**Conclusion**

- Correct with a modeled abstraction: The trio of helpers is consistent with the whitepaper’s Algorithms 1–2 and Definitions 12, 15, and 18. In particular, `VotedForBlock` correctly encodes “I cast an initial notarization vote for this specific block in slot s” and is used precisely where the whitepaper requires `VotedNotar(hash(b))`.
- Safety is preserved: Finalization requires notarization in state, our own initial notarization vote for the exact block, and no fallback activity—matching Algorithm 2’s guard. The Pool-backed check respects count-once semantics (Definition 12).

**Open Questions / Concerns**

- Parameterization gap vs. Definition 18
  - The paper defines `VotedNotar(hash(b))` and `BlockNotarized(hash(b))` as parameterized state objects (alpenglow-whitepaper.md:615–621, alpenglow-whitepaper.md:647–651), while the spec models them as unparameterized flags in `StateObject` and stores the hashes separately (for parent readiness via `parentReady`, and for voted block via `VotedForBlock`). This is a valid abstraction but deviates from the literal state shape in the paper. It slightly disperses the state knowledge across `state` and `pool`.

- Reliance on Pool for self-vote witness
  - `VotedForBlock` assumes our own initial notar vote is present in the local Pool. In TryNotar, state is updated and `StoreVote` is called in one atomic step, so divergence is not observable. However, this coupling could be called out explicitly as an invariant (see Suggestions).

- Typing precondition on slot
  - `HasState`/`AddState` read `validator.state[slot]` and assume `slot \in Slots`. The surrounding code ensures this, and `ValidatorStateOK` enforces types, but a note or precondition could improve local clarity.

**Suggestions for Improvement**

- Make state flags carry hashes (closer to the paper)
  - Option A (spec-level): Parameterize `VotedNotar` and `BlockNotarized` with `blockHash` in `state` to align exactly with Definition 18. Then replace `VotedForBlock` calls in TryNotar/TryFinal with direct state membership checks and simplify reasoning.
  - Option B (documented abstraction): If you prefer the current approach, add a short comment in `VotorCore.tla` clarifying that block-specific information for `VotedNotar` and `BlockNotarized` is tracked via `VotedForBlock` (Pool) and the `parentReady` map, respectively, and that this is observationally equivalent for Algorithm 2 guards.

- Add a linking lemma/invariant
  - Lemma: `\A v,s,h : VotedForBlock(v,s,h) => HasState(v,s,"Voted")`. This captures the intended coupling between Pool and state and aids model checking and reader confidence.

- Small ergonomics
  - Consider a helper predicate `IsInitialNotarVote(v) == v.type = "NotarVote"` to avoid duplicating the string literal in multiple places and reduce maintenance risk.

**Cross-Module References Checked**

- `GetVotesForSlot` (VoteStorage): specs/tla/alpenglow/VoteStorage.tla:142
- Vote creation/typing (Messages): specs/tla/alpenglow/Messages.tla:65–71, specs/tla/alpenglow/Messages.tla:111–121
- Pool multiplicity rules (Definition 12): specs/tla/alpenglow/VoteStorage.tla:54–85
- Validator carries `id` and `pool`: specs/tla/alpenglow/VotorCore.tla:56, specs/tla/alpenglow/VotorCore.tla:60
- TryNotar/TryFinal usage sites: specs/tla/alpenglow/VotorCore.tla:107–129, specs/tla/alpenglow/VotorCore.tla:141–152

