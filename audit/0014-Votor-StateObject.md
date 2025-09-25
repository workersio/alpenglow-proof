# Audit: Votor StateObject (slot state flags)

## 1. Code Audited

Source: `specs/tla/alpenglow/VotorCore.tla:41`

```tla
StateObject == {
    "ParentReady",      \* Pool emitted ParentReady event
    "Voted",            \* Cast notarization or skip vote
    "VotedNotar",       \* Cast notarization vote for specific block
    "BlockNotarized",   \* Pool has notarization certificate
    "ItsOver",          \* Cast finalization vote, done with slot
    "BadWindow",        \* Cast skip or fallback vote
    "BlockSeen"         \* First Block(...) event consumed for this slot
}
```

This set provides the per-slot flags used by Votor to track a validator’s local progress through the voting lifecycle. It is consumed via `HasState`/`AddState` and typed by `ValidatorStateOK`.

Key usages (writes/reads) for orientation:
- `ParentReady` set in `HandleParentReady` (`specs/tla/alpenglow/VotorCore.tla:255`).
- `Voted` set in `TryNotar` and `TrySkipWindow` (`specs/tla/alpenglow/VotorCore.tla:123`, `:175`).
- `VotedNotar` set in `TryNotar` (`specs/tla/alpenglow/VotorCore.tla:124`).
- `BlockNotarized` set in `HandleBlockNotarized` (`specs/tla/alpenglow/VotorCore.tla:246`).
- `ItsOver` set in `TryFinal` (`specs/tla/alpenglow/VotorCore.tla:149`).
- `BadWindow` set in `TrySkipWindow`, `HandleSafeToNotar`, `HandleSafeToSkip` (`specs/tla/alpenglow/VotorCore.tla:176`, `:281`, `:297`).
- `BlockSeen` used to gate first delivery in `ReceiveBlock` (`specs/tla/alpenglow/MainProtocol.tla:201`).

Related typing and invariants:
- `state: [Slots -> SUBSET StateObject]` (`specs/tla/alpenglow/VotorCore.tla:57`).
- `ValidatorStateOK` (`specs/tla/alpenglow/VotorCore.tla:324`).
- ParentReady/BlockNotarized event–certificate implications (`specs/tla/alpenglow/MainProtocol.tla:998`, `:1010`).

## 2. Whitepaper Sections Represented

- Definition 18 (Votor state): `alpenglow-whitepaper.md:615` (pp. 23–24)
  - ParentReady(hash(b)), Voted, VotedNotar(hash(b)), BlockNotarized(hash(b)), ItsOver, BadWindow.
- Definition 15 (Pool events): `alpenglow-whitepaper.md:543`
  - BlockNotarized(s, hash(b)), ParentReady(s, hash(b)).
- Algorithms 1 and 2 (event loop and helpers): `alpenglow-whitepaper.md:634`, `:675` (pp. 24–25)
  - Where these state flags are added/checked.
- Definition 17 (timeout scheduling on ParentReady): `alpenglow-whitepaper.md:607` (p. 23).

Note: “BlockSeen” does not appear in Definition 18; it is a modeling artifact introduced in the spec to avoid re-processing duplicate Block events (see `specs/tla/alpenglow/MainProtocol.tla:195`–`:209`).

## 3. Reasoning and Conformance

High-level intent: The StateObject set captures the minimal, persistent markers the whitepaper requires Votor to hold per slot. Each item either mirrors a named item in Definition 18 or supports the TLA+ event-delivery modeling.

- ParentReady
  - Whitepaper: Def. 18 includes ParentReady(hash(b)); Def. 15 defines when it is emitted.
  - Model: The flag is set in `HandleParentReady` and its parameter (parent hash) is stored separately in `parentReady[slot]` (`specs/tla/alpenglow/VotorCore.tla:255`–`:267`). Emission guarded by `ShouldEmitParentReady` exactly matches Def. 15 (`specs/tla/alpenglow/VoteStorage.tla:268`–`:273`). Invariant `ParentReadyImpliesCert` ties the flag to the pool condition (`specs/tla/alpenglow/MainProtocol.tla:998`–`:1003`).

- Voted and VotedNotar
  - Whitepaper: Def. 18 has Voted and VotedNotar(hash(b)); Alg. 2 lines 7–15 add both upon a notar vote.
  - Model: `Voted` is a boolean “initial vote cast (skip or notar)”. `VotedNotar` is stored only as a tag, while the specific block hash is tracked via pool votes and checked through `VotedForBlock(validator, s, hash)` (`specs/tla/alpenglow/VotorCore.tla:88`–`:93`). Parent gating for non-first slots uses `VotedForBlock` in the previous slot as a substitute for `VotedNotar(hash_parent) ∈ state[s−1]` (Alg. 2 line 11) (`specs/tla/alpenglow/VotorCore.tla:118`–`:119`). This preserves the whitepaper’s semantics without parameterizing the flag.

- BlockNotarized and ItsOver
  - Whitepaper: Def. 18 includes BlockNotarized(hash(b)) and ItsOver; Alg. 1 lines 9–11 add BlockNotarized on event; Alg. 2 lines 18–21 add ItsOver on final vote.
  - Model: `HandleBlockNotarized` sets BlockNotarized; `TryFinal` requires the flag, the validator’s own prior notar vote for the same hash, and no `BadWindow` (`specs/tla/alpenglow/VotorCore.tla:141`–`:151`). The hash comes as the event parameter, maintaining the binding required by the paper. `BlockNotarizedImpliesCert` connects the flag to pool reality (`specs/tla/alpenglow/MainProtocol.tla:1010`–`:1013`).

- BadWindow
  - Whitepaper: Def. 18 says BadWindow indicates that the node cast skip, skip-fallback, or notar-fallback in slot s.
  - Model: The flag is set exactly when casting SkipVote (TrySkipWindow) or either fallback vote (SafeToNotar/Skip) (`specs/tla/alpenglow/VotorCore.tla:176`, `:281`, `:297`). `TryFinal` forbids finalization if `BadWindow` is present, matching Alg. 2 line 19’s guard (`specs/tla/alpenglow/VotorCore.tla:145`).

- BlockSeen (modeling only)
  - Not in Def. 18. Used to model the assumption that only the first complete block per slot reaches Votor (to avoid double handling in the model). See rationale comment and gating in `ReceiveBlock` (`specs/tla/alpenglow/MainProtocol.tla:195`–`:209`). This does not change protocol semantics because leaders produce one block per slot; it only prevents duplicate delivery.

Persistence: All flags are added via `AddState` and never removed, matching Def. 18’s “permanently added” requirement.

Parameterization choice: Where the whitepaper parameterizes flags with hashes, the model stores the hash either in a parallel map (`parentReady[slot]`) or re-derives it from votes/certificates in Pool (e.g., `VotedForBlock`, event parameters). This is a faithful abstraction: guards relying on the parameter check the exact hash as required by the paper.

## 4. Conclusion

The StateObject definition and its use across VotorCore and MainProtocol conform to the abstractions of Whitepaper §2.4:
- All required flags from Definition 18 are represented; their addition points and guards align with Algorithms 1–2 and Definitions 15–17.
- Parameterized flags (ParentReady, VotedNotar, BlockNotarized) are represented with a boolean flag plus explicit hash checks via auxiliary state (parentReady map) or Pool queries. Guards that need the hash (e.g., try-finalize) correctly bind to the same hash.
- The extra BlockSeen flag is a modeling convenience for event delivery and is not part of the protocol state; it does not affect safety/liveness reasoning.

Overall, the abstraction is sound: it preserves the intended safety and liveness semantics while simplifying per-slot state.

## 5. Open Questions / Concerns

- Comment accuracy: `specs/tla/alpenglow/VotorCore.tla:51` claims “These flags are exactly the items listed in Definition 18,” but BlockSeen is extra and not in the whitepaper’s list.
- Redundant `VotedNotar` tag: The model never reads `HasState(_,_, "VotedNotar")`. All logic uses `Voted` and `VotedForBlock`. While harmless, this may confuse readers expecting the hash-parameterized semantics of Def. 18.
- Hash binding for BlockNotarized: The flag is not parameterized, so binding relies on the event’s parameter and invariants. This is correct, but consider documenting that `BlockNotarized` means “some block in slot is notarized” and the specific hash is carried by the event into `TryFinal`.

## 6. Suggestions for Improvement

- Clarify documentation:
  - Update/expand the comment near `StateObject` to note that BlockSeen is a modeling artifact and that some Def. 18 items are parameterized via auxiliary state/pool queries.
  - Optionally rename `VotedNotar` to `VotedNotarTag` (or remove it) to avoid implying parameterization when the tag isn’t consulted.

- Strengthen invariants for auditability (optional but helpful):
  - VotedConsistency: If `"Voted" ∈ state[s]`, then this validator has either a NotarVote or SkipVote for slot s in Pool.
  - VotedNotarConsistency (if retaining the tag): If `"VotedNotar" ∈ state[s]`, there exists a NotarVote by this validator for slot s in Pool.
  - BadWindowWitness: If `"BadWindow" ∈ state[s]`, this validator has at least one of SkipVote, SkipFallbackVote, NotarFallbackVote in Pool for slot s.
  - ItsOverWitness: If `"ItsOver" ∈ state[s]`, this validator has a FinalVote for slot s in Pool.

- Minor: If desired to mirror the paper more closely, `state` could store parameterized records for ParentReady/VotedNotar/BlockNotarized. The current design is fine; adding a short comment explaining the choice will prevent confusion.

