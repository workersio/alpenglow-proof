# Audit: HandleBlockNotarized — Algorithm 1 (lines 9–11)

## 1. Code Audited

```
HandleBlockNotarized(validator, slot, blockHash) ==
    LET newValidator == AddState(validator, slot, "BlockNotarized")
    IN TryFinal(newValidator, slot, blockHash)
```

Reference: `specs/tla/alpenglow/VotorCore.tla:245`–`specs/tla/alpenglow/VotorCore.tla:247`

## 2. Whitepaper Sections and References

- Algorithm 1 — Votor event loop, BlockNotarized handler:
  - `alpenglow-whitepaper.md:647`–`alpenglow-whitepaper.md:651`
    - 9: upon BlockNotarized(s, hash(b))
    - 10: state[s] ← state[s] ∪ {BlockNotarized(hash(b))}
    - 11: TRYFINAL(s, hash(b))
- Definition 15 (Pool events): `alpenglow-whitepaper.md:543`–`alpenglow-whitepaper.md:546`
  - BlockNotarized(s, hash(b)) occurs when Pool holds a notarization certificate for b.

Cross‑module connections that realize the event and its preconditions:

- Event emission rule: `specs/tla/alpenglow/MainProtocol.tla:603`–`specs/tla/alpenglow/MainProtocol.tla:609` (EmitBlockNotarized)
- Event predicate (Def. 15): `specs/tla/alpenglow/VoteStorage.tla:257` (ShouldEmitBlockNotarized)
- Invariant tying state to certificates: `specs/tla/alpenglow/MainProtocol.tla:1008`–`specs/tla/alpenglow/MainProtocol.tla:1013` (BlockNotarizedImpliesCert)
- Finalization helper used here: `specs/tla/alpenglow/VotorCore.tla:141`–`specs/tla/alpenglow/VotorCore.tla:151` (TryFinal)

## 3. Reasoning vs. Whitepaper

What Algorithm 1 requires (lines 9–11):
- On BlockNotarized(s, h): add BlockNotarized(h) to state[s], then invoke TRYFINAL(s, h).

How the spec models it:
- The handler sets the per‑slot flag `"BlockNotarized"` via `AddState` and immediately invokes `TryFinal(…, slot, blockHash)`.
- The model does not parameterize the state object with the hash (i.e., not `BlockNotarized(h)` inside the set). Instead, it:
  - Records a plain `"BlockNotarized"` flag; and
  - Passes `blockHash` to `TryFinal`, which checks both the flag and that the validator itself notar‑voted for that specific hash: `VotedForBlock(validator, slot, blockHash)`.
  - This preserves the whitepaper’s intended binding to h using Pool data rather than an annotated state element.

Event precondition fidelity:
- `EmitBlockNotarized` only fires when `ShouldEmitBlockNotarized(pool, s, h)` holds (`specs/tla/alpenglow/MainProtocol.tla:603`–:609), which is exactly “Pool holds a notarization certificate for block h” (`specs/tla/alpenglow/VoteStorage.tla:257`).
- `BlockNotarizedImpliesCert` ensures any `"BlockNotarized"` flag implies presence of the corresponding notarization certificate (`specs/tla/alpenglow/MainProtocol.tla:1008`–:1013), matching Definition 15.

TRYFINAL alignment:
- Whitepaper Alg. 2 requires, for finalization: BlockNotarized(h) ∈ state[s], VotedNotar(h) ∈ state[s], and BadWindow ∉ state[s] (`alpenglow-whitepaper.md:699`–`alpenglow-whitepaper.md:704`).
- The spec’s `TryFinal` enforces the equivalent using:
  - `HasState(_, s, "BlockNotarized")` (BlockNotarized present),
  - `VotedForBlock(_, s, h)` (validator’s own notar vote for h), and
  - `~HasState(_, s, "BadWindow")` (no fallback activity),
  which is faithful to Alg. 2 while using Pool votes to bind the hash.

## 4. Conclusion

- The handler exactly matches Algorithm 1 lines 9–11: it marks `BlockNotarized` for the slot and immediately attempts `TryFinal` on the same hash.
- Preconditions for emitting the event are correctly sourced from Definition 15 via Pool certificate checks, and the spec enforces a certificate–state correspondence through invariants.
- The internal choice to represent `BlockNotarized` as an unparameterized flag is sound here because `TryFinal` additionally checks that the node previously notar‑voted for the same `blockHash` in slot `s`.

Overall: This code block is correct and faithful to the whitepaper.

## 5. Open Questions / Concerns

- Finalization trigger symmetry (minor modeling deviation already noted elsewhere):
  - Alg. 2 line 15 calls TRYFINAL immediately after a successful notar vote in TRYNOTAR. In the current spec, `TryNotar` does not call `TryFinal`; finalization is only attempted here (upon BlockNotarized). If `BlockNotarized(s, h)` was handled before the node casts its own notar vote, the earlier `TryFinal` would have failed; later success in `TryNotar` would not retrigger it. This can delay or miss finalization relative to the paper’s more eager behavior.
- Non‑parameterized state element:
  - Using `"BlockNotarized"` without the hash is acceptable because `TryFinal` binds `h` via the Pool, but it makes properties that quantify over “the hash inside the state” less direct to express.

## 6. Suggestions for Improvement

- Invoke `TryFinal` from `TryNotar` upon a successful notar vote (matching Alg. 2 line 15). This ensures that both pathways (event arrival and local successful vote) attempt finalization, preventing missed opportunities.
- Optional: Parameterize state flags in the model (e.g., carry the hash in `BlockNotarized`) or provide derived functions that expose the associated hash from Pool for readability when writing invariants.
- Add a liveness check (model property) that if `BlockNotarized(s, h)` and the validator later records `VotedForBlock(s, h)` and no `BadWindow`, then eventually a `FinalVote(s)` appears in the validator’s Pool. This would catch scheduling gaps where `TryFinal` is not retried.

