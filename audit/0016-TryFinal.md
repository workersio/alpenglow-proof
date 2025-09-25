# Audit: TryFinal (finalization vote issuance)

1. Code that you are auditing.

```tla
TryFinal(validator, slot, blockHash) ==
    LET canVote ==
            /\ HasState(validator, slot, "BlockNotarized")
            /\ VotedForBlock(validator, slot, blockHash)
            /\ ~HasState(validator, slot, "BadWindow")
    IN
        IF canVote THEN
            LET vote == CreateFinalVote(validator.id, slot)
                newState == AddState(validator, slot, "ItsOver")
                poolWithVote == StoreVote(newState.pool, vote)
            IN [newState EXCEPT !.pool = poolWithVote]
        ELSE validator
```

- Source: `specs/tla/alpenglow/VotorCore.tla:141`

2. The whitepaper section and references that the code represents.

- Algorithm 2 (TRYFINAL) guard and action:
  - If BlockNotarized(hash(b)) ∈ state[s] and VotedNotar(hash(b)) ∈ state[s] and BadWindow ∉ state[s] then broadcast FinalVote(s) and add ItsOver.
    - `alpenglow-whitepaper.md:700` (guard), `alpenglow-whitepaper.md:702` (broadcast), `alpenglow-whitepaper.md:703` (ItsOver)
- Definition 15 (Pool events): BlockNotarized(s, hash(b)).
  - `alpenglow-whitepaper.md:543`, `alpenglow-whitepaper.md:545`
- Definition 18 (Votor state): VotedNotar(hash(b)), BlockNotarized(hash(b)), ItsOver, BadWindow.
  - `alpenglow-whitepaper.md:615`, `alpenglow-whitepaper.md:619`, `alpenglow-whitepaper.md:621`, `alpenglow-whitepaper.md:630`
- Table 5 (Finalization Vote): FinalVote(s).
  - `alpenglow-whitepaper.md:495`
- Table 6 (Finalization Certificate): FinalVote, Σ ≥ 60%.
  - `alpenglow-whitepaper.md:505`
- Interaction with TRYSKIPWINDOW/SafeToNotar/SafeToSkip that set BadWindow and thereby forbid finalization in the same slot/window:
  - `alpenglow-whitepaper.md:660`, `alpenglow-whitepaper.md:666`, `alpenglow-whitepaper.md:709`
- Definition 14 (Finalization): slow path requires FinalizationCert(s) together with the notarized block in s; fast path via FastFinalizationCert(b).
  - `alpenglow-whitepaper.md:536`

3. The reasoning behind the code and what the whitepaper claims.

- Block notarized prerequisite:
  - Code requires `HasState(_, s, "BlockNotarized")`. In the model this flag is added by handling the Pool event BlockNotarized(s, h), which is emitted exactly when a NotarizationCert(s, h) is present: `specs/tla/alpenglow/VoteStorage.tla:222` checked and used by `specs/tla/alpenglow/MainProtocol.tla:603` → `HandleBlockNotarized` → `specs/tla/alpenglow/VotorCore.tla:246`.
  - Matches Algorithm 2’s requirement that finalization voting is enabled only after notarization (not after notar-fallback), consistent with Definition 15’s wording.
- Own notar vote for the same block:
  - Code uses `VotedForBlock(validator, s, blockHash)` to check that this validator cast a NotarVote for hash(b) in slot s, implemented via a Pool query: `specs/tla/alpenglow/VotorCore.tla:86` → `GetVotesForSlot` `specs/tla/alpenglow/VoteStorage.tla:142`.
  - This realizes “VotedNotar(hash(b)) ∈ state[s]” from Algorithm 2; the binding to hash(b) is enforced via the pool rather than a parameterized state flag.
- No fallback activity in window/slot:
  - Code requires `~HasState(_, s, "BadWindow")`. Per Algorithm 2 and the paper, BadWindow is added when casting skip or either fallback vote in the same slot/window, forbidding finalization thereafter: see `specs/tla/alpenglow/VotorCore.tla:176`, `:281`, `:297` and whitepaper ref `alpenglow-whitepaper.md:849`.
- Action on success:
  - Construct `FinalVote(s)` with `CreateFinalVote`: `specs/tla/alpenglow/Messages.tla:97`. The vote’s `blockHash = NoBlock` reflects slot-scoped finalization (Definition 14; FinalizationCert is slot-scoped): `specs/tla/alpenglow/Certificates.tla:309`.
  - Store the vote via `StoreVote` respecting multiplicity (only one FinalVote per validator per slot): `specs/tla/alpenglow/VoteStorage.tla:76`–`:85`.
  - Add `ItsOver` to `state[s]` so no further votes are cast for s, matching Algorithm 2 line 21.
- Downstream finalization:
  - FinalizationCert(s) is generated once Σ of FinalVote(s) reaches ≥60%: `specs/tla/alpenglow/Certificates.tla:298` (CanCreateFinalizationCert) and aggregated in `specs/tla/alpenglow/VoteStorage.tla:168` (GenerateCertificate).
  - A node finalizes the unique notarized block in s when it has both NotarizationCert(s, b) and FinalizationCert(s): `specs/tla/alpenglow/MainProtocol.tla:255`–`:262`, reflecting Definition 14.

4. The conclusion of the audit.

- The TryFinal guard and effects match Algorithm 2 (lines 18–21) exactly: it requires BlockNotarized(s, h), the validator’s own NotarVote for h in s, and absence of BadWindow; on success it broadcasts FinalVote(s) and marks ItsOver.
- The modeling choice to test “VotedNotar(h) ∈ state[s]” via a pool-based predicate `VotedForBlock` enforces the same constraint with correct hash binding.
- FinalVote creation uses `NoBlock` and is slot-scoped, aligning with Table 5/6 and Definition 14; certificate generation and finalization logic downstream is consistent with the whitepaper.
- Therefore, with respect to the paper, TryFinal is correct in safety and intended behavior. Any difference versus the pseudocode is cosmetic and does not change semantics.

5. Any open questions or concerns.

- State parameterization vs. pool queries:
  - The paper’s state objects are parameterized (e.g., VotedNotar(hash(b)), BlockNotarized(hash(b))). The spec stores unparameterized flags and relies on the event parameter and pool queries to carry the hash binding. This is sound but slightly indirect for readers. See `specs/tla/alpenglow/VotorCore.tla:60`–`:72` where flags are strings.
- Event placement vs. pseudo-code’s immediate TRYFINAL call:
  - Algorithm 2 calls TRYFINAL immediately after a successful TRYNOTAR (line 15). In the model, finalization voting happens upon handling BlockNotarized(s, h) (`EmitBlockNotarized` → `HandleBlockNotarized` → `TryFinal`). This can delay the attempt by one scheduling step but is behaviorally equivalent; still worth calling out as a modeling deviation.
- NotarFallbackCert does not trigger BlockNotarized:
  - Per Definition 15, BlockNotarized is tied to NotarizationCert only. This matches the model (`ShouldEmitBlockNotarized` checks notarization only), but some readers might expect fallback notarization to also “notarize” a block. The paper’s terminology reserves the event for the notarization certificate; the model follows that strictly.

6. Any suggestions for improvement.

- Documentation tweak: Add a brief comment above `TryFinal` noting the modeling choice (pool-backed `VotedForBlock` in place of parameterized `VotedNotar(h)`), with a pointer to Algorithm 2 lines 18–21 and Definition 15.
- Optional: Parameterize state flags for clarity (e.g., store `VotedNotar(h)` and `BlockNotarized(h)` as values rather than plain strings) and adjust guards to use them. This would more literally mirror Definition 18 without changing behavior.
- Micro-optimization parity: Consider invoking `TryFinal` at the end of `TryNotar` (as in Algorithm 2 line 15) to attempt immediate finalization if BlockNotarized(s, h) is already in state. Functionally redundant given the event path, but it reduces latency in models that schedule events later.
- Add an invariant for auditability: “FinalVote issuance implies BlockNotarized(s, h) and the issuer’s `NotarVote(s, h)` exist and `BadWindow ∉ state[s]`.” This is already enforced by `TryFinal` but codifying it as an invariant can aid TLC runs and future refactors.

```text
Key cross-file references
- specs/tla/alpenglow/VotorCore.tla:141 (TryFinal)
- specs/tla/alpenglow/VotorCore.tla:86 (VotedForBlock), :74 (HasState), :78 (AddState)
- specs/tla/alpenglow/VotorCore.tla:246 (HandleBlockNotarized)
- specs/tla/alpenglow/VoteStorage.tla:222 (ShouldEmitBlockNotarized), :84 (StoreVote), :142 (GetVotesForSlot)
- specs/tla/alpenglow/Messages.tla:97 (CreateFinalVote)
- specs/tla/alpenglow/Certificates.tla:298 (CanCreateFinalizationCert), :309 (CreateFinalizationCert)
- specs/tla/alpenglow/MainProtocol.tla:255 (FinalizeBlock slow/fast conditions)
```

