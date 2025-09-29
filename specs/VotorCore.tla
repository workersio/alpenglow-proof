---------------------------- MODULE VotorCore ----------------------------
(***************************************************************************
 * VOTOR VOTING STATE MACHINE FOR ALPENGLOW
 *
 * Whitepaper references
 * - §2.6 Votor: Algorithm 1 (event loop) and Algorithm 2 (helpers), pp. 24–25.
 * - §2.5 Pool: Definitions 12–15 (votes, certificates, Pool events), pp. 20–22.
 * - Definition 17 (timeouts), p. 23; Definition 18 (Votor state), pp. 23–24.
 * - §2.4 introduces vote/certificate message types used by Pool.
 *
 * Rationale
 * - This module implements the validator-local Votor state machine. The code
 *   mirrors Algorithm 1 and Algorithm 2 line-by-line; guards and effects are
 *   annotated to match the paper’s predicates and events. Where the paper
 *   uses parameterized state (e.g., VotedNotar(hash(b))), we carry the hash via
 *   Pool queries or event parameters for readability and type simplicity.
 ***************************************************************************)

EXTENDS Naturals, FiniteSets, Sequences, TLC, 
        Messages, Blocks, 
        Certificates, VoteStorage

CONSTANTS
    \* Whitepaper: Definition 17 (timeouts), p. 23
    \* - DeltaTimeout (Δ_timeout): residual synchrony/observation slack.
    \* - DeltaBlock   (Δ_block): protocol block time.
    \* Modeling: both share the same time base as `clock`.
    DeltaTimeout,   \* Timeout delay parameter (Def. 17; e.g., 3Δ)
    DeltaBlock      \* Block time parameter (Def. 17; e.g., 400ms)

ASSUME
    /\ DeltaTimeout \in Nat \ {0}
    /\ DeltaBlock \in Nat \ {0}

\* Alias types for clarity (audit 0015 suggestion)
TimeTS == Nat
TimeoutTS == Nat

\* ============================================================================
\* VOTOR STATE (Whitepaper Definition 18, pp. 23–24)
\* ============================================================================

(***************************************************************************
 * State objects (per Def. 18), with modeling notes:
 * - ParentReady(h): Ready to vote on blocks with parent h.
 *   Modeling: store a boolean tag; the bound hash is carried in
 *   `parentReady[slot]` and used by guards (Alg. 1 L12–15; Def. 15, Def. 17).
 * - Voted: Cast the unique initial vote (notar or skip) in this slot.
 *   Paper: Def. 18 mentions the effect; Lemma 20 asserts uniqueness.
 * - VotedNotarTag: Tag set when casting a notarization vote.
 *   Modeling: unparameterized; the concrete hash is witnessed by Pool via
 *   the stored NotarVote (Def. 12) and checked by `VotedForBlock(..)`.
 * - BlockNotarized(h): Pool has a notarization certificate for hash h.
 *   Paper: Def. 15 event; Def. 13 certificate; used by TRYFINAL (Alg. 2 L18–21).
 * - ItsOver: Cast finalization vote; no further votes in slot (Alg. 2 L20–21).
 * - BadWindow: Slot participated in a skip or fallback path (Alg. 1 L16–25).
 * - BlockSeen: First Block(...) event consumed for this slot.
 *   Modeling-only: helps deduplicate deliveries from Blokstor (Def. 10).
 ***************************************************************************)

StateObject == {
    "ParentReady",      \* Pool emitted ParentReady event
    "Voted",            \* Cast notarization or skip vote
    "VotedNotarTag",    \* Local tag added when casting notar vote
    "BlockNotarized",   \* Pool has notarization certificate
    "ItsOver",          \* Cast finalization vote, done with slot
    "BadWindow",        \* Cast skip or fallback vote
    "BlockSeen"         \* First Block(...) event consumed for this slot
}

\* Commentary: Items correspond to Def. 18 but parameterized ones
\* (ParentReady, VotedNotar, BlockNotarized) are represented by boolean
\* flags, with the bound hash tracked via `parentReady[slot]`, Pool queries
\* (Def. 12; e.g., `VotedForBlock`), or event parameters (Def. 15). `BlockSeen`
\* is a modeling artifact (not protocol state) to deduplicate Block delivery
\* from Blokstor (Def. 10) and ensure single processing per slot.

\* Validator state structure (Def. 18 fields; Alg. 2 helpers)
ValidatorState == [
    id: Validators,                                     \* Validator identifier
    state: [Slots -> SUBSET StateObject],               \* State flags per slot
    parentReady: [Slots -> BlockHashes \cup {NoBlock}], \* Parent hash per slot (Def. 18: models ParentReady(h) binding)
    pendingBlocks: [Slots -> SUBSET Block],             \* Blocks to retry
    \* Whitepaper: Alg. 1 L5 stores at most one
    \* pending block per slot. We generalize to a set
    \* for idempotence; TRYNOTAR and CHECKPENDINGBLOCKS
    \* (Alg. 2 L28–30) ensure only one initial vote per
    \* slot (Def. 12 multiplicity) and eventual clearing.
    \* MainProtocol delivers only the first complete
    \* block per slot (Def. 10); see also
    \* `PendingBlocksSingleton` and `...SlotAligned`.
    pool: PoolState,                                   \* Vote/certificate storage
    clock: TimeTS,                                     \* Local clock
    timeouts: [Slots -> TimeoutTS]                     \* Scheduled timeouts
]

\* Initialize validator state — Whitepaper: Definition 18 (pp. 23–24)
\* Commentary: Per Def. 18, per-slot state starts empty. Parameterized
\* state (ParentReady(h), VotedNotar(h), BlockNotarized(h)) is modeled as
\* unparameterized tags; the bound hashes are carried in
\* `parentReady[s]` (Alg. 1 L12–15), Pool (Def. 12–13), or event params
\* (Def. 15, Def. 16).
InitValidatorState(validatorId) == [
    id |-> validatorId,
    state |-> [s \in Slots |-> {}],
    parentReady |-> [s \in Slots |-> NoBlock],
    pendingBlocks |-> [s \in Slots |-> {}],
    pool |-> InitPool,
    clock |-> 0,
    timeouts |-> [s \in Slots |-> 0]
]

\* ============================================================================
\* STATE HELPERS (ties to Def. 12–18)
\* ============================================================================

\* Check if validator has a specific state in slot (Def. 18)
\* Precondition: `slot \in Slots` (enforced by callers and ValidatorStateOK).
HasState(validator, slot, stateObj) ==
    stateObj \in validator.state[slot]

\* Add state object to validator's slot (Def. 18)
\* Precondition: `slot \in Slots` (enforced by callers and ValidatorStateOK).
AddState(validator, slot, stateObj) ==
    [validator EXCEPT !.state[slot] = validator.state[slot] \cup {stateObj}]

\* Check if validator voted for a specific block
\* Whitepaper: Def. 12 (first notar/skip per slot); uses Pool to witness
\* our own notar vote for a concrete block hash in slot s.
VotedForBlock(validator, slot, blockHash) ==
    \E vote \in GetVotesForSlot(validator.pool, slot) :
        /\ vote.validator = validator.id
        /\ IsInitialNotarVote(vote)
        /\ vote.blockHash = blockHash

\* Derived helpers (audit 0016): expose the hash(es) associated with a
\* BlockNotarized flag via Pool certificates (Def. 13/15) without
\* parameterizing the local state tag.
BlockNotarizedHashes(validator, slot) ==
    IF HasState(validator, slot, "BlockNotarized")
    THEN { h \in BlockHashes : HasNotarizationCert(validator.pool, slot, h) }
    ELSE {}

\* ============================================================================
\* TRYFINAL - Try to cast finalization vote (Alg. 2, L18–21; Def. 14–15)
\* ============================================================================

(***************************************************************************
 * Finalization vote when safe.
 * Whitepaper: Algorithm 2 (L18–21), Def. 14 (finalization), Def. 15 (Pool events).
 * Reasoning: requires notarization of the hash, our own notar vote for it,
 * and no fallback activity (BadWindow) in this slot/window.
 ***************************************************************************)

(*
 * Modeling note (audit 0016): The whitepaper expresses the guard using
 * parameterized state (e.g., VotedNotar(hash(b))). Here, the hash binding
 * is carried by the BlockNotarized event and enforced via Pool queries:
 * we check VotedForBlock(_, s, blockHash) instead of storing a
 * parameterized VotedNotar(h) flag. This is equivalent to Algorithm 2
 * lines 18–21; see also Definition 15 (BlockNotarized event) and
 * Definition 14 (finalization conditions).
 *)
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
            IN [newState EXCEPT 
                    !.pool = poolWithVote,
                    !.pendingBlocks[slot] = {}]  \* Clear pending for this slot once finalized (audit 0015 suggestion)
        ELSE validator

\* ============================================================================
\* TRYNOTAR - Try to cast notarization vote (Alg. 2, L7–17)
\* ============================================================================

(***************************************************************************
 * Initial notarization vote.
 * Whitepaper: Algorithm 2 (L7–17), Def. 18 (Voted/VotedNotar), Def. 15.
 * Reasoning: one initial vote per slot (Lemma 20). Allowed when either:
 *  - first slot of window and ParentReady(parent) holds (Alg. 1 L12–15), or
 *  - later slot and we notar-voted the parent in s-1.
 ***************************************************************************)

TryNotar(validator, block) ==
    LET 
        slot == block.slot
        isFirstSlot == IsFirstSlotOfWindow(slot)
        parentSlot == slot - 1
        
        canVote == 
            /\ ~HasState(validator, slot, "Voted")
            /\ \/ (isFirstSlot
                    /\ HasState(validator, slot, "ParentReady")
                    /\ validator.parentReady[slot] = block.parent)
               \/ (~isFirstSlot /\ parentSlot \in Slots /\ 
                   VotedForBlock(validator, parentSlot, block.parent))
    IN
        IF canVote THEN
            LET vote == CreateNotarVoteForBlock(validator.id, block)
                newState1 == AddState(validator, slot, "Voted")
                newState2 == AddState(newState1, slot, "VotedNotarTag")
                poolWithVote == StoreVote(newState2.pool, vote)
                withVote == [newState2 EXCEPT 
                             !.pool = poolWithVote,
                             !.pendingBlocks[slot] = {}]  \* Clear all pending blocks for this slot (Alg. 2 line 14)
                afterFinal == TryFinal(withVote, slot, block.hash)  \* Immediately attempt finalization (Alg. 2 line 15)
            IN afterFinal
        ELSE validator

\* ============================================================================
\* TRYSKIPWINDOW - Skip unvoted slots (Alg. 2, L22–27)
\* ============================================================================

(***************************************************************************
 * Skip all unvoted slots in the window.
 * Whitepaper: Algorithm 2 (L22–27). Triggered by timeouts or fallback events.
 * Reasoning: enforce unique initial vote (Def. 12, Lemma 20), mark BadWindow,
 * and clear pending to prevent later notar votes in skipped slots.
 * Network broadcast modeled elsewhere (MainProtocol).
 ***************************************************************************)

TrySkipWindow(validator, slot) ==
    LET windowSlots == WindowSlots(slot)
        slotsToSkip == {s \in windowSlots : 
                        s \in Slots /\ ~HasState(validator, s, "Voted")}
    IN
        IF slotsToSkip # {} THEN
            LET SkipSlots[state \in ValidatorState, remainingSlots \in SUBSET slotsToSkip] ==
                    IF remainingSlots = {} THEN state
                    ELSE 
                        LET s == CHOOSE x \in remainingSlots : TRUE
                            vote == CreateSkipVoteForSlot(state.id, s)
                            newVal1 == AddState(state, s, "Voted")
                            newVal2 == AddState(newVal1, s, "BadWindow")
                            poolWithVote == StoreVote(newVal2.pool, vote)
                            updatedVal == [newVal2 EXCEPT 
                                          !.pool = poolWithVote,
                                          !.pendingBlocks[s] = {}]
                        IN SkipSlots[updatedVal, remainingSlots \ {s}]
            IN SkipSlots[validator, slotsToSkip]
        ELSE validator

\* ============================================================================
\* CHECK PENDING BLOCKS (Alg. 2, L28–30)
\* ============================================================================

CheckPendingBlocks(validator) ==
    LET Step[val \in ValidatorState] ==
            LET eligibleSlots == { s \in Slots :
                                    /\ val.pendingBlocks[s] # {}
                                    /\ \E b \in val.pendingBlocks[s] : TryNotar(val, b) # val }
            IN IF eligibleSlots = {} THEN val
            ELSE 
                \* Choose the earliest eligible slot deterministically
                LET s == CHOOSE x \in eligibleSlots : \A y \in eligibleSlots : x <= y
                    eligibleBlocks == { b \in val.pendingBlocks[s] : TryNotar(val, b) # val }
                    b == CHOOSE x \in eligibleBlocks : TRUE
                IN Step[TryNotar(val, b)]
    IN Step[validator]

\* ============================================================================
\* EVENT HANDLERS (Algorithm 1, pp. 24–25)
\* ============================================================================

(***************************************************************************
 * Handle Block event (Alg. 1, L1–5; Def. 10 Blokstor ► Block(...)).
 * On delivery attempt notarization immediately, else retain as pending until
 * ParentReady prerequisites hold.
 * Notes
 * - We generalize the paper's single pending entry to a set; union is idempotent.
 * - `TryNotar` clears pending on success and immediately invokes `TryFinal`
 *   (Alg. 2 L15), so we only re-check other pending slots here.
 ***************************************************************************)

HandleBlock(validator, block) ==
    LET slot == block.slot
        tryResult == TryNotar(validator, block)
    IN
        IF tryResult # validator THEN
            CheckPendingBlocks(tryResult)  \* Successfully voted; re-evaluate pending
        ELSE IF ~HasState(validator, slot, "Voted") THEN
            \* Store as pending to retry later
            [validator EXCEPT !.pendingBlocks[slot] = 
                validator.pendingBlocks[slot] \cup {block}]  \* Set union deduplicates; idempotent buffering
        ELSE validator

(***************************************************************************
 * Handle Timeout event (Alg. 1, L6–8; Def. 17 timeouts).
 * On timer expiry cast skip votes for all slots still lacking initial votes.
 ***************************************************************************)

HandleTimeout(validator, slot) ==
    LET cleared == [validator EXCEPT !.timeouts[slot] = 0]
    IN IF HasState(cleared, slot, "ItsOver") THEN
           cleared
       ELSE IF ~HasState(cleared, slot, "Voted") THEN
           TrySkipWindow(cleared, slot)
       ELSE cleared

(***************************************************************************
 * Handle BlockNotarized event (Alg. 1, L9–11; Def. 13–15).
 * Mark slot as notarized and attempt the slow-path finalization vote.
 * The event carries `hash(b)` to bind the specific block being notarized.
 ***************************************************************************)

HandleBlockNotarized(validator, slot, blockHash) ==
    LET newValidator == AddState(validator, slot, "BlockNotarized")
    IN TryFinal(newValidator, slot, blockHash)

(***************************************************************************
 * Handle ParentReady event (Alg. 1, L12–15; Def. 15; Def. 17).
 * Record parent hash for the first slot of the window, re-check pending,
 * then schedule timeouts for all slots in the window per Def. 17.
 ***************************************************************************)

HandleParentReady(validator, slot, parentHash) ==
    LET newValidator == AddState(validator, slot, "ParentReady")
        withParent == [newValidator EXCEPT !.parentReady[slot] = parentHash]
        afterCheck == CheckPendingBlocks(withParent)
        \* Self-contained per Def. 17: compute window using its first slot
        first == FirstSlotOfWindow(slot)
        windowSlots == WindowSlots(first)
        \* Set timeouts for all slots in window
        \* Note (Def. 17): Using `first` (the window's first slot), the
        \* term (s - first + 1) \in Nat \ {0}. With DeltaTimeout, DeltaBlock > 0
        \* and non-decreasing `clock`, all scheduled timeouts satisfy
        \* timeout > pre-call clock. See MainProtocol.TimeoutsInFuture.
        \*
        \* AUDIT NOTE (issues_claude.md §5):
        \* Variable naming: The whitepaper Definition 17 (:609) uses:
        \*   Timeout(i): clock() + Δ_timeout + (i - s + 1) · Δ_block
        \* where `i` is the slot being scheduled and `s` is the window start.
        \* The spec reverses this naming: `s` is the slot being scheduled (loop var)
        \* and `first` is the window start. The formula is mathematically identical:
        \*   Paper:  timeout(i) = clock + Δ_timeout + (i - s + 1) · Δ_block
        \*   Spec:   timeout(s) = clock + DeltaTimeout + (s - first + 1) * DeltaBlock
        \* Mapping: paper's `i` ↔ spec's `s`; paper's `s` ↔ spec's `first`.
        SetTimeouts[val \in ValidatorState, remainingSlots \in SUBSET windowSlots] ==
            IF remainingSlots = {} THEN val
            ELSE
                LET s == CHOOSE x \in remainingSlots : TRUE
                    timeout == val.clock + DeltaTimeout + ((s - first + 1) * DeltaBlock)
                IN SetTimeouts[[val EXCEPT !.timeouts[s] = timeout], remainingSlots \ {s}]
        \* Note: WindowSlots already ranges over production slots; no extra \cap Slots needed
    IN SetTimeouts[afterCheck, windowSlots]

(***************************************************************************
 * Handle SafeToNotar event (Alg. 1, L16–20; Def. 16 — fallback events).
 * Emit skip votes for any missed slots, then cast notar-fallback vote.
 * Modeling: accept block-typed `b` to preserve slot–hash pairing.
 ***************************************************************************)

HandleSafeToNotar(validator, b) ==
    LET slot == b.slot
        skipResult == TrySkipWindow(validator, slot)
    IN
        IF ~HasState(skipResult, slot, "ItsOver") THEN
            LET vote == CreateNotarFallbackVoteForBlock(skipResult.id, b)
                newValidator == AddState(skipResult, slot, "BadWindow")
                poolWithVote == StoreVote(newValidator.pool, vote)
            IN [newValidator EXCEPT !.pool = poolWithVote]
        ELSE skipResult

(***************************************************************************
 * Handle SafeToSkip event (Alg. 1, L21–25; Def. 16 — fallback events).
 * Similar to notar fallback but issues skip-fallback votes once Def. 16’s
 * inequality is met.
 ***************************************************************************)

HandleSafeToSkip(validator, slot) ==
    \* Defensive guard (audit 0017): under the spec’s emission guards this
    \* handler is never invoked when BadWindow already holds. Early return
    \* avoids redundant work if called out-of-contract.
    IF HasState(validator, slot, "BadWindow") THEN validator
    ELSE
        \* Clarity (audit 0017): TRYSKIPWINDOW acts on other unvoted slots
        \* in the window. Because SafeToSkip requires "already voted in s"
        \* (Def. 16 precondition), it will not skip s itself.
        LET skipResult == TrySkipWindow(validator, slot)
        IN
            IF ~HasState(skipResult, slot, "ItsOver") THEN
                LET vote == CreateSkipFallbackVote(skipResult.id, slot)
                    newValidator == AddState(skipResult, slot, "BadWindow")
                    poolWithVote == StoreVote(newValidator.pool, vote)
                IN [newValidator EXCEPT 
                        !.pool = poolWithVote,
                        !.pendingBlocks[slot] = {}]
            ELSE skipResult

\* ============================================================================
\* CLOCK AND TIMEOUT MANAGEMENT
\* ============================================================================

\* Advance clock and process expired timeouts (Def. 17; §2.6 clocks)
AdvanceClock(validator, newTime) ==
    \* Monotonic guard (audit 0015 suggestion): do not move clock backwards
    IF newTime < validator.clock THEN validator
    ELSE
        LET 
            \* MC note (audit 0017): `Slots` is configuration-bounded in
            \* MainProtocol (Slots = 0..MaxSlot), so this set is finite.
            expiredTimeouts == {s \in Slots :
                                   /\ validator.timeouts[s] > 0
                                   /\ validator.timeouts[s] <= newTime}
            ProcessTimeouts[val \in ValidatorState, remainingSlots \in SUBSET expiredTimeouts] ==
                IF remainingSlots = {} THEN val
                ELSE
                    LET s == CHOOSE x \in remainingSlots : \A y \in remainingSlots : x <= y
                        newVal == HandleTimeout(val, s)
                    IN ProcessTimeouts[newVal, remainingSlots \ {s}]
        IN [ProcessTimeouts[validator, expiredTimeouts] EXCEPT !.clock = newTime]

\* ============================================================================
\* TYPE INVARIANT (Def. 12–18 typing and domains)
\* ============================================================================

ValidatorStateOK(validator) ==
    /\ validator.id \in Validators
    /\ validator.state \in [Slots -> SUBSET StateObject]
    /\ validator.parentReady \in [Slots -> BlockHashes \cup {NoBlock}]
    /\ validator.pendingBlocks \in [Slots -> SUBSET Block]
    /\ PoolTypeOK(validator.pool)
    /\ validator.clock \in TimeTS
    /\ validator.timeouts \in [Slots -> TimeoutTS]

\* Representation invariants (link to Def. 18 semantics)
ParentReadyConsistency(validator) ==
    \A s \in Slots : HasState(validator, s, "ParentReady") <=> validator.parentReady[s] # NoBlock


PendingBlocksSingleton(validator) ==
    \A s \in Slots : Cardinality(validator.pendingBlocks[s]) <= 1

\* Domain discipline for pending blocks (Alg. 1 L5 intent)
PendingBlocksSlotAligned(validator) ==
    \A s \in Slots : \A b \in validator.pendingBlocks[s] : b.slot = s

\* Optional lemma: votes produced for valid blocks are valid by construction
\* (content-only, signatures abstracted; cf. §2.4/§2.5 message typing).
THEOREM TryNotarProducesValidNotarVote ==
    \A v \in Validators, b \in Block :
        IsValidBlock(b) => IsValidVote(CreateNotarVoteForBlock(v, b))

\* Creation-time validity: TRYSKIPWINDOW constructs skip votes via the
\* typed wrapper; these are valid by construction (Def. 12 vote types).
THEOREM TrySkipWindowProducesValidSkipVotes ==
    \A validator, s \in Slots :
        ValidatorStateOK(validator) /\ ~HasState(validator, s, "Voted")
            => IsValidVote(CreateSkipVoteForSlot(validator.id, s))

\* ============================================================================
\* LOCAL SAFETY (Lemma 22): No mixing finalization and fallback per-slot
\* ============================================================================

\* Lemma 22 (validator-local form): a slot marked finalized (ItsOver)
\* never also records fallback/skip activity (BadWindow), and conversely.
\* These reflect Alg. 1 (L16–L25) guards and TRYFINAL’s precondition
\* (~BadWindow), making mutual exclusion explicit.
Lemma22_ItsOverImpliesNotBadWindow(validator) ==
    \A s \in Slots : HasState(validator, s, "ItsOver") => ~HasState(validator, s, "BadWindow")

Lemma22_BadWindowImpliesNotItsOver(validator) ==
    \A s \in Slots : HasState(validator, s, "BadWindow") => ~HasState(validator, s, "ItsOver")

=============================================================================
