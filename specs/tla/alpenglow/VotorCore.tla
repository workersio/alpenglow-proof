---------------------------- MODULE VotorCore ----------------------------
(***************************************************************************
 * VOTOR VOTING STATE MACHINE FOR ALPENGLOW
 *
 * Implements the state machine described in Whitepaper §2.4. Readers can
 * cross-reference the pseudocode directly:
 *   • Definition 18 — what each slot remembers (`ParentReady`, `Voted`, ...).
 *   • Algorithm 1 — event handlers (`Block`, `Timeout`, `SafeToNotar`, ...).
 *   • Algorithm 2 — helper procedures (`TRYNOTAR`, `TRYSKIPWINDOW`, ...).
 * Every guard here matches the corresponding line in the pseudocode, so the
 * behaviour is easy to follow even without deep TLA+ knowledge.
 ***************************************************************************)

EXTENDS Naturals, FiniteSets, Sequences, TLC, 
        Messages, Blocks, 
        Certificates, VoteStorage

CONSTANTS
    DeltaTimeout,   \* Timeout delay parameter (e.g., 3Δ)
    DeltaBlock      \* Block time parameter (e.g., 400ms)

ASSUME
    /\ DeltaTimeout \in Nat \ {0}
    /\ DeltaBlock \in Nat \ {0}

\* Alias types for clarity (audit 0015 suggestion)
TimeTS == Nat
TimeoutTS == Nat

\* ============================================================================
\* VOTOR STATE (Definition 18 from whitepaper)
\* ============================================================================

(***************************************************************************
 * State objects that can be added to validator state (Def. 18), with
 * implementation notes on parameterization:
 * - ParentReady(h): Ready to vote on blocks with parent h.
 *   Implementation: boolean flag; the bound hash `h` is recorded in
 *   `parentReady[slot]` and used by guards.
 * - Voted: Cast initial vote (notar or skip) in this slot.
 *   Modeling note: not explicitly enumerated in Def. 18, but referenced
 *   by Algorithm 1/2 to gate re-voting. Included to mirror the pseudo-code.
 * - VotedNotarTag: Bookkeeping tag set when casting a notarization vote.
 *   Implementation: unparameterized tag; the specific block hash is
 *   witnessed by the stored NotarVote in Pool and queried via
 *   `VotedForBlock(..)` rather than reading the tag.
 * - BlockNotarized(h): Pool has a notarization certificate for block h.
 *   Implementation: boolean flag on the slot; the specific hash `h` is
 *   carried by the BlockNotarized event parameter and passed to `TryFinal`.
 * - ItsOver: Cast finalization vote; done with this slot.
 * - BadWindow: Cast skip or fallback vote in this slot/window.
 * - BlockSeen: First Block(...) event consumed for this slot.
 *   Modeling note: not part of Def. 18; used only to ignore duplicate
 *   Block deliveries in the model (leaders produce one block per slot).
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
\* (e.g., `VotedForBlock`), or event parameters. `BlockSeen` is a modeling
\* artifact for deduplicating Block delivery and is not a protocol state.

\* Validator state structure
ValidatorState == [
    id: Validators,                                  \* Validator identifier
    state: [Slots -> SUBSET StateObject],           \* State flags per slot
    parentReady: [Slots -> BlockHashes \cup {NoBlock}], \* Parent hash per slot (Def. 18: models ParentReady(h) binding)
    pendingBlocks: [Slots -> SUBSET Block],         \* Blocks to retry
                                                   \* Modeling note: The whitepaper (Alg.1 L5)
                                                   \* buffers a single pending block per slot.
                                                   \* We model this as a set for generality and
                                                   \* idempotence. Due to nondeterministic delivery
                                                   \* there may be multiple candidates buffered; the
                                                   \* guards in TRYNOTAR and the sweep in
                                                   \* CHECKPENDINGBLOCKS ensure only one initial
                                                   \* vote per slot (Pool multiplicity) and that the
                                                   \* set is eventually cleared upon success. `MainProtocol.ReceiveBlock`
                                                   \* delivers only the first complete block per
                                                   \* slot to Algorithm 1 in this model. See also
                                                   \* `PendingBlocksSingleton` for the intended
                                                   \* singleton discipline and `...SlotAligned`.
    pool: PoolState,                                \* Vote/certificate storage
    clock: TimeTS,                                  \* Local clock
    timeouts: [Slots -> TimeoutTS]                  \* Scheduled timeouts
]

\* Initialize validator state (Definition 18)
\* Commentary: Per Def. 18, per-slot state starts empty. Parameterized
\* state objects (ParentReady(h), VotedNotar(h), BlockNotarized(h)) are
\* represented via boolean tags in `state[s]` with their bound hashes
\* carried in companion structures (e.g., `parentReady[s]`) or event
\* parameters; see notes above.
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
\* STATE HELPERS
\* ============================================================================

\* Check if validator has a specific state in slot
\* Precondition: `slot \in Slots` (enforced by callers and ValidatorStateOK).
HasState(validator, slot, stateObj) ==
    stateObj \in validator.state[slot]

\* Add state object to validator's slot
\* Precondition: `slot \in Slots` (enforced by callers and ValidatorStateOK).
AddState(validator, slot, stateObj) ==
    [validator EXCEPT !.state[slot] = validator.state[slot] \union {stateObj}]

\* Check if validator voted for a specific block
VotedForBlock(validator, slot, blockHash) ==
    \E vote \in GetVotesForSlot(validator.pool, slot) :
        /\ vote.validator = validator.id
        /\ IsInitialNotarVote(vote)
        /\ vote.blockHash = blockHash

\* Derived helpers (audit 0016 suggestion): expose the hash associated
\* with a BlockNotarized state via the Pool certificate for readability
\* in properties and invariants, without parameterizing the state tag.
BlockNotarizedHashes(validator, slot) ==
    IF HasState(validator, slot, "BlockNotarized")
    THEN { h \in BlockHashes : HasNotarizationCert(validator.pool, slot, h) }
    ELSE {}

\* Optional chooser when uniqueness is enforced by Pool invariants.
\* Returns NoBlock when the set is empty. Domain: BlockHashes ∪ {NoBlock}.
BlockNotarizedHashOpt(validator, slot) ==
    IF BlockNotarizedHashes(validator, slot) = {}
    THEN NoBlock
    ELSE CHOOSE h \in BlockNotarizedHashes(validator, slot) : TRUE


\* ============================================================================
\* TRYFINAL - Try to cast finalization vote (Algorithm 2, lines 18-21)
\* ============================================================================

(***************************************************************************
 * Vote to finalize a notarized block. Mirrors Whitepaper Algorithm 2
 * (lines 18–21): requires notarization, our own notar vote, and no
 * fallback activity in the window (`BadWindow`).
 ***************************************************************************)

(*
 * Modeling note (audit 0016): The whitepaper expresses the guard using
 * parameterized state (e.g., VotedNotar(hash(b))). Here, the hash binding
 * is carried by the BlockNotarized event and enforced via Pool queries:
 * we check VotedForBlock(_, s, blockHash) instead of storing a
 * parameterized VotedNotar(h) flag. This is equivalent to Algorithm 2
 * lines 18–21; see also Definition 15 (BlockNotarized event).
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
\* TRYNOTAR - Try to cast notarization vote (Algorithm 2, lines 7-17)
\* ============================================================================

(***************************************************************************
 * Try to vote for a block. Mirrors Whitepaper Algorithm 2 (lines 7–17):
 * 1. No prior vote in this slot
 * 2. Either
 *    a) first slot AND `ParentReady` for the indicated parent, or
 *    b) later slot AND notarized the parent in slot s-1
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
\* TRYSKIPWINDOW - Skip unvoted slots (Algorithm 2, lines 22-27)
\* ============================================================================

(***************************************************************************
 * Skip all unvoted slots in the window, per Whitepaper Algorithm 2
 * (lines 22–27). Triggered by timeouts or fallback events.
 * Cross-refs: Def. 18 (BadWindow semantics), Def. 12 (StoreVote multiplicity
 * and idempotence). Network broadcast is modeled elsewhere (MainProtocol).
 * Typing note: `validator.id \in Validators` is guaranteed by ValidatorStateOK.
 ***************************************************************************)

TrySkipWindow(validator, slot) ==
    LET windowSlots == WindowSlots(slot)
        slotsToSkip == {s \in windowSlots : 
                        s \in Slots /\ ~HasState(validator, s, "Voted")}
    IN
        IF slotsToSkip # {} THEN
            LET RECURSIVE SkipSlots(_,_)
                SkipSlots(val, slots) ==
                    IF slots = {} THEN val
                    ELSE 
                        LET s == CHOOSE x \in slots : TRUE
                            vote == CreateSkipVoteForSlot(val.id, s)
                            newVal1 == AddState(val, s, "Voted")
                            newVal2 == AddState(newVal1, s, "BadWindow")
                            poolWithVote == StoreVote(newVal2.pool, vote)
                            updatedVal == [newVal2 EXCEPT 
                                          !.pool = poolWithVote,
                                          !.pendingBlocks[s] = {}]
                        IN SkipSlots(updatedVal, slots \ {s})
            IN SkipSlots(validator, slotsToSkip)
        ELSE validator

\* ============================================================================
\* CHECK PENDING BLOCKS
\* ============================================================================

CheckPendingBlocks(validator) ==
    LET RECURSIVE Step(_)
        Step(val) ==
            LET eligibleSlots == { s \in Slots :
                                    /\ val.pendingBlocks[s] # {}
                                    /\ \E b \in val.pendingBlocks[s] : TryNotar(val, b) # val }
            IN IF eligibleSlots = {} THEN val
            ELSE 
                \* Choose the earliest eligible slot deterministically
                LET s == CHOOSE x \in eligibleSlots : \A y \in eligibleSlots : x <= y
                    eligibleBlocks == { b \in val.pendingBlocks[s] : TryNotar(val, b) # val }
                    b == CHOOSE x \in eligibleBlocks : TRUE
                IN Step(TryNotar(val, b))
    IN Step(validator)

\* ============================================================================
\* EVENT HANDLERS (Algorithm 1)
\* ============================================================================

(***************************************************************************
 * Handle Block event (Whitepaper Algorithm 1, lines 1–5).
 * On delivery we attempt to notarize immediately; otherwise retain as
 * pending until prerequisites (parent readiness) hold.
 *
 * Notes
 * - We generalize the paper's single pending entry to a set; union below
 *   is idempotent and deduplicates repeated deliveries.
 * - `TryNotar` clears the slot's pending set on success and immediately
 *   invokes `TryFinal` (Alg.2 L15). Thus the success branch here only
 *   needs to re-check other pending slots.
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
                validator.pendingBlocks[slot] \union {block}]  \* Set union deduplicates; idempotent buffering
        ELSE validator

(***************************************************************************
 * Handle Timeout event (Whitepaper Algorithm 1, lines 6–8).
 * On timer expiry the validator casts skip votes for all slots still
 * lacking initial votes.
 ***************************************************************************)

HandleTimeout(validator, slot) ==
    LET cleared == [validator EXCEPT !.timeouts[slot] = 0]
    IN IF HasState(cleared, slot, "ItsOver") THEN
           cleared
       ELSE IF ~HasState(cleared, slot, "Voted") THEN
           TrySkipWindow(cleared, slot)
       ELSE cleared

(***************************************************************************
 * Handle BlockNotarized event (Whitepaper Algorithm 1, lines 9–11).
 * Marks the slot as notarized and attempts to cast the slow-path
 * finalization vote. Note the flag is slot-scoped; the concrete `blockHash`
 * carried by the event preserves the hash binding from the paper.
 ***************************************************************************)

HandleBlockNotarized(validator, slot, blockHash) ==
    LET newValidator == AddState(validator, slot, "BlockNotarized")
    IN TryFinal(newValidator, slot, blockHash)

(***************************************************************************
 * Handle ParentReady event (Whitepaper Algorithm 1, lines 12–15).
 * Records the parent hash for the first slot of the window, schedules all
 * timeouts, and re-checks pending blocks that might now be safe.
 ***************************************************************************)

HandleParentReady(validator, slot, parentHash) ==
    LET newValidator == AddState(validator, slot, "ParentReady")
        withParent == [newValidator EXCEPT !.parentReady[slot] = parentHash]
        afterCheck == CheckPendingBlocks(withParent)
        \* Self-contained per Def. 17: compute window using its first slot
        first == FirstSlotOfWindow(slot)
        windowSlots == WindowSlots(first)
        \* Set timeouts for all slots in window
        RECURSIVE SetTimeouts(_,_)
        SetTimeouts(val, slots) ==
            IF slots = {} THEN val
            ELSE
                LET s == CHOOSE x \in slots : TRUE
                    timeout == val.clock + DeltaTimeout + ((s - first + 1) * DeltaBlock)
                IN SetTimeouts([val EXCEPT !.timeouts[s] = timeout], slots \ {s})
        \* Note: WindowSlots already ranges over production slots; no extra \cap Slots needed
    IN SetTimeouts(afterCheck, windowSlots)

(***************************************************************************
 * Handle SafeToNotar event (Whitepaper Algorithm 1, lines 16–20).
 * After verifying Definition 16 conditions, emits skip votes for any
 * missed slots and casts the notar-fallback vote.
 *
 * Note: We accept the block `b` (available at the call site) and use the
 * block-typed wrapper to preserve slot–hash pairing by construction.
 * Inline reference: Alg. 1 L16–L20; Def. 16.
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
 * Handle SafeToSkip event (Whitepaper Algorithm 1, lines 21–25).
 * Similar to the notar fallback but issues skip-fallback votes once
 * Definition 16’s inequality is met.
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

\* Advance clock and process expired timeouts
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
            RECURSIVE ProcessTimeouts(_,_)
        ProcessTimeouts(val, slots) ==
            IF slots = {} THEN val
            ELSE
                LET s == CHOOSE x \in slots : \A y \in slots : x <= y
                    newVal == HandleTimeout(val, s)
                IN ProcessTimeouts(newVal, slots \ {s})
        IN [ProcessTimeouts(validator, expiredTimeouts) EXCEPT !.clock = newTime]

\* ============================================================================
\* TYPE INVARIANT
\* ============================================================================

ValidatorStateOK(validator) ==
    /\ validator.id \in Validators
    /\ validator.state \in [Slots -> SUBSET StateObject]
    /\ validator.parentReady \in [Slots -> BlockHashes \cup {NoBlock}]
    /\ validator.pendingBlocks \in [Slots -> SUBSET Block]
    /\ PoolTypeOK(validator.pool)
    /\ validator.clock \in TimeTS
    /\ validator.timeouts \in [Slots -> TimeoutTS]

\* Representation invariants (audit 0015 suggestion)
ParentReadyConsistency(validator) ==
    \A s \in Slots : HasState(validator, s, "ParentReady") <=> validator.parentReady[s] # NoBlock

\* Readability lemma (audit 2025-09-25 ValidatorStateOK suggestion):
\* If ParentReady holds in slot s, then the companion field carries a
\* concrete block hash (follows from ParentReadyConsistency and typing).
ParentReadyImpliesHashSet(validator) ==
    \A s \in Slots : HasState(validator, s, "ParentReady") => validator.parentReady[s] \in BlockHashes

\* Linking lemma (audit 2025-09-25): witnessing our initial notar vote for
\* block hash `h` in slot `s` via the local Pool implies we have recorded the
\* slot-local `Voted` flag. This reflects TryNotar's atomic update that stores
\* the vote and sets state, and clarifies the intended coupling between Pool
\* and state.
PoolInitialNotarVoteImpliesVoted(validator) ==
    \A s \in Slots : \A h \in BlockHashes :
        VotedForBlock(validator, s, h) => HasState(validator, s, "Voted")

PendingBlocksSingleton(validator) ==
    \A s \in Slots : Cardinality(validator.pendingBlocks[s]) <= 1

\* Domain discipline for pending blocks (audit 0015 suggestion)
PendingBlocksSlotAligned(validator) ==
    \A s \in Slots : \A b \in validator.pendingBlocks[s] : b.slot = s

\* Optional lemma (audit suggestion): votes produced for valid blocks are
\* valid by construction (content-only, signatures abstracted).
THEOREM TryNotarProducesValidNotarVote ==
    \A v \in Validators, b \in Block :
        IsValidBlock(b) => IsValidVote(CreateNotarVoteForBlock(v, b))

\* Audit lemma (creation-time validity): TrySkipWindow constructs skip votes
\* using the typed wrapper; these are valid by construction.
THEOREM TrySkipWindowProducesValidSkipVotes ==
    \A validator, s \in Slots :
        ValidatorStateOK(validator) /\ ~HasState(validator, s, "Voted")
            => IsValidVote(CreateSkipVoteForSlot(validator.id, s))

\* Post-condition lemma (audit 0016): After TrySkipWindow(v, s), every slot
\* k in the same window that was previously unvoted gains {Voted, BadWindow}
\* and has its pending blocks cleared.
TrySkipWindowSetsFlagsAndClearsPending(v, s) ==
    LET after == TrySkipWindow(v, s)
    IN \A k \in WindowSlots(s) :
        (~HasState(v, k, "Voted") /\ k \in Slots)
            => /\ HasState(after, k, "Voted")
               /\ HasState(after, k, "BadWindow")
               /\ after.pendingBlocks[k] = {}

\* Idempotence lemma (audit 0016): applying TrySkipWindow twice is a no-op
\* after the first application (StoreVote multiplicity + state flags).
TrySkipWindowIdempotent(v, s) ==
    TrySkipWindow(TrySkipWindow(v, s), s) = TrySkipWindow(v, s)

\* Optional verification predicate (audit 0016): After scheduling in
\* HandleParentReady, each timeout for the leader window is strictly
\* greater than the pre-call clock (Def. 17, with DeltaTimeout > 0).
TimeoutsScheduledInFutureAfterParentReady(v, s, h) ==
    LET after == HandleParentReady(v, s, h)
        first == FirstSlotOfWindow(s)
    IN \A i \in WindowSlots(first) : after.timeouts[i] > v.clock

\* ============================================================================
\* LOCAL SAFETY (Lemma 22): No mixing finalization and fallback per-slot
\* ============================================================================

\* Lemma 22 (validator-local form): a slot marked finalized (ItsOver)
\* never also records fallback/skip activity (BadWindow), and conversely.
\* These reflect Algorithm 1 (L16–L20, L21–L25) guards and TryFinal’s
\* precondition (~BadWindow), making the mutual exclusion explicit.
Lemma22_ItsOverImpliesNotBadWindow(validator) ==
    \A s \in Slots : HasState(validator, s, "ItsOver") => ~HasState(validator, s, "BadWindow")

Lemma22_BadWindowImpliesNotItsOver(validator) ==
    \A s \in Slots : HasState(validator, s, "BadWindow") => ~HasState(validator, s, "ItsOver")

\* ============================================================================
\* FINALIZATION GUARD INVARIANT (audit 0016)
\* ============================================================================

\* If a validator has issued its finalization vote for a slot (ItsOver),
\* then TryFinal’s guard held: the slot is notarized, the validator voted
\* for the notarized hash, and no fallback occurred in that slot/window.
\* This mirrors Algorithm 2 (lines 18–21) and aids TLC.
FinalVoteIssuanceImpliesPrereqs(validator) ==
    \A s \in Slots :
        HasState(validator, s, "ItsOver") =>
            /\ HasState(validator, s, "BlockNotarized")
            /\ ~HasState(validator, s, "BadWindow")
            /\ \E h \in BlockHashes :
                    HasNotarizationCert(validator.pool, s, h)
                    /\ VotedForBlock(validator, s, h)

\* ============================================================================
\* NO FINAL VOTE AFTER BADWINDOW (audit 0017)
\* ============================================================================

\* Verification aid: once BadWindow holds for a slot, the validator does not
\* store a FinalVote for that slot in its Pool. This follows from TryFinal’s
\* guard (~BadWindow) and Definition 12’s multiplicity rules, and makes the
\* safety argument explicit for model checking.
NoFinalVoteStoredAfterBadWindow(validator) ==
    \A s \in Slots : HasState(validator, s, "BadWindow") =>
        Cardinality({ v \in validator.pool.votes[s][validator.id] : v.type = "FinalVote" }) = 0

=============================================================================
