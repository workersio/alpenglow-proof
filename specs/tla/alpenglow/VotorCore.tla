---------------------------- MODULE VotorCore ----------------------------
(***************************************************************************
 * VOTOR VOTING STATE MACHINE FOR ALPENGLOW
 * 
 * This module implements the core voting logic from Algorithms 1-2 and
 * Definition 18 of the Alpenglow whitepaper.
 * 
 * MAPS TO WHITEPAPER:
 * - Algorithm 1: Event loop (lines 1-25)
 * - Algorithm 2: Helper functions (lines 1-30)
 * - Definition 18: Votor state objects
 * 
 * KEY CONCEPTS:
 * - Validators maintain state per slot (Voted, VotedNotar, BadWindow, etc.)
 * - Events trigger state transitions (Block arrival, Timeout, SafeToNotar)
 * - Dual paths run concurrently (fast 80% vs slow 60%)
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

\* ============================================================================
\* VOTOR STATE (Definition 18 from whitepaper)
\* ============================================================================

(***************************************************************************
 * State objects that can be added to validator state:
 * - ParentReady(h): Ready to vote on blocks with parent h
 * - Voted: Cast initial vote (notar or skip) in this slot
 * - VotedNotar(h): Cast notarization vote for block h
 * - BlockNotarized(h): Pool holds notarization cert for h
 * - ItsOver: Cast finalization vote, no more votes in slot
 * - BadWindow: Cast skip or fallback vote
 ***************************************************************************)

StateObject == {
    "ParentReady",      \* Pool emitted ParentReady event
    "Voted",            \* Cast notarization or skip vote
    "VotedNotar",       \* Cast notarization vote for specific block
    "BlockNotarized",   \* Pool has notarization certificate
    "ItsOver",          \* Cast finalization vote, done with slot
    "BadWindow"         \* Cast skip or fallback vote
}

\* Validator state structure
ValidatorState == [
    id: Validators,                                  \* Validator identifier
    state: [Slots -> SUBSET StateObject],           \* State flags per slot
    pendingBlocks: [Slots -> SUBSET Block],         \* Blocks to retry
    pool: PoolState,                                \* Vote/certificate storage
    clock: Nat,                                     \* Local clock
    timeouts: [Slots -> Nat]                        \* Scheduled timeouts
]

\* Initialize validator state
InitValidatorState(validatorId) == [
    id |-> validatorId,
    state |-> [s \in Slots |-> {}],
    pendingBlocks |-> [s \in Slots |-> {}],
    pool |-> InitPool,
    clock |-> 0,
    timeouts |-> [s \in Slots |-> 0]
]

\* ============================================================================
\* STATE HELPERS
\* ============================================================================

\* Check if validator has a specific state in slot
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

\* ============================================================================
\* TRYNOTAR - Try to cast notarization vote (Algorithm 2, lines 7-17)
\* ============================================================================

(***************************************************************************
 * Try to vote for a block. Conditions:
 * 1. Haven't voted yet in this slot
 * 2. Either:
 *    a) First slot of window AND ParentReady
 *    b) Not first slot AND voted for parent in previous slot
 ***************************************************************************)

TryNotar(validator, block) ==
    LET 
        slot == block.slot
        isFirstSlot == IsFirstSlotOfWindow(slot)
        parentSlot == slot - 1
        
        canVote == 
            /\ ~HasState(validator, slot, "Voted")
            /\ \/ (isFirstSlot /\ HasState(validator, slot, "ParentReady"))
               \/ (~isFirstSlot /\ parentSlot \in Slots /\ 
                   VotedForBlock(validator, parentSlot, block.parent))
    IN
        IF canVote THEN
            LET vote == CreateNotarVote(validator.id, slot, block.hash)
                newState1 == AddState(validator, slot, "Voted")
                newState2 == AddState(newState1, slot, "VotedNotar")
                poolWithVote == StoreVote(newState2.pool, vote)
            IN [newState2 EXCEPT 
                !.pool = poolWithVote,
                !.pendingBlocks[slot] = validator.pendingBlocks[slot] \ {block}]
        ELSE validator

\* ============================================================================
\* TRYFINAL - Try to cast finalization vote (Algorithm 2, lines 18-21)
\* ============================================================================

(***************************************************************************
 * Vote to finalize a notarized block. Conditions:
 * 1. Block is notarized (certificate exists)
 * 2. We voted to notarize this block
 * 3. Not in BadWindow state
 ***************************************************************************)

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

\* ============================================================================
\* TRYSKIPWINDOW - Skip unvoted slots (Algorithm 2, lines 22-27)
\* ============================================================================

(***************************************************************************
 * Skip all unvoted slots in the window. 
 * Called on timeout or when safe to skip.
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
                            vote == CreateSkipVote(val.id, s)
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
\* EVENT HANDLERS (Algorithm 1)
\* ============================================================================

(***************************************************************************
 * Handle Block event (Algorithm 1, lines 1-5)
 * When: New block arrives
 * Action: Try to vote for it or store as pending
 ***************************************************************************)

HandleBlock(validator, block) ==
    LET slot == block.slot
        tryResult == TryNotar(validator, block)
    IN
        IF tryResult # validator THEN
            tryResult  \* Successfully voted
        ELSE IF ~HasState(validator, slot, "Voted") THEN
            \* Store as pending to retry later
            [validator EXCEPT !.pendingBlocks[slot] = 
                validator.pendingBlocks[slot] \union {block}]
        ELSE validator

(***************************************************************************
 * Handle Timeout event (Algorithm 1, lines 6-8)
 * When: Slot timer expires
 * Action: Skip the slot if haven't voted
 ***************************************************************************)

HandleTimeout(validator, slot) ==
    IF ~HasState(validator, slot, "Voted") THEN
        TrySkipWindow(validator, slot)
    ELSE validator

(***************************************************************************
 * Handle BlockNotarized event (Algorithm 1, lines 9-11)
 * When: Pool gets notarization certificate
 * Action: Try to finalize the block
 ***************************************************************************)

HandleBlockNotarized(validator, slot, blockHash) ==
    LET newValidator == AddState(validator, slot, "BlockNotarized")
    IN TryFinal(newValidator, slot, blockHash)

(***************************************************************************
 * Handle ParentReady event (Algorithm 1, lines 12-15)
 * When: Ready to start new leader window
 * Action: Set timeouts for all slots in window
 ***************************************************************************)

HandleParentReady(validator, slot, parentHash) ==
    LET newValidator == AddState(validator, slot, "ParentReady")
        windowSlots == WindowSlots(slot)
        \* Set timeouts for all slots in window
        RECURSIVE SetTimeouts(_,_)
        SetTimeouts(val, slots) ==
            IF slots = {} THEN val
            ELSE
                LET s == CHOOSE x \in slots : TRUE
                    timeout == val.clock + DeltaTimeout + ((s - slot + 1) * DeltaBlock)
                IN SetTimeouts([val EXCEPT !.timeouts[s] = timeout], slots \ {s})
    IN SetTimeouts(newValidator, windowSlots \cap Slots)

(***************************************************************************
 * Handle SafeToNotar event (Algorithm 1, lines 16-20)
 * When: Safe to cast notar-fallback vote
 * Action: Skip window and cast notar-fallback
 ***************************************************************************)

HandleSafeToNotar(validator, slot, blockHash) ==
    LET skipResult == TrySkipWindow(validator, slot)
    IN
        IF ~HasState(skipResult, slot, "ItsOver") THEN
            LET vote == CreateNotarFallbackVote(skipResult.id, slot, blockHash)
                newValidator == AddState(skipResult, slot, "BadWindow")
                poolWithVote == StoreVote(newValidator.pool, vote)
            IN [newValidator EXCEPT !.pool = poolWithVote]
        ELSE skipResult

(***************************************************************************
 * Handle SafeToSkip event (Algorithm 1, lines 21-25)
 * When: Safe to cast skip-fallback vote
 * Action: Skip window and cast skip-fallback
 ***************************************************************************)

HandleSafeToSkip(validator, slot) ==
    LET skipResult == TrySkipWindow(validator, slot)
    IN
        IF ~HasState(skipResult, slot, "ItsOver") THEN
            LET vote == CreateSkipFallbackVote(skipResult.id, slot)
                newValidator == AddState(skipResult, slot, "BadWindow")
                poolWithVote == StoreVote(newValidator.pool, vote)
            IN [newValidator EXCEPT !.pool = poolWithVote]
        ELSE skipResult

\* ============================================================================
\* CHECK PENDING BLOCKS (Algorithm 1, lines 28-30)
\* ============================================================================

CheckPendingBlocks(validator) ==
    LET RECURSIVE CheckSlots(_,_)
        CheckSlots(val, slots) ==
            IF slots = {} THEN val
            ELSE
                LET s == CHOOSE x \in slots : TRUE
                    blocks == val.pendingBlocks[s]
                IN IF blocks = {} THEN CheckSlots(val, slots \ {s})
                   ELSE 
                       LET block == CHOOSE b \in blocks : TRUE
                           newVal == TryNotar(val, block)
                       IN CheckSlots(newVal, slots \ {s})
    IN CheckSlots(validator, {s \in Slots : validator.pendingBlocks[s] # {}})

\* ============================================================================
\* CLOCK AND TIMEOUT MANAGEMENT
\* ============================================================================

\* Advance clock and process expired timeouts
AdvanceClock(validator, newTime) ==
    LET expiredTimeouts == {s \in Slots : 
                            validator.timeouts[s] > 0 /\ 
                            validator.timeouts[s] <= newTime}
        RECURSIVE ProcessTimeouts(_,_)
        ProcessTimeouts(val, slots) ==
            IF slots = {} THEN val
            ELSE
                LET s == CHOOSE x \in slots : TRUE
                    newVal == HandleTimeout(val, s)
                IN ProcessTimeouts(newVal, slots \ {s})
    IN [ProcessTimeouts(validator, expiredTimeouts) EXCEPT !.clock = newTime]

\* ============================================================================
\* TYPE INVARIANT
\* ============================================================================

ValidatorStateOK(validator) ==
    /\ validator.id \in Validators
    /\ validator.state \in [Slots -> SUBSET StateObject]
    /\ validator.pendingBlocks \in [Slots -> SUBSET Block]
    /\ PoolTypeOK(validator.pool)
    /\ validator.clock \in Nat
    /\ validator.timeouts \in [Slots -> Nat]

=============================================================================