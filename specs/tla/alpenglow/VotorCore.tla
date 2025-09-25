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
 * - BlockSeen: First Block(...) event consumed for this slot
 ***************************************************************************)

StateObject == {
    "ParentReady",      \* Pool emitted ParentReady event
    "Voted",            \* Cast notarization or skip vote
    "VotedNotar",       \* Cast notarization vote for specific block
    "BlockNotarized",   \* Pool has notarization certificate
    "ItsOver",          \* Cast finalization vote, done with slot
    "BadWindow",        \* Cast skip or fallback vote
    "BlockSeen"         \* First Block(...) event consumed for this slot
}

\* These flags are exactly the items listed in Definition 18 and let us track
\* where each slot sits in the voting process.

\* Validator state structure
ValidatorState == [
    id: Validators,                                  \* Validator identifier
    state: [Slots -> SUBSET StateObject],           \* State flags per slot
    parentReady: [Slots -> BlockHashes \cup {NoBlock}], \* Parent hash per slot
    pendingBlocks: [Slots -> SUBSET Block],         \* Blocks to retry
    pool: PoolState,                                \* Vote/certificate storage
    clock: Nat,                                     \* Local clock
    timeouts: [Slots -> Nat]                        \* Scheduled timeouts
]

\* Initialize validator state
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
 * Vote to finalize a notarized block. Mirrors Whitepaper Algorithm 2
 * (lines 18–21): requires notarization, our own notar vote, and no
 * fallback activity in the window (`BadWindow`).
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
 * Skip all unvoted slots in the window, per Whitepaper Algorithm 2
 * (lines 22–27). Triggered by timeouts or fallback events.
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
\* CHECK PENDING BLOCKS (Whitepaper Algorithm 1, lines 28–30)
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
\* EVENT HANDLERS (Algorithm 1)
\* ============================================================================

(***************************************************************************
 * Handle Block event (Whitepaper Algorithm 1, lines 1–5).
 * On delivery we attempt to notarize immediately; otherwise retain as
 * pending until prerequisites (parent readiness) hold.
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
                validator.pendingBlocks[slot] \union {block}]
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
 * finalization vote.
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
        windowSlots == WindowSlots(slot)
        \* Set timeouts for all slots in window
        RECURSIVE SetTimeouts(_,_)
        SetTimeouts(val, slots) ==
            IF slots = {} THEN val
            ELSE
                LET s == CHOOSE x \in slots : TRUE
                    timeout == val.clock + DeltaTimeout + ((s - slot + 1) * DeltaBlock)
                IN SetTimeouts([val EXCEPT !.timeouts[s] = timeout], slots \ {s})
    IN SetTimeouts(afterCheck, windowSlots \cap Slots)

(***************************************************************************
 * Handle SafeToNotar event (Whitepaper Algorithm 1, lines 16–20).
 * After verifying Definition 16 conditions, emits skip votes for any
 * missed slots and casts the notar-fallback vote.
 *
 * Note: We accept the block `b` (available at the call site) and use the
 * block-typed wrapper to preserve slot–hash pairing by construction.
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
    LET skipResult == TrySkipWindow(validator, slot)
    IN
        IF ~HasState(skipResult, slot, "ItsOver") THEN
            LET vote == CreateSkipFallbackVote(skipResult.id, slot)
                newValidator == AddState(skipResult, slot, "BadWindow")
                poolWithVote == StoreVote(newValidator.pool, vote)
            IN [newValidator EXCEPT !.pool = poolWithVote]
        ELSE skipResult

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
    /\ validator.parentReady \in [Slots -> BlockHashes \cup {NoBlock}]
    /\ validator.pendingBlocks \in [Slots -> SUBSET Block]
    /\ PoolTypeOK(validator.pool)
    /\ validator.clock \in Nat
    /\ validator.timeouts \in [Slots -> Nat]

\* Optional lemma (audit suggestion): votes produced for valid blocks are
\* valid by construction (content-only, signatures abstracted).
THEOREM TryNotarProducesValidNotarVote ==
    \A v \in Validators, b \in Block :
        IsValidBlock(b) => IsValidVote(CreateNotarVoteForBlock(v, b))

=============================================================================
