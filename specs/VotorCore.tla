---------------------------- MODULE VotorCore ----------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC, 
        Messages, Blocks, 
        Certificates, VoteStorage

(*
  Context: Votor local logic per §2.4–2.6. Algorithms 1–2 drive events and helpers.
  Citations in-line per operator to Definitions/Algorithms/Lemmas.
*)

CONSTANTS
    DeltaTimeout,
    DeltaBlock
(*
  ∆timeout and ∆block correspond to Definition 17 timeout schedule. See §2.6 p.23–24.
*)

ASSUME
    /\ DeltaTimeout \in Nat \ {0}
    /\ DeltaBlock \in Nat \ {0}

TimeTS == Nat
TimeoutTS == Nat
(*
  Local clock and timeout timestamp domains. See §1.5 “Time” and Definition 17.
*)

StateObject == {
    "ParentReady",      \* Pool emitted ParentReady event
    "Voted",            \* Cast notarization or skip vote
    "VotedNotarTag",    \* Local tag added when casting notar vote
    "BlockNotarized",   \* Pool has notarization certificate
    "ItsOver",          \* Cast finalization vote, done with slot
    "BadWindow",        \* Cast skip or fallback vote
    "BlockSeen"         \* First Block(...) event consumed for this slot
}
(*
  Slot flags mirror Definition 18: ParentReady, Voted, VotedNotar(hash), BlockNotarized(hash), ItsOver, BadWindow. 
  Note: "BlockSeen" is an extra implementation tag not in Def. 18; it is benign if not used in proofs. p.23–24.
*)

ValidatorState == [
    id: Validators,                                     \* Validator identifier
    state: [Slots -> SUBSET StateObject],               \* State flags per slot
    parentReady: [Slots -> BlockHashes \cup {NoBlock}], \* Parent hash per slot (Def. 18: models ParentReady(h) binding)
    pendingBlocks: [Slots -> SUBSET Block],             \* Blocks to retry
    pool: PoolState,                                   \* Vote/certificate storage
    clock: TimeTS,                                     \* Local clock
    timeouts: [Slots -> TimeoutTS]                     \* Scheduled timeouts
]
(*
  Local per-validator store. Pool semantics per Definitions 12–13; per-slot state per Definition 18. §2.5–2.6.
*)

InitValidatorState(validatorId) == [
    id |-> validatorId,
    state |-> [s \in Slots |-> {}],
    parentReady |-> [s \in Slots |-> NoBlock],
    pendingBlocks |-> [s \in Slots |-> {}],
    pool |-> InitPool,
    clock |-> 0,
    timeouts |-> [s \in Slots |-> 0]
]
(*
  Initial conditions: empty state, no parent, no pending, empty Pool, zero clock/timeouts. Matches Defs. 12–13, 18.
*)

HasState(validator, slot, stateObj) ==
    stateObj \in validator.state[slot]
(*
  Helper to test Def. 18 slot-state membership. Used by Alg. 1–2 guards.
*)

AddState(validator, slot, stateObj) ==
    [validator EXCEPT !.state[slot] = validator.state[slot] \cup {stateObj}]
(*
  Idempotent add of a Def. 18 flag to a slot. Mirrors Alg. 1/2 writes.
*)

VotedForBlock(validator, slot, blockHash) ==
    \E vote \in GetVotesForSlot(validator.pool, slot) :
        /\ vote.validator = validator.id
        /\ IsInitialNotarVote(vote)
        /\ vote.blockHash = blockHash
(*
  Checks our initial notarization vote for hash in slot via Pool. 
  Alg. 2 line 19 uses VotedNotar(hash) ∈ state[s]; here we equivalently query Pool for our signed NotarVote. Tables 5–6, p.20; Alg. 2 p.25.
*)

BlockNotarizedHashes(validator, slot) ==
    IF HasState(validator, slot, "BlockNotarized")
    THEN { h \in BlockHashes : HasNotarizationCert(validator.pool, slot, h) }
    ELSE {}
(*
  Reads notarization certificate(s) for slot from Pool; Def. 13 and Pool event BlockNotarized in Def. 15. p.20–21.
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
(*
  Alg. 2 lines 18–21: finalize if notarized for same hash AND we notar-voted AND not BadWindow. 
  Def. 14 defines finalization modes; Lemma 22 forbids ItsOver ∧ BadWindow. p.21,25,29.
*)

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
(*
  Alg. 2 lines 7–17: cast notarization when either first slot with ParentReady(parent) or later slot with prior VotedNotar(parent) in slot−1. 
  We mark Voted and VotedNotar*, clear pending for slot, then possibly finalize. p.25; Def. 15 ParentReady.
*)

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
                            vote == CreateSkipVote(state.id, s)
                            newVal1 == AddState(state, s, "Voted")
                            newVal2 == AddState(newVal1, s, "BadWindow")
                            poolWithVote == StoreVote(newVal2.pool, vote)
                            updatedVal == [newVal2 EXCEPT 
                                          !.pool = poolWithVote,
                                          !.pendingBlocks[s] = {}]
                        IN SkipSlots[updatedVal, remainingSlots \ {s}]
            IN SkipSlots[validator, slotsToSkip]
        ELSE validator
(*
  Alg. 2 lines 22–27: for all slots in leader window, if not Voted then cast Skip, mark BadWindow, clear pending. p.25.
*)

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
(*
  Alg. 2 lines 28–30: retry pending blocks, earliest slot first. Paper’s model has single ⊥/block; here we keep a set with an invariant (≤1). p.25.
*)

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
(*
  Alg. 1 lines 1–5: on Block event tryNotar; if not and not Voted then buffer; else no-op. §2.6 p.24.
*)

HandleTimeout(validator, slot) ==
    LET cleared == [validator EXCEPT !.timeouts[slot] = 0]
    IN IF HasState(cleared, slot, "ItsOver") THEN
           cleared
       ELSE IF ~HasState(cleared, slot, "Voted") THEN
           TrySkipWindow(cleared, slot)
       ELSE cleared
(*
  Alg. 1 lines 6–8: on Timeout(s) if not Voted then skip window; if ItsOver then ignore. Def. 17 schedules the timeouts. p.23–24.
*)

HandleBlockNotarized(validator, slot, blockHash) ==
    LET newValidator == AddState(validator, slot, "BlockNotarized")
    IN TryFinal(newValidator, slot, blockHash)
(*
  Alg. 1 lines 9–11: mark notarized then try finalization. Def. 14–15. p.21,24.
*)

HandleParentReady(validator, slot, parentHash) ==
    IF ~IsFirstSlotOfWindow(slot)
    THEN validator
    ELSE
        LET newValidator == AddState(validator, slot, "ParentReady")
            withParent == [newValidator EXCEPT !.parentReady[slot] = parentHash]
            afterCheck == CheckPendingBlocks(withParent)
            first == FirstSlotOfWindow(slot)
            windowSlots == WindowSlots(first)
            SetTimeouts[val \in ValidatorState, remainingSlots \in SUBSET windowSlots] ==
                IF remainingSlots = {} THEN val
                ELSE
                    LET s == CHOOSE x \in remainingSlots : TRUE
                        timeout == val.clock + DeltaTimeout + ((s - first + 1) * DeltaBlock)
                    IN SetTimeouts[[val EXCEPT !.timeouts[s] = timeout], remainingSlots \ {s}]
            \* Note: WindowSlots already ranges over production slots; no extra \cap Slots needed
        IN SetTimeouts[afterCheck, windowSlots]
(*
  Alg. 1 lines 12–15: on ParentReady(s,·) set flag, recheck pending, then schedule Timeout(i) for window starting at first slot. 
  Schedule matches Definition 17: clock()+∆timeout+(i−s+1)·∆block; ParentReady is only emitted for the first slot, Def. 15. p.21,23–24.
*)

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
(*
  Alg. 1 lines 16–20: after trySkipWindow(s), if not ItsOver then cast Notar-Fallback and mark BadWindow. 
  Conditions for SafeToNotar per Definition 16. p.21–22,24.
*)

HandleSafeToSkip(validator, slot) ==
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
(*
  Alg. 1 lines 21–25: after trySkipWindow(s), if not ItsOver then cast Skip-Fallback, mark BadWindow, clear pending.
  Note: Definition 16 permits sending SkipFallback even if a prior NotarFallback was sent; we deliberately do not guard on BadWindow.
  SafeToSkip condition per Definition 16. p.21–22,24.
*)

AdvanceClock(validator, newTime) ==
    IF newTime < validator.clock THEN validator
    ELSE
        LET 
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
(*
  Processes all expired Timeout(i) in nondecreasing slot order, then advances local clock. 
  Timeout semantics from Definition 17; Alg. 1 line 6. p.23–24.
*)

ValidatorStateOK(validator) ==
    /\ validator.id \in Validators
    /\ validator.state \in [Slots -> SUBSET StateObject]
    /\ validator.parentReady \in [Slots -> BlockHashes \cup {NoBlock}]
    /\ validator.pendingBlocks \in [Slots -> SUBSET Block]
    /\ PoolTypeOK(validator.pool)
    /\ validator.clock \in TimeTS
    /\ validator.timeouts \in [Slots -> TimeoutTS]
(*
  Type invariants for local state and Pool. PoolTypeOK covers Definitions 12–13 constraints. p.20–21.
*)

ParentReadyConsistency(validator) ==
    \A s \in Slots : HasState(validator, s, "ParentReady") <=> validator.parentReady[s] # NoBlock
(*
  Consistency between Def. 18 flag and stored parent hash. Def. 15/18. p.21,23–24.
*)

PendingBlocksSingleton(validator) ==
    \A s \in Slots : Cardinality(validator.pendingBlocks[s]) <= 1
(*
  Paper models a single optional pending block per slot (⊥ or b). We enforce ≤1 here to match Def. 18 and Alg. 1 line 5. p.24.
*)

PendingBlocksSlotAligned(validator) ==
    \A s \in Slots : \A b \in validator.pendingBlocks[s] : b.slot = s
(*
  Any buffered block must be for its indexed slot. Alg. 1 lines 1–5. p.24.
*)

Lemma22_ItsOverImpliesNotBadWindow(validator) ==
    \A s \in Slots : HasState(validator, s, "ItsOver") => ~HasState(validator, s, "BadWindow")
(*
  From Lemma 22: after finalization vote, no fallback votes in that slot. p.29.
*)

Lemma22_BadWindowImpliesNotItsOver(validator) ==
    \A s \in Slots : HasState(validator, s, "BadWindow") => ~HasState(validator, s, "ItsOver")
(*
  From Lemma 22: if any fallback vote cast, we cannot later finalize in that slot. p.29.
*)

=============================================================================
