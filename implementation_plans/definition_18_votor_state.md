# Definition 18: Votor State Implementation Plan

## Definition
Votor (Algorithms 1 and 2) accesses state associated with each slot. The state of every slot is initialized to the empty set: state ← [∅, ∅, ...]. The following objects can be permanently added to the state of any slot s:

- **ParentReady(hash(b))**: Pool emitted the event ParentReady(s, hash(b))
- **Voted**: The node has cast either a notarization vote or a skip vote in slot s
- **VotedNotar(hash(b))**: The node has cast a notarization vote on block b in slot s

## TLA+ Implementation Plan

### Constants
```tla
CONSTANTS
    Slots,           \* Set of possible slot numbers
    BlockHashes,     \* Set of possible block hashes
    Validators       \* Set of validator nodes
```

### State Object Types
```tla
\* State objects that can be added to slot state
StateObject ==
    \* ParentReady object with block hash
    \/ [type: {"ParentReady"}, blockHash: BlockHashes]
    \* Voted flag (no additional data)
    \/ [type: {"Voted"}]
    \* VotedNotar object with block hash
    \/ [type: {"VotedNotar"}, blockHash: BlockHashes]

\* Constructor functions for state objects
ParentReadyObject(blockHash) ==
    [type |-> "ParentReady", blockHash |-> blockHash]

VotedObject == 
    [type |-> "Voted"]

VotedNotarObject(blockHash) ==
    [type |-> "VotedNotar", blockHash |-> blockHash]
```

### Votor State Structure
```tla
VARIABLES
    votorState  \* Function from [Validators × Slots] to SUBSET StateObject

\* Initialize all slot states to empty sets
InitVotorState ==
    votorState = [v \in Validators, s \in Slots |-> {}]

\* Get state for specific validator and slot
GetSlotState(validator, slot) ==
    votorState[validator, slot]

\* Add object to slot state (permanent addition)
AddToSlotState(validator, slot, stateObject) ==
    votorState' = [votorState EXCEPT ![validator, slot] = @ \union {stateObject}]

\* Check if specific object is in slot state
HasStateObject(validator, slot, stateObject) ==
    stateObject \in GetSlotState(validator, slot)
```

### State Query Functions
```tla
\* Check if ParentReady for specific block hash is in state
HasParentReady(validator, slot, blockHash) ==
    ParentReadyObject(blockHash) \in GetSlotState(validator, slot)

\* Check if Voted flag is in state
HasVoted(validator, slot) ==
    VotedObject \in GetSlotState(validator, slot)

\* Check if VotedNotar for specific block is in state
HasVotedNotar(validator, slot, blockHash) ==
    VotedNotarObject(blockHash) \in GetSlotState(validator, slot)

\* Get all blocks for which ParentReady is set
GetParentReadyBlocks(validator, slot) ==
    {obj.blockHash : obj \in GetSlotState(validator, slot), obj.type = "ParentReady"}

\* Get all blocks for which VotedNotar is set
GetVotedNotarBlocks(validator, slot) ==
    {obj.blockHash : obj \in GetSlotState(validator, slot), obj.type = "VotedNotar"}
```

### State Modification Operations
```tla
\* Add ParentReady to slot state
AddParentReady(validator, slot, blockHash) ==
    AddToSlotState(validator, slot, ParentReadyObject(blockHash))

\* Add Voted flag to slot state
AddVoted(validator, slot) ==
    AddToSlotState(validator, slot, VotedObject)

\* Add VotedNotar to slot state
AddVotedNotar(validator, slot, blockHash) ==
    AddToSlotState(validator, slot, VotedNotarObject(blockHash))

\* Combined operation: vote notarization (sets both Voted and VotedNotar)
VoteNotarization(validator, slot, blockHash) ==
    /\ AddVoted(validator, slot)
    /\ AddVotedNotar(validator, slot, blockHash)

\* Combined operation: vote skip (sets only Voted)
VoteSkip(validator, slot) ==
    AddVoted(validator, slot)
```

### State Consistency Checks
```tla
\* Check if VotedNotar implies Voted
VotedNotarImpliesVoted(validator, slot) ==
    (\E blockHash \in BlockHashes : HasVotedNotar(validator, slot, blockHash)) =>
        HasVoted(validator, slot)

\* Check if state is consistent (all invariants hold)
IsConsistentState(validator, slot) ==
    VotedNotarImpliesVoted(validator, slot)

\* Check if validator can still vote in slot (hasn't voted yet)
CanVoteInSlot(validator, slot) ==
    ~HasVoted(validator, slot)

\* Check if validator has voted for any block in slot
HasVotedForAnyBlock(validator, slot) ==
    GetVotedNotarBlocks(validator, slot) # {}
```

### State Evolution Functions
```tla
\* Handle ParentReady event from Pool
HandleParentReadyEvent(validator, slot, blockHash) ==
    /\ ~HasParentReady(validator, slot, blockHash)
    /\ AddParentReady(validator, slot, blockHash)

\* Handle notarization vote casting
HandleNotarizationVote(validator, slot, blockHash) ==
    /\ CanVoteInSlot(validator, slot)
    /\ VoteNotarization(validator, slot, blockHash)

\* Handle skip vote casting
HandleSkipVote(validator, slot) ==
    /\ CanVoteInSlot(validator, slot)
    /\ VoteSkip(validator, slot)
```

### State Queries for Algorithm Logic
```tla
\* Check conditions for TRYNOTAR function
CanTryNotar(validator, slot, blockHash, parentHash) ==
    /\ CanVoteInSlot(validator, slot)
    /\ \/ (IsFirstSlotInWindow(slot) /\ HasParentReady(validator, slot, parentHash))
       \/ (~IsFirstSlotInWindow(slot) /\ 
           HasVotedNotar(validator, slot-1, parentHash))

\* Check conditions for TRYFINAL function
CanTryFinal(validator, slot, blockHash) ==
    /\ HasBlockNotarized(validator, slot, blockHash)
    /\ HasVotedNotar(validator, slot, blockHash)
    /\ ~HasBadWindow(validator, slot)  \* Would need BadWindow state object

\* Abstract helper functions (would be implemented based on other definitions)
IsFirstSlotInWindow(slot) == 
    TRUE  \* Placeholder - depends on window structure

HasBlockNotarized(validator, slot, blockHash) ==
    TRUE  \* Placeholder - depends on Pool certificates

HasBadWindow(validator, slot) ==
    FALSE \* Placeholder - would need additional state object
```

### Global State Properties
```tla
\* All validator states are consistent
AllStatesConsistent ==
    \A v \in Validators, s \in Slots : IsConsistentState(v, s)

\* No validator votes twice in same slot
NoDoubleVoting ==
    \A v \in Validators, s \in Slots :
        \A b1, b2 \in BlockHashes :
            /\ HasVotedNotar(v, s, b1)
            /\ HasVotedNotar(v, s, b2) =>
                b1 = b2

\* Voted implies existence of specific vote type
VotedImpliesSpecificVote ==
    \A v \in Validators, s \in Slots :
        HasVoted(v, s) =>
            \/ \E b \in BlockHashes : HasVotedNotar(v, s, b)
            \/ TRUE  \* Skip vote (no specific state object)
```

## Dependencies
- **Definition 15 (Pool events)**: For ParentReady event handling
- **Algorithms 1 and 2**: The actual Votor algorithm implementations
- **Pool data structure**: For BlockNotarized events
- **Leader window concepts**: For first slot determination

## Implementation Notes
1. State is per-validator per-slot, allowing concurrent operation
2. Objects are permanently added - no removal once added
3. The Voted flag prevents double voting within a slot
4. VotedNotar tracks specific block votes for safety
5. ParentReady enables building on confirmed parents
6. State consistency must be maintained across all operations
7. The abstract helper functions need concrete implementations

## Testing Properties
```tla
\* Property: State objects are permanent
StatePermanence ==
    \A v \in Validators, s \in Slots, obj \in StateObject :
        HasStateObject(v, s, obj) =>
            \□ HasStateObject(v, s, obj)

\* Property: VotedNotar implies Voted
VotedNotarConsistency ==
    \A v \in Validators, s \in Slots, b \in BlockHashes :
        HasVotedNotar(v, s, b) => HasVoted(v, s)

\* Property: At most one notarization vote per slot
AtMostOneNotarVote ==
    \A v \in Validators, s \in Slots :
        Cardinality(GetVotedNotarBlocks(v, s)) <= 1

\* Property: Cannot vote after voting
VotingPreventsVoting ==
    \A v \in Validators, s \in Slots :
        HasVoted(v, s) => ~CanVoteInSlot(v, s)

\* Property: State initialization
StateInitialization ==
    InitVotorState => 
        \A v \in Validators, s \in Slots : 
            GetSlotState(v, s) = {}
```