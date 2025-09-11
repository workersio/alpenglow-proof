# Definition 16: Fallback Events Implementation Plan

## Definition
Consider block b in slot s = slot(b). By notar(b) denote the cumulative stake of nodes whose notarization votes for block b are in Pool, and by skip(s) denote the cumulative stake of nodes whose skip votes for slot s are in Pool. The following events are emitted as input for Algorithm 1:

- **SafeToNotar(s, hash(b))**: The event is only issued if the node voted in slot s already, but not to notarize b. Moreover:
  $$\textit{notar}(b) \geq 40\% \text{ or } \Big( \textit{skip}(s) + \textit{notar}(b) \geq 60\% \text{ and } \textit{notar}(b) \geq 20\%\Big).$$

- **SafeToSkip(s)**: The event is only issued if the node voted in slot s already, but not to skip s. Moreover:
  $$\textit{skip}(s) + \sum_{b} \textit{notar}(b) - \max_b \textit{notar}(b) \geq 40\%.$$

## TLA+ Implementation Plan

### Constants
```tla
CONSTANTS
    Validators,     \* Set of validator nodes  
    Slots,          \* Set of slot numbers
    BlockHashes,    \* Set of block hashes
    StakeThreshold40,  \* 40% stake threshold
    StakeThreshold60,  \* 60% stake threshold  
    StakeThreshold20   \* 20% stake threshold
```

### Variables
```tla
VARIABLES
    poolVotes,         \* Pool vote storage (from Definition 12)
    emittedEvents,     \* Set of events already emitted
    validatorState     \* Per-validator state (from Definition 18)
```

### Stake Calculation Functions
```tla
\* Calculate cumulative stake of notarization votes for block b
NotarStake(slot, blockHash) ==
    LET notarVotes == GetNotarVotesForBlock(slot, blockHash)
    IN SumStake({vote.validator : vote \in notarVotes})

\* Calculate cumulative stake of skip votes for slot s  
SkipStake(slot) ==
    LET skipVotes == GetSkipVotesForSlot(slot)
    IN SumStake({vote.validator : vote \in skipVotes})

\* Calculate total stake for all notarization votes in slot (any block)
TotalNotarStakeInSlot(slot) ==
    LET allNotarVotes == UNION {GetNotarVotesForBlock(slot, b) : b \in BlockHashes}
    IN SumStake({vote.validator : vote \in allNotarVotes})

\* Find maximum notarization stake among all blocks in slot
MaxNotarStakeInSlot(slot) ==
    IF \E b \in BlockHashes : GetNotarVotesForBlock(slot, b) # {}
    THEN Max({NotarStake(slot, b) : b \in BlockHashes, GetNotarVotesForBlock(slot, b) # {}})
    ELSE 0

\* Helper function to sum stake of validators
SumStake(validators) ==
    \* Abstract - would sum actual validator stakes
    Cardinality(validators) * 1  \* Placeholder assuming equal stakes

\* Helper to find maximum value in set
Max(values) ==
    CHOOSE v \in values : \A other \in values : v >= other
```

### SafeToNotar Event Conditions
```tla
\* Check if SafeToNotar conditions are met
SafeToNotarConditions(validator, slot, blockHash) ==
    LET notarStake == NotarStake(slot, blockHash)
        skipStake == SkipStake(slot)
    IN
        \* Condition 1: notar(b) >= 40%
        \/ notarStake >= StakeThreshold40
        \* Condition 2: skip(s) + notar(b) >= 60% AND notar(b) >= 20%
        \/ (/\ skipStake + notarStake >= StakeThreshold60
            /\ notarStake >= StakeThreshold20)

\* Check if validator is eligible for SafeToNotar event
CanEmitSafeToNotar(validator, slot, blockHash) ==
    /\ HasVoted(validator, slot)  \* Already voted in slot
    /\ ~HasVotedNotar(validator, slot, blockHash)  \* But not for this block
    /\ SafeToNotarConditions(validator, slot, blockHash)
    /\ [type |-> "SafeToNotar", slot |-> slot, blockHash |-> blockHash] \notin emittedEvents
```

### SafeToSkip Event Conditions  
```tla
\* Check if SafeToSkip conditions are met
SafeToSkipConditions(slot) ==
    LET skipStake == SkipStake(slot)
        totalNotarStake == TotalNotarStakeInSlot(slot)
        maxNotarStake == MaxNotarStakeInSlot(slot)
    IN skipStake + totalNotarStake - maxNotarStake >= StakeThreshold40

\* Check if validator is eligible for SafeToSkip event
CanEmitSafeToSkip(validator, slot) ==
    /\ HasVoted(validator, slot)  \* Already voted in slot
    /\ GetNotarOrSkipVote(validator, slot).type # "SkipVote"  \* But not to skip
    /\ SafeToSkipConditions(slot)
    /\ [type |-> "SafeToSkip", slot |-> slot] \notin emittedEvents
```

### Event Emission Functions
```tla
\* Emit SafeToNotar event
EmitSafeToNotar(validator, slot, blockHash) ==
    /\ CanEmitSafeToNotar(validator, slot, blockHash)
    /\ LET event == [type |-> "SafeToNotar", 
                     validator |-> validator,
                     slot |-> slot, 
                     blockHash |-> blockHash]
       IN emittedEvents' = emittedEvents \union {event}

\* Emit SafeToSkip event  
EmitSafeToSkip(validator, slot) ==
    /\ CanEmitSafeToSkip(validator, slot)
    /\ LET event == [type |-> "SafeToSkip",
                     validator |-> validator, 
                     slot |-> slot]
       IN emittedEvents' = emittedEvents \union {event}

\* General event emission handler
EmitFallbackEvents(validator, slot) ==
    \/ \E blockHash \in BlockHashes : EmitSafeToNotar(validator, slot, blockHash)
    \/ EmitSafeToSkip(validator, slot)
    \/ UNCHANGED emittedEvents
```

### Event Processing for Algorithm 1
```tla
\* Check if SafeToNotar event should trigger for any validator
ShouldEmitSafeToNotar(slot, blockHash) ==
    \E validator \in Validators : CanEmitSafeToNotar(validator, slot, blockHash)

\* Check if SafeToSkip event should trigger for any validator
ShouldEmitSafeToSkip(slot) ==
    \E validator \in Validators : CanEmitSafeToSkip(validator, slot)

\* Process all pending fallback events
ProcessFallbackEvents ==
    \E validator \in Validators, slot \in Slots :
        EmitFallbackEvents(validator, slot)
```

### Additional Requirements (Leader Window & Repair)
```tla
\* Check if slot is first in leader window
IsFirstSlotInWindow(slot) ==
    \* Abstract - depends on leader window structure
    TRUE  \* Placeholder

\* Handle repair procedure for SafeToNotar (if not first slot)
HandleSafeToNotarRepair(validator, slot, blockHash) ==
    IF IsFirstSlotInWindow(slot) 
    THEN EmitSafeToNotar(validator, slot, blockHash)
    ELSE 
        \* Need to retrieve block and verify parent has notar-fallback cert
        /\ RepairBlock(blockHash)  \* Abstract repair operation
        /\ ParentHasNotarFallbackCert(validator, slot, blockHash)
        /\ EmitSafeToNotar(validator, slot, blockHash)

\* Abstract functions for repair and parent verification
RepairBlock(blockHash) == TRUE  \* Placeholder
ParentHasNotarFallbackCert(validator, slot, blockHash) == TRUE  \* Placeholder
```

### Event History and Tracking
```tla
\* Initialize event tracking
InitFallbackEvents ==
    emittedEvents = {}

\* Get all SafeToNotar events for a slot
GetSafeToNotarEvents(slot) ==
    {event \in emittedEvents : 
     event.type = "SafeToNotar" /\ event.slot = slot}

\* Get all SafeToSkip events for a slot  
GetSafeToSkipEvents(slot) ==
    {event \in emittedEvents :
     event.type = "SafeToSkip" /\ event.slot = slot}

\* Check if specific event was emitted
WasEventEmitted(eventType, slot, blockHash) ==
    CASE eventType = "SafeToNotar" ->
         \E event \in emittedEvents :
           /\ event.type = "SafeToNotar"
           /\ event.slot = slot 
           /\ event.blockHash = blockHash
    [] eventType = "SafeToSkip" ->
         \E event \in emittedEvents :
           /\ event.type = "SafeToSkip"
           /\ event.slot = slot
    [] OTHER -> FALSE
```

## Dependencies
- **Definition 11 (messages)**: For vote types and structure
- **Definition 12 (storing votes)**: For pool vote storage
- **Definition 18 (Votor state)**: For validator voting state
- **Stake calculation system**: For computing cumulative stakes
- **Repair procedure**: For block retrieval in non-first slots
- **Algorithm 1**: These events are inputs to Votor algorithm

## Implementation Notes
1. Events are only emitted once per condition satisfaction
2. SafeToNotar requires validator hasn't voted for that specific block
3. SafeToSkip requires validator hasn't voted to skip the slot
4. Stake calculations use cumulative validator stakes, not just counts
5. The "max_b notar(b)" term prevents double-counting the largest block
6. Repair procedure is needed for SafeToNotar in non-first window slots
7. Events trigger fallback voting mechanisms in the Votor algorithm

## Testing Properties
```tla
\* Property: Events only emitted when conditions met
EventConditionsRespected ==
    \A event \in emittedEvents :
        CASE event.type = "SafeToNotar" ->
             SafeToNotarConditions(event.validator, event.slot, event.blockHash)
        [] event.type = "SafeToSkip" ->
             SafeToSkipConditions(event.slot)

\* Property: No duplicate events
NoDuplicateEvents ==
    \A event1, event2 \in emittedEvents :
        /\ event1.type = event2.type
        /\ event1.slot = event2.slot
        /\ (event1.type = "SafeToNotar" => event1.blockHash = event2.blockHash) =>
            event1 = event2

\* Property: SafeToNotar only for non-voted blocks
SafeToNotarNonVoted ==
    \A event \in emittedEvents :
        event.type = "SafeToNotar" =>
            ~HasVotedNotar(event.validator, event.slot, event.blockHash)

\* Property: SafeToSkip only for non-skip voters
SafeToSkipNonSkip ==
    \A event \in emittedEvents :
        event.type = "SafeToSkip" =>
            GetNotarOrSkipVote(event.validator, event.slot).type # "SkipVote"

\* Property: Stake thresholds are meaningful
StakeThresholdConsistency ==
    /\ StakeThreshold20 < StakeThreshold40
    /\ StakeThreshold40 < StakeThreshold60
    /\ StakeThreshold60 < 100  \* Assuming percentage scale
```