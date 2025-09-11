# Definition 12: Storing Votes Implementation Plan

## Definition
Pool stores received votes for every slot and every node as follows:
- The first received notarization or skip vote,
- up to 3 received notar-fallback votes,
- the first received skip-fallback vote, and
- the first received finalization vote.

## TLA+ Implementation Plan

### Constants
```tla
CONSTANTS
    Validators,          \* Set of validator nodes
    Slots,               \* Set of possible slot numbers
    MaxNotarFallbackVotes \* Maximum notar-fallback votes (3)
```

### Pool Vote Storage Structure
```tla
VARIABLES
    poolVotes  \* Function: [Validators × Slots] -> VoteStorage

\* Vote storage record for each validator per slot
VoteStorage == [
    notarOrSkip: VoteMessage \union {"NONE"},     \* First notar or skip vote
    notarFallbacks: Seq(VoteMessage),             \* Up to 3 notar-fallback votes
    skipFallback: VoteMessage \union {"NONE"},    \* First skip-fallback vote
    finalization: VoteMessage \union {"NONE"}     \* First finalization vote
]

\* Initialize empty vote storage
InitVoteStorage ==
    [notarOrSkip |-> "NONE",
     notarFallbacks |-> <<>>,
     skipFallback |-> "NONE",
     finalization |-> "NONE"]
```

### Pool Initialization
```tla
\* Initialize pool with empty storage for all validators and slots
InitPool ==
    poolVotes = [v \in Validators, s \in Slots |-> InitVoteStorage]

\* Get vote storage for specific validator and slot
GetVoteStorage(validator, slot) ==
    poolVotes[validator, slot]
```

### Vote Storage Operations
```tla
\* Store first notarization or skip vote
StoreNotarOrSkipVote(validator, slot, vote) ==
    LET storage == GetVoteStorage(validator, slot)
    IN /\ vote.type \in {"NotarVote", "SkipVote"}
       /\ storage.notarOrSkip = "NONE"
       /\ poolVotes' = [poolVotes EXCEPT 
            ![validator, slot].notarOrSkip = vote]

\* Store notar-fallback vote (up to 3)
StoreNotarFallbackVote(validator, slot, vote) ==
    LET storage == GetVoteStorage(validator, slot)
    IN /\ vote.type = "NotarFallbackVote"
       /\ Len(storage.notarFallbacks) < MaxNotarFallbackVotes
       /\ poolVotes' = [poolVotes EXCEPT 
            ![validator, slot].notarFallbacks = Append(@, vote)]

\* Store first skip-fallback vote
StoreSkipFallbackVote(validator, slot, vote) ==
    LET storage == GetVoteStorage(validator, slot)
    IN /\ vote.type = "SkipFallbackVote"
       /\ storage.skipFallback = "NONE"
       /\ poolVotes' = [poolVotes EXCEPT 
            ![validator, slot].skipFallback = vote]

\* Store first finalization vote
StoreFinalizationVote(validator, slot, vote) ==
    LET storage == GetVoteStorage(validator, slot)
    IN /\ vote.type = "FinalVote"
       /\ storage.finalization = "NONE"
       /\ poolVotes' = [poolVotes EXCEPT 
            ![validator, slot].finalization = vote]
```

### Vote Addition Interface
```tla
\* Main function to add vote to pool (enforcing storage rules)
AddVoteToPool(vote) ==
    LET validator == vote.validator
        slot == vote.slot
        storage == GetVoteStorage(validator, slot)
    IN
        \/ (vote.type \in {"NotarVote", "SkipVote"} /\ 
            storage.notarOrSkip = "NONE" /\
            StoreNotarOrSkipVote(validator, slot, vote))
        \/ (vote.type = "NotarFallbackVote" /\ 
            Len(storage.notarFallbacks) < MaxNotarFallbackVotes /\
            StoreNotarFallbackVote(validator, slot, vote))
        \/ (vote.type = "SkipFallbackVote" /\ 
            storage.skipFallback = "NONE" /\
            StoreSkipFallbackVote(validator, slot, vote))
        \/ (vote.type = "FinalVote" /\ 
            storage.finalization = "NONE" /\
            StoreFinalizationVote(validator, slot, vote))
        \/ UNCHANGED poolVotes  \* Vote rejected (duplicate or invalid)

\* Check if vote can be stored
CanStoreVote(vote) ==
    LET validator == vote.validator
        slot == vote.slot
        storage == GetVoteStorage(validator, slot)
    IN
        \/ (vote.type \in {"NotarVote", "SkipVote"} /\ storage.notarOrSkip = "NONE")
        \/ (vote.type = "NotarFallbackVote" /\ 
            Len(storage.notarFallbacks) < MaxNotarFallbackVotes)
        \/ (vote.type = "SkipFallbackVote" /\ storage.skipFallback = "NONE")
        \/ (vote.type = "FinalVote" /\ storage.finalization = "NONE")
```

### Vote Retrieval Functions
```tla
\* Get stored notarization or skip vote
GetNotarOrSkipVote(validator, slot) ==
    GetVoteStorage(validator, slot).notarOrSkip

\* Get all stored notar-fallback votes
GetNotarFallbackVotes(validator, slot) ==
    GetVoteStorage(validator, slot).notarFallbacks

\* Get stored skip-fallback vote
GetSkipFallbackVote(validator, slot) ==
    GetVoteStorage(validator, slot).skipFallback

\* Get stored finalization vote
GetFinalizationVote(validator, slot) ==
    GetVoteStorage(validator, slot).finalization

\* Check if validator has specific vote type stored
HasVoteType(validator, slot, voteType) ==
    CASE voteType \in {"NotarVote", "SkipVote"} ->
         GetNotarOrSkipVote(validator, slot) # "NONE"
    [] voteType = "NotarFallbackVote" ->
         Len(GetNotarFallbackVotes(validator, slot)) > 0
    [] voteType = "SkipFallbackVote" ->
         GetSkipFallbackVote(validator, slot) # "NONE"
    [] voteType = "FinalVote" ->
         GetFinalizationVote(validator, slot) # "NONE"
    [] OTHER -> FALSE
```

### Vote Collection for Certificate Generation
```tla
\* Get all notarization votes for a specific block
GetNotarVotesForBlock(slot, blockHash) ==
    {storage.notarOrSkip : 
     v \in Validators, 
     storage \in {GetVoteStorage(v, slot)},
     storage.notarOrSkip # "NONE",
     storage.notarOrSkip.type = "NotarVote",
     storage.notarOrSkip.blockHash = blockHash}

\* Get all skip votes for a slot
GetSkipVotesForSlot(slot) ==
    {storage.notarOrSkip : 
     v \in Validators,
     storage \in {GetVoteStorage(v, slot)},
     storage.notarOrSkip # "NONE",
     storage.notarOrSkip.type = "SkipVote"}

\* Get all notar-fallback votes for a specific block
GetNotarFallbackVotesForBlock(slot, blockHash) ==
    UNION {SeqToSet(storage.notarFallbacks) : 
           v \in Validators,
           storage \in {GetVoteStorage(v, slot)},
           \A vote \in SeqToSet(storage.notarFallbacks) :
             vote.blockHash = blockHash}

\* Get all finalization votes for a slot
GetFinalizationVotesForSlot(slot) ==
    {storage.finalization :
     v \in Validators,
     storage \in {GetVoteStorage(v, slot)},
     storage.finalization # "NONE"}

\* Helper to convert sequence to set
RECURSIVE SeqToSet(_)
SeqToSet(seq) ==
    IF seq = <<>> THEN {}
    ELSE {Head(seq)} \union SeqToSet(Tail(seq))
```

### Storage Validation
```tla
\* Check if storage respects the rules
IsValidStorage(storage) ==
    /\ (storage.notarOrSkip = "NONE" \/ 
        storage.notarOrSkip.type \in {"NotarVote", "SkipVote"})
    /\ Len(storage.notarFallbacks) <= MaxNotarFallbackVotes
    /\ \A vote \in SeqToSet(storage.notarFallbacks) :
        vote.type = "NotarFallbackVote"
    /\ (storage.skipFallback = "NONE" \/
        storage.skipFallback.type = "SkipFallbackVote")
    /\ (storage.finalization = "NONE" \/
        storage.finalization.type = "FinalVote")

\* Check if entire pool is valid
IsValidPool ==
    \A v \in Validators, s \in Slots :
        IsValidStorage(GetVoteStorage(v, s))
```

## Dependencies
- **Definition 11 (messages)**: For vote message types and structure
- **Vote validation**: For ensuring vote authenticity
- **Stake calculation**: For certificate generation

## Implementation Notes
1. Storage is per-validator per-slot to prevent interference
2. Only the first notarization OR skip vote is stored (mutually exclusive)
3. Multiple notar-fallback votes allowed (up to 3) for resilience
4. Skip-fallback and finalization votes are unique per validator per slot
5. Storage rules prevent vote duplication and enforce limits
6. Vote retrieval functions support certificate generation

## Testing Properties
```tla
\* Property: Storage limits are enforced
StorageLimitsEnforced ==
    \A v \in Validators, s \in Slots :
        LET storage == GetVoteStorage(v, s)
        IN /\ Len(storage.notarFallbacks) <= MaxNotarFallbackVotes
           /\ (storage.notarOrSkip # "NONE" => 
               storage.notarOrSkip.type \in {"NotarVote", "SkipVote"})

\* Property: No duplicate primary votes
NoDuplicatePrimaryVotes ==
    \A v \in Validators, s \in Slots :
        LET storage == GetVoteStorage(v, s)
        IN storage.notarOrSkip # "NONE" =>
            \A vote \in SeqToSet(storage.notarFallbacks) :
                vote # storage.notarOrSkip

\* Property: Vote types are consistent
VoteTypeConsistency ==
    \A v \in Validators, s \in Slots :
        IsValidStorage(GetVoteStorage(v, s))

\* Property: First vote principle
FirstVotePrinciple ==
    \A v \in Validators, s \in Slots, vote \in VoteMessage :
        /\ vote.validator = v /\ vote.slot = s
        /\ CanStoreVote(vote) =>
            (AddVoteToPool(vote) => ~CanStoreVote(vote))
```