# Definition 14: Finalization Implementation Plan

## Definition
We have two ways to finalize a block:
- If a finalization certificate on slot s is in Pool, the unique notarized block in slot s is finalized (we call this slow-finalized).
- If a fast-finalization certificate on block b is in Pool, the block b is finalized (fast-finalized).

Whenever a block is finalized (slow or fast), all ancestors of the block are finalized first.

## TLA+ Implementation Plan

### Constants
```tla
CONSTANTS
    Blocks,          \* Set of all possible blocks
    Slots,           \* Set of possible slot numbers
    BlockHashes      \* Set of possible block hashes
```

### Variables
```tla
VARIABLES
    finalizedBlocks,    \* Set of finalized block hashes
    poolCertificates,   \* Pool containing certificates
    finalizationOrder   \* Sequence tracking finalization order
```

### Finalization Status Functions
```tla
\* Check if block is finalized
IsFinalized(blockHash) ==
    blockHash \in finalizedBlocks

\* Check if block can be fast-finalized
CanFastFinalize(blockHash) ==
    \E cert \in poolCertificates :
        /\ cert.type = "FastFinalizationCert"
        /\ cert.blockHash = blockHash
        /\ ~IsFinalized(blockHash)

\* Check if block can be slow-finalized
CanSlowFinalize(slot) ==
    /\ \E cert \in poolCertificates : cert.type = "FinalizationCert" /\ cert.slot = slot
    /\ Cardinality(GetNotarizedBlocksInSlot(slot)) = 1
    /\ LET uniqueBlock == GetUniqueNotarizedBlock(slot)
       IN uniqueBlock # "NONE" /\ ~IsFinalized(uniqueBlock)

\* Get all notarized blocks in a specific slot
GetNotarizedBlocksInSlot(slot) ==
    {cert.blockHash : cert \in poolCertificates, 
     cert.type = "NotarizationCert" /\ cert.slot = slot}

\* Get the unique notarized block in slot (if exactly one exists)
GetUniqueNotarizedBlock(slot) ==
    LET notarizedBlocks == GetNotarizedBlocksInSlot(slot)
    IN IF Cardinality(notarizedBlocks) = 1
       THEN CHOOSE b \in notarizedBlocks : TRUE
       ELSE "NONE"
```

### Ancestor Finalization
```tla
\* Get all ancestors that need to be finalized before this block
GetUnfinalizedAncestors(blockHash) ==
    LET block == GetBlockByHash(blockHash)
        allAncestors == AllAncestors(block)
    IN {Hash(ancestor) : ancestor \in allAncestors, ~IsFinalized(Hash(ancestor))}

\* Finalize all ancestors of a block in dependency order
FinalizeAncestorsFirst(blockHash) ==
    LET unfinalizedAncestors == GetUnfinalizedAncestors(blockHash)
        orderedAncestors == TopologicalSort(unfinalizedAncestors)
    IN FinalizeBlockSet(orderedAncestors)

\* Finalize a set of blocks in order
RECURSIVE FinalizeBlockSet(_)
FinalizeBlockSet(blockHashes) ==
    IF blockHashes = <<>> THEN 
        UNCHANGED <<finalizedBlocks, finalizationOrder>>
    ELSE 
        /\ FinalizeBlock(Head(blockHashes))
        /\ FinalizeBlockSet(Tail(blockHashes))

\* Topologically sort blocks by ancestor relationships
TopologicalSort(blockHashes) ==
    \* Abstract sorting - would implement proper topological ordering
    \* For now, assume blocks are provided in correct order
    blockHashes  \* Placeholder implementation
```

### Core Finalization Operations
```tla
\* Finalize a single block (without ancestor checking)
FinalizeBlock(blockHash) ==
    /\ ~IsFinalized(blockHash)
    /\ finalizedBlocks' = finalizedBlocks \union {blockHash}
    /\ finalizationOrder' = Append(finalizationOrder, blockHash)

\* Fast finalization process
FastFinalizeBlock(blockHash) ==
    /\ CanFastFinalize(blockHash)
    /\ FinalizeAncestorsFirst(blockHash)
    /\ FinalizeBlock(blockHash)

\* Slow finalization process
SlowFinalizeSlot(slot) ==
    /\ CanSlowFinalize(slot)
    /\ LET blockHash == GetUniqueNotarizedBlock(slot)
       IN /\ blockHash # "NONE"
          /\ FinalizeAncestorsFirst(blockHash)
          /\ FinalizeBlock(blockHash)
```

### Finalization Event Handlers
```tla
\* Handle fast-finalization certificate appearance
HandleFastFinalizationCert(cert) ==
    /\ cert.type = "FastFinalizationCert"
    /\ FastFinalizeBlock(cert.blockHash)

\* Handle finalization certificate appearance
HandleFinalizationCert(cert) ==
    /\ cert.type = "FinalizationCert"
    /\ SlowFinalizeSlot(cert.slot)

\* General certificate handler
HandleCertificate(cert) ==
    \/ HandleFastFinalizationCert(cert)
    \/ HandleFinalizationCert(cert)
    \/ UNCHANGED <<finalizedBlocks, finalizationOrder>>  \* Other cert types
```

### Finalization Type Classification
```tla
\* Check how a block was finalized
GetFinalizationType(blockHash) ==
    IF ~IsFinalized(blockHash) THEN "NOT_FINALIZED"
    ELSE IF \E cert \in poolCertificates :
              /\ cert.type = "FastFinalizationCert"
              /\ cert.blockHash = blockHash
         THEN "FAST_FINALIZED"
    ELSE "SLOW_FINALIZED"

\* Check if finalization was direct or through ancestor chain
WasDirectlyFinalized(blockHash) ==
    \/ CanFastFinalize(blockHash)
    \/ \E slot \in Slots : 
        /\ CanSlowFinalize(slot)
        /\ GetUniqueNotarizedBlock(slot) = blockHash
```

### Safety and Consistency Checks
```tla
\* Verify finalization consistency
IsFinalizationConsistent ==
    \A blockHash \in finalizedBlocks :
        \* All ancestors must be finalized
        \A ancestor \in GetUnfinalizedAncestors(blockHash) :
            ancestor \in finalizedBlocks

\* Check if block should be finalized based on certificates
ShouldBeFinalized(blockHash) ==
    \/ CanFastFinalize(blockHash)
    \/ \E slot \in Slots :
        /\ CanSlowFinalize(slot)
        /\ GetUniqueNotarizedBlock(slot) = blockHash

\* Verify all finalized blocks have proper justification
AllFinalizedJustified ==
    \A blockHash \in finalizedBlocks :
        ShouldBeFinalized(blockHash) \/ 
        \E ancestor \in GetUnfinalizedAncestors(blockHash) :
            ShouldBeFinalized(ancestor)
```

### Utility Functions
```tla
\* Get block object by hash (abstract)
GetBlockByHash(blockHash) ==
    CHOOSE block \in Blocks : Hash(block) = blockHash

\* Initialize finalization state
InitFinalization ==
    /\ finalizedBlocks = {}
    /\ finalizationOrder = <<>>

\* Check if all blocks in a set are finalized
AllFinalized(blockHashSet) ==
    \A blockHash \in blockHashSet : IsFinalized(blockHash)

\* Get finalization depth (how many blocks finalized after this one)
FinalizationDepth(blockHash) ==
    IF ~IsFinalized(blockHash) THEN -1
    ELSE 
        LET pos == PositionInSeq(finalizationOrder, blockHash)
        IN IF pos = -1 THEN -1 ELSE Len(finalizationOrder) - pos

\* Helper to find position in sequence
RECURSIVE PositionInSeq(_, _, _)
PositionInSeq(seq, element, index) ==
    IF index > Len(seq) THEN -1
    ELSE IF seq[index] = element THEN index
    ELSE PositionInSeq(seq, element, index + 1)
```

## Dependencies
- **Definition 5 (ancestor/descendant)**: For ancestor finalization
- **Definition 11 (messages)**: For certificate types and structure
- **Definition 13 (certificates)**: For certificate validation
- **Pool data structure**: For accessing certificates
- **Block hash function**: For identifying blocks

## Implementation Notes
1. Finalization is irreversible - once finalized, always finalized
2. Ancestor finalization must happen atomically with block finalization
3. Fast finalization (80% stake) is preferred over slow finalization (60% stake)
4. Slow finalization requires exactly one notarized block in the slot
5. Topological ordering ensures ancestors are finalized before descendants
6. Finalization order tracking helps with rollback scenarios and debugging

## Testing Properties
```tla
\* Property: Finalization is permanent
FinalizationPermanence ==
    \A blockHash \in BlockHashes :
        IsFinalized(blockHash) => \□ IsFinalized(blockHash)

\* Property: Ancestors finalized before descendants
AncestorFinalizationOrder ==
    \A blockHash \in finalizedBlocks :
        \A ancestor \in GetUnfinalizedAncestors(blockHash) :
            ancestor \in finalizedBlocks

\* Property: Fast finalization implies certificates
FastFinalizationRequiresCert ==
    \A blockHash \in finalizedBlocks :
        GetFinalizationType(blockHash) = "FAST_FINALIZED" =>
            \E cert \in poolCertificates :
                /\ cert.type = "FastFinalizationCert"
                /\ cert.blockHash = blockHash

\* Property: Slow finalization implies unique notarized block
SlowFinalizationRequiresUnique ==
    \A blockHash \in finalizedBlocks :
        GetFinalizationType(blockHash) = "SLOW_FINALIZED" =>
            \E slot \in Slots :
                /\ GetUniqueNotarizedBlock(slot) = blockHash
                /\ \E cert \in poolCertificates :
                    cert.type = "FinalizationCert" /\ cert.slot = slot

\* Property: No conflicts between fast and slow finalization
NoFinalizationConflict ==
    \A blockHash \in finalizedBlocks :
        ~(CanFastFinalize(blockHash) /\ 
          \E slot \in Slots : 
            /\ CanSlowFinalize(slot)
            /\ GetUniqueNotarizedBlock(slot) # blockHash)
```