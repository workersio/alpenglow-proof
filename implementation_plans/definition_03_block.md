# Definition 3: Block Implementation Plan

## Definition
A block b is the sequence of all slices of a slot, for the purpose of voting and reaching consensus. A block is of the form:

$$b = \{(s,t,z_t,r_t,M_t,\sigma_t)\}_{t\in\{1,...,k\}}$$

where z_k=1, z_t=0 for t<k. The data of the block is the concatenation of all the slice data, i.e., M=(M_1,M_2,...,M_k). We define slot(b)=s. The block data M contains information about the slot slot(parent(b)) and hash hash(parent(b)) of the parent block of b. There are various limits on a block.

## TLA+ Implementation Plan

### Constants
```tla
CONSTANTS
    Slots,           \* Set of possible slot numbers
    MaxSlicesPerBlock, \* Maximum number of slices in a block (k)
    BlockHashes,     \* Set of possible block hashes
    SliceData,       \* Set of possible slice data
    MaxBlockSize,    \* Maximum block size in bytes
    MaxExecutionTime \* Maximum execution time for block
```

### Type Definition
```tla
Block == [
    slot: Slots,
    slices: Seq(Slice),      \* Ordered sequence of slices
    parentSlot: Slots,       \* slot(parent(b))
    parentHash: BlockHashes, \* hash(parent(b))
    size: Nat,               \* Block size in bytes
    executionTime: Nat       \* Estimated execution time
]
```

### Block Construction Functions
```tla
\* Create block from ordered sequence of slices
CreateBlock(slices, slot, parentSlot, parentHash) ==
    [slot |-> slot,
     slices |-> slices,
     parentSlot |-> parentSlot,
     parentHash |-> parentHash,
     size |-> CalculateBlockSize(slices),
     executionTime |-> CalculateExecutionTime(slices)]

\* Get slot number of block
SlotOf(block) == block.slot

\* Get concatenated data of all slices
BlockData(block) ==
    \* Concatenation M = (M_1, M_2, ..., M_k)
    [i \in 1..Len(block.slices) |-> block.slices[i].data]

\* Check if block satisfies size and time limits
WithinLimits(block) ==
    /\ block.size <= MaxBlockSize
    /\ block.executionTime <= MaxExecutionTime
```

### Validation Functions
```tla
\* Check if block has valid structure
IsValidBlock(block) ==
    /\ block.slot \in Slots
    /\ Len(block.slices) > 0
    /\ Len(block.slices) <= MaxSlicesPerBlock
    /\ block.parentSlot \in Slots
    /\ block.parentHash \in BlockHashes
    /\ ValidateSliceSequence(block.slices, block.slot)
    /\ WithinLimits(block)

\* Validate that slices form a proper sequence for the block
ValidateSliceSequence(slices, slot) ==
    /\ Len(slices) > 0
    /\ \A i \in 1..Len(slices) :
        /\ slices[i].slot = slot
        /\ slices[i].sliceIndex = i
        /\ slices[i].isLastSlice = (i = Len(slices))
    /\ slices[Len(slices)].isLastSlice = TRUE  \* z_k = 1
    /\ \A i \in 1..Len(slices)-1 : 
        slices[i].isLastSlice = FALSE           \* z_t = 0 for t < k

\* Check if block contains parent information in its data
ContainsParentInfo(block) ==
    \* Abstract check - would verify that block data M contains
    \* slot(parent(b)) and hash(parent(b)) information
    /\ block.parentSlot \in Slots
    /\ block.parentHash \in BlockHashes
    /\ ParentInfoInBlockData(BlockData(block), block.parentSlot, block.parentHash)

\* Abstract function to verify parent info is encoded in block data
ParentInfoInBlockData(blockData, parentSlot, parentHash) ==
    TRUE  \* Placeholder for actual data parsing
```

### Block Relationships
```tla
\* Check if block b' is a parent of block b
IsParent(parent, child) ==
    /\ child.parentSlot = parent.slot
    /\ child.parentHash = Hash(parent)  \* Assuming Hash function defined

\* Check if block is genesis (no parent)
IsGenesis(block) ==
    /\ block.parentSlot = 0  \* Convention for genesis
    /\ block.parentHash = "GENESIS_HASH"

\* Get all slices in block ordered by slice index
GetOrderedSlices(block) ==
    block.slices
```

### Size and Resource Calculations
```tla
\* Calculate total block size (abstract)
CalculateBlockSize(slices) ==
    \* Would sum up actual byte sizes of all slice data
    Len(slices) * 1000  \* Placeholder calculation

\* Calculate execution time (abstract)
CalculateExecutionTime(slices) ==
    \* Would analyze slice data for execution complexity
    Len(slices) * 100   \* Placeholder calculation
```

## Dependencies
- **Definition 2 (slice)**: Blocks are composed of slices
- **Definition 4 (block hash)**: For parent hash relationships
- **Definition 5 (ancestor/descendant)**: For parent-child relationships
- **Merkle tree construction**: For slice validation within blocks
- **Resource limits**: Size and execution time constraints

## Implementation Notes
1. The slice sequence must maintain proper ordering (t ∈ {1,...,k})
2. Only the last slice has z_t = 1, all others have z_t = 0
3. Parent information must be encoded within the block data M
4. Block limits (size, execution time) need concrete definitions
5. The relationship between blocks and their parents is fundamental for chain validation

## Testing Properties
```tla
\* Property: Valid blocks have properly ordered slices
ProperSliceOrdering ==
    \A block \in Block :
        IsValidBlock(block) =>
            \A i \in 1..Len(block.slices) :
                block.slices[i].sliceIndex = i

\* Property: Last slice flag is set correctly
LastSliceFlagProperty ==
    \A block \in Block :
        IsValidBlock(block) =>
            /\ block.slices[Len(block.slices)].isLastSlice = TRUE
            /\ \A i \in 1..Len(block.slices)-1 :
                block.slices[i].isLastSlice = FALSE

\* Property: All slices in block have same slot number
SliceSameslot ==
    \A block \in Block :
        IsValidBlock(block) =>
            \A i \in 1..Len(block.slices) :
                block.slices[i].slot = block.slot

\* Property: Block data contains parent information
ParentInfoProperty ==
    \A block \in Block :
        IsValidBlock(block) /\ ~IsGenesis(block) =>
            ContainsParentInfo(block)

\* Property: Blocks respect resource limits
ResourceLimitsProperty ==
    \A block \in Block :
        IsValidBlock(block) => WithinLimits(block)
```