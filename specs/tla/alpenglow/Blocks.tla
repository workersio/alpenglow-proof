---------------------------- MODULE Blocks ----------------------------
(***************************************************************************
 * BLOCK STRUCTURE AND RELATIONSHIPS FOR ALPENGLOW
 * 
 * This module defines the block data structure and the blockchain DAG
 * (Directed Acyclic Graph) relationships.
 * 
 * MAPS TO WHITEPAPER:
 * - Definition 3: Block structure
 * - Definition 4: Block hash
 * - Definition 5: Ancestor and descendant relationships
 * 
 * KEY CONCEPTS:
 * - Blocks form a chain through parent-child links
 * - Each slot can have at most one finalized block
 * - Leader windows group consecutive slots under one leader
 ***************************************************************************)

EXTENDS Naturals, FiniteSets, Messages

\* ============================================================================
\* CONSTANTS
\* ============================================================================

CONSTANTS
    GenesisHash,    \* Special hash for the genesis (first) block
    WindowSize      \* Number of consecutive slots per leader window

ASSUME
    /\ GenesisHash \in BlockHashes
    /\ WindowSize \in Nat \ {0}  \* Window size must be positive

\* ============================================================================
\* BLOCK STRUCTURE (Definition 3 from whitepaper)
\* ============================================================================

(***************************************************************************
 * A block contains:
 * - slot: When this block was created
 * - hash: Unique identifier for this block
 * - parent: Hash of the previous block in the chain
 * - leader: Which validator created this block
 ***************************************************************************)

Block == [
    slot: Slots,
    hash: BlockHashes,
    parent: BlockHashes,
    leader: Validators
]

\* The very first block in the chain (has no real parent)
GenesisBlock == [
    slot |-> 0,
    hash |-> GenesisHash,
    parent |-> GenesisHash,  \* Genesis is its own parent
    leader |-> CHOOSE v \in Validators : TRUE  \* Arbitrary leader
]

\* ============================================================================
\* BLOCK VALIDATION
\* ============================================================================

\* Check if a block is properly formatted
IsValidBlock(b) ==
    /\ b.slot \in Slots
    /\ b.hash \in BlockHashes
    /\ b.parent \in BlockHashes
    /\ b.leader \in Validators
    /\ b.slot > 0 => b.parent # b.hash  \* Non-genesis blocks can't self-reference

\* Check if two blocks conflict (same slot, different hash)
\* IMPORTANT: This shouldn't happen if the protocol works correctly!
ConflictingBlocks(b1, b2) ==
    /\ b1.slot = b2.slot     \* Same slot
    /\ b1.hash # b2.hash     \* Different blocks!

\* Check if parent-child relationship is valid
ValidParentChild(parent, child) ==
    /\ parent.hash = child.parent   \* Child references parent correctly
    /\ parent.slot < child.slot     \* Parent comes before child

\* ============================================================================
\* ANCESTRY RELATIONSHIPS (Definition 5 from whitepaper)
\* ============================================================================

(***************************************************************************
 * Ancestry is crucial for consensus safety:
 * - If block A is an ancestor of block B, then B's chain includes A
 * - This ensures all validators build on the same history
 * 
 * SAFETY INVARIANT: If two blocks are finalized, one must be an ancestor
 * of the other (no forks allowed!)
 ***************************************************************************)

\* Is block b1 an ancestor of block b2?
\* This means: following parent links from b2 eventually reaches b1
IsAncestor(b1, b2, allBlocks) ==
    LET
        \* Recursively follow parent links
        RECURSIVE ReachableFrom(_)
        ReachableFrom(b) ==
            IF b = b1 THEN TRUE  \* Found the ancestor!
            ELSE IF b.parent = b.hash THEN FALSE  \* Hit genesis
            ELSE 
                \* Find the parent block and continue
                LET parentBlocks == {p \in allBlocks : p.hash = b.parent}
                IN IF parentBlocks = {} THEN FALSE
                   ELSE LET parent == CHOOSE p \in parentBlocks : TRUE
                        IN ReachableFrom(parent)
    IN b1 = b2 \/ ReachableFrom(b2)  \* A block is its own ancestor

\* Is block b1 a descendant of block b2?
IsDescendant(b1, b2, allBlocks) == 
    IsAncestor(b2, b1, allBlocks)

\* Get all ancestors of a block (its entire history)
GetAncestors(b, allBlocks) ==
    {ancestor \in allBlocks : IsAncestor(ancestor, b, allBlocks)}

\* Check if two blocks are in the same chain
InSameChain(b1, b2, allBlocks) ==
    \/ IsAncestor(b1, b2, allBlocks)
    \/ IsDescendant(b1, b2, allBlocks)

\* ============================================================================
\* LEADER WINDOWS (Section 2.7 from whitepaper)
\* ============================================================================

(***************************************************************************
 * Leaders are assigned consecutive slots called "windows"
 * 
 * Example with WindowSize = 4:
 * - Slots 0-3: Leader A
 * - Slots 4-7: Leader B
 * - Slots 8-11: Leader C
 * 
 * IMPORTANT: First slot of window has special rules (needs ParentReady)
 ***************************************************************************)

\* Deterministic leader assignment (abstraction of VRF in real protocol)
Leader(slot) ==
    CHOOSE v \in Validators : TRUE  \* Simplified - would use VRF

\* Get the first slot of the window containing 'slot'
FirstSlotOfWindow(slot) ==
    IF slot = 0 THEN 0
    ELSE ((slot - 1) \div WindowSize) * WindowSize + 1

\* Check if this slot is the first in its window
IsFirstSlotOfWindow(slot) ==
    slot = FirstSlotOfWindow(slot)

\* Get all slots in the same window as 'slot'
WindowSlots(slot) ==
    LET first == FirstSlotOfWindow(slot)
    IN {s \in Slots : 
        /\ s >= first 
        /\ s < first + WindowSize}

\* ============================================================================
\* CHAIN OPERATIONS
\* ============================================================================

\* Get the block at a specific slot in a chain
GetBlockAtSlot(slot, chain) ==
    LET blocksAtSlot == {b \in chain : b.slot = slot}
    IN IF blocksAtSlot = {} THEN GenesisBlock
       ELSE CHOOSE b \in blocksAtSlot : TRUE

\* Get the complete chain from genesis to a block
GetChain(b, allBlocks) ==
    LET ancestors == GetAncestors(b, allBlocks)
    IN {a \in ancestors : 
        \* Include only blocks that are ancestors of all later blocks
        \A a2 \in ancestors : a2.slot <= a.slot => IsAncestor(a2, a, allBlocks)}

\* Check if a new block properly extends an existing chain
ExtendsChain(newBlock, existingChain) ==
    \E parent \in existingChain :
        /\ ValidParentChild(parent, newBlock)
        /\ \A other \in existingChain : other.slot < newBlock.slot

\* ============================================================================
\* INVARIANTS FOR VERIFICATION
\* ============================================================================

\* All blocks in the system must be valid
AllBlocksValid(blocks) ==
    \A b \in blocks : IsValidBlock(b)

\* No two different blocks can be finalized in the same slot
\* This is a key safety property!
UniqueBlocksPerSlot(finalizedBlocks) ==
    \A b1, b2 \in finalizedBlocks :
        b1.slot = b2.slot => b1.hash = b2.hash

\* All finalized blocks must form a single chain (no forks)
\* This is THE main safety property (Theorem 1 from whitepaper)
SingleChain(finalizedBlocks) ==
    \A b1, b2 \in finalizedBlocks :
        InSameChain(b1, b2, finalizedBlocks)

=============================================================================
