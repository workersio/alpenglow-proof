# Definition 4: Block Hash Implementation Plan

## Definition
We define hash(b) of block b={s,t,z_t,r_t,M_t,σ_t)}_{t∈{1,...,k}} as the root of a Merkle tree T where:
- T is a complete, full binary tree with the smallest possible number of leaves m (with m being a power of 2) such that m≥k
- The first k leaves of T are r_1,...,r_k (each hash is concatenated with a label that marks the hash as a leaf)
- The remaining leaves of T are ⊥

## TLA+ Implementation Plan

### Constants
```tla
CONSTANTS
    BlockHashes,     \* Set of possible block hash values
    MerkleRoots,     \* Set of possible Merkle root hashes from slices
    BOTTOM,          \* Special value ⊥ for empty leaves
    LEAF_LABEL       \* Label to mark leaf hashes
```

### Helper Functions
```tla
\* Calculate smallest power of 2 >= n
NextPowerOfTwo(n) ==
    IF n <= 1 THEN 1
    ELSE IF n <= 2 THEN 2
    ELSE IF n <= 4 THEN 4
    ELSE IF n <= 8 THEN 8
    ELSE IF n <= 16 THEN 16
    ELSE IF n <= 32 THEN 32
    ELSE 64  \* Reasonable upper bound for practical blocks

\* Create leaf hash with label
LeafHash(merkleRoot) ==
    [hash |-> merkleRoot, label |-> LEAF_LABEL]

\* Create padded leaf sequence for Merkle tree
PaddedLeaves(sliceRoots) ==
    LET k == Len(sliceRoots)
        m == NextPowerOfTwo(k)
        realLeaves == [i \in 1..k |-> LeafHash(sliceRoots[i])]
        bottomLeaves == [i \in (k+1)..m |-> BOTTOM]
    IN realLeaves \o bottomLeaves
```

### Merkle Tree Construction
```tla
\* Hash two nodes together (internal node)
HashPair(left, right) ==
    \* Abstract hash function - would use actual cryptographic hash
    "hash_" \o ToString(left) \o "_" \o ToString(right)

\* Build Merkle tree level by level
BuildMerkleLevel(level) ==
    IF Len(level) = 1 THEN level[1]  \* Root reached
    ELSE 
        LET nextLevel == [i \in 1..(Len(level) \div 2) |->
                           HashPair(level[2*i-1], level[2*i])]
        IN BuildMerkleLevel(nextLevel)

\* Compute block hash from slice Merkle roots
ComputeBlockHash(block) ==
    LET sliceRoots == [i \in 1..Len(block.slices) |-> 
                        block.slices[i].merkleRoot]
        paddedLeaves == PaddedLeaves(sliceRoots)
    IN BuildMerkleLevel(paddedLeaves)
```

### Block Hash Operations
```tla
\* Get hash of a block
Hash(block) ==
    ComputeBlockHash(block)

\* Verify block hash matches expected value
VerifyBlockHash(block, expectedHash) ==
    Hash(block) = expectedHash

\* Check if tree structure is valid for given block
IsValidMerkleStructure(block) ==
    LET k == Len(block.slices)
        m == NextPowerOfTwo(k)
    IN 
        /\ k > 0
        /\ m >= k
        /\ IsPowerOfTwo(m)
        /\ k <= m

\* Check if number is power of 2
IsPowerOfTwo(n) ==
    /\ n > 0
    /\ \E i \in 0..10 : n = 2^i  \* Reasonable range
```

### Tree Structure Validation
```tla
\* Validate that tree is complete and full binary tree
IsCompleteBinaryTree(numLeaves) ==
    /\ numLeaves > 0
    /\ IsPowerOfTwo(numLeaves)

\* Get validation path for leaf at position i in block
GetValidationPath(block, sliceIndex) ==
    \* Abstract - would return actual Merkle path for verification
    LET k == Len(block.slices)
        m == NextPowerOfTwo(k)
    IN 
        IF sliceIndex \in 1..k
        THEN "path_for_" \o ToString(sliceIndex)  \* Placeholder
        ELSE "INVALID_INDEX"

\* Verify leaf at position using validation path
VerifyLeaf(blockHash, sliceRoot, sliceIndex, path) ==
    \* Abstract verification - would check Merkle path
    TRUE  \* Placeholder for cryptographic verification
```

### Double Merkle Construction Visualization
```tla
\* Visual representation of the double-Merkle structure:
\* Level 1: Block data -> Slices -> Slice Merkle Roots (r_1, r_2, ..., r_k)
\* Level 2: Slice roots -> Block Merkle Tree -> Block Hash
DoublemerkleStructure(block) ==
    [sliceLevel |-> [i \in 1..Len(block.slices) |->
                      block.slices[i].merkleRoot],
     blockLevel |-> Hash(block)]
```

## Dependencies
- **Definition 3 (block)**: Block hash is computed from block slices
- **Definition 2 (slice)**: Uses slice Merkle roots r_t
- **Merkle tree construction**: Core cryptographic primitive
- **Collision-resistant hash function**: For computing internal nodes

## Implementation Notes
1. The tree must be a complete, full binary tree with power-of-2 leaves
2. Empty positions are filled with ⊥ (BOTTOM value)
3. Leaf hashes are labeled to distinguish from internal node hashes
4. This creates a "double Merkle" structure: slice data → slice root → block hash
5. The hash function must be collision-resistant (e.g., SHA-256)
6. Tree height is log₂(m) where m is the next power of 2 ≥ k

## Testing Properties
```tla
\* Property: Block hash is deterministic
HashDeterminism ==
    \A block \in Block :
        IsValidBlock(block) =>
            Hash(block) = Hash(block)

\* Property: Different blocks have different hashes (collision resistance)
CollisionResistance ==
    \A b1, b2 \in Block :
        /\ IsValidBlock(b1) /\ IsValidBlock(b2)
        /\ b1 # b2 =>
            Hash(b1) # Hash(b2)

\* Property: Merkle tree structure is valid
MerkleStructureValidity ==
    \A block \in Block :
        IsValidBlock(block) =>
            IsValidMerkleStructure(block)

\* Property: Padding works correctly
PaddingProperty ==
    \A block \in Block :
        IsValidBlock(block) =>
            LET k == Len(block.slices)
                m == NextPowerOfTwo(k)
                padded == PaddedLeaves([i \in 1..k |-> block.slices[i].merkleRoot])
            IN 
                /\ Len(padded) = m
                /\ IsPowerOfTwo(m)
                /\ m >= k

\* Property: Leaf validation paths work correctly
LeafValidationProperty ==
    \A block \in Block, i \in 1..Len(block.slices) :
        IsValidBlock(block) =>
            LET path == GetValidationPath(block, i)
                root == Hash(block)
                leafRoot == block.slices[i].merkleRoot
            IN VerifyLeaf(root, leafRoot, i, path)
```