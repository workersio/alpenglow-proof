# Definition 5: Ancestor and Descendant Implementation Plan

## Definition
An ancestor of a block b is any block that can be reached from b by the parent links, i.e., b, b's parent, b's parent's parent, and so on. If b' is an ancestor of b, b is a descendant of b'. Note that b is its own ancestor and descendant.

## TLA+ Implementation Plan

### Constants
```tla
CONSTANTS
    Blocks,          \* Set of all possible blocks
    MaxChainDepth    \* Maximum depth to prevent infinite recursion
```

### Recursive Ancestor Relations
```tla
\* Base case: every block is its own ancestor
IsSelfAncestor(b) == TRUE

\* Direct parent relationship
IsDirectParent(parent, child) ==
    /\ parent.slot = child.parentSlot
    /\ Hash(parent) = child.parentHash

\* Recursive ancestor relationship
RECURSIVE IsAncestor(_,_,_)
IsAncestor(ancestor, descendant, depth) ==
    IF depth > MaxChainDepth THEN FALSE
    ELSE IF ancestor = descendant THEN TRUE
    ELSE IF IsGenesis(descendant) THEN FALSE
    ELSE 
        \E parent \in Blocks :
            /\ IsDirectParent(parent, descendant)
            /\ IsAncestor(ancestor, parent, depth + 1)

\* Public ancestor check (starting with depth 0)
Ancestor(ancestor, descendant) ==
    IsAncestor(ancestor, descendant, 0)

\* Descendant relationship (inverse of ancestor)
Descendant(descendant, ancestor) ==
    Ancestor(ancestor, descendant)
```

### Chain Navigation Functions
```tla
\* Get immediate parent of a block
GetParent(block) ==
    IF IsGenesis(block) THEN "NO_PARENT"
    ELSE CHOOSE parent \in Blocks : IsDirectParent(parent, block)

\* Get all ancestors of a block (up to max depth)
RECURSIVE GetAllAncestors(_,_,_)
GetAllAncestors(block, depth, acc) ==
    IF depth > MaxChainDepth THEN acc
    ELSE IF IsGenesis(block) THEN acc \union {block}
    ELSE 
        LET parent == GetParent(block) IN
        IF parent = "NO_PARENT" THEN acc \union {block}
        ELSE GetAllAncestors(parent, depth + 1, acc \union {block})

\* Public function to get all ancestors
AllAncestors(block) ==
    GetAllAncestors(block, 0, {})

\* Get all descendants of a block
AllDescendants(ancestor) ==
    {desc \in Blocks : Ancestor(ancestor, desc)}

\* Get direct children of a block
DirectChildren(parent) ==
    {child \in Blocks : IsDirectParent(parent, child)}
```

### Chain Properties
```tla
\* Check if blocks form a valid chain
IsValidChain(blockSequence) ==
    /\ Len(blockSequence) > 0
    /\ \A i \in 1..Len(blockSequence)-1 :
        IsDirectParent(blockSequence[i], blockSequence[i+1])

\* Get chain from ancestor to descendant
RECURSIVE GetChainTo(_,_,_,_)
GetChainTo(from, to, currentPath, depth) ==
    IF depth > MaxChainDepth THEN "TOO_DEEP"
    ELSE IF from = to THEN Append(currentPath, to)
    ELSE IF IsGenesis(to) THEN "NOT_CONNECTED"
    ELSE
        LET parent == GetParent(to) IN
        IF parent = "NO_PARENT" THEN "NOT_CONNECTED"
        ELSE GetChainTo(from, parent, Append(currentPath, to), depth + 1)

\* Public function to get chain between blocks
ChainBetween(ancestor, descendant) ==
    IF ~Ancestor(ancestor, descendant) THEN "NOT_ANCESTOR_DESCENDANT"
    ELSE 
        LET chain == GetChainTo(ancestor, descendant, <<>>, 0) IN
        IF chain = "TOO_DEEP" \/ chain = "NOT_CONNECTED" 
        THEN chain
        ELSE Reverse(chain)  \* Return in ancestor->descendant order
```

### Distance and Depth Calculations
```tla
\* Calculate distance between ancestor and descendant
RECURSIVE ChainDistance(_,_,_)
ChainDistance(ancestor, descendant, depth) ==
    IF depth > MaxChainDepth THEN -1  \* Error: too deep
    ELSE IF ancestor = descendant THEN depth
    ELSE IF IsGenesis(descendant) THEN -1  \* Not connected
    ELSE
        LET parent == GetParent(descendant) IN
        IF parent = "NO_PARENT" THEN -1
        ELSE ChainDistance(ancestor, parent, depth + 1)

\* Get depth of block from genesis
BlockDepth(block) ==
    ChainDistance("GENESIS", block, 0)

\* Check if block is at specific depth from ancestor
IsAtDepth(ancestor, descendant, expectedDepth) ==
    ChainDistance(ancestor, descendant, 0) = expectedDepth
```

### Common Ancestor Functions
```tla
\* Find common ancestors of two blocks
CommonAncestors(block1, block2) ==
    AllAncestors(block1) \cap AllAncestors(block2)

\* Find the lowest common ancestor (most recent)
LowestCommonAncestor(block1, block2) ==
    LET commonAncs == CommonAncestors(block1, block2) IN
    IF commonAncs = {} THEN "NO_COMMON_ANCESTOR"
    ELSE 
        \* Find the ancestor with maximum depth (closest to blocks)
        CHOOSE anc \in commonAncs :
            \A other \in commonAncs : BlockDepth(anc) >= BlockDepth(other)
```

## Dependencies
- **Definition 3 (block)**: Uses block structure and parent information
- **Definition 4 (block hash)**: For parent hash verification
- **Genesis block concept**: Special case handling
- **Hash function**: For verifying parent relationships

## Implementation Notes
1. Self-ancestry is reflexive: every block is its own ancestor and descendant
2. The relationship is transitive: if A is ancestor of B and B is ancestor of C, then A is ancestor of C
3. Genesis block has no parent, terminating the ancestor chain
4. Maximum depth prevents infinite recursion in case of cycles (though blockchain should be acyclic)
5. Parent verification requires both slot number and hash to match
6. Efficient implementation might cache ancestor relationships to avoid repeated computation

## Testing Properties
```tla
\* Property: Self-ancestry (reflexivity)
SelfAncestryProperty ==
    \A block \in Blocks :
        IsValidBlock(block) => Ancestor(block, block)

\* Property: Transitivity of ancestor relationship
TransitivityProperty ==
    \A a, b, c \in Blocks :
        /\ Ancestor(a, b) /\ Ancestor(b, c) =>
            Ancestor(a, c)

\* Property: Asymmetry (except for self-ancestry)
AsymmetryProperty ==
    \A a, b \in Blocks :
        /\ a # b 
        /\ Ancestor(a, b) =>
            ~Ancestor(b, a)

\* Property: Genesis termination
GenesisTerminationProperty ==
    \A block \in Blocks :
        IsValidBlock(block) =>
            \E genesis \in Blocks :
                /\ IsGenesis(genesis)
                /\ Ancestor(genesis, block)

\* Property: Parent-child consistency
ParentChildConsistency ==
    \A parent, child \in Blocks :
        IsDirectParent(parent, child) =>
            /\ Ancestor(parent, child)
            /\ Descendant(child, parent)

\* Property: Chain distance consistency
ChainDistanceConsistency ==
    \A ancestor, descendant \in Blocks :
        Ancestor(ancestor, descendant) =>
            ChainDistance(ancestor, descendant, 0) >= 0

\* Property: Common ancestor existence
CommonAncestorProperty ==
    \A b1, b2 \in Blocks :
        /\ IsValidBlock(b1) /\ IsValidBlock(b2) =>
            \E genesis \in Blocks :
                /\ IsGenesis(genesis)
                /\ genesis \in CommonAncestors(b1, b2)
```