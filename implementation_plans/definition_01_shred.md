# Definition 1: Shred Implementation Plan

## Definition
A shred fits neatly in a UDP datagram. It has the form:
```
(s, t, i, z_t, r_t, (d_i, π_i), σ_t)
```

Where:
- s, t, i ∈ ℕ are slot number, slice index, shred index, respectively
- z_t ∈ {0, 1} is a flag (see Definition 2)
- d_i is the data at position i with path π_i for Merkle root r_t
- σ_t is the signature of the object Slice(s, t, z_t, r_t) from the node leader(s)

## TLA+ Implementation Plan

### Constants
```tla
CONSTANTS
    Slots,          \* Set of possible slot numbers
    SliceIndices,   \* Set of possible slice indices
    ShredIndices,   \* Set of possible shred indices
    MerkleRoots,    \* Set of possible Merkle root hashes
    ShredData,      \* Set of possible shred data
    MerklePaths,    \* Set of possible Merkle paths
    Signatures      \* Set of possible signatures
```

### Type Definition
```tla
Shred == [
    slot: Slots,
    sliceIndex: SliceIndices,
    shredIndex: ShredIndices,
    isLastSlice: BOOLEAN,          \* z_t flag
    merkleRoot: MerkleRoots,       \* r_t
    data: ShredData,               \* d_i
    merklePath: MerklePaths,       \* π_i
    signature: Signatures          \* σ_t
]
```

### Validation Functions
```tla
\* Check if shred has valid structure
IsValidShred(shred) ==
    /\ shred.slot \in Slots
    /\ shred.sliceIndex \in SliceIndices
    /\ shred.shredIndex \in ShredIndices
    /\ shred.isLastSlice \in BOOLEAN
    /\ shred.merkleRoot \in MerkleRoots
    /\ shred.data \in ShredData
    /\ shred.merklePath \in MerklePaths
    /\ shred.signature \in Signatures

\* Verify Merkle path for shred data
VerifyShredMerklePath(shred) ==
    \* Abstract verification - would check that merklePath proves
    \* shred.data is at position shred.shredIndex for root shred.merkleRoot
    TRUE  \* Placeholder for actual cryptographic verification

\* Verify signature on slice object
VerifyShredSignature(shred, leader) ==
    \* Abstract verification - would check signature on Slice(s, t, z_t, r_t)
    \* by the designated leader for this slot
    TRUE  \* Placeholder for actual cryptographic verification
```

### Operations
```tla
\* Create a new shred
CreateShred(slot, sliceIdx, shredIdx, isLast, root, data, path, sig) ==
    [slot |-> slot,
     sliceIndex |-> sliceIdx,
     shredIndex |-> shredIdx,
     isLastSlice |-> isLast,
     merkleRoot |-> root,
     data |-> data,
     merklePath |-> path,
     signature |-> sig]

\* Check if shred fits in UDP datagram (size constraint)
FitsInUDPDatagram(shred) ==
    \* Abstract size check - would verify shred size <= UDP_MAX_SIZE
    TRUE  \* Placeholder for actual size validation
```

## Dependencies
- **Definition 2 (slice)**: The z_t flag indicates if this is the last slice
- **Merkle tree construction**: For data verification via π_i and r_t
- **Digital signatures**: For σ_t verification
- **Leader assignment function**: To validate signature source

## Implementation Notes
1. The actual cryptographic operations (Merkle path verification, signature verification) are abstracted in TLA+
2. Size constraints for UDP datagrams should be modeled as a boolean property
3. The relationship between shreds and slices needs careful modeling of the erasure coding reconstruction
4. Leader function leader(s) must be defined to validate signatures

## Testing Properties
```tla
\* Property: Valid shreds maintain their structure
ValidShredPreservation ==
    \A shred \in Shred :
        IsValidShred(shred) =>
            /\ VerifyShredMerklePath(shred)
            /\ FitsInUDPDatagram(shred)

\* Property: Shreds from correct leaders have valid signatures
CorrectLeaderSignatures ==
    \A shred \in Shred :
        \A leader \in Nodes :
            IsCorrectLeader(leader, shred.slot) =>
                VerifyShredSignature(shred, leader)
```