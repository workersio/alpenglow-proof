# Definition 2: Slice Implementation Plan

## Definition
A slice is the input of Rotor (Section 2.2). Given any γ of the Γ shreds, we can decode the slice. A slice has the form:
```
(s, t, z_t, r_t, M_t, σ_t)
```

Where:
- s, t ∈ ℕ are the slot number and slice index respectively
- z_t ∈ {0, 1} is a flag indicating the last slice index
- M_t is the decoding of the shred data {(d_i)}_{i ∈ I} for Merkle root r_t
- σ_t is the signature of the object Slice(s, t, z_t, r_t) from the node leader(s)

## TLA+ Implementation Plan

### Constants
```tla
CONSTANTS
    Slots,           \* Set of possible slot numbers
    SliceIndices,    \* Set of possible slice indices
    MerkleRoots,     \* Set of possible Merkle root hashes
    SliceData,       \* Set of possible decoded slice data
    Signatures,      \* Set of possible signatures
    GAMMA,           \* Minimum shreds needed for decoding (γ)
    CAPITAL_GAMMA    \* Total shreds in erasure code (Γ)
```

### Type Definition
```tla
Slice == [
    slot: Slots,
    sliceIndex: SliceIndices,
    isLastSlice: BOOLEAN,          \* z_t flag
    merkleRoot: MerkleRoots,       \* r_t
    data: SliceData,               \* M_t (decoded from shreds)
    signature: Signatures          \* σ_t
]
```

### Erasure Coding Operations
```tla
\* Decode slice from sufficient shreds
DecodeSlice(shreds, merkleRoot) ==
    \* Precondition: Have at least GAMMA shreds with same merkleRoot
    \* Returns decoded data M_t or FAILED
    IF Cardinality({sh \in shreds : sh.merkleRoot = merkleRoot}) >= GAMMA
    THEN
        \* Abstract decoding - would perform Reed-Solomon reconstruction
        LET validShreds == {sh \in shreds : 
                              /\ sh.merkleRoot = merkleRoot
                              /\ VerifyShredMerklePath(sh)} IN
        IF Cardinality(validShreds) >= GAMMA
        THEN SliceDataFromShreds(validShreds)  \* Abstract reconstruction
        ELSE "DECODE_FAILED"
    ELSE "INSUFFICIENT_SHREDS"

\* Check if we have enough shreds to decode slice
CanDecodeSlice(shreds, merkleRoot) ==
    Cardinality({sh \in shreds : 
                   /\ sh.merkleRoot = merkleRoot
                   /\ VerifyShredMerklePath(sh)}) >= GAMMA
```

### Validation Functions
```tla
\* Check if slice has valid structure
IsValidSlice(slice) ==
    /\ slice.slot \in Slots
    /\ slice.sliceIndex \in SliceIndices
    /\ slice.isLastSlice \in BOOLEAN
    /\ slice.merkleRoot \in MerkleRoots
    /\ slice.data \in SliceData
    /\ slice.signature \in Signatures

\* Verify slice signature by leader
VerifySliceSignature(slice, leader) ==
    \* Abstract verification - would check signature on 
    \* Slice(slot, sliceIndex, isLastSlice, merkleRoot) by leader
    TRUE  \* Placeholder for actual cryptographic verification

\* Check consistency with shreds
IsConsistentWithShreds(slice, shreds) ==
    \* Verify that slice was correctly decoded from the shreds
    /\ slice.data = DecodeSlice(shreds, slice.merkleRoot)
    /\ \A sh \in shreds : 
        /\ sh.slot = slice.slot
        /\ sh.sliceIndex = slice.sliceIndex
        /\ sh.isLastSlice = slice.isLastSlice
        /\ sh.merkleRoot = slice.merkleRoot
```

### Operations
```tla
\* Create slice from decoded shreds
CreateSliceFromShreds(shreds, slot, sliceIdx) ==
    IF shreds = {} THEN "NO_SHREDS"
    ELSE
        LET sampleShred == CHOOSE sh \in shreds : TRUE
            merkleRoot == sampleShred.merkleRoot
            isLast == sampleShred.isLastSlice
            decodedData == DecodeSlice(shreds, merkleRoot)
        IN
        IF decodedData \notin {"DECODE_FAILED", "INSUFFICIENT_SHREDS"}
        THEN [slot |-> slot,
              sliceIndex |-> sliceIdx,
              isLastSlice |-> isLast,
              merkleRoot |-> merkleRoot,
              data |-> decodedData,
              signature |-> sampleShred.signature]
        ELSE "SLICE_CREATION_FAILED"

\* Check if slice is the last in a block
IsLastSliceInBlock(slice) ==
    slice.isLastSlice = TRUE
```

## Dependencies
- **Definition 1 (shred)**: Slices are decoded from shreds
- **Reed-Solomon erasure coding**: For decoding M_t from shred data
- **Merkle tree verification**: For validating shred authenticity
- **Digital signatures**: For σ_t verification
- **Rotor protocol**: Slice is input to dissemination protocol

## Implementation Notes
1. The erasure coding operations are abstracted - actual Reed-Solomon implementation would be complex
2. The relationship between γ (GAMMA) minimum shreds and Γ (CAPITAL_GAMMA) total shreds is crucial
3. Signature verification needs the exact signed object format: Slice(s, t, z_t, r_t)
4. Error handling for failed decoding scenarios is important
5. The z_t flag coordination across all shreds of a slice must be consistent

## Testing Properties
```tla
\* Property: Sufficient valid shreds can always decode a slice
DecodeProperty ==
    \A shreds \in SUBSET Shred, merkleRoot \in MerkleRoots :
        (/\ Cardinality(shreds) >= GAMMA
         /\ \A sh \in shreds : 
            /\ sh.merkleRoot = merkleRoot
            /\ VerifyShredMerklePath(sh)) =>
        CanDecodeSlice(shreds, merkleRoot)

\* Property: Last slice flag consistency
LastSliceFlagConsistency ==
    \A slice \in Slice, shreds \in SUBSET Shred :
        IsConsistentWithShreds(slice, shreds) =>
            \A sh \in shreds : sh.isLastSlice = slice.isLastSlice

\* Property: Decoded slice preserves slot and index information
SliceShredConsistency ==
    \A slice \in Slice, shreds \in SUBSET Shred :
        IsConsistentWithShreds(slice, shreds) =>
            \A sh \in shreds : 
                /\ sh.slot = slice.slot
                /\ sh.sliceIndex = slice.sliceIndex
```