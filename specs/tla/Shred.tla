---------------------------- MODULE Shred ----------------------------
(*
Implementation of Definition 1: Shred from Alpenglow White Paper

A shred fits neatly in a UDP datagram. It has the form:
(s, t, i, z_t, r_t, (d_i, π_i), σ_t)

Where:
- s, t, i ∈ ℕ are slot number, slice index, shred index, respectively
- z_t ∈ {0, 1} is a flag (see Definition 2)
- d_i is the data at position i with path π_i for Merkle root r_t
- σ_t is the signature of the object Slice(s, t, z_t, r_t) from the node leader(s)
*)

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Slots,              \* Set of possible slot numbers
    SliceIndices,       \* Set of possible slice indices  
    ShredIndices,       \* Set of possible shred indices
    MerkleRoots,        \* Set of possible Merkle root hashes
    ShredData,          \* Set of possible shred data
    MerklePaths,        \* Set of possible Merkle paths
    Signatures,         \* Set of possible signatures
    Nodes,              \* Set of validator nodes
    UDP_MAX_SIZE        \* Maximum UDP datagram size

ASSUME
    /\ Slots # {}
    /\ SliceIndices # {}
    /\ ShredIndices # {}
    /\ MerkleRoots # {}
    /\ ShredData # {}
    /\ MerklePaths # {}
    /\ Signatures # {}
    /\ Nodes # {}
    /\ UDP_MAX_SIZE \in Nat /\ UDP_MAX_SIZE > 0

VARIABLES
    shreds              \* Set of all shreds in the system

vars == <<shreds>>

\* Type definition for a shred
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

\* Leader assignment function (abstract)
Leader(slot) ==
    CHOOSE node \in Nodes : TRUE  \* Placeholder - would use actual leader selection

\* Check if shred has valid structure
IsValidShred(shred) ==
    /\ shred \in Shred
    /\ shred.slot \in Slots
    /\ shred.sliceIndex \in SliceIndices
    /\ shred.shredIndex \in ShredIndices
    /\ shred.isLastSlice \in BOOLEAN
    /\ shred.merkleRoot \in MerkleRoots
    /\ shred.data \in ShredData
    /\ shred.merklePath \in MerklePaths
    /\ shred.signature \in Signatures

\* Verify Merkle path for shred data (abstract cryptographic operation)
VerifyShredMerklePath(shred) ==
    \* In a real implementation, this would verify that:
    \* shred.merklePath proves shred.data is at position shred.shredIndex 
    \* for Merkle root shred.merkleRoot
    /\ IsValidShred(shred)
    /\ shred.merklePath \in MerklePaths
    /\ shred.data \in ShredData
    /\ shred.merkleRoot \in MerkleRoots

\* Verify signature on slice object (abstract cryptographic operation)
VerifyShredSignature(shred) ==
    \* In a real implementation, this would verify the signature on
    \* Slice(shred.slot, shred.sliceIndex, shred.isLastSlice, shred.merkleRoot)
    \* by the designated leader for this slot
    /\ IsValidShred(shred)
    /\ LET leader == Leader(shred.slot)
       IN shred.signature \in Signatures

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
    \* Abstract size check - in practice would calculate actual byte size
    \* of all shred fields and verify <= UDP_MAX_SIZE
    IsValidShred(shred)

\* Get shred identifier (for uniqueness checking)
ShredId(shred) ==
    <<shred.slot, shred.sliceIndex, shred.shredIndex>>

\* Check if two shreds are for the same position
SamePosition(shred1, shred2) ==
    /\ shred1.slot = shred2.slot
    /\ shred1.sliceIndex = shred2.sliceIndex  
    /\ shred1.shredIndex = shred2.shredIndex

\* Get all shreds for a specific slice
GetShredsForSlice(slot, sliceIndex) ==
    {shred \in shreds : shred.slot = slot /\ shred.sliceIndex = sliceIndex}

\* Get all shreds with a specific Merkle root
GetShredsWithRoot(merkleRoot) ==
    {shred \in shreds : shred.merkleRoot = merkleRoot}

\* Check if we have enough shreds to potentially reconstruct a slice
\* (assuming we need some minimum number GAMMA)
HasSufficientShreds(slot, sliceIndex, merkleRoot) ==
    LET relevantShreds == {shred \in shreds : 
                            /\ shred.slot = slot
                            /\ shred.sliceIndex = sliceIndex
                            /\ shred.merkleRoot = merkleRoot
                            /\ VerifyShredMerklePath(shred)}
    IN Cardinality(relevantShreds) >= 1  \* Placeholder - would use actual GAMMA threshold

\* Initialize system
Init ==
    shreds = {}

\* Add a new shred to the system
AddShred(shred) ==
    /\ IsValidShred(shred)
    /\ VerifyShredMerklePath(shred)
    /\ VerifyShredSignature(shred)
    /\ FitsInUDPDatagram(shred)
    /\ ~\E existing \in shreds : SamePosition(shred, existing)  \* No duplicates at same position
    /\ shreds' = shreds \union {shred}

\* Next state relation
Next ==
    \E slot \in Slots, sliceIdx \in SliceIndices, shredIdx \in ShredIndices,
       isLast \in BOOLEAN, root \in MerkleRoots, data \in ShredData,
       path \in MerklePaths, sig \in Signatures :
        LET newShred == CreateShred(slot, sliceIdx, shredIdx, isLast, root, data, path, sig)
        IN AddShred(newShred)

\* Specification
Spec == Init /\ [][Next]_vars

\* Type invariant
TypeOK ==
    /\ shreds \subseteq Shred
    /\ \A shred \in shreds : IsValidShred(shred)

\* Safety Properties

\* Property: All shreds maintain their structure
ValidShredPreservation ==
    \A shred \in shreds :
        /\ IsValidShred(shred)
        /\ VerifyShredMerklePath(shred)
        /\ FitsInUDPDatagram(shred)

\* Property: No duplicate shreds at same position
NoDuplicatePositions ==
    \A shred1, shred2 \in shreds :
        /\ shred1 # shred2
        /\ SamePosition(shred1, shred2) =>
            FALSE  \* This should never happen

\* Property: Shreds from correct leaders have valid signatures
CorrectLeaderSignatures ==
    \A shred \in shreds :
        VerifyShredSignature(shred)

\* Property: Merkle paths are consistent
MerklePathConsistency ==
    \A shred \in shreds :
        VerifyShredMerklePath(shred)

\* Property: All shreds fit in UDP datagrams
UDPSizeConstraint ==
    \A shred \in shreds :
        FitsInUDPDatagram(shred)

\* Property: Shred data integrity
ShredDataIntegrity ==
    \A shred \in shreds :
        /\ shred.slot \in Slots
        /\ shred.sliceIndex \in SliceIndices
        /\ shred.shredIndex \in ShredIndices
        /\ shred.merkleRoot \in MerkleRoots
        /\ shred.data \in ShredData
        /\ shred.merklePath \in MerklePaths
        /\ shred.signature \in Signatures

\* Liveness Properties (would require fairness assumptions)

\* Property: If conditions are met, shreds can be added
\* CanAddShred ==
\*     \A shred \in Shred :
\*         /\ IsValidShred(shred)
\*         /\ VerifyShredMerklePath(shred)
\*         /\ VerifyShredSignature(shred)
\*         /\ FitsInUDPDatagram(shred)
\*         /\ ~\E existing \in shreds : SamePosition(shred, existing) =>
\*             \Diamond (shred \in shreds)

\* These invariants should be added to the model checker configuration 
\* when creating the TLC model, not in the specification itself.
\* Properties to check:
\* - TypeOK
\* - ValidShredPreservation  
\* - NoDuplicatePositions
\* - CorrectLeaderSignatures
\* - MerklePathConsistency
\* - UDPSizeConstraint
\* - ShredDataIntegrity

=======================================================================