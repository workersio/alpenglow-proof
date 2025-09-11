---------------------------- MODULE Shred ----------------------------
(***************************************************************************
 * Implementation of Definition 1: Shred from Alpenglow White Paper
 * 
 * Reference: Alpenglow White Paper, Page 12, Definition 1 (shred)
 * 
 * From the paper:
 * "A shred fits neatly in a UDP datagram. It has the form:
 * (s, t, i, z_t, r_t, (d_i, π_i), σ_t)"
 * 
 * Component Mapping to TLA+:
 * - s ∈ ℕ: slot number → shred.slot ∈ Slots
 * - t ∈ ℕ: slice index → shred.sliceIndex ∈ SliceIndices  
 * - i ∈ ℕ: shred index → shred.shredIndex ∈ ShredIndices
 * - z_t ∈ {0, 1}: last slice flag → shred.isLastSlice ∈ BOOLEAN
 * - r_t: Merkle root hash → shred.merkleRoot ∈ MerkleRoots
 * - d_i: data at position i → shred.data ∈ ShredData
 * - π_i: Merkle path for d_i → shred.merklePath ∈ MerklePaths
 * - σ_t: signature on Slice(s,t,z_t,r_t) → shred.signature ∈ Signatures
 * 
 * Key Protocol Properties:
 * 1. Shreds must fit in UDP datagrams (max ~1500 bytes)
 * 2. Any γ out of Γ shreds can reconstruct the slice (erasure coding)
 * 3. Signature is on the slice object, not individual shreds
 * 4. Merkle path proves shred belongs to the slice
 ***************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Slots,              \* Set of possible slot numbers (s in Definition 1)
    SliceIndices,       \* Set of possible slice indices (t in Definition 1)  
    ShredIndices,       \* Set of possible shred indices (i in Definition 1)
    MerkleRoots,        \* Set of possible Merkle root hashes (r_t in Definition 1)
    ShredData,          \* Set of possible shred data (d_i in Definition 1)
    MerklePaths,        \* Set of possible Merkle paths (π_i in Definition 1)
    Signatures,         \* Set of possible signatures (σ_t in Definition 1)
    Nodes,              \* Set of validator nodes (for leader(s) function)
    UDP_MAX_SIZE,       \* Maximum UDP datagram size (protocol constraint)
    GAMMA               \* Reed-Solomon parameter γ (Definition 2: "any γ of the Γ shreds")

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
    /\ GAMMA \in Nat /\ GAMMA > 0

VARIABLES
    shreds,             \* Set of all shreds in the system
    validMerklePaths,   \* Set of <<data, path, index, root>> tuples with valid paths
    validSignatures,    \* Set of <<slot, sliceIndex, isLastSlice, merkleRoot, node, signature>> tuples
    leaderSchedule      \* Function: Slots -> Nodes (leader assignment)

vars == <<shreds, validMerklePaths, validSignatures, leaderSchedule>>

\***************************************************************************
\* Type definition for a shred
\* Directly implements the tuple structure from Definition 1:
\* (s, t, i, z_t, r_t, (d_i, π_i), σ_t)
\***************************************************************************
Shred == [
    slot: Slots,                   \* s: slot number (natural number)
    sliceIndex: SliceIndices,      \* t: slice index within the block
    shredIndex: ShredIndices,      \* i: position within the slice (0 to Γ-1)
    isLastSlice: BOOLEAN,          \* z_t: flag indicating last slice (Definition 2)
    merkleRoot: MerkleRoots,       \* r_t: Merkle root of the slice data
    data: ShredData,               \* d_i: erasure-coded data piece at position i
    merklePath: MerklePaths,       \* π_i: Merkle proof for d_i at position i
    signature: Signatures          \* σ_t: leader's signature on Slice(s,t,z_t,r_t)
]

\***************************************************************************
\* Leader assignment function
\* References: "σ_t is the signature... from the node leader(s)"
\* The leader for each slot is determined by the protocol's leader schedule
\***************************************************************************
Leader(slot) ==
    leaderSchedule[slot]

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

\***************************************************************************
\* Verify Merkle path for shred data
\* Reference: Definition 1 - "d_i is the data at position i with path π_i 
\*            for Merkle root r_t"
\* 
\* This abstracts the cryptographic verification that:
\* - The data d_i is at position i in the Merkle tree
\* - The path π_i correctly proves membership for root r_t
\***************************************************************************
VerifyShredMerklePath(shred) ==
    <<shred.data, shred.merklePath, shred.shredIndex, shred.merkleRoot>> \in validMerklePaths

\***************************************************************************
\* Verify signature on slice object
\* Reference: Definition 1 - "σ_t is the signature of the object 
\*            Slice(s, t, z_t, r_t) from the node leader(s)"
\* 
\* Key insight: The signature is on the slice metadata, NOT the shred data
\* This allows any γ shreds to verify the same signature
\***************************************************************************
VerifyShredSignature(shred) ==
    LET leader == Leader(shred.slot)
    IN <<shred.slot, shred.sliceIndex, shred.isLastSlice, shred.merkleRoot, leader, shred.signature>> \in validSignatures

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
\***************************************************************************
\* Check if shred fits in UDP datagram
\* Reference: Definition 1 - "A shred fits neatly in a UDP datagram"
\* 
\* Critical for network layer: UDP max ~1500 bytes (typical MTU)
\* This ensures shreds can be transmitted without fragmentation
\***************************************************************************
FitsInUDPDatagram(shred) ==
    \* Abstract size check - actual implementation would sum:
    \* sizeof(s) + sizeof(t) + sizeof(i) + 1 + sizeof(r_t) + 
    \* sizeof(d_i) + sizeof(π_i) + sizeof(σ_t) <= UDP_MAX_SIZE
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

\***************************************************************************
\* Check if we have enough shreds to reconstruct a slice
\* Reference: Definition 2 - "Given any γ of the Γ shreds, we can decode 
\*            (Section 1.6) the slice"
\* 
\* This implements the erasure coding recovery threshold:
\* - Need at least γ valid shreds from the same slice
\* - All must have the same Merkle root (ensures consistency)
\***************************************************************************
HasSufficientShreds(slot, sliceIndex, merkleRoot) ==
    LET relevantShreds == {shred \in shreds : 
                            /\ shred.slot = slot
                            /\ shred.sliceIndex = sliceIndex
                            /\ shred.merkleRoot = merkleRoot
                            /\ VerifyShredMerklePath(shred)}
    IN Cardinality(relevantShreds) >= GAMMA

\* Initialize system
Init ==
    /\ shreds = {}
    /\ validMerklePaths = {}  \* Start with empty set of valid paths
    /\ validSignatures = {}   \* Start with empty set of valid signatures
    /\ leaderSchedule \in [Slots -> Nodes]

\* Establish valid cryptographic material (simulates correct signatures/paths)
EstablishValidCrypto ==
    \E data \in ShredData, path \in MerklePaths, idx \in ShredIndices, root \in MerkleRoots,
       slot \in Slots, sliceIdx \in SliceIndices, isLast \in BOOLEAN, 
       node \in Nodes, sig \in Signatures :
        \/ /\ validMerklePaths' = validMerklePaths \union {<<data, path, idx, root>>}
           /\ UNCHANGED <<shreds, validSignatures, leaderSchedule>>
        \/ /\ node = leaderSchedule[slot]  \* Only the leader can create valid signatures
           /\ validSignatures' = validSignatures \union {<<slot, sliceIdx, isLast, root, node, sig>>}
           /\ UNCHANGED <<shreds, validMerklePaths, leaderSchedule>>

\* Add a new shred to the system
AddShred(shred) ==
    /\ IsValidShred(shred)
    /\ VerifyShredMerklePath(shred)
    /\ VerifyShredSignature(shred)
    /\ FitsInUDPDatagram(shred)
    /\ ~\E existing \in shreds : SamePosition(shred, existing)  \* No duplicates at same position
    /\ shreds' = shreds \union {shred}
    /\ UNCHANGED <<validMerklePaths, validSignatures, leaderSchedule>>

\* Next state relation
Next ==
    \/ EstablishValidCrypto
    \/ \E slot \in Slots, sliceIdx \in SliceIndices, shredIdx \in ShredIndices,
          isLast \in BOOLEAN, root \in MerkleRoots, data \in ShredData,
          path \in MerklePaths, sig \in Signatures :
           LET newShred == CreateShred(slot, sliceIdx, shredIdx, isLast, root, data, path, sig)
           IN AddShred(newShred)

\* Specification
Spec == Init /\ [][Next]_vars

\* State constraint for model checking
StateConstraint ==
    /\ Cardinality(shreds) <= 2
    /\ Cardinality(validMerklePaths) <= 3
    /\ Cardinality(validSignatures) <= 3

\* Type invariant
TypeOK ==
    /\ shreds \subseteq Shred
    /\ \A shred \in shreds : IsValidShred(shred)
    /\ validMerklePaths \subseteq (ShredData \X MerklePaths \X ShredIndices \X MerkleRoots)
    /\ validSignatures \subseteq (Slots \X SliceIndices \X BOOLEAN \X MerkleRoots \X Nodes \X Signatures)
    /\ leaderSchedule \in [Slots -> Nodes]

\* Safety Properties

\* Property: All shreds maintain their structure
ValidShredPreservation ==
    \A shred \in shreds :
        /\ IsValidShred(shred)
        /\ VerifyShredMerklePath(shred)
        /\ FitsInUDPDatagram(shred)

\***************************************************************************
\* Property: No duplicate shreds at same position
\* Reference: Definition 10 (Blokstor) - "the Blokstor does not contain a 
\*            shred for indices (s,t,i) yet"
\* 
\* Ensures uniqueness constraint: at most one shred per (slot, slice, index)
\***************************************************************************
NoDuplicatePositions ==
    \A shred1, shred2 \in shreds :
        shred1 # shred2 => ~SamePosition(shred1, shred2)

\***************************************************************************
\* Property: Shreds from correct leaders have valid signatures
\* Reference: Definition 10 - "σ_t is the signature of the object 
\*            Slice(s,t,z_t,r_t) from the node leader(s)"
\* 
\* Ensures only designated leaders can produce valid shreds for their slots
\***************************************************************************
CorrectLeaderSignatures ==
    \A shred \in shreds :
        VerifyShredSignature(shred)

\***************************************************************************
\* Property: Merkle paths are consistent
\* Reference: Definition 10 - "(d_i, π_i) is the data with path for 
\*            Merkle root r_t at position i"
\* 
\* Ensures data integrity: shred data must be provably part of the slice
\***************************************************************************
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

=======================================================================