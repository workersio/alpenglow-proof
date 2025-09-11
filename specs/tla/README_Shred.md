# Shred TLA+ Specification

This directory contains the TLA+ specification for Definition 1 (Shred) from the Alpenglow white paper.

## Files

- `Shred.tla` - Main specification module
- `Shred.cfg` - Configuration file for model checking
- `ShredTest.tla` - Test module with sample scenarios
- `README_Shred.md` - This documentation

## Definition 1: Shred

A shred fits neatly in a UDP datagram with the form:
```
(s, t, i, z_t, r_t, (d_i, π_i), σ_t)
```

Where:
- `s` = slot number
- `t` = slice index  
- `i` = shred index
- `z_t` = flag indicating last slice (boolean)
- `r_t` = Merkle root hash
- `d_i` = data at position i
- `π_i` = Merkle path proving data position
- `σ_t` = signature from slot leader

## Key Properties Verified

1. **Valid Structure**: All shreds maintain proper field types
2. **No Duplicates**: No two shreds can exist at the same position (s,t,i)
3. **Signature Validity**: All shreds have valid leader signatures
4. **Merkle Consistency**: All Merkle paths are valid
5. **UDP Size Constraint**: All shreds fit in UDP datagrams
6. **Data Integrity**: All fields contain valid values

## Running the Specification

### Prerequisites
- TLA+ tools installed (TLC model checker, TLAPS prover)
- Java runtime environment

### Model Checking
```bash
# Run TLC model checker
java -cp tla2tools.jar tlc2.TLC Shred.tla -config Shred.cfg

# Run with more workers (for faster checking)
java -cp tla2tools.jar tlc2.TLC Shred.tla -config Shred.cfg -workers 4
```

### Running Tests
```bash
# Check test module
java -cp tla2tools.jar tlc2.TLC ShredTest.tla
```

## Configuration

The `Shred.cfg` file defines small finite sets for model checking:
- 3 slots, 2 slice indices, 4 shred indices
- 3 Merkle roots, 3 data values, 3 paths, 3 signatures
- 3 nodes, UDP max size of 1500 bytes

For larger-scale verification, increase these set sizes, but expect longer model checking times.

## Abstract Operations

Several operations are abstracted for TLA+ specification:
- **Cryptographic verification**: `VerifyShredMerklePath()`, `VerifyShredSignature()`
- **Size calculation**: `FitsInUDPDatagram()` 
- **Leader selection**: `Leader()` function

In a concrete implementation, these would use actual:
- SHA-256 or other hash functions
- Digital signature schemes (Ed25519, etc.)
- Precise byte-size calculations
- Verifiable random functions for leader selection

## Safety Properties

The specification enforces several critical safety properties:

1. **Position Uniqueness**: `NoDuplicatePositions`
   - Prevents conflicting shreds at same (slot, slice, shred) position

2. **Structural Integrity**: `ValidShredPreservation`
   - All shreds maintain valid structure and pass verification

3. **Cryptographic Validity**: `CorrectLeaderSignatures`, `MerklePathConsistency`
   - All signatures and Merkle proofs are valid

## Integration with Other Definitions

This Shred specification is designed to integrate with:
- **Definition 2 (Slice)**: Shreds are erasure-coded to reconstruct slices
- **Definition 3 (Block)**: Slices combine to form blocks
- **Rotor Protocol**: Shreds are disseminated through the network
- **Blokstor**: Shreds are stored and validated upon receipt

## Future Extensions

Potential enhancements to this specification:
- Add erasure coding reconstruction logic
- Model network dissemination and arrival timing
- Include repair mechanisms for missing shreds
- Add stake-weighted leader selection
- Model Byzantine behavior and fault tolerance