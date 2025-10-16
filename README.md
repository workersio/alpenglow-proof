# Alpenglow Formal Verification

Formal verification of the Alpenglow consensus protocol using TLA+ and Lean4.

## Docs

**Proof docs** - `lean-specs/doc` - Auto generated using doc-gen4

## Overview

This repository contains formal specifications and proofs for Alpenglow, a Byzantine fault-tolerant consensus protocol with fast finality and crash tolerance. The work includes both model checking in TLA+ and machine-checked proofs in Lean4.

## What We've Built

### TLA+ Specification (`specs/`)

The TLA+ models formalize the protocol described in the Alpenglow whitepaper, covering the core consensus mechanisms:

- **MainProtocol.tla** - Top-level protocol model integrating Votor (voting), Rotor (dissemination), Blokstor (storage), and Repair mechanisms
- **VotorCore.tla** - Validator state machines and voting logic per Algorithms 1-2
- **Rotor.tla** - Block dissemination with PS-P relay sampling
- **Certificates.tla** - Certificate generation and threshold validation
- **VoteStorage.tla** - Vote pool management and storage rules
- **Blocks.tla** - Block structure and chain relationships
- **Messages.tla** - Vote and certificate message formats

### Lean4 Proofs (`lean-specs/`)

The Lean4 development proves safety properties from the whitepaper using mechanically verified proofs:

**Core Lemmas:**
- **Lemma20.lean** - Vote uniqueness (one initial vote per slot)
- **Lemma21.lean** - Fast finalization excludes conflicting notarization
- **Lemma22.lean** - Final votes and fallback votes are mutually exclusive
- **Lemma23.lean** - Stake overlap prevents conflicting notarization
- **Lemma24.lean** - Uniqueness of notarized blocks per slot
- **Lemma25.lean** - Finalized blocks are notarized
- **Lemma26.lean** - Slow finalization requires unique notarization
- **Lemma27.lean** - Notar-fallback requires notarization support
- **Lemma28.lean** - Voting for a block implies voting for ancestors
- **Lemma29.lean** - Fallback votes require parent certificates
- **Lemma30.lean** - Notarized blocks have ancestor support

**Protocol Components:**
- **Algorithm1.lean** - Timeout handling and fallback voting
- **Algorithm2.lean** - Event-driven voting logic
- **Basics.lean** - Core data structures (blocks, votes, certificates)
- **Blokstor.lean** - Block storage abstractions

## What's Verified

### TLA+ Specification

The TLA+ models define both safety and liveness properties:

**Safety Properties:**
- No conflicting finalization (Theorem 1)
- Vote uniqueness per slot (Lemma 20)
- Unique notarization per slot (Lemmas 23-24)
- Certificate generation correctness
- Dual voting paths (fast 80% threshold, slow 60% threshold)
- Byzantine resilience under protocol assumptions

**Liveness Properties (with fairness constraints):**
- Basic liveness: blocks eventually finalize after GST (Theorem 2)
- Progress: each correct node eventually increases its highest finalized slot
- Window finalization: correct leader windows finalize completely
- Fast path: fast-finalization certificates lead to finalization
- Repair: nodes eventually obtain needed blocks after GST

### Lean4 Proofs

The Lean4 development establishes safety properties through mechanically verified proofs, including the key lemmas from Section 2.9 of the whitepaper that together prove Theorem 1 (safety). Liveness properties are modeled in TLA+ but not yet fully proven in Lean4.

## Model Definitions

### TLA+ Models

**Configuration:**
- `specs/MC.cfg` - Model checking configuration
- `specs/MC.tla` - Model constants and state constraints

**Core Definitions:**
- Byzantine nodes hold &lt;20% stake (Assumption 1)
- Crash failures ≤20% stake with ≥60% correct nodes (Assumption 2)
- Single epoch with fixed stake distribution
- Global stabilization time (GST) for synchrony

### Lean4 Definitions

**Key Structures:**
- `VotorState` - Validator local state with slot tags and vote pool
- `VotorConfig` - Protocol parameters (thresholds, window size)
- `NotarVote`, `SkipVote`, `FinalVote` - Vote types
- `Certificate` - Aggregated vote certificates
- `StakeWeight` - Stake distribution over validators

**Thresholds:**
- Fast finalization: 80% stake
- Notarization: 60% stake
- Fallback: 40% stake
- Byzantine bound: &lt;20% stake

## Repository Structure

```
alpenglow-proof/
├── specs/                    # TLA+ specifications
│   ├── MainProtocol.tla     # Main protocol model
│   ├── VotorCore.tla        # Voting logic
│   ├── Rotor.tla            # Dissemination
│   ├── Certificates.tla     # Certificate logic
│   ├── VoteStorage.tla      # Vote pool
│   ├── Blocks.tla           # Block structures
│   ├── Messages.tla         # Message types
│   └── MC*.cfg              # Model configs
├── lean-specs/              # Lean4 proofs
│   ├── Basics.lean          # Core definitions
│   ├── Algorithm1.lean      # Timeout logic
│   ├── Algorithm2.lean      # Voting logic
│   ├── Lemma*.lean          # Safety proofs
│   └── Corollary34.lean     # Derived results
└── alpenglow-whitepaper.md  # Protocol specification
```

## Running the Models

### TLA+

Requires TLC model checker. Run with:

```bash
java -XX:+UseParallelGC -jar tla2tools.jar -config specs/MC.cfg specs/MC.tla
```

### Lean4

Requires Lean4 and mathlib. Build with:

```bash
cd lean-specs
lake build
```

## References

This work formalizes the protocol described in the Alpenglow whitepaper. All lemma numbers and section references correspond to that document.
