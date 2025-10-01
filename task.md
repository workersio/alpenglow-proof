# Overview
Alpenglow is Solana's consensus protocol upgrade achieving dramatic improvements over TowerBFT: 100-150ms finalization (100x faster than current)

Dual-path consensus: Votor enables fast finalization with 80% stake participation or conservative finalization with 60% stake

Optimized block propagation: Rotor uses erasure coding for efficient single-hop block distribution

"20+20" resilience: Tolerates up to 20% Byzantine nodes plus 20% crashed/offline nodes under good network conditions

Despite rigorous academic design, Alpenglow currently has only paper-based mathematical proofs. For a blockchain securing billions in value, we need machine-checkable formal verification.

# The Challenge
Transform the mathematical theorems from the Alpenglow whitepaper into proofs using formal methods tools (TLA+ or Stateright). You must create abstract formal models and prove correctness properties in the paper.

# Key Requirements
## 1. Complete Formal Specification
- Protocol modeling in TLA+ or Stateright covering:
- Votor's dual voting paths (fast 80% vs slow 60% finalization)
- Rotor's erasure-coded block propagation with stake-weighted relay sampling
- Certificate generation, aggregation, and uniqueness properties
- Timeout mechanisms and skip certificate logic
- Leader rotation and window management

## 2. Machine-Verified Theorems
### Safety Properties:
- No two conflicting blocks can be finalized in the same slot
- Chain consistency under up to 20% Byzantine stake
- Certificate uniqueness and non-equivocation

### Liveness Properties:
- Progress guarantee under partial synchrony with >60% honest participation
- Fast path completion in one round with >80% responsive stake
- Bounded finalization time (min(δ₈₀%, 2δ₆₀%) as claimed in paper)

### Resilience Properties:
- Safety maintained with ≤20% Byzantine stake
- Liveness maintained with ≤20% non responsive stake
- Network partition recovery guarantees

## 3. Model Checking & Validation
Exhaustive verification for small configurations (4-10 nodes)
Statistical model checking for realistic network sizes

# Deliverables
GitHub Repository:
- Complete formal specification
- All proof scripts with reproducible verification results
- Submission must be original work and open-source under Apache 2.0

Technical Report and Video Walkthrough:
- Executive summary of verification results
- Detailed proof status for each theorem and lemmas

# Evaluation Criteria
Rigor: Successfully verify or refute core theorems with proper formal abstraction
Completeness: Comprehensive coverage including edge cases and boundary conditions