# Alpenglow Consensus Protocol: Formal Verification Plan

## Executive Summary

This document outlines a comprehensive plan for formally modeling and verifying the Alpenglow consensus protocol using TLA+ and the TLC model checker. Alpenglow is a high-performance proof-of-stake blockchain consensus protocol that achieves finalization in one round with 80% stake participation or two rounds with 60% participation. Our goal is to create a mathematically rigorous specification that proves the protocol's safety and liveness properties under various failure scenarios.

## 1. Protocol Overview

### 1.1 Core Innovation
Alpenglow introduces a "20+20" resilience model:
- Tolerates 20% Byzantine (malicious) stake
- Additional 20% can be offline under stronger network assumptions
- Achieves finalization in min(δ₈₀%, 2·δ₆₀%) time

### 1.2 Key Components
1. **Votor**: The voting algorithm that handles block finalization
2. **Rotor**: Erasure-coded block distribution (optimization, not safety-critical)
3. **Pool**: Local data structure storing votes and certificates
4. **Blokstor**: Storage for blocks and their relationships

## 2. Modeling Scope and Boundaries

### 2.1 What We MUST Model (Safety-Critical)

#### 2.1.1 Core Consensus Components
- **All 5 vote types** (Definition 11 from whitepaper):
  - NotarVote(slot, hash)
  - NotarFallbackVote(slot, hash)
  - SkipVote(slot)
  - SkipFallbackVote(slot)
  - FinalVote(slot)

- **All 5 certificate types** (Table 6):
  - Fast-Finalization Certificate (≥80% stake on NotarVote)
  - Notarization Certificate (≥60% stake on NotarVote)
  - Notar-Fallback Certificate (≥60% stake on NotarVote OR NotarFallbackVote)
  - Skip Certificate (≥60% stake on SkipVote OR SkipFallbackVote)
  - Finalization Certificate (≥60% stake on FinalVote)

#### 2.1.2 Critical State Machine Components (Algorithms 1–2; Defs. 12–18)
- **Validator State Variables**:
  - Per-slot `state[s]` items: `ParentReady(h)`, `Voted`, `VotedNotar(h)`, `BlockNotarized(h)`, `ItsOver`, `BadWindow` (Def. 18).
  - `pendingBlocks[s]` buffer to retry notarization once preconditions hold (Def. 18).
  - `firstSlot` detection for leader window boundaries (Alg. 2 `windowSlots`).

- **Pool-Driven Events** (Defs. 15–16):
  - `Block(s, h, parent)` from Blokstor when a complete block for slot `s` is reconstructed.
  - `ParentReady(s, h)`: `s` must be the first slot of its leader window and Pool must hold (i) a notarization or notar-fallback certificate for some prior block `b`, and (ii) skip certificates for all intermediate slots `s'` with `slot(b) < s' < s`.
  - `SafeToNotar(s, h)`: only after the node cast its initial vote in `s` (but not notarized `h`), and iff Def. 16 thresholds hold (see 2.3).
  - `SafeToSkip(s)`: only after the node cast its initial vote in `s` (but not skip), and iff Def. 16 threshold holds (see 2.3).
  - `Timeout(i)`: a single timeout per slot in the current window, scheduled at `clock() + Δtimeout + (i − s + 1)·Δblock` when the first `ParentReady` for that window is seen (Def. 17).

- **Vote Multiplicity Rules** (Def. 12):
  - First notarization OR skip vote per slot per node is stored.
  - Up to 3 notar-fallback votes stored per slot per node.
  - First skip-fallback vote stored; first finalization vote stored.

#### 2.1.3 Block Structure and Relationships
- Blocks with unique hashes
- Parent-child relationships (DAG structure)
- Slot assignment (natural numbers, monotonically increasing)
- Genesis block as root
- **Leader assignment per slot** (leader(s) function)
- **Block validity checks** before voting

#### 2.1.4 Timing and Synchrony
- Slot-based time progression.
- A single timeout family `Timeout(i)` scheduled for all slots `i` in a leader window when `ParentReady(firstSlot, …)` is received, with schedule `clock() + Δtimeout + (i − s + 1)·Δblock` (Def. 17).
- Partial synchrony assumptions (GST) and message delays bounded after GST; clocks unsynchronized but local timers only (Sec. 1.5; Def. 17 notes).
- Leader window boundaries (`windowSlots` function) constrain allowable voting dependencies within a window (Alg. 2).

#### 2.1.5 Stake Distribution
- Validator set V with stake function ρ: V → ℕ
- Byzantine stake < 20% (Assumption 1)
- Optional: Additional 20% crash failures (Assumption 2)
- **Stake aggregation rules** for mixed vote types in certificates

### 2.2 What We Can Abstract (Non-Critical for Safety)

1. **Rotor/Turbine**: Block distribution mechanism (abstract as eventual delivery)
2. **Cryptographic details**: Abstract signatures as validator identities
3. **Network topology**: Abstract as point-to-point communication
4. **Transaction execution**: Focus on consensus, not computation
5. **Leader election details**: Abstract as deterministic schedule

### 2.3 What We Must NOT Simplify

1. **Two-phase voting**: Both fast (1-round) and slow (2-round) paths must run concurrently
2. **Fallback mechanisms**: SafeToNotar and SafeToSkip events with the exact thresholds from Definition 16, and with the “initial vote already cast” precondition:
   - SafeToNotar(s, b): only if the node already voted in slot `s`, but not to notarize `b`, and either:
     - (i) `notar(b) ≥ 40%`, OR  
     - (ii) `skip(s) + notar(b) ≥ 60%` AND `notar(b) ≥ 20%`
   - SafeToSkip(s): only if the node already voted in slot `s`, but not to skip, and `skip(s) + Σ_b notar(b) − max_b notar(b) ≥ 40%`.
   - Count each node’s stake at most once per slot, even if it sent multiple vote types (Def. 12/16).
3. **Vote counting**: Exact stake percentages (60%, 80%) are protocol constants
4. **Block ancestry**: Finalization must propagate to ancestors (Definition 14)
5. **Vote ordering constraints**: Cannot vote finalization after casting fallback votes
6. **Certificate uniqueness**: At most one certificate of each type per slot/block

## 3. Safety Properties to Prove

### 3.1 Primary Safety Invariant (Theorem 1)
**Statement**: If a correct node finalizes block b in slot s, then if any correct node finalizes block b' in slot s' ≥ s, then b' is a descendant of b.

**Formal TLA+ Expression**:
```tla
SafetyInvariant == 
  \A n1, n2 \in CorrectNodes :
  \A b1, b2 \in FinalizedBlocks[n1] \X FinalizedBlocks[n2] :
    (slot[b1] <= slot[b2]) => IsAncestor(b1, b2)
```

### 3.2 Secondary Safety Properties

#### 3.2.1 Unique Finalization per Slot
At most one block can be finalized per slot across all correct nodes.

#### 3.2.2 No Conflicting Certificates
- Cannot have both a notarization certificate and skip certificate for same slot
- Cannot have notarization certificates for different blocks in same slot
- If a fast-finalization certificate exists in Pool, a notarization certificate (and thus a notar-fallback certificate) must also exist at that node; this follows directly from Table 6 and Def. 13’s note (Σ≥80% implies Σ≥60%).

#### 3.2.3 Ancestry Preservation
When block b is finalized, all ancestors of b are finalized (recursively).

#### 3.2.4 Vote Uniqueness (Lemma 20)
Correct nodes cast at most one initial vote (notar or skip) per slot.

#### 3.2.5 Vote Ordering Constraints (Lemma 22)
- No finalization vote after notar-fallback vote in same slot
- No finalization vote after skip-fallback vote in same slot
- BadWindow state prevents finalization voting

#### 3.2.6 Notarization Implications (Lemmas 23-25)
- 40% correct stake on block b prevents notarization of b' ≠ b
- Every finalized block is also notarized
- Fast-finalized blocks have unique notarization

## 4. Liveness Properties to Prove

### 4.1 Primary Liveness Property (Theorem 2)
**Statement**: During periods of synchrony (after GST), if the leader is correct and network is stable, new blocks are continuously finalized.

**Formal Specification**:
```tla
LivenessProperty ==
  AfterGST => 
    \E slot \in Nat : 
      Eventually(BlockFinalizedInSlot(slot))
```

Notes: Liveness relies on (i) timely `ParentReady` emission conditions (Definition 15), and (ii) the single `Timeout(i)` mechanism (Definition 17). We do not introduce separate vote/finalization timeouts; the protocol uses one timer family only.

### 4.2 Secondary Liveness Properties

#### 4.2.1 Certificate Generation
Under synchrony, every slot eventually gets either:
- A notarization certificate for some block, OR
- A skip certificate

#### 4.2.2 Progress Guarantee
The highest finalized slot number increases without bound (no permanent halting).

## 5. Adversarial Model

### 5.1 Byzantine Adversary Capabilities
- Controls < 20% of total stake
- Can send arbitrary messages (violate protocol)
- Can see all messages before deciding actions
- Can coordinate Byzantine nodes perfectly
- Cannot forge cryptographic signatures
- Cannot prevent eventual message delivery after GST

### 5.2 Network Adversary (Before GST)
- Can delay messages arbitrarily
- Can reorder messages
- Can partition the network
- Cannot drop messages permanently (eventual delivery)

### 5.3 Crash Failures (Optional, Assumption 2)
- Additional 20% stake can crash (stop responding)
- Crashed nodes don't recover within the execution trace
- Total faulty stake (Byzantine + crashed) < 40%

### 5.4 Additional Assumption for Extra Crash Tolerance
- Assumption 3 (Rotor non-equivocation): If a correct node receives a full block via Rotor for some slot, any other correct node that receives a full block for the same slot receives the same block (Sec. 2.11). This strengthens liveness under crash faults without affecting safety.

## 6. Verification Strategy

### 6.1 Incremental Modeling Approach

#### Phase 1: Single-Slot Consensus
1. Model single slot with fixed validator set
2. Verify vote aggregation and certificate generation
3. Prove fast-finalization (80%) and slow-finalization (60%) paths
4. Test with minimal validator sets (4-5 validators)

#### Phase 2: Multi-Slot with Parents
1. Extend to multiple sequential slots
2. Add parent-child block relationships
3. Verify ancestry finalization
4. Test leader rotation

#### Phase 3: Concurrent Voting Paths
1. Model concurrent fast and slow paths
2. Add fallback voting mechanisms
3. Implement SafeToNotar and SafeToSkip events
4. Verify no conflicting finalizations

#### Phase 4: Byzantine Behavior
1. Add Byzantine nodes with adversarial actions
2. Model equivocation (voting multiple times)
3. Test safety under maximum Byzantine stake (19.9%)
4. Verify timeout-based recovery

#### Phase 5: Network Adversary
1. Model message delays and reordering
2. Add GST (Global Stabilization Time)
3. Verify liveness after GST
4. Test network partitions

### 6.2 Model Checking Strategy

#### 6.2.1 State Space Reduction
- **Small constants**: 4-6 validators, 3-5 slots, 2-3 blocks
- **Symmetry reduction**: Exploit validator symmetry
- **View abstraction**: Abstract message contents where possible
- **Bounded model checking**: Limit execution depth

#### 6.2.2 Critical Scenarios to Test
1. **Fast path only**: All nodes online, no delays
2. **Slow path only**: 20% Byzantine, requires 2 rounds
3. **Path racing**: Fast and slow paths compete
4. **Leader failure**: Byzantine leader, skip certificates needed
5. **Network partition**: Temporary partition, recovery after GST
6. **Cascading timeouts**: Multiple validators timeout simultaneously
7. **Rejoin/resync**: A node reboots or joins late; validates it can safely reconstruct state using either a fast-finalization certificate for some slot or a finalization certificate for the slot together with a notarization certificate for the unique notarized block in that slot (Sec. 3.3).

### 6.3 Proof Techniques

#### 6.3.1 Inductive Invariant Method
1. Define inductive invariant implying safety
2. Prove invariant holds initially
3. Prove invariant preserved by all actions
4. Use TLC to find counterexamples to candidate invariants

#### 6.3.2 Refinement Mapping
1. Create abstract specification (simple consensus)
2. Prove Alpenglow refines abstract spec
3. Inherit safety properties from abstract spec

#### 6.3.3 Compositional Verification
1. Verify Pool operations separately
2. Verify certificate generation independently
3. Compose proofs for full protocol

## 7. TLA+ Module Architecture

### 7.1 Module Hierarchy
```
AlpenglowMain.tla
├── NetworkModel.tla      (message passing, delays, GST)
├── ValidatorModel.tla    (validator states and actions)
├── VotingLogic.tla      (Votor algorithm implementation)
│   ├── VoteTypes.tla    (5 vote type definitions)
│   └── CertificateTypes.tla (5 certificate types)
├── BlockStructure.tla   (blocks, parents, slots)
├── Pool.tla             (vote/certificate storage)
├── StakeModel.tla       (stake distribution, quorums)
├── TimeModel.tla        (slots, timeouts, synchrony)
└── AdversaryModel.tla   (Byzantine and network adversary)
```

Notes:
- `TimeModel.tla` implements the single `Timeout(i)` family per Definition 17; no separate finalize timers.
- `Pool.tla` enforces vote storage multiplicity (Def. 12) and stake-count-once-per-slot when aggregating evidence for Def. 16 and certificate thresholds.

### 7.2 Key Type Definitions
```tla
Block == [
  hash: BlockHash,
  parent: BlockHash,
  slot: Nat,
  leader: ValidatorId
]

Vote == [
  type: {"NotarVote", "NotarFallbackVote", "SkipVote", 
         "SkipFallbackVote", "FinalVote"},
  validator: ValidatorId, 
  slot: Nat,
  hash: BlockHash \union {NoBlock},
  signature: Signature
]

Certificate == [
  type: {"FastFinalizationCert", "NotarizationCert", 
         "NotarFallbackCert", "SkipCert", "FinalizationCert"},
  slot: Nat,
  hash: BlockHash \union {NoBlock},
  votes: SUBSET Vote,
  totalStake: Nat
]

ValidatorState == [
  votedNotar: BlockHash \union {None},
  votedSkip: BOOLEAN,
  badWindow: BOOLEAN,
  notarFallbackCount: 0..3,
  finalVoted: BOOLEAN
]
```

### 7.3 Critical Algorithm Components (MUST IMPLEMENT)

#### 7.3.1 Vote Casting Logic (Algorithms 1–2)
We follow the paper’s event-driven structure. Skip votes are produced by `trySkipWindow` when triggered by `Timeout(s)`, `SafeToNotar`, or `SafeToSkip`.

```tla
TryNotar(v, s, block, parent) ==
  /\ ~State[v][s].Voted
  /\ ((IsFirstSlotOfWindow(s) /\ ParentReadyInState(v, s, parent))
      \/ (~IsFirstSlotOfWindow(s) /\ VotedNotarForParentInPrevSlot(v, s, parent)))
  /\ CastNotarVote(v, s, block)
  /\ AddToState(v, s, <<Voted, VotedNotar(block)>>)

TryFinal(v, s, b) ==
  /\ BlockNotarizedInState(v, s, b)
  /\ VotedNotarInState(v, s, b)
  /\ ~BadWindowInState(v, s)
  /\ CastFinalVote(v, s)
  /\ AddToState(v, s, <<ItsOver>>)

TrySkipWindow(v, s0) ==
  \E k \in WindowSlots(s0) : ~State[v][k].Voted /\
     CastSkipVote(v, k) /\ AddToState(v, k, <<Voted, BadWindow>>)
```

#### 7.3.2 Fallback Event Detection (Definition 16)
```tla
SafeToNotarEvent(v, s, b) ==
  /\ State[v][s].Voted
  /\ ~VotedNotarInState(v, s, b)
  /\ ( NotarStake(s, b) >= 40 
     \/ ((SkipStake(s) + NotarStake(s, b) >= 60) /\ (NotarStake(s, b) >= 20)) )

SafeToSkipEvent(v, s) ==
  LET maxNotar == Max_b(NotarStake(s, b)) IN
  /\ State[v][s].Voted
  /\ ~VotedSkipInState(v, s)
  /\ (SkipStake(s) + TotalNotarStakeAllBlocks(s) - maxNotar >= 40)
```

## 8. Validation Methodology

### 8.1 Cross-Validation
1. **Reference implementation**: Create simplified Python model
2. **Trace validation**: Compare TLA+ traces with whitepaper examples
3. **Counterexample analysis**: For each TLC counterexample, determine if it's real or spurious
4. **Definition mapping**: Maintain a table mapping each TLA+ element/action/event to whitepaper Definitions 10–18, Algorithms 1–3, and Lemmas 20–33.

### 8.2 Incremental Confidence Building
1. Start with known-correct simple consensus (e.g., PBFT)
2. Add Alpenglow features incrementally
3. Verify each addition preserves safety
4. Document assumptions at each step

### 8.3 Peer Review Process
1. **Internal review**: Team validates model against whitepaper
2. **Expert review**: TLA+ experts review specification
3. **Academic review**: Consensus researchers validate approach
4. **Implementation team**: Verify model matches implementation intent

## 9. Success Criteria

### 9.1 Mandatory Requirements
- [ ] All 5 vote types correctly modeled
- [ ] All 5 certificate types with correct thresholds
- [ ] Safety invariant holds for all reachable states
- [ ] Fast-finalization path works with 80% stake
- [ ] Slow-finalization path works with 60% stake
- [ ] Byzantine nodes cannot violate safety with <20% stake
- [ ] Ancestry finalization correctly implemented
- [ ] No deadlocks in correct executions

### 9.2 Highly Desirable
- [ ] Liveness proven after GST
- [ ] Model scales to 10+ validators
- [ ] Crash failures (Assumption 2) modeled
- [ ] Leader rotation verified
- [ ] State space < 10M states for base configuration

### 9.3 Nice to Have
- [ ] TLAPS (theorem prover) proofs for key lemmas
- [ ] Performance metrics (finalization latency)
- [ ] Comparison with other consensus protocols
- [ ] Probabilistic analysis of finalization times

## 10. Formal Proof Obligations (CRITICAL ADDITION)

### 10.1 Core Safety Proof Obligations
1. **Invariant I1**: At most one block finalized per slot
   - Proof approach: Show certificate uniqueness prevents multiple finalizations
   
2. **Invariant I2**: Finalized blocks form a chain
   - Proof approach: Induction on slot numbers and parent relationships
   
3. **Invariant I3**: No conflicting certificates in same slot
   - Proof approach: Stake arithmetic; ensure the “count once per slot per node” rule when aggregating stake for mixed vote types (Defs. 12/16); can't have 60% + 60% > 100%.

4. **Invariant I4**: Fallback event mutual exclusion and gating (Def. 16)
   - Both fallback events require that the node already cast its initial vote in the slot.
   - Under Def. 16 arithmetic and count-once-per-slot rule, `SafeToNotar(s, b)` and `SafeToSkip(s)` cannot both hold simultaneously at a correct node.

### 10.2 Key Proof Dependencies
```
Theorem 1 (Main Safety)
  ├── Lemma 26 (Fast-finalized unique)
  │   ├── Lemma 20 (Vote uniqueness)
  │   └── 80% stake requirement
  ├── Lemma 27 (Slow-finalized unique)
  │   ├── Lemma 24 (One notarized block)
  │   ├── Lemma 22 (No final after fallback)
  │   └── Lemma 25 (Finalized → notarized)
  └── Ancestry preservation

For liveness (Thm. 2), dependencies include:
- Lemma 33 and Corollary 34 (timeouts scheduled for the entire window upon `ParentReady`).
- Lemma 35–37 (under synchrony, initial votes occur and either skip or notarization certificate emerges).
- Assumption 3 (Rotor non-equivocation) for the extra crash tolerance regime (Sec. 2.11).
```

### 10.3 Inductive Invariant Structure
The complete inductive invariant must include:
1. Local validator state consistency
2. Global certificate uniqueness
3. Stake accounting correctness
4. Message causality preservation
5. Temporal ordering of events

## 11. Risk Mitigation

### 11.1 Specification Risks
- **Risk**: Model doesn't match whitepaper
- **Mitigation**: Line-by-line mapping document, expert review

### 11.2 Verification Risks
- **Risk**: State explosion prevents verification
- **Mitigation**: Incremental approach, bounded model checking

### 11.3 Assumption Risks
- **Risk**: Hidden assumptions make proof invalid
- **Mitigation**: Explicit assumption documentation, sensitivity analysis

## 12. Timeline and Milestones

### Week 1-2: Foundation
- Set up TLA+ environment and tools
- Create basic type definitions
- Implement single-slot voting

### Week 3-4: Core Protocol
- Add all vote and certificate types
- Implement Pool operations
- Basic safety checking

### Week 5-6: Advanced Features
- Multi-slot operation
- Parent-child relationships
- Fallback mechanisms

### Week 7-8: Adversarial Testing
- Byzantine node behavior
- Network adversary
- Edge cases

### Week 9-10: Validation and Documentation
- Cross-validation with reference implementation
- Performance optimization
- Final documentation

## 13. Documentation Requirements

### 13.1 Specification Documentation
- Complete TLA+ spec with extensive comments
- Mapping between spec and whitepaper sections
- Assumption documentation
- Design decision rationale

### 13.2 Proof Documentation
- Invariant definitions and justification
- Proof sketches for key theorems
- TLC configuration and results
- Counterexample analysis

### 13.3 User Documentation
- How to run the model checker
- How to interpret results
- How to modify parameters
- Known limitations

## Appendix A: Key Definitions from Whitepaper

### Definition 11: Messages
Five vote types and five certificate types as specified in Tables 5 and 6.

### Definition 14: Finalization
Two paths to finalization:
1. Fast: 80% stake votes directly
2. Slow: 60% stake votes twice (notarization then finalization)

### Definition 16: Fallback Events
Exact thresholds and gating:
- SafeToNotar(s, b): only after the node has cast its initial vote in slot s (but not to notarize b), and either (i) notar(b) ≥ 40%, or (ii) skip(s) + notar(b) ≥ 60% and notar(b) ≥ 20%.
- SafeToSkip(s): only after the node has cast its initial vote in slot s (but not to skip), and skip(s) + Σ_b notar(b) − max_b notar(b) ≥ 40%.
- Each node’s stake is counted at most once per slot in these sums (Def. 12/16).

### Definition 15: Pool Events (preconditions summarized)
- ParentReady(s, h): s is first in its leader window and Pool holds (i) a notarization or notar-fallback certificate for some prior block b, and (ii) skip certificates for all slots s′ with slot(b) < s′ < s.

## Appendix B: Critical Lemmas to Verify

From the whitepaper:
- Lemma 20: Vote uniqueness per slot (at most one initial vote: notar OR skip)
- Lemma 21: Fast-finalized block prevents other notarizations/skips in same slot
- Lemma 22: No finalization vote after fallback votes (BadWindow flag prevents it)
- Lemma 23: 40% correct stake on block b prevents notarization of b' ≠ b
- Lemma 24: At most one block can be notarized per slot
- Lemma 25: Any finalized block is also notarized
- Lemma 26: Slow-finalized block prevents other notarizations/skips in same slot  
- Lemma 27: If notar/notar-fallback cert exists, some correct node cast notarization vote
- Lemma 28: Notarization vote for b implies notarization votes for all ancestors in window
- Lemma 29: Notar-fallback vote for non-first slot requires parent notarized or 40% voted
- Lemma 30: Notarized block has notarized/fallback ancestors in all prior window slots
- Lemma 31-32: Cross-window finalization ordering (blocks in later windows descend from earlier finalized blocks)
- Lemma 33-34: Timeout scheduling (ParentReady triggers timeouts for entire window)
- Lemma 35: Timeout forces vote (notar or skip) in slot
- Lemma 36: No ItsOver state without 40% notarization consensus
- Lemma 37: Every slot gets certificate (notar-fallback or skip) eventually
- Lemma 38: 40% notarization stake guarantees notar-fallback certificate
- Lemma 39-43: Liveness under synchrony (blocks arrive on time, votes cast)

## Appendix D: Complexity Analysis and State Space Management

### State Space Estimation
For n validators, s slots, and b blocks per slot:
- Vote combinations: O(n × s × 5) [5 vote types]
- Certificate combinations: O(s × 5 × 2^n) [power set of voters]
- Validator states: O(n × b^s × 2^3) [notar choice, skip, badWindow flags]
- Total worst case: O(n × b^s × 2^n)

### Reduction Strategies
1. **Symmetry Breaking**: 
   - Only distinguish Byzantine vs correct validators
   - Reduces from n! to (n-f)! permutations
   
2. **State Pruning**:
   - Ignore unreachable states (e.g., 100% Byzantine stake)
   - Prune states violating invariants early
   
3. **Abstraction**:
   - Abstract message contents when possible
   - Group validators by behavior patterns
   
4. **Bounded Checking**:
   - Limit to k=2 consecutive leader windows
   - Bound message reordering to depth d=3

## Appendix E: Edge Cases and Corner Scenarios

### Must Test These Specific Scenarios:
1. **Exactly 20% Byzantine stake** - boundary condition
2. **Exactly 40% non-participating** - Assumption 2 boundary
3. **Exactly 60% stake for certificates** - minimum threshold
4. **Exactly 80% stake for fast path** - fast finalization threshold
5. **3 notar-fallback votes** - maximum allowed
6. **Simultaneous SafeToNotar and SafeToSkip** - race condition
7. **Leader producing multiple blocks** - equivocation
8. **Network partition at slot boundary** - timing attack
9. **Byzantine nodes voting for future slots** - time manipulation
10. **Certificate with mixed vote types** - notar + notar-fallback

## Appendix C: Model Checking Configuration

### Recommended TLC Settings
```
CONSTANTS
  Validators = {v1, v2, v3, v4, v5}
  MaxSlot = 3
  MaxBlocks = 4
  ByzantineNodes = {v1}  // 20% stake
  
INVARIANTS
  SafetyInvariant
  NoConflictingCertificates
  ValidBlockChain
  
PROPERTIES
  EventualFinalization
  
SYMMETRY
  Permutations(Validators \ ByzantineNodes)
```

## Appendix F: Critical Protocol Invariants to Maintain

### State Consistency Invariants
1. **Vote State Consistency**: If `Voted ∈ state[s]`, then exactly one of `VotedNotar(h)` or `VotedSkip` is also in `state[s]`
2. **BadWindow Propagation**: If `BadWindow ∈ state[s]`, then no `FinalVote` can be cast in slot s
3. **ItsOver Finality**: If `ItsOver ∈ state[s]`, then no fallback votes can be cast in slot s
4. **Parent Readiness**: `ParentReady(s,h)` only if s is first slot of window AND parent has certificate

### Certificate Generation Invariants  
1. **Threshold Enforcement**: Certificates only created when exact thresholds met (60%, 80%)
2. **Vote Type Consistency**: Notar-Fallback cert can mix NotarVote and NotarFallbackVote types
3. **Skip Certificate Mixing**: Skip cert can mix SkipVote and SkipFallbackVote types
4. **Count-Once Rule**: Each validator's stake counted at most once per slot for thresholds

### Timing Invariants
1. **Single Timeout Family**: Only one timeout schedule per window (not separate vote/finalize timers)
2. **Window-Wide Scheduling**: Timeouts for all slots in window scheduled together on ParentReady
3. **Monotonic Scheduling**: Timeout(i) scheduled at `clock() + Δtimeout + (i-s+1)·Δblock`

## Conclusion

This plan provides a systematic approach to formally verifying the Alpenglow consensus protocol. By following this methodology, we will produce a TLA+ specification that:

1. **Accurately models** the protocol as described in the whitepaper
2. **Proves safety** under the stated Byzantine fault tolerance assumptions
3. **Demonstrates liveness** under partial synchrony
4. **Provides confidence** in the protocol's correctness
5. **Serves as documentation** for implementers and researchers

The incremental approach ensures we build confidence at each step while managing complexity. The extensive validation ensures our model accurately represents the intended protocol behavior.

Success depends on rigorous adherence to the whitepaper definitions, careful modeling of all voting paths, and thorough testing of adversarial scenarios. With this plan, we can achieve academic-level reliability in our formal verification of Alpenglow.
