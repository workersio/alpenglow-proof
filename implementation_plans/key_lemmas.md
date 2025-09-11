# Key Lemmas for Alpenglow Implementation

Based on the white paper analysis, here are the critical lemmas that support the definitions and should have separate TLA+ implementations:

## Core Voting and Safety Lemmas

### Lemma 20: Notarization or Skip Exclusivity
**Statement**: A correct node exclusively casts only one notarization vote or skip vote per slot.

**TLA+ Implementation Plan**:
```tla
\* Property: No node votes both notarization and skip in same slot
NotarizationSkipExclusive ==
    \A v \in Validators, s \in Slots :
        ~(HasVotedNotar(v, s) /\ HasVotedSkip(v, s))

\* Property: At most one vote type per slot per validator
AtMostOneVotePerSlot ==
    \A v \in Validators, s \in Slots :
        Cardinality({vote \in GetVotesForSlot(v, s) : 
                     vote.type \in {"NotarVote", "SkipVote"}}) <= 1
```

### Lemma 21: Fast-Finalization Properties
**Statement**: If a block b is fast-finalized: (i) no other block b' in same slot can be notarized, (ii) no other block b' can be notar-fallback certified, (iii) no skip certificate exists for same slot.

**Dependencies**: Definition 14 (finalization), Definition 11 (messages)

### Lemma 23-24: Block Notarization Uniqueness  
**Statement**: At most one block can be notarized in a given slot. If >40% stake votes for block b, no other block can be notarized in same slot.

**TLA+ Implementation Plan**:
```tla
\* Property: Unique notarized block per slot
UniqueNotarizedBlock ==
    \A s \in Slots :
        Cardinality(GetNotarizedBlocksInSlot(s)) <= 1

\* Property: 40% threshold prevents conflicts
FortyPercentPreventsConflicts ==
    \A s \in Slots, b1, b2 \in BlockHashes :
        /\ b1 # b2
        /\ NotarStake(s, b1) > StakeThreshold40 =>
            NotarStake(s, b2) <= StakeThreshold60 - NotarStake(s, b1)
```

## Rotor Protocol Lemmas

### Lemma 7: Rotor Resilience
**Statement**: With erasure coding over-provisioning κ = Γ/γ > 5/3, if γ→∞, probability 1 that slice is received correctly.

**TLA+ Implementation Plan**:
```tla
\* Property: Sufficient correct relays ensure delivery
RotorResilience ==
    \A slot \in Slots :
        /\ LeaderCorrect(slot)
        /\ Cardinality(CorrectRelays(slot)) >= GAMMA =>
            \A v \in CorrectNodes : EventuallyReceives(v, slot)
```

### Lemma 8: Rotor Latency
**Statement**: If Rotor succeeds, network latency ≤ 2δ. With high over-provisioning, can approach δ.

### Lemma 9: Bandwidth Optimality
**Statement**: Rotor delivers data at rate β_ℓ/κ, which is optimal up to expansion rate κ.

## Chain Safety and Liveness Lemmas

### Lemma 28: Ancestor Voting Consistency
**Statement**: If correct node votes for block b in slot s, then for every slot s' ≤ s in same window, it voted for ancestor b' in slot s'.

**TLA+ Implementation Plan**:
```tla
\* Property: Window voting consistency
WindowVotingConsistency ==
    \A v \in Validators, s \in Slots, b \in Blocks :
        /\ HasVotedNotar(v, s, Hash(b))
        /\ IsInSameWindow(s, slot) =>
            \A ancestor \in AllAncestors(b) :
                ancestor.slot \in WindowSlots(s) =>
                    HasVotedNotar(v, ancestor.slot, Hash(ancestor))
```

### Lemma 31-32: Finalization Ordering
**Statement**: If block b_i is finalized and b_k is in same/later window, then if b_k gets notarized, b_k must be descendant of b_i.

**TLA+ Implementation Plan**:
```tla
\* Property: Finalization preserves chain order
FinalizationOrdering ==
    \A bi, bk \in Blocks :
        /\ IsFinalized(Hash(bi))
        /\ IsNotarized(Hash(bk))
        /\ bi.slot <= bk.slot =>
            Ancestor(bi, bk)
```

## Timeout and Liveness Lemmas

### Lemma 35: Timeout Forces Voting
**Statement**: If all correct nodes set timeout for slot s, all will cast notarization or skip vote in s.

**TLA+ Implementation Plan**:
```tla
\* Property: Timeouts ensure voting
TimeoutForcesVoting ==
    \A s \in Slots :
        (\A v \in CorrectNodes : TimeoutSet(v, s)) =>
            \A v \in CorrectNodes : 
                \/ HasVotedNotar(v, s)
                \/ HasVotedSkip(v, s)
```

### Lemma 37: Progress Guarantee
**Statement**: If all correct nodes set timeout for slot s, either skip certificate observed or >40% stake votes for same block.

### Lemma 41-42: Universal Timeout Setting
**Statement**: All correct nodes eventually set timeouts. After GST, timeouts propagate within Δ time.

## Certificate and Fallback Lemmas

### Lemma 38: Stake Threshold Implies Certificates
**Statement**: If >40% correct stake votes for block b, all correct nodes observe notar-fallback certificate for b.

**TLA+ Implementation Plan**:
```tla
\* Property: Sufficient stake guarantees certificate visibility
StakeImpliesCertificate ==
    \A b \in Blocks :
        NotarStake(b.slot, Hash(b)) > StakeThreshold40 =>
            \A v \in CorrectNodes : 
                \Diamond ObservesCertificate(v, "NotarFallback", Hash(b))
```

## Implementation Priority

### High Priority (Core Safety)
1. **Lemma 20**: Vote exclusivity - prevents double voting
2. **Lemma 23-24**: Notarization uniqueness - prevents forks
3. **Lemma 21**: Fast-finalization properties - safety under 80% threshold

### Medium Priority (Chain Properties)
1. **Lemma 28**: Ancestor voting consistency - chain validity
2. **Lemma 31-32**: Finalization ordering - prevents rollbacks
3. **Lemma 38**: Certificate propagation - liveness guarantees

### Lower Priority (Performance)
1. **Lemma 7-9**: Rotor properties - dissemination guarantees
2. **Lemma 35, 37, 41-42**: Timeout and progress - liveness under synchrony

## Common TLA+ Patterns for Lemmas

### Safety Properties (□P)
```tla
\* Always true once established
THEOREM SafetyProperty == 
    Spec => □(Condition => □Property)
```

### Liveness Properties (◇P)
```tla
\* Eventually becomes true under conditions
THEOREM LivenessProperty ==
    Spec => (Condition ~> Property)
```

### Invariant Properties
```tla
\* Never violated throughout execution
INVARIANT InvariantProperty ==
    Property
```

These lemmas form the theoretical foundation for the Alpenglow protocol and should be implemented as formal properties and theorems in the TLA+ specification to verify correctness.