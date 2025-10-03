----------------------------- MODULE LivenessProofs -----------------------------
(***************************************************************************
 * LIVENESS COMPOSITION THEOREM (WHITEPAPER LEMMAS 7–42)
 *
 * This module packages the high-level liveness conclusions that follow from
 * the Alpenglow lemmas enumerated in `specs/liveness-proof.md`.  We reuse the
 * formalised protocol state found in `MainProtocol` and derive the three
 * conclusions highlighted in the document:
 *   1. eventual global finalisation (slow path, ≥60% honest stake)
 *   2. fast-path finalisation within δ80 once 80% availability holds
 *   3. a min{δ80, 2·δ60} bound on finalisation time for post-GST blocks
 *
 * The statements connect previously modelled invariants/temporal properties
 * with auxiliary definitions that make the whitepaper text explicit.  Proofs
 * reference the constituent lemmas and invariants used in the implementation;
 * deeper temporal reasoning steps are left as proof obligations for TLAPS,
 * mirroring the style in `ResilienceProofs.tla`.
 ***************************************************************************)

EXTENDS MainProtocol, TLC, TLAPS

(***************************************************************************
 * AUXILIARY PREDICATES USED IN THE THEOREM STATEMENT
 ***************************************************************************)

BlockFinalizedEverywhere(s, h) ==
    \A v \in CorrectNodes :
        \E b \in finalized[v] : b.slot = s /\ b.hash = h

SomeBlockFinalizedEverywhere ==
    \E s \in 1..MaxSlot : \E h \in BlockHashes : BlockFinalizedEverywhere(s, h)

FastAvailabilityImpliesFastCert ==
    \A s \in 1..MaxSlot :
    \A h \in BlockHashes :
        (ExistsBlockAt(s, h) /\ Avail80Now(s, h)) => FastCertExistsAt(s, h)

BoundedFastDeadline(s, h) ==
    LET st == EffectiveStart(avail80Start[s][h])
    IN (st = 0) \/ (time <= st + Delta80) \/ BlockHashFinalizedAt(s, h)

BoundedSlowDeadline(s, h) ==
    LET st == EffectiveStart(avail60Start[s][h])
    IN (st = 0) \/ (time <= st + (2 * Delta60)) \/ BlockHashFinalizedAt(s, h)

MinNat(x, y) == IF x <= y THEN x ELSE y

FinalizationWithinMinBound(s, h) ==
    LET fastStart == EffectiveStart(avail80Start[s][h])
        slowStart == EffectiveStart(avail60Start[s][h])
        fastDeadline == fastStart + Delta80
        slowDeadline == slowStart + (2 * Delta60)
        bound == MinNat(fastDeadline, slowDeadline)
    IN (fastStart # 0 /\ slowStart # 0 /\ time > bound)
        => BlockHashFinalizedAt(s, h)

(***************************************************************************
 * HELPER LEMMAS
 ***************************************************************************)

LEMMA FirstSlotBelongsToWindow ==
    ASSUME NEW s \in 1..MaxSlot,
           IsFirstSlotOfWindow(s)
    PROVE s \in WindowSlots(s)
PROOF
<1>1. s = FirstSlotOfWindow(s)
      BY DEF IsFirstSlotOfWindow
<1>2. s >= 1 /\ s \in Slots
      OBVIOUS
<1>3. s >= s /\ s < s + WindowSize
      OBVIOUS
<1>4. s \in {slot \in Slots : slot >= s /\ slot < s + WindowSize /\ slot >= 1}
      BY <1>2, <1>3
<1>5. QED BY <1>1, <1>4 DEF WindowSlots

LEMMA WindowFinalizedSlotImpliesGlobal ==
    ASSUME NEW s \in 1..MaxSlot,
           IsFirstSlotOfWindow(s),
           WindowFinalizedState(s),
           Invariant,
           CorrectNodes # {}
    PROVE \E h \in BlockHashes : BlockFinalizedEverywhere(s, h)
PROOF
<1>1. CorrectNodes # {}
      OBVIOUS
<1>1a. PICK v0 \in CorrectNodes : TRUE
      BY <1>1
<1>2. s \in WindowSlots(s)
      BY FirstSlotBelongsToWindow, IsFirstSlotOfWindow(s)
<1>3. v0 \in CorrectNodes
      BY <1>1a
<1>4. \E b0 \in blocks :
        /\ b0.slot = s
        /\ b0.leader = Leader(s)
        /\ b0 \in finalized[v0]
      BY WindowFinalizedState(s), <1>2, <1>3 DEF WindowFinalizedState
<1>5. PICK b0 \in blocks :
        /\ b0.slot = s
        /\ b0.leader = Leader(s)
        /\ b0 \in finalized[v0]
      BY <1>4
<1>6. ASSUME NEW v \in CorrectNodes
      PROVE \E b \in finalized[v] :
              /\ b.slot = s
              /\ b.hash = b0.hash
      <2>1. \E bv \in blocks :
              /\ bv.slot = s
              /\ bv.leader = Leader(s)
              /\ bv \in finalized[v]
            BY WindowFinalizedState(s), <1>2 DEF WindowFinalizedState
      <2>2. PICK bv \in blocks :
              /\ bv.slot = s
              /\ bv.leader = Leader(s)
              /\ bv \in finalized[v]
            BY <2>1
      <2>3. bv.hash = b0.hash
            BY Invariant, <2>2, <1>5 DEF Invariant, NoConflictingFinalization
      <2>4. \E b \in finalized[v] : b.slot = s /\ b.hash = b0.hash
            BY <2>2, <2>3
      <2>5. QED BY <2>4
<1>7. \A v \in CorrectNodes :
        \E b \in finalized[v] : b.slot = s /\ b.hash = b0.hash
      BY <1>6
<1>8. b0.hash \in BlockHashes
       BY Invariant, <1>5 DEF Invariant, AllBlocksValid, Block, IsValidBlock
<1>9. \E h \in BlockHashes : BlockFinalizedEverywhere(s, h)
       BY <1>7, <1>8 DEF BlockFinalizedEverywhere
<1>10. QED BY <1>9

LEMMA FastAvailabilityYieldsFastDeadline ==
    ASSUME NEW s \in 1..MaxSlot,
           NEW h \in BlockHashes,
           ExistsBlockAt(s, h),
           Avail80Now(s, h),
           FastAvailabilityImpliesFastCert,
           BoundedFinalization80
    PROVE /\ FastCertExistsAt(s, h)
          /\ BoundedFastDeadline(s, h)
PROOF
<1>1. FastCertExistsAt(s, h)
      BY DEF FastAvailabilityImpliesFastCert, ExistsBlockAt, Avail80Now
<1>2. BoundedFastDeadline(s, h)
      BY DEF BoundedFinalization80, BoundedFastDeadline
<1>3. QED BY <1>1, <1>2

LEMMA MinBoundFromFastAndSlow ==
    ASSUME NEW s \in 1..MaxSlot,
           NEW h \in BlockHashes,
           BoundedFinalization80,
           BoundedFinalization60
    PROVE FinalizationWithinMinBound(s, h)
PROOF
<1>1. SUFFICES ASSUME NEW fastStart,
                      NEW slowStart,
                      NEW fastDeadline,
                      NEW slowDeadline,
                      NEW bound,
                      fastStart = EffectiveStart(avail80Start[s][h]),
                      slowStart = EffectiveStart(avail60Start[s][h]),
                      fastDeadline = fastStart + Delta80,
                      slowDeadline = slowStart + (2 * Delta60),
                      bound = MinNat(fastDeadline, slowDeadline),
                      fastStart # 0,
                      slowStart # 0,
                      time > bound
               PROVE BlockHashFinalizedAt(s, h)
      BY DEF FinalizationWithinMinBound
<1>2. CASE fastDeadline <= slowDeadline
      <2>1. bound = fastDeadline
            BY <1>1, <1>2 DEF MinNat
      <2>2. time > fastDeadline
            BY <1>1, <2>1
      <2>3. time > fastStart + Delta80
            BY <1>1, <2>2
      <2>4. (fastStart = 0) \/ (time <= fastStart + Delta80) \/ BlockHashFinalizedAt(s, h)
            BY DEF BoundedFinalization80, BoundedFastDeadline, EffectiveStart
      <2>5. ~ (time <= fastStart + Delta80)
            BY <2>3
      <2>6. fastStart # 0
            BY <1>1
      <2>7. BlockHashFinalizedAt(s, h)
            BY <2>4, <2>5, <2>6
      <2>8. QED BY <2>7
<1>3. CASE fastDeadline > slowDeadline
      <2>1. bound = slowDeadline
            BY <1>1, <1>3 DEF MinNat
      <2>2. time > slowDeadline
            BY <1>1, <2>1
      <2>3. time > slowStart + (2 * Delta60)
            BY <1>1, <2>2
      <2>4. (slowStart = 0) \/ (time <= slowStart + (2 * Delta60)) \/ BlockHashFinalizedAt(s, h)
            BY DEF BoundedFinalization60, BoundedSlowDeadline, EffectiveStart
      <2>5. ~ (time <= slowStart + (2 * Delta60))
            BY <2>3
      <2>6. slowStart # 0
            BY <1>1
      <2>7. BlockHashFinalizedAt(s, h)
            BY <2>4, <2>5, <2>6
      <2>8. QED BY <2>7
<1>4. QED BY <1>2, <1>3

(***************************************************************************
 * MAIN LIVENESS THEOREM (Theorem 2 style statement)
 ***************************************************************************)

WindowProgressConclusion ==
    \A s \in 1..MaxSlot :
        (IsFirstSlotOfWindow(s) /\ Leader(s) \in CorrectNodes /\ NoTimeoutsBeforeGST(s) /\ time >= GST)
            ~> (\E h \in BlockHashes : BlockFinalizedEverywhere(s, h))

FastPathConclusion ==
    \A s \in 1..MaxSlot :
    \A h \in BlockHashes :
        (ExistsBlockAt(s, h) /\ Avail80Now(s, h))
            => (/\ FastCertExistsAt(s, h)
                 /\ BoundedFastDeadline(s, h))

SlowPathBoundConclusion ==
    \A s \in 1..MaxSlot :
    \A h \in BlockHashes : FinalizationWithinMinBound(s, h)

THEOREM AlpenglowMainLiveness ==
    ASSUME []Invariant,
           WindowFinalizationAll,
           FastAvailabilityImpliesFastCert,
           BoundedFinalization80,
           BoundedFinalization60,
           CorrectNodes # {}
    PROVE /\ WindowProgressConclusion
          /\ FastPathConclusion
          /\ SlowPathBoundConclusion
PROOF
<1>1. \A s \in 1..MaxSlot :
        (IsFirstSlotOfWindow(s) /\ WindowFinalizedState(s))
            => \E h \in BlockHashes : BlockFinalizedEverywhere(s, h)
      <2>1. ASSUME NEW s \in 1..MaxSlot,
                     IsFirstSlotOfWindow(s),
                     WindowFinalizedState(s)
              PROVE \E h \in BlockHashes : BlockFinalizedEverywhere(s, h)
            <3>1. Invariant
                  BY PTL DEF Invariant
            <3>2. QED BY WindowFinalizedSlotImpliesGlobal, <3>1
      <2>2. QED BY <2>1
<1>2. WindowProgressConclusion
      BY PTL DEF WindowProgressConclusion, WindowFinalizationAll, WindowFinalization
<1>3. FastPathConclusion
      <2>1. ASSUME NEW s \in 1..MaxSlot,
                     NEW h \in BlockHashes,
                     ExistsBlockAt(s, h),
                     Avail80Now(s, h)
              PROVE (/\ FastCertExistsAt(s, h)
                     /\ BoundedFastDeadline(s, h))
            <3>1. FastCertExistsAt(s, h)
                  BY DEF FastAvailabilityImpliesFastCert, ExistsBlockAt, Avail80Now
            <3>2. BoundedFastDeadline(s, h)
                  BY DEF BoundedFinalization80, BoundedFastDeadline
            <3>3. QED BY <3>1, <3>2
      <2>2. QED BY <2>1 DEF FastPathConclusion
<1>4. SlowPathBoundConclusion
      <2>1. ASSUME NEW s \in 1..MaxSlot,
                     NEW h \in BlockHashes
              PROVE FinalizationWithinMinBound(s, h)
            BY MinBoundFromFastAndSlow
      <2>2. QED BY <2>1 DEF SlowPathBoundConclusion
<1>5. QED BY <1>2, <1>3, <1>4

=============================================================================
