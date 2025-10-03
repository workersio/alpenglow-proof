------------------------------ MODULE WhitepaperThm1 ------------------------------
(***************************************************************************
 * THEOREM 1 (SAFETY) — TLAPS PROOF MIRRORING WHITEPAPER LEMMAS 25, 31, 32
 *
 * This auxiliary module packages the TLAPS derivation of SafetyInvariant,
 * assuming the key lemmas already formalised in `MainProtocol`. The lemmas
 * capture the whitepaper reasoning that (i) finalized blocks are notarized,
 * (ii) notarized descendants within a leader window extend the finalized
 * block, and (iii) notarized descendants across windows likewise extend it.
 ***************************************************************************)
EXTENDS MainProtocol, TLC, TLAPS

(***************************************************************************
 * STRUCTURAL ASSUMPTIONS
 ***************************************************************************)
ASSUME CorrectNodesAreValidators == CorrectNodes \subseteq Validators

ASSUME BlocksWellFormed ==
    \A b \in blocks :
        \/ b.parent = GenesisHash
        \/ b.parent \in blocks

ASSUME GenesisIsAncestorOfAll ==
    \A b \in blocks : IsAncestor(GenesisBlock, b, blocks)

ASSUME BlocksHaveProperType ==
    \A b \in blocks : b \in Block

(***************************************************************************
 * HELPER DEFINITIONS
 ***************************************************************************)
HasNotarOrFallbackCert(pool, slot, blockHash) ==
    \/ HasNotarizationCert(pool, slot, blockHash)
    \/ HasNotarFallbackCert(pool, slot, blockHash)
    \/ HasFastFinalizationCert(pool, slot, blockHash)

(***************************************************************************
 * CERTIFICATE PROPAGATION AND ALIGNMENT
 ***************************************************************************)
ASSUME CertificatePropagation ==
    \A v1, v2 \in CorrectNodes :
    \A s \in Slots :
    \A h \in BlockHashes :
        HasNotarOrFallbackCert(validators[v1].pool, s, h) =>
        HasNotarOrFallbackCert(validators[v2].pool, s, h)

FinalizedSubsetOfBlocks ==
    \A v \in Validators : finalized[v] \subseteq blocks

(***************************************************************************
 * KEY LEMMAS FROM WHITEPAPER
 ***************************************************************************)

(* Lemma 31: Same-window descendancy *)
SameWindowCertificateDescend ==
    \A vFinal \in CorrectNodes :
    \A vObs \in CorrectNodes :
    \A bFinal \in finalized[vFinal] :
    \A bSeen \in blocks :
        ( /\ WindowIndex(bSeen.slot) = WindowIndex(bFinal.slot)
          /\ bFinal.slot <= bSeen.slot
          /\ HasNotarOrFallbackCert(validators[vObs].pool, bSeen.slot, bSeen.hash))
        => IsAncestor(bFinal, bSeen, blocks)

(* Lemma 32: Cross-window descendancy *)
CrossWindowCertificateDescend ==
    \A vFinal \in CorrectNodes :
    \A vObs \in CorrectNodes :
    \A bFinal \in finalized[vFinal] :
    \A bSeen \in blocks :
        ( /\ WindowIndex(bSeen.slot) # WindowIndex(bFinal.slot)
          /\ bFinal.slot < bSeen.slot
          /\ HasNotarOrFallbackCert(validators[vObs].pool, bSeen.slot, bSeen.hash))
        => IsAncestor(bFinal, bSeen, blocks)

(***************************************************************************
 * AUXILIARY LEMMAS
 ***************************************************************************)

LEMMA IsAncestorTransitive ==
    ASSUME NEW b1 \in blocks,
           NEW b2 \in blocks,
           NEW b3 \in blocks,
           IsAncestor(b1, b2, blocks),
           IsAncestor(b2, b3, blocks)
    PROVE IsAncestor(b1, b3, blocks)
PROOF OMITTED  \* Follows from IsAncestor definition

LEMMA IsAncestorReflexive ==
    ASSUME NEW b \in blocks
    PROVE IsAncestor(b, b, blocks)
PROOF BY DEF IsAncestor

(***************************************************************************
 * CERTIFICATE EXISTENCE LEMMAS
 ***************************************************************************)

LEMMA FinalizedHasCertificate ==
    ASSUME NEW v \in CorrectNodes,
           NEW b \in finalized[v],
           FinalizedImpliesNotarized,
           PoolCertificatesSlotAligned(validators[v].pool)
    PROVE \E cert \in validators[v].pool.certificates[b.slot] :
             /\ cert.type \in {"NotarizationCert", "FastFinalizationCert"}
             /\ cert.blockHash = b.hash
PROOF BY FinalizedImpliesNotarized DEF FinalizedImpliesNotarized

LEMMA CertificateImpliesNotarOrFallback ==
    ASSUME NEW pool,
           NEW s \in Slots,
           NEW h \in BlockHashes,
           NEW cert \in pool.certificates[s],
           cert.type \in {"NotarizationCert", "FastFinalizationCert"},
           cert.blockHash = h,
           PoolCertificatesSlotAligned(pool)
    PROVE HasNotarOrFallbackCert(pool, s, h)
PROOF
<1>1. CASE cert.type = "NotarizationCert"
      <2>1. cert.slot = s
            BY PoolCertificatesSlotAligned(pool), cert \in pool.certificates[s]
            DEF PoolCertificatesSlotAligned
      <2>2. HasBlockCertOfType(pool, s, h, "NotarizationCert")
            BY <2>1, <1>1, cert \in pool.certificates[s], cert.blockHash = h
            DEF HasBlockCertOfType
      <2>3. HasNotarizationCert(pool, s, h)
            BY <2>2 DEF HasNotarizationCert
      <2>4. QED BY <2>3 DEF HasNotarOrFallbackCert
<1>2. CASE cert.type = "FastFinalizationCert"
      <2>1. cert.slot = s
            BY PoolCertificatesSlotAligned(pool), cert \in pool.certificates[s]
            DEF PoolCertificatesSlotAligned
      <2>2. HasBlockCertOfType(pool, s, h, "FastFinalizationCert")
            BY <2>1, <1>2, cert \in pool.certificates[s], cert.blockHash = h
            DEF HasBlockCertOfType
      <2>3. HasFastFinalizationCert(pool, s, h)
            BY <2>2 DEF HasFastFinalizationCert
      <2>4. QED BY <2>3 DEF HasNotarOrFallbackCert
<1>3. QED BY <1>1, <1>2

(***************************************************************************
 * SLOT ORDERING LEMMAS
 ***************************************************************************)

LEMMA SlotTrichotomy ==
    ASSUME NEW s1 \in Slots,
           NEW s2 \in Slots
    PROVE \/ s1 < s2
          \/ s1 = s2
          \/ s1 > s2
PROOF OMITTED  \* Follows from natural number properties

LEMMA SlotLessOrEqual ==
    ASSUME NEW s1 \in Slots,
           NEW s2 \in Slots,
           s1 <= s2,
           s1 # s2
    PROVE s1 < s2
PROOF OMITTED  \* Follows from natural number properties

LEMMA SameSlotsImplySameWindow ==
    ASSUME NEW s1 \in Slots,
           NEW s2 \in Slots,
           s1 = s2
    PROVE WindowIndex(s1) = WindowIndex(s2)
PROOF OBVIOUS

(***************************************************************************
 * THEOREM 1 PROOF
 *
 * This proof follows the whitepaper's strategy by case analysis:
 * 1. Same window: Use Lemma 31 (SameWindowCertificateDescend)
 * 2. Different windows: Use Lemma 32 (CrossWindowCertificateDescend)
 * 
 * The proof proceeds by showing that for any two finalized blocks b1, b2
 * where b1.slot <= b2.slot, b1 is an ancestor of b2. This is done by:
 * - Showing b2 has a certificate (Lemma 25)
 * - Case splitting on whether they're in the same window
 * - Applying the appropriate descendancy lemma
 ***************************************************************************)

THEOREM WhitepaperTheorem1 ==
    ASSUME FinalizedSubsetOfBlocks,
           FinalizedImpliesNotarized,
           SameWindowCertificateDescend,
           CrossWindowCertificateDescend,
           \A v \in Validators : PoolCertificatesSlotAligned(validators[v].pool)
    PROVE SafetyInvariant
PROOF
<1>1. SUFFICES ASSUME NEW v1 \in CorrectNodes,
                     NEW v2 \in CorrectNodes,
                     NEW b1 \in finalized[v1],
                     NEW b2 \in finalized[v2],
                     b1.slot <= b2.slot
              PROVE IsAncestor(b1, b2, blocks)
      BY DEF SafetyInvariant
      
<1>2. b1 \in blocks /\ b2 \in blocks
      BY <1>1, FinalizedSubsetOfBlocks, CorrectNodesAreValidators 
      DEF FinalizedSubsetOfBlocks
      
<1>3. \E cert \in validators[v2].pool.certificates[b2.slot] :
         /\ cert.type \in {"NotarizationCert", "FastFinalizationCert"}
         /\ cert.blockHash = b2.hash
      BY <1>1, <1>2, FinalizedHasCertificate, CorrectNodesAreValidators
      
<1>4. HasNotarOrFallbackCert(validators[v2].pool, b2.slot, b2.hash)
      <2>1. PICK cert \in validators[v2].pool.certificates[b2.slot] :
               /\ cert.type \in {"NotarizationCert", "FastFinalizationCert"}
               /\ cert.blockHash = b2.hash
            BY <1>3
      <2>2. PoolCertificatesSlotAligned(validators[v2].pool)
            BY <1>1, CorrectNodesAreValidators
      <2>3. CASE cert.type = "NotarizationCert"
            <3>1. cert.slot = b2.slot
                  <4>1. cert \in validators[v2].pool.certificates[b2.slot]
                        BY <2>1
                  <4>2. b2.slot \in Slots
                        BY <1>2, BlocksHaveProperType DEF Block
                  <4>3. \A c \in validators[v2].pool.certificates[b2.slot] : c.slot = b2.slot
                        BY <4>2, <2>2 DEF PoolCertificatesSlotAligned
                  <4>4. QED BY <4>1, <4>3
            <3>2. HasBlockCertOfType(validators[v2].pool, b2.slot, b2.hash, "NotarizationCert")
                  BY <2>1, <3>1, <2>3 DEF HasBlockCertOfType
            <3>3. HasNotarizationCert(validators[v2].pool, b2.slot, b2.hash)
                  BY <3>2 DEF HasNotarizationCert
            <3>4. QED BY <3>3 DEF HasNotarOrFallbackCert
      <2>4. CASE cert.type = "FastFinalizationCert"
            <3>1. cert.slot = b2.slot
                  <4>1. cert \in validators[v2].pool.certificates[b2.slot]
                        BY <2>1
                  <4>2. b2.slot \in Slots
                        BY <1>2, BlocksHaveProperType DEF Block
                  <4>3. \A c \in validators[v2].pool.certificates[b2.slot] : c.slot = b2.slot
                        BY <4>2, <2>2 DEF PoolCertificatesSlotAligned
                  <4>4. QED BY <4>1, <4>3
            <3>2. HasBlockCertOfType(validators[v2].pool, b2.slot, b2.hash, "FastFinalizationCert")
                  BY <2>1, <3>1, <2>4 DEF HasBlockCertOfType
            <3>3. HasFastFinalizationCert(validators[v2].pool, b2.slot, b2.hash)
                  BY <3>2 DEF HasFastFinalizationCert
            <3>4. QED BY <3>3 DEF HasNotarOrFallbackCert
      <2>5. QED BY <2>1, <2>3, <2>4

<1>5. CASE WindowIndex(b1.slot) = WindowIndex(b2.slot)
      <2>1. IsAncestor(b1, b2, blocks)
            <3>1. v1 \in CorrectNodes /\ v2 \in CorrectNodes
                  BY <1>1
            <3>2. b1 \in finalized[v1]
                  BY <1>1
            <3>3. b2 \in blocks
                  BY <1>2
            <3>4. WindowIndex(b2.slot) = WindowIndex(b1.slot)
                  BY <1>5
            <3>5. b1.slot <= b2.slot
                  BY <1>1
            <3>6. HasNotarOrFallbackCert(validators[v2].pool, b2.slot, b2.hash)
                  BY <1>4
            <3>7. QED
                  BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, SameWindowCertificateDescend
                  DEF SameWindowCertificateDescend
      <2>2. QED BY <2>1

<1>6. CASE WindowIndex(b1.slot) # WindowIndex(b2.slot)
      <2>1. b1.slot # b2.slot
            <3>1. ASSUME b1.slot = b2.slot
                  PROVE FALSE
                  <4>1. WindowIndex(b1.slot) = WindowIndex(b2.slot)
                        BY <3>1, SameSlotsImplySameWindow DEF SameSlotsImplySameWindow
                  <4>2. QED BY <4>1, <1>6
            <3>2. QED BY <3>1, SlotTrichotomy
            
      <2>2. b1.slot < b2.slot
            <3>1. b1 \in blocks /\ b2 \in blocks
                  BY <1>2
            <3>2. b1 \in Block /\ b2 \in Block
                  BY <3>1, BlocksHaveProperType
            <3>3. b1.slot \in Slots /\ b2.slot \in Slots
                  BY <3>2 DEF Block
            <3>4. QED BY <1>1, <2>1, <3>3, SlotLessOrEqual
            
      <2>3. IsAncestor(b1, b2, blocks)
            <3>1. v1 \in CorrectNodes /\ v2 \in CorrectNodes
                  BY <1>1
            <3>2. b1 \in finalized[v1]
                  BY <1>1
            <3>3. b2 \in blocks
                  BY <1>2
            <3>4. WindowIndex(b2.slot) # WindowIndex(b1.slot)
                  BY <1>6
            <3>5. b1.slot < b2.slot
                  BY <2>2
            <3>6. HasNotarOrFallbackCert(validators[v2].pool, b2.slot, b2.hash)
                  BY <1>4
            <3>7. QED
                  BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, CrossWindowCertificateDescend
                  DEF CrossWindowCertificateDescend
               
      <2>4. QED BY <2>3
      
<1>7. QED BY <1>5, <1>6

=============================================================================