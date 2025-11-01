---------------------------- MODULE VoteStorage ----------------------------

EXTENDS Naturals, FiniteSets, Messages, Blocks, Certificates

(*
  Vote multiplicities follow Pool storage rules: 
  - first notarization or skip vote; up to 3 notar-fallback; first skip-fallback; first finalization. 
  Source: §2.5, Def. 12, p.20.
*)
MaxInitialVotes == 1  
MaxNotarFallbacks == 3 
MaxSkipFallbacks == 1  
MaxFinalVotes == 1     

(*
  NotarTypes = block-bound certificate kinds. 
  Source: §2.4, Tables 5–6, p.20 (Fast-Finalization, Notarization, Notar-Fallback).
*)
NotarTypes == {"NotarizationCert", "NotarFallbackCert", "FastFinalizationCert"}

(*
  Pool state mirrors the white paper’s “Pool”: votes are bucketed by slot+validator; 
  certificates are bucketed by slot. 
  Source: §2.5, Defs. 12–13, pp.20–21.
*)
PoolState == [
    votes: [Slots -> [Validators -> SUBSET Vote]],  \* Votes by slot and validator
    certificates: [Slots -> SUBSET Certificate]      \* Certificates by slot
]

(*
  Empty Pool initialization. 
  Source: §2.5, pp.20–21.
*)
InitPool == [
    votes |-> [s \in Slots |-> [v \in Validators |-> {}]],
    certificates |-> [s \in Slots |-> {}]
]

(*
  Vote admission guards implement Def. 12 multiplicities and Lemma 20
  (exactly one initial vote per slot per validator). 
  Sources: §2.5, Def. 12; §2.9, Lemma 20, pp.20, 28.
*)
CanStoreVote(pool, vote) ==
    LET 
        slot == vote.slot
        validator == vote.validator
        existingVotes == pool.votes[slot][validator]
    IN
        CASE vote.type = "NotarVote" ->
            ~\E v \in existingVotes : IsInitialVote(v)

        [] vote.type = "SkipVote" ->
            ~\E v \in existingVotes : IsInitialVote(v)
            
        [] vote.type = "NotarFallbackVote" ->
            Cardinality({v \in existingVotes : v.type = "NotarFallbackVote"}) < MaxNotarFallbacks
            
        [] vote.type = "SkipFallbackVote" ->
            Cardinality({v \in existingVotes : v.type = "SkipFallbackVote"}) < MaxSkipFallbacks
            
        [] vote.type = "FinalVote" ->
            Cardinality({v \in existingVotes : v.type = "FinalVote"}) < MaxFinalVotes
            
        [] OTHER -> FALSE

(*
  Store only valid and admissible votes. Type/validity comes from Messages module. 
  Sources: §2.4 (Table 5); §2.5 (Def. 12).
*)
StoreVote(pool, vote) ==
    IF IsValidVote(vote) /\ CanStoreVote(pool, vote) THEN
        LET 
            slot == vote.slot
            validator == vote.validator
            existingVotes == pool.votes[slot][validator]
        IN
            [pool EXCEPT !.votes[slot][validator] = existingVotes \cup {vote}]
    ELSE
        pool

(*
  Certificate admission enforces one-per-type per slot (or per block for notar-type),
  and that all notar-type certs in a slot refer to the same block hash. Rejects a second Skip/Finalization per slot.
  Also requires “skip vs. block-cert” mutual exclusion as per safety lemmas once finalization occurs. 
  Sources: §2.5, Def. 13 (single certificate per type per block/slot), p.21; 
           §2.9 Lemmas 21 & 26 (exclusion with skip when finalized), pp.28–30.
*)
CanStoreCertificate(pool, cert) ==
    LET 
        slot == cert.slot
        existing == pool.certificates[slot]
        newset == existing \cup {cert}
    IN
        /\ SkipVsBlockCertExclusion(newset)
        /\ CASE cert.type = "SkipCert" ->
                 ~\E c \in existing : c.type = "SkipCert"

           [] cert.type = "FinalizationCert" ->
                 ~\E c \in existing : c.type = "FinalizationCert"

           [] cert.type \in NotarTypes ->
                 /\ ~\E c \in existing : c.type = cert.type /\ c.blockHash = cert.blockHash
                 /\ (\A c \in existing : c.type \in NotarTypes => c.blockHash = cert.blockHash)

           [] OTHER -> FALSE

(*
  Store only well-formed and valid certificates. Generation/broadcast is specified in §2.5, Def. 13. 
  Note: a FinalizationCert may arrive before the NotarizationCert due to network reordering; 
  we store it and rely on Votor to finalize only after notarization is known (Alg. 2 line 19).
  Sources: §2.5, Def. 13; §2.4, Table 6; §2.6, Alg. 2, p.25.
*)
StoreCertificate(pool, cert) ==
    IF CanStoreCertificate(pool, cert)
       /\ IsValidCertificate(cert)
       /\ CertificateWellFormed(cert)
    THEN
        LET base == [pool EXCEPT !.certificates[cert.slot] = 
                           pool.certificates[cert.slot] \cup {cert}]
            implied ==
                IF cert.type = "FastFinalizationCert" THEN
                    { CreateNotarizationCert(cert.votes, cert.slot, cert.blockHash),
                      CreateNotarFallbackCert(cert.votes, cert.slot, cert.blockHash) }
                ELSE {}
            RECURSIVE StoreAll(_,_)
            StoreAll(p, cs) ==
                IF cs = {} THEN p
                ELSE LET c == CHOOSE x \in cs : TRUE
                         ok == CanStoreCertificate(p, c) /\ IsValidCertificate(c) /\ CertificateWellFormed(c)
                         pNext == IF ok THEN [p EXCEPT !.certificates[c.slot] = p.certificates[c.slot] \cup {c}] ELSE p
                     IN StoreAll(pNext, cs \ {c})
        IN StoreAll(base, implied)
    ELSE
        pool

(*
  Utility: maximum of a finite Nat set. Standard. 
*)
MaxNat(S) == IF S = {} THEN 0 ELSE CHOOSE x \in S : \A y \in S : x >= y

(*
  Slot aggregations. Votes counted once per validator per slot (Def. 16 “only once per slot”). 
  Sources: §2.5, Def. 12; §2.5, Def. 16, p.21.
*)
GetVotesForSlot(pool, slot) ==
    UNION { pool.votes[slot][v] : v \in DOMAIN pool.votes[slot] }

GetVotesForSlotTypeOK(pool, slot) ==
    GetVotesForSlot(pool, slot) \subseteq Vote

(*
  Stake tallies for thresholds in SafeToNotar / SafeToSkip. 
  NotarStake uses only initial notar votes for block b; SkipStake counts initial skip voters. 
  Sources: §2.5, Def. 16 (formulas), pp.21–22; §2.4, Table 6 (thresholds 60/80).
*)
NotarStake(pool, slot, blockHash) ==
    LET votes == GetVotesForSlot(pool, slot)
        notarVotes == {v \in votes :
            /\ IsInitialNotarVote(v)
            /\ v.slot = slot
            /\ v.blockHash = blockHash}
    IN StakeFromVotes(notarVotes)

SkipStake(pool, slot) ==
    LET votes == GetVotesForSlot(pool, slot)
        skipVotes == {v \in votes : v.type = "SkipVote"}
        validators == {v.validator : v \in skipVotes}
    IN CalculateStake(validators)

(*
  Total/Max notar stake and “non-max” term used in SafeToSkip. 
  Source: §2.5, Def. 16, p.22.
*)
TotalNotarStake(pool, slot) ==
    LET votes == GetVotesForSlot(pool, slot)
        notarVotes == {v \in votes : IsInitialNotarVote(v)}
    IN StakeFromVotes(notarVotes)

MaxNotarStake(pool, slot) ==
    LET votes == GetVotesForSlot(pool, slot)
        notarVotes == {v \in votes : IsInitialNotarVote(v)}
        blocks == {v.blockHash : v \in notarVotes}
    IN IF blocks = {} THEN 0
       ELSE LET stakes == {NotarStake(pool, slot, b) : b \in blocks}
            IN MaxNat(stakes)

NonMaxNotarStake(pool, slot) ==
    TotalNotarStake(pool, slot) - MaxNotarStake(pool, slot)

(*
  Local certificate construction mirrors Table 6:
  - FastFinalizationCert: NotarVote Σ≥80% (fast path)
  - NotarizationCert: NotarVote Σ≥60%
  - NotarFallbackCert: NotarVote or NotarFallbackVote Σ≥60%
  - SkipCert: SkipVote or SkipFallbackVote Σ≥60% (only if no block cert emerges)
  - FinalizationCert: FinalVote Σ≥60%, and only meaningful with notarization known (Alg. 2, line 19).
  Sources: §2.4, Table 6, p.20; §2.6, Alg. 1–2, pp.24–25.
*)
GenerateCertificate(pool, slot) ==
    LET
        votes == GetVotesForSlot(pool, slot)
        candidateBlocks == {v.blockHash : v \in {vt \in votes : vt.type \in {"NotarVote", "NotarFallbackVote"}}}
        BlockCertFor(block) ==
            IF CanCreateFastFinalizationCert(votes, slot, block) THEN
                {
                    CreateFastFinalizationCert(votes, slot, block),
                    CreateNotarizationCert(votes, slot, block),
                    CreateNotarFallbackCert(votes, slot, block)
                }
            ELSE IF CanCreateNotarizationCert(votes, slot, block) THEN
                {
                    CreateNotarizationCert(votes, slot, block),
                    CreateNotarFallbackCert(votes, slot, block)
                }
            ELSE IF CanCreateNotarFallbackCert(votes, slot, block) THEN
                {CreateNotarFallbackCert(votes, slot, block)}
            ELSE {}
        blockCerts ==
            UNION {BlockCertFor(block) : block \in candidateBlocks}
        skipCert == IF (blockCerts = {}) /\ CanCreateSkipCert(votes, slot)
                     THEN {CreateSkipCert(votes, slot)}
                     ELSE {}
        hasNotarNow == \E c \in blockCerts : c.type = "NotarizationCert"
        hasNotarStored == \E c \in pool.certificates[slot] : c.type = "NotarizationCert"
        finalCert == IF CanCreateFinalizationCert(votes, slot) /\ (hasNotarNow \/ hasNotarStored)
                      THEN {CreateFinalizationCert(votes, slot)}
                      ELSE {}
    IN blockCerts \cup skipCert \cup finalCert

(*
  Certificate presence helpers used by event predicates (§2.5, Def. 15).
*)
HasBlockCertOfType(pool, slot, blockHash, certType) ==
    \E cert \in pool.certificates[slot] :
        /\ cert.type = certType
        /\ cert.blockHash = blockHash
        /\ cert.slot = slot

\* Wrappers for clarity
HasNotarizationCert(pool, slot, blockHash) ==
    HasBlockCertOfType(pool, slot, blockHash, "NotarizationCert")

HasNotarFallbackCert(pool, slot, blockHash) ==
    HasBlockCertOfType(pool, slot, blockHash, "NotarFallbackCert")

HasSlotCertOfType(pool, slot, certType) ==
    \E cert \in pool.certificates[slot] :
        /\ cert.type = certType
        /\ cert.slot = slot

HasSkipCert(pool, slot) ==
    HasSlotCertOfType(pool, slot, "SkipCert")

HasFastFinalizationCert(pool, slot, blockHash) ==
    HasBlockCertOfType(pool, slot, blockHash, "FastFinalizationCert")

HasFinalizationCert(pool, slot) ==
    HasSlotCertOfType(pool, slot, "FinalizationCert")

(*
  Slow finalization requires both FinalizationCert and notarized block for the slot. 
  Source: §2.5, Def. 14, p.21.
*)
CanFinalizeSlow(pool, slot, blockHash) ==
    /\ HasFinalizationCert(pool, slot)
    /\ HasNotarizationCert(pool, slot, blockHash)

(*
  Emits BlockNotarized when notarization certificate for (slot,block). 
  Source: §2.5, Def. 15, p.21.
*)
ShouldEmitBlockNotarized(pool, slot, blockHash) ==
    HasNotarizationCert(pool, slot, blockHash)

(*
  Emits ParentReady for first slot of a window when parent is notarized or notar-fallback,
  and all intermediate slots have skip certs. 
  Source: §2.5, Def. 15, p.21.
*)
ShouldEmitParentReady(pool, slot, parentHash, parentSlot) ==
    /\ IsFirstSlotOfWindow(slot)
    /\ parentSlot < slot
    /\ parentSlot \in Slots
    /\ (HasNotarizationCert(pool, parentSlot, parentHash) \/
        HasNotarFallbackCert(pool, parentSlot, parentHash))
    /\ \A s \in (parentSlot+1)..(slot-1) : HasSkipCert(pool, s)

(*
  For SafeToNotar in non-first slots require notar-fallback of the parent (§2.5, Def. 16). 
  First slot needs no parent fallback precondition. pp.21–22.
*)
ParentFallbackReady(pool, slot, parentSlot, parentHash) ==
    IF IsFirstSlotOfWindow(slot)
    THEN TRUE
    ELSE /\ parentSlot \in Slots
         /\ parentSlot < slot
         /\ HasNotarFallbackCert(pool, parentSlot, parentHash)

(*
  SafeToNotar thresholds:
   notar(b) ≥ 40  OR  (skip(s)+notar(b) ≥ 60 AND notar(b) ≥ 20).
  “alreadyVoted /\ ~votedForBlock” follows Alg. 1–2 guards.
  DefaultThreshold is 60% per Table 6. 
  Sources: §2.5, Def. 16, pp.21–22; §2.6, Alg. 1–2, pp.24–25.
*)
CanEmitSafeToNotar(pool, slot, blockHash, parentSlot, parentHash, alreadyVoted, votedForBlock) ==
    /\ alreadyVoted
    /\ ~votedForBlock
    /\ ParentFallbackReady(pool, slot, parentSlot, parentHash)
    /\ LET notar == NotarStake(pool, slot, blockHash)
           skip == SkipStake(pool, slot)
       IN (MeetsThreshold(notar, 40)
           \/ (MeetsThreshold(skip + notar, DefaultThreshold) /\ MeetsThreshold(notar, 20)))

(*
  SafeToSkip threshold: skip(s) + Σ_b notar(b) − max_b notar(b) ≥ 40.
  “alreadyVoted /\ ~votedSkip” follows Alg. 1–2 guards. 
  Source: §2.5, Def. 16, p.22.
*)
CanEmitSafeToSkip(pool, slot, alreadyVoted, votedSkip) ==
    /\ alreadyVoted
    /\ ~votedSkip
    /\ LET skip == SkipStake(pool, slot)
           nonMaxNotar == NonMaxNotarStake(pool, slot)
       IN MeetsThreshold(skip + nonMaxNotar, 40)

(*
  Structural well-typedness of Pool state. 
  Source: §2.5, pp.20–21.
*)
PoolTypeOK(pool) ==
    /\ DOMAIN pool.votes = Slots
    /\ \A s \in Slots : DOMAIN pool.votes[s] = Validators
    /\ \A s \in Slots : \A v \in Validators : pool.votes[s][v] \subseteq Vote
    /\ DOMAIN pool.certificates = Slots
    /\ \A s \in Slots : pool.certificates[s] \subseteq Certificate

(*
  Cross-checks that stored votes are aligned with their slot and validator. 
  Justification: votes are stored per slot+validator (Def. 12).
*)
PoolVotesSlotValidatorAligned(pool) ==
    \A s \in Slots : \A v \in Validators :
        \A vt \in pool.votes[s][v] : vt.slot = s /\ vt.validator = v

(*
  Certificate slot alignment. 
*)
PoolCertificatesSlotAligned(pool) ==
    \A s \in Slots : \A c \in pool.certificates[s] : c.slot = s

BucketSlotConsistency(pool) == PoolCertificatesSlotAligned(pool)

(*
  Vote multiplicities per Def. 12. 
  Source: §2.5, Def. 12, p.20.
*)
MultiplicityRulesRespected(pool) ==
    \A s \in Slots, v \in Validators :
        LET votes == pool.votes[s][v]
        IN /\ Cardinality({vt \in votes : IsInitialVote(vt)}) <= MaxInitialVotes
           /\ Cardinality({vt \in votes : vt.type = "NotarFallbackVote"}) <= MaxNotarFallbacks
           /\ Cardinality({vt \in votes : vt.type = "SkipFallbackVote"}) <= MaxSkipFallbacks
           /\ Cardinality({vt \in votes : vt.type = "FinalVote"}) <= MaxFinalVotes

(*
  REMOVED (unsound): a constraint forcing each validator’s notar-fallback votes in a slot
  to target a single block. The white paper allows byzantine equivocation; Pool stores “received” votes. 
  Enforcing per-validator single block here would wrongly exclude valid byzantine traces and
  contradict §2.9’s model. Use stake de-duplication instead. 
  Source: §2.9, model + Lemmas, pp.28–32.
*)

(*
  Skip-fallback after an initial notar vote only. Matches Alg. 1 line 21 and its guard (~votedSkip).
  Source: §2.6, Alg. 1–2, p.24; §2.5, Def. 16, p.22.
*)
SkipFallbackAfterInitialNotarAt(pool, s, v) ==
    LET votes == pool.votes[s][v]
    IN (\E vt \in votes : vt.type = "SkipFallbackVote")
            => (\E vn \in votes : IsInitialNotarVote(vn))

(*
  Certificate uniqueness and “single block per slot” for notar-type certs. 
  Source: §2.5, Def. 13; §2.9, Lemmas 23–24, pp.20–21, 29.
*)
CertificateUniqueness(pool) ==
    \A s \in Slots :
      /\ \A t \in {"SkipCert", "FinalizationCert"} :
            Cardinality({c \in pool.certificates[s] : c.type = t}) <= 1
      /\ \A t \in NotarTypes :
            \A b \in BlockHashes :
                Cardinality({c \in pool.certificates[s] : c.type = t /\ c.blockHash = b}) <= 1
      /\ LET notarBs == {c.blockHash : c \in {d \in pool.certificates[s] : d.type \in NotarTypes}}
         IN Cardinality(notarBs) <= 1

(*
  Well-formedness (signatures, hashes, etc.). 
  Sources: §1.6; §2.4.
*)
CertificatesWellFormed(pool) ==
    \A s \in Slots : AllCertificatesWellFormed(pool.certificates[s])

(*
  Logical dependency used by Votor’s tryFinal: slow finalization is only issued after a notarization
  has been observed (Alg. 2 line 19). Not asserted as a global invariant due to message reordering. 
  Sources: §2.5, Def. 14; §2.6, Alg. 2, p.25.
*)
FinalizationImpliesNotarizationPresent(pool, s) ==
    (\E c \in pool.certificates[s] : c.type = "FinalizationCert")
        => (\E n \in pool.certificates[s] : n.type = "NotarizationCert")

(*
  Deduplication: “TotalNotarStake” equals stake of unique initial notar voters. 
  Ensures a validator’s weight is counted once per slot as in Def. 16. 
  Source: §2.5, Def. 16, p.21.
*)
TotalNotarStakeEqualsUniqueNotarVoters(pool, s) ==
    LET votes == GetVotesForSlot(pool, s)
        nv == {vt \in votes : IsInitialNotarVote(vt)}
        uniqVals == {vt.validator : vt \in nv}
    IN TotalNotarStake(pool, s) = CalculateStake(uniqVals)

=============================================================================
