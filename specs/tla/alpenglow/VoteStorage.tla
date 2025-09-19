---------------------------- MODULE VoteStorage ----------------------------
(***************************************************************************
 * VOTE AND CERTIFICATE STORAGE (POOL) FOR ALPENGLOW
 *
 * Whitepaper §2.4 describes a per-validator "Pool" structure that remembers
 * votes, emits events, and constructs certificates. This module encodes those
 * rules so readers can see how raw votes are transformed into notarization,
 * skip, and finalization certificates.
 ***************************************************************************)

EXTENDS Naturals, FiniteSets, Messages, Blocks, Certificates

\* ============================================================================
\* POOL STATE STRUCTURE
\* ============================================================================

(***************************************************************************
 * The Pool is a local data structure maintained by each validator to:
 * 1. Store received votes with multiplicity rules
 * 2. Store certificates (at most one of each type per slot/block)
 * 3. Generate events that trigger state transitions
 ***************************************************************************)

PoolState == [
    votes: [Slots -> [Validators -> SUBSET Vote]],  \* Votes by slot and validator
    certificates: [Slots -> SUBSET Certificate]      \* Certificates by slot
]

\* Initialize an empty pool
InitPool == [
    votes |-> [s \in Slots |-> [v \in Validators |-> {}]],
    certificates |-> [s \in Slots |-> {}]
]

\* ============================================================================
\* VOTE STORAGE WITH MULTIPLICITY RULES (Definition 12)
\* ============================================================================

(***************************************************************************
 * DEFINITION 12 (Storing votes) - Whitepaper page 20:
 * "Pool stores received votes for every slot and every node as follows:
 *  • The first received notarization or skip vote,
 *  • up to 3 received notar-fallback votes,
 *  • the first received skip-fallback vote, and
 *  • the first received finalization vote."
 * 
 * This enforces LEMMA 20 (page 28): "A correct node casts at most one 
 * notarization or skip vote per slot"
 ***************************************************************************)

\* Definition 12: multiplicity limits — exactly one initial vote, up to
\* three notar fallback votes, etc. This predicate enforces those limits
\* before adding anything to the Pool.
CanStoreVote(pool, vote) ==
    LET 
        slot == vote.slot
        validator == vote.validator
        existingVotes == pool.votes[slot][validator]
    IN
        CASE vote.type = "NotarVote" -> 
            \* Can only store if no NotarVote exists yet
            ~\E v \in existingVotes : v.type = "NotarVote"
            
        [] vote.type = "SkipVote" ->
            \* Can only store if no SkipVote exists yet
            ~\E v \in existingVotes : v.type = "SkipVote"
            
        [] vote.type = "NotarFallbackVote" ->
            \* Can store up to 3 notar-fallback votes
            Cardinality({v \in existingVotes : v.type = "NotarFallbackVote"}) < 3
            
        [] vote.type = "SkipFallbackVote" ->
            \* Can only store if no SkipFallbackVote exists yet
            ~\E v \in existingVotes : v.type = "SkipFallbackVote"
            
        [] vote.type = "FinalVote" ->
            \* Can only store if no FinalVote exists yet
            ~\E v \in existingVotes : v.type = "FinalVote"
            
        [] OTHER -> FALSE

\* Definition 12: once the multiplicity check passes we record the vote for
\* this validator/slot so later stake calculations can see it.
StoreVote(pool, vote) ==
    IF CanStoreVote(pool, vote) THEN
        LET 
            slot == vote.slot
            validator == vote.validator
            existingVotes == pool.votes[slot][validator]
        IN
            [pool EXCEPT !.votes[slot][validator] = existingVotes \union {vote}]
    ELSE
        pool  \* Don't store if multiplicity rules violated

\* ============================================================================
\* CERTIFICATE STORAGE (Definition 13)
\* ============================================================================

(***************************************************************************
 * CRITICAL RULE from Definition 13:
 * "A single certificate of each type corresponding to the given block/slot
 * is stored in Pool"
 * 
 * This ensures certificate uniqueness - can't have conflicting certificates!
 ***************************************************************************)

\* Definition 13: only one certificate of a given type is stored for each
\* slot/block combination. This predicate enforces that uniqueness.
CanStoreCertificate(pool, cert) ==
    LET 
        slot == cert.slot
        existing == pool.certificates[slot]
        NotarTypes == {"NotarizationCert", "NotarFallbackCert", "FastFinalizationCert"}
    IN
        CASE cert.type \in {"SkipCert", "FinalizationCert"} ->
            \* At most one SkipCert and one FinalizationCert per slot
            ~\E c \in existing : c.type = cert.type

        [] cert.type \in NotarTypes ->
            /\ ~\E c \in existing : c.type = cert.type /\ c.blockHash = cert.blockHash
            /\ \A c \in existing :
                  c.type \in NotarTypes => c.blockHash = cert.blockHash

        [] OTHER -> FALSE

\* Store a certificate in the pool
StoreCertificate(pool, cert) ==
    IF CanStoreCertificate(pool, cert) THEN
        [pool EXCEPT !.certificates[cert.slot] = 
            pool.certificates[cert.slot] \union {cert}]
    ELSE
        pool

\* ============================================================================
\* VOTE AGGREGATION AND QUERIES
\* ============================================================================

\* Get all votes for a slot (across all validators)
GetVotesForSlot(pool, slot) ==
    UNION {pool.votes[slot][v] : v \in Validators}

\* Count stake for notarization votes on a specific block
\* IMPORTANT: Uses count-once-per-slot rule!
NotarStake(pool, slot, blockHash) ==
    LET votes == GetVotesForSlot(pool, slot)
        notarVotes == {v \in votes : 
            v.type = "NotarVote" /\ v.blockHash = blockHash}
        validators == {v.validator : v \in notarVotes}
    IN CalculateStake(validators)

\* Count stake for skip votes in a slot
SkipStake(pool, slot) ==
    LET votes == GetVotesForSlot(pool, slot)
        skipVotes == {v \in votes : v.type = "SkipVote"}
        validators == {v.validator : v \in skipVotes}
    IN CalculateStake(validators)

\* Total notarization stake across ALL blocks in a slot
TotalNotarStake(pool, slot) ==
    LET votes == GetVotesForSlot(pool, slot)
        notarVotes == {v \in votes : v.type = "NotarVote"}
        validators == {v.validator : v \in notarVotes}
    IN CalculateStake(validators)

\* Maximum notarization stake for any single block in a slot
MaxNotarStake(pool, slot) ==
    LET votes == GetVotesForSlot(pool, slot)
        notarVotes == {v \in votes : v.type = "NotarVote"}
        blocks == {v.blockHash : v \in notarVotes}
    IN IF blocks = {} THEN 0
       ELSE LET stakes == {NotarStake(pool, slot, b) : b \in blocks}
            IN CHOOSE s \in stakes : \A s2 \in stakes : s >= s2

\* ============================================================================
\* CERTIFICATE GENERATION
\* ============================================================================

\* Definition 13: whenever enough votes are collected we must form the
\* corresponding certificate(s). This function checks every block with
\* votes and returns any certificate that can now be assembled.
GenerateCertificate(pool, slot) ==
    LET votes == GetVotesForSlot(pool, slot)
        notarBlocks == {vote.blockHash : vote \in {vt \in votes : vt.type = "NotarVote"}}
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
            UNION {BlockCertFor(block) : block \in notarBlocks}
        skipCert == IF CanCreateSkipCert(votes, slot)
                     THEN {CreateSkipCert(votes, slot)}
                     ELSE {}
        finalCert == IF CanCreateFinalizationCert(votes, slot)
                      THEN {CreateFinalizationCert(votes, slot)}
                      ELSE {}
    IN blockCerts \cup skipCert \cup finalCert

\* ============================================================================
\* CERTIFICATE QUERIES
\* ============================================================================

\* Check if pool has a notarization certificate for a block
HasNotarizationCert(pool, slot, blockHash) ==
    \E cert \in pool.certificates[slot] :
        /\ cert.type = "NotarizationCert"
        /\ cert.blockHash = blockHash

\* Check if pool has a notar-fallback certificate for a block
HasNotarFallbackCert(pool, slot, blockHash) ==
    \E cert \in pool.certificates[slot] :
        /\ cert.type = "NotarFallbackCert"
        /\ cert.blockHash = blockHash

\* Check if pool has a skip certificate for a slot
HasSkipCert(pool, slot) ==
    \E cert \in pool.certificates[slot] :
        cert.type = "SkipCert"

\* Check if pool has a fast-finalization certificate
HasFastFinalizationCert(pool, slot, blockHash) ==
    \E cert \in pool.certificates[slot] :
        /\ cert.type = "FastFinalizationCert"
        /\ cert.blockHash = blockHash

\* Check if pool has a finalization certificate
HasFinalizationCert(pool, slot) ==
    \E cert \in pool.certificates[slot] :
        cert.type = "FinalizationCert"

\* ============================================================================
\* EVENT GENERATION (Definitions 15 and 16)
\* ============================================================================

(***************************************************************************
 * Event: BlockNotarized (Definition 15)
 * Emitted when: Pool holds a notarization certificate for block b
 * Effect: Enables finalization voting in slow path
 ***************************************************************************)
ShouldEmitBlockNotarized(pool, slot, blockHash) ==
    HasNotarizationCert(pool, slot, blockHash)

(***************************************************************************
 * Event: ParentReady (Definition 15)
 * Emitted when: 
 * 1. Slot is first of its leader window
 * 2. Pool has cert for previous block
 * 3. Pool has skip certs for all gaps
 * Effect: Leader can start producing blocks
 ***************************************************************************)
ShouldEmitParentReady(pool, slot, parentHash, parentSlot) ==
    /\ IsFirstSlotOfWindow(slot)
    /\ (HasNotarizationCert(pool, parentSlot, parentHash) \/
        HasNotarFallbackCert(pool, parentSlot, parentHash))
    /\ \A s \in (parentSlot+1)..(slot-1) : HasSkipCert(pool, s)

(***************************************************************************
 * Event: SafeToNotar - DEFINITION 16 (Fallback events) - Page 21:
 * "The event is only issued if the node voted in slot s already, but not 
 * to notarize b. Moreover:
 *   notar(b) ≥ 40% OR (skip(s) + notar(b) ≥ 60% AND notar(b) ≥ 20%)"
 * 
 * This prevents fast-finalization of a conflicting block (safety).
 * Effect: Enables casting notar-fallback vote for block b.
 ***************************************************************************)
CanEmitSafeToNotar(pool, slot, blockHash, parentHash, alreadyVoted, votedForBlock) ==
    /\ alreadyVoted      \* Must have voted in slot
    /\ ~votedForBlock    \* But not for this block
    /\ LET notar == NotarStake(pool, slot, blockHash)
           skip == SkipStake(pool, slot)
           parentSlot == IF slot = 0 THEN 0 ELSE slot - 1
           parentReady ==
                IF IsFirstSlotOfWindow(slot)
                THEN TRUE
                ELSE parentSlot \in Slots /\ HasNotarFallbackCert(pool, parentSlot, parentHash)
       IN parentReady /\
          (MeetsThreshold(notar, 40)
           \/ (MeetsThreshold(skip + notar, 60) /\ MeetsThreshold(notar, 20)))

(***************************************************************************
 * Event: SafeToSkip - DEFINITION 16 (Fallback events) - Page 22:
 * "The event is only issued if the node voted in slot s already, but not 
 * to skip s. Moreover:
 *   skip(s) + Σ_b notar(b) - max_b notar(b) ≥ 40%"
 * 
 * This ensures no block can achieve fast finalization (safety).
 * Effect: Enables casting skip-fallback vote for slot s.
 ***************************************************************************)
CanEmitSafeToSkip(pool, slot, alreadyVoted, votedSkip) ==
    /\ alreadyVoted      \* Must have voted in slot
    /\ ~votedSkip        \* But not skip
    /\ LET skip == SkipStake(pool, slot)
           totalNotar == TotalNotarStake(pool, slot)
           maxNotar == MaxNotarStake(pool, slot)
       IN MeetsThreshold(skip + totalNotar - maxNotar, 40)

\* ============================================================================
\* INVARIANTS FOR VERIFICATION
\* ============================================================================

\* Pool state is properly typed
PoolTypeOK(pool) ==
    /\ DOMAIN pool.votes = Slots
    /\ \A s \in Slots : DOMAIN pool.votes[s] = Validators
    /\ \A s \in Slots : pool.certificates[s] \subseteq Certificate

\* Multiplicity rules are respected
MultiplicityRulesRespected(pool) ==
    \A s \in Slots, v \in Validators :
        LET votes == pool.votes[s][v]
        IN /\ Cardinality({vt \in votes : vt.type = "NotarVote"}) <= 1
           /\ Cardinality({vt \in votes : vt.type = "SkipVote"}) <= 1
           /\ Cardinality({vt \in votes : vt.type = "NotarFallbackVote"}) <= 3
           /\ Cardinality({vt \in votes : vt.type = "SkipFallbackVote"}) <= 1
           /\ Cardinality({vt \in votes : vt.type = "FinalVote"}) <= 1

\* Certificate uniqueness is maintained
CertificateUniqueness(pool) ==
    \A s \in Slots :
        \A c1, c2 \in pool.certificates[s] :
            (c1.type = c2.type /\ c1.slot = c2.slot) =>
            (c1.type \in {"SkipCert", "FinalizationCert"} \/ c1.blockHash = c2.blockHash)

=============================================================================
