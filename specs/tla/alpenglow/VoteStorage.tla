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
\* PARAMETERS (caps from Definition 12)
\* ============================================================================

(***************************************************************************
 * Parameterized caps for vote multiplicity (audit suggestion)
 * - These mirror Definition 12’s “first/first/up to 3/first” limits.
 * - Using named constants avoids magic numbers and clarifies intent.
 ***************************************************************************)

MaxInitialVotes == 1         \* First initial (Notar or Skip) per slot/validator
MaxNotarFallbacks == 3       \* Up to three notar-fallback votes
MaxSkipFallbacks == 1        \* First skip-fallback vote
MaxFinalVotes == 1           \* First finalization vote

\* Reusable set of notarization-family certificate types (Table 6)
NotarTypes == {"NotarizationCert", "NotarFallbackCert", "FastFinalizationCert"}

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
    certificates: [Slots -> SUBSET Certificate]      \* Certificates by slot (see Def. 12/13)
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
\* Cross-link: alpenglow-whitepaper.md:513 (page 20)
\* Scope note: the "up to 3 notar-fallback votes" cap is per (slot, validator)
\* across all blocks (as encoded here), not per-block.
CanStoreVote(pool, vote) ==
    LET 
        slot == vote.slot
        validator == vote.validator
        existingVotes == pool.votes[slot][validator]
    IN
        CASE vote.type = "NotarVote" ->
            \* Can store only if no initial vote (Notar or Skip) exists yet
            ~\E v \in existingVotes : IsInitialVote(v)

        [] vote.type = "SkipVote" ->
            \* Can store only if no initial vote (Notar or Skip) exists yet
            ~\E v \in existingVotes : IsInitialVote(v)
            
        [] vote.type = "NotarFallbackVote" ->
            \* Can store up to 3 notar-fallback votes
            Cardinality({v \in existingVotes : v.type = "NotarFallbackVote"}) < MaxNotarFallbacks
            
        [] vote.type = "SkipFallbackVote" ->
            \* Can store only if under cap for SkipFallbackVote
            Cardinality({v \in existingVotes : v.type = "SkipFallbackVote"}) < MaxSkipFallbacks
            
        [] vote.type = "FinalVote" ->
            \* Can store only if under cap for FinalVote
            Cardinality({v \in existingVotes : v.type = "FinalVote"}) < MaxFinalVotes
            
        [] OTHER -> FALSE

\* Definition 12: once the multiplicity check passes we record the vote for
\* this validator/slot so later stake calculations can see it.
StoreVote(pool, vote) ==
    \* Cross-link: alpenglow-whitepaper.md:513 (page 20)
    \* Defensive validity gate (audit suggestion): only store well-formed votes.
    \* See MainProtocol.DeliverVote for the ingress contract that selects
    \* only `vote \in Vote /\ IsValidVote(vote)` from the network.
    IF IsValidVote(vote) /\ CanStoreVote(pool, vote) THEN
        LET 
            slot == vote.slot
            validator == vote.validator
            existingVotes == pool.votes[slot][validator]
        IN
            \* Idempotence: set union ensures duplicate deliveries are harmless.
            \* Re-storing an identical vote has no effect on Pool state.
            [pool EXCEPT !.votes[slot][validator] = existingVotes \union {vote}]
    ELSE
        pool  \* Don't store if multiplicity rules violated

\* ============================================================================
\* CERTIFICATE STORAGE (Definition 13, Whitepaper page 21)
\* ============================================================================

(***************************************************************************
 * CRITICAL RULE from Definition 13 (Whitepaper page 21):
 * "A single certificate of each type corresponding to the given block/slot
 * is stored in Pool"
 * 
 * This ensures certificate uniqueness - can't have conflicting certificates!
 ***************************************************************************)

\* Definition 13 (Whitepaper page 21): only one certificate of a given type is stored for each
\* slot/block combination. This predicate enforces that uniqueness.
CanStoreCertificate(pool, cert) ==
    LET 
        slot == cert.slot
        existing == pool.certificates[slot]
        HasBlockCert == (\E c \in existing : c.type \in NotarTypes)
    IN
        CASE cert.type = "SkipCert" ->
                 \* Enforce mutual exclusion with any block-related cert
                 ( ~\E c \in existing : c.type = "SkipCert" ) /\ ~HasBlockCert

           [] cert.type = "FinalizationCert" ->
                 \* At most one FinalizationCert per slot
                 ~\E c \in existing : c.type = "FinalizationCert"

           [] cert.type \in NotarTypes ->
                 /\ ~\E c \in existing : c.type = cert.type /\ c.blockHash = cert.blockHash
                 /\ (\A c \in existing : c.type \in NotarTypes => c.blockHash = cert.blockHash)
                 /\ ~\E c \in existing : c.type = "SkipCert"

           [] OTHER -> FALSE

\* Store a certificate in the pool
\* Improvement: validate certificate contents on store (see audit suggestions).
\* We keep acceptance independent of local vote availability to avoid dropping
\* network-learned certificates whose constituent votes may arrive later.
StoreCertificate(pool, cert) ==
    \* Enforce structural well-formedness on store (audit suggestion):
    \* certificates must contain only votes relevant to their (type, slot, blockHash).
    IF CanStoreCertificate(pool, cert)
       /\ IsValidCertificate(cert)
       /\ CertificateWellFormed(cert)
    THEN
        [pool EXCEPT !.certificates[cert.slot] = 
            pool.certificates[cert.slot] \union {cert}]
    ELSE
        pool

\* ============================================================================
\* VOTE AGGREGATION AND QUERIES
\* ============================================================================

\* Helper: maximum of a finite set of natural numbers.
\* Returns 0 on the empty set. Useful for Def. 16 formulas (e.g., SafeToSkip).
MaxNat(S) == IF S = {} THEN 0 ELSE CHOOSE x \in S : \A y \in S : x >= y

\* Get all votes for a slot (across all validators)
\* Cross-link: Whitepaper Definition 16 (pages 21–22) defines notar(b) and
\* skip(s) as stake over votes "in Pool" for the slot. This operator is the
\* Pool-side aggregator used by those stake formulas.
GetVotesForSlot(pool, slot) ==
    \* Domain-robustness (audit 0009): iterate over DOMAIN of the slot map
    UNION { pool.votes[slot][v] : v \in DOMAIN pool.votes[slot] }

\* Lightweight lemma (audit 0009): result is a subset of Vote
GetVotesForSlotTypeOK(pool, slot) ==
    GetVotesForSlot(pool, slot) \subseteq Vote

\* Count stake for notarization votes on a specific block
\* IMPORTANT (Def. 16 clarification): Uses initial votes only (NotarVote),
\* not notar-fallback votes, and enforces count-once-per-slot via deduplication.
\* Cross-link: alpenglow-whitepaper.md:554–:571 (pages 21–22).
NotarStake(pool, slot, blockHash) ==
    LET votes == GetVotesForSlot(pool, slot)
        notarVotes == {v \in votes : 
            IsInitialNotarVote(v) /\ v.blockHash = blockHash}
        validators == {v.validator : v \in notarVotes}
    IN CalculateStake(validators)

\* Count stake for skip votes in a slot
\* IMPORTANT (Def. 16 clarification): Uses initial votes only (SkipVote),
\* not skip-fallback votes, and enforces count-once-per-slot via deduplication.
\* Cross-link: alpenglow-whitepaper.md:554–:571 (pages 21–22).
SkipStake(pool, slot) ==
    LET votes == GetVotesForSlot(pool, slot)
        skipVotes == {v \in votes : v.type = "SkipVote"}
        validators == {v.validator : v \in skipVotes}
    IN CalculateStake(validators)

\* Total notarization stake across ALL blocks in a slot
\* Whitepaper §2.5, Definition 16: corresponds to Σ_b notar(b) and uses
\* count-once-per-slot semantics per Definition 12 (deduplicate validators).
TotalNotarStake(pool, slot) ==
    LET votes == GetVotesForSlot(pool, slot)
        notarVotes == {v \in votes : IsInitialNotarVote(v)}
    IN StakeFromVotes(notarVotes)

\* Maximum notarization stake for any single block in a slot
\* Whitepaper §2.5, Definition 16 (SafeToSkip): this is the max_b notar(b)
\* term used in `CanEmitSafeToSkip` (see alpenglow-whitepaper.md:571).
MaxNotarStake(pool, slot) ==
    LET votes == GetVotesForSlot(pool, slot)
        notarVotes == {v \in votes : IsInitialNotarVote(v)}
        blocks == {v.blockHash : v \in notarVotes}
    IN IF blocks = {} THEN 0
       ELSE LET stakes == {NotarStake(pool, slot, b) : b \in blocks}
            IN MaxNat(stakes)

\* Readability helper (audit 0013): stake outside the max-notarized block.
\* Mirrors the paper’s Σ_b notar(b) − max_b notar(b) term.
NonMaxNotarStake(pool, slot) ==
    TotalNotarStake(pool, slot) - MaxNotarStake(pool, slot)

\* ============================================================================
\* CERTIFICATE GENERATION
\* ============================================================================

\* Definition 13 (Whitepaper page 21): whenever enough votes are collected we must form the
\* corresponding certificate(s). This function checks every block with
\* votes and returns any certificate that can now be assembled.
GenerateCertificate(pool, slot) ==
    LET \* Assumption: `votes` are Pool-sourced (Definition 12), ensuring
        \* count-once-per-slot semantics for stake aggregation in guards.
        votes == GetVotesForSlot(pool, slot)
        \* Improvement (audit 0012): discover candidates from both notar and
        \* notar-fallback votes to improve liveness under out-of-order delivery.
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
        \* Gate SkipCert creation: do not emit if any block certificate is creatable
        skipCert == IF (blockCerts = {}) /\ CanCreateSkipCert(votes, slot)
                     THEN {CreateSkipCert(votes, slot)}
                     ELSE {}
        \* Optional gating (audit 0012): create FinalizationCert only when
        \* some notarization is known (stored) or creatable now, to reduce churn.
        hasNotarNow == \E c \in blockCerts : c.type = "NotarizationCert"
        hasNotarStored == \E c \in pool.certificates[slot] : c.type = "NotarizationCert"
        finalCert == IF CanCreateFinalizationCert(votes, slot) /\ (hasNotarNow \/ hasNotarStored)
                      THEN {CreateFinalizationCert(votes, slot)}
                      ELSE {}
    IN blockCerts \cup skipCert \cup finalCert

\* ============================================================================
\* CERTIFICATE QUERIES
\* ============================================================================

\* Trust boundary (audit 0013): validity and structural well-formedness of
\* certificates are enforced at store time by StoreCertificate via
\* IsValidCertificate / CertificateWellFormed. The following predicates are
\* presence checks over the Pool and may assume well-formed entries.

\* Check if pool has a notarization certificate for a block
\* Trust boundary: validity is enforced when storing certificates via
\* StoreCertificate (requires IsValidCertificate / CertificateWellFormed).
\* This query assumes stored certs are valid and is a presence check.
HasNotarizationCert(pool, slot, blockHash) ==
    \E cert \in pool.certificates[slot] :
        /\ cert.type = "NotarizationCert"
        /\ cert.blockHash = blockHash
        /\ cert.slot = slot

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
        /\ cert.slot = slot

\* Check if pool has a finalization certificate
\* Clarification (Def. 14): This is a slot-level check. The finalized block
\* in the slow path is determined by combining this with the unique notarized
\* block for the slot via HasNotarizationCert.
HasFinalizationCert(pool, slot) ==
    \E cert \in pool.certificates[slot] :
        cert.type = "FinalizationCert"

\* Readability helper (audit 0013): slow-path finalization guard from Def. 14
\* Encodes the pairing "FinalizationCert(s) + NotarizationCert(s, h)".
CanFinalizeSlow(pool, slot, blockHash) ==
    /\ HasFinalizationCert(pool, slot)
    /\ HasNotarizationCert(pool, slot, blockHash)

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
    /\ parentSlot < slot   \* "previous block" guard (Def. 15)
    /\ (HasNotarizationCert(pool, parentSlot, parentHash) \/
        HasNotarFallbackCert(pool, parentSlot, parentHash))
    /\ \A s \in (parentSlot+1)..(slot-1) : HasSkipCert(pool, s)
        \* Note: (a)..(b) is empty when a > b, so if slot = parentSlot + 1
        \* (adjacent), the universal quantification holds vacuously.

(***************************************************************************
 * Event: SafeToNotar - DEFINITION 16 (Fallback events) - Page 21:
 * "The event is only issued if the node voted in slot s already, but not 
 * to notarize b. Moreover:
 *   notar(b) ≥ 40% OR (skip(s) + notar(b) ≥ 60% AND notar(b) ≥ 20%)"
 * 
 * This prevents fast-finalization of a conflicting block (safety).
 * Effect: Enables casting notar-fallback vote for block b.
 ***************************************************************************)
\* Readability (audit 0013): centralize Def. 16 parent-gating logic.
ParentFallbackReady(pool, slot, parentHash) ==
    /\ IsFirstSlotOfWindow(slot)
    \/ (\E ps \in Slots : ps < slot /\ HasNotarFallbackCert(pool, ps, parentHash))

CanEmitSafeToNotar(pool, slot, blockHash, parentHash, alreadyVoted, votedForBlock) ==
    /\ alreadyVoted      \* Must have voted in slot
    /\ ~votedForBlock    \* But not for this block
    /\ ParentFallbackReady(pool, slot, parentHash)
    /\ LET notar == NotarStake(pool, slot, blockHash)
           skip == SkipStake(pool, slot)
       IN (MeetsThreshold(notar, 40)
           \/ (MeetsThreshold(skip + notar, DefaultThreshold) /\ MeetsThreshold(notar, 20)))

(***************************************************************************
 * Event: SafeToSkip - DEFINITION 16 (Fallback events) - Page 22:
 * "The event is only issued if the node voted in slot s already, but not 
 * to skip s. Moreover:
 *   skip(s) + Σ_b notar(b) - max_b notar(b) ≥ 40%"
 * 
 * This ensures no block can achieve fast finalization (safety).
 * Def. 16 anchor: alpenglow-whitepaper.md:571
 * Effect: Enables casting skip-fallback vote for slot s.
 ***************************************************************************)
\* Clarification (audit 0013): The quantities skip(s) and notar(b) below refer
\* to initial votes only (SkipVote/NotarVote), not fallback votes. Count-once-
\* per-slot semantics (Definition 12) are realized via TotalNotarStake/SkipStake
\* by deduplicating validators per slot. This matches the whitepaper’s intent.
CanEmitSafeToSkip(pool, slot, alreadyVoted, votedSkip) ==
    /\ alreadyVoted      \* Must have voted in slot
    /\ ~votedSkip        \* But not skip
    /\ LET skip == SkipStake(pool, slot)
           nonMaxNotar == NonMaxNotarStake(pool, slot)
       IN MeetsThreshold(skip + nonMaxNotar, 40)

\* ============================================================================
\* INVARIANTS FOR VERIFICATION
\* ============================================================================

\* Pool state is properly typed (strengthened per audit 0013)
PoolTypeOK(pool) ==
    /\ DOMAIN pool.votes = Slots
    /\ \A s \in Slots : DOMAIN pool.votes[s] = Validators
    /\ \A s \in Slots : \A v \in Validators : pool.votes[s][v] \subseteq Vote
    /\ DOMAIN pool.certificates = Slots
    /\ \A s \in Slots : pool.certificates[s] \subseteq Certificate

\* Alignment invariants (audit 0009): items stored match their slot/validator keys
PoolVotesSlotValidatorAligned(pool) ==
    \A s \in Slots : \A v \in Validators :
        \A vt \in pool.votes[s][v] : vt.slot = s /\ vt.validator = v

\* Bucket-slot consistency (audit 0011): certificates stored under slot s
\* all have c.slot = s.
PoolCertificatesSlotAligned(pool) ==
    \A s \in Slots : \A c \in pool.certificates[s] : c.slot = s

\* Alias (audit 0013 terminology): bucket–slot consistency
BucketSlotConsistency(pool) == PoolCertificatesSlotAligned(pool)

\* Votes aggregated per slot are well-typed (audit 0009)
VotesTypeOK(pool) ==
    \A s \in Slots : GetVotesForSlotTypeOK(pool, s)

\* Optional invariant (audit 0013): No double-counting across skip+notar.
\* For every slot, the set of validators with an initial SkipVote is disjoint
\* from those with an initial NotarVote (any block). This makes explicit the
\* property relied upon by Def. 16 arithmetic: SkipStake and NotarStake never
\* count the same validator in the same slot.
NoSkipAndNotarDoubleCount(pool, s) ==
    LET votes == GetVotesForSlot(pool, s)
        skipVotes == {vt \in votes : vt.type = "SkipVote"}
        notarVotes == {vt \in votes : IsInitialNotarVote(vt)}
        skipVals == {vt.validator : vt \in skipVotes}
        notarVals == {vt.validator : vt \in notarVotes}
    IN skipVals \cap notarVals = {}

\* Optional typing lemma (audit 0011): the per-block notar-stake values
\* considered by MaxNotarStake are natural numbers, making the MaxNat domain
\* explicit. This follows from CalculateStake: Validators → Nat.
BlockNotarStakesAreNat(pool, s) ==
    LET votes == GetVotesForSlot(pool, s)
        notarVotes == {v \in votes : IsInitialNotarVote(v)}
        blocks == {v.blockHash : v \in notarVotes}
        stakes == {NotarStake(pool, s, b) : b \in blocks}
    IN stakes \subseteq Nat

\* Multiplicity rules are respected
MultiplicityRulesRespected(pool) ==
    \A s \in Slots, v \in Validators :
        LET votes == pool.votes[s][v]
        IN /\ Cardinality({vt \in votes : IsInitialVote(vt)}) <= MaxInitialVotes
           /\ Cardinality({vt \in votes : vt.type = "NotarFallbackVote"}) <= MaxNotarFallbacks
           /\ Cardinality({vt \in votes : vt.type = "SkipFallbackVote"}) <= MaxSkipFallbacks
           /\ Cardinality({vt \in votes : vt.type = "FinalVote"}) <= MaxFinalVotes

\* Certificate uniqueness (strengthened to match Definition 13)
\* - At most one SkipCert and one FinalizationCert per slot.
\* - For notarization-family types, at most one per (type, blockHash) per slot.
\* - Cross-type consistency: all notarization-family certs in a slot, if any,
\*   must reference the same blockHash.
CertificateUniqueness(pool) ==
    \A s \in Slots :
      /\ \A t \in {"SkipCert", "FinalizationCert"} :
            Cardinality({c \in pool.certificates[s] : c.type = t}) <= 1
      /\ \A t \in NotarTypes :
            \A b \in BlockHashes :
                Cardinality({c \in pool.certificates[s] : c.type = t /\ c.blockHash = b}) <= 1
      /\ LET notarBs == {c.blockHash : c \in {d \in pool.certificates[s] : d.type \in NotarTypes}}
         IN Cardinality(notarBs) <= 1

(***************************************************************************
 * Pool-scoped lemma (audit suggestion): For the certificates stored in a
 * given slot of a Pool, every fast-finalization certificate implies the
 * existence of a notarization certificate for the same block with
 * vote-subset inclusion (per Certificates.FastFinalizationImpliesNotarization).
 * This removes ambiguity about cross-node timing by scoping to a single Pool.
 *************************************************************************)
PoolFastImpliesNotarSubset(pool, s, h) ==
    LET certs == pool.certificates[s]
    IN \A fastCert \in certs :
        (fastCert.type = "FastFinalizationCert" /\ fastCert.blockHash = h)
            => \E notarCert \in certs :
                /\ notarCert.type = "NotarizationCert"
                /\ notarCert.slot = fastCert.slot
                /\ notarCert.blockHash = h
                /\ notarCert.votes \subseteq fastCert.votes

\* Optional global invariant (audit suggestion): All stored certificates are
\* structurally well-formed (their vote sets contain only relevant votes).
CertificatesWellFormed(pool) ==
    \A s \in Slots : AllCertificatesWellFormed(pool.certificates[s])

\* Def. 14 pairing (audit 0013): presence of a FinalizationCert for slot s in
\* a Pool implies presence of some NotarizationCert in the same slot set.
FinalizationImpliesNotarizationPresent(pool, s) ==
    (\E c \in pool.certificates[s] : c.type = "FinalizationCert")
        => (\E n \in pool.certificates[s] : n.type = "NotarizationCert")

(***************************************************************************
 * Post-condition lemma (audit suggestion): Storing a valid vote that passes
 * CanStoreVote preserves MultiplicityRulesRespected for the Pool.
 * This ties StoreVote directly to the invariant used by DeliverVote.
 *************************************************************************)
THEOREM StoreVotePreservesMultiplicity ==
    \A pool \in PoolState, vote \in Vote :
        (MultiplicityRulesRespected(pool) /\ IsValidVote(vote) /\ CanStoreVote(pool, vote))
            => MultiplicityRulesRespected(StoreVote(pool, vote))

\* Optional sanity (audit 0010): TotalNotarStake equals stake of unique
\* validators that cast a NotarVote in the slot (Σ over projection).
TotalNotarStakeEqualsUniqueNotarVoters(pool, s) ==
    LET votes == GetVotesForSlot(pool, s)
        nv == {vt \in votes : IsInitialNotarVote(vt)}
        uniqVals == {vt.validator : vt \in nv}
    IN TotalNotarStake(pool, s) = CalculateStake(uniqVals)

=============================================================================
