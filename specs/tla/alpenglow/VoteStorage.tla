---------------------------- MODULE VoteStorage ----------------------------
(***************************************************************************
 * VOTE AND CERTIFICATE STORAGE (POOL) FOR ALPENGLOW
 *
 * What this module specifies and why (whitepaper anchors):
 * - §2.4 Votes & Certificates (Tables 5–6): vote/certificate families,
 *   thresholds, and the fast (80%) vs slow (60%+second round) paths.
 * - §2.5 Pool (Definition 12–16): what each validator stores locally,
 *   when certificates are generated/stored/broadcast, and which events are
 *   emitted to drive Algorithm 1. See alpenglow-whitepaper.md:509–:571.
 * - §2.5 (Definition 14): finalization semantics — slot-scoped slow
 *   finalization vs block-scoped fast finalization (lines 536–539).
 *
 * This module encodes the Pool-side logic: how raw votes (counted once per
 * slot per validator; Def. 12 at :513) are collected and turned into
 * notarization/skip/finalization certificates (Def. 13 at :520, :532), and
 * how Pool emits events (Def. 15–16 at :543–:571) that enable the protocol
 * to progress.
 ***************************************************************************)

EXTENDS Naturals, FiniteSets, Messages, Blocks, Certificates

\* ============================================================================
\* PARAMETERS (caps from Definition 12)
\* ============================================================================

(***************************************************************************
 * VOTE MULTIPLICITY LIMITS — Definition 12 (Pool; §2.5)
 * Whitepaper text (alpenglow-whitepaper.md:513):
 *   “Pool stores received votes for every slot and every node as follows:
 *     • The first received notarization or skip vote,
 *     • up to 3 received notar-fallback votes,
 *     • the first received skip-fallback vote, and
 *     • the first received finalization vote.”
 * We expose the limits as constants (avoid magic numbers) and use them in
 * multiplicity guards below. Lemma 20 (:820) justifies that correct nodes
 * cast at most one initial vote per slot (notar or skip).
 ***************************************************************************)

MaxInitialVotes == 1         \* First initial (Notar or Skip) per slot/validator
MaxNotarFallbacks == 3       \* Up to three notar-fallback votes
MaxSkipFallbacks == 1        \* First skip-fallback vote
MaxFinalVotes == 1           \* First finalization vote

\* Reusable set of notarization-family certificate types (Table 6; :507)
NotarTypes == {"NotarizationCert", "NotarFallbackCert", "FastFinalizationCert"}

\* ============================================================================
\* POOL STATE STRUCTURE
\* ============================================================================

(***************************************************************************
 * POOL SHAPE — Definition 12–13 (§2.5)
 * - Stores votes per (slot, validator) under Def. 12’s count-once policy
 *   (alpenglow-whitepaper.md:513, Lemma 20 at :820).
 * - Stores certificates per slot under Def. 13, one of each type for the
 *   given block/slot (lines :520, :532; Table 6 at :507).
 * - Serves as the source of stake tallies for Def. 16’s notar(b) and
 *   skip(s) quantities (lines :554–:571) and as the emitter for events
 *   in Def. 15–16 (:543–:571).
 ***************************************************************************)

PoolState == [
    votes: [Slots -> [Validators -> SUBSET Vote]],  \* Votes by slot and validator
    certificates: [Slots -> SUBSET Certificate]      \* Certificates by slot (see Def. 12/13)
]

\* Initialize an empty Pool (all buckets empty; §2.5)
InitPool == [
    votes |-> [s \in Slots |-> [v \in Validators |-> {}]],
    certificates |-> [s \in Slots |-> {}]
]

\* ============================================================================
\* VOTE STORAGE WITH MULTIPLICITY RULES (Definition 12)
\* ============================================================================

(***************************************************************************
 * STORE-TIME MULTIPLICITY GUARDS — Definition 12 (§2.5)
 * Source: alpenglow-whitepaper.md:513; Lemma 20 at :820.
 * - First initial vote per (slot, validator): either NotarVote or SkipVote.
 * - Up to 3 NotarFallbackVote per (slot, validator).
 * - First SkipFallbackVote and first FinalVote per (slot, validator).
 * Rationale: Ensures “count once per slot” semantics for stake tallies used
 * in Def. 16’s notar(b) and skip(s), and bounds fallback multiplicity.
 ***************************************************************************)

\* Definition 12 guard: enforce the limits before adding anything to Pool.
\* Reference: alpenglow-whitepaper.md:513 (Def. 12). Scope: caps are per
\* (slot, validator) across any blocks (fallbacks), not per-block.
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

\* Definition 12 effect: after passing multiplicity we record the vote for
\* this (slot, validator) so later stake calculations can see it.
StoreVote(pool, vote) ==
    \* Whitepaper anchor: Def. 12 at :513; see also Lemma 20 at :820.
    \* Defensive validity gate: only store well-formed votes (Messages.tla).
    \* The ingress (DeliverVote) ensures `vote \in Vote /\ IsValidVote(vote)`.
    IF IsValidVote(vote) /\ CanStoreVote(pool, vote) THEN
        LET 
            slot == vote.slot
            validator == vote.validator
            existingVotes == pool.votes[slot][validator]
        IN
            \* Idempotence: set union ensures duplicate deliveries are harmless.
            \* Re-storing an identical vote has no effect on Pool state.
            [pool EXCEPT !.votes[slot][validator] = existingVotes \cup {vote}]
    ELSE
        pool  \* Don't store if multiplicity rules violated

\* ============================================================================
\* CERTIFICATE STORAGE (Definition 13; §2.5)
\* ============================================================================

(***************************************************************************
 * CERTIFICATE UNIQUENESS — Definition 13 (§2.5)
 * Sources: alpenglow-whitepaper.md:520, :532.
 * “Pool generates, stores and broadcasts certificates … A single certificate
 * of each type corresponding to the given block/slot is stored in Pool.”
 * Consequence: prevents conflicting certificates from coexisting locally.
 ***************************************************************************)

\* Enforce Def. 13 uniqueness per slot/block/type; also ensure Skip vs Block
\* mutual exclusion (SkipCert cannot coexist with any block-related cert) via
\* Certificates.SkipVsBlockCertExclusion. See Table 6 (:507) and :532.
CanStoreCertificate(pool, cert) ==
    LET 
        slot == cert.slot
        existing == pool.certificates[slot]
        newset == existing \cup {cert}
    IN
        /\ SkipVsBlockCertExclusion(newset)
        /\ CASE cert.type = "SkipCert" ->
                 \* At most one SkipCert per slot
                 ~\E c \in existing : c.type = "SkipCert"

           [] cert.type = "FinalizationCert" ->
                 \* At most one FinalizationCert per slot
                 ~\E c \in existing : c.type = "FinalizationCert"

           [] cert.type \in NotarTypes ->
                 /\ ~\E c \in existing : c.type = cert.type /\ c.blockHash = cert.blockHash
                 /\ (\A c \in existing : c.type \in NotarTypes => c.blockHash = cert.blockHash)

           [] OTHER -> FALSE

\* Store a certificate in Pool (Def. 13; :520, :532)
\* - Validate structure and thresholds (Certificates.IsValidCertificate).
\* - Accept network-learned certificates even if constituent votes arrive later.
\*   Pool invariants handle safety: Skip-vs-Block exclusion, uniqueness.
StoreCertificate(pool, cert) ==
    \* Structural well-formedness: votes must be relevant to (type, slot, block).
    IF CanStoreCertificate(pool, cert)
       /\ IsValidCertificate(cert)
       /\ CertificateWellFormed(cert)
    THEN
        [pool EXCEPT !.certificates[cert.slot] = 
            pool.certificates[cert.slot] \cup {cert}]
    ELSE
        pool

\* Cross-type coherence (derivable from Table 6 & Def. 13): within a slot,
\* all notar-family certificates (Notarization/NotarFallback/FastFinalization)
\* refer to the same blockHash. This aligns with §2.5’s slow/fast semantics.
\* DELETE: local uniqueness helper not used elsewhere
NotarFamilyUniqueBlockPerSlot(pool, s) ==
    LET notarBs == {c.blockHash : c \in {d \in pool.certificates[s] : d.type \in NotarTypes}}
    IN Cardinality(notarBs) <= 1

\* ============================================================================
\* VOTE AGGREGATION AND QUERIES
\* ============================================================================

\* Helper: maximum of a finite set of natural numbers (0 on empty).
\* Used in Def. 16’s SafeToSkip formula (Σ notar − max notar) at :571.
MaxNat(S) == IF S = {} THEN 0 ELSE CHOOSE x \in S : \A y \in S : x >= y

\* Slot-wide vote aggregator (Def. 16; §2.5). Notar(b) and skip(s) are
\* computed over votes “in Pool” for the slot (alpenglow-whitepaper.md:554).
GetVotesForSlot(pool, slot) ==
    \* Domain-robustness: iterate over DOMAIN of the slot map
    UNION { pool.votes[slot][v] : v \in DOMAIN pool.votes[slot] }

\* Typing lemma: aggregator result is a subset of Vote
GetVotesForSlotTypeOK(pool, slot) ==
    GetVotesForSlot(pool, slot) \subseteq Vote

\* NOTAR STAKE (notar(b)) — Definition 16 (§2.5)
\* Source: alpenglow-whitepaper.md:554. Uses initial NotarVote only.
\* Count once per slot via StakeFromVotes(UniqueValidators(...)).
NotarStake(pool, slot, blockHash) ==
    LET votes == GetVotesForSlot(pool, slot)
        notarVotes == {v \in votes :
            /\ IsInitialNotarVote(v)
            /\ v.slot = slot            \* explicit slot guard for clarity
            /\ v.blockHash = blockHash}
    IN StakeFromVotes(notarVotes)

\* SKIP STAKE (skip(s)) — Definition 16 (§2.5)
\* Source: alpenglow-whitepaper.md:554. Uses initial SkipVote only.
\* Count once per slot by deduplicating validators.
SkipStake(pool, slot) ==
    LET votes == GetVotesForSlot(pool, slot)
        skipVotes == {v \in votes : v.type = "SkipVote"}
        validators == {v.validator : v \in skipVotes}
    IN CalculateStake(validators)
\* Alias for readability (audit suggestion): emphasize the "initial" semantics
\* DELETE: alias, unused by current spec
InitialSkipStake(pool, slot) == SkipStake(pool, slot)

\* Σ_b NOTAR(b) — sum over all blocks in slot (Def. 16; :554)
\* Applies count-once-per-slot semantics per Def. 12 (:513).
TotalNotarStake(pool, slot) ==
    LET votes == GetVotesForSlot(pool, slot)
        notarVotes == {v \in votes : IsInitialNotarVote(v)}
    IN StakeFromVotes(notarVotes)

\* max_b NOTAR(b) — maximum per-block notar stake (Def. 16; :571).
\* Used in SafeToSkip guard.
MaxNotarStake(pool, slot) ==
    LET votes == GetVotesForSlot(pool, slot)
        notarVotes == {v \in votes : IsInitialNotarVote(v)}
        blocks == {v.blockHash : v \in notarVotes}
    IN IF blocks = {} THEN 0
       ELSE LET stakes == {NotarStake(pool, slot, b) : b \in blocks}
            IN MaxNat(stakes)

\* Σ notar − max notar (Def. 16; :571) — stake outside the max block.
NonMaxNotarStake(pool, slot) ==
    TotalNotarStake(pool, slot) - MaxNotarStake(pool, slot)

\* ============================================================================
\* CERTIFICATE GENERATION
\* ============================================================================

\* CERTIFICATE GENERATION — Definition 13 (§2.5)
\* When enough votes accumulate, Pool generates certificates and (per Def. 13)
\* broadcasts them. Here we compute the set of creatable certificates for a
\* slot from Pool votes; broadcasting is handled by the caller.
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
        \* Slow-path finalization (Def. 14; :536–:539): prefer creating it when
        \* a notarization is present (stored or creatable) to mirror the paper.
        hasNotarNow == \E c \in blockCerts : c.type = "NotarizationCert"
        hasNotarStored == \E c \in pool.certificates[slot] : c.type = "NotarizationCert"
        finalCert == IF CanCreateFinalizationCert(votes, slot) /\ (hasNotarNow \/ hasNotarStored)
                      THEN {CreateFinalizationCert(votes, slot)}
                      ELSE {}
    IN blockCerts \cup skipCert \cup finalCert

\* ============================================================================
\* CERTIFICATE QUERIES
\* ============================================================================

\* Query helpers assume StoreCertificate enforces validity/structure; these
\* are presence checks over Pool’s stored certificates (Table 6; :507).

\* Generic block-scoped presence query; specialized wrappers follow.
HasBlockCertOfType(pool, slot, blockHash, certType) ==
    \E cert \in pool.certificates[slot] :
        /\ cert.type = certType
        /\ cert.blockHash = blockHash
        /\ cert.slot = slot

\* Specialized wrappers for clarity
HasNotarizationCert(pool, slot, blockHash) ==
    HasBlockCertOfType(pool, slot, blockHash, "NotarizationCert")

HasNotarFallbackCert(pool, slot, blockHash) ==
    HasBlockCertOfType(pool, slot, blockHash, "NotarFallbackCert")

\* Slot-scoped presence; Table 6 (:507) notes Skip/Finalization are slot-scoped.
HasSlotCertOfType(pool, slot, certType) ==
    \E cert \in pool.certificates[slot] :
        /\ cert.type = certType
        /\ cert.slot = slot

\* Check if pool has a skip certificate for a slot
\* Def. 15 (ParentReady) requires skip certs for all gap slots between the
\* certified parent and the first slot of a leader window (alpenglow-whitepaper.md:543–:546).
\* Skip-vs-Block mutual exclusion is ensured by Pool storage rules.
HasSkipCert(pool, slot) ==
    HasSlotCertOfType(pool, slot, "SkipCert")

\* Check if pool has a fast-finalization certificate
HasFastFinalizationCert(pool, slot, blockHash) ==
    HasBlockCertOfType(pool, slot, blockHash, "FastFinalizationCert")

\* Finalization presence (Def. 14; :536–:539). Slow path is slot-scoped; the
\* finalized block is the unique notarized block in that slot.
HasFinalizationCert(pool, slot) ==
    HasSlotCertOfType(pool, slot, "FinalizationCert")

\* Optional typing helper for proof obligations: make slot/block domains explicit.
\* DELETE: typing helper unused
BlockCertQueryTypesOK(slot, blockHash) ==
    /\ slot \in Slots
    /\ blockHash \in BlockHashes

\* Slow-path finalization guard (Def. 14; :536–:539): requires the slot-level
\* FinalizationCert plus the slot’s unique NotarizationCert for block h.
CanFinalizeSlow(pool, slot, blockHash) ==
    /\ HasFinalizationCert(pool, slot)
    /\ HasNotarizationCert(pool, slot, blockHash)

\* ============================================================================
\* EVENT GENERATION (Definitions 15 and 16)
\* ============================================================================

(***************************************************************************
 * BLOCKNOTARIZED — Definition 15 (§2.5)
 * Source: alpenglow-whitepaper.md:545.
 * Emitted when Pool holds a NotarizationCert for block b; enables slow-path
 * FinalVote issuance and subsequent FinalizationCert creation (Def. 14).
 ***************************************************************************)
ShouldEmitBlockNotarized(pool, slot, blockHash) ==
    HasNotarizationCert(pool, slot, blockHash)

(***************************************************************************
 * PARENTREADY — Definition 15 (§2.5)
 * Source: alpenglow-whitepaper.md:546.
 * Emitted for the first slot s of a leader window when Pool has a notar or
 * notar-fallback cert for the parent block and skip certs for all gaps. This
 * lets the leader safely start its window (see also §2.6 usage around :602–:617).
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
 * SAFETONOTAR — Definition 16 (§2.5 fallback events)
 * Source: alpenglow-whitepaper.md:554, :556 and :569.
 * Conditions:
 * - Node has already voted in slot s, but not to notarize b.
 * - Parent gating: if s is first in window, OK; otherwise require parent’s
 *   notar-fallback certificate (repair procedure resolves parent, :569).
 * - Stake thresholds: notar(b) ≥ 40% OR ((skip(s)+notar(b)) ≥ 60% AND notar(b) ≥ 20%).
 * Rationale: ensures no conflicting block can be fast-finalized; enables
 * issuing a NotarFallbackVote for b.
 ***************************************************************************)
\* Readability (audit 0013): centralize Def. 16 parent-gating logic.
ParentFallbackReady(pool, slot, parentHash) ==
    /\ IsFirstSlotOfWindow(slot)
    \/ (\E ps \in Slots : ps < slot /\ HasNotarFallbackCert(pool, ps, parentHash))
    \* Modeling note: Def. 16 refers to the parent’s notar-fallback cert.
    \* Here we quantify over prior slots by blockHash because this helper is
    \* used where parentSlot is not directly available; ShouldEmitParentReady
    \* uses the precise (parentSlot, parentHash) pairing.

CanEmitSafeToNotar(pool, slot, blockHash, parentHash, alreadyVoted, votedForBlock) ==
    /\ alreadyVoted      \* Must have voted in slot
    /\ ~votedForBlock    \* But not for this block
    /\ ParentFallbackReady(pool, slot, parentHash)
    /\ LET notar == NotarStake(pool, slot, blockHash)
           skip == SkipStake(pool, slot)
       IN (MeetsThreshold(notar, 40)
           \/ (MeetsThreshold(skip + notar, DefaultThreshold) /\ MeetsThreshold(notar, 20)))

(***************************************************************************
 * SAFETOSKIP — Definition 16 (§2.5 fallback events)
 * Source: alpenglow-whitepaper.md:571.
 * Conditions: node has already voted in slot s, but not to skip s; and
 *   skip(s) + (Σ_b notar(b) − max_b notar(b)) ≥ 40%.
 * Rationale: ensures no block in s can be fast-finalized; enables
 * SkipFallbackVote for s.
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

\* Pool state is properly typed (Pool domain; §2.5 definitions)
PoolTypeOK(pool) ==
    /\ DOMAIN pool.votes = Slots
    /\ \A s \in Slots : DOMAIN pool.votes[s] = Validators
    /\ \A s \in Slots : \A v \in Validators : pool.votes[s][v] \subseteq Vote
    /\ DOMAIN pool.certificates = Slots
    /\ \A s \in Slots : pool.certificates[s] \subseteq Certificate

\* Alignment invariant: votes match their (slot, validator) keys
PoolVotesSlotValidatorAligned(pool) ==
    \A s \in Slots : \A v \in Validators :
        \A vt \in pool.votes[s][v] : vt.slot = s /\ vt.validator = v

\* Bucket–slot consistency: certificates stored under slot s all have c.slot = s.
PoolCertificatesSlotAligned(pool) ==
    \A s \in Slots : \A c \in pool.certificates[s] : c.slot = s

\* Alias for proof scripts: bucket–slot consistency
BucketSlotConsistency(pool) == PoolCertificatesSlotAligned(pool)

\* Aggregated votes are well-typed
\* DELETE: typing helper unused
VotesTypeOK(pool) ==
    \A s \in Slots : GetVotesForSlotTypeOK(pool, s)

\* Optional invariant: No double-counting across skip+notar initial votes.
\* For every slot, the set of validators with an initial SkipVote is disjoint
\* from those with an initial NotarVote (any block). This makes explicit the
\* property relied upon by Def. 16 arithmetic: SkipStake and NotarStake never
\* count the same validator in the same slot.
\* DELETE: strengthening invariant unused
NoSkipAndNotarDoubleCount(pool, s) ==
    LET votes == GetVotesForSlot(pool, s)
        skipVotes == {vt \in votes : vt.type = "SkipVote"}
        notarVotes == {vt \in votes : IsInitialNotarVote(vt)}
        skipVals == {vt.validator : vt \in skipVotes}
        notarVals == {vt.validator : vt \in notarVotes}
    IN skipVals \cap notarVals = {}

\* Count-once lemma: SkipStake equals the stake of unique validators with an
\* initial SkipVote in the slot (mirrors the TotalNotar lemma).
\* DELETE: lemma unused
SkipStakeEqualsUniqueSkipVoters(pool, s) ==
    LET votes == GetVotesForSlot(pool, s)
        sv == {vt \in votes : vt.type = "SkipVote"}
        uniqVals == {vt.validator : vt \in sv}
    IN SkipStake(pool, s) = CalculateStake(uniqVals)

\* SafeToSkip arithmetic sanity: expression is non-negative.
\* DELETE: arithmetic sanity unused
SafeToSkipExpressionNonNegative(pool, s) ==
    SkipStake(pool, s) + TotalNotarStake(pool, s) - MaxNotarStake(pool, s) >= 0

\* Typing lemma: per-block notar-stake values are natural numbers, matching
\* the MaxNat domain (CalculateStake: Validators → Nat).
\* DELETE: typing lemma unused
BlockNotarStakesAreNat(pool, s) ==
    LET votes == GetVotesForSlot(pool, s)
        notarVotes == {v \in votes : IsInitialNotarVote(v)}
        blocks == {v.blockHash : v \in notarVotes}
        stakes == {NotarStake(pool, s, b) : b \in blocks}
    IN stakes \subseteq Nat

\* Local sanity: NotarStake equals StakeFromVotes over initial NotarVote when
\* using the slot’s aggregated votes (explicit slot guard is redundant).
\* DELETE: redundancy check unused
NotarStakeMatchesStakeFromVotes(pool, s, b) ==
    LET votes == GetVotesForSlot(pool, s)
        nv == {v \in votes : /\ IsInitialNotarVote(v) /\ v.blockHash = b}
    IN NotarStake(pool, s, b) = StakeFromVotes(nv)

\* Multiplicity rules respected (Def. 12; :513): per (slot, validator) caps for
\* initial, fallback, and finalization votes.
MultiplicityRulesRespected(pool) ==
    \A s \in Slots, v \in Validators :
        LET votes == pool.votes[s][v]
        IN /\ Cardinality({vt \in votes : IsInitialVote(vt)}) <= MaxInitialVotes
           /\ Cardinality({vt \in votes : vt.type = "NotarFallbackVote"}) <= MaxNotarFallbacks
           /\ Cardinality({vt \in votes : vt.type = "SkipFallbackVote"}) <= MaxSkipFallbacks
           /\ Cardinality({vt \in votes : vt.type = "FinalVote"}) <= MaxFinalVotes

\* Optional strengthening: for a fixed (slot, validator), all stored
\* NotarFallbackVote messages, if any, agree on the same blockHash; i.e., a
\* validator backs at most one block with fallback votes within a slot.
NotarFallbackBlockConsistencyAt(pool, s, v) ==
    LET votes == pool.votes[s][v]
        fbVotes == {vt \in votes : vt.type = "NotarFallbackVote"}
        fbBlocks == {vt.blockHash : vt \in fbVotes}
    IN Cardinality(fbBlocks) <= 1

\* Optional sequencing clarification (Algorithm 1 semantics): if Pool contains
\* a SkipFallbackVote for (s, v), then it also contains an initial NotarVote
\* for (s, v). This mirrors Def. 16’s “already voted in s, but not to skip s”.
SkipFallbackAfterInitialNotarAt(pool, s, v) ==
    LET votes == pool.votes[s][v]
    IN (\E vt \in votes : vt.type = "SkipFallbackVote")
            => (\E vn \in votes : IsInitialNotarVote(vn))

\* Certificate uniqueness (Def. 13; :520, :532)
\* - ≤1 SkipCert and ≤1 FinalizationCert per slot.
\* - For notarization-family types, ≤1 per (type, blockHash) per slot.
\* - Cross-type consistency: all notar-family certs in a slot, if any, share
\*   the same blockHash (matches slow/fast path coherence).
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
 * FAST ⇒ NOTAR (local Pool view) — §2.5
 * Anchors: Table 6 (:507) and the note at :534 (“fast ⇒ notar ⇒ fallback”).
 * For certificates stored in a slot’s Pool bucket, every FastFinalizationCert
 * implies a NotarizationCert for the same block, with vote-subset inclusion.
 * This scopes the cross-node timing statement to a single Pool state.
 *************************************************************************)
\* DELETE: unused; MainProtocol uses Certificates.FastPathImplication
PoolFastImpliesNotarSubset(pool, s, h) ==
    LET certs == pool.certificates[s]
    IN \A fastCert \in certs :
        (fastCert.type = "FastFinalizationCert" /\ fastCert.blockHash = h)
            => \E notarCert \in certs :
                /\ notarCert.type = "NotarizationCert"
                /\ notarCert.slot = fastCert.slot
                /\ notarCert.blockHash = h
                /\ notarCert.votes \subseteq fastCert.votes

\* Optional: all stored certificates are structurally well-formed (votes only
\* for the certificate’s (type, slot, blockHash)).
CertificatesWellFormed(pool) ==
    \A s \in Slots : AllCertificatesWellFormed(pool.certificates[s])

\* Def. 14 pairing: FinalizationCert(s) implies presence of some
\* NotarizationCert in slot s (slow path needs a unique notarized block).
FinalizationImpliesNotarizationPresent(pool, s) ==
    (\E c \in pool.certificates[s] : c.type = "FinalizationCert")
        => (\E n \in pool.certificates[s] : n.type = "NotarizationCert")

(***************************************************************************
 * Preservation: StoreVote preserves multiplicity rules (Def. 12; :513)
 * If a vote is valid and allowed by CanStoreVote, MultiplicityRulesRespected
 * remains true of the Pool state.
 *************************************************************************)
THEOREM StoreVotePreservesMultiplicity ==
    \A pool \in PoolState, vote \in Vote :
        (MultiplicityRulesRespected(pool) /\ IsValidVote(vote) /\ CanStoreVote(pool, vote))
            => MultiplicityRulesRespected(StoreVote(pool, vote))

\* Sanity: TotalNotarStake equals stake of unique validators that cast an
\* initial NotarVote in the slot (Σ over validator projection).
TotalNotarStakeEqualsUniqueNotarVoters(pool, s) ==
    LET votes == GetVotesForSlot(pool, s)
        nv == {vt \in votes : IsInitialNotarVote(vt)}
        uniqVals == {vt.validator : vt \in nv}
    IN TotalNotarStake(pool, s) = CalculateStake(uniqVals)

=============================================================================
