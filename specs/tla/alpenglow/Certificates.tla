---------------------------- MODULE Certificates ----------------------------
(***************************************************************************
 * CERTIFICATE GENERATION AND STAKE AGGREGATION FOR ALPENGLOW
 *
 * Implements the threshold logic from Whitepaper §2.4 (Definition 11,
 * Table 6) together with the stake-counting rules of Definition 12.
 *  - Fast finalization: ≥80% stake on `NotarVote`
 *  - Notarization / fallback / skip / slow finalization: ≥60%
 * Each validator contributes stake at most once per slot, matching the
 * "count-once" constraint discussed in §2.4.
 ***************************************************************************)

EXTENDS Naturals, FiniteSets, Messages

\* ============================================================================
\* CONSTANTS
\* ============================================================================

CONSTANTS
    StakeMap        \* Function mapping validators to their stake amounts

ASSUME
    /\ StakeMap \in [Validators -> Nat \ {0}]  \* Every validator has positive stake

\* ============================================================================
\* THRESHOLD PARAMETERS (avoid magic numbers)
\* ============================================================================

(***************************************************************************
 * Named thresholds used across certificate predicates and validation.
 * These match Table 6 of the whitepaper and make cross-references clearer.
 ***************************************************************************)
FastFinalThreshold == 80
DefaultThreshold  == 60

\* ============================================================================
\* STAKE CALCULATIONS
\* ============================================================================

(***************************************************************************
 * CRITICAL: "Count once per slot" rule (Definition 12)
 * 
 * Even if a validator sends multiple votes in a slot (e.g., NotarVote 
 * followed by NotarFallbackVote), their stake is counted ONLY ONCE when
 * creating certificates. This prevents double-counting.
 ***************************************************************************)

\* Calculate total stake in the system
TotalStake == 
    LET vals == DOMAIN StakeMap
    IN IF vals = {} THEN 0
       ELSE LET RECURSIVE Sum(_)
            Sum(S) == 
                IF S = {} THEN 0
                ELSE LET v == CHOOSE x \in S : TRUE
                     IN StakeMap[v] + Sum(S \ {v})
            IN Sum(vals)

\* Calculate stake for a set of validators
CalculateStake(validatorSet) ==
    LET vals == validatorSet \cap DOMAIN StakeMap
    IN IF vals = {} THEN 0
       ELSE LET RECURSIVE Sum(_)
            Sum(S) == 
                IF S = {} THEN 0
                ELSE LET v == CHOOSE x \in S : TRUE
                     IN StakeMap[v] + Sum(S \ {v})
            IN Sum(vals)

\* Get unique validators from a set of votes (for count-once rule)
UniqueValidators(votes) ==
    {v.validator : v \in votes}

\* Calculate total stake from votes (counting each validator once!)
StakeFromVotes(votes) ==
    CalculateStake(UniqueValidators(votes))

\* Check if stake meets a percentage threshold
MeetsThreshold(stake, thresholdPercent) ==
    stake * 100 >= TotalStake * thresholdPercent

\* ============================================================================
\* CERTIFICATE CREATION CONDITIONS
\* These functions check if we have enough votes to create certificates
\* ============================================================================

(***************************************************************************
 * READABILITY HELPER: Common vote scoping pattern
 * Filters a vote set to those for a particular (slot, blockHash) and
 * within a given set of vote types. Mirrors Table 6 rows.
 ***************************************************************************)
VotesFor(votes, slot, blockHash, types) ==
    {v \in votes :
        /\ v.slot = slot
        /\ v.blockHash = blockHash
        /\ v.type \in types}

(***************************************************************************
 * PRECONDITION (documentation): The `votes` argument to the `CanCreate*`
 * predicates is intended to be Pool-sourced, e.g., `GetVotesForSlot(pool, s)`,
 * so that multiplicity rules (count-once-per-slot, Definition 12) already
 * hold. `StakeFromVotes` is defensive and deduplicates by validator, but callers
 * should still pass Pool-sourced votes to avoid accidental misuse.
 ***************************************************************************)

(***************************************************************************
 * Fast-Finalization Certificate (Table 6, row 1)
 * Requirements:
 * - Vote type: NotarVote only
 * - Threshold: ≥80% of total stake
 * - Effect: Immediate finalization in one round!
 ***************************************************************************)
\* PRECONDITION: `votes` is Pool-sourced (e.g., `GetVotesForSlot`) to respect
\* multiplicity rules; `StakeFromVotes` will still deduplicate by validator.
CanCreateFastFinalizationCert(votes, slot, blockHash) ==
    LET relevantVotes == {v \in votes : 
        /\ v.type = "NotarVote"
        /\ v.slot = slot
        /\ v.blockHash = blockHash}
    IN MeetsThreshold(StakeFromVotes(relevantVotes), FastFinalThreshold)

(***************************************************************************
 * Notarization Certificate (Table 6, row 2)
 * Requirements:
 * - Vote type: NotarVote only
 * - Threshold: ≥60% of total stake
 * - Effect: Block is notarized, enables second round voting
 ***************************************************************************)
CanCreateNotarizationCert(votes, slot, blockHash) ==
    LET relevantVotes == {v \in votes :
        /\ v.type = "NotarVote"
        /\ v.slot = slot
        /\ v.blockHash = blockHash}
    IN MeetsThreshold(StakeFromVotes(relevantVotes), DefaultThreshold)

(***************************************************************************
 * Notar-Fallback Certificate (Table 6, row 3)
 * Requirements:
 * - Vote types: NotarVote OR NotarFallbackVote (mixed OK!)
 * - Threshold: ≥60% of total stake
 * - Effect: Fallback notarization when not everyone agrees initially
 * - Counting note (Definition 12): stake is counted once per validator via
 *   UniqueValidators → StakeFromVotes, even if both NotarVote and
 *   NotarFallbackVote from the same validator are present.
 ***************************************************************************)
CanCreateNotarFallbackCert(votes, slot, blockHash) ==
    LET relevantVotes == VotesFor(votes, slot, blockHash,
                                  {"NotarVote", "NotarFallbackVote"})
    IN MeetsThreshold(StakeFromVotes(relevantVotes), DefaultThreshold)

(***************************************************************************
 * Skip Certificate (Table 6, row 4)
 * Requirements:
 * - Vote types: SkipVote OR SkipFallbackVote (mixed OK!)
 * - Threshold: ≥60% of total stake
 * - Effect: Slot is skipped, move to next slot
 ***************************************************************************)
CanCreateSkipCert(votes, slot) ==
    LET relevantVotes == {v \in votes :
        /\ IsSkipVote(v)
        /\ v.slot = slot}
    IN MeetsThreshold(StakeFromVotes(relevantVotes), DefaultThreshold)

(***************************************************************************
 * Finalization Certificate (Table 6, row 5)
 * Requirements:
 * - Vote type: FinalVote only
 * - Threshold: ≥60% of total stake
 * - Effect: Complete slow-path finalization (second round)
 ***************************************************************************)
CanCreateFinalizationCert(votes, slot) ==
    LET relevantVotes == {v \in votes :
        /\ v.type = "FinalVote"
        /\ v.slot = slot}
    IN MeetsThreshold(StakeFromVotes(relevantVotes), DefaultThreshold)

\* ============================================================================
\* CERTIFICATE CREATION FUNCTIONS
\* These actually create certificate objects when thresholds are met
\* ============================================================================

\* Canonicalize skip votes so the certificate carries at most one vote
\* per validator for the given slot. If both SkipVote and SkipFallbackVote
\* exist for a validator, prefer the SkipFallbackVote (later, safety-driven).
CanonicalizeSkipVotes(votes, slot) ==
    LET S == {v \in votes : /\ IsSkipVote(v) /\ v.slot = slot}
        V == {v.validator : v \in S}
        Pick(val) ==
            IF \E x \in S : /\ x.validator = val /\ x.type = "SkipFallbackVote"
            THEN CHOOSE x \in S : /\ x.validator = val /\ x.type = "SkipFallbackVote"
            ELSE CHOOSE x \in S : /\ x.validator = val /\ x.type = "SkipVote"
    IN { Pick(val) : val \in V }

CreateFastFinalizationCert(votes, slot, blockHash) ==
    [type |-> "FastFinalizationCert",
     slot |-> slot,
     blockHash |-> blockHash,
     votes |-> {v \in votes : 
        v.type = "NotarVote" /\ v.slot = slot /\ v.blockHash = blockHash}]

CreateNotarizationCert(votes, slot, blockHash) ==
    [type |-> "NotarizationCert",
     slot |-> slot,
     blockHash |-> blockHash,
     votes |-> {v \in votes : 
        v.type = "NotarVote" /\ v.slot = slot /\ v.blockHash = blockHash}]

CreateNotarFallbackCert(votes, slot, blockHash) ==
    \* Note: `votes` is expected to be Pool-sourced (Definition 12),
    \* so multiplicity and count-once semantics hold in practice. The
    \* validator-level deduplication is still enforced during validation.
    [type |-> "NotarFallbackCert",
     slot |-> slot,
     blockHash |-> blockHash,
     votes |-> {v \in votes : 
        v.type \in {"NotarVote", "NotarFallbackVote"} /\ 
        v.slot = slot /\ v.blockHash = blockHash}]

\* PRECONDITIONS (documentation):
\* - votes \subseteq Vote
\* - slot \in Slots
\* The surrounding modules (e.g., Pool/GetVotesForSlot) ensure these types.
CreateSkipCert(votes, slot) ==
    [type |-> "SkipCert",
     slot |-> slot,
     blockHash |-> NoBlock,
     votes |-> CanonicalizeSkipVotes(votes, slot)]

\* Note (Definition 14): slow-path finalization is slot-scoped; the finalized
\* block is the unique notarized block in this slot. Hence `blockHash = NoBlock`.
CreateFinalizationCert(votes, slot) ==
    [type |-> "FinalizationCert",
     slot |-> slot,
     blockHash |-> NoBlock,
     votes |-> {v \in votes : 
        v.type = "FinalVote" /\ v.slot = slot}]

\* ============================================================================
\* CERTIFICATE VALIDATION
\* ============================================================================

\* Check if a certificate is valid (Table 6 thresholds with relevance filtering)
\* Implements the audit suggestion: compute stake from votes relevant to the
\* certificate's (type, slot, blockHash). Optionally defensively checks that
\* provided votes are well-typed.
IsValidCertificate(cert) ==
    LET RelevantVotes ==
            CASE cert.type = "FastFinalizationCert" ->
                     VotesFor(cert.votes, cert.slot, cert.blockHash, {"NotarVote"})
               [] cert.type = "NotarizationCert" ->
                     VotesFor(cert.votes, cert.slot, cert.blockHash, {"NotarVote"})
               [] cert.type = "NotarFallbackCert" ->
                     VotesFor(cert.votes, cert.slot, cert.blockHash, {"NotarVote", "NotarFallbackVote"})
               [] cert.type = "SkipCert" ->
                     VotesFor(cert.votes, cert.slot, NoBlock, {"SkipVote", "SkipFallbackVote"})
               [] cert.type = "FinalizationCert" ->
                     VotesFor(cert.votes, cert.slot, NoBlock, {"FinalVote"})
               [] OTHER -> {}
        stake == StakeFromVotes(RelevantVotes)
    IN /\ cert.type \in CertificateType
       /\ cert.slot \in Slots
       /\ (\A v \in cert.votes : IsValidVote(v))  \* defensive typing check
       /\ CASE cert.type = "FastFinalizationCert" ->
               /\ cert.blockHash \in BlockHashes
               /\ MeetsThreshold(stake, FastFinalThreshold)
          [] cert.type \in {"NotarizationCert", "NotarFallbackCert"} ->
               /\ cert.blockHash \in BlockHashes
               /\ MeetsThreshold(stake, DefaultThreshold)
          [] cert.type = "SkipCert" ->
               /\ cert.blockHash = NoBlock
               /\ MeetsThreshold(stake, DefaultThreshold)
          [] cert.type = "FinalizationCert" ->
               /\ cert.blockHash = NoBlock
               /\ MeetsThreshold(stake, DefaultThreshold)
          [] OTHER -> FALSE

\* Optional: structural well-formedness of a certificate's vote contents.
\* This does not affect acceptance via IsValidCertificate, but is useful as an
\* invariant on pool storage if desired by the model user.
CertificateWellFormed(cert) ==
    LET RelevantVotes ==
            CASE cert.type = "FastFinalizationCert" ->
                     VotesFor(cert.votes, cert.slot, cert.blockHash, {"NotarVote"})
               [] cert.type = "NotarizationCert" ->
                     VotesFor(cert.votes, cert.slot, cert.blockHash, {"NotarVote"})
               [] cert.type = "NotarFallbackCert" ->
                     VotesFor(cert.votes, cert.slot, cert.blockHash, {"NotarVote", "NotarFallbackVote"})
               [] cert.type = "SkipCert" ->
                     VotesFor(cert.votes, cert.slot, NoBlock, {"SkipVote", "SkipFallbackVote"})
               [] cert.type = "FinalizationCert" ->
                     VotesFor(cert.votes, cert.slot, NoBlock, {"FinalVote"})
               [] OTHER -> {}
    IN cert.votes \subseteq RelevantVotes

\* ============================================================================
\* CERTIFICATE PROPERTIES AND IMPLICATIONS
\* ============================================================================

(***************************************************************************
 * IMPORTANT IMPLICATION (from whitepaper):
 * If a FastFinalizationCert exists (80% stake), then a NotarizationCert
 * (60% stake) must also exist, since 80% > 60%.
 ***************************************************************************)
\* Scope/assumption: This implication and the subset relation below are
\* intended for certificates produced under the same local Pool view
\* (same node, same slot view). Across different nodes or times, two
\* certificates for the same (slot, blockHash) might carry different
\* vote sets. The relation reflects constructor behavior when created
\* from a consistent local view. Whitepaper anchors: thresholds
\* (alpenglow-whitepaper.md:501), pool rules (:520, :532), fast⇒notar⇒fallback
\* (:534), and notarized block uniqueness (:855).
FastFinalizationImpliesNotarization(fastCert, notarCert) ==
    /\ fastCert.type = "FastFinalizationCert"
    /\ notarCert.type = "NotarizationCert"
    /\ fastCert.slot = notarCert.slot
    /\ fastCert.blockHash = notarCert.blockHash
    => notarCert.votes \subseteq fastCert.votes

(***************************************************************************
 * IMPLICATION (cascade): Notarization implies Notar-Fallback
 * If a NotarizationCert exists for (slot, block), a NotarFallbackCert for
 * the same (slot, block) also exists (GenerateCertificate ensures this).
 ***************************************************************************)
NotarizationImpliesFallback(notarCert, fallbackCert) ==
    /\ notarCert.type = "NotarizationCert"
    /\ fallbackCert.type = "NotarFallbackCert"
    /\ notarCert.slot = fallbackCert.slot
    /\ notarCert.blockHash = fallbackCert.blockHash

(***************************************************************************
 * SANITY PROPERTY: Fast path excludes fallback votes.
 * Enforced by constructors; IsValidCertificate computes stake from the
 * relevant NotarVote subset, ignoring any extraneous votes.
 ***************************************************************************)
FastFinalizationVotesAreNotar(cert) ==
    cert.type = "FastFinalizationCert" =>
    \A v \in cert.votes : v.type = "NotarVote"

(***************************************************************************
 * LEMMA (documentation): Constructor validity under guard.
 * If the Notar-Fallback guard holds for (votes, s, b), then creating the
 * certificate with those votes yields a valid certificate.
 ***************************************************************************)
FallbackConstructorValidUnderGuard(votes, s, b) ==
    CanCreateNotarFallbackCert(votes, s, b)
        => IsValidCertificate(CreateNotarFallbackCert(votes, s, b))

(***************************************************************************
 * LEMMA (readability): Notarization guard implies Notar-Fallback guard.
 * Matches the paper's implication chain (80% ⇒ 60% notar ⇒ 60% fallback).
 ***************************************************************************)
NotarizationGuardImpliesFallbackGuard(votes, s, b) ==
    CanCreateNotarizationCert(votes, s, b)
        => CanCreateNotarFallbackCert(votes, s, b)

\* Check if two certificates conflict (shouldn't happen!)
\* Note: This predicate treats conflicts only within the same certificate type.
\* Cross-type coherence (e.g., Notarization vs NotarFallback for a slot)
\* is enforced by Pool storage rules and system invariants elsewhere.
\* Whitepaper anchors: storage uniqueness (alpenglow-whitepaper.md:520, :532),
\* uniqueness of notarized block (alpenglow-whitepaper.md:855).
ConflictingCertificates(cert1, cert2) ==
    /\ cert1.slot = cert2.slot           \* Same slot
    /\ cert1.type = cert2.type           \* Same type
    /\ cert1.blockHash # cert2.blockHash \* Different blocks!

\* Companion predicate (for use outside Pool if needed):
\* Detect cross-type conflicts among notar-related certificate types for the
\* same slot. Within Pool, CanStoreCertificate already forbids such states by
\* requiring a single blockHash across Notarization/NotarFallback/FastFinalization
\* for a slot.
CrossTypeNotarConflict(c1, c2) ==
    LET NotarTypes == {"NotarizationCert", "NotarFallbackCert", "FastFinalizationCert"}
    IN /\ c1.slot = c2.slot
       /\ c1.type \in NotarTypes
       /\ c2.type \in NotarTypes
       /\ c1.blockHash # c2.blockHash

\* ============================================================================
\* INVARIANTS FOR VERIFICATION
\* ============================================================================

\* All certificates must be valid
\* Intended domain: apply to Pool's certificates[slot] sets.
AllCertificatesValid(certificates) ==
    \A cert \in certificates : IsValidCertificate(cert)

\* No conflicting certificates should exist
\* Intended domain: apply to Pool's certificates[slot] sets.
NoConflictingCertificates(certificates) ==
    \A cert1, cert2 \in certificates :
        ~ConflictingCertificates(cert1, cert2)

\* Fast finalization implies a corresponding notarization with vote inclusion
\* Intended domain: apply to Pool's certificates[slot] sets.
FastPathImplication(certificates) ==
    \A fastCert \in certificates :
        fastCert.type = "FastFinalizationCert" =>
        \E notarCert \in certificates :
            FastFinalizationImpliesNotarization(fastCert, notarCert)

\* Notarization cascade: every notarization implies a corresponding fallback
NotarizationCascadeImplication(certificates) ==
    \A notarCert \in certificates :
        notarCert.type = "NotarizationCert" =>
        \E fallbackCert \in certificates :
            NotarizationImpliesFallback(notarCert, fallbackCert)

\* Skip vs Block-certificate mutual exclusion (per whitepaper intent):
\* No slot's certificate set may contain both a SkipCert and any
\* block-related certificate (Notarization, NotarFallback, FastFinalization).
SkipVsBlockCertExclusion(certificates) ==
    LET hasSkip == \E c \in certificates : c.type = "SkipCert"
        hasBlock == \E c \in certificates :
                        c.type \in {"NotarizationCert", "NotarFallbackCert", "FastFinalizationCert"}
    IN ~(hasSkip /\ hasBlock)

\* Optional helper: all certificates in a set are structurally well-formed
AllCertificatesWellFormed(certificates) ==
    \A cert \in certificates : CertificateWellFormed(cert)

=============================================================================
