---------------------------- MODULE Certificates ----------------------------
(***************************************************************************
 * CERTIFICATE GENERATION AND STAKE AGGREGATION FOR ALPENGLOW
 * 
 * This module handles the creation of certificates from votes, implementing
 * the stake counting rules and threshold requirements.
 * 
 * MAPS TO WHITEPAPER:
 * - Definition 11, Table 6: Certificate types and thresholds
 * - Definition 12: Vote storage and stake counting rules
 * - Definition 13: Certificate generation and uniqueness
 * 
 * KEY SAFETY PROPERTIES:
 * - Fast path requires 80% stake (one-round finalization)
 * - Slow path requires 60% stake (two-round finalization)
 * - Each validator counted ONCE per slot (even with multiple votes)
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
 * Fast-Finalization Certificate (Table 6, row 1)
 * Requirements:
 * - Vote type: NotarVote only
 * - Threshold: ≥80% of total stake
 * - Effect: Immediate finalization in one round!
 ***************************************************************************)
CanCreateFastFinalizationCert(votes, slot, blockHash) ==
    LET relevantVotes == {v \in votes : 
        /\ v.type = "NotarVote"
        /\ v.slot = slot
        /\ v.blockHash = blockHash}
    IN MeetsThreshold(StakeFromVotes(relevantVotes), 80)

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
    IN MeetsThreshold(StakeFromVotes(relevantVotes), 60)

(***************************************************************************
 * Notar-Fallback Certificate (Table 6, row 3)
 * Requirements:
 * - Vote types: NotarVote OR NotarFallbackVote (mixed OK!)
 * - Threshold: ≥60% of total stake
 * - Effect: Fallback notarization when not everyone agrees initially
 ***************************************************************************)
CanCreateNotarFallbackCert(votes, slot, blockHash) ==
    LET relevantVotes == {v \in votes :
        /\ v.type \in {"NotarVote", "NotarFallbackVote"}
        /\ v.slot = slot
        /\ v.blockHash = blockHash}
    IN MeetsThreshold(StakeFromVotes(relevantVotes), 60)

(***************************************************************************
 * Skip Certificate (Table 6, row 4)
 * Requirements:
 * - Vote types: SkipVote OR SkipFallbackVote (mixed OK!)
 * - Threshold: ≥60% of total stake
 * - Effect: Slot is skipped, move to next slot
 ***************************************************************************)
CanCreateSkipCert(votes, slot) ==
    LET relevantVotes == {v \in votes :
        /\ v.type \in {"SkipVote", "SkipFallbackVote"}
        /\ v.slot = slot}
    IN MeetsThreshold(StakeFromVotes(relevantVotes), 60)

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
    IN MeetsThreshold(StakeFromVotes(relevantVotes), 60)

\* ============================================================================
\* CERTIFICATE CREATION FUNCTIONS
\* These actually create certificate objects when thresholds are met
\* ============================================================================

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
    [type |-> "NotarFallbackCert",
     slot |-> slot,
     blockHash |-> blockHash,
     votes |-> {v \in votes : 
        v.type \in {"NotarVote", "NotarFallbackVote"} /\ 
        v.slot = slot /\ v.blockHash = blockHash}]

CreateSkipCert(votes, slot) ==
    [type |-> "SkipCert",
     slot |-> slot,
     blockHash |-> NoBlock,
     votes |-> {v \in votes : 
        v.type \in {"SkipVote", "SkipFallbackVote"} /\ v.slot = slot}]

CreateFinalizationCert(votes, slot) ==
    [type |-> "FinalizationCert",
     slot |-> slot,
     blockHash |-> NoBlock,
     votes |-> {v \in votes : 
        v.type = "FinalVote" /\ v.slot = slot}]

\* ============================================================================
\* CERTIFICATE VALIDATION
\* ============================================================================

\* Check if a certificate is valid (has required threshold)
IsValidCertificate(cert) ==
    LET stake == StakeFromVotes(cert.votes)
    IN /\ cert.type \in CertificateType
       /\ cert.slot \in Slots
       /\ CASE cert.type = "FastFinalizationCert" -> 
               /\ cert.blockHash \in BlockHashes
               /\ MeetsThreshold(stake, 80)  \* 80% for fast path
          [] cert.type \in {"NotarizationCert", "NotarFallbackCert"} ->
               /\ cert.blockHash \in BlockHashes
               /\ MeetsThreshold(stake, 60)  \* 60% for notarization
          [] cert.type = "SkipCert" ->
               /\ cert.blockHash = NoBlock
               /\ MeetsThreshold(stake, 60)  \* 60% for skip
          [] cert.type = "FinalizationCert" ->
               /\ cert.blockHash = NoBlock
               /\ MeetsThreshold(stake, 60)  \* 60% for finalization
          [] OTHER -> FALSE

\* ============================================================================
\* CERTIFICATE PROPERTIES AND IMPLICATIONS
\* ============================================================================

(***************************************************************************
 * IMPORTANT IMPLICATION (from whitepaper):
 * If a FastFinalizationCert exists (80% stake), then a NotarizationCert
 * (60% stake) must also exist, since 80% > 60%.
 ***************************************************************************)
FastFinalizationImpliesNotarization(fastCert, notarCert) ==
    /\ fastCert.type = "FastFinalizationCert"
    /\ notarCert.type = "NotarizationCert"
    /\ fastCert.slot = notarCert.slot
    /\ fastCert.blockHash = notarCert.blockHash
    => notarCert.votes \subseteq fastCert.votes

\* Check if two certificates conflict (shouldn't happen!)
ConflictingCertificates(cert1, cert2) ==
    /\ cert1.slot = cert2.slot           \* Same slot
    /\ cert1.type = cert2.type           \* Same type
    /\ cert1.blockHash # cert2.blockHash \* Different blocks!

\* ============================================================================
\* INVARIANTS FOR VERIFICATION
\* ============================================================================

\* All certificates must be valid
AllCertificatesValid(certificates) ==
    \A cert \in certificates : IsValidCertificate(cert)

\* No conflicting certificates should exist
NoConflictingCertificates(certificates) ==
    \A cert1, cert2 \in certificates :
        ~ConflictingCertificates(cert1, cert2)

\* Fast finalization implies notarization exists
FastPathImplication(certificates) ==
    \A fastCert \in certificates :
        fastCert.type = "FastFinalizationCert" =>
        \E notarCert \in certificates :
            /\ notarCert.type = "NotarizationCert"
            /\ notarCert.slot = fastCert.slot
            /\ notarCert.blockHash = fastCert.blockHash

=============================================================================