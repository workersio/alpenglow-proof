# Definition 13: Certificates Implementation Plan

## Definition
Pool generates, stores and broadcasts certificates:
- When enough votes (see Table 6) are received, the respective certificate is generated.
- When a received or constructed certificate is newly added to Pool, the certificate is broadcast to all other nodes.
- A single (received or constructed) certificate of each type corresponding to the given block/slot is stored in Pool.

## TLA+ Implementation Plan

### Constants
```tla
CONSTANTS
    Validators,            \* Set of validator nodes
    Slots,                \* Set of slot numbers
    BlockHashes,          \* Set of block hashes
    CertificateTypes,     \* Set of certificate types
    StakeThreshold80,     \* 80% threshold for fast-finalization
    StakeThreshold60      \* 60% threshold for other certificates
```

### Variables
```tla
VARIABLES
    poolVotes,            \* Vote storage from Definition 12
    poolCertificates,     \* Set of generated certificates
    broadcastQueue,       \* Certificates pending broadcast
    receivedCertificates  \* Certificates received from other nodes
```

### Certificate Generation Functions
```tla
\* Generate fast-finalization certificate (80% NotarVotes)
TryGenerateFastFinalizationCert(slot, blockHash) ==
    LET notarVotes == GetNotarVotesForBlock(slot, blockHash)
        totalStake == CalculateStake(notarVotes)
        cert == FastFinalizationCert(slot, blockHash, notarVotes)
    IN IF /\ totalStake >= StakeThreshold80
          /\ ~HasCertificate("FastFinalizationCert", slot, blockHash)
       THEN AddCertificateToPool(cert)
       ELSE UNCHANGED poolCertificates

\* Generate notarization certificate (60% NotarVotes)
TryGenerateNotarizationCert(slot, blockHash) ==
    LET notarVotes == GetNotarVotesForBlock(slot, blockHash)
        totalStake == CalculateStake(notarVotes)
        cert == NotarizationCert(slot, blockHash, notarVotes)
    IN IF /\ totalStake >= StakeThreshold60
          /\ ~HasCertificate("NotarizationCert", slot, blockHash)
       THEN AddCertificateToPool(cert)
       ELSE UNCHANGED poolCertificates

\* Generate notar-fallback certificate (60% Notar + NotarFallback votes)
TryGenerateNotarFallbackCert(slot, blockHash) ==
    LET notarVotes == GetNotarVotesForBlock(slot, blockHash)
        fallbackVotes == GetNotarFallbackVotesForBlock(slot, blockHash)
        combinedVotes == notarVotes \union fallbackVotes
        totalStake == CalculateStake(combinedVotes)
        cert == NotarFallbackCert(slot, blockHash, combinedVotes)
    IN IF /\ totalStake >= StakeThreshold60
          /\ ~HasCertificate("NotarFallbackCert", slot, blockHash)
       THEN AddCertificateToPool(cert)
       ELSE UNCHANGED poolCertificates

\* Generate skip certificate (60% Skip + SkipFallback votes)
TryGenerateSkipCert(slot) ==
    LET skipVotes == GetSkipVotesForSlot(slot)
        fallbackVotes == GetSkipFallbackVotesForSlot(slot)
        combinedVotes == skipVotes \union fallbackVotes
        totalStake == CalculateStake(combinedVotes)
        cert == SkipCert(slot, combinedVotes)
    IN IF /\ totalStake >= StakeThreshold60
          /\ ~HasCertificate("SkipCert", slot, "")
       THEN AddCertificateToPool(cert)
       ELSE UNCHANGED poolCertificates

\* Generate finalization certificate (60% FinalizationVotes)
TryGenerateFinalizationCert(slot) ==
    LET finalVotes == GetFinalizationVotesForSlot(slot)
        totalStake == CalculateStake(finalVotes)
        cert == FinalizationCert(slot, finalVotes)
    IN IF /\ totalStake >= StakeThreshold60
          /\ ~HasCertificate("FinalizationCert", slot, "")
       THEN AddCertificateToPool(cert)
       ELSE UNCHANGED poolCertificates
```

### Certificate Management
```tla
\* Add certificate to pool and broadcast queue
AddCertificateToPool(cert) ==
    /\ poolCertificates' = poolCertificates \union {cert}
    /\ broadcastQueue' = broadcastQueue \union {cert}

\* Check if certificate already exists in pool
HasCertificate(certType, slot, blockHash) ==
    \E cert \in poolCertificates :
        /\ cert.type = certType
        /\ cert.slot = slot
        /\ (certType \in {"FastFinalizationCert", "NotarizationCert", "NotarFallbackCert"} =>
            cert.blockHash = blockHash)

\* Get certificate by type and identifiers
GetCertificate(certType, slot, blockHash) ==
    CHOOSE cert \in poolCertificates :
        /\ cert.type = certType
        /\ cert.slot = slot
        /\ (certType \in {"FastFinalizationCert", "NotarizationCert", "NotarFallbackCert"} =>
            cert.blockHash = blockHash)

\* Check if certificate is valid
IsValidCertificate(cert) ==
    /\ cert.type \in CertificateTypes
    /\ cert.slot \in Slots
    /\ MeetsStakeThreshold(cert)
    /\ AllVotesValid(cert.votes)
```

### Certificate Generation Orchestrator
```tla
\* Try to generate all possible certificates
GenerateCertificates(possibleBlocks) ==
    /\ \A slot \in Slots, blockHash \in possibleBlocks :
        /\ TryGenerateFastFinalizationCert(slot, blockHash)
        /\ TryGenerateNotarizationCert(slot, blockHash) 
        /\ TryGenerateNotarFallbackCert(slot, blockHash)
    /\ \A slot \in Slots :
        /\ TryGenerateSkipCert(slot)
        /\ TryGenerateFinalizationCert(slot)

\* Main certificate generation action
GenerateCertsAction ==
    GenerateCertificates(BlockHashes)
```

### Certificate Broadcasting
```tla
\* Broadcast pending certificates
BroadcastCertificates ==
    /\ broadcastQueue # {}
    /\ LET cert == CHOOSE c \in broadcastQueue : TRUE
       IN /\ SendToAllNodes(cert)
          /\ broadcastQueue' = broadcastQueue \ {cert}
          /\ UNCHANGED <<poolVotes, poolCertificates, receivedCertificates>>

\* Receive certificate from another node
ReceiveCertificate(cert) ==
    /\ IsValidCertificate(cert)
    /\ cert \notin poolCertificates
    /\ poolCertificates' = poolCertificates \union {cert}
    /\ receivedCertificates' = receivedCertificates \union {cert}
    /\ broadcastQueue' = broadcastQueue \union {cert}  \* Re-broadcast
    /\ UNCHANGED poolVotes

\* Abstract network operations
SendToAllNodes(cert) == TRUE  \* Placeholder for network broadcast
```

### Certificate Hierarchy Properties
```tla
\* Fast-finalization implies notarization
FastImpliesNotar ==
    \A cert \in poolCertificates :
        cert.type = "FastFinalizationCert" =>
            HasCertificate("NotarizationCert", cert.slot, cert.blockHash)

\* Notarization implies notar-fallback
NotarImpliesNotarFallback ==
    \A cert \in poolCertificates :
        cert.type = "NotarizationCert" =>
            HasCertificate("NotarFallbackCert", cert.slot, cert.blockHash)

\* Check certificate hierarchy consistency
CertificateHierarchyConsistent ==
    /\ FastImpliesNotar
    /\ NotarImpliesNotarFallback
```

### Utility Functions
```tla
\* Initialize certificate management
InitCertificates ==
    /\ poolCertificates = {}
    /\ broadcastQueue = {}
    /\ receivedCertificates = {}

\* Get all certificates for a slot
GetCertificatesForSlot(slot) ==
    {cert \in poolCertificates : cert.slot = slot}

\* Check if all votes in certificate are valid
AllVotesValid(votes) ==
    \A vote \in votes : 
        /\ IsValidVoteStructure(vote)
        /\ VerifyVoteSignature(vote)

\* Get certificate stake threshold based on type
GetCertificateThreshold(certType) ==
    CASE certType = "FastFinalizationCert" -> StakeThreshold80
    [] certType \in {"NotarizationCert", "NotarFallbackCert", 
                     "SkipCert", "FinalizationCert"} -> StakeThreshold60
    [] OTHER -> 0
```

## Dependencies
- **Definition 11 (messages)**: For certificate and vote types
- **Definition 12 (storing votes)**: For vote retrieval from pool
- **Stake calculation system**: For verifying thresholds
- **Network layer**: For certificate broadcasting

## Implementation Notes
1. Certificate generation is triggered when sufficient votes are collected
2. Only one certificate per type per slot/block is stored
3. All newly added certificates are automatically broadcast
4. Certificate hierarchy: Fast-finalization ⊃ Notarization ⊃ Notar-fallback
5. Received certificates are validated before adding to pool
6. Broadcasting ensures network-wide certificate propagation

## Testing Properties
```tla
\* Property: Certificates meet stake thresholds
CertificatesHaveStake ==
    \A cert \in poolCertificates :
        cert.aggregatedStake >= GetCertificateThreshold(cert.type)

\* Property: Single certificate per type per slot/block
UniqueCertificatesPerSlotBlock ==
    \A cert1, cert2 \in poolCertificates :
        /\ cert1.type = cert2.type
        /\ cert1.slot = cert2.slot
        /\ (cert1.type \in {"FastFinalizationCert", "NotarizationCert", "NotarFallbackCert"} =>
            cert1.blockHash = cert2.blockHash) =>
        cert1 = cert2

\* Property: Certificate generation is deterministic
CertificateGenerationDeterministic ==
    \A votes \in SUBSET VoteMessage, slot \in Slots, blockHash \in BlockHashes :
        CalculateStake(votes) >= StakeThreshold60 =>
            \E cert \in poolCertificates : 
                cert.votes = votes /\ cert.slot = slot

\* Property: Broadcast queue eventually empties
BroadcastQueueEventuallyEmpty ==
    broadcastQueue # {} ~> broadcastQueue = {}
```