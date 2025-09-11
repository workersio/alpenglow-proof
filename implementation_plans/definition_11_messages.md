# Definition 11: Messages Implementation Plan

## Definition
Alpenglow uses voting and certificate messages listed in Tables 5 and 6.

**Table 5: Alpenglow's voting messages**
| Vote Type | Object |
|---|---|
| Notarization Vote | NotarVote(slot(b), hash(b)) |
| Notar-Fallback Vote | NotarFallbackVote(slot(b), hash(b)) |
| Skip Vote | SkipVote(s) |
| Skip-Fallback Vote | SkipFallbackVote(s) |
| Finalization Vote | FinalVote(s) |

**Table 6: Alpenglow's certificate messages**
| Certificate Type | Aggregated Votes | Condition |
|---|---|---|
| Fast-Finalization Cert. | NotarVote | Σ ≥ 80% |
| Notarization Cert. | NotarVote | Σ ≥ 60% |
| Notar-Fallback Cert. | NotarVote or NotarFallbackVote | Σ ≥ 60% |
| Skip Cert. | SkipVote or SkipFallbackVote | Σ ≥ 60% |
| Finalization Cert. | FinalVote | Σ ≥ 60% |

Where Σ is the cumulative stake of the aggregated votes.

## TLA+ Implementation Plan

### Constants
```tla
CONSTANTS
    Validators,      \* Set of validator nodes
    Slots,          \* Set of possible slot numbers
    BlockHashes,    \* Set of possible block hashes
    Signatures,     \* Set of possible signatures
    MinFastFinalizationStake,  \* 80% threshold
    MinCertificationStake      \* 60% threshold
```

### Vote Message Types
```tla
\* Notarization vote for a specific block
NotarVote(validator, slot, blockHash) ==
    [type |-> "NotarVote",
     validator |-> validator,
     slot |-> slot,
     blockHash |-> blockHash,
     signature |-> SignVote(validator, "NotarVote", slot, blockHash)]

\* Notar-fallback vote for a specific block
NotarFallbackVote(validator, slot, blockHash) ==
    [type |-> "NotarFallbackVote",
     validator |-> validator,
     slot |-> slot,
     blockHash |-> blockHash,
     signature |-> SignVote(validator, "NotarFallbackVote", slot, blockHash)]

\* Skip vote for a slot
SkipVote(validator, slot) ==
    [type |-> "SkipVote",
     validator |-> validator,
     slot |-> slot,
     signature |-> SignVote(validator, "SkipVote", slot, "")]

\* Skip-fallback vote for a slot
SkipFallbackVote(validator, slot) ==
    [type |-> "SkipFallbackVote",
     validator |-> validator,
     slot |-> slot,
     signature |-> SignVote(validator, "SkipFallbackVote", slot, "")]

\* Finalization vote for a slot
FinalVote(validator, slot) ==
    [type |-> "FinalVote",
     validator |-> validator,
     slot |-> slot,
     signature |-> SignVote(validator, "FinalVote", slot, "")]
```

### Certificate Message Types
```tla
\* Fast-finalization certificate (80% notarization votes)
FastFinalizationCert(slot, blockHash, votes) ==
    [type |-> "FastFinalizationCert",
     slot |-> slot,
     blockHash |-> blockHash,
     votes |-> votes,
     aggregatedStake |-> CalculateStake(votes)]

\* Notarization certificate (60% notarization votes)
NotarizationCert(slot, blockHash, votes) ==
    [type |-> "NotarizationCert",
     slot |-> slot,
     blockHash |-> blockHash,
     votes |-> votes,
     aggregatedStake |-> CalculateStake(votes)]

\* Notar-fallback certificate (60% notar/notar-fallback votes)
NotarFallbackCert(slot, blockHash, votes) ==
    [type |-> "NotarFallbackCert",
     slot |-> slot,
     blockHash |-> blockHash,
     votes |-> votes,
     aggregatedStake |-> CalculateStake(votes)]

\* Skip certificate (60% skip/skip-fallback votes)
SkipCert(slot, votes) ==
    [type |-> "SkipCert",
     slot |-> slot,
     votes |-> votes,
     aggregatedStake |-> CalculateStake(votes)]

\* Finalization certificate (60% finalization votes)
FinalizationCert(slot, votes) ==
    [type |-> "FinalizationCert",
     slot |-> slot,
     votes |-> votes,
     aggregatedStake |-> CalculateStake(votes)]
```

### Message Validation Functions
```tla
\* Verify vote signature
VerifyVoteSignature(vote) ==
    \* Abstract signature verification
    /\ vote.validator \in Validators
    /\ vote.signature \in Signatures
    /\ ValidateSignature(vote.signature, vote.validator, vote)

\* Check if vote is for correct slot and type
IsValidVoteStructure(vote) ==
    /\ vote.type \in {"NotarVote", "NotarFallbackVote", "SkipVote", 
                      "SkipFallbackVote", "FinalVote"}
    /\ vote.validator \in Validators
    /\ vote.slot \in Slots
    /\ (vote.type \in {"NotarVote", "NotarFallbackVote"} => 
        vote.blockHash \in BlockHashes)

\* Check if certificate meets stake threshold
MeetsStakeThreshold(cert) ==
    CASE cert.type = "FastFinalizationCert" -> 
         cert.aggregatedStake >= MinFastFinalizationStake
    [] cert.type \in {"NotarizationCert", "NotarFallbackCert", 
                      "SkipCert", "FinalizationCert"} ->
         cert.aggregatedStake >= MinCertificationStake
    [] OTHER -> FALSE
```

### Vote and Certificate Creation
```tla
\* Calculate total stake from a set of votes
CalculateStake(votes) ==
    LET validators == {vote.validator : vote \in votes}
    IN StakeSum(validators)

\* Check if votes are sufficient for fast-finalization certificate
CanCreateFastFinalizationCert(votes, slot, blockHash) ==
    /\ \A vote \in votes : 
        /\ vote.type = "NotarVote"
        /\ vote.slot = slot
        /\ vote.blockHash = blockHash
        /\ VerifyVoteSignature(vote)
    /\ CalculateStake(votes) >= MinFastFinalizationStake

\* Check if votes are sufficient for notarization certificate
CanCreateNotarizationCert(votes, slot, blockHash) ==
    /\ \A vote \in votes : 
        /\ vote.type = "NotarVote"
        /\ vote.slot = slot
        /\ vote.blockHash = blockHash
        /\ VerifyVoteSignature(vote)
    /\ CalculateStake(votes) >= MinCertificationStake

\* Check if votes are sufficient for notar-fallback certificate
CanCreateNotarFallbackCert(votes, slot, blockHash) ==
    /\ \A vote \in votes : 
        /\ vote.type \in {"NotarVote", "NotarFallbackVote"}
        /\ vote.slot = slot
        /\ vote.blockHash = blockHash
        /\ VerifyVoteSignature(vote)
    /\ CalculateStake(votes) >= MinCertificationStake

\* Check if votes are sufficient for skip certificate
CanCreateSkipCert(votes, slot) ==
    /\ \A vote \in votes : 
        /\ vote.type \in {"SkipVote", "SkipFallbackVote"}
        /\ vote.slot = slot
        /\ VerifyVoteSignature(vote)
    /\ CalculateStake(votes) >= MinCertificationStake

\* Check if votes are sufficient for finalization certificate
CanCreateFinalizationCert(votes, slot) ==
    /\ \A vote \in votes : 
        /\ vote.type = "FinalVote"
        /\ vote.slot = slot
        /\ VerifyVoteSignature(vote)
    /\ CalculateStake(votes) >= MinCertificationStake
```

### Message Classification
```tla
\* Check message type
IsVoteMessage(msg) ==
    msg.type \in {"NotarVote", "NotarFallbackVote", "SkipVote", 
                  "SkipFallbackVote", "FinalVote"}

IsCertificateMessage(msg) ==
    msg.type \in {"FastFinalizationCert", "NotarizationCert", 
                  "NotarFallbackCert", "SkipCert", "FinalizationCert"}

\* Check if vote is for a specific block
IsBlockVote(vote) ==
    vote.type \in {"NotarVote", "NotarFallbackVote"}

\* Check if vote is slot-only
IsSlotOnlyVote(vote) ==
    vote.type \in {"SkipVote", "SkipFallbackVote", "FinalVote"}
```

### Abstract Signature Functions
```tla
\* Abstract signature creation
SignVote(validator, voteType, slot, blockHash) ==
    "sig_" \o ToString(validator) \o "_" \o voteType \o "_" \o 
    ToString(slot) \o "_" \o ToString(blockHash)

\* Abstract signature validation
ValidateSignature(signature, validator, message) ==
    TRUE  \* Placeholder for cryptographic verification
```

## Dependencies
- **Definition 3 (block)**: For slot(b) and hash(b) functions
- **Stake system**: For validator stake calculations and thresholds
- **Digital signatures**: For vote authenticity
- **Pool data structure**: For storing and managing votes/certificates

## Implementation Notes
1. Each vote must be signed by the validator casting it
2. Certificates aggregate votes and verify stake thresholds
3. Fast-finalization requires 80% stake, all others require 60%
4. Votes reference either blocks (with hash) or just slots
5. Certificate creation is deterministic given sufficient valid votes
6. The stake calculation must account for validator stake weights
7. Signature verification ensures vote authenticity and non-repudiation

## Testing Properties
```tla
\* Property: Valid votes have correct structure
ValidVoteStructure ==
    \A vote \in VoteMessages :
        IsValidVoteStructure(vote) => VerifyVoteSignature(vote)

\* Property: Certificates meet stake thresholds
CertificateStakeThreshold ==
    \A cert \in CertificateMessages :
        IsCertificateMessage(cert) => MeetsStakeThreshold(cert)

\* Property: Fast-finalization implies notarization
FastImpliesNotar ==
    \A votes \in SUBSET VoteMessages, slot \in Slots, hash \in BlockHashes :
        CanCreateFastFinalizationCert(votes, slot, hash) =>
            CanCreateNotarizationCert(votes, slot, hash)

\* Property: Notarization implies notar-fallback
NotarImpliesNotarFallback ==
    \A votes \in SUBSET VoteMessages, slot \in Slots, hash \in BlockHashes :
        CanCreateNotarizationCert(votes, slot, hash) =>
            CanCreateNotarFallbackCert(votes, slot, hash)

\* Property: Vote uniqueness per validator per slot
VoteUniqueness ==
    \A v \in Validators, s \in Slots :
        \A vote1, vote2 \in VoteMessages :
            /\ vote1.validator = v /\ vote1.slot = s
            /\ vote2.validator = v /\ vote2.slot = s
            /\ vote1.type = vote2.type =>
                vote1 = vote2
```