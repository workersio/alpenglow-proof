---------------------------- MODULE Messages ----------------------------
(***************************************************************************
 * MESSAGE TYPES FOR ALPENGLOW CONSENSUS PROTOCOL
 *
 * Encodes the voting and certification objects enumerated in Whitepaper
 * §2.4 (Definition 11, Tables 5–6). Each constructor mirrors the notation
 * `NotarVote`, `SkipVote`, etc., so later modules can reason about the
 * fast (≥80%) and slow (≥60%) finalization paths.
 ***************************************************************************)

EXTENDS Naturals, FiniteSets

\* ============================================================================
\* CONSTANTS
\* ============================================================================

CONSTANTS
    Validators,     \* Set of all validator nodes in the network
    Slots,          \* Natural numbers representing time slots
    BlockHashes,    \* Set of possible block identifiers
    NoBlock         \* Special value meaning "no block" (for skip votes)

\* Basic assumptions about our constants
ASSUME
    /\ Validators # {}           \* At least one validator exists
    /\ Slots \subseteq Nat       \* Slots are natural numbers
    /\ BlockHashes # {}          \* At least one possible block hash
    /\ NoBlock \notin BlockHashes \* NoBlock is distinct from real blocks

\* ============================================================================
\* VOTE TYPES (Definition 11, Table 5 from whitepaper)
\* ============================================================================

(***************************************************************************
 * The five vote types in Alpenglow:
 * 
 * 1. NotarVote: "I approve this block" (first vote)
 * 2. NotarFallbackVote: "Others seem to approve, I'll go along" (safety vote)
 * 3. SkipVote: "This slot timed out, skip it" (first skip)
 * 4. SkipFallbackVote: "Others want to skip, I'll go along" (safety skip)
 * 5. FinalVote: "This block was notarized, finalize it" (second round)
 ***************************************************************************)

VoteType == {
    "NotarVote",           \* Initial approval vote for a block
    "NotarFallbackVote",   \* Fallback approval (up to 3 allowed per validator)
    "SkipVote",            \* Initial vote to skip a slot
    "SkipFallbackVote",    \* Fallback skip vote
    "FinalVote"            \* Second-round finalization vote
}

\* Structure of a vote message
Vote == [
    type: VoteType,                           \* Which of the 5 vote types
    validator: Validators,                    \* Who is voting
    slot: Slots,                             \* Which slot this vote is for
    blockHash: BlockHashes \union {NoBlock}  \* What block (NoBlock for skips)
]

\* ============================================================================
\* VOTE CREATION HELPERS
\* These functions create properly formatted vote messages
\* ============================================================================

\* Create a NotarVote: "I approve block 'blockHash' in slot 'slot'"
CreateNotarVote(validator, slot, blockHash) ==
    [type |-> "NotarVote",
     validator |-> validator,
     slot |-> slot,
     blockHash |-> blockHash]

\* Create a NotarFallbackVote: "I'll go along with notarizing this block"
CreateNotarFallbackVote(validator, slot, blockHash) ==
    [type |-> "NotarFallbackVote",
     validator |-> validator,
     slot |-> slot,
     blockHash |-> blockHash]

\* Create a SkipVote: "Let's skip this slot"
CreateSkipVote(validator, slot) ==
    [type |-> "SkipVote",
     validator |-> validator,
     slot |-> slot,
     blockHash |-> NoBlock]  \* Skip votes don't reference a block

\* Create a SkipFallbackVote: "I'll go along with skipping"
CreateSkipFallbackVote(validator, slot) ==
    [type |-> "SkipFallbackVote",
     validator |-> validator,
     slot |-> slot,
     blockHash |-> NoBlock]

\* Create a FinalVote: "This notarized block should be finalized"
CreateFinalVote(validator, slot) ==
    [type |-> "FinalVote",
     validator |-> validator,
     slot |-> slot,
     blockHash |-> NoBlock]  \* Final votes don't need block hash

\* ============================================================================
\* VOTE CLASSIFICATION HELPERS
\* These help categorize and query votes
\* ============================================================================

\* Is this a vote to approve a block (notar or notar-fallback)?
IsNotarVote(vote) ==
    vote.type \in {"NotarVote", "NotarFallbackVote"}

\* Is this a vote to skip a slot?
IsSkipVote(vote) ==
    vote.type \in {"SkipVote", "SkipFallbackVote"}

\* Is this an initial vote (first vote a validator casts in a slot)?
\* IMPORTANT: Validators can only cast ONE initial vote per slot (Lemma 20)
IsInitialVote(vote) ==
    vote.type \in {"NotarVote", "SkipVote"}

\* Is this a fallback vote (safety mechanism)?
IsFallbackVote(vote) ==
    vote.type \in {"NotarFallbackVote", "SkipFallbackVote"}

\* Does this vote support a specific block?
IsVoteForBlock(vote, blockHash) ==
    /\ IsNotarVote(vote)
    /\ vote.blockHash = blockHash

\* ============================================================================
\* CERTIFICATE TYPES (Definition 11, Table 6 from whitepaper)
\* ============================================================================

(***************************************************************************
 * Certificates are collections of votes that meet stake thresholds:
 * 
 * 1. FastFinalizationCert: ≥80% NotarVotes → instant finalization!
 * 2. NotarizationCert: ≥60% NotarVotes → block is notarized
 * 3. NotarFallbackCert: ≥60% mixed notar votes → fallback notarization
 * 4. SkipCert: ≥60% skip votes → slot is skipped
 * 5. FinalizationCert: ≥60% FinalVotes → slow-path finalization
 ***************************************************************************)

CertificateType == {
    "FastFinalizationCert",  \* 80% threshold - one round finalization!
    "NotarizationCert",      \* 60% threshold - enables second round
    "NotarFallbackCert",     \* 60% threshold - mixed vote types OK
    "SkipCert",              \* 60% threshold - skip this slot
    "FinalizationCert"       \* 60% threshold - complete slow path
}

\* Structure of a certificate
Certificate == [
    type: CertificateType,                    \* Which certificate type
    slot: Slots,                              \* Which slot
    blockHash: BlockHashes \union {NoBlock},  \* Which block (or NoBlock)
    votes: SUBSET Vote                        \* The votes in this certificate
]

\* ============================================================================
\* VOTE VALIDATION
\* ============================================================================

\* Check if a vote is properly formatted and valid
IsValidVote(vote) ==
    /\ vote.type \in VoteType
    /\ vote.validator \in Validators
    /\ vote.slot \in Slots
    /\ (IsNotarVote(vote) => vote.blockHash \in BlockHashes)
    /\ (IsSkipVote(vote) \/ vote.type = "FinalVote" => vote.blockHash = NoBlock)

\* Check if two votes conflict (violate protocol rules)
\* IMPORTANT: This helps verify Lemma 20 - validators vote once per slot
ConflictingVotes(vote1, vote2) ==
    /\ vote1.validator = vote2.validator  \* Same validator
    /\ vote1.slot = vote2.slot            \* Same slot
    /\ IsInitialVote(vote1)               \* Both are initial votes
    /\ IsInitialVote(vote2)
    /\ vote1.type # vote2.type            \* But different types!

\* ============================================================================
\* QUERY FUNCTIONS
\* These help analyze sets of votes
\* ============================================================================

\* Get all votes of a specific type from a set
GetVotesByType(votes, voteType) ==
    {v \in votes : v.type = voteType}

\* Get all votes for a specific slot
GetVotesBySlot(votes, slot) ==
    {v \in votes : v.slot = slot}

\* Get all votes from a specific validator
GetVotesByValidator(votes, validator) ==
    {v \in votes : v.validator = validator}

\* Get all votes supporting a specific block
GetVotesForBlock(votes, slot, blockHash) ==
    {v \in votes : 
        /\ v.slot = slot
        /\ IsVoteForBlock(v, blockHash)}

=============================================================================
