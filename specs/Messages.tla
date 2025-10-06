---------------------------- MODULE Messages ----------------------------


EXTENDS Naturals, FiniteSets

CONSTANTS
    Validators,     \* All validators (stake-weighted in §2.4/§2.5)
    Slots,          \* Natural-numbered slots (§2.4 context; ordered timeline)
    BlockHashes,    \* Abstract block identifiers (cf. Blocks.tla §2.1)
    NoBlock         \* Sentinel for slot-only messages (Table 5 :497)

ASSUME
    /\ Validators # {}                 \* Non-empty validator set
    /\ Slots \subseteq Nat             \* Slots are naturals
    /\ Slots # {}                      \* Non-empty slot set
    /\ \A s \in Slots : 1..s \subseteq Slots  \* Prefix-closed from 1 (whitepaper §1.5 p. 213: s ≥ 1)
    /\ BlockHashes # {}                \* Non-empty block-id universe
    /\ NoBlock \notin BlockHashes      \* Slot-only objects can't be blocks

VoteType == {
    "NotarVote",           \* Initial approval vote for a block
    "NotarFallbackVote",   \* Fallback approval (up to 3 allowed per validator)
    "SkipVote",            \* Initial vote to skip a slot
    "SkipFallbackVote",    \* Fallback skip vote
    "FinalVote"            \* Second-round finalization vote
}

NotarVoteT == "NotarVote"
NotarFallbackVoteT == "NotarFallbackVote"
SkipVoteT == "SkipVote"
SkipFallbackVoteT == "SkipFallbackVote"
FinalVoteT == "FinalVote"

Vote == [
    type: VoteType,                           \* Which of the 5 vote types
    validator: Validators,                    \* Who is voting
    slot: Slots,                             \* Which slot this vote is for
    blockHash: BlockHashes \cup {NoBlock}  \* What block (NoBlock for skips)
]

CreateNotarVote(validator, slot, blockHash) ==
    [type |-> NotarVoteT,
     validator |-> validator,
     slot |-> slot,
     blockHash |-> blockHash]

CreateNotarFallbackVote(validator, slot, blockHash) ==
    [type |-> NotarFallbackVoteT,
     validator |-> validator,
     slot |-> slot,
     blockHash |-> blockHash]

CreateSkipVote(validator, slot) ==
    [type |-> SkipVoteT,
     validator |-> validator,
     slot |-> slot,
     blockHash |-> NoBlock]  \* Skip votes don't reference a block

CreateSkipFallbackVote(validator, slot) ==
    [type |-> SkipFallbackVoteT,
     validator |-> validator,
     slot |-> slot,
     blockHash |-> NoBlock]

CreateFinalVote(validator, slot) ==
    [type |-> FinalVoteT,
     validator |-> validator,
     slot |-> slot,
     blockHash |-> NoBlock]  \* Slot-scoped finalization vote (FinalVote(s))

IsNotarVote(vote) ==
    vote.type \in {NotarVoteT, NotarFallbackVoteT}
IsApprovalVote(vote) == IsNotarVote(vote)

IsSkipVote(vote) ==
    vote.type \in {SkipVoteT, SkipFallbackVoteT}

IsFinalVote(vote) ==
    vote.type = FinalVoteT

IsInitialVote(vote) ==
    vote.type \in {NotarVoteT, SkipVoteT}

IsInitialNotarVote(vote) ==
    vote.type = NotarVoteT


IsVoteForBlock(vote, blockHash) ==
    /\ IsApprovalVote(vote)
    /\ vote.blockHash = blockHash


CertificateType == {
    "FastFinalizationCert",  \* 80% threshold - one round finalization!
    "NotarizationCert",      \* 60% threshold - enables second round
    "NotarFallbackCert",     \* 60% threshold - mixed vote types OK
    "SkipCert",              \* 60% threshold - skip this slot
    "FinalizationCert"       \* 60% threshold - complete slow path
}

Certificate == [
    type: CertificateType,                    \* Which certificate type
    slot: Slots,                              \* Which slot
    blockHash: BlockHashes \cup {NoBlock},  \* Which block (or NoBlock)
    votes: SUBSET Vote                        \* The votes in this certificate
]


IsValidVote(vote) ==
    /\ vote.type \in VoteType
    /\ vote.validator \in Validators
    /\ vote.slot \in Slots
    /\ (IsNotarVote(vote) => vote.blockHash \in BlockHashes)
    /\ (IsSkipVote(vote) \/ IsFinalVote(vote) => vote.blockHash = NoBlock)



THEOREM ApprovalVotesCarryBlockHash ==
    \A v \in Vote :
        (IsValidVote(v) /\ IsApprovalVote(v)) => v.blockHash \in BlockHashes

THEOREM NonBlockVotesUseNoBlock ==
    \A v \in Vote :
        (IsValidVote(v) /\ (IsSkipVote(v) \/ IsFinalVote(v))) => v.blockHash = NoBlock


THEOREM SkipFallbackVoteCreationIsValid ==
    \A v \in Validators, s \in Slots :
        IsValidVote(CreateSkipFallbackVote(v, s))

THEOREM SkipVoteCreationIsValid ==
    \A v \in Validators, s \in Slots :
        IsValidVote(CreateSkipVote(v, s))


=============================================================================
