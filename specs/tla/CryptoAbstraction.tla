---------------------------- MODULE CryptoAbstraction ----------------------------
EXTENDS Common, Stake

CONSTANTS
    VoteTypes

VoteTypes_Default ==
    {"NotarVote", "FinalVote", "SkipVote"}

Vote(Blocks) ==
    [validator: V,
     slot: {"s0"},
     type: VoteTypes,
     hash: Blocks \union {"-"}]

NotarVote(v, s, h) ==
    [validator |-> v, slot |-> s, type |-> "NotarVote", hash |-> h]

FinalVote(v, s) ==
    [validator |-> v, slot |-> s, type |-> "FinalVote", hash |-> "-"]

SkipVote(v, s) ==
    [validator |-> v, slot |-> s, type |-> "SkipVote", hash |-> "-"]

GetVoteValidator(vote) ==
    vote.validator

GetVoteSlot(vote) ==
    vote.slot

GetVoteType(vote) ==
    vote.type

GetVoteHash(vote) ==
    vote.hash

VoteKey(vote) ==
    <<vote.validator, vote.slot, vote.type>>

IsNotarVote(vote) ==
    vote.type = "NotarVote"

IsFinalVote(vote) ==
    vote.type = "FinalVote"

IsSkipVote(vote) ==
    vote.type = "SkipVote"

VotesForSameBlock(vote1, vote2) ==
    /\ IsNotarVote(vote1)
    /\ IsNotarVote(vote2)
    /\ vote1.hash = vote2.hash

VotesForSameSlot(vote1, vote2) ==
    vote1.slot = vote2.slot

GetSigners(votes) ==
    {v.validator : v \in votes}

ValidVote(vote, Blocks) ==
    /\ vote.validator \in V
    /\ vote.slot = "s0"
    /\ vote.type \in VoteTypes
    /\ (IsNotarVote(vote) => vote.hash \in Blocks)
    /\ (~IsNotarVote(vote) => vote.hash = "-")

=======================================================================