# Solana Alpenglow Consensus

## Increased Bandwidth, Reduced Latency

## Quentin Kniep Jakub Sliwinski Roger Wattenhofer

## Anza

## White Paper v1.1, July 22, 2025

```
Abstract
In this paper we describe and analyze Alpenglow, a consensus protocol
tailored for a global high-performance proof-of-stake blockchain.
The voting componentVotorfinalizes blocks in a single round of voting
if 80% of the stake is participating, and in two rounds if only 60% of
the stake is responsive. These voting modes are performed concurrently,
such that finalization takes min(δ80%, 2 δ60%) time after a block has been
distributed.
The fast block distribution componentRotoris based on erasure cod-
ing. Rotor utilizes the bandwidth of participating nodes proportionally
to their stake, alleviating the leader bottleneck for high throughput. As
a result, total available bandwidth is used asymptotically optimally.
Alpenglow features a distinctive “20+20” resilience, wherein the pro-
tocol can tolerate harsh network conditions and an adversary controlling
20% of the stake. Anadditional20% of the stake can be offline if the
network assumptions are stronger.
```
## 1 Introduction

“I think there is a world market for maybe five computers.” – This quote
is often attributed to Thomas J. Watson, president of IBM. It is disputed
whether Watson ever said this, but it was certainly in the spirit of the time
as similar quotes exist, e.g., by Howard H. Aiken. The quote was often made
fun of in the last decades, but if we move one word, we can probably agree:
“I think there is a market for maybe fiveworldcomputers.”
So, what is aworld computer? In many ways a world computer is like
a common desktop/laptop computer that takes commands (“transactions”)
as input and then changes its bookkeeping (“internal state”) accordingly. A
world computer provides a shared environment for users from all over the
world. Moreover, a world computer itself is distributed over the entire world:


Instead of just having a single processor, we have dozens, hundreds or thou-
sands of processors, connected through the internet.
Such a world computer has a big advantage over even the most advanced
traditional computer: The world computer is much more fault tolerant, as it
can survive a large number of crashes of individual components. Beyond that,
no authority can corrupt the computer for other users. A world computer
must survive even if some of its components are controlled by an evil botnet.
The currently common name for such a world computer isblockchain.
In this paper we present Alpenglow, a new blockchain protocol. Alpen-
glow uses the Rotor protocol, which is an optimized and simplified variant of
Solana’s data dissemination protocol Turbine [Fou19]. Turbine brought era-
sure coded information dispersal [CT05] to permissionless blockchains. Rotor
uses the total amount of available bandwidth provided by the nodes. Because
of this, Rotor achieves an asymptotically optimal throughput. In contrast,
consensus protocols that do not address the leader bandwidth bottleneck suf-
fer from low throughput.
The Votor consensus logic at the core of Alpenglow inherits the simplic-
ity from the Simplex protocol line of work [CP23; Sho24] and translates it
to a proof-of-stake context, resulting in natural support for rotating leaders
without complicated view changes. In the common case, we achieve finality
in a single round of voting, while a conservative two-round procedure is run
Intuitionconcurrently as backup [SSV25; Von+24].

### 1.1 Alpenglow Overview

```
First, let us provide a high-level description of Alpenglow. We are going
to describe all the individual parts in detail in Section 2.
Alpenglow runs on top ofncomputers, which we call nodes, wherencan
be in the thousands. This set of nodes is known and fixed over a period of
time called an epoch. Any node can communicate with any other node in the
set by sending a direct message.
Alpenglow is a proof-of-stake blockchain, where each node has a known
stake of cryptocurrency. The stake of a node signals how much the node
contributes to the blockchain. If nodev 2 has twice the stake of nodev 1 ,
nodev 2 will also earn twice the fees, and provide twice the outgoing network
bandwidth.
Time is partitioned into slots. Each time slot has a slot number and a
designated leader from the set of nodes. Each leader will be in charge for a
fixed amount of consecutive slots, known as the leader window. A threshold
verifiable random function determines the leader schedule.
While a node is the leader, it will receive all the new transactions, either
directly from the users or relayed by other nodes. The leader will construct
a block with these transactions. A block consists of slices for pipelining. The
slices themselves consist of shreds for fault tolerance and balanced dispersal
```

(Section 2.1). The leader incorporates the Rotor algorithm (Section 2.2),
which is based on erasure coding, to disseminate the shreds. In essence, we
want the nodes to utilize their total outgoing network bandwidth in a stake-
fair way, and avoid the common pitfall of having a leader bottleneck. The
leader will continuously send its shreds to relay nodes, which will in turn
forward the shreds to all other nodes.
As soon as a block is complete, the (next) leader will start building and
disseminating the next block. Meanwhile, concurrently, every node eventually
receives that newly constructed block. The shreds and slices of the incoming
blocks are stored in the Blokstor (Section 2.3).
Nodes will then vote on whether they support the block. We introduce
different types of votes (and certificates of aggregated votes) in Section 2.4.
These votes and certificates are stored in a local data structure called Pool
(Section 2.5).
With all the data structures in place, we discuss the voting algorithm Votor
in Section 2.6: If the block is constructed correctly and arrives in time, a node
will vote for the block. If a block arrives too late, a node will instead vote
to skip the block (since either the leader cannot be trusted, or the network
is unstable). If a super-majority of the total stake votes for a block, the
block can be finalized immediately. However, if something goes wrong, an
additional round of voting will decide whether or not to skip the block.
In Section 2.7 we discuss the logic of creating blocks as a leader, and how
to decide on where to append the newly created block.
Finally, in Section 2.8 we discuss Repair – how a node can get missing
shreds, slices or blocks from other peers. Repair is needed to help nodes to
retrieve the content of an earlier block that they might have missed, which is
now an ancestor of a finalized block. This completes the main parts of our
Protocoldiscussion of the consensus algorithm.

```
We proceed to prove the correctness of Alpenglow. First, we prove safety
(we do not make fatal mistakes even if the network is unreliable, see Sec-
tion 2.9), then liveness (we do make progress if the network is reliable, see
Section 2.10). Finally, we also consider a scenario with a high number of crash
failures in Section 2.11.
While not directly essential for Alpenglow’s correctness, Section 3 exam-
ines various concepts that are important for Alpenglow’s understanding. First
we describe our novel Rotor relay sampling algorithm in Section 3.1. Next,
we explore how transactions are executed in Section 3.2.
Then we move on to advanced failure handling. In Section 3.3 we consider
how a node re-connects to Alpenglow after it lost contact, and how the sys-
tem can “re-sync” when experiencing severe network outages. Then we add
dynamic timeouts to resolve a crisis (Section 3.4).
In the last part, we present potential choices for protocol parameters (Sec-
tion 3.5). Based on these we show some measurement results; to better under-
stand possible efficiency gains, we simulate Alpenglow with Solana’s current
```

node and stake distribution, both for bandwidth (Section 3.6) and latency
(Section 3.7).
In the remainder ofthissection, we present some preliminaries which are
necessary to understand the paper. We start out with a short discussion on
security design goals in Section 1.2 and performance metrics in Section 1.3.
In Section 1.4 we discuss how Alpenglow relates to other work on consensus.
Finally we present the model assumptions (Section 1.5) and the cryptographic
Intuitiontools we use (Section 1.6).

### 1.2 Fault Tolerance

```
Safety and security are the most important objectives of any consensus
protocol. Typically, this involves achieving resilience against adversaries that
control up to 33% of the stake [PSL80]. This 33% (also known as “3f+ 1”)
bound iseverywherein today’s world of fault-tolerant distributed systems.
When discovering the fundamental result in 1980, Pease et al. considered
systems where the number of nodesnwas small. However, today’s blockchain
systems consist ofthousandsof nodes! While the 33% bound of [PSL80] also
holds for largen, attacking one or two nodes is not the same as attacking
thousands. In a large scale proof-of-stake blockchain system, running a thou-
sand malicious (“byzantine”) nodes would be a costly endeavor, as it would
likely require billions of USD as staking capital. Even worse, misbehavior is
often punishable, hence an attacker would lose all this staked capital.
So, in areallarge scale distributed blockchain system, we will probably
seesignificantly less than 33% byzantines. Instead, realistic bad behavior
often comes from machine misconfigurations, software bugs, and network or
power outages. In other words, large scale faults are likely accidents rather
than coordinated attacks.
Thisattack model paradigm shiftopens an opportunity to reconsider the
classic 3f+ 1 bound. Alpenglow is based on the 5f+ 1 bound that has been
introduced in [DGV04] and [MA06]. While beingless tolerant to orthodox
byzantine attacks, the 5f+ 1 bound offers other advantages. Two rounds
of voting are required for finalization if the adversary is strong. However, if
the adversary possesses less stake, or does not misbehave all the time, it is
possible for a correct 5f+ 1 protocol to finalize a block in justa single round
of voting.
In Sections 2.9 and 2.10 we rely on Assumption 1 to show that our protocol
is correct.
```
```
Assumption 1(fault tolerance).Byzantine nodes control less than 20% of
the stake. The remaining nodes controlling more than 80% of stake are cor-
rect.
```
```
As we explain later, Alpenglow is partially-synchronous, and Assumption 1
is enough to ensure that even an adversary completely controlling the network
```

```
(inspecting, delaying, and scheduling communication between correct nodes
at will) cannot violate safety. A network outage or partition would simply
cause the protocol to pause and continue as soon as communication is restored,
without any incorrect outcome.
However, if the network is not being attacked, or the adversary does not
leverage some network advantage, Alpenglow can tolerate an even higher share
of nodes that simply crash. In Section 2.11 we intuitively explain the differ-
ence between Assumption 1 and Assumption 2, and we sketch Alpenglow’s
correctness under Assumption 2.
```
Assumption 2(extra crash tolerance). Byzantine nodes control less than
20% of the stake. Other nodes with up to 20% stake might crash. The re-
Intuitionmaining nodes controlling more than 60% of the stake are correct.

### 1.3 Performance Metrics

Alpenglow achieves the fastest possible consensus. In particular, after a
block is distributed, our protocol finalizes the block in min(δ80%, 2 δ60%) time.
We will explain this formula in more detail in Section 1.5; in a nutshell,δθis
a network delay between a stake-weighted fractionθof nodes. To achieve this
finalization time, we run an 80% and a 60% majority consensus mechanism
concurrently. A low-latency 60% majority cluster is likely to finish faster on
the 2δpath, whereas more remote nodes may finish faster on the singleδpath,
hence min(δ80%, 2 δ60%). Having low latency is an important factor deciding
the blockchain’s usability. Improving latency means establishing transaction
finality faster, and providing users with results with minimal delay.
Another common pain point of a blockchain is the system’s throughput,
measured in transaction bytes per second or transactions per second. In terms
of throughput, our protocol is using the total available bandwidth asymptot-
ically optimally.
After achieving the best possible results across these main performance
metrics, it is also important to minimize protocol overhead, including com-
putational requirements and other resource demands.
Moreover, in Alpenglow, we strive for simplicity whenever possible. While
simplicity is difficult to quantify, it remains a highly desirable property, be-
cause simplicity makes it easier to reason about correctness and implemen-
tation. A simple protocol can also be upgraded and optimized more conve-
Intiuitionniently.


### 1.4 Related Work

Different consensus protocols contribute different techniques to address
different performance metrics. Some techniques can be translated from one
protocol to another without compromise, while other techniques cannot. In
the following we describe each protocol as it was originally published, and not
what techniques could hypothetically be added to the protocol.

Increase Bandwidth. In classic leader-based consensus protocols such as
PBFT [CL99], Tendermint [BKM18] or HotStuff [Yin+19], at a given time
one leader node is responsible for disseminating the proposed payload to all
replicas. This bandwidth bottleneck can constitute a defining limitation on
the throughput [Dan+22; Mil+16; SDV19].
DAG protocols [Dan+22; Spi+22] are a prominent line of work focused on
addressing this concern. In these protocols data dissemination is performed
by all nodes. Unfortunately, protocols following the DAG approach exhibit a
latency penalty [Aru+25]. Some DAG protocols [Kei+22] reduce the latency
penalty by foregoing “certifying” the disseminated data. For example, in
Mysticeti [Bab+25] the leader block can be confirmed in two rounds of voting,
i.e., after disseminating the block and observing two block layers referencing
this block (corresponding to 3 network delays, or 3δ). However, most of the
data (all non-leader blocks) is ordered by the protocol when a leader block
“certifying” the data is finalized. In other words, most of the throughput
is confirmed with a latency of 5δ. Some researchers raise concerns that this
technique impacts the robustness of the protocol [Aru+24].
Another prominent technique used to alleviate the leader bottleneck for
high throughput involves erasure coding [CT05; Sho24; Yan+22]. Solana [Fou19;
Yak18] pioneered this approach in blockchains. In this technique, the leader
erasure-codes the payload into smaller fragments. The fragments are sent
to different nodes, which in turn participate in disseminating the fragments,
making the bandwidth use balanced. Alpenglow follows this line of work.
A recent study [LNS25] proposes a framework to compare the impact
of above-mentioned techniques on throughput and latency in a principled
way. The study indicates that erasure coding of the payload (represented by
DispersedSimplex [Sho24]) achieves better latency than DAG protocols.

Reduce Latency. A long line of work proposes consensus protocols that
can terminate after one round of voting, typically called fast or one-step
consensus. This approach has received a lot of attention, e.g., [DGV04; GV07;
Kot+07; Kur02; Lam03; MA06; SR08]. Protocols DGV [DGV04] and FaB
Paxos [MA06] introduce a parametrized model with 3f+2p+1 replicas, where
p≥0. The parameterpdescribes the number of replicas that are not needed
for the fast path. These protocols can terminate optimally fast in theory (2δ,
or 2 network delays) under optimistic conditions. Liveness and safety issues of


landmark papers were later pointed out [Abr+17], showcasing the complexity
of the domain and thus posing the research question of fast consensus again.
SBFT [Gue+19] addressed the correctness issues. SBFT can terminate after
one round of voting, but is optimized for linear message complexity, therefore
incurring higher latency.
As pointed out by [DGV04], and later in [KTZ21] and [Abr+21], the lower
bound of 3f+ 2p+ 1 actually only applies to a restricted type of protocol.
These works prove the lower bound and show single-shot consensus protocols
that use only 3f+ 2p∗−1 replicas, withp∗≥1.
Interestingly, in practice, one-step protocols mightincreasethe finalization
latency, as one-round finalization requires voting betweenn−preplicas, which
could be slower than two rounds of voting betweenn−f−preplicas that are
more concentrated in a geographic area. Banyan [Von+24] renewed interest
in fast BFT protocols, as it performs a one-round and a two-round mechanism
in parallel, guaranteeing the best possible latency.

Concurrent Work. Kudzu [SSV25] is Alpenglow’s “academic sibling” with
a simpler theoretical model. Like Alpenglow, Kudzu features high throughput
via the previously mentioned technique of erasure coding, and one- and two-
round parallel finalization paths. The differences between Alpenglow and
Kudzu include:

- Kudzu is specified in a permissioned model, while Alpenglow is a proof-
    of-stake protocol. In many protocols merely the voting weight of nodes
    would be impacted by this difference. However, disseminating erasure-
    coded data cannot be easily translated between these models.
- Alpenglow features leader windows where the leader streams the data
    without interruption, improving throughput. Concurrent processing of
    slots allows block times to be shorter than the assumed latency bound
    (∆).
- Alpenglow features fast leader handoff. When the leader is rotated, the
    next leader can start producing a block as soon as it has received the
    previous block.
- With Assumption 3, Alpenglow features higher resilience to crash faults.
- In Kudzu, due to the different model, nodes can vote as soon as they
    receive the first fragment of a block proposal, while in Alpenglow nodes
    vote after reconstructing a full proposal. In theory, the former is faster,
    while in practice, the difference is a fraction of one network delay.
- The data expansion ratio associated with erasure coding can be freely
    set in Alpenglow. We suggest a ratio of 2, while in Kudzu the ratio
    needs to be higher.


Follow-up Work. Hydrangea [SKN25] is a protocol proposed after Alpen-
glow that parametrizes resilience to byzantine and crash faults in a way related
to Alpenglow. The protocol requiresn= 3f+ 2c+k+ 1, and toleratesf
byzantine faults andccrash faults in partial synchrony. The number of nodes
not needed for finalization in one round of voting is thenp=⌊c+ 2 k⌋. For ex-
ample, to terminate in one round of voting among 80% of nodes, Hydrangea
would setp=c=k= 20% andf= 13%, for a total of 33% of tolerated
faulty nodes. In contrast, Alpenglow can toleratef <20% and a total of 40%
of faulty nodes, but needs Assumption 3 for fault rates higher than 20%.
Hydrangea suffers from a bandwidth bottleneck at the leader and, in
our view, remains underspecified for practical implementation. However, the
parametrization is an interesting contribution than could also be applied to
IntuitionAlpenglow.

### 1.5 Model and Preliminaries

```
Names. We introduce various objects of the formName(x,y). This indi-
cates some deterministic encoding of the object type “Name” and its param-
etersxandy.
```
```
Epoch. To allow for changing participants and other dynamics, the protocol
rejuvenates itself in regular intervals. The time between two such changes is
called an epoch. Epochs are numbered ase= 1, 2 , 3 ,etc. The participants
register/unregister two epochs earlier, i.e., the participants (and their stake)
of epoche+ 1 are decided at the end of epoche−1, i.e., a long enough time
before epoche+ 1 starts. This makes sure that everybody is in agreement on
the current nodes and their stake at the beginning of epoche+ 1.
```
```
Node. We operate onnindividual computers, which we call nodesv 1 ,v 2 ,
..., vn. The main jobs of these nodes are to send/relay messages and to
validate blocks. Because of this, nodes are sometimes also called validators
in the literature. While the set of nodes changes with every new epoch, as
mentioned in the previous paragraph, the nodes are static and fixed during
an epoch. The set of nodes is publicly known, i.e., each node knows how
to contact (IP address and port number) every nodevi. Each node has a
public key, and all nodes know all public keys. The information of each
node (public key, stake, IP address, port number, etc.) is announced and
updated by including the information in a transaction on the blockchain. This
guarantees that everybody has the same information. Currently, Solana has
n≈ 1 ,500 nodes, but our protocol can in principle scale to higher numbers.
However, for practical reasons it may be beneficial to boundn≤nmax.
```
```
Message. Nodes communicate by exchanging authenticated messages. Our
protocol never uses large messages. Specifically, all messages are less than
```

1,500 bytes [Pos84]. Because of this, we use UDP with authentication, so
either QUIC-UDP or UDP with a pair-wise message authentication code
(MAC). The symmetric keys used for this purpose are derived with a key
exchange protocol using the public keys.

Broadcast. Sometimes, a node needs to broadcast the same message to
all(n−1 other) nodes. The sender node simply loops over all other nodes
and sends the message to one node after the other. Despite this loop, the
total delay is dominated by the network delay. With a bandwidth of 1Gb/s,
transmittingn= 1,500 shreds takes 18 ms (well below the average network
delay of about 80 ms). To get to 80% of the total stake we need to reach
n≈150 nodes, which takes only about 2 ms. Voting messages are shorter,
and hence need even less time. Moreover, we can use a multicast primitive
provided by an alternative network provider, e.g., DoubleZero [FMW24] or
SCION [Zha+11].

Stake. Each nodevihas a known positive stake of cryptocurrency. We use
ρi>0 to denote nodevi’s fraction of the entire stake, i.e.,

Pn
i=1ρi= 1.
Each (fractional) stakeρistays fixed during the epoch. The stake of a node
signals how much the node contributes to the blockchain. If nodev 2 has
twice the stake of nodev 1 , nodev 2 will also earn roughly twice the fees.
Moreover, nodev 2 also has twice the outgoing network bandwidth. However,
all nodes need enough in-bandwidth to receive the blocks, and some minimum
out-bandwidth to distribute blocks when they are a leader.

Time. We assume that each node is equipped with a local system clock
that is reasonably accurate, e.g., 50 ppm drift. We do not consider clock drift
in our analysis, but it can be easily addressed by incorporating the assumed
drift into timeout periods. Clocks do not need to be synchronized at all, as
every node only uses its local system clock.

Slot. Each epoch is partitioned into slots. A slot is a natural number asso-
ciated with a block, and does not require timing agreements between nodes.
The time period of a slot could start (and end) at a different local time for
different nodes. Nevertheless, in normal network conditions the slots will
become somewhat synchronized. During an epoch, the protocol will iterate
through slotss= 1, 2 ,...,L. Solana’s current parameter ofL= 432,000 is
possible, but much shorter epochs, e.g.,L≈ 18 ,000, could be advantageous,
for instance to change stake more quickly. Each slotsis assigned a leader
node, given by the deterministic functionleader(s) (which is known before the
epoch starts).

Leader. Each slot has a designated leader from the set of nodes. Each
leader will be in charge for a fixed amount of consecutive slots, known as the


```
leader window. A threshold verifiable random function [Dod02; MRV99] is
evaluated before each epoch to determine a publicly known leader schedule
that defines which node is the leader in what slot.
```
Timeout. Our protocol uses timeouts. Nodes set timeouts to make sure
that the protocol does not get stuck waiting forever for some messages. For
simplicity, timeouts are based on a global protocol parameter ∆, which is
the maximum possible network delay between any two correct nodes when
the network is in synchronous operation. However, timeout durations can be
changed dynamically based on conditions, such that the protocol is correct
irrespectively of the ∆ exhibited by the network. For simplicity, we conser-
vatively assume ∆ to be a constant, e.g., ∆≈400 ms. Importantly, timeouts
donotassume synchronized clocks. Instead, only short periods of time are
measured locally by the nodes. Therefore, the absolute wall-clock time and
clock skew have no significance to the protocol. Even extreme clock drift can
be simply incorporated into the timeouts - e.g. to tolerate clock drift of 5%,
the timeouts can simply be extended by 5%. As explained later, Alpenglow
is partially-synchronous, so no timing- or clock-related errors can derail the
Protocolprotocol.

```
Adversary. Some nodes can be byzantine in the sense that they can mis-
behave in arbitrary ways. Byzantine nodes can for instance forget to send a
message. They can also collude to attack the blockchain in a coordinated way.
Some misbehavior (e.g. signing inconsistent information) may be a provable
offense, while some other misbehavior cannot be punished, e.g., sending a
message late could be due to an extraordinary network delay. As discussed in
Assumption 1, we assume that all the byzantine nodes together own strictly
less than 20% of the total stake. Up to an additional 20% of the stake may
be crashed under the conditions described in Section 2.11. The remaining
nodes arecorrectand follow the protocol. For simplicity, in our analysis (Sec-
tions 2.9 to 2.11) we consider a static adversary over a period of one epoch.
```
```
Asynchrony. We consider the partially synchronous network setting of
Global Stabilization Time (GST) [Con+24; DLS88]. Messages sent between
correct nodes will eventually arrive, but they may take arbitrarily long to
arrive. We always guaranteesafety, which means that irrespectively of ar-
bitrary network delays (known as the asynchronous network model), correct
nodes output the same blocks in the same order.
```
```
Synchrony. However, we only guaranteelivenesswhen the network is syn-
chronous, and all messages are delivered quickly. In other words, correct
nodes continue to make progress and output transactions in periods when
messages between correct nodes are delivered “in time.” In the model of
GST, synchrony simply corresponds to a global worst-case bound ∆ on mes-
```

```
sage delivery. The GST model captures periods of synchrony and asynchrony
by stating that before the unknown and arbitrary timeGST(global stabi-
lization time) messages can be arbitrarily delayed, but after timeGSTall
previous and future messagesmsent at timetmwill arrive at the recipient
at latest at time max(GST,tm) + ∆.
```
```
Network Delay. During synchrony, the protocol will rarely wait for a time-
out. We model the actual message delay between correct nodes asδ, with
δ≪∆. The real message delayδis variable and unknown. Naturally,δis
not part of the protocol, and will only be used for the latency analysis. In
other words, the performance of optimistically responsive protocols such as
Alpenglow in the common case depends only onδand not the timeout bound
∆. As discussed in Section 1.3, we useδθto indicate how long it takes a
fractionθof nodes to send each other messages. More precisely, letSbe a
set of nodes with cumulative stake at leastθ. In one network delayδθ, each
node inSsends a message to every node inS. Ifθ= 60% of the nodes
are geographically close, then it is possible that 2δ60%isless timethanδ80%,
which needs only one network delay, but the involvement of 80% of the nodes.
```
```
Correctness. The purpose of a blockchain is to produce a sequence offi-
nalizedblocks containing transactions, so that all nodes output transactions
in the same order. Every block is associated with a parent (starting at some
notional genesis block). Finalized blocks form a single chain of parent-child
links. When a block is finalized, all ancestors of the block are finalized as
well.
Our protocol orders blocks by associating them with natural numbered
slots, where a child block has to have a higher slot number than its parent.
For every slot, either some block produced by the leader might be finalized,
or the protocol can yield askip. The blocks in finalized slots are transmitted
in-order to the execution layer of the protocol stack. Definition 14 describes
the conditions for block finalization. The guarantees of our protocol can be
stated as follows:
```
- Safety.Suppose a correct node finalizes a blockbin slots. Then, if any
    correct node finalizes any blockb′in any slots′≥s,b′is a descendant
    ofb. (See also Theorem 1.)
- Liveness. In any long enough period of network synchrony, correct
    nodes finalize new blocks produced by correct nodes. (See also Theo-
Analysis rem 2.)


### 1.6 Cryptographic Techniques

Hash Function. We have a collision-resistant hash function, e.g., SHA256.

Digital Signature. We have secure (non-forgeable) digital signatures. As
stated earlier, each node knows the public key of every other node.

Aggregate Signature. Signatures from different signers may be combined
non-interactively to form an aggregate signature. Technically, we only require
non-interactive multi-signatures, which only enable signatures over the same
message to be aggregated. This can be implemented in various ways, e.g.
based on BLS signatures [Bon+03]. Aggregate signatures allow certificates to
fit into a short message as long asn≤nmax.

Erasure Code. For integer parameters Γ≥γ≥1, a (Γ,γ)erasure code
encodes a bit stringMof sizemas a vector of Γ data piecesd 1 ,...,dΓof
sizem/γ+O(log Γ) each. TheO(log Γ) overhead is needed to index each
data piece. Erasure coding makes sure that anyγdata pieces may be used to
efficiently reconstructM. The reconstruction algorithm also takes as input
the lengthmofM, which we assume to be constant (achieved by padding
smaller payloads).
In our protocol, the payload of a slice will be encoded using a (Γ,γ)
Reed-Solomon erasure code [RS60], which encodes a payloadMas a vector
d 1 ,...,dΓ, where anyγ di’s can be used to reconstructM. The data expansion
rate isκ= Γ/γ.

Merkle Tree. A Merkle tree [Mer79] allows one party to commit to a vector
of data (d 1 ,...,dΓ) using a collision-resistant hash function by building a (full)
binary tree where the leaves are the hashes ofd 1 ,...,dΓ. Each leaf hash is
concatenated with a label that marks the hash as a leaf, and each internal
node of the tree is the hash of its two children. The rootrof the tree is the
commitment.
Thevalidation pathπifor positioni∈ { 1 ,...,Γ}consists of the siblings
of all nodes along the path in the tree from the hash ofdito the rootr. The
rootrtogether with the validation pathπican be used to prove thatdiis at
positioniof the Merkle tree with rootr.
The validation path is checked by recomputing the hashes along the cor-
responding path in the tree, and by verifying that the recomputed root is
equal to the given commitmentr. If this verification is successful, we calldi
the data at positioniwith pathπifor Merkle rootr. The collision resistance
of the hash function ensures that no datad′i̸=dican have a valid proof for
positioniin the Merkle tree.


Encoding and Decoding. [CT05] The functionencodetakes as input a
payloadMof sizem. It erasure codesMas (d 1 ,...,dΓ) and builds a Merkle
tree with rootrwhere the leaves are the hashes ofd 1 ,...,dΓ. The root of
the treeris uniquely associated withM. It returns (r, {(di,πi)}i∈{ 1 ,...,Γ}),
where eachdiis the data at positioniwith pathπifor Merkle rootr.
The functiondecodetakes as input (r,{(di,πi)}i∈I),whereIis a subset
of{ 1 ,...,Γ}of sizeγ, and eachdi(of correct length) is the data at position
iwith pathπifor Merkle rootr. Moreover, the decoding routine makes sure
that the rootris correctly computed based onallΓ data pieces that correctly
encode some messageM′, or itfails. If it fails, it guarantees that no set of
γdata pieces associated withrcan be decoded, and thatrwas (provably)
maliciously constructed.
To ensure this pass/fail property, the decoding algorithm needs to check
for each reconstructed data piece that it corresponds to the same rootr. More
precisely,decodereconstructs a messageM′from the data{di}i∈I. Then, it
encodesM′as a vector (d′ 1 ,...,d′Γ), and builds a Merkle tree with rootr′with
the hashes of (d′ 1 ,...,d′Γ) as leaves. Ifr′=r,decodereturnsM′, otherwise it
Protocolfails.

## 2 The Alpenglow Protocol

```
In this section we describe the Alpenglow protocol in detail.
```
```
Blokstor Repair
```
```
Pool block creation
```
```
Votor
```
```
Rotor
```
```
broadcast
```
Figure 1: Overview of components of Alpenglow and their interactions. Ar-
rows show information flow: block data in the form of shreds (blue), internal
Protocolevents (green), and votes/certificates (red).


### 2.1 Shred, Slice, Block

```
hash(b)
```
```
r 1
```
```
d 1 d 2... dΓ
```
```
r 2
```
```
d 1 d 2... dΓ
```
... rk

```
d 1 d 2... dΓ
slice 1 slice 2 slicek
blockb
```
Figure 2: Hierarchy of block data, visualizing the double-Merkle construction
of the block hash. Each slice has a Merkle root hashri, which are in turn
the leaf nodes for the second Merkle tree, where the root corresponds to the
block hash.

Definition 1(shred). Ashredfits neatly in a UDP datagram. It has the
form:
(s,t,i,zt,rt,(di,πi),σt),

where

- s,t,i∈Nare slot number, slice index, shred index, respectively,
- zt∈{ 0 , 1 }is a flag (see Definition 2 below),
- diis the data at positioniwith pathπifor Merkle rootrt(Section 1.6),
- σtis the signature of the objectSlice(s,t,zt,rt)from the nodeleader(s).

Definition 2(slice).Asliceis the input of Rotor, see Section 2.2. Given
anyγof theΓshreds, we can decode (Section 1.6) the slice. A slice has the
form: 
s,t,zt,rt,Mt,σt

#### 

#### ,

where

- s,t∈Nare the slot number and slice index respectively,
- zt∈{ 0 , 1 }is a flag indicating the last slice index,
- Mtis the decoding of the shred data{(di)}i∈Ifor Merkle rootrt,
- σtis the signature of the objectSlice(s,t,zt,rt)from the nodeleader(s).


```
Definition 3(block).Ablockbis the sequence of all slices of a slot, for the
purpose of voting and reaching consensus. A block is of the form:
```
```
b={
```
#### 

```
s,t,zt,rt,Mt,σt
```
#### 

```
}t∈{ 1 ,...,k},
```
```
wherezk= 1,zt= 0fort < k. The data of the block is the concatenation
of all the slice data, i.e.,M= (M 1 ,M 2 ,...,Mk). We defineslot(b) =s.
The block dataMcontains information about the slot slot(parent(b))and
hashhash(parent(b))of the parent block ofb. There are various limits on a
block, for instance, each block can only have a bounded amount of bytes and
a bounded amount of time for execution.
```
```
Definition 4(block hash). We definehash(b)of blockb={
```
#### 

```
s,t,zt,rt,Mt,
σt
```
#### 

```
}t∈{ 1 ,...,k}as the root of a Merkle treeTwhere:
```
- Tis a complete, full binary tree with the smallest possible number of
    leavesm(withmbeing a power of 2 ) such thatm≥k,
- the firstkleaves ofTarer 1 ,...,rk(each hash is concatenated with a
    label that marks the hash as a leaf ),
- the remaining leaves ofTare⊥.

Definition 5(ancestor and descendant). An ancestor of a blockbis any
block that can be reached frombby the parent links, i.e.,b,b’s parent,b’s
parent’s parent, and so on. Ifb′is an ancestor ofb,bis a descendant ofb′.
ProtocolNote thatbis its own ancestor and descendant.

### 2.2 Rotor

```
Rotor is the block dissemination protocol of Alpenglow. The leader
(sender) wants to broadcast some data (a block) to all other nodes. This
procedure should have low latency, utilize the bandwidth of the network in
a balanced way, and be resilient to transmission failures. The block should
be produced and transmitted in a streaming manner, that is, the leader does
not need to wait until the entire block is constructed.
```
```
leader
```
```
shred-1 relay
```
```
v 1 v 2... vn
```
```
shred-2 relay
```
```
v 1 v 2... vn
```
... shred-Γ relay

```
v 1 v 2... vn
```
IntiuitionFigure 3: Basic structure of the Rotor data dissemination protocol.


A leader uses multiple rounds of the Rotor protocol to broadcast a block.
Each round considers the independent transmission of one slice of the block.
The leader transmits each slice as soon as it is ready. This achieves pipelining
of block production and transmission.
For each slice, the leader generates Γ Reed-Solomon coding shreds and
constructs a Merkle tree over their hashes and signs the root. Each coding
shred includes the Merkle path along with the root signature. Each shred
contains as much data and corresponding metadata as can fit into a single
UDP datagram.
Using Reed-Solomon erasure coding [RS60] ensures that, at the cost of
sending more data, receiving anyγshreds is enough to reconstruct the slice
(Section 1.6). After that, as an additional validity check, a receiver generates
the (up to Γ−γ) missing shreds.
For any given slice, the leader sends each shred directly to a corresponding
node selected as shred relay. We sample relays for every slice. We use a novel
sampling method which improves resilience. We describe our new method in
detail in Section 3.1.
Each relay then broadcasts its shred to all nodes that still need it, i.e., all
nodes except for the leader and itself, in decreasing stake order. As a minor
optimization, all shred relays send their shred to the next leader first. This
slightly improves latency for the next leader, who most urgently needs the
block.
A shred’s authenticity needs to be checked to reconstruct the slice fromγ
of the shreds. To enable receivers to cheaply check authenticity of each shred
individually, the leader builds a Merkle tree [Mer79] over all shreds of a slice,
as described in Section 1.6. Each shred then includes its path in the tree and
the leader’s signature of the root of the tree.
When receiving the first shred of a slice, a node checks the validity of the
Merkle path and the leader’s signature, and then stores the verified root. For
any later shred, the receiving node only checks the validity of the Merkle path
Protocolagainst the stored root.


```
64 80 96 320
```
```
0
```
```
20
```
```
40
```
```
60
```
```
80
```
```
100
```
```
120
```
```
Total shreds (Γ)
```
```
Latency [ms]
```
```
Average Rotor Latency (γ= 32)
```
```
64 80 96 320
```
```
0
```
```
20
```
```
40
```
```
60
```
```
80
```
```
100
```
```
120
```
```
Total shreds (Γ)
```
```
Latency [ms]
```
```
Median Rotor Latency (γ= 32)
```
Figure 4: Rotor latency for different data expansion ratios (and thus total
numbers of shreds), all withγ= 32 data shreds using our sampling from
Section 3.1. The red lines indicate the average/median network latency. With
a high data expansion rate (κ= 10, hence Γ = 320) we pretty much achieve
the singleδlatency described in Lemma 8. All our simulation results use the
current (epoch 780) Solana stake distribution. Network latency is inferred
from public data. Computation and transmission delays are omitted.

Definition 6.Given a slots, we say that Rotor issuccessfulif the leader of
sis correct, and at leastγof the corresponding relays are correct.

Resilience. If the conditions of Definition 6 are met, all correct nodes will
receive the block distributed by the leader, as enough relays are correct. On
the other hand, a faulty leader can simply not send any data, and Rotor will
immediately fail. In the following we assume that the leader is correct. The
following lemma shows that Rotor is likely to succeed if we over-provision the
coding shreds by at least 67%.

Lemma 7 (rotor resilience). Assume that the leader is correct, and that
erasure coding over-provisioning is at leastκ= Γ/γ > 5 / 3 .Ifγ→ ∞, with
probability 1, a slice is received correctly.

Proof Sketch.We choose the relay nodes randomly, according to stake. The
failure probability of each relay is less than 40% according to Section 1.2. The
expected value of correct relays is then at least 60%·Γ>60%· 5 γ/3 =γ. So
strictly more thanγshreds will arrive in expectation. Withγ→∞, applying
an appropriate Chernoff bound, with probability 1 we will have at leastγ
shreds that correctly arrive at all nodes.


Latency. The latency of Rotor is betweenδand 2δ, depending on whether
we make optimistic or pessimistic assumptions on various parameters.

Lemma 8.(rotor latency) If Rotor succeeds, network latency of Rotor is at
most 2 δ. A high over-provisioning factorκcan reduce latency. In the extreme
case withn→∞andκ→∞, we can bring network latency down toδ. (See
also Figure 4 for simulation results with Solana’s stake distribution.)

Proof Sketch.Assuming a correct leader, all relays receive their shred in time
δdirectly from the leader. The correct relays then send their shred to the
nodes in another timeδ, so in time 2δin total.
If we over-provision the relays, chances are that many correct relays are
geographically located between leader and the receiving node. In the extreme
case with infinitely many relays, and some natural stake distribution assump-
tions, there will be at leastγcorrect relays between any pair of leader and
receiving node. If the relays are on the direct path between leader and re-
ceiver, they do not add any overhead, and both legs of the trip just sum up
toδ.

Bandwidth. Both the leader and the shred relays are sampled by stake. As
a result, in expectation each node has to transmit data proportional to their
stake. This aligns well with the fact that staking rewards are also proportional
to the nodes’ stake. If the available out-bandwidth is proportional to stake,
it can be utilized perfectly apart from the overhead.

Lemma 9(bandwidth optimality). Assume a fixed leader sending data at
rateβℓ ≤β ̄, whereβ ̄is the average outgoing bandwidth across all nodes.
Suppose any distribution of out-bandwidth and proportional node stake. Then,
at every correct node, Rotor delivers block data at rateβℓ/κin expectation.
Up to the data expansion rateκ= Γ/γ, this is optimal.

Proof.Nodeviis chosen to be a shred relay in expectation Γρitimes. Each
shred relay receives data from the leader with bandwidthβℓ/Γ, because the
leader splits its bandwidth across all shred relays. Hence, in expectation,
nodevireceives data from the leader at rate Γρi·βℓ/Γ =ρiβℓ. Nodevineeds
to forward this data ton−2 nodes. So, in expectation, nodevineeds to send
data at rateρiβℓ(n−2). Nodevihas outgoing bandwidthβi=nβρ ̄i, since
outgoing bandwidth is proportional to stake (Section 1.5). Sinceβℓ≤β ̄, we
haveρiβℓ(n−2)< βi. Each node thus has enough outgoing bandwidth to
support the data they need to send.
Note that we cannot get above rateβℓbecause the leader is the only one
who knows the data. Likewise we cannot get above rateβ ̄, because all nodes
need to receive the data, and the nodes can send with no more total rate than
nβ ̄. So apart from the data expansion factorκ, we are optimal.

```
Note that any potential attacks on Rotor may only impact liveness, not
```

safety, since the other parts of Alpenglow ensure safety even under asynchrony
Analysisand rely on Rotor only for data dissemination.

### 2.3 Blokstor

```
Blokstor collects and stores the first block received through Rotor in every
slot, as described in Definition 10.
```
```
Definition 10(Blokstor). TheBlokstoris a data structure managing the
storage of slices disseminated by the protocol of Section 2.2. When a shred
(s,t,i,zt,rt,(di,πi),σt)is received by a node, the node checks the following
conditions. If the conditions are satisfied, the shred is added to the Blokstor:
```
- the Blokstor does not contain a shred for indices(s,t,i)yet,
- (di,πi)is the data with path for Merkle rootrtat positioni,
- σtis the signature of the objectSlice(s,t,zt,rt)from the nodeleader(s).

```
Blokstor emits the eventBlock(slot(b),hash(b),hash(parent(b)))as input
for Algorithm 1 when it receives the first complete blockbforslot(b).
```
In addition to storing the first block received for a given slot, the Blokstor
can perform the repair procedure (Section 2.8) to collect some other blockb
and store it in the Blokstor. If a block is finalized according to Definition 14,
Blokstor has to collect and store only this block in the given slot. Otherwise,
before the eventSafeToNotar(slot(b),hash(b)) of Definition 16 is emitted,b
Protocolhas to be stored in the Blokstor as well.

### 2.4 Votes and Certificates

Next we describe the voting data structures and algorithms of Alpenglow.
In a nutshell, if a leader gets at least 80% of the stake to vote for its block, the
block is immediately finalized after one round of voting with a fast-finalization
certificate. However, as soon as a node observes 60% of stake voting for a
block, it issues its second-round vote. After 60% of stake voted for a block the
second time, the block is also finalized. On the other hand, if enough stake
considers the block late, a skip certificate can be produced, and the block
Intiuitionproposal will be skipped.

```
Definition 11(messages).Alpenglow uses voting and certificate messages
listed in Tables 5 and 6.
```

```
Vote Type Object
Notarization Vote NotarVote(slot(b),hash(b))
Notar-Fallback Vote NotarFallbackVote(slot(b),hash(b))
Skip Vote SkipVote(s)
Skip-Fallback Vote SkipFallbackVote(s)
Finalization Vote FinalVote(s)
```
```
Table 5: Alpenglow’s voting messages with respect to blockband slots. Each
object is signed by a signatureσvof the voting nodev.
```
```
Certificate Type Aggregated Votes Condition
Fast-Finalization Cert. NotarVote Σ≥80%
Notarization Cert. NotarVote Σ≥60%
Notar-Fallback Cert. NotarVoteorNotarFallbackVote Σ≥60%
Skip Cert. SkipVoteorSkipFallbackVote Σ≥60%
Finalization Cert. FinalVote Σ≥60%
```
```
Table 6: Alpenglow’s certificate messages. Σ is the cumulative stake of the
aggregated votes (σi)I⊆{ 1 ,...,n}in the certificate, i.e., Σ =
```
#### P

Protocol i∈Iρi.

### 2.5 Pool

```
Every node maintains a data structure calledPool. In its Pool, each node
memorizes all votes and certificates for every slot.
```
```
Definition 12(storing votes).Pool stores received votes for every slot and
every node as follows:
```
- The first received notarization or skip vote,
- up to 3 received notar-fallback votes,
- the first received skip-fallback vote, and
- the first received finalization vote.

```
Definition 13(certificates). Pool generates, stores and broadcasts certifi-
cates:
```
- When enough votes (see Table 6) are received, the respective certificate
    is generated.
- When a received or constructed certificate is newly added to Pool, the
    certificate is broadcast to all other nodes.


- A single (received or constructed) certificate of each type corresponding
    to the given block/slot is stored in Pool.

```
Note that the conditions in Table 6 imply that if a correct node generated
the Fast-Finalization Certificate, it also generated the Notarization Certifi-
cate, which in turn implies it generated the Notar-Fallback Certificate.
```
```
Definition 14(finalization). We have two ways to finalize a block:
```
- If a finalization certificate on slotsis in Pool, the unique notarized block
    in slotsis finalized (we call this slow-finalized).
- If a fast-finalization certificate on blockbis in Pool, the blockbis final-
    ized (fast-finalized).

```
Whenever a block is finalized (slow or fast), all ancestors of the block are
finalized first.
```
```
Definition 15(Pool events).The following events are emitted as input for
Algorithm 1:
```
- BlockNotarized(slot(b),hash(b)): Pool holds a notarization certificate for
    blockb.
- ParentReady(s,hash(b)): Slotsis the first of its leader window, and Pool
    holds a notarization or notar-fallback certificate for a previous blockb,
Protocoland skip certificates for every slots′sinceb, i.e., forslot(b)< s′< s.

As we will see later (Lemmas 20 and 35), for every slots, every cor-
rect node will cast exactly one notarization or skip vote. After casting this
initial vote, the node might emit events according to Definition 16 and cast
additional votes.
The eventSafeToNotar(s,b) indicates that it is not possible that some
blockb′̸=bcould be fast-finalized (Definition 14) in slots, and so it is safe
to issue the notar-fallback vote forb.
Similarly,SafeToSkip(s) indicates that it is not possible that any block
in slotscould be fast-finalized (Definition 14), and so it is safe to issue the
Intiuitionskip-fallback vote fors.

```
Definition 16(fallback events).Consider blockbin slots=slot(b). By
notar(b)denote the cumulative stake of nodes whose notarization votes for
blockbare in Pool, and byskip(s)denote the cumulative stake of nodes whose
skip votes for slotsare in Pool. Recall that by Definition 12 the stake of any
node can be counted only once per slot. The following events are emitted as
input for Algorithm 1:
```
- SafeToNotar(s,hash(b)): The event is only issued if the node voted in


```
slotsalready, but not to notarizeb. Moreover:
```
```
notar(b)≥40%or
```
#### 

```
skip(s) +notar(b)≥60%andnotar(b)≥20%
```
#### 

#### .

```
Ifsis the first slot in the leader window, the event is emitted. Otherwise,
blockbis retrieved in the repair procedure (Section 2.8) first, in order
to identify the parent of the block. Then, the event is emitted when Pool
contains the notar-fallback certificate for the parent as well.
```
- SafeToSkip(s): The event is only issued if the node voted in slotsal-
    ready, but not to skips. Moreover:

```
skip(s) +
```
#### X

```
b
```
notar(b)−max
b
notar(b)≥40%.
Protocol

### 2.6 Votor

```
Leader sends
```
```
Relays send
```
```
Notar. votes
```
```
Final. votes
```
```
notarization
```
```
fast-finalization
```
```
slow-finalization
```
```
Figure 7: Protocol overview: a full common case life cycle of a block in
Alpenglow.
```
```
The purpose of voting is to notarize and finalize blocks. Finalized blocks
constitute a single chain of parent references and indicate the output of the
protocol.
The protocol ensures that for every slot, either a skip certificate is created,
or some blockbis notarized (or notarized-fallback), such that all ancestors
ofbare also notarized. Condition thresholds ensure that a malicious leader
cannot prevent the creation of certificates needed for liveness. If many correct
nodes produced notarization votes for the same blockb, then all other correct
nodes will make notar-fallback votes forb. Otherwise, all correct nodes will
broadcast skip-fallback votes.
By Definition 14, a node can finalize a block as soon as it observes enough
notarization votes produced by other nodes immediately upon receiving a
block. However, a lower participation threshold is required to make a nota-
```

```
rization certificate. Then the node will send the finalization vote. Therefore,
blocks are finalized after one round of voting among nodes with 80% of the
stake, or two rounds of voting among nodes with 60% of the stake.
Nodes have local clocks and emit timeout events. Whenever a nodev’s
Pool emits the eventParentReady(s,...), it starts timeout timers correspond-
ing to all blocks of the leader window beginning with slots. The timeouts
are parametrized with two delays (pertaining to network synchrony):
```
- ∆block: This denotes the protocol-specified block time.
- ∆timeout: Denotes the rest of the possible delay (other than ∆block) be-
    tween setting the timeouts and receiving a correctly disseminated block.
    As a conservative global constant, ∆timeoutcan be set to (1∆ + 2∆)>
    (time needed for the leader to observe the certificates) + (latency of
Intuitionslice dissemination through Rotor).

```
Definition 17(timeout).When a nodev’s Pool emits the first eventParent-
Ready(s,...),Timeout(i)events for the leader window beginning withs(for
alli∈windowSlots(s)) are scheduled at the following times:
```
```
Timeout(i) :clock() + ∆timeout+ (i−s+ 1)·∆block.
```
```
The timeouts are set to correspond to the latest possible time of receiving
a block if the leader is correct and the network is synchronous. Timeouts can
be optimized, e.g., by fine-grained ∆ estimation or to address specific faults,
such as crash faults.
Note thatParentReady(s,...) is only emitted for the first slotsof a win-
dow. Therefore, (i−s+ 1)≥1 andTimeout(i) is never scheduled to be
emitted in the past.
```
```
Definition 18(Votor state).Votor (Algorithms 1 and 2) accesses state as-
sociated with each slot. The state of every slot is initialized to the empty set:
state←[∅,∅,...]. The following objects can be permanently added to the state
of any slots:
```
- ParentReady(hash(b)): Pool emitted the eventParentReady(s,hash(b)).
- Voted: The node has cast either a notarization vote or a skip vote in
    slots.
- VotedNotar(hash(b)): The node has cast a notarization vote on blockb
    in slots.
- BlockNotarized(hash(b)): Pool holds the notarization certificate for block
    bin slots.
- ItsOver: The node has cast the finalization vote in slots, and will not
    cast any more votes in slots.


- BadWindow: The node has cast at least one of these votes in slots: skip,
    skip-fallback, notar-fallback.

Additionally, every slot can be associated with a pending block, which is
initialized to bottom: pendingBlocks←[⊥,⊥,...]. ThependingBlocksare
blocks which will be revisited to calltryNotar(), as the tested condition
Protocolmight be met later.

```
Algorithm 1Votor, event loop, single-threaded
1:uponBlock(s,hash,hashparent)do
2: iftryNotar(Block(s,hash,hashparent))then
3: checkPendingBlocks()
4: else ifVoted̸∈state[s]then
5: pendingBlocks[s]←Block(s,hash,hashparent)
```
```
6:uponTimeout(s)do
7: ifVoted̸∈state[s]then
8: trySkipWindow(s)
```
```
9:uponBlockNotarized(s,hash(b))do
10: state[s]←state[s]∪{BlockNotarized(hash(b))}
11: tryFinal(s,hash(b))
```
```
12:uponParentReady(s,hash(b))do
13: state[s]←state[s]∪{ParentReady(hash(b))}
14: checkPendingBlocks()
15: setTimeouts(s) ▷start timer for all slots in this window
```
```
16:uponSafeToNotar(s,hash(b))do
17: trySkipWindow(s)
18: ifItsOver̸∈state[s]then
19: broadcastNotarFallbackVote(s,hash(b)) ▷notar-fallback vote
20: state[s]←state[s]∪{BadWindow}
```
```
21:uponSafeToSkip(s)do
22: trySkipWindow(s)
23: ifItsOver̸∈state[s]then
24: broadcastSkipFallbackVote(s) ▷skip-fallback vote
25: state[s]←state[s]∪{BadWindow}
```

Algorithm 2Votor, helper functions

```
1:functionwindowSlots(s)
2: returnarray with slot numbers of the leader window with slots
```
```
3:functionsetTimeouts(s) ▷ sis first slot of window
4: fori∈windowSlots(s)do ▷set timeouts for all slots
5: schedule eventTimeout(i) at timeclock()+∆timeout+(i−s+1)·∆block
```
```
6:▷Check if a notarization vote can be cast. ◁
7:functiontryNotar(Block(s,hash,hashparent))
8: ifVoted∈state[s]then
9: returnfalse
10: firstSlot←(sis the first slot in leader window) ▷boolean
11: if(firstSlotandParentReady(hashparent)∈state[s]
or(notfirstSlotandVotedNotar(hashparent)∈state[s−1])then
12: broadcastNotarVote(s,hash) ▷notarization vote
13: state[s]←state[s]∪{Voted,VotedNotar(hash)}
14: pendingBlocks[s]←⊥ ▷won’t vote notar a second time
15: tryFinal(s,hash) ▷maybe vote finalize as well
16: returntrue
17: returnfalse
```
```
18:functiontryFinal(s,hash(b))
19: ifBlockNotarized(hash(b))∈state[s]andVotedNotar(hash(b))∈state[s]
andBadWindow̸∈state[s]then
20: broadcastFinalVote(s) ▷finalization vote
21: state[s]←state[s]∪{ItsOver}
```
```
22:functiontrySkipWindow(s)
23: fork∈windowSlots(s)do ▷skip unvoted slots
24: ifVoted̸∈state[k]then
25: broadcastSkipVote(k) ▷skip vote
26: state[k]←state[k]∪{Voted,BadWindow}
27: pendingBlocks[k]←⊥ ▷won’t vote notar after skip
```
```
28:functioncheckPendingBlocks()
29: fors:pendingBlocks[s]̸=⊥do ▷iterate with increasings
30: tryNotar(pendingBlocks[s])
```

### 2.7 Block Creation

```
The leadervof the window beginning with slotsproduces blocks for all
slotswindowSlots(s) in the window. After the eventParentReady(s,hash(bp))
is emitted,vcan be sure that a blockbin slotswithbpas its parent will be
valid. In other words, other nodes will receive the certificates that resulted
invemittingParentReady(hash(bp)), and emit this event themselves. As a
result, all correct nodes will vote forb.
In the common case, only oneParentReady(s,hash(bp)) will be emitted for
a givens. Then,vhas to build its block on top ofbpand cannot “fork off”
the chain in any way. Ifvemits manyParentReady(s,hash(bp)) events for
different blocksbp(as a result of the previous leader misbehaving or network
delays),vcan build its block with any suchbpas its parent.
Algorithm 3 introduces an optimization wherevstarts building its block
“optimistically” before anyParentReady(s,hash(bp)) is emitted. Usuallyv
will receive some blockbpin slots−1 first, then observe a certificate forbp
after additional network delay, and only then emitParentReady(s,hash(bp)).
Algorithm 3 avoids this delay in the common case. Ifvstarted building
a block with parentbp, but then only emitsParentReady(s,hash(b′p)) where
b′p̸=bp,vwill then instead indicateb′pas the parent of the block in the
content of some slicet. In this case, slices 1,...,t−1 are ignored for the
purpose of execution.
We allow changing the indicated parent of a block only once, and only in
blocks in the first slot of a given window.
When a leader already observed someParentReady(s,...), the leader pro-
duces all blocks of its leader window without delays. As a result, the first block
b 0 always builds on some parentbpsuch thatvemittedParentReady(s,hash(bp)),
b 0 is the parent of the blockb 1 in slots+ 1,b 1 is the parent of the blockb 2
in slots+ 2, and so on.
```
```
ParentReady(s,b 1 )
bk 1
```
```
b^12 b^22 b^32 ··· bk 2
```
```
ParentReady(s,b′ 1 )
```
```
b 2 starts here with a different parentb′ 1
```
```
bk 1
```
```
b^12 b^22 b^32 ··· bk 2
```
Figure 8: Handover between leader windows withkslices per block. The
new leader starts to produce the first slice of its first block (b^12 ) as soon as
it received the last slice (bk 1 ) of the previous leader. The common case is
on top and the case where leader switches parents at the bottom, see also
ProtocolAlgorithm 3.


Algorithm 3Block creation for leader window starting with slots

```
1:wait untilblockbpin slots−1 receivedorParentReady(hash(bp))∈state[s]
2:b←generate a block with parentbpin slots ▷block being produced
3:t← 1 ▷slice index
4:whileParentReady(...)̸∈state[s]do ▷produce slices optimistically
5: Rotor(slicetofb)
6: t←t+ 1
7:ifParentReady(hash(bp))̸∈state[s]then ▷change parent, reset block
8: bp←anyb′such thatParentReady(hash(b′))∈state[s]
9: b←generate a block with parentbpin slotsstarting with slice indext
10:start←clock() ▷some parent is ready, set timeout
11:whileclock()<start+ ∆blockdo▷produce rest of block in normal slot time
12: Rotor(slicetofb)
13: t←t+ 1
14:forremaining slots of the windows′=s+ 1,s+ 2,...do
15: b←generate a block with parentbin slots′
16: Rotor(b) over ∆block
```
### 2.8 Repair

Repair is the process of retrieving a block with a given hash that is
missing from Blokstor. After Pool obtains a certificate of signatures on
Notar(slot(b),hash(b)) orNotarFallback(slot(b),hash(b)), the blockbwith hash
hash(b) according to Definition 4 needs to be retrieved.

Definition 19(repair functions). The protocol supports functions for the
repair process:

- sampleNode(): Choose some nodevat random based on stake.
- getSliceCount(hash(b),v): Contact nodev, which returns(k,rk,πk)where:
    - kis the number of slices ofbas in Definition 4,
    - rkis the hash at positionkwith pathπkfor Merkle roothash(b).

```
The requesting node needs to make surerkis the last non-zero leaf of the
Merkle tree with roothash(b). It verifies that the rightward intermediate
hashes inπkcorrespond to empty sub-trees.
```
- getSliceHash(t,hash(b),v): Contact nodev, which returns(rt,πt)where
    rtis the hash at positiontwith pathπtfor Merkle roothash(b).
- getShred(s,t,i,rt,v): Contact nodev, which returns the shred(s,t,i,zt,
    rt,(di,πi),σt)as in Definition 1.


The functions can fail verification of the data provided byvand return⊥
(e.g. if invalid data is returned orvsimply does not have the correct data to
Protocolreturn).

```
Algorithm 4Repair blockbwithhash(b) in slots
1:k←⊥
2:whilek=⊥do ▷find the number of sliceskinb
3: (k,rk,πk)←getSliceCount(hash(b),sampleNode())
4:fort= 1,...,kconcurrently do
5: whilert=⊥do ▷get slice hashrtif missing
6: (rt,πt)←getSliceHash(t,hash(b),sampleNode())
7: foreach shred indexiconcurrently do
8: whileshred with indicess,t,imissingdo ▷get shred if missing
9: shred←getShred(s,t,i,rt,sampleNode())
10: storeshredif valid
```
### 2.9 Safety

```
In the following analysis, whenever we say that a certificate exists, we
mean that a correct node observed the certificate. Whenever we say that an
ancestorb′of a blockbexists in some slots=slot(b′), we mean that starting
at blockband following the parent links in blocks with the given hash we
reach blockb′in slots=slot(b′).
```
```
Lemma 20(notarization or skip).A correct node exclusively casts only one
notarization vote or skip vote per slot.
```
```
Proof.Notarization votes and skip votes are only cast via functionstryNotar()
andtrySkipWindow() of Algorithm 2, respectively. Votes are only cast if
Voted̸∈state[s]. After voting, the state is modified so thatVoted∈state[s].
Therefore, a notarization or skip vote can only be cast once per slot by a
correct node.
```
```
Lemma 21(fast-finalization property). If a blockbis fast-finalized:
```
```
(i) no other blockb′in the same slot can be notarized,
```
```
(ii) no other blockb′in the same slot can be notarized-fallback,
```
```
(iii) there cannot exist a skip certificate for the same slot.
```
```
Proof.Suppose some correct node fast-finalized some blockbin slots. By
Definition 14, nodes holding at least 80% of stake cast notarization votes
forb. Recall (Assumption 1) that all byzantine nodes hold less than 20% of
stake. Therefore, a setV of correct nodes holding more than 60% of stake
cast notarization votes forb.
```

(i) By Lemma 20, nodes inVcannot cast a skip vote or a notarization vote
for a different blockb′̸=b. Therefore, the collective stake of nodes casting a
notarization vote forb′has to be smaller than 40%.
(ii) Correct nodes only cast notar-fallback votes in Algorithm 1 when
Pool emits the eventSafeToNotar. By Definition 16, a correct node emits
SafeToNotar(s,hash(b′)), if either a) at least 40% of stake holders voted to
notarizeb′, or b) at least 60% of stake holders voted to notarizeb′or skip slot
s. Only nodesv /∈V holding less than 40% of stake can vote to notarizeb′
or skip slots. Therefore, no correct nodes can vote to notar-fallbackb′.
(iii) Skip-fallback votes are only cast in Algorithm 1 by correct nodes if
Pool emits the eventSafeToSkip. By Definition 16, a correct node can emit
SafeToSkipif at least 40% of stake have cast a skip vote or a notarization vote
onb′̸=bin slots. Only nodesv /∈Vholding less than 40% of stake can cast
a skip vote or a notarization vote onb′̸=bin slots. Therefore, no correct
nodes vote to skip-fallback, and no nodes inV vote to skip or skip-fallback
slots.

Lemma 22.If a correct nodevcast a finalization vote in slots, thenvdid
not cast a notar-fallback or skip-fallback vote ins.

Proof.A correct node addsItsOverto its state of slotsin line 21 of Algo-
rithm 2 when casting a finalization vote. Notar-fallback or skip-fallback votes
can only be cast ifItsOver̸∈state[s] in lines 18 and 23 of Algorithm 1 respec-
tively. Therefore, notar-fallback and skip-fallback votes cannot be cast byv
in slotsafter casting a finalization vote in slots.
On the other hand, a correct node addsBadWindowto its state of slots
when casting a notar-fallback or skip-fallback vote in slots. A finalization
vote can only be cast ifBadWindow ̸∈state[s] in line 19 of Algorithm 2.
Therefore, a finalization vote cannot be cast byvin slotsafter casting a
notar-fallback and skip-fallback vote in slots.

Lemma 23.If correct nodes with more than 40% of stake cast notarization
votes for blockbin slots, no other block can be notarized in slots.

Proof.LetV be the set of correct nodes that cast notarization votes forb.
Suppose for contradiction someb′̸=bin slotsis notarized. Since 60% of
stake holders had to cast notarization votes forb′(Definition 11), there is
a nodev∈V that cast notarization votes for bothbandb′, contradicting
Lemma 20.

Lemma 24.At most one block can be notarized in a given slot.

Proof.Suppose a blockbis notarized. Since 60% of stake holders had to cast
notarization votes forb(Definition 11) and we assume all byzantine nodes
hold less than 20% of stake, then correct nodes with more than 40% of stake
cast notarization votes forb. By Lemma 23, no blockb′̸=bin the same slot
can be notarized.


Lemma 25.If a block is finalized by a correct node, the block is also notarized.

Proof.Ifbwas fast-finalized by some correct node, nodes with at least 80% of
the stake cast their notarization votes forb. Since byzantine nodes possess less
than 20% of stake, correct nodes with more than 60% of stake broadcast their
notarization votes, and correct nodes will observe a notarization certificate
forb.
Ifbwas slow-finalized by some correct node, nodes with at least 60% of
stake cast their finalization vote forb(Def. 11 and 14), including some correct
nodes. Correct nodes cast finalization votes only ifBlockNotarized(hash(b))∈
state[s] in line 19 of Algorithm 2 after they observe some notarization certifi-
cate. By Lemma 24, this notarization certificate has to be forb.

Lemma 26(slow-finalization property).If a blockbis slow-finalized:

```
(i) no other blockb′in the same slot can be notarized,
```
```
(ii) no other blockb′in the same slot can be notarized-fallback,
```
```
(iii) there cannot exist a skip certificate for the same slot.
```
Proof.Suppose some correct node slow-finalized some blockbin slots. By
Definition 14, nodes holding at least 60% of stake cast finalization votes in
slots. Recall that we assume all byzantine nodes to hold less than 20% of
stake. Therefore, a setVof correct nodes holding more than 40% of stake cast
finalization votes in slots. By condition in line 19 of Algorithm 2, nodes in
Vobserved a notarization certificate for some block. By Lemma 24, all nodes
inV observed a notarization certificate for the same blockb, and because of
the condition in line 19, all nodes inVpreviously cast a notarization vote for
b. By Lemmas 20 and 22, all nodes inV cast no votes in slotsother than
the notarization vote forband the finalization vote. Since nodes inV hold
more than 40% of stake, and every certificate requires at least 60% of stake
holder votes, no skip certificate or certificate on another blockb′̸=bin slot
scan be produced.

Lemma 27. If there exists a notarization or notar-fallback certificate for
blockb, then some correct node cast its notarization vote forb.

Proof.Suppose for contradiction no correct node cast its notarization vote for
b. Since byzantine nodes possess less than 20% of stake, every correct node
observed less than 20% of stake voting to notarizeb. Both sub-conditions for
emitting the eventSafeToNotar(s,hash(b)) by Definition 16 require observ-
ing 20% of stake voting to notarizeb. Therefore, no correct node emitted
SafeToNotar(s,hash(b)). In Algorithm 1, emittingSafeToNotar(s,hash(b)) is
the only trigger that might lead to casting a notar-fallback vote forb. There-
fore, no correct node cast a notar-fallback vote forb. However, at least 60%


of stake has to cast a notarization or notar-fallback vote forbfor a certificate
to exist (Definition 11), leading to a contradiction.

Lemma 28.If a correct nodevcast the notarization vote for blockbin slot
s=slot(b), then for every slots′≤ssuch thats′∈windowSlots(s),vcast
the notarization vote for the ancestorb′ofbin slots′=slot(b′).

Proof.Ifsis the first slot of the leader window, there are no slotss′< sin
the same window. Sincevvoted forbinswe are done. Supposesis not the
first slot of the window.
Due to the condition in line 11 of Algorithm 2,vhad to evaluate the lat-
ter leg of the condition (namely (notfirstSlotandVotedNotar(hashparent)∈
state[s−1])) totrueto cast a notarization vote forb. The objectVotedNotar(hash)
is added to the state of slots−1 only when casting a notarization vote on a
block with the givenhashin line 13. By induction,vcast notarization votes
for ancestors ofbin all slotss′< sin the same leader window.

Lemma 29.Suppose a correct nodevcast a notar-fallback vote for a block
bin slotsthat is not the first slot of the window, andb′is the parent ofb.
Then, either some correct node cast a notar-fallback vote forb′, or correct
nodes with more than 40% of stake cast notarization votes forb′.

Proof.SafeToNotarconditions (Definition 16) require thatvobserved a nota-
rization or notar-fallback certificate forb′, and so nodes with at least 60% of
stake cast notarization or notar-fallback votes forb′. Since byzantine nodes
possess less than 20% of stake, either correct nodes with more than 40% of
stake cast notarization votes forb′, or some correct node cast a notar-fallback
vote forb′.

Lemma 30. Suppose a blockbin slotsis notarized or notarized-fallback.
Then, for every slots′ ≤ssuch thats′ ∈windowSlots(s), there is an
ancestorb′ofbin slots′. Moreover, either correct nodes with more than
40% of stake cast notarization votes forb′, or some correct node cast a notar-
fallback vote forb′.

Proof.By Lemma 27, some correct node voted forb. By Lemma 28, for every
slots′≤ssuch thats′∈windowSlots(s), there is an ancestorb′ofbin
slots′.
Letb′be the parent ofbin slots−1. Suppose correct nodes with more
than 40% of stake cast notarization votes forb′. Then, the result follows by
Lemma 28 applied to each of these nodes.
Otherwise, by Lemma 29, either some correct node cast a notar-fallback
vote forb′, or correct nodes with more than 40% of stake cast notarization
votes forb′. By induction, the result follows for all ancestors ofbin the same
leader window.


```
Lemma 31.Suppose some correct node finalizes a blockbiandbkis a block in
the same leader window withslot(bi)≤slot(bk). If any correct node observes
a notarization or notar-fallback certificate forbk,bkis a descendant ofbi.
```
```
Proof.Supposebkis not a descendant ofbi. By Lemmas 21 and 26,slot(bi)̸=
slot(bk). Therefore,slot(bi)<slot(bk) andbkis not in the first slot of the
leader window. By Lemmas 27 and 25, some correct nodevcast a notarization
vote forbk. By Lemma 28, there is an ancestor ofbkin every slots′<slot(bk)
in the same leader window.
Letbjbe the ancestor ofbkin slotslot(bi) + 1.bkis not a descendant of
bi, so the parentb′iofbjin the same slot asbiis different frombi.
By Lemma 30, either correct nodes with more than 40% of stake cast
notarization votes forbj, or some correct node cast a notar-fallback vote for
bj. If a correct node cast a notar-fallback vote forbj, by Definition 16, the
parentb′iofbjin the same slot asbiis notarized, or notarized-fallback. That
would be a contradiction with Lemma 21 or 26. Otherwise, if correct nodes
with more than 40% of stake cast notarization votes forbj, by Lemma 28, these
nodes also cast notarization votes forb′i, a contradiction with Lemma 23.
```
```
Lemma 32.Suppose some correct node finalizes a blockbiandbkis a block
in a different leader window such thatslot(bi)<slot(bk). If any correct node
observes a notarization or notar-fallback certificate forbk,bkis a descendant
ofbi.
```
```
Proof.Letbjbe the highest ancestor ofbksuch thatslot(bi)≤slot(bj) and
bjis notarized or notarized-fallback. Ifbj is in the same leader window as
bi, we are done by Lemma 31; assume bj is not in the same leader win-
dow asbi. By Lemmas 27 and 28, some correct nodevcast a notariza-
tion vote for an ancestorb′jofbjin the first slotsof the same leader win-
dow. Due to the condition in line 11 of Algorithm 2,vhad to evaluate
the former leg of the condition (namelyfirstSlotandParentReady(hash(b))∈
state[s]) totrue(withs=slot(b′j)) to cast a notarization vote forb′j, where
bis the parent ofb′j. ParentReady(hash(b)) is added tostate[s] only when
ParentReady(s,hash(b)) is emitted. Note that by Definition 15, if a correct
node has emittedParentReady(s,hash(b)), thenbis notarized or notarized-
fallback. Ifslot(b)<slot(bi), by Definition 15 Pool holds a skip certificate
forslot(bi), contradicting Lemma 21 or 26. Ifslot(b) =slot(bi), sincebis
notarized or notarized-fallback, again Lemma 21 or 26 is violated. Due to
choice ofbj,slot(bi)<slot(b) is also impossible.
```
```
Theorem 1(safety).If any correct node finalizes a blockbin slotsand any
correct node finalizes any blockb′in any slots′≥s,b′is a descendant ofb.
```
Proof.By Lemma 25,b′is also notarized. By Lemmas 31 and 32,b′is a
Analysisdescendant ofb.


### 2.10 Liveness

Lemma 33.If a correct node emits the eventParentReady(s,...), then for
every slotkin the leader window beginning withsthe node will emit the event
Timeout(k).

Proof.The handler of eventParentReady(s,...) in line 12 of Algorithm 1 calls
the functionsetTimeouts(s) which schedules the eventTimeout(k) for every
slotkof the leader window containings(i.e.,k∈windowSlots(s)).

If a node scheduled the eventTimeout(k), we say that it set the timeout
for slotk.
Since the functionsetTimeouts(s) is called only in the handler of the
eventParentReady(s,...) in Algorithm 1, we can state the following corollary:

Corollary 34. If a node sets a timeout for slots, the node emitted an
eventParentReady(s′,hash(b)), wheres′is the first slot of the leader window
windowSlots(s).

Lemma 35.If all correct nodes set the timeout for slots, all correct nodes
will cast a notarization vote or skip vote in slots.

Proof.For any correct node that set the timeout for slots, the handler of event
Timeout(s) in line 6 of Algorithm 1 will call the functiontrySkipWindow(s),
unlessVoted∈state[s]. Next, eitherVoted̸∈state[s] in line 24 of Algorithm 2,
and the node casts a skip vote in slots, orVoted∈state[s]. The objectVoted
is added tostate[s] only when the node cast a notarization or skip vote in slot
s, and therefore the node must have cast either vote.

Lemma 36.If no set of correct nodes with more than 40% of stake cast their
notarization votes for the same block in slots, no correct node will add the
objectItsOvertostate[s].

Proof.ObjectItsOveris only added tostate[s] in line 21 of Algorithm 2 after
testing thatBlockNotarized(hash(b))∈state[s]. The objectBlockNotarized(hash(b))
is only added tostate[s] when the eventBlockNotarized(s,hash(b)) is handled
in Algorithm 1. By Definition 15, Pool needs to hold a notarization certificate
forbto emit the event. The certificate requires that 60% of stake voted to
notarizeb(Def. 11). Since we assume that byzantine nodes hold less than
20% of stake, correct nodes with more than 40% of stake need to cast their
notarization votes for the same block in slotsfor any correct node to add the
objectItsOvertostate[s].

Lemma 37. If all correct nodes set the timeout for slots, either the skip
certificate forsis eventually observed by all correct nodes, or correct nodes
with more than 40% of stake cast notarization votes for the same block in slot
s.


Proof.Suppose no set of correct nodes with more than 40% of stake cast their
notarization votes for the same block in slots.
Since all correct nodes set the timeout for slots, by Lemma 35, all correct
nodes will observe skip votes or notarization votes in slotsfrom a setSof
correct nodes with at least 80% of stake (Assumption 1).
Consider any correct nodev∈S. As in Definition 16, bynotar(b) denote
the cumulative stake of nodes whose notarization votes for blockbin slot
s=slot(b) are inv’s Pool, and byskip(s) denote the cumulative stake of
nodes whose skip votes for slotsare in Pool ofv. Letwbe the stake of
nodes outside ofSwhose notarization or skip votevobserved. Then, afterv
received votes of nodes inS:skip(s) +

#### P

bnotar(b) = 80% +w. Since no set
of correct nodes with more than 40% of stake cast their notarization votes for
the same block in slots, maxbnotar(b)≤40% +w. Therefore,

```
skip(s) +
```
#### X

```
b
```
```
notar(b)−max
b
```
```
notar(b) =
```
```
80% +w−max
b
```
```
notar(b)≥
```
```
80% +w−(40% +w) = 40%.
```
Therefore, ifvhas not cast a skip vote fors,vwill emit the eventSafeToSkip(s).
By Lemma 36,vwill test thatItsOver̸∈state[s] in line 23 of Algorithm 1,
and cast a skip-fallback vote fors.
Therefore, all correct node will cast a skip or skip-fallback vote forsand
observe a skip certificate fors.

Lemma 38.If correct nodes with more than 40% of stake cast notarization
votes for blockb, all correct nodes will observe a notar-fallback certificate for
b.

Proof.Reason by induction on the difference betweenslot(b) and the first slot
inwindowSlots(slot(b)).
Supposeslot(b) is the first slot in the window. Suppose for contradiction
some correct nodevwill not cast a notarization or notar-fallback vote forb.
Sincevwill observe the notarization votes of correct nodes with more than
40% of stake, by Definition 16vwill emitSafeToNotar(slot(b),hash(b)).
The objectItsOveris added tostate[slot(b)] in line 21 of Algorithm 2 after
casting a finalization vote. The condition in line 19 ensures thatvcast a
notarization vote for a notarized blockb′. However, by Lemma 23, there can
be no suchb′̸=bin the same slot, andvhas not cast the notarization vote
forb.
When triggered bySafeToNotar(slot(b),hash(b)),vwill test thatItsOver̸∈
state[s] in line 18 and cast the notar-fallback vote forb, a contradiction.
Therefore, all correct nodes will cast a notarization or notar-fallback vote
forb, and observe a notar-fallback certificate forb.


Next, supposeslot(b) is not the first slot in the window and assume the
induction hypothesis holds for the previous slot.
Suppose for contradiction some correct nodevwill not cast a notarization
or notar-fallback vote forb. Sincevwill observe the notarization votes of
correct nodes with more than 40% of stake, by Definition 16vwill retrieve
blockband identify its parentb′. By Lemma 28, the correct nodes that
cast notarization votes forbalso voted forb′, andslot(b′) =slot(b)−1. By
induction hypothesis,vwill observe a notar-fallback certificate forb′, and
emitSafeToNotar(slot(b),hash(b)). Identically to the argument above,vwill
cast the notar-fallback vote forb, causing a contradiction.
Therefore, all correct nodes will cast a notarization or notar-fallback vote
forb, and observe a notar-fallback certificate forb.

Lemma 39.If all correct nodes set the timeouts for slots of the leader window
windowSlots(s), then for every slots′∈windowSlots(s)all correct nodes
will observe a notar-fallback certificate forbin slots′=slot(b), or a skip
certificate fors′.

Proof.If correct nodes observe skip certificates in all slotss′∈windowSlots(s),
we are done. Otherwise, lets′∈windowSlots(s) be any slot for which a
correct node will not observe a skip certificate. By Lemma 37, there is a block
bin slots′=slot(b) such that correct nodes with more than 40% of stake
cast the notarization vote forb. By Lemma 38, correct nodes will observe a
notar-fallback certificate forb.

Lemma 40.If all correct nodes set the timeouts for slotswindowSlots(s),
then all correct nodes will emit the eventParentReady(s+,...), wheres+> s
is the first slot of the following leader window.

Proof.Consider two cases:

```
(i) all correct nodes observe skip certificates for all slots inwindowSlots(s);
```
```
(ii) some correct node does not observe a skip certificate for some slots′∈
windowSlots(s).
```
(i) Consider some correct nodev. By Corollary 34,vhad emitted an
eventParentReady(k,hash(b)), wherekis the first slot ofwindowSlots(s).
By Definition 15, there is a blockb, such thatvobserved a notar-fallback
certificate forb, and skip certificates for all slotsisuch thatslot(b)< i < k.
Sincevwill observe skip certificates for all slots inwindowSlots(s),vwill
observe skip certificates for all slotsisuch thatslot(b)< i < s+. By 15,v
will emitParentReady(s+,hash(b).
(ii) Lets′be the highest slot inwindowSlots(s) for which some correct
nodevwill not observe a skip certificate. By Lemma 39,vwill observe a
notar-fallback certificate for some blockbin slots′=slot(b). By definition of


s′,vwill observe skip certificates for all slotsisuch thatslot(b)< i < s+. By
15,vwill emitParentReady(s+,hash(b).

Lemma 41.All correct nodes will set the timeouts for all slots.

Proof.Follows by induction from Lemma 33 and Lemma 40.

Lemma 42.Suppose it is after GST and the first correct nodevset the
timeout for the first slotsof a leader windowwindowSlots(s)at timet.
Then, all correct nodes will emit some eventParentReady(s,hash(b))and set
timeouts for slots inwindowSlots(s)by timet+ ∆.

Proof.By Corollary 34 and Definition 15,vobserved a notar-fallback certifi-
cate for some blockband skip certificates for all slotsisuch thatslot(b)<
i < sby timet. Sincevis correct, it broadcast the certificates, which were
also observed by all correct nodes by timet+ ∆. Therefore, all correct nodes
emittedParentReady(s,hash(b)) by timet+ ∆ and set the timeouts for all
slots inwindowSlots(s).

Theorem 2(liveness). Letvℓ be a correct leader of a leader window be-
ginning with slots. Suppose no correct node set the timeouts for slots in
windowSlots(s)before GST, and that Rotor is successful for all slots in
windowSlots(s). Then, blocks produced byvℓin all slotswindowSlots(s)
will be finalized by all correct nodes.

Proof.The intuitive outline of the proof is as follows:

(1) We calculate the time by which correct nodes receive blocks.

(2) Suppose for contradiction some correct nodevcast a skip vote. We argue
thatvcast a skip vote in every slotk′≥k,k′∈windowSlots(s).

(3) We consider different causes for the first skip vote cast byv. We determine
that someTimeout(j) resulted in casting a skip vote byvbefore any
SafeToNotarorSafeToSkipis emitted in the window.

(4) We argue thatTimeout(k) can only be emitted aftervhas already received
a block and cast a notarization vote in slotk, a contradiction.

(1) By Lemma 41, all correct nodes will set the timeouts fors. Lettbe
the time at which the first correct node sets the timeout fors. Sincet≥
GST, by Lemma 42,vℓemittedParentReady(s,hash(b)) for someband added
ParentReady(hash(b)) tostate[s] in line 13 of Algorithm 1 by timet+ ∆. Con-
ditions in lines 1 and 4 of Algorithm 3 imply that afterParentReady(hash(b))∈
state[s],vℓproceeded to line 10 by timet+ ∆. According to lines 11 and 16,
vℓwill finish transmission of a blockbkin slotk∈windowSlots(s) by time
t+∆+(k−s+1)·∆block. Since Rotor is successful for slots inwindowSlots(s),


correct nodes will receive the block in slotk∈windowSlots(s) by time
t+ 3∆ + (k−s+ 1)·∆block.
(2) Suppose for contradiction, some correct nodevwill not cast a nota-
rization vote for somebk, and letkbe the lowest such slot. Sincevℓis correct,
the only valid block received by any party in slotkisbk, andvcannot cast a
different notarization vote in slotk. By Lemma 35,vwill cast a skip vote in
slotk. Moreover,vcannot cast a notarization vote in any slotk′> kin the
leader window, due to the latter leg of the condition in line 11 of Algorithm 2
(i.e. notfirstSlotandVotedNotar(hashparent)∈state[k′−1]). Therefore,v
cast a skip vote in every slotk′≥k,k′∈windowSlots(s).
(3) Skip votes in slotkare cast bytrySkipWindow(j) in Algorithm 2,
wherej∈windowSlots(s). The functiontrySkipWindow(j) is called af-
ter handlingSafeToNotar(j,...),SafeToSkip(j), orTimeout(j) in Algorithm 1.
Letjbe the slot such that the first skip vote ofvfor a slot inwindowSlots(s)
resulted from handlingSafeToNotar(j,...),SafeToSkip(j), orTimeout(j). Con-
sider the following cases:

- SafeToNotar(j,...): Ifj < k, by definition ofk, all correct nodes cast
    notarization votes forbj. Therefore,SafeToNotar(j,...) cannot be emit-
    ted by a correct node. Therefore,j≥k.SafeToNotar(j,...) requiresv
    to cast a skip vote in slotjfirst. Therefore,vcast a skip vote for slot
    jbefore emittingSafeToNotar(j,...), a contradiction.
- SafeToSkip(j): Similarly toSafeToNotar, the event cannot be emitted
    by a correct node forj < k, and requires thatvcast some skip vote for
    slotj≥kbefore it is emitted, a contradiction.
- Timeout(j): Due to the condition when handling the event in line 6 of
    Algorithm 1, the event does not have any effect ifvcast a notarization
    vote in slotj. Moreover,vcannot cast a notarization vote in slotjif
    Timeout(j) was emitted beforehand. Sincevcast notarization votes in
    slots of the window lower thank, thenj≥k. Since the eventTimeout(j)
    is scheduled at a higher time for a higher slot in line 5 of Algorithm 2,
    the time at whichTimeout(k) is emitted is the earliest possible time at
    whichvcast the first skip vote in the window.

(4) Sincetis the time at which the first correct node set the timeout for
slots,vemittedTimeout(k) at timet′≥t+ ∆timeout+ (k−s+ 1)·∆block≥
t+ 3∆ + (k−s+ 1)·∆block. However, as calculated above,vhas received
bifor alls≤i≤kby that time. Analogously to Lemma 42,vhas also
emittedParentReady(s,hash(b)) and addedParentReady(hash(b)) tostate[s],
wherebis the parent ofbs. The condition in line 11 is satisfied whenvcalls
tryNotar(Block(s,hash(bs),hash(b))), andvcast a notarization vote forbs.
SincecheckPendingBlocks() is called in lines 3 and 14 of Algorithm 1
when handlingBlockandParentReadyevents,vcast a notarization vote for
bifor alls≤i≤kby the timeTimeout(k) is emitted, irrespectively of the


order in whichbiwere received. This contradicts the choice ofvas a node
that did not cast a notarization vote forbk.
Since for allk ∈windowSlots(s) all correct nodes cast notarization
votes forbk, all correct nodes will observe the fast-finalization certificate for
Analysisbkand finalizebk.

### 2.11 Higher Crash Resilience

```
In this section we sketch the intuition behind Alpenglow’s correctness in
less adversarial network conditions, but with more crash faults.
In harsh network conditions Alpenglow can be attacked by an adversary
with over 20% of stake. However, such an attack requires careful orchestra-
tion. Unintentional mistakes, crash faults and denial-of-service attacks (which
are functionally akin to crash faults) have historically caused more problems
for blockchain systems. In the rest of this section, we will consider Assump-
tion 2 instead of Assumption 1. Additionally, Assumption 3 captures on a
high level the attacker’s lesser control over the network.
```
```
Assumption 3(Rotor non-equivocation). If a correct node receives a full
blockbvia Rotor (Section 2.2), any other correct node that receives a full
block via Rotor for the same slot, receives the same blockb.
```
```
Note that crashed nodes are functionally equivalent to nodes exhibiting
indefinite network delay. In Section 2.9 we have demonstrated that Alpenglow
is safe with arbitrarily large network delays, which are possible in our model.
Therefore, safety is ensured under Assumption 2.
The reasoning behind liveness (Section 2.10) is affected by Assumption 2
whenever we argue that correct nodes will observe enough votes to trigger the
conditions of Definition 16 (SafeToNotarandSafeToSkip). However, with the
additional Assumption 3 that two correct nodes cannot reconstruct a different
block in the same slot, eitherSafeToNotarorSafeToSkiphas to be emitted
by all correct nodes after they observe the votes of other correct nodes. If
correct nodes with at least 20% of stake voted to notarize a block, then the
condition:

skip(s) +notar(b)≥60%andnotar(b)≥20%
```
#### 

```
will be satisfied after votes of all correct nodes are observed. Otherwise,
```
```
skip(s) +
```
#### X

```
b
```
```
notar(b)−max
b
notar(b)≥skip(s)≥40%
```
```
will be satisfied.
```
```
Corollary 43.Theorem 2 holds under Assumptions 2 and 3 instead of As-
sumption 1.
```

```
Note that if the leader is correct or crashed, Assumption 3 is never vi-
olated, as the leader would produce at most one block per slot. Therefore,
crash-only faults amounting to less than 40% of stake are always tolerated.
To conclude, we intuitively sketch the conditions in which Assumption 3
can be violated by an adversary distributing different blocks to different par-
ties. If there are also many crash nodes in this scenario, correct nodes might
not observe enough votes to emitSafeToNotarorSafeToSkip, and the protocol
could get stuck.
Suppose a malicious leader attempts to distribute two different blocksb
andb′such that some correct nodes reconstruct and vote forb, while other
correct nodes reconstruct and vote forb′. If a correct node receives two
shreds not belonging to the same block (having a different Merkle root for
the same slice index) before being able to reconstruct the block, the node
will not vote for the block. Therefore, network topology and sampling of
Rotor relays determines the feasibility of distributing two different blocks to
different correct nodes.
```
```
Example 44.Consider two clusters of correct nodesAandB, such that the
network latency within a cluster is negligible in relation to the network latency
betweenAandB. EachAandBare comprised of nodes with 31% of stake.
The adversary controls 18% of stake, and 20% of stake is crashed. The Rotor
relays inAreceive shreds for a blockbAfrom a malicious leader, while Rotor
relays inBreceive shreds for a blockbB. The Rotor relays controlled by the
adversary forward shreds ofbAtoA, and shreds ofbBtoB. Due to the delay
betweenAandB, nodes inAwill reconstructbAbefore observing any shred
ofbB. Similarly forBandbB. Assumption 3 is violated in this scenario.
```
If the network topology has uniformly distributed nodes, it is harder to
arrange for large groups to receive enough shreds of a slice ofbbefore receiving
Analysisany shreds of a corresponding slice ofb′.

## 3 Beyond Consensus

This section describes a few issues that are not directly in the core of
the consensus protocol but deserve attention. We start with three issues
(sampling, rewards, execution) closely related to consensus, then we move on
to advanced failure handling, and we finish the section with bandwidth and
Intiuitionlatency simulation measurement results.


### 3.1 Smart Sampling

```
To improve resilience of Rotor in practice, we use a novel committee
sampling scheme. It is inspired by FA1 [GKR23] and improves upon FA1-
IID. It takes the idea of reducing variance in the sampling further.
```
```
Definition 45.Given a number of binskand relative stakes 0 < ρ 1 ,...,ρn<
1. Apartitioningof these stakes is a mapping
```
```
p:{ 1 ,...,k}×{ 1 ,...,n}→[0,1]R,
```
```
such that:
```
- stakes are fully assigned, i.e.,∀v∈{ 1 ,...,n}:

#### P

```
b∈{ 1 ,...,k}p(b,v) =ρv,
and
```
- bins are filled entirely, i.e.,∀b∈{ 1 ,...,k}:

#### P

```
v∈{ 1 ,...,n}p(b,v) = 1/k.
A procedure that for any number of binskand relative stakesρ 1 ,...,ρncal-
culates a valid partitioning is called apartitioning algorithm.
```
```
Definition 46.Our committee sampling scheme, calledpartition samplingor
PS-P, is instantiated with a specific partitioning algorithmP. It then proceeds
as follows to generate a single set ofΓsamples:
```
1. For each node with relative stakeρi> 1 /Γ, fill⌊ρiΓ⌋bins with that node.
    The remaining stake isρ′i=ρi−⌊ρiΓΓ⌋< 1 /Γ. For all other nodes, the
    remaining stake is their original stake:ρ′i=ρi
2. Calculate a partitioning for stakesρ′ 1 ,...,ρ′ninto the remainingk=
    Γ−

#### P

```
i∈[n]⌊ρiΓ⌋bins according toP.
```
3. From each bin, sample one node proportional to their stake.

One simple example for a partitioning algorithm randomly orders nodes,
and make cuts exactly after every 1/krelative stake.PS-Pinstantiated with
this simple partitioning algorithm is already better than the published state
Protocolof the art [GKR23]. However, this topic deserves more research.

```
Next, we show thatPS-Pimproves upon IID and FA1-IID. LetAdenote
the adversary andρAthe total stake they control, possibly spread over many
nodes. Further, assumeρA< γ/Γ = 1/κand thereforeγ < ρAΓ.
```
```
Lemma 47.For any stake distribution withρi< 1 /Γfor alli∈ { 1 ,...,n},
any partitioning algorithmP, adversaryAbeing sampled at leastγtimes in
PS-Pis at most as likely as likely as in IID stake-weighted sampling.
```
```
Proof.For any partitioning, in step 3 of Definition 46, the number of sam-
ples for the adversary is Poisson binomial distributed, i.e., it is the number
```

```
of successes in Γ independent Bernoulli trials (possibly with different prob-
abilities). The success probability of each trial is the proportion of stake in
each bin the adversary controls. Consider the case whereAachieves to be
packed equally in all Γ bins. In that case, the number of samples from the
adversary follows the Binomial distribution withp=ρA. This is the same
as for IID stake-weighted sampling. Also, the Binomial case is also known to
be maximizing the variance for Poisson binomial distributions [Hoe56], thus
maximizing the probability for the adversary to get sampled at leastγ <Γ
times.
```
```
Theorem 3.For any stake distribution, adversaryAbeing sampled at least
γtimes inPS-Pis at most as likely as in FA1-IID.
```
```
Proof.Because of step 1 of in Definition 46, applying our scheme directly is
equivalent to using FA1 with our scheme as the fallback scheme it is instan-
tiated with. Therefore, together with Lemma 47, the statement follows.
```
```
Finally, we practically analyze how this sampling scheme compares to
regular stake-weighted IID sampling and FA1-IID on the current Solana stake
distribution.
```
```
40% 30% 20%
```
```
10 −^12
```
```
10 −^8
```
```
10 −^4
```
```
100
```
```
Crashed nodes (by stake)
```
```
Failure probability
```
```
Crashes (γ= 32,Γ = 64)
```
```
PS-P
FA1-IID
Stake-weighted
Turbine
```
```
64 128 256
```
```
10 −^12
```
```
10 −^8
```
```
10 −^4
```
```
100
```
```
Total shreds (Γ)
```
```
Failure probability
```
```
40% Crashes (κ= 2)
```
```
PS-P
FA1-IID
Stake-weighted
Turbine
```
Figure 9: Probabilities that Rotor is not successful when experiencing crash
failures, when instantiated withPS-P(with fully randomized partitioning)
compared to other sampling techniques. This assumes 64 slices per block
Analysis(Rotor is only successful for the block if it is successful for every slice).


### 3.2 Voting vs. Execution

```
In Section 2, we omitted the execution of the blocks and the transactions
therein. Currently, Solana uses the synchronous execution model described
below.
```
```
Eager (Synchronous) Execution. The leader executes the block before
sending it, and all nodes execute the block before voting for it. With the
slices being pipelined (the next slice is propagated while the previous slice
is executed), this may add some time to the critical path, since we need to
execute the last slice before we can send a notarization vote for the block.
```
```
Lazy (Asynchronous) Execution. We can also vote on a block before
executing it. We need to make sure that the Compute Units (CUs) reflect
actual execution costs. This way the CU bounds on transactions and the
whole block guarantee that blocks are executed timely. If CUs are unrealis-
tically optimistic, this cannot work since execution delays may grow without
bounds.
```
Distributed Execution. Another active area of research is distributed ex-
ecution, which is related to this discussion about execution model. In dis-
tributed execution validators use multiple machines (co-located for minimal
latency) for executing transactions. Ideally, in contrast to executions on a
single machine, this allows the system to scale to higher transaction through-
puts. It also allows nodes to respond to surges in traffic without always
over-provisioning (this is called elasticity). Examples of this line of research
Intiuitionare Pilotfish [Kni+25] and Stingray [SSK25].

### 3.3 Asynchrony in Practice

In our model assumptions of Section 1.5 we assumed that delayed mes-
sages are eventually delivered. While this is a standard model in distributed
computing, in reality (as well as in the original formulation of partial syn-
chrony with GST [DLS88]) messages might be lost. Note that we already
allow asynchrony (arbitrarily long message delays), so our protocol is safe
even if messages are dropped. In this section we discuss two mechanisms en-
hancing Alpenglow to address network reality in practice, to restore liveness
Intiuitionif the protocol makes no progress.

```
Joining. Nodes might go offline for a period of time and miss all of the
messages delivered during that time. We note that if a rebooting or newly
joining node observes a finalization of blockbin slots, it is not necessary
to observe any vote or certificate messages for earlier slots. Due to safety
(Theorem 1), any future block in a slots′≥sthat might be finalized will be
a descendant ofb, and if any correct node emits the eventParentReady(s′,b′),
```

```
b′has to be a descendant ofb.
Rebooting or joining nodes need to observe a fast-finalization certificate for
a blockbin slots, or a finalization certificate forstogether with a notarization
certificate forbin the same slots. Blockbcan be retrieved with Repair
Section 2.8. The parent ofbcan be identified and retrieved afterbis stored,
and so on. A practical implementation might retrieve any missing blocks for
all slots in parallel, before verifying and repairing all ancestors ofb.
```
Standstill. Eventual delivery of messages needs to be ensured to guarantee
liveness after GST. As noted above, if a correct node observes a finalization
in slots, no vote or certificate messages for slots earlier thansare needed
for liveness. Lack of liveness can be detected simply by observing a period
of time without new slots being finalized. After some parametrized amount
of time, e.g., ∆standstill≈10 sec in which the highest finalized slot stays the
same, correct nodes trigger a re-transmission routine. Then, nodes broadcast
a finalization certificate for the highest slot observed (either a fast-finalization
certificate for a blockbin slots, or a finalization certificate forstogether with
a notarization certificate forbin the same slots). Moreover, for all higher
slotss′> s, nodes broadcast observed certificates and own votes cast in these
Protocolslots.

### 3.4 Dynamic Timeouts

Alpenglow is defined in the partially synchronous model, but strictly
speaking, epochs deviate from partial synchrony. For epoch changes to work,
at least one block needs to be finalized in each epoch. A finalized block in
epochemakes sure that the previous epoche−1 ended with an agreed-upon
state. This is important for setting the stage of epoche+ 1, i.e., to make
sure that there is agreement on the nodes and their stake at the beginning of
Intiuitionepoche+ 1.

Our solution is to extend timeouts if the situation looks dire. More
precisely, if a node does not have a finalized block in ∆standstill≈10 sec of
consecutive leader windows, the node will start extending its timeouts by
ε≈5% in every leader window.
Note that the nodes do not need coordination in extending the timeouts.
As soon as nodes see finalized blocks again, they can return to the standard
timeouts immediately as described in Section 2.6. Also when returning to
normal timeouts, no agreement or coordination is needed, and some nodes
can still have longer timeouts without jeopardizing the correctness of the
system.
Increasing timeouts byε≈5% in every leader window results in expo-
nential growth. With exponential growth, timeouts quickly become longer
than any extraordinary network delay caused by any network/power disaster.
ProtocolTherefore, it can be guaranteed that we have a finalized slot in each epoch.


### 3.5 Protocol Parameters

```
Throughout the document we have introduced various parameters. Ta-
ble 10 shows how we set the parameters in our preliminary simulations. Test-
ing is needed to ultimately decide these parameters.
Some parameters are set implicitly, and will be different in every epoch.
This includes in particular the parameter for the number of nodesn. Through-
out this paper we usedn≈ 1 ,500 for the number of nodes. The reality at the
time of writing is closer ton≈ 1 ,300.
```
```
Blocks per leader windoww 4
Data shreds per sliceγ 32
Coding shreds per slice Γ 64
Timeout increaseε 5%
Maximum nodesnmax 2,000
Standstill trigger ∆standstill 10 sec
Block time ∆block 400 ms
Epoch lengthL 18,000 slots
```
Protocol Table 10: Protocol Parameters.

### 3.6 Bandwidth

```
In this section we analyze the bandwidth usage of Alpenglow. Table 11
lists the size of Votor-related messages. As a bandwidth optimization, only
one of the finalization certificates should be broadcast (whichever is observed
first). Then, in the common case, every node broadcasts a notarization vote,
finalization vote, notarization certificate and one of the finalization certificates
for every slot. If we account for the larger of the finalization certificates (fast-
finalization), forn= 1,500, a node transmits (196 + 384 + 384 + 164)· 1 , 500
bytes for every 400 ms slot, which corresponds to 32.27 Mbit/s. The total
```

```
outgoing bandwidth is plotted in Figure 12.
```
```
Message BLS Sig.
Slot NumberBlock HashNode Bitmap
```
#### MAC

```
Headers
```
```
Total
```
```
notar. vote 96 8 32 – 32 28 196
notar. cert. 96 8 32 188 32 28 384
fast-final. cert. 96 8 32 188 32 28 384
final. vote 96 8 – – 32 28 164
final. cert. 96 8 – 188 32 28 352
skip vote 96 8 – – 32 28 164
skip cert. 96 8 – 188 32 28 352
```
```
Table 11: Estimation of message sizes in bytes for a network comprised of
1,500 nodes.
```
```
0 200 400 600 800 1 , 000 1 , 200
```
```
101
```
```
102
```
```
103
```
```
104
```
```
Validators (from small to large)
```
```
Bandwidth [Mbps]
```
```
Up-Bandwidth Usage Histogram for 500 Mbps Goodput
```
```
Rotor
Votor
```
Figure 12: Bandwidth usage to achieve consistent goodput of 500 Mbps, i.e.,
Analysiswhere the leader role requires sending at 1 Gbps forκ= 2.


### 3.7 Latency

We simulated Alpenglow in a realistic environment. In particular, in our
simulation, the stake distribution is the same as Solana’s stake distribution at
the time of writing (epoch 780), and the latencies between nodes correspond to
real-world latency measurements. Some possible time delays are not included
in the simulation, in particular block execution time. Moreover, a different
stake distribution would change our results.
Figure 13 shows a latency histogram for the case when the block leader is
located in Zurich, Switzerland, our location at the time of writing. The leader
is fixed in Zurich, and each bar shows the average over 100,000 simulated
executions. The Rotor relays are chosen randomly, according to stake. We
plot simulated latencies to reach different stages of the Alpenglow protocol
against the fraction of the network that arrived at that stage.

- The green bars show the network latency. With the current node distri-
    bution of Solana, about 65% of Solana’s stake is within 50 ms network
    latency round-trip time) of Zurich. The long tail of stake has more than
    200 ms network latency from Zurich. The network latency serves as a
    natural lower bound for our plot, e.g., if a node is 100 ms from Zurich,
    then any protocol needs at least 100 ms to finalize a block at that node.
- The yellow bars show the delay incurred by Rotor, the first stage of our
    protocol. More precisely, the yellow bars show when the nodes received
    γshreds, enough to reconstruct a slice.
- The red bars mark the point in time when a node has received nota-
    rization votes from at least 60% of the stake.
- Finally, the blue bars show the actual finalization time. A node can
    finalize because they construct a fast-finalization certificate (having re-
    ceived 80% stake of the original notarization votes), or a finalization
    certificate (having received 60% of the finalization votes), or having
    received one of these certificates from a third party, whatever is first.


```
0 20 40 60 80 100
```
```
0
```
```
50
```
```
100
```
```
150
```
```
200
```
```
250
```
```
300
```
```
Validators reached [% of stake]
```
```
Latency [ms]
```
```
Alpenglow Latency Histogram for Leader in Zurich
```
```
Finalization
Notarization
Rotor
Network latency
```
```
Figure 13: For a fixed leader in Zurich with random relays we have: (i) the
last node in the network finalizes in less than 270 ms, (ii) the median node
finalizes almost as fast as the fastest ones, in roughly 115 ms.
```
```
0 20 40 60 80 100
```
```
0
```
```
50
```
```
100
```
```
150
```
```
200
```
```
250
```
```
300
```
```
Validators reached [% of stake]
```
```
Latency [ms]
```
```
Alpenglow Latency Histogram for Random Leaders
```
```
Finalization
Notarization
Rotor
Network latency
```
Figure 14: This plot is a generalized version of Figure 13, where the leader
is chosen randomly according to stake. While Zurich isnot“the center of
the Solana universe,” it is more central than the average leader. Hence the
numbers in this plot are a bit higher than in Figure 13, and the median
Analysisfinalization time is roughly 150 ms.


Thanks. We thank the following people for their input: Ittai Abraham, Zeta
Avarikioti, Emanuele Cesena, Igor Durovic, Yuval Efron, Pranav Garimidi, Sam
Kim, Charlie Li, Carl Lin, Julian Loss, Zarko Milosevic, Gabriela Moreira,
Karthik Narayan, Joachim Neu, Alexander Pyattaev, Ling Ren, Max Resnick,
Tim Roughgarden, Ashwin Sekar, Victor Shoup, Philip Taffet, Yann Vonlan-
then, Marko Vukoli ́c, Josef Widder, Wen Xu, Anatoly Yakovenko, Haoran Yi,
Yunhao Zhang.

## References

[Abr+21] Ittai Abraham, Kartik Nayak, Ling Ren, and Zhuolun Xiang. “Good-
case Latency of Byzantine Broadcast: A Complete Categorization”.
In:Proceedings of the ACM Symposium on Principles of Distributed
Computing (PODC). 2021, pages 331–341.

[Abr+17] Ittai Abraham et al. “Revisiting fast practical byzantine fault tol-
erance”. In:arXiv preprint arXiv:1712.01367(2017).

[Aru+24] Balaji Arun, Zekun Li, Florian Suri-Payer, Sourav Das, and Alexan-
der Spiegelman.Shoal++: High Throughput DAG-BFT Can Be Fast!
https : / / decentralizedthoughts. github. io / 2024 - 06 - 12 -
shoalpp/. 2024.

[Aru+25] Balaji Arun, Zekun Li, Florian Suri-Payer, Sourav Das, and Alexan-
der Spiegelman. “Shoal++: High Throughput DAG BFT Can Be
Fast and Robust!” In:22nd USENIX Symposium on Networked Sys-
tems Design and Implementation (NSDI). 2025.

[Bab+25] Kushal Babel et al. “Mysticeti: Reaching the Latency Limits with
Uncertified DAGs”. In:32nd Annual Network and Distributed Sys-
tem Security Symposium (NDSS). The Internet Society, 2025.

[Bon+03] Dan Boneh, Craig Gentry, Ben Lynn, and Hovav Shacham. “Ag-
gregate and verifiably encrypted signatures from bilinear maps”.
In:Advances in Cryptology (Eurocrypt), Warsaw, Poland. Springer.
2003, pages 416–432.

[BKM18] Ethan Buchman, Jae Kwon, and Zarko Milosevic.The latest gossip
on BFT consensus. arXiv:1807.04938,http://arxiv.org/abs/
1807.04938. 2018.

[CT05] Christian Cachin and Stefano Tessaro. “Asynchronous verifiable in-
formation dispersal”. In:24th IEEE Symposium on Reliable Dis-
tributed Systems (SRDS). IEEE. 2005, pages 191–201.

[CL99] Miguel Castro and Barbara Liskov. “Practical Byzantine Fault Tol-
erance”. In:Proceedings of the Third Symposium on Operating Sys-
tems Design and Implementation (OSDI). New Orleans, Louisiana,
USA, 1999, pages 173–186.


[CP23] Benjamin Y. Chan and Rafael Pass. “Simplex Consensus: A Simple
and Fast Consensus Protocol”. In:Theory of Cryptography (TCC),
Taipei, Taiwan. Taipei, Taiwan: Springer-Verlag, 2023, pages 452–
479.

[Con+24] Andrei Constantinescu, Diana Ghinea, Jakub Sliwinski, and Roger
Wattenhofer. “Brief Announcement: Unifying Partial Synchrony”.
In:38th International Symposium on Distributed Computing (DISC).
2024.

[Dan+22] George Danezis, Lefteris Kokoris-Kogias, Alberto Sonnino, and Alex-
ander Spiegelman. “Narwhal and Tusk: a DAG-based mempool and
efficient BFT consensus”. In:Proceedings of the Seventeenth Euro-
pean Conference on Computer Systems (EuroSys). 2022, pages 34–
50.

[Dod02] Yevgeniy Dodis. “Efficient construction of (distributed) verifiable
random functions”. In:Public Key Cryptography (PKC), Miami,
FL, USA. Springer. 2002, pages 1–17.

[DGV04] Partha Dutta, Rachid Guerraoui, and Marko Vukolic.The Complex-
ity of Asynchronous Byzantine Consensus.https://infoscience.
epfl.ch/server/api/core/bitstreams/19ce5930-31af-4489-
9551-d5d014b8c1f1/content. 2004.

[DLS88] Cynthia Dwork, Nancy A. Lynch, and Larry J. Stockmeyer. “Con-
sensus in the Presence of Partial Synchrony”. In:J. ACM 35.2
(1988), pages 288–323.

[FMW24] Austin Federa, Andrew McConnell, and Mateo Ward.DoubleZero
Protocol.https://doublezero.xyz/whitepaper.pdf. 2024.

[Fou19] Solana Foundation.Turbine–Solana’s Block Propagation Protocol
Solves the Scalability Trilemma.https : / / solana. com / news /
turbine---solana-s-block-propagation-protocol-solves-
the-scalability-trilemma. 2019.

[GKR23] Peter Gazi, Aggelos Kiayias, and Alexander Russell. “Fait Accom-
pli Committee Selection: Improving the Size-Security Tradeoff of
Stake-Based Committees”. In:ACM SIGSAC Conference on Com-
puter and Communications Security (CCS), Copenhagen, Denmark.
ACM, 2023, pages 845–858.

[GV07] Rachid Guerraoui and Marko Vukoli ́c. “Refined Quorum Systems”.
In:Proceedings of the 26th Annual ACM Aymposium on Principles
of Distributed Computing (PODC). 2007, pages 119–128.

[Gue+19] Guy Golan Gueta et al. “SBFT: A scalable and decentralized trust
infrastructure”. In:49th Annual IEEE/IFIP International Confer-
ence on Dependable Systems and Networks (DSN). 2019, pages 568–
580.


[Hoe56] Wassily Hoeffding. “On the distribution of the number of successes
in independent trials”. In:The Annals of Mathematical Statistics
(1956), pages 713–721.

[Kei+22] Idit Keidar, Oded Naor, Ouri Poupko, and Ehud Shapiro. “Cor-
dial miners: Fast and efficient consensus for every eventuality”. In:
arXiv:2205.09174(2022).

[Kni+25] Quentin Kniep, Lefteris Kokoris-Kogias, Alberto Sonnino, Igor Za-
blotchi, and Nuda Zhang. “Pilotfish: Distributed Execution for Scal-
able Blockchains”. In:Financial Cryptography and Data Security
(FC), Miyakojima, Japan. Apr. 2025.

[Kot+07] Ramakrishna Kotla, Lorenzo Alvisi, Mike Dahlin, Allen Clement,
and Edmund Wong. “Zyzzyva: speculative byzantine fault toler-
ance”. In:Proceedings of 21st Symposium on Operating Systems
Principles (SOSP). 2007, pages 45–58.

[Kur02] Klaus Kursawe. “Optimistic byzantine agreement”. In:21st IEEE
Symposium on Reliable Distributed Systems (DSN). IEEE. 2002,
pages 262–267.

[KTZ21] Petr Kuznetsov, Andrei Tonkikh, and Yan X Zhang. “Revisiting Op-
timal Resilience of Fast Byzantine Consensus”. In:Proceedings of the
ACM Symposium on Principles of Distributed Computing (PODC).
Virtual Event, Italy, 2021, pages 343–353.

[Lam03] Leslie Lamport. “Lower Bounds for Asynchronous Consensus”. In:
Future Directions in Distributed Computing: Research and Position
Papers. 2003, pages 22–23.

[LNS25] Andrew Lewis-Pye, Kartik Nayak, and Nibesh Shrestha.The Pipes
Model for Latency and Throughput Analysis. Cryptology ePrint Ar-
chive, Paper 2025/1116. 2025.url:https://eprint.iacr.org/
2025/1116.

[MA06] J-P Martin and Lorenzo Alvisi. “Fast byzantine consensus”. In:
IEEE Transactions on Dependable and Secure Computing(2006),
pages 202–215.

[Mer79] Ralph Charles Merkle.Secrecy, Authentication, and Public Key Sys-
tems. Stanford University, 1979.

[MRV99] Silvio Micali, Michael Rabin, and Salil Vadhan. “Verifiable random
functions”. In:40th Annual Symposium on Foundations of Com-
puter Science (FOCS). IEEE. 1999, pages 120–130.

[Mil+16] Andrew Miller, Yu Xia, Kyle Croman, Elaine Shi, and Dawn Song.
“The Honey Badger of BFT Protocols”. In:Proceedings of the ACM
SIGSAC Conference on Computer and Communications Security
(CCS). 2016, pages 31–42.

[PSL80] Marshall C. Pease, Robert E. Shostak, and Leslie Lamport. “Reach-
ing Agreement in the Presence of Faults”. In:J. ACM27.2 (1980),
pages 228–234.


[Pos84] Jon Postel.Standard for the Interchange of Ethernet Frames. RFC

894. Apr. 1984.

[RS60] Irving S Reed and Gustave Solomon. “Polynomial codes over certain
finite fields”. In:Journal of the society for industrial and applied
mathematics8.2 (1960), pages 300–304.

[Sho24] Victor Shoup. “Sing a Song of Simplex”. In:38th International Sym-
posium on Distributed Computing (DISC). Volume 319. Leibniz In-
ternational Proceedings in Informatics. Dagstuhl, Germany, 2024,
37:1–37:22.

[SSV25] Victor Shoup, Jakub Sliwinski, and Yann Vonlanthen. “Kudzu: Fast
and Simple High-Throughput BFT”. In:arXiv:2505.08771(2025).

[SKN25] Nibesh Shrestha, Aniket Kate, and Kartik Nayak. “Hydrangea: Op-
timistic Two-Round Partial Synchrony with One-Third Fault Re-
silience”. In:Cryptology ePrint Archive(2025).

[SR08] Yee Jiun Song and Robbert van Renesse. “Bosco: One-step byzan-
tine asynchronous consensus”. In:International Symposium on Dis-
tributed Computing (DISC). Springer. 2008, pages 438–450.

[Spi+22] Alexander Spiegelman, Neil Giridharan, Alberto Sonnino, and Lef-
teris Kokoris-Kogias. “Bullshark: DAG BFT protocols made practi-
cal”. In:Proceedings of the ACM SIGSAC Conference on Computer
and Communications Security (CCS). 2022, pages 2705–2718.

[SSK25] Srivatsan Sridhar, Alberto Sonnino, and Lefteris Kokoris-Kogias.
“Stingray: Fast Concurrent Transactions Without Consensus”. In:
arXiv preprint arXiv:2501.06531(2025).

[SDV19] Chrysoula Stathakopoulou, Tudor David, and Marko Vukolic. “Mir-
BFT: High-Throughput BFT for Blockchains”. In:arXiv:1906.05552
(2019).

[Von+24] Yann Vonlanthen, Jakub Sliwinski, Massimo Albarello, and Roger
Wattenhofer. “Banyan: Fast Rotating Leader BFT”. In:25th ACM
International Middleware Conference, Hong Kong, China. Dec. 2024.

[Yak18] Anatoly Yakovenko.Solana: A new architecture for a high perfor-
mance blockchain v0.8.13.https://solana.com/solana-whitepaper.
pdf. 2018.

[Yan+22] Lei Yang, Seo Jin Park, Mohammad Alizadeh, Sreeram Kannan, and
David Tse. “DispersedLedger: High-Throughput Byzantine Consen-
sus on Variable Bandwidth Networks”. In:19th USENIX Symposium
on Networked Systems Design and Implementation (NSDI). Renton,
WA, Apr. 2022, pages 493–512.

[Yin+19] Maofan Yin, Dahlia Malkhi, Michael K Reiter, Guy Golan Gueta,
and Ittai Abraham. “HotStuff: BFT Consensus with Linearity and
Responsiveness”. In:Proceedings of the ACM Symposium on Prin-
ciples of Distributed Computing (PODC). 2019, pages 347–356.


[Zha+11] Xin Zhang et al. “SCION: Scalability, Control, and Isolation on
Next-Generation Networks”. In:IEEE Symposium on Security and
Privacy (S&P). 2011, pages 212–227.


