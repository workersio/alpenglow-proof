
## Page 1

Solana Alpenglow Consensus
Increased Bandwidth, Reduced Latency

Quentin Kniep Jakub Sliwinski Roger Wattenhofer
Anza

White Paper v1.1, July 22, 2025

Abstract

In this paper we describe and analyze Alpenglow, a consensus protocol tailored for a global high-performance proof-of-stake blockchain.

The voting component *Votor* finalizes blocks in a single round of voting if 80% of the stake is participating, and in two rounds if only 60% of the stake is responsive. These voting modes are performed concurrently, such that finalization takes $\min(\delta_{80\%}, 2\delta_{60\%})$ time after a block has been distributed.

The fast block distribution component *Rotor* is based on erasure coding. Rotor utilizes the bandwidth of participating nodes proportionally to their stake, alleviating the leader bottleneck for high throughput. As a result, total available bandwidth is used asymptotically optimally.

Alpenglow features a distinctive “20+20” resilience, wherein the protocol can tolerate harsh network conditions and an adversary controlling 20% of the stake. An additional 20% of the stake can be offline if the network assumptions are stronger.

1 Introduction

“I think there is a world market for maybe five computers.” – This quote is often attributed to Thomas J. Watson, president of IBM. It is disputed whether Watson ever said this, but it was certainly in the spirit of the time as similar quotes exist, e.g., by Howard H. Aiken. The quote was often made fun of in the last decades, but if we move one word, we can probably agree: “I think there is a market for maybe five *world* computers.”

So, what is a *world computer*? In many ways a world computer is like a common desktop/laptop computer that takes commands (“transactions”) as input and then changes its bookkeeping (“internal state”) accordingly. A world computer provides a shared environment for users from all over the world. Moreover, a world computer itself is distributed over the entire world:

&lt;page_number&gt;1&lt;/page_number&gt;

---


## Page 2

Instead of just having a single processor, we have dozens, hundreds or thousands of processors, connected through the internet.

Such a world computer has a big advantage over even the most advanced traditional computer: The world computer is much more fault tolerant, as it can survive a large number of crashes of individual components. Beyond that, no authority can corrupt the computer for other users. A world computer must survive even if some of its components are controlled by an evil botnet. The currently common name for such a world computer is *blockchain*.

In this paper we present Alpenglow, a new blockchain protocol. Alpenglow uses the Rotor protocol, which is an optimized and simplified variant of Solana’s data dissemination protocol Turbine [Fou19]. Turbine brought erasure coded information dispersal [CT05] to permissionless blockchains. Rotor uses the total amount of available bandwidth provided by the nodes. Because of this, Rotor achieves an asymptotically optimal throughput. In contrast, consensus protocols that do not address the leader bandwidth bottleneck suffer from low throughput.

The Votor consensus logic at the core of Alpenglow inherits the simplicity from the Simplex protocol line of work [CP23, Sho24] and translates it to a proof-of-stake context, resulting in natural support for rotating leaders without complicated view changes. In the common case, we achieve finality in a single round of voting, while a conservative two-round procedure is run concurrently as backup [SSV25, Von+24].

**Intuition**

**1.1 Alpenglow Overview**

First, let us provide a high-level description of Alpenglow. We are going to describe all the individual parts in detail in Section 2.

Alpenglow runs on top of $n$ computers, which we call nodes, where $n$ can be in the thousands. This set of nodes is known and fixed over a period of time called an epoch. Any node can communicate with any other node in the set by sending a direct message.

Alpenglow is a proof-of-stake blockchain, where each node has a known stake of cryptocurrency. The stake of a node signals how much the node contributes to the blockchain. If node $v_2$ has twice the stake of node $v_1$, node $v_2$ will also earn twice the fees, and provide twice the outgoing network bandwidth.

Time is partitioned into slots. Each time slot has a slot number and a designated leader from the set of nodes. Each leader will be in charge for a fixed amount of consecutive slots, known as the leader window. A threshold verifiable random function determines the leader schedule.

While a node is the leader, it will receive all the new transactions, either directly from the users or relayed by other nodes. The leader will construct a block with these transactions. A block consists of slices for pipelining. The slices themselves consist of shreds for fault tolerance and balanced dispersal

&lt;page_number&gt;2&lt;/page_number&gt;

---


## Page 3

(Section 2.1). The leader incorporates the Rotor algorithm (Section 2.2), which is based on erasure coding, to disseminate the shreds. In essence, we want the nodes to utilize their total outgoing network bandwidth in a stake-fair way, and avoid the common pitfall of having a leader bottleneck. The leader will continuously send its shreds to relay nodes, which will in turn forward the shreds to all other nodes.

As soon as a block is complete, the (next) leader will start building and disseminating the next block. Meanwhile, concurrently, every node eventually receives that newly constructed block. The shreds and slices of the incoming blocks are stored in the Blokstor (Section 2.3).

Nodes will then vote on whether they support the block. We introduce different types of votes (and certificates of aggregated votes) in Section 2.4. These votes and certificates are stored in a local data structure called Pool (Section 2.5).

With all the data structures in place, we discuss the voting algorithm Votor in Section 2.6. If the block is constructed correctly and arrives in time, a node will vote for the block. If a block arrives too late, a node will instead vote to skip the block (since either the leader cannot be trusted, or the network is unstable). If a super-majority of the total stake votes for a block, the block can be finalized immediately. However, if something goes wrong, an additional round of voting will decide whether or not to skip the block.

In Section 2.7 we discuss the logic of creating blocks as a leader, and how to decide on where to append the newly created block.

Finally, in Section 2.8 we discuss Repair – how a node can get missing shreds, slices or blocks from other peers. Repair is needed to help nodes to retrieve the content of an earlier block that they might have missed, which is now an ancestor of a finalized block. This completes the main parts of our discussion of the consensus algorithm.

We proceed to prove the correctness of Alpenglow. First, we prove safety (we do not make fatal mistakes even if the network is unreliable, see Section 2.9), then liveness (we do make progress if the network is reliable, see Section 2.10). Finally, we also consider a scenario with a high number of crash failures in Section 2.11.

While not directly essential for Alpenglow’s correctness, Section 3 examines various concepts that are important for Alpenglow’s understanding. First we describe our novel Rotor relay sampling algorithm in Section 3.1. Next, we explore how transactions are executed in Section 3.2.

Then we move on to advanced failure handling. In Section 3.3 we consider how a node re-connects to Alpenglow after it lost contact, and how the system can “re-sync” when experiencing severe network outages. Then we add dynamic timeouts to resolve a crisis (Section 3.4).

In the last part, we present potential choices for protocol parameters (Section 3.5). Based on these we show some measurement results; to better understand possible efficiency gains, we simulate Alpenglow with Solana’s current

&lt;page_number&gt;3&lt;/page_number&gt;

---


## Page 4

node and stake distribution, both for bandwidth (Section 3.6) and latency (Section 3.7).

In the remainder of *this* section, we present some preliminaries which are necessary to understand the paper. We start out with a short discussion on security design goals in Section 1.2 and performance metrics in Section 1.3. In Section 1.4 we discuss how Alpenglow relates to other work on consensus. Finally we present the model assumptions (Section 1.5) and the cryptographic tools we use (Section 1.6).

## 1.2 Fault Tolerance

Safety and security are the most important objectives of any consensus protocol. Typically, this involves achieving resilience against adversaries that control up to 33% of the stake [PSL80]. This 33% (also known as “$3f+1$”) bound is *everywhere* in today’s world of fault-tolerant distributed systems.

When discovering the fundamental result in 1980, Pease et al. considered systems where the number of nodes $n$ was small. However, today’s blockchain systems consist of *thousands* of nodes! While the 33% bound of [PSL80] also holds for large $n$, attacking one or two nodes is not the same as attacking thousands. In a large scale proof-of-stake blockchain system, running a thousand malicious (“byzantine”) nodes would be a costly endeavor, as it would likely require billions of USD as staking capital. Even worse, misbehavior is often punishable, hence an attacker would lose all this staked capital.

So, in a *real* large scale distributed blockchain system, we will probably see *significantly less* than 33% byzantines. Instead, realistic bad behavior often comes from machine misconfigurations, software bugs, and network or power outages. In other words, large scale faults are likely accidents rather than coordinated attacks.

This *attack model paradigm shift* opens an opportunity to reconsider the classic $3f+1$ bound. Alpenglow is based on the $5f+1$ bound that has been introduced in [DGV04] and [MA06]. While being *less* tolerant to orthodox byzantine attacks, the $5f+1$ bound offers other advantages. Two rounds of voting are required for finalization if the adversary is strong. However, if the adversary possesses less stake, or does not misbehave all the time, it is possible for a correct $5f+1$ protocol to finalize a block in just *a single round* of voting.

In Sections 2.9 and 2.10 we rely on Assumption 1 to show that our protocol is correct.

**Assumption 1** (fault tolerance). *Byzantine nodes control less than 20% of the stake. The remaining nodes controlling more than 80% of stake are correct.*

As we explain later, Alpenglow is partially-synchronous, and Assumption 1 is enough to ensure that even an adversary completely controlling the network

&lt;page_number&gt;4&lt;/page_number&gt;

---


## Page 5

(inspecting, delaying, and scheduling communication between correct nodes at will) cannot violate safety. A network outage or partition would simply cause the protocol to pause and continue as soon as communication is restored, without any incorrect outcome.

However, if the network is not being attacked, or the adversary does not leverage some network advantage, Alpenglow can tolerate an even higher share of nodes that simply crash. In Section 2.11 we intuitively explain the difference between Assumption 1 and Assumption 2, and we sketch Alpenglow’s correctness under Assumption 2.

**Assumption 2 (extra crash tolerance).** Byzantine nodes control less than 20% of the stake. Other nodes with up to 20% stake might crash. The remaining nodes controlling more than 60% of the stake are correct.

### 1.3 Performance Metrics

Alpenglow achieves the fastest possible consensus. In particular, after a block is distributed, our protocol finalizes the block in min(δ80%, 2δ60%) time. We will explain this formula in more detail in Section 1.5; in a nutshell, δθ is a network delay between a stake-weighted fraction θ of nodes. To achieve this finalization time, we run an 80% and a 60% majority consensus mechanism concurrently. A low-latency 60% majority cluster is likely to finish faster on the 2δ path, whereas more remote nodes may finish faster on the single δ path, hence min(δ80%, 2δ60%). Having low latency is an important factor deciding the blockchain’s usability. Improving latency means establishing transaction finality faster, and providing users with results with minimal delay.

Another common pain point of a blockchain is the system’s throughput, measured in transaction bytes per second or transactions per second. In terms of throughput, our protocol is using the total available bandwidth asymptotically optimally.

After achieving the best possible results across these main performance metrics, it is also important to minimize protocol overhead, including computational requirements and other resource demands.

Moreover, in Alpenglow, we strive for simplicity whenever possible. While simplicity is difficult to quantify, it remains a highly desirable property, because simplicity makes it easier to reason about correctness and implementation. A simple protocol can also be upgraded and optimized more conveniently.

&lt;page_number&gt;5&lt;/page_number&gt;

---


## Page 6

1.4 Related Work

Different consensus protocols contribute different techniques to address different performance metrics. Some techniques can be translated from one protocol to another without compromise, while other techniques cannot. In the following we describe each protocol as it was originally published, and not what techniques could hypothetically be added to the protocol.

**Increase Bandwidth.** In classic leader-based consensus protocols such as PBFT [CL99], Tendermint [BKM18] or HotStuff [Yin+19], at a given time one leader node is responsible for disseminating the proposed payload to all replicas. This bandwidth bottleneck can constitute a defining limitation on the throughput [Dan+22, Mil+16, SDV19].

DAG protocols [Dan+22, Spi+22] are a prominent line of work focused on addressing this concern. In these protocols data dissemination is performed by all nodes. Unfortunately, protocols following the DAG approach exhibit a latency penalty [Aru+25]. Some DAG protocols [Kei+22] reduce the latency penalty by foregoing “certifying” the disseminated data. For example, in Mysticeti [Bab+25] the leader block can be confirmed in two rounds of voting, i.e., after disseminating the block and observing two block layers referencing this block (corresponding to 3 network delays, or $3\delta$). However, most of the data (all non-leader blocks) is ordered by the protocol when a leader block “certifying” the data is finalized. In other words, most of the throughput is confirmed with a latency of $5\delta$. Some researchers raise concerns that this technique impacts the robustness of the protocol [Aru+24].

Another prominent technique used to alleviate the leader bottleneck for high throughput involves erasure coding [CT05, Sho24, Yan+22]. Solana [Fou19, Yak18] pioneered this approach in blockchains. In this technique, the leader erasure-codes the payload into smaller fragments. The fragments are sent to different nodes, which in turn participate in disseminating the fragments, making the bandwidth use balanced. Alpenglow follows this line of work.

A recent study [LNS25] proposes a framework to compare the impact of above-mentioned techniques on throughput and latency in a principled way. The study indicates that erasure coding of the payload (represented by DispersedSimplex [Sho24]) achieves better latency than DAG protocols.

**Reduce Latency.** A long line of work proposes consensus protocols that can terminate after one round of voting, typically called fast or one-step consensus. This approach has received a lot of attention, e.g., [DGV04, GV07, Kot+07, Kur02, Lam03, MA06, SR08]. Protocols DGV [DGV04] and FaB Paxos [MA06] introduce a parametrized model with $3f + 2p + 1$ replicas, where $p \geq 0$. The parameter $p$ describes the number of replicas that are not needed for the fast path. These protocols can terminate optimally fast in theory ($2\delta$, or 2 network delays) under optimistic conditions. Liveness and safety issues of

---


## Page 7

landmark papers were later pointed out [Abr+17], showcasing the complexity of the domain and thus posing the research question of fast consensus again. SBFT [Gue+19] addressed the correctness issues. SBFT can terminate after one round of voting, but is optimized for linear message complexity, therefore incurring higher latency.

As pointed out by [DGV04], and later in [KTZ21] and [Abr+21], the lower bound of $3f + 2p + 1$ actually only applies to a restricted type of protocol. These works prove the lower bound and show single-shot consensus protocols that use only $3f + 2p^* - 1$ replicas, with $p^* \geq 1$.

Interestingly, in practice, one-step protocols might *increase* the finalization latency, as one-round finalization requires voting between $n-p$ replicas, which could be slower than two rounds of voting between $n-f-p$ replicas that are more concentrated in a geographic area. Banyan [Von+24] renewed interest in fast BFT protocols, as it performs a one-round and a two-round mechanism in parallel, guaranteeing the best possible latency.

**Concurrent Work.** Kudzu [SSV25] is Alpenglow’s “academic sibling” with a simpler theoretical model. Like Alpenglow, Kudzu features high throughput via the previously mentioned technique of erasure coding, and one- and two-round parallel finalization paths. The differences between Alpenglow and Kudzu include:

*   Kudzu is specified in a permissioned model, while Alpenglow is a proof-of-stake protocol. In many protocols merely the voting weight of nodes would be impacted by this difference. However, disseminating erasure-coded data cannot be easily translated between these models.
*   Alpenglow features leader windows where the leader streams the data without interruption, improving throughput. Concurrent processing of slots allows block times to be shorter than the assumed latency bound ($\Delta$).
*   Alpenglow features fast leader handoff. When the leader is rotated, the next leader can start producing a block as soon as it has received the previous block.
*   With Assumption[3], Alpenglow features higher resilience to crash faults.
*   In Kudzu, due to the different model, nodes can vote as soon as they receive the first fragment of a block proposal, while in Alpenglow nodes vote after reconstructing a full proposal. In theory, the former is faster, while in practice, the difference is a fraction of one network delay.
*   The data expansion ratio associated with erasure coding can be freely set in Alpenglow. We suggest a ratio of 2, while in Kudzu the ratio needs to be higher.

&lt;page_number&gt;7&lt;/page_number&gt;

---


## Page 8

Follow-up Work. Hydrangea [SKN25] is a protocol proposed after Alpenglow that parametrizes resilience to byzantine and crash faults in a way related to Alpenglow. The protocol requires $n = 3f + 2c + k + 1$, and tolerates $f$ byzantine faults and $c$ crash faults in partial synchrony. The number of nodes not needed for finalization in one round of voting is then $p = \lfloor\frac{c+k}{2}\rfloor$. For example, to terminate in one round of voting among 80% of nodes, Hydrangea would set $p = c = k = 20\%$ and $f = 13\%$, for a total of 33% of tolerated faulty nodes. In contrast, Alpenglow can tolerate $f < 20\%$ and a total of 40% of faulty nodes, but needs Assumption 3 for fault rates higher than 20%.

Hydrangea suffers from a bandwidth bottleneck at the leader and, in our view, remains underspecified for practical implementation. However, the parametrization is an interesting contribution than could also be applied to Alpenglow.

Intuition

1.5 Model and Preliminaries

Names. We introduce various objects of the form $\text{Name}(x,y)$. This indicates some deterministic encoding of the object type “Name” and its parameters $x$ and $y$.

Epoch. To allow for changing participants and other dynamics, the protocol rejuvenates itself in regular intervals. The time between two such changes is called an epoch. Epochs are numbered as $e = 1, 2, 3$, etc. The participants register/unregister two epochs earlier, i.e., the participants (and their stake) of epoch $e+1$ are decided at the end of epoch $e-1$, i.e., a long enough time before epoch $e+1$ starts. This makes sure that everybody is in agreement on the current nodes and their stake at the beginning of epoch $e+1$.

Node. We operate on $n$ individual computers, which we call nodes $v_1, v_2, \ldots, v_n$. The main jobs of these nodes are to send/relay messages and to validate blocks. Because of this, nodes are sometimes also called validators in the literature. While the set of nodes changes with every new epoch, as mentioned in the previous paragraph, the nodes are static and fixed during an epoch. The set of nodes is publicly known, i.e., each node knows how to contact (IP address and port number) every node $v_i$. Each node has a public key, and all nodes know all public keys. The information of each node (public key, stake, IP address, port number, etc.) is announced and updated by including the information in a transaction on the blockchain. This guarantees that everybody has the same information. Currently, Solana has $n \approx 1,500$ nodes, but our protocol can in principle scale to higher numbers. However, for practical reasons it may be beneficial to bound $n \leq n_{\max}$.

Message. Nodes communicate by exchanging authenticated messages. Our protocol never uses large messages. Specifically, all messages are less than

&lt;page_number&gt;8&lt;/page_number&gt;

---


## Page 9

1,500 bytes [Pos84]. Because of this, we use UDP with authentication, so either QUIC-UDP or UDP with a pair-wise message authentication code (MAC). The symmetric keys used for this purpose are derived with a key exchange protocol using the public keys.

**Broadcast.** Sometimes, a node needs to broadcast the same message to all ($n - 1$ other) nodes. The sender node simply loops over all other nodes and sends the message to one node after the other. Despite this loop, the total delay is dominated by the network delay. With a bandwidth of 1Gb/s, transmitting $n = 1,500$ shreds takes 18 ms (well below the average network delay of about 80 ms). To get to 80% of the total stake we need to reach $n \approx 150$ nodes, which takes only about 2 ms. Voting messages are shorter, and hence need even less time. Moreover, we can use a multicast primitive provided by an alternative network provider, e.g., DoubleZero [FMW24] or SCION [Zha+11].

**Stake.** Each node $v_i$ has a known positive stake of cryptocurrency. We use $\rho_i > 0$ to denote node $v_i$'s fraction of the entire stake, i.e., $\sum_{i=1}^{n} \rho_i = 1$. Each (fractional) stake $\rho_i$ stays fixed during the epoch. The stake of a node signals how much the node contributes to the blockchain. If node $v_2$ has twice the stake of node $v_1$, node $v_2$ will also earn roughly twice the fees. Moreover, node $v_2$ also has twice the outgoing network bandwidth. However, all nodes need enough in-bandwidth to receive the blocks, and some minimum out-bandwidth to distribute blocks when they are a leader.

**Time.** We assume that each node is equipped with a local system clock that is reasonably accurate, e.g., 50 ppm drift. We do not consider clock drift in our analysis, but it can be easily addressed by incorporating the assumed drift into timeout periods. Clocks do not need to be synchronized at all, as every node only uses its local system clock.

**Slot.** Each epoch is partitioned into slots. A slot is a natural number associated with a block, and does not require timing agreements between nodes. The time period of a slot could start (and end) at a different local time for different nodes. Nevertheless, in normal network conditions the slots will become somewhat synchronized. During an epoch, the protocol will iterate through slots $s = 1, 2, \ldots, L$. Solana's current parameter of $L = 432,000$ is possible, but much shorter epochs, e.g., $L \approx 18,000$, could be advantageous, for instance to change stake more quickly. Each slot $s$ is assigned a leader node, given by the deterministic function $\text{leader}(s)$ (which is known before the epoch starts).

**Leader.** Each slot has a designated leader from the set of nodes. Each leader will be in charge for a fixed amount of consecutive slots, known as the

---


## Page 10

leader window. A threshold verifiable random function [Dod02] [MRV99] is evaluated before each epoch to determine a publicly known leader schedule that defines which node is the leader in what slot.

**Timeout.** Our protocol uses timeouts. Nodes set timeouts to make sure that the protocol does not get stuck waiting forever for some messages. For simplicity, timeouts are based on a global protocol parameter $\Delta$, which is the maximum possible network delay between any two correct nodes when the network is in synchronous operation. However, timeout durations can be changed dynamically based on conditions, such that the protocol is correct irrespectively of the $\Delta$ exhibited by the network. For simplicity, we conservatively assume $\Delta$ to be a constant, e.g., $\Delta \approx 400$ ms. Importantly, timeouts do *not* assume synchronized clocks. Instead, only short periods of time are measured locally by the nodes. Therefore, the absolute wall-clock time and clock skew have no significance to the protocol. Even extreme clock drift can be simply incorporated into the timeouts - e.g. to tolerate clock drift of $5\%$, the timeouts can simply be extended by $5\%$. As explained later, Alpenglow is partially-synchronous, so no timing- or clock-related errors can derail the protocol.

**Adversary.** Some nodes can be byzantine in the sense that they can misbehave in arbitrary ways. Byzantine nodes can for instance forget to send a message. They can also collude to attack the blockchain in a coordinated way. Some misbehavior (e.g. signing inconsistent information) may be a provable offense, while some other misbehavior cannot be punished, e.g., sending a message late could be due to an extraordinary network delay. As discussed in Assumption [1], we assume that all the byzantine nodes together own strictly less than $20\%$ of the total stake. Up to an additional $20\%$ of the stake may be crashed under the conditions described in Section [2.11]. The remaining nodes are *correct* and follow the protocol. For simplicity, in our analysis (Sections [2.9] to [2.11]) we consider a static adversary over a period of one epoch.

**Asynchrony.** We consider the partially synchronous network setting of Global Stabilization Time (GST) [Con+24] [DLS88]. Messages sent between correct nodes will eventually arrive, but they may take arbitrarily long to arrive. We always guarantee *safety*, which means that irrespectively of arbitrary network delays (known as the asynchronous network model), correct nodes output the same blocks in the same order.

**Synchrony.** However, we only guarantee *liveness* when the network is synchronous, and all messages are delivered quickly. In other words, correct nodes continue to make progress and output transactions in periods when messages between correct nodes are delivered “in time.” In the model of GST, synchrony simply corresponds to a global worst-case bound $\Delta$ on mes-

&lt;page_number&gt;10&lt;/page_number&gt;

---


## Page 11

sage delivery. The GST model captures periods of synchrony and asynchrony by stating that before the unknown and arbitrary time GST (global stabilization time) messages can be arbitrarily delayed, but after time GST all previous and future messages $m$ sent at time $t_m$ will arrive at the recipient at latest at time $\max(\text{GST}, t_m) + \Delta$.

**Network Delay.** During synchrony, the protocol will rarely wait for a timeout. We model the actual message delay between correct nodes as $\delta$, with $\delta \ll \Delta$. The real message delay $\delta$ is variable and unknown. Naturally, $\delta$ is not part of the protocol, and will only be used for the latency analysis. In other words, the performance of optimistically responsive protocols such as Alpenglow in the common case depends only on $\delta$ and not the timeout bound $\Delta$. As discussed in Section 1.3, we use $\delta_\theta$ to indicate how long it takes a fraction $\theta$ of nodes to send each other messages. More precisely, let $S$ be a set of nodes with cumulative stake at least $\theta$. In one network delay $\delta_\theta$, each node in $S$ sends a message to every node in $S$. If $\theta = 60\%$ of the nodes are geographically close, then it is possible that $2\delta_{60\%}$ is less time than $\delta_{80\%}$, which needs only one network delay, but the involvement of $80\%$ of the nodes.

**Correctness.** The purpose of a blockchain is to produce a sequence of *finalized* blocks containing transactions, so that all nodes output transactions in the same order. Every block is associated with a parent (starting at some notional genesis block). Finalized blocks form a single chain of parent-child links. When a block is finalized, all ancestors of the block are finalized as well.

Our protocol orders blocks by associating them with natural numbered slots, where a child block has to have a higher slot number than its parent. For every slot, either some block produced by the leader might be finalized, or the protocol can yield a *skip*. The blocks in finalized slots are transmitted in-order to the execution layer of the protocol stack. Definition 14 describes the conditions for block finalization. The guarantees of our protocol can be stated as follows:

- **Safety.** Suppose a correct node finalizes a block $b$ in slot $s$. Then, if any correct node finalizes any block $b'$ in any slot $s' \geq s$, $b'$ is a descendant of $b$. (See also Theorem 1)
- **Liveness.** In any long enough period of network synchrony, correct nodes finalize new blocks produced by correct nodes. (See also Theorem 2)

&lt;page_number&gt;11&lt;/page_number&gt;

---


## Page 12

1.6 Cryptographic Techniques

**Hash Function.** We have a collision-resistant hash function, e.g., SHA256.

**Digital Signature.** We have secure (non-forgivable) digital signatures. As stated earlier, each node knows the public key of every other node.

**Aggregate Signature.** Signatures from different signers may be combined non-interactively to form an aggregate signature. Technically, we only require non-interactive multi-signatures, which only enable signatures over the same message to be aggregated. This can be implemented in various ways, e.g. based on BLS signatures [Bon+03]. Aggregate signatures allow certificates to fit into a short message as long as $n \leq n_{\text{max}}$.

**Erasure Code.** For integer parameters $\Gamma \geq \gamma \geq 1$, a $(\Gamma, \gamma)$ erasure code encodes a bit string $M$ of size $m$ as a vector of $\Gamma$ data pieces $d_1, \ldots, d_\Gamma$ of size $m/\gamma + O(\log \Gamma)$ each. The $O(\log \Gamma)$ overhead is needed to index each data piece. Erasure coding makes sure that any $\gamma$ data pieces may be used to efficiently reconstruct $M$. The reconstruction algorithm also takes as input the length $m$ of $M$, which we assume to be constant (achieved by padding smaller payloads).

In our protocol, the payload of a slice will be encoded using a $(\Gamma, \gamma)$ Reed-Solomon erasure code [RS60], which encodes a payload $M$ as a vector $d_1, \ldots, d_\Gamma$, where any $\gamma$ $d_i$’s can be used to reconstruct $M$. The data expansion rate is $\kappa = \Gamma / \gamma$.

**Merkle Tree.** A Merkle tree [Mer79] allows one party to commit to a vector of data $(d_1, \ldots, d_\Gamma)$ using a collision-resistant hash function by building a (full) binary tree where the leaves are the hashes of $d_1, \ldots, d_\Gamma$. Each leaf hash is concatenated with a label that marks the hash as a leaf, and each internal node of the tree is the hash of its two children. The root $r$ of the tree is the commitment.

The validation path $\pi_i$ for position $i \in \{1, \ldots, \Gamma\}$ consists of the siblings of all nodes along the path in the tree from the hash of $d_i$ to the root $r$. The root $r$ together with the validation path $\pi_i$ can be used to prove that $d_i$ is at position $i$ of the Merkle tree with root $r$.

The validation path is checked by recomputing the hashes along the corresponding path in the tree, and by verifying that the recomputed root is equal to the given commitment $r$. If this verification is successful, we call $d_i$ the data at position $i$ with path $\pi_i$ for Merkle root $r$. The collision resistance of the hash function ensures that no data $d'_i \neq d_i$ can have a valid proof for position $i$ in the Merkle tree.

&lt;page_number&gt;12&lt;/page_number&gt;

---


## Page 13

Encoding and Decoding. [CT05] The function $encode$ takes as input a payload $M$ of size $m$. It erasure codes $M$ as $(d_1,\ldots,d_\Gamma)$ and builds a Merkle tree with root $r$ where the leaves are the hashes of $d_1,\ldots,d_\Gamma$. The root of the tree $r$ is uniquely associated with $M$. It returns $(r,\{(d_i,\pi_i)\}_{i\in\{1,\ldots,\Gamma\}})$, where each $d_i$ is the data at position $i$ with path $\pi_i$ for Merkle root $r$.

The function $decode$ takes as input $(r,\{(d_i,\pi_i)\}_{i\in\mathcal{I}})$, where $\mathcal{I}$ is a subset of $\{1,\ldots,\Gamma\}$ of size $\gamma$, and each $d_i$ (of correct length) is the data at position $i$ with path $\pi_i$ for Merkle root $r$. Moreover, the decoding routine makes sure that the root $r$ is correctly computed based on all $\Gamma$ data pieces that correctly encode some message $M'$, or it fails. If it fails, it guarantees that no set of $\gamma$ data pieces associated with $r$ can be decoded, and that $r$ was (provably) maliciously constructed.

To ensure this pass/fail property, the decoding algorithm needs to check for each reconstructed data piece that it corresponds to the same root $r$. More precisely, $decode$ reconstructs a message $M'$ from the data $\{d_i\}_{i\in\mathcal{I}}$. Then, it encodes $M'$ as a vector $(d'_1,\ldots,d'_\Gamma)$, and builds a Merkle tree with root $r'$ with the hashes of $(d'_1,\ldots,d'_\Gamma)$ as leaves. If $r'=r$, $decode$ returns $M'$, otherwise it fails.

&lt;page_number&gt;13&lt;/page_number&gt;

**2 The Alpenglow Protocol**

In this section we describe the Alpenglow protocol in detail.

&lt;img&gt;
A flowchart showing the components of Alpenglow and their interactions.
- Blokstor
- Pool
- Votor
- block creation
- Rotor
- Repair
- broadcast
Arrows show information flow:
- Blue arrows represent block data in the form of shreds.
- Green arrows represent internal events.
- Red arrows represent votes/certificates.
&lt;/img&gt;

Figure 1: Overview of components of Alpenglow and their interactions. Arrows show information flow: block data in the form of shreds (blue), internal events (green), and votes/certificates (red).

---


## Page 14

2.1 Shred, Slice, Block

&lt;img&gt;A diagram showing the hierarchy of block data, visualizing the double-Merkle construction of the block hash. Each slice has a Merkle root hash \( r_i \), which are in turn the leaf nodes for the second Merkle tree, where the root corresponds to the block hash.&lt;/img&gt;

Figure 2: Hierarchy of block data, visualizing the double-Merkle construction of the block hash. Each slice has a Merkle root hash \( r_i \), which are in turn the leaf nodes for the second Merkle tree, where the root corresponds to the block hash.

**Definition 1 (shred).** A shred fits neatly in a UDP datagram. It has the form:
\[
(s, t, i, z_t, r_t, (d_i, \pi_i), \sigma_t),
\]
where

- \( s, t, i \in \mathbb{N} \) are slot number, slice index, shred index, respectively,
- \( z_t \in \{0, 1\} \) is a flag (see Definition 2 below),
- \( d_i \) is the data at position \( i \) with path \( \pi_i \) for Merkle root \( r_t \) (Section 1.6),
- \( \sigma_t \) is the signature of the object \( \text{Slice}(s, t, z_t, r_t) \) from the node leader\( (s) \).

**Definition 2 (slice).** A slice is the input of Rotor, see Section 2.2. Given any \( \gamma \) of the \( \Gamma \) shreds, we can decode (Section 1.6) the slice. A slice has the form:
\[
(s, t, z_t, r_t, M_t, \sigma_t),
\]
where

- \( s, t \in \mathbb{N} \) are the slot number and slice index respectively,
- \( z_t \in \{0, 1\} \) is a flag indicating the last slice index,
- \( M_t \) is the decoding of the shred data \( \{(d_i)\}_{i \in I} \) for Merkle root \( r_t \),
- \( \sigma_t \) is the signature of the object \( \text{Slice}(s, t, z_t, r_t) \) from the node leader\( (s) \).

&lt;page_number&gt;14&lt;/page_number&gt;

---


## Page 15

**Definition 3 (block).** *A block b is the sequence of all slices of a slot, for the purpose of voting and reaching consensus. A block is of the form:*

$$b = \{(s,t,z_t,r_t,M_t,\sigma_t)\}_{t\in\{1,...,k\}},$$

*where $z_k=1$, $z_t=0$ for $t<k$. The data of the block is the concatenation of all the slice data, i.e., $\mathcal{M}=(M_1,M_2,...,M_k)$. We define $\text{slot}(b)=s$. The block data $\mathcal{M}$ contains information about the slot $\text{slot}(\text{parent}(b))$ and hash $\text{hash}(\text{parent}(b))$ of the parent block of b. There are various limits on a block, for instance, each block can only have a bounded amount of bytes and a bounded amount of time for execution.*

**Definition 4 (block hash).** *We define $\text{hash}(b)$ of block $b=\{(s,t,z_t,r_t,M_t,$ $\sigma_t)\}_{t\in\{1,...,k\}}$ as the root of a Merkle tree T where:*

*   *T is a complete, full binary tree with the smallest possible number of leaves m (with m being a power of 2) such that $m\geq k$,*
*   *the first k leaves of T are $r_1,...,r_k$ (each hash is concatenated with a label that marks the hash as a leaf),*
*   *the remaining leaves of T are $\bot$.*

**Definition 5 (ancestor and descendant).** *An ancestor of a block b is any block that can be reached from b by the parent links, i.e., b, b’s parent, b’s parent’s parent, and so on. If $b'$ is an ancestor of b, b is a descendant of $b'$. Note that b is its own ancestor and descendant.*

**2.2 Rotor**

Rotor is the block dissemination protocol of Alpenglow. The leader (sender) wants to broadcast some data (a block) to all other nodes. This procedure should have low latency, utilize the bandwidth of the network in a balanced way, and be resilient to transmission failures. The block should be produced and transmitted in a streaming manner, that is, the leader does not need to wait until the entire block is constructed.

&lt;img&gt;Protocol Intuition&lt;/img&gt;

Figure 3: Basic structure of the Rotor data dissemination protocol.

---


## Page 16

A leader uses multiple rounds of the Rotor protocol to broadcast a block. Each round considers the independent transmission of one slice of the block. The leader transmits each slice as soon as it is ready. This achieves pipelining of block production and transmission.

For each slice, the leader generates $\Gamma$ Reed-Solomon coding shreds and constructs a Merkle tree over their hashes and signs the root. Each coding shred includes the Merkle path along with the root signature. Each shred contains as much data and corresponding metadata as can fit into a single UDP datagram.

Using Reed-Solomon erasure coding [RS60] ensures that, at the cost of sending more data, receiving any $\gamma$ shreds is enough to reconstruct the slice (Section 1.6). After that, as an additional validity check, a receiver generates the (up to $\Gamma - \gamma$) missing shreds.

For any given slice, the leader sends each shred directly to a corresponding node selected as shred relay. We sample relays for every slice. We use a novel sampling method which improves resilience. We describe our new method in detail in Section 3.1.

Each relay then broadcasts its shred to all nodes that still need it, i.e., all nodes except for the leader and itself, in decreasing stake order. As a minor optimization, all shred relays send their shred to the next leader first. This slightly improves latency for the next leader, who most urgently needs the block.

A shred’s authenticity needs to be checked to reconstruct the slice from $\gamma$ of the shreds. To enable receivers to cheaply check authenticity of each shred individually, the leader builds a Merkle tree [Mer79] over all shreds of a slice, as described in Section 1.6. Each shred then includes its path in the tree and the leader’s signature of the root of the tree.

When receiving the first shred of a slice, a node checks the validity of the Merkle path and the leader’s signature, and then stores the verified root. For any later shred, the receiving node only checks the validity of the Merkle path against the stored root.

&lt;page_number&gt;16&lt;/page_number&gt;

---


## Page 17

&lt;img&gt;
Average Rotor Latency ($\gamma = 32$)
Latency [ms]
0 20 40 60 80 100 120
Total shreds ($\Gamma$)
64 80 96 320
Median Rotor Latency ($\gamma = 32$)
Latency [ms]
0 20 40 60 80 100 120
Total shreds ($\Gamma$)
64 80 96 320
&lt;/img&gt;

Figure 4: Rotor latency for different data expansion ratios (and thus total numbers of shreds), all with $\gamma = 32$ data shreds using our sampling from Section 3.1. The red lines indicate the average/median network latency. With a high data expansion rate ($\kappa = 10$, hence $\Gamma = 320$) we pretty much achieve the single $\delta$ latency described in Lemma 8. All our simulation results use the current (epoch 780) Solana stake distribution. Network latency is inferred from public data. Computation and transmission delays are omitted.

**Definition 6.** *Given a slot $s$, we say that Rotor is successful if the leader of $s$ is correct, and at least $\gamma$ of the corresponding relays are correct.*

**Resilience.** If the conditions of Definition 6 are met, all correct nodes will receive the block distributed by the leader, as enough relays are correct. On the other hand, a faulty leader can simply not send any data, and Rotor will immediately fail. In the following we assume that the leader is correct. The following lemma shows that Rotor is likely to succeed if we over-provision the coding shreds by at least 67%.

**Lemma 7** (rotor resilience). *Assume that the leader is correct, and that erasure coding over-provisioning is at least $\kappa = \Gamma / \gamma > 5/3$. If $\gamma \to \infty$, with probability 1, a slice is received correctly.*

*Proof Sketch.* We choose the relay nodes randomly, according to stake. The failure probability of each relay is less than 40% according to Section 1.2. The expected value of correct relays is then at least $60\% \cdot \Gamma > 60\% \cdot 5\gamma / 3 = \gamma$. So strictly more than $\gamma$ shreds will arrive in expectation. With $\gamma \to \infty$, applying an appropriate Chernoff bound, with probability 1 we will have at least $\gamma$ shreds that correctly arrive at all nodes. $\square$

&lt;page_number&gt;17&lt;/page_number&gt;

---


## Page 18

**Latency.** The latency of Rotor is between $\delta$ and $2\delta$, depending on whether we make optimistic or pessimistic assumptions on various parameters.

**Lemma 8. (rotor latency)** *If Rotor succeeds, network latency of Rotor is at most $2\delta$. A high over-provisioning factor $\kappa$ can reduce latency. In the extreme case with $n \to \infty$ and $\kappa \to \infty$, we can bring network latency down to $\delta$. (See also Figure [4] for simulation results with Solana’s stake distribution.)*

*Proof Sketch.* Assuming a correct leader, all relays receive their shred in time $\delta$ directly from the leader. The correct relays then send their shred to the nodes in another time $\delta$, so in time $2\delta$ in total.

If we over-provision the relays, chances are that many correct relays are geographically located between leader and the receiving node. In the extreme case with infinitely many relays, and some natural stake distribution assumptions, there will be at least $\gamma$ correct relays between any pair of leader and receiving node. If the relays are on the direct path between leader and receiver, they do not add any overhead, and both legs of the trip just sum up to $\delta$.

**Bandwidth.** Both the leader and the shred relays are sampled by stake. As a result, in expectation each node has to transmit data proportional to their stake. This aligns well with the fact that staking rewards are also proportional to the nodes’ stake. If the available out-bandwidth is proportional to stake, it can be utilized perfectly apart from the overhead.

**Lemma 9** (bandwidth optimality). *Assume a fixed leader sending data at rate $\beta_\ell \leq \bar{\beta}$, where $\bar{\beta}$ is the average outgoing bandwidth across all nodes. Suppose any distribution of out-bandwidth and proportional node stake. Then, at every correct node, Rotor delivers block data at rate $\beta_\ell/\kappa$ in expectation. Up to the data expansion rate $\kappa = \Gamma/\gamma$, this is optimal.*

*Proof.* Node $v_i$ is chosen to be a shred relay in expectation $\Gamma\rho_i$ times. Each shred relay receives data from the leader with bandwidth $\beta_\ell/\Gamma$, because the leader splits its bandwidth across all shred relays. Hence, in expectation, node $v_i$ receives data from the leader at rate $\Gamma\rho_i \cdot \beta_\ell/\Gamma = \rho_i\beta_\ell$. Node $v_i$ needs to forward this data to $n-2$ nodes. So, in expectation, node $v_i$ needs to send data at rate $\rho_i\beta_\ell(n-2)$. Node $v_i$ has outgoing bandwidth $\beta_i = n\bar{\beta}\rho_i$, since outgoing bandwidth is proportional to stake (Section [1.5]). Since $\beta_\ell \leq \bar{\beta}$, we have $\rho_i\beta_\ell(n-2) < \beta_i$. Each node thus has enough outgoing bandwidth to support the data they need to send.

Note that we cannot get above rate $\beta_\ell$ because the leader is the only one who knows the data. Likewise we cannot get above rate $\bar{\beta}$, because all nodes need to receive the data, and the nodes can send with no more total rate than $n\bar{\beta}$. So apart from the data expansion factor $\kappa$, we are optimal.

Note that any potential attacks on Rotor may only impact liveness, not

&lt;page_number&gt;18&lt;/page_number&gt;

---


## Page 19

Analysis

safety, since the other parts of Alpenglow ensure safety even under asynchrony and rely on Rotor only for data dissemination.

2.3 Blokstor

Blokstor collects and stores the first block received through Rotor in every slot, as described in Definition 10.

**Definition 10 (Blokstor).** *The Blokstor is a data structure managing the storage of slices disseminated by the protocol of Section 2.2.* When a shred $(s,t,i,z_t,r_t,(d_i,\pi_i),\sigma_t)$ is received by a node, the node checks the following conditions. If the conditions are satisfied, the shred is added to the Blokstor:

- *the Blokstor does not contain a shred for indices $(s,t,i)$ yet,* 
- $(d_i,\pi_i)$ is the data with path for Merkle root $r_t$ at position $i$, 
- $\sigma_t$ is the signature of the object Slice$(s,t,z_t,r_t)$ from the node leader$(s)$.

*Blokstor emits the event Block(slot(b), hash(b), hash(parent(b))) as input for Algorithm 1 when it receives the first complete block b for slot(b).* 

In addition to storing the first block received for a given slot, the Blokstor can perform the repair procedure (Section 2.8) to collect some other block $b$ and store it in the Blokstor. If a block is finalized according to Definition 14, Blokstor has to collect and store only this block in the given slot. Otherwise, before the event SafeToNotar(slot(b), hash(b)) of Definition 16 is emitted, $b$ has to be stored in the Blokstor as well.

Protocol

2.4 Votes and Certificates

Next we describe the voting data structures and algorithms of Alpenglow. In a nutshell, if a leader gets at least 80% of the stake to vote for its block, the block is immediately finalized after one round of voting with a fast-finalization certificate. However, as soon as a node observes 60% of stake voting for a block, it issues its second-round vote. After 60% of stake voted for a block the second time, the block is also finalized. On the other hand, if enough stake considers the block late, a skip certificate can be produced, and the block proposal will be skipped.

**Definition 11 (messages).** *Alpenglow uses voting and certificate messages listed in Tables 5 and 6.*

Intuition

&lt;page_number&gt;19&lt;/page_number&gt;

---


## Page 20

| Vote Type | Object |
|---|---|
| Notarization Vote | NotarVote(slot(b), hash(b)) |
| Notar-Fallback Vote | NotarFallbackVote(slot(b), hash(b)) |
| Skip Vote | SkipVote(s) |
| Skip-Fallback Vote | SkipFallbackVote(s) |
| Finalization Vote | FinalVote(s) |

Table 5: Alpenglow's voting messages with respect to block $b$ and slot $s$. Each object is signed by a signature $\sigma_v$ of the voting node $v$.

| Certificate Type | Aggregated Votes | Condition |
|---|---|---|
| Fast-Finalization Cert. | NotarVote | $\Sigma \geq 80\%$ |
| Notarization Cert. | NotarVote | $\Sigma \geq 60\%$ |
| Notar-Fallback Cert. | NotarVote or NotarFallbackVote | $\Sigma \geq 60\%$ |
| Skip Cert. | SkipVote or SkipFallbackVote | $\Sigma \geq 60\%$ |
| Finalization Cert. | FinalVote | $\Sigma \geq 60\%$ |

Table 6: Alpenglow's certificate messages. $\Sigma$ is the cumulative stake of the aggregated votes $(\sigma_i)_{I \subseteq \{1,\ldots,n\}}$ in the certificate, i.e., $\Sigma = \sum_{i \in I} \rho_i$.

**2.5 Pool**

Every node maintains a data structure called *Pool*. In its Pool, each node memorizes all votes and certificates for every slot.

**Definition 12** (storing votes). *Pool stores received votes for every slot and every node as follows:*

* The first received notarization or skip vote,
* up to 3 received notar-fallback votes,
* the first received skip-fallback vote, and
* the first received finalization vote.

**Definition 13** (certificates). *Pool generates, stores and broadcasts certificates:*

* When enough votes (see Table [6]) are received, the respective certificate is generated.
* When a received or constructed certificate is newly added to Pool, the certificate is broadcast to all other nodes.

&lt;page_number&gt;20&lt;/page_number&gt;

---


## Page 21

- A single (received or constructed) certificate of each type corresponding to the given block/slot is stored in Pool.

Note that the conditions in Table 6 imply that if a correct node generated the Fast-Finalization Certificate, it also generated the Notarization Certificate, which in turn implies it generated the Notar-Fallback Certificate.

**Definition 14 (finalization).** We have two ways to finalize a block:

- If a finalization certificate on slot $s$ is in Pool, the unique notarized block in slot $s$ is finalized (we call this slow-finalized).
- If a fast-finalization certificate on block $b$ is in Pool, the block $b$ is finalized (fast-finalized).

Whenever a block is finalized (slow or fast), all ancestors of the block are finalized first.

**Definition 15 (Pool events).** The following events are emitted as input for Algorithm 1:

- BlockNotarized(slot($b$), hash($b$)): Pool holds a notarization certificate for block $b$.
- ParentReady($s$, hash($b$)): Slot $s$ is the first of its leader window, and Pool holds a notarization or notar-fallback certificate for a previous block $b$, and skip certificates for every slot $s'$ since $b$, i.e., for slot($b$) < $s'$ < $s$.

As we will see later (Lemmas 20 and 35), for every slot $s$, every correct node will cast exactly one notarization or skip vote. After casting this initial vote, the node might emit events according to Definition 16 and cast additional votes.

The event SafeToNotar($s$, $b$) indicates that it is not possible that some block $b' \neq b$ could be fast-finalized (Definition 14) in slot $s$, and so it is safe to issue the notar-fallback vote for $b$.

Similarly, SafeToSkip($s$) indicates that it is not possible that any block in slot $s$ could be fast-finalized (Definition 14), and so it is safe to issue the skip-fallback vote for $s$.

**Definition 16 (fallback events).** Consider block $b$ in slot $s = \text{slot}(b)$. By $\text{notar}(b)$ denote the cumulative stake of nodes whose notarization votes for block $b$ are in Pool, and by $\text{skip}(s)$ denote the cumulative stake of nodes whose skip votes for slot $s$ are in Pool. Recall that by Definition 12 the stake of any node can be counted only once per slot. The following events are emitted as input for Algorithm 1:

- SafeToNotar($s$, hash($b$)): The event is only issued if the node voted in

&lt;page_number&gt;21&lt;/page_number&gt;

---


## Page 22

slot $s$ already, but not to notarize $b$. Moreover:

$$\textit{notar}(b) \geq 40\% \textbf{ or } \Big( \textit{skip}(s) + \textit{notar}(b) \geq 60\% \textbf{ and } \textit{notar}(b) \geq 20\%\Big).$$

If $s$ is the first slot in the leader window, the event is emitted. Otherwise, block $b$ is retrieved in the repair procedure (Section [2.8]) first, in order to identify the parent of the block. Then, the event is emitted when Pool contains the notar-fallback certificate for the parent as well.

- **SafeToSkip($s$):** The event is only issued if the node voted in slot $s$ already, but not to skip $s$. Moreover:

$$\textit{skip}(s) + \sum_{b} \textit{notar}(b) - \max_b \textit{notar}(b) \geq 40\%. $$

### 2.6 Votor

&lt;img&gt;
Leader sends
Relays send
Notar. votes
Final. votes
slow-finalization
fast-finalization
notarization
&lt;/img&gt;

Figure 7: Protocol overview: a full common case life cycle of a block in Alpenglow.

The purpose of voting is to notarize and finalize blocks. Finalized blocks constitute a single chain of parent references and indicate the output of the protocol.

The protocol ensures that for every slot, either a skip certificate is created, or some block $b$ is notarized (or notarized-fallback), such that all ancestors of $b$ are also notarized. Condition thresholds ensure that a malicious leader cannot prevent the creation of certificates needed for liveness. If many correct nodes produced notarization votes for the same block $b$, then all other correct nodes will make notar-fallback votes for $b$. Otherwise, all correct nodes will broadcast skip-fallback votes.

By Definition [14], a node can finalize a block as soon as it observes enough notarization votes produced by other nodes immediately upon receiving a block. However, a lower participation threshold is required to make a nota-

---


## Page 23

rization certificate. Then the node will send the finalization vote. Therefore, blocks are finalized after one round of voting among nodes with 80% of the stake, or two rounds of voting among nodes with 60% of the stake.

Nodes have local clocks and emit timeout events. Whenever a node $v$'s Pool emits the event ParentReady($s,\ldots$), it starts timeout timers corresponding to all blocks of the leader window beginning with slot $s$. The timeouts are parametrized with two delays (pertaining to network synchrony):

- $\Delta_{\text{block}}$: This denotes the protocol-specified block time.
- $\Delta_{\text{timeout}}$: Denotes the rest of the possible delay (other than $\Delta_{\text{block}}$) between setting the timeouts and receiving a correctly disseminated block. As a conservative global constant, $\Delta_{\text{timeout}}$ can be set to $(1\Delta + 2\Delta) > (\text{time needed for the leader to observe the certificates}) + (\text{latency of slice dissemination through Rotor})$.

**Definition 17 (timeout).** *When a node $v$'s Pool emits the first event ParentReady($s,\ldots$), Timeout($i$) events for the leader window beginning with $s$ (for all $i \in \text{WINDOWSLOTS}(s)$) are scheduled at the following times:*

$$\text{Timeout}(i): \text{clock}() + \Delta_{\text{timeout}} + (i - s + 1) \cdot \Delta_{\text{block}}.$$ 

The timeouts are set to correspond to the latest possible time of receiving a block if the leader is correct and the network is synchronous. Timeouts can be optimized, e.g., by fine-grained $\Delta$ estimation or to address specific faults, such as crash faults.

Note that ParentReady($s,\ldots$) is only emitted for the first slot $s$ of a window. Therefore, $(i - s + 1) \geq 1$ and Timeout($i$) is never scheduled to be emitted in the past.

**Definition 18 (Votor state).** *Votor (Algorithms [1] and [2]) accesses state associated with each slot. The state of every slot is initialized to the empty set: $\text{state} \leftarrow [\emptyset, \emptyset, \ldots]$. The following objects can be permanently added to the state of any slot $s$:*

- *ParentReady(hash($b$)): Pool emitted the event ParentReady($s$, hash($b$)).*
- *Voted: The node has cast either a notarization vote or a skip vote in slot $s$.*
- *VotedNotar(hash($b$)): The node has cast a notarization vote on block $b$ in slot $s$.*
- *BlockNotarized(hash($b$)): Pool holds the notarization certificate for block $b$ in slot $s$.*
- *ItsOver: The node has cast the finalization vote in slot $s$, and will not cast any more votes in slot $s$.*

&lt;page_number&gt;23&lt;/page_number&gt;

---


## Page 24

- **BadWindow**: The node has cast at least one of these votes in slot $s$: skip, skip-fallback, notar-fallback.

Additionally, every slot can be associated with a pending block, which is initialized to bottom: $\text{pendingBlocks} \leftarrow [\bot, \bot, \ldots]$. The pendingBlocks are blocks which will be revisited to call TRYNOTAR(), as the tested condition might be met later.

**Algorithm 1** Votor, event loop, single-threaded

```plaintext
1: upon Block(s, hash, hash_parent) do
2:   if TRYNOTAR(Block(s, hash, hash_parent)) then
3:     CHECKPENDINGBLOCKS()
4:   else if Voted ∉ state[s] then
5:     pendingBlocks[s] ← Block(s, hash, hash_parent)

6: upon Timeout(s) do
7:   if Voted ∉ state[s] then
8:     TRYSKIPWINDOW(s)

9: upon BlockNotarized(s, hash(b)) do
10:   state[s] ← state[s] ∪ {BlockNotarized(hash(b))}
11:   TRYFINAL(s, hash(b))

12: upon ParentReady(s, hash(b)) do
13:   state[s] ← state[s] ∪ {ParentReady(hash(b))}
14:   CHECKPENDINGBLOCKS()
15:   SETTIMEOUTS(s) ▷ start timer for all slots in this window

16: upon SafeToNotar(s, hash(b)) do
17:   TRYSKIPWINDOW(s)
18:   if ltsOver ∉ state[s] then
19:     broadcast NotarFallbackVote(s, hash(b)) ▷ notar-fallback vote
20:     state[s] ← state[s] ∪ {BadWindow}

21: upon SafeToSkip(s) do
22:   TRYSKIPWINDOW(s)
23:   if ltsOver ∉ state[s] then
24:     broadcast SkipFallbackVote(s) ▷ skip-fallback vote
25:     state[s] ← state[s] ∪ {BadWindow}
```

&lt;page_number&gt;24&lt;/page_number&gt;

---


## Page 25

Algorithm 2 Votor, helper functions

1: function WINDOWSLOTS(s)
2: return array with slot numbers of the leader window with slot s

3: function SETTIMEOUTS(s) ▷ $s$ is first slot of window
4: for $i \in$ WINDOWSLOTS(s) do ▷ set timeouts for all slots
5: schedule event Timeout(i) at time clock() + $\Delta_{\text{timeout}}$ + $(i - s + 1) \cdot \Delta_{\text{block}}$

6: ▷ Check if a notarization vote can be cast.
7: function TRYNOTAR(Block(s, hash, hash$_{\text{parent}}$))
8: if Voted $\in$ state[s] then
9: return false
10: firstSlot $\leftarrow$ (s is the first slot in leader window) ▷ boolean
11: if (firstSlot and ParentReady(hash$_{\text{parent}}$) $\in$ state[s]
or (not firstSlot and VotedNotar(hash$_{\text{parent}}$) $\in$ state[s-1])) then
12: broadcast NotarVote(s, hash) ▷ notarization vote
13: state[s] $\leftarrow$ state[s] $\cup$ {Voted, VotedNotar(hash)}
14: pendingBlocks[s] $\leftarrow$ ⊥ ▷ won’t vote notar a second time
15: TRYFINAL(s, hash) ▷ maybe vote finalize as well
16: return true
17: return false

18: function TRYFINAL(s, hash(b))
19: if BlockNotarized(hash(b)) $\in$ state[s] and VotedNotar(hash(b)) $\in$ state[s]
and BadWindow $\notin$ state[s] then
20: broadcast FinalVote(s) ▷ finalization vote
21: state[s] $\leftarrow$ state[s] $\cup$ {ItsOver}

22: function TRYSKIPWINDOW(s)
23: for $k \in$ WINDOWSLOTS(s) do ▷ skip unvoted slots
24: if Voted $\notin$ state[k] then
25: broadcast SkipVote(k) ▷ skip vote
26: state[k] $\leftarrow$ state[k] $\cup$ {Voted, BadWindow}
27: pendingBlocks[k] $\leftarrow$ ⊥ ▷ won’t vote notar after skip

28: function CHECKPENDINGBLOCKS()
29: for $s :$ pendingBlocks[s] $\neq$ ⊥ do ▷ iterate with increasing s
30: TRYNOTAR(pendingBlocks[s])

---


## Page 26

2.7 Block Creation

The leader $v$ of the window beginning with slot $s$ produces blocks for all slots $\text{WINDOW\_SLOTS}(s)$ in the window. After the event $\text{ParentReady}(s, \text{hash}(b_p))$ is emitted, $v$ can be sure that a block $b$ in slot $s$ with $b_p$ as its parent will be valid. In other words, other nodes will receive the certificates that resulted in $v$ emitting $\text{ParentReady}(\text{hash}(b_p))$, and emit this event themselves. As a result, all correct nodes will vote for $b$.

In the common case, only one $\text{ParentReady}(s, \text{hash}(b_p))$ will be emitted for a given $s$. Then, $v$ has to build its block on top of $b_p$ and cannot “fork off” the chain in any way. If $v$ emits many $\text{ParentReady}(s, \text{hash}(b_p))$ events for different blocks $b_p$ (as a result of the previous leader misbehaving or network delays), $v$ can build its block with any such $b_p$ as its parent.

Algorithm 3 introduces an optimization where $v$ starts building its block “optimistically” before any $\text{ParentReady}(s, \text{hash}(b_p))$ is emitted. Usually $v$ will receive some block $b_p$ in slot $s-1$ first, then observe a certificate for $b_p$ after additional network delay, and only then emit $\text{ParentReady}(s, \text{hash}(b_p))$. Algorithm 3 avoids this delay in the common case. If $v$ started building a block with parent $b_p$, but then only emits $\text{ParentReady}(s, \text{hash}(b'_p))$ where $b'_p \neq b_p$, $v$ will then instead indicate $b'_p$ as the parent of the block in the content of some slice $t$. In this case, slices $1, \ldots, t-1$ are ignored for the purpose of execution.

We allow changing the indicated parent of a block only once, and only in blocks in the first slot of a given window.

When a leader already observed some $\text{ParentReady}(s, \ldots)$, the leader produces all blocks of its leader window without delays. As a result, the first block $b_0$ always builds on some parent $b_p$ such that $v$ emitted $\text{ParentReady}(s, \text{hash}(b_p))$, $b_0$ is the parent of the block $b_1$ in slot $s+1$, $b_1$ is the parent of the block $b_2$ in slot $s+2$, and so on.

&lt;img&gt;
A diagram showing two scenarios of block creation.
Top scenario:
- A blue box labeled $b^k_1$ is at the left.
- A green box labeled $b^1_2$ is next to it.
- A green box labeled $b^2_2$ is next to it.
- A green box labeled $b^3_2$ is next to it.
- A green box labeled $b^k_2$ is next to it.
- An arrow points from the blue box to the green boxes, labeled "ParentReady(s, b_1)".
Bottom scenario:
- A blue box labeled $b^k_1$ is at the left.
- A red box labeled $b^1_2$ is next to it.
- A red box labeled $b^2_2$ is next to it.
- A green box labeled $b^3_2$ is next to it.
- A green box labeled $b^k_2$ is next to it.
- An arrow points from the blue box to the green boxes, labeled "ParentReady(s, b'_1)".
- An arrow points from the bottom green box to the top green boxes, labeled "$b_2$ starts here with a different parent $b'_1$".
&lt;/img&gt;

Figure 8: Handover between leader windows with $k$ slices per block. The new leader starts to produce the first slice of its first block ($b^1_2$) as soon as it received the last slice ($b^k_1$) of the previous leader. The common case is on top and the case where leader switches parents at the bottom, see also Algorithm 3.

---


## Page 27

**Algorithm 3** Block creation for leader window starting with slot $s$

1: **wait until** block $b_p$ in slot $s-1$ received **or** $\text{ParentReady}(\text{hash}(b_p)) \in \text{state}[s]$
2: $b \leftarrow$ generate a block with parent $b_p$ in slot $s$ ▶ *block being produced*
3: $t \leftarrow 1$ ▶ *slice index*
4: **while** $\text{ParentReady}(\dots) \not\in \text{state}[s]$ **do** ▶ *produce slices optimistically*
5: Rotor(slice $t$ of $b$)
6: $t \leftarrow t + 1$
7: **if** $\text{ParentReady}(\text{hash}(b_p)) \not\in \text{state}[s]$ **then** ▶ *change parent, reset block*
8: $b_p \leftarrow$ any $b'$ such that $\text{ParentReady}(\text{hash}(b')) \in \text{state}[s]$
9: $b \leftarrow$ generate a block with parent $b_p$ in slot $s$ starting with slice index $t$
10: $\text{start} \leftarrow \text{clock()}$ ▶ *some parent is ready, set timeout*
11: **while** $\text{clock()} < \text{start} + \Delta_{\text{block}}$ **do** ▶ *produce rest of block in normal slot time*
12: Rotor(slice $t$ of $b$)
13: $t \leftarrow t + 1$
14: **for** remaining slots of the window $s' = s+1, s+2, \dots$ **do**
15: $b \leftarrow$ generate a block with parent $b$ in slot $s'$
16: Rotor($b$) over $\Delta_{\text{block}}$

### 2.8 Repair

Repair is the process of retrieving a block with a given hash that is missing from Blokstor. After Pool obtains a certificate of signatures on $\text{Notar}(\text{slot}(b), \text{hash}(b))$ or $\text{NotarFallback}(\text{slot}(b), \text{hash}(b))$, the block $b$ with hash $\text{hash}(b)$ according to Definition [4] needs to be retrieved.

**Definition 19** (repair functions). The protocol supports functions for the repair process:

- **sampleNode()**: Choose some node $v$ at random based on stake.
- **getSliceCount($\text{hash}(b), v$)**: Contact node $v$, which returns $(k, r_k, \pi_k)$ where:
  - $k$ is the number of slices of $b$ as in Definition [4].
  - $r_k$ is the hash at position $k$ with path $\pi_k$ for Merkle root $\text{hash}(b)$.
The requesting node needs to make sure $r_k$ is the last non-zero leaf of the Merkle tree with root $\text{hash}(b)$. It verifies that the rightward intermediate hashes in $\pi_k$ correspond to empty sub-trees.
- **getSliceHash($t, \text{hash}(b), v$)**: Contact node $v$, which returns $(r_t, \pi_t)$ where $r_t$ is the hash at position $t$ with path $\pi_t$ for Merkle root $\text{hash}(b)$.
- **getShred($s, t, i, r_t, v$)**: Contact node $v$, which returns the shred $(s, t, i, z_t, r_t, (d_i, \pi_i), \sigma_t)$ as in Definition [1].

&lt;page_number&gt;27&lt;/page_number&gt;

---


## Page 28

The functions can fail verification of the data provided by $v$ and return $\bot$ (e.g. if invalid data is returned or $v$ simply does not have the correct data to return).

**Algorithm 4** Repair block $b$ with $\text{hash}(b)$ in slot $s$

```plaintext
1: $k \leftarrow \bot$
2: **while** $k = \bot$ **do** ▷ find the number of slices $k$ in $b$
3: $(k, r_k, \pi_k) \leftarrow \text{getSliceCount}(\text{hash}(b), \text{sampleNode}())$
4: **for** $t = 1, \ldots, k$ **concurrently do**
5:   **while** $r_t = \bot$ **do** ▷ get slice hash $r_t$ if missing
6:     $(r_t, \pi_t) \leftarrow \text{getSliceHash}(t, \text{hash}(b), \text{sampleNode}())$
7:   **for** each shred index $i$ **concurrently do**
8:     **while** shred with indices $s$, $t$, $i$ missing **do** ▷ get shred if missing
9:       shred $\leftarrow \text{getShred}(s, t, i, r_t, \text{sampleNode}())$
10:   store shred if valid
```
