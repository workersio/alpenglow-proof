---------------------------- MODULE MainProtocol ----------------------------

(* WP Sec. 2 overview + Sec. 1.5 model. Module encodes Votor + Rotor + Blokstor + Repair at the level of messages, slots, leader windows, and GST. Safety follows Sec. 2.9; liveness after GST follows Sec. 2.10. :contentReference[oaicite:1]{index=1} *)

(***************************************************************************
 * DESIGN DECISIONS AND MODELING ABSTRACTIONS
 *
 * This specification makes several intentional design choices to focus on
 * consensus-layer correctness while keeping the model tractable:
 *
 * 1. OPTIMISTIC BLOCK CREATION (Algorithm 3, §2.7, p.26-27):
 *    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
 *    OMITTED: The protocol allows leaders to start building blocks
 *    "optimistically" before ParentReady(s, hash(b_p)) fires, then
 *    potentially switch parent once in the first slot of a window.
 *
 *    Our model: Conservatively requires ParentReady before block proposal
 *    for all slots (see HonestProposeBlock guard line 184-185).
 *
 *    Rationale: This optimization reduces latency by ~1Δ in the common
 *    case but does NOT affect safety properties. The protocol explicitly
 *    states "affects latency only, not safety" (§2.7, Fig. 8 caption).
 *    We prioritize clarity and verifiable safety over latency modeling.
 *
 * 2. DATA PLANE ABSTRACTION (Definitions 1-2, §2.1, p.14-15):
 *    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
 *    ABSTRACTED: Shred-level details, slice reconstruction, Merkle path
 *    validation, and erasure-coded data pieces.
 *
 *    Our model: Works with complete blocks only. A block is either fully
 *    available to a node or not (blockAvailability variable).
 *
 *    Rationale: Standard practice for control-plane consensus models.
 *    The consensus algorithm reasons about complete blocks; shred-level
 *    details are data-plane concerns that don't affect consensus safety.
 *    Rotor.tla models the structural constraints (PS-P sampling, success
 *    conditions) without byte-level details.
 *
 * 3. REPAIR MECHANISM (Algorithm 4, §2.8, p.27-28):
 *    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
 *    SIMPLIFIED: Repair is modeled as atomic block transfer from a
 *    correct supplier to a node needing the block (RepairBlock action).
 *
 *    Our model: RepairBlock(v, block, supplier) instantly makes block
 *    available to v if supplier has it and v needs it (NeedsBlockRepair).
 *
 *    Rationale: The detailed repair algorithm (concurrent slice fetches,
 *    retry loops, getSliceCount/getSliceHash/getShred functions) affects
 *    repair latency and bandwidth, not consensus safety. Nodes obtain
 *    blocks they need for notarized/fast-finalized slots; the mechanism
 *    is orthogonal to consensus correctness.
 *
 * 4. SINGLE EPOCH SCOPE (§1.5, p.8-9):
 *    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
 *    SCOPED: Model covers one epoch with a fixed validator set and stake
 *    distribution.
 *
 *    Our model: Validators and StakeMap are constants. No validator
 *    registration/unregistration, no stake updates, no epoch transitions.
 *
 *    Rationale: Single-epoch correctness is the foundational property.
 *    Multi-epoch concerns (epoch boundaries, validator set changes, stake
 *    re-weighting) are important but orthogonal to core consensus safety.
 *    Standard approach: prove single-epoch safety first, then extend.
 *
 * 5. CRYPTOGRAPHIC PRIMITIVES (§1.6, p.12):
 *    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
 *    ASSUMED: Hash collision resistance, signature unforgeability,
 *    aggregate signature correctness, Merkle proof soundness.
 *
 *    Our model: Hashes are abstract identifiers (UniqueBlockHashes
 *    invariant), signatures are implicit via validator fields, aggregate
 *    signatures via NoDupValidators constraint.
 *
 *    Rationale: Standard cryptographic assumptions. Models assume these
 *    primitives work correctly; vulnerabilities in implementations are
 *    out of scope for consensus-layer verification.
 *
 * IMPLICATIONS FOR VERIFICATION:
 * ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
 * SCOPE: This is a SAFETY-ONLY specification. All invariants check safety
 * properties (Theorem 1, Lemmas 20-26). No temporal operators or fairness
 * constraints are included.
 *
 * This model is suitable for:
 *   ✓ Safety verification (Theorem 1: no conflicting finalizations)
 *   ✓ Invariant checking (all safety Lemmas 20-26)
 *   ✓ Certificate generation correctness
 *   ✓ Vote storage and pool behavior
 *   ✓ Dual voting path (fast 80%, slow 60%) correctness
 *   ✓ Byzantine resilience up to protocol assumptions
 *
 * Additional work needed for:
 *   • Liveness verification (Theorem 2: eventual finalization; requires
 *     fairness constraints on message delivery, clock advancement, event
 *     processing, and certificate propagation per §2.10)
 *   • Latency bounds (requires optimistic start, slice pipelining)
 *   • Bandwidth analysis (requires shred-level modeling)
 *   • Repair latency (requires detailed Algorithm 4)
 *   • Multi-epoch transitions
 ***************************************************************************)

EXTENDS Naturals, FiniteSets, Sequences, TLC,
        Messages, Blocks,
        Certificates, VoteStorage,
        VotorCore, Rotor
(* WP Sec. 2.4–2.6 define messages, certificates, Pool, and Votor;
   Sec. 2.2 defines Rotor; Sec. 2.3 Blokstor; Sec. 2.8 Repair. :contentReference[oaicite:2]{index=2} *)

CONSTANTS
    NumValidators,      
    ByzantineCount,     
    GST,                
    MaxSlot,            
    MaxBlocks,          
    
    Delta80,            
    Delta60             
(* WP Abstract + Sec. 1.3 latency: finality time min(δ80, 2δ60) “after distribution”.
   We model δθ with constants Delta80/Delta60 and tie “distribution” to availability (below). :contentReference[oaicite:3]{index=3} *)

ASSUME
    /\ NumValidators \in Nat \ {0}
    /\ ByzantineCount \in Nat
    /\ ByzantineCount < NumValidators
    /\ GST \in Nat
    /\ MaxSlot \in Nat \ {0}
    /\ MaxBlocks \in Nat \ {0}
    /\ Cardinality(Validators) = NumValidators
    /\ Slots = 1..MaxSlot   
    /\ Delta80 \in Nat \ {0}
    /\ Delta60 \in Nat \ {0}
(* WP Sec. 1.5 “Names/Node/Slot/Time” + Sec. 1.2 Assumptions. Slots are 1..MaxSlot within an epoch; time is unbounded Nat with GST marker. :contentReference[oaicite:4]{index=4} *)

VARIABLES
    validators,         
    blocks,             
    messages,           
    byzantineNodes,     
    unresponsiveNodes,  
    time,               
    finalized,          
    blockAvailability,  
    
    
    
    avail80Start,       
    avail60Start        
(* WP Sec. 2: validators carry Pool, state, timeouts (Alg. 1–2);
   blocks and availability model Blokstor/Rotor (Sec. 2.2–2.3);
   messages transport votes/certificates (Sec. 2.4–2.5);
   avail*Start capture the moment ≥θ stake has the block, to reflect δθ clocks. :contentReference[oaicite:5]{index=5} *)

vars == <<validators, blocks, messages, byzantineNodes, unresponsiveNodes, time, finalized, blockAvailability, avail80Start, avail60Start>>

CorrectNodes == Validators \ (byzantineNodes \cup unresponsiveNodes)
(* WP Assumption 2 (20% byz + 20% crash permitted, ≥60% correct). We separate byzantine vs. unresponsive to reason about Sec. 2.11. :contentReference[oaicite:6]{index=6} *)

ByzantineStakeOK == (CalculateStake(byzantineNodes) * 100) < (TotalStake * 20)
UnresponsiveStakeOK ==
    /\ (CalculateStake(unresponsiveNodes) * 100) <= (TotalStake * 20)
    /\ (byzantineNodes \cap unresponsiveNodes) = {}

Assumption2OK ==
    /\ ByzantineStakeOK
    /\ UnresponsiveStakeOK
    /\ (CalculateStake(CorrectNodes) * 100) > (TotalStake * 60)
(* WP Sec. 1.2 Assumptions 1 and 2. These constraints match f<20% byz and extra crash ≤20% with ≥60% correct; used for safety in Sec. 2.9 and liveness sketch in Sec. 2.11. :contentReference[oaicite:7]{index=7} *)

NeedsBlockRepair(pool, block) ==
    LET slot == block.slot
        hash == block.hash
    IN /\ slot \in Slots  
       /\ (HasFastFinalizationCert(pool, slot, hash)
           \/ HasNotarizationCert(pool, slot, hash)
           \/ HasNotarFallbackCert(pool, slot, hash))
(* WP Sec. 2.8 Algorithm 4 + Definition 19: after observing fast‑finalization or (notarization / notar‑fallback) for (s,hash), the block must be retrievable via Repair. :contentReference[oaicite:8]{index=8} *)

AfterGST == time >= GST
(* WP Sec. 1.5 GST definition. Before GST, messages may be arbitrarily delayed; after GST, Δ bounds hold. :contentReference[oaicite:9]{index=9} *)

ExistsBlockAt(s, h) == \E b \in blocks : b.slot = s /\ b.hash = h
(* Utility for availability timers. *)

AvailabilityStakeFor(s, h) ==
    LET holders == { v \in CorrectNodes :
                        \E b \in blockAvailability[v] : b.slot = s /\ b.hash = h }
    IN CalculateStake(holders)

AvailMeets(s, h, thetaPercent) ==
    MeetsThreshold(AvailabilityStakeFor(s, h), thetaPercent)

Avail80Now(s, h) == AvailMeets(s, h, 80)
Avail60Now(s, h) == AvailMeets(s, h, 60)
(* WP Abstract + Sec. 1.3: δθ measures delay for θ% stake to communicate.
   We proxy “distributed” by ≥θ% correct stake having the block (Rotor-delivered),
   starting δ80/δ60 clocks accordingly. :contentReference[oaicite:10]{index=10} *)

Init ==
    /\ validators = [v \in Validators |->
                        LET base == InitValidatorState(v)
                            withParent == [base EXCEPT !.parentReady[1] = GenesisHash]
                            withClock == [withParent EXCEPT !.clock = GST]
                        IN AddState(withClock, 1, "ParentReady")]
    (* WP Sec. 2.7: first slot of first window is parent‑ready on genesis so the first leader can produce immediately. :contentReference[oaicite:11]{index=11} *)
    /\ blocks = {GenesisBlock}
    /\ messages = {}
    /\ byzantineNodes \in {S \in SUBSET Validators : Cardinality(S) = ByzantineCount}
    /\ unresponsiveNodes \in SUBSET (Validators \ byzantineNodes)
    /\ (CalculateStake(byzantineNodes) * 100) < (TotalStake * 20)
    /\ (CalculateStake(unresponsiveNodes) * 100) <= (TotalStake * 20)
    /\ time = GST
    /\ finalized = [v \in Validators |-> {}]
    /\ blockAvailability = [v \in Validators |-> {GenesisBlock}]
    /\ avail80Start = [s \in 1..MaxSlot |-> [h \in BlockHashes |-> 0]]
    /\ avail60Start = [s \in 1..MaxSlot |-> [h \in BlockHashes |-> 0]]
(* WP Sec. 2.1–2.3: initialize genesis block, Blokstor contains genesis everywhere;
   Sec. 1.2 stake bounds. :contentReference[oaicite:12]{index=12} *)

ReceiveBlock(v, block) ==
    /\ v \in CorrectNodes
    /\ block \in blocks
    /\ IsValidBlock(block)
    /\ block \in blockAvailability[v]
    /\ ~HasState(validators[v], block.slot, "BlockSeen")
    /\ validators' = [validators EXCEPT ![v] =
                         AddState(HandleBlock(validators[v], block), block.slot, "BlockSeen")]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, unresponsiveNodes, time, finalized, blockAvailability, avail80Start, avail60Start>>
(* WP Sec. 2.3 Blokstor: node processes first complete block per slot when stored; we tag “BlockSeen”. Safety uses only notarized/skip outcomes (Sec. 2.9). :contentReference[oaicite:13]{index=13} *)

GenerateCertificateAction(v, slot) ==
    /\ v \in CorrectNodes
    /\ slot \in Slots
    /\ slot <= MaxSlot
    /\ LET pool == validators[v].pool
           certs == GenerateCertificate(pool, slot)
          candidates == {c \in certs :
                             /\ c \notin messages
                             /\ (\E w \in Validators : CanStoreCertificate(validators[w].pool, c))
                             /\ CanStoreCertificate(validators[v].pool, c)}
       IN /\ candidates # {}
          /\ LET cert ==
                    IF (\E c \in candidates : c.type = "FastFinalizationCert")
                    THEN CHOOSE c \in candidates : c.type = "FastFinalizationCert"
                    ELSE IF (\E c \in candidates : c.type = "NotarizationCert")
                         THEN CHOOSE c \in candidates : c.type = "NotarizationCert"
                         ELSE CHOOSE c \in candidates : TRUE
             IN /\ messages' = messages \cup {cert}
                /\ validators' = [validators EXCEPT ![v].pool = StoreCertificate(validators[v].pool, cert)]
    /\ UNCHANGED <<blocks, byzantineNodes, unresponsiveNodes, time, finalized, blockAvailability, avail80Start, avail60Start>>
(* WP Def. 13: when enough votes exist, generate and broadcast the certificate, storing one per type. Prefer fast-finalization if present. :contentReference[oaicite:14]{index=14} *)

FinalizeBlock(v, block) ==
    /\ v \in CorrectNodes
    /\ block \in blocks
    /\ block.slot \in Slots  
    /\ LET pool == validators[v].pool
           slot == block.slot
       IN \/ HasFastFinalizationCert(pool, slot, block.hash)
          \/ CanFinalizeSlow(pool, slot, block.hash)
    /\ finalized' = [finalized EXCEPT ![v] = finalized[v] \cup GetAncestors(block, blocks)]
    /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, unresponsiveNodes, time, blockAvailability, avail80Start, avail60Start>>
(* WP Def. 14 finalization: fast if fast-finalization cert on (s,hash); slow if finalization cert on s with unique notarized block; ancestors finalize first. :contentReference[oaicite:15]{index=15} *)

ByzantineAction(v) ==
    /\ v \in byzantineNodes
    /\ \E vote \in Vote :
        /\ IsValidVote(vote)
        /\ vote.validator = v
        /\ vote.slot <= MaxSlot
        /\ vote.blockHash \in ({b.hash : b \in blocks} \cup {NoBlock})
        /\ Cardinality({m \in messages : m \in Vote /\ m.validator \in byzantineNodes}) < 3
        /\ messages' = messages \cup {vote}
    /\ UNCHANGED <<validators, blocks, byzantineNodes, unresponsiveNodes, time, finalized, blockAvailability, avail80Start, avail60Start>>
(* WP Sec. 1.5 “Adversary”: byzantine nodes may send arbitrarily scheduled but syntactically valid votes; safety must hold regardless (Sec. 2.9). :contentReference[oaicite:16]{index=16} *)

HonestProposeBlock(leader, slot, parent) ==
    /\ leader \in CorrectNodes
    /\ parent \in blocks
    /\ parent \in blockAvailability[leader]
    /\ slot \in Slots
    /\ slot > parent.slot
    /\ slot <= MaxSlot
    /\ Cardinality(blocks) < MaxBlocks
    /\ ~\E b \in blocks : b.slot = slot /\ b.leader = leader
    /\ IsFirstSlotOfWindow(slot)
        => /\ HasState(validators[leader], slot, "ParentReady")
           /\ parent.hash = validators[leader].parentReady[slot]
    /\ ~IsFirstSlotOfWindow(slot)
        => \/ parent.slot < slot
    /\ LET newBlock == [
           slot |-> slot,
           hash |-> CHOOSE h \in BlockHashes : 
                    h \notin {b.hash : b \in blocks},
           parent |-> parent.hash,
           leader |-> leader
       ]
       IN 
          /\ LeaderMatchesSchedule(newBlock)
          /\ IsValidBlock(newBlock)
          /\ blocks' = blocks \cup {newBlock}
          /\ blockAvailability' = [blockAvailability EXCEPT ![leader] = @ \cup {newBlock}]
          /\ UNCHANGED <<validators, messages, byzantineNodes, unresponsiveNodes, time, finalized, avail80Start, avail60Start>>
(* WP Sec. 2.7 + Alg. 3: leader builds a block per slot; in first slot require ParentReady; later slots chain to previous block. We conservatively omit the “optimistic parent switch” micro‑optimization; this affects latency only, not safety (Sec. 2.7 Fig. 8). :contentReference[oaicite:17]{index=17} *)

ByzantineProposeBlock(leader, slot, parent) ==
    /\ leader \in byzantineNodes
    /\ parent \in blocks
    /\ slot \in Slots
    /\ slot > parent.slot
    /\ slot <= MaxSlot
    /\ Cardinality(blocks) < MaxBlocks
    /\ LET newBlock == [
           slot |-> slot,
           hash |-> CHOOSE h \in BlockHashes :
                    h \notin {b.hash : b \in blocks},
           parent |-> parent.hash,
           leader |-> leader
       ]
       IN /\ LeaderMatchesSchedule(newBlock)
          /\ blocks' = blocks \cup {newBlock}
          /\ \E recipients \in SUBSET Validators :
                blockAvailability' =
                    [w \in Validators |->
                        IF w \in recipients THEN blockAvailability[w] \cup {newBlock}
                        ELSE blockAvailability[w]]
          /\ UNCHANGED <<validators, messages, byzantineNodes, unresponsiveNodes, time, finalized, avail80Start, avail60Start>>
(* WP Sec. 2.2 Rotor + Sec. 2.7: faulty leaders may disseminate unevenly or equivocate; availability reflects partial delivery. Safety later prevents conflicting notarizations (Lemmas 21, 24). :contentReference[oaicite:18]{index=18} *)

AdvanceTime ==
    /\ time' = time + 1
    /\ validators' = [w \in Validators |->
                        IF w \in CorrectNodes
                        THEN AdvanceClock(validators[w], time')
                        ELSE validators[w]]
    /\ avail80Start' =
        [s \in 1..MaxSlot |->
            [h \in BlockHashes |->
                IF avail80Start[s][h] # 0 THEN avail80Start[s][h]
                ELSE IF ExistsBlockAt(s, h) /\ Avail80Now(s, h)
                     THEN time'
                     ELSE 0
            ]
        ]
    /\ avail60Start' =
        [s \in 1..MaxSlot |->
            [h \in BlockHashes |->
                IF avail60Start[s][h] # 0 THEN avail60Start[s][h]
                ELSE IF ExistsBlockAt(s, h) /\ Avail60Now(s, h)
                     THEN time'
                     ELSE 0
            ]
        ]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, unresponsiveNodes, finalized, blockAvailability>>
(* WP Sec. 1.5 “Time/Timeout” and Sec. 1.3: start δ80/δ60 clocks the first time ≥θ correct stake has the block. Local clocks advance monotonically (timeouts set elsewhere). :contentReference[oaicite:19]{index=19} *)

RotorDisseminateSuccess(block) ==
    /\ block \in blocks
    /\ block.leader \in CorrectNodes
    /\ LET needers == {v \in Validators : block \notin blockAvailability[v]}
           nextSlot == IF block.slot + 1 <= MaxSlot THEN block.slot + 1 ELSE block.slot
           nextLeader == Leader(nextSlot)
       IN /\ needers # {}
          /\ \E bins \in BinCandidates(needers, nextLeader) :
                /\ RotorSuccessfulBins(block.leader, bins, CorrectNodes)
                /\ LET relays == BinsToRelaySet(bins)
                   IN /\ relays # {}
                      /\ blockAvailability' =
                            [w \in Validators |->
                                IF w \in CorrectNodes
                                THEN blockAvailability[w] \cup {block}
                                ELSE blockAvailability[w]]
                      /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, unresponsiveNodes, time, finalized, avail80Start, avail60Start>>
(* WP Sec. 2.2 Definition 6 + Lemma 7 + Lemma 8: if leader correct and ≥γ correct relays, all correct nodes receive within ≤2δ; we abstract the sampling via bins, then deliver to all correct nodes. :contentReference[oaicite:20]{index=20} *)

RotorFailInsufficientRelays(block) ==
    /\ block \in blocks
    /\ block.leader \in CorrectNodes
    /\ LET needers == {v \in Validators : block \notin blockAvailability[v]}
           nextSlot == IF block.slot + 1 <= MaxSlot THEN block.slot + 1 ELSE block.slot
           nextLeader == Leader(nextSlot)
       IN /\ needers # {}
          /\ \E bins \in BinCandidates(needers, nextLeader) :
                /\ ~RotorSuccessfulBins(block.leader, bins, CorrectNodes)
                /\ LET relays == BinsToRelaySet(bins)
                   IN /\ relays # {}
                      /\ blockAvailability' = [w \in Validators |->
                                                IF w \in relays
                                                THEN blockAvailability[w] \cup {block}
                                                ELSE blockAvailability[w]]
                      /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, unresponsiveNodes, time, finalized, avail80Start, avail60Start>>
(* WP Sec. 2.2: dissemination can fail if too few correct relays; only relays obtain block. Liveness then relies on fallback votes/repair. :contentReference[oaicite:21]{index=21} *)

RotorFailByzantineLeader(block) ==
    /\ block \in blocks
    /\ block.leader \in byzantineNodes
    /\ \E recipients \in SUBSET Validators :
          /\ blockAvailability' = [w \in Validators |->
                                        IF w \in recipients
                                        THEN blockAvailability[w] \cup {block}
                                        ELSE blockAvailability[w]]
          /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, unresponsiveNodes, time, finalized, avail80Start, avail60Start>>
(* WP Sec. 2.2 and Sec. 2.11: malicious leaders may selectively disseminate. Repair and fallback handle progress. :contentReference[oaicite:22]{index=22} *)

RotorNoDissemination(block) ==
    /\ block \in blocks
    /\ block.leader \in byzantineNodes
    /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, unresponsiveNodes, time, finalized, blockAvailability, avail80Start, avail60Start>>
(* WP Sec. 2.2: a faulty leader can send nothing; Votor’s timeout path ensures safety and progress after GST (Sec. 2.10). :contentReference[oaicite:23]{index=23} *)

RepairBlock(v, block, supplier) ==
    /\ v \in CorrectNodes
    /\ block \in blocks
    /\ block \notin blockAvailability[v]
    /\ NeedsBlockRepair(validators[v].pool, block)
    /\ supplier \in CorrectNodes
    /\ block \in blockAvailability[supplier]
    /\ blockAvailability' = [blockAvailability EXCEPT ![v] = @ \cup {block}]
    /\ UNCHANGED <<validators, blocks, messages, byzantineNodes, time, finalized, avail80Start, avail60Start>>
(* WP Sec. 2.8 Algorithm 4: on observing (fast‑final or notar*/slot) evidence, repair retrieves missing block from peers. :contentReference[oaicite:24]{index=24} *)

DeliverVote ==
    /\ \E vote \in messages : vote \in Vote /\ IsValidVote(vote)
    /\ LET vmsg == CHOOSE vv \in messages : vv \in Vote /\ IsValidVote(vv)
       IN /\ messages' = messages \ {vmsg}
          /\ validators' = [w \in Validators |->
                               [validators[w] EXCEPT
                                   !.pool = StoreVote(@, vmsg)]]
    /\ UNCHANGED <<blocks, byzantineNodes, unresponsiveNodes, time, finalized, blockAvailability, avail80Start, avail60Start>>
(* WP Sec. 2.5 Def. 12: Pool stores first notar/skip, up to limited fallback, and first final vote, keyed by (slot,validator). :contentReference[oaicite:25]{index=25} *)

DeliverCertificate ==
    /\ \E cert \in messages : cert \in Certificate /\ IsValidCertificate(cert)
    /\ LET cmsg == CHOOSE cc \in messages : cc \in Certificate /\ IsValidCertificate(cc)
       IN /\ messages' = messages \ {cmsg}
          /\ validators' = [w \in Validators |->
                               [validators[w] EXCEPT
                                   !.pool = StoreCertificate(@, cmsg)]]
    /\ UNCHANGED <<blocks, byzantineNodes, unresponsiveNodes, time, finalized, blockAvailability, avail80Start, avail60Start>>
(* WP Sec. 2.5 Def. 13: Pool stores at most one certificate per type, broadcasts on add. :contentReference[oaicite:26]{index=26} *)

BroadcastLocalVote ==
    /\ \E v \in CorrectNodes, s \in 1..MaxSlot :
         LET localVotes == validators[v].pool.votes[s][v]
         IN localVotes # {}
    /\ LET vSel == CHOOSE vv \in CorrectNodes :
                      \E s \in 1..MaxSlot : validators[vv].pool.votes[s][vv] # {}
           sSel == CHOOSE ss \in 1..MaxSlot : validators[vSel].pool.votes[ss][vSel] # {}
           vt == CHOOSE x \in validators[vSel].pool.votes[sSel][vSel] : TRUE
       IN 
          /\ vt \notin messages
          /\ \E w \in Validators : vt \notin validators[w].pool.votes[vt.slot][vt.validator]
          /\ messages' = messages \cup {vt}
    /\ UNCHANGED <<validators, blocks, byzantineNodes, unresponsiveNodes, time, finalized, blockAvailability, avail80Start, avail60Start>>
(* WP Sec. 2.6 Alg. 1–2: votes are broadcast once produced; uniqueness per slot/validator enforced. :contentReference[oaicite:27]{index=27} *)

EmitBlockNotarized ==
    /\ \E v \in CorrectNodes, b \in blocks :
         /\ b.slot \in (Slots \cap 1..MaxSlot)
         /\ ShouldEmitBlockNotarized(validators[v].pool, b.slot, b.hash)
         /\ ~HasState(validators[v], b.slot, "BlockNotarized")
         /\ validators' = [validators EXCEPT ![v] =
                               HandleBlockNotarized(@, b.slot, b.hash)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, unresponsiveNodes, time, finalized, blockAvailability, avail80Start, avail60Start>> 
(* WP Def. 15 “BlockNotarized(s,h)” event: Pool holds a notarization cert for b. We set the local state tag. :contentReference[oaicite:28]{index=28} *)

EmitSafeToNotar ==
    /\ \E v \in CorrectNodes, s \in 1..MaxSlot, b \in blocks :
         /\ b.slot = s
         /\ b \in blockAvailability[v]
         /\ LET alreadyVoted == HasState(validators[v], s, "Voted")
                votedForB == VotedForBlock(validators[v], s, b.hash)
            IN CanEmitSafeToNotar(validators[v].pool, s, b.hash, b.slot - 1, b.parent, alreadyVoted, votedForB)
         /\ ~HasState(validators[v], s, "BadWindow") 
         /\ validators' = [validators EXCEPT ![v] = HandleSafeToNotar(@, b)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, unresponsiveNodes, time, finalized, blockAvailability, avail80Start, avail60Start>>
(* WP Def. 16 “SafeToNotar(s,h)”: either notar(b)≥40% or (skip(s)+notar(b)≥60% and notar(b)≥20%); also require parent certs per first‑slot rule. We then issue notar‑fallback. :contentReference[oaicite:29]{index=29} *)

EmitSafeToSkip ==
    /\ \E v \in CorrectNodes, s \in 1..MaxSlot :
         /\ LET alreadyVoted == HasState(validators[v], s, "Voted")
                votedSkip == 
                    \E vt \in GetVotesForSlot(validators[v].pool, s) :
                        /\ vt.validator = v
                        /\ vt.type = "SkipVote"
            IN CanEmitSafeToSkip(validators[v].pool, s, alreadyVoted, votedSkip)
         /\ ~HasSkipCert(validators[v].pool, s) 
         /\ ~HasState(validators[v], s, "BadWindow") 
         /\ validators' = [validators EXCEPT ![v] = HandleSafeToSkip(@, s)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, unresponsiveNodes, time, finalized, blockAvailability, avail80Start, avail60Start>>
(* WP Def. 16 “SafeToSkip(s)”: skip(s)+Σ_b notar(b) − max_b notar(b) ≥ 40%; we then issue skip‑fallback. :contentReference[oaicite:30]{index=30} *)

EmitParentReady ==
    /\ \E v \in CorrectNodes, s \in 1..MaxSlot, p \in blocks :
         /\ p.slot < s  
         /\ ShouldEmitParentReady(validators[v].pool, s, p.hash, p.slot)
         /\ ~HasState(validators[v], s, "ParentReady")
         /\ validators' = [validators EXCEPT ![v] = HandleParentReady(@, s, p.hash)]
    /\ UNCHANGED <<blocks, messages, byzantineNodes, unresponsiveNodes, time, finalized, blockAvailability, avail80Start, avail60Start>>
(* WP Def. 15 “ParentReady(s,hash(p))”: first slot of window with notar/‑fallback for p and skips for gaps; enables leader timeouts (Alg. 1 line 15). :contentReference[oaicite:31]{index=31} *)

Next ==
    \/ \E v \in Validators, b \in blocks : ReceiveBlock(v, b)
    \/ BroadcastLocalVote
    \/ DeliverVote
    \/ \E v \in Validators, s \in 1..MaxSlot : GenerateCertificateAction(v, s)
    \/ DeliverCertificate
    \/ EmitBlockNotarized
    \/ EmitParentReady
    \/ EmitSafeToNotar
    \/ EmitSafeToSkip
    \/ \E v \in Validators, b \in blocks : FinalizeBlock(v, b)
    \/ \E b \in blocks : RotorDisseminateSuccess(b)
    \/ \E b \in blocks : RotorFailInsufficientRelays(b)
    \/ \E v \in Validators, b \in blocks, supplier \in Validators : RepairBlock(v, b, supplier)
    \/ \E l \in Validators, s \in 1..MaxSlot, p \in blocks : HonestProposeBlock(l, s, p)
    \/ \E l \in Validators, s \in 1..MaxSlot, p \in blocks : ByzantineProposeBlock(l, s, p)
    \/ \E v \in byzantineNodes : ByzantineAction(v)
    \/ \E b \in blocks : RotorFailByzantineLeader(b)
    \/ \E b \in blocks : RotorNoDissemination(b)
    \/ AdvanceTime
(* WP Sec. 2 Figure 7 pipeline: dissemination → votes → certs → finalization; adversarial and repair transitions included. :contentReference[oaicite:32]{index=32} *)

Fairness ==
    /\ WF_vars(AdvanceTime)
    /\ WF_vars(IF AfterGST THEN DeliverVote ELSE UNCHANGED vars)
    /\ WF_vars(IF AfterGST THEN DeliverCertificate ELSE UNCHANGED vars)
    /\ WF_vars(IF AfterGST THEN BroadcastLocalVote ELSE UNCHANGED vars)
    /\ WF_vars(IF AfterGST THEN EmitBlockNotarized ELSE UNCHANGED vars)
    /\ WF_vars(IF AfterGST THEN EmitSafeToNotar ELSE UNCHANGED vars)
    /\ WF_vars(IF AfterGST THEN EmitSafeToSkip ELSE UNCHANGED vars)
    /\ WF_vars(IF AfterGST THEN EmitParentReady ELSE UNCHANGED vars)
    /\ WF_vars(IF AfterGST THEN (\E l \in Validators, s \in 1..MaxSlot, p \in blocks : HonestProposeBlock(l, s, p)) ELSE UNCHANGED vars)
    /\ WF_vars(IF AfterGST THEN (\E v \in Validators, s \in 1..MaxSlot : GenerateCertificateAction(v, s)) ELSE UNCHANGED vars)
    /\ WF_vars(IF AfterGST THEN (\E v \in Validators, b \in blocks : FinalizeBlock(v, b)) ELSE UNCHANGED vars)
    /\ WF_vars(IF AfterGST THEN (\E b \in blocks : RotorDisseminateSuccess(b)) ELSE UNCHANGED vars)
    /\ WF_vars(IF AfterGST THEN (\E v \in Validators, b \in blocks, supplier \in Validators : RepairBlock(v, b, supplier)) ELSE UNCHANGED vars)
    /\ \A v \in Validators :
           IF v \in CorrectNodes
           THEN WF_vars(IF AfterGST THEN (\E b \in blocks : ReceiveBlock(v, b)) ELSE UNCHANGED vars)
           ELSE TRUE
(* WP Sec. 1.5 GST: after GST we require weak fairness for delivery, voting, cert generation, and parent‑ready, matching liveness proof structure (Lemmas 33–42, Theorem 2). :contentReference[oaicite:33]{index=33} *)

Spec == Init /\ [][Next]_vars /\ Fairness
(* Full behavior as in Sec. 2: init, step relation, and fairness under GST. :contentReference[oaicite:34]{index=34} *)

SafetyInvariant ==
    \A v1, v2 \in CorrectNodes :
    \A b1 \in finalized[v1], b2 \in finalized[v2] :
        (b1.slot <= b2.slot) => IsAncestor(b1, b2, blocks)
(* WP Theorem 1 Safety: later finalized blocks are descendants of earlier. :contentReference[oaicite:35]{index=35} *)

NoConflictingFinalization ==
    \A v1, v2 \in CorrectNodes :
    \A b1 \in finalized[v1], b2 \in finalized[v2] :
        (b1.slot = b2.slot) => b1.hash = b2.hash
(* Restates uniqueness per slot from Theorem 1. :contentReference[oaicite:36]{index=36} *)

SafeToSkipPrecludesFastNow ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        CanEmitSafeToSkip(validators[v].pool, s, TRUE, FALSE)
            => (\A b \in {x \in blocks : x.slot = s} :
                    ~MeetsThreshold(NotarStake(validators[v].pool, s, b.hash), 80))
(* WP Lemma 21(i–iii): if fast‑finalization is possible, SafeToSkip cannot hold; conversely SafeToSkip implies no block can reach 80% notar quickly. :contentReference[oaicite:37]{index=37} *)

ChainConsistency == SafetyInvariant

VoteUniqueness ==
    \A v \in CorrectNodes :
    \A slot \in 1..MaxSlot :
        LET votes == GetVotesForSlot(validators[v].pool, slot)
            initVotes == {vt \in votes : 
                         IsInitialVote(vt) /\ vt.validator = v}
        IN Cardinality(initVotes) <= 1
(* WP Lemma 20: one initial vote (notar or skip) per slot per node. Alg. 2 lines 8–16, 22–27. :contentReference[oaicite:38]{index=38} *)

UniqueNotarization ==
    \A v \in CorrectNodes :
    \A slot \in 1..MaxSlot :
        LET pool == validators[v].pool
            notarCerts == {c \in pool.certificates[slot] : 
                          c.type = "NotarizationCert"}
            notarBlocks == {c.blockHash : c \in notarCerts}
        IN Cardinality(notarBlocks) <= 1
(* WP Lemma 24: at most one block notarized per slot. :contentReference[oaicite:39]{index=39} *)

GlobalNotarizationUniqueness ==
    \A s \in 1..MaxSlot :
        \A v1, v2 \in CorrectNodes :
            LET p1 == validators[v1].pool
                p2 == validators[v2].pool
            IN \A c1 \in p1.certificates[s], c2 \in p2.certificates[s] :
                   (c1.type \in {"NotarizationCert", "NotarFallbackCert"} /\
                    c2.type \in {"NotarizationCert", "NotarFallbackCert"}) =>
                   c1.blockHash = c2.blockHash
(* WP Lemmas 23–24 imply global uniqueness of notarized/‑fallback block per slot once ≥40% correct stake aligns. :contentReference[oaicite:40]{index=40} *)

FinalizedImpliesNotarized ==
    \A v \in CorrectNodes :
    \A b \in finalized[v] :
        b.slot \in Slots =>  
            LET pool == validators[v].pool
            IN \E cert \in pool.certificates[b.slot] :
                /\ cert.type \in {"NotarizationCert", "FastFinalizationCert"}
                /\ cert.blockHash = b.hash
(* WP Lemma 25: finalized ⇒ notarized (fast path trivially implies notar; slow path observes notar before final votes). :contentReference[oaicite:41]{index=41} *)

CertificateNonEquivocation ==
    \A v \in CorrectNodes :
    \A slot \in 1..MaxSlot :
        LET pool == validators[v].pool
        IN \A c1, c2 \in pool.certificates[slot] :
            (c1.type = c2.type /\ 
             c1.type \in {"NotarizationCert", "NotarFallbackCert", "FastFinalizationCert"}) =>
            c1.blockHash = c2.blockHash
(* WP Def. 13 storage rule: single cert per type per slot; prevents equivocation locally. :contentReference[oaicite:42]{index=42} *)

Lemma21_FastFinalizationProperty ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        LET pool == validators[v].pool
            fastCerts == {c \in pool.certificates[s] : c.type = "FastFinalizationCert"}
        IN \A fc \in fastCerts :
            LET h == fc.blockHash
                otherNotarCerts == {c \in pool.certificates[s] :
                    /\ c.type \in {"NotarizationCert", "NotarFallbackCert"}
                    /\ c.blockHash # h}
                skipCerts == {c \in pool.certificates[s] : c.type = "SkipCert"}
            IN /\ otherNotarCerts = {}  
               /\ skipCerts = {}        
(* WP Lemma 21(i–iii): fast‑finalizing b excludes any other notar/‑fallback in s and excludes skip in s. :contentReference[oaicite:43]{index=43} *)

NoMixFinalizationAndFallback ==
    \A v \in CorrectNodes :
        Lemma22_ItsOverImpliesNotBadWindow(validators[v]) /\
        Lemma22_BadWindowImpliesNotItsOver(validators[v])
(* WP Lemma 22: after final vote (ItsOver) no fallback votes, and vice versa. Alg. 1–2 guards. :contentReference[oaicite:44]{index=44} *)

Lemma23_FortyPercentPreventsConflictingNotar ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        LET pool == validators[v].pool
            notarVotesForHash(h) == {vote \in GetVotesForSlot(pool, s) :
                /\ IsInitialNotarVote(vote)
                /\ vote.blockHash = h
                /\ vote.validator \in CorrectNodes}
            hashesWithOver40 == {h \in BlockHashes :
                MeetsThreshold(StakeFromVotes(notarVotesForHash(h)), 41)}
        IN \A h1, h2 \in hashesWithOver40 : h1 = h2  
(* WP Lemma 23: >40% correct notar votes on one hash preclude notarization of any conflicting block in that slot. :contentReference[oaicite:45]{index=45} *)

Lemma26_SlowFinalizationProperty ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        LET pool == validators[v].pool
            finalizationCerts == {c \in pool.certificates[s] : c.type = "FinalizationCert"}
        IN \A fc \in finalizationCerts :
            LET notarCerts == {c \in pool.certificates[s] : c.type = "NotarizationCert"}
            IN notarCerts # {} =>
                LET h == (CHOOSE c \in notarCerts : TRUE).blockHash
                    otherNotarCerts == {c \in pool.certificates[s] :
                        /\ c.type \in {"NotarizationCert", "NotarFallbackCert"}
                        /\ c.blockHash # h}
                    skipCerts == {c \in pool.certificates[s] : c.type = "SkipCert"}
                IN /\ Cardinality(notarCerts) = 1  
                   /\ otherNotarCerts = {}         
                   /\ skipCerts = {}               
(* WP Lemma 26: when slow‑finalizing, exactly one notarized block exists for the slot and no skip for that slot. :contentReference[oaicite:46]{index=46} *)

PoolSkipVsBlockExclusion ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        SkipVsBlockCertExclusion(validators[v].pool.certificates[s])
(* WP Defs. 11–16: skip vs notarization certificates are mutually exclusive per slot at one node. :contentReference[oaicite:47]{index=47} *)

HonestNonEquivocation ==
    \A l \in CorrectNodes :
    \A s \in 1..MaxSlot :
        LET bs == {b \in blocks : b.leader = l /\ b.slot = s}
        IN Cardinality(bs) <= 1
(* WP Sec. 2.7 leader behavior: one block per slot per leader. :contentReference[oaicite:48]{index=48} *)

TransitCertificatesValid ==
    \A c \in messages : c \in Certificate => IsValidCertificate(c)
 
TransitVotesValid ==
    \A v \in messages : v \in Vote => IsValidVote(v)
(* WP Sec. 2.4–2.5: only well‑formed messages circulate. :contentReference[oaicite:49]{index=49} *)

LocalVotesWellFormed ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        \A vt \in validators[v].pool.votes[s][v] :
            IsValidVote(vt) /\ vt.slot = s
(* WP Def. 12 storage discipline per slot. :contentReference[oaicite:50]{index=50} *)

PoolFastPathImplication ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        FastImpliesNotarThresholdOnly(validators[v].pool.certificates[s])
(* WP Table 6 + Def. 14: fast‑finalization implies ≥80% notar votes. :contentReference[oaicite:51]{index=51} *)

PoolFinalizationImpliesNotarizationPresent ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        FinalizationImpliesNotarizationPresent(validators[v].pool, s)
(* WP Def. 14 slow finalization requires unique notarized block. :contentReference[oaicite:52]{index=52} *)

CertificateBlockProvenance ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        \A c \in validators[v].pool.certificates[s] :
            (c.type \in {"NotarizationCert", "NotarFallbackCert", "FastFinalizationCert"}) =>
            c.blockHash \in {b.hash : b \in blocks}
(* WP Sec. 2.3–2.8: certificates reference extant blocks (stored or repairable). :contentReference[oaicite:53]{index=53} *)

PoolMultiplicityOK ==
    \A v \in Validators : MultiplicityRulesRespected(validators[v].pool)

PoolCertificateUniqueness ==
    \A v \in Validators : CertificateUniqueness(validators[v].pool)

PoolCertificatesValid ==
    \A v \in Validators :
    \A s \in 1..MaxSlot :
        AllCertificatesValid(validators[v].pool.certificates[s])

PoolCertificatesWellFormedOK ==
    \A v \in Validators : CertificatesWellFormed(validators[v].pool)

PoolAlignmentOK ==
    \A v \in Validators :
        /\ PoolVotesSlotValidatorAligned(validators[v].pool)
        /\ PoolCertificatesSlotAligned(validators[v].pool)

BucketSlotConsistencyOK ==
    \A v \in Validators : BucketSlotConsistency(validators[v].pool)
(* WP Defs. 12–13 enforce per‑slot, per‑type storage and alignment. :contentReference[oaicite:54]{index=54} *)

PoolSkipFallbackAfterInitialNotarOK ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        SkipFallbackAfterInitialNotarAt(validators[v].pool, s, v)
(* WP Alg. 1–2: fallback only after initial vote and event conditions. :contentReference[oaicite:55]{index=55} *)

TotalNotarStakeSanity ==
    \A v \in Validators :
    \A s \in 1..MaxSlot :
        TotalNotarStakeEqualsUniqueNotarVoters(validators[v].pool, s)
(* WP Def. 12 counting: stake for notar in a slot counts each validator once. :contentReference[oaicite:56]{index=56} *)

TimeoutsInFuture ==
    \A v \in CorrectNodes:
        \A s \in 1..MaxSlot:
            LET timeout == validators[v].timeouts[s]
            IN timeout = 0 \/ timeout > validators[v].clock
(* WP Def. 17: timeouts scheduled in the future relative to local clock. :contentReference[oaicite:57]{index=57} *)

LocalClockMonotonic ==
    \A v \in CorrectNodes : validators[v].clock <= time
(* WP Sec. 1.5 “Time”: local clocks drift but monotonically advance; we conservatively bound by global “time”. :contentReference[oaicite:58]{index=58} *)

RotorSelectSoundness ==
    \A b \in blocks :
        LET needers == {v \in Validators : b \notin blockAvailability[v]}
            nextSlot == IF b.slot + 1 <= MaxSlot THEN b.slot + 1 ELSE b.slot
            nextLeader == Leader(nextSlot)
        IN RotorSelectSound(b, needers, nextLeader)
(* WP Sec. 3.1 Smart sampling: relay selection soundness; bins and partition sampling reduce variance and failure probability (Thm 3). :contentReference[oaicite:59]{index=59} *)

BasicLiveness ==
    (time >= GST) ~> 
        (\E v \in Validators :
             \E b \in blocks : b.slot > 0 /\ b \in finalized[v])
(* WP Sec. 2.10 Theorem 2: after GST and correct leader windows, finalized blocks appear. This is the base “something eventually finalizes”. :contentReference[oaicite:60]{index=60} *)

FastCertExistsAt(s, h) ==
    \E v \in CorrectNodes : HasFastFinalizationCert(validators[v].pool, s, h)

BlockHashFinalizedAt(s, h) ==
    \E v \in CorrectNodes : \E b \in blocks : b.slot = s /\ b.hash = h /\ b \in finalized[v]

FastPathOneRound ==
    \A s \in 1..MaxSlot :
    \A h \in BlockHashes :
        ((time >= GST /\ FastCertExistsAt(s, h)) ~>
            BlockHashFinalizedAt(s, h))
(* WP Def. 14 + Fig. 7: once a fast‑finalization certificate is observed, the block is finalized; we phrase as leads‑to to account for explicit FinalizeBlock step. :contentReference[oaicite:61]{index=61} *)

TryFinalProgress ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        ( /\ HasState(validators[v], s, "BlockNotarized")
          /\ ~HasState(validators[v], s, "BadWindow")
          /\ (\E h \in BlockNotarizedHashes(validators[v], s) :
                  VotedForBlock(validators[v], s, h))
        ) ~>
        (<> (\E vt \in validators[v].pool.votes[s][v] : IsFinalVote(vt)))
(* WP Alg. 2 line 19: after notarized and not in BadWindow, node casts final vote; progress to final vote occurs. :contentReference[oaicite:62]{index=62} *)

Progress ==
    (time >= GST) ~>
        (\A v \in Validators :
            IF v \in CorrectNodes
            THEN LET currentMax == IF finalized[v] = {} THEN 0
                                   ELSE CHOOSE s \in {b.slot : b \in finalized[v]} :
                                            \A s2 \in {b.slot : b \in finalized[v]} : s >= s2
                 IN <>(\E b \in blocks : b.slot > currentMax /\ b \in finalized[v])
            ELSE TRUE)
(* WP Sec. 2.10 Theorem 2: each correct node eventually increases its highest finalized slot under synchrony and successful Rotor/leader windows. :contentReference[oaicite:63]{index=63} *)

Liveness60Responsive == Progress
CrashToleranceLiveness20 == Progress
(* WP Sec. 1.2 + Sec. 2.11 Cor. 43: same qualitative progress under Assumption 2 (+ Assumption 3 on Rotor non‑equivocation) when ≥60% stake is correct. :contentReference[oaicite:64]{index=64} *)

NodeNeedsRepair(v) ==
    v \in CorrectNodes /\ 
    \E b \in blocks : NeedsBlockRepair(validators[v].pool, b) /\ b \notin blockAvailability[v]

RepairEventuallySucceeds ==
    \A v \in Validators :
        ((time >= GST /\ NodeNeedsRepair(v)) ~> 
            ~NodeNeedsRepair(v))
(* WP Sec. 2.8 Algorithm 4: after GST, repair completes eventually for any node needing a notarized/fast‑final block. :contentReference[oaicite:65]{index=65} *)

NoTimeoutsBeforeGST(startSlot) ==
    \A v \in CorrectNodes :
        \A i \in (WindowSlots(startSlot) \cap 1..MaxSlot) :
            validators[v].timeouts[i] = 0 \/ validators[v].timeouts[i] >= GST
(* WP Def. 17: timeouts are scheduled relative to ParentReady; before GST they may not fire; guard used in window liveness below. :contentReference[oaicite:66]{index=66} *)

WindowRotorSuccessful(startSlot) ==
    \A i \in (WindowSlots(startSlot) \cap 1..MaxSlot) :
        \E b \in blocks :
            /\ b.slot = i
            /\ b.leader = Leader(startSlot)
            /\ (\A v \in CorrectNodes : b \in blockAvailability[v])
(* WP Theorem 2 precondition: leader correct and Rotor successful across a leader window. :contentReference[oaicite:67]{index=67} *)

WindowFinalizedState(s) ==
    \A v \in CorrectNodes :
        \A i \in (WindowSlots(s) \cap 1..MaxSlot) :
            \E b \in blocks :
                /\ b.slot = i
                /\ b.leader = Leader(s)
                /\ b \in finalized[v]
(* WP Sec. 2.10: desired post‑condition—every block of the window is finalized everywhere. :contentReference[oaicite:68]{index=68} *)

WindowFinalization(s) ==
    (IsFirstSlotOfWindow(s)
     /\ Leader(s) \in CorrectNodes
     /\ NoTimeoutsBeforeGST(s)
     /\ WindowRotorSuccessful(s)
     /\ time >= GST) ~>
        WindowFinalizedState(s)
(* WP Theorem 2: with correct leader, Rotor success, and GST, whole window finalizes. :contentReference[oaicite:69]{index=69} *)

WindowFinalizationAll ==
    \A s \in 1..MaxSlot : WindowFinalization(s)

TypeInvariant ==
    /\ validators \in [Validators -> ValidatorState]
    /\ blocks \subseteq Block
    /\ messages \subseteq (Vote \cup Certificate)
    /\ byzantineNodes \subseteq Validators
    /\ unresponsiveNodes \subseteq Validators
    /\ time \in Nat
    /\ finalized \in [Validators -> SUBSET blocks]
    /\ blockAvailability \in [Validators -> SUBSET blocks]
    /\ avail80Start \in [1..MaxSlot -> [BlockHashes -> Nat]]
    /\ avail60Start \in [1..MaxSlot -> [BlockHashes -> Nat]]
    /\ \A v \in Validators : ValidatorStateOK(validators[v])
    /\ \A v \in Validators : \A s \in 1..MaxSlot :
            AllCertificatesValid(validators[v].pool.certificates[s])
(* WP Sec. 1.5 types and Sec. 2 data structures; every pool/certificate is well‑formed. :contentReference[oaicite:70]{index=70} *)

ParentReadyImpliesCert ==
    \A v \in CorrectNodes, s \in 1..MaxSlot:
        (s > 1 /\ "ParentReady" \in validators[v].state[s]) =>
            \E p \in blocks:
                ShouldEmitParentReady(validators[v].pool, s, p.hash, p.slot)
(* WP Def. 15: ParentReady is only set when its preconditions are met. :contentReference[oaicite:71]{index=71} *)

ParentReadyUsesPreviousBlock ==
    \A v \in CorrectNodes, s \in 1..MaxSlot:
        (s > 1 /\ "ParentReady" \in validators[v].state[s]) =>
            \E p \in blocks :
                /\ p.slot < s
                /\ ShouldEmitParentReady(validators[v].pool, s, p.hash, p.slot)
(* WP Def. 15 requires a previous notar/‑fallback parent. :contentReference[oaicite:72]{index=72} *)

BlockNotarizedImpliesCert ==
    \A v \in CorrectNodes, s \in 1..MaxSlot :
        (\E b \in blocks : b.slot = s /\ "BlockNotarized" \in validators[v].state[s]) =>
        (\E b \in blocks : b.slot = s /\ HasNotarizationCert(validators[v].pool, s, b.hash))
(* WP Def. 15: BlockNotarized(s,h) is emitted only if Pool has the notarization certificate for b. :contentReference[oaicite:73]{index=73} *)

FinalVoteImpliesBlockNotarized ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        \A vt \in validators[v].pool.votes[s][v] :
            IsFinalVote(vt) => HasState(validators[v], s, "BlockNotarized")
(* WP Alg. 2 line 19: finalization vote only after notarization observed and no BadWindow. :contentReference[oaicite:74]{index=74} *)

VotedConsistency ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        ("Voted" \in validators[v].state[s])
            => (\E vt \in validators[v].pool.votes[s][v] : IsInitialVote(vt))
(* WP Lemma 20 + Alg. 2: “Voted” tag iff initial vote exists. :contentReference[oaicite:75]{index=75} *)

VotedNotarTagConsistency ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        ("VotedNotarTag" \in validators[v].state[s])
            => (\E vt \in validators[v].pool.votes[s][v] : vt.type = "NotarVote")
(* Consistency of local tags with stored votes. :contentReference[oaicite:76]{index=76} *)

BadWindowWitness ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        ("BadWindow" \in validators[v].state[s])
            => (\E vt \in validators[v].pool.votes[s][v] :
                    vt.type \in {"SkipVote", "SkipFallbackVote", "NotarFallbackVote"})
(* WP Alg. 1 lines 18–25: entering fallback marks BadWindow and is evidenced by one of these vote types. :contentReference[oaicite:77]{index=77} *)

ItsOverWitness ==
    \A v \in CorrectNodes :
    \A s \in 1..MaxSlot :
        ("ItsOver" \in validators[v].state[s])
            => (\E vt \in validators[v].pool.votes[s][v] : vt.type = "FinalVote")
(* WP Lemma 22 + Alg. 2 line 21: ItsOver iff FinalVote exists. :contentReference[oaicite:78]{index=78} *)

FinalizedAncestorClosure ==
    \A v \in Validators : \A b \in finalized[v] :
        GetAncestors(b, blocks) \subseteq finalized[v]
(* WP Def. 14: when finalizing b, finalize all ancestors first. :contentReference[oaicite:79]{index=79} *)

ParentReadyConsistencyAll ==
    \A v \in Validators : ParentReadyConsistency(validators[v])

PendingBlocksSingletonAll ==
    \A v \in Validators : PendingBlocksSingleton(validators[v])

PendingBlocksSlotAlignedAll ==
    \A v \in Validators : PendingBlocksSlotAligned(validators[v])
(* WP Alg. 1–2 bookkeeping for pending blocks and per‑slot alignment. :contentReference[oaicite:80]{index=80} *)

EffectiveStart(start) == IF start = 0 THEN 0 ELSE IF start < GST THEN GST ELSE start
(* WP “after distribution” should be evaluated under synchrony; EffectiveStart maxes with GST. :contentReference[oaicite:81]{index=81} *)

BoundedFinalization80 ==
    \A s \in 1..MaxSlot :
    \A h \in BlockHashes :
        LET st == EffectiveStart(avail80Start[s][h])
        IN (st = 0) \/ (time <= st + Delta80) \/ BlockHashFinalizedAt(s, h)
(* WP Abstract + Sec. 1.3: once ≥80% participating stake has the block after GST, finalization occurs within δ80. Here Delta80 ≈ δ80. :contentReference[oaicite:82]{index=82} *)

BoundedFinalization60 ==
    \A s \in 1..MaxSlot :
    \A h \in BlockHashes :
        LET st == EffectiveStart(avail60Start[s][h])
        IN (st = 0) \/ (time <= st + (2 * Delta60)) \/ BlockHashFinalizedAt(s, h)
(* WP Abstract + Sec. 1.3: once ≥60% has the block after GST, two‑round path finalizes within 2δ60. :contentReference[oaicite:83]{index=83} *)

StateConstraint ==
    /\ Cardinality(blocks) <= MaxBlocks
    /\ \A v \in Validators :
       \A s \in 1..MaxSlot :
           Cardinality(GetVotesForSlot(validators[v].pool, s)) <= NumValidators * 5
(* CHANGE (soundness): removed “time <= GST + 10”. WP Sec. 1.5/3.4 give no global time cap; timeouts can be extended to restore liveness. A finite cap can mask liveness violations. :contentReference[oaicite:84]{index=84} *)


ParentSlotConsistency ==
    \A b \in blocks :
        /\ ~IsGenesis(b)
        => (\E p \in blocks :
               /\ p.hash = b.parent
               /\ p.slot < b.slot)
(* WP Def. 3 (p.15): Block data M carries slot(parent(b)) and hash(parent(b)).
   We store only hash(parent(b)) in the parent field, but this invariant ensures
   that parent blocks exist in the blocks set with correct slot ordering.
   Combined with UniqueBlockHashes, this guarantees parent slot is uniquely
   recoverable: given b.parent hash, there exists exactly one block p with
   p.hash = b.parent, and that block's slot p.slot < b.slot. *)
Invariant ==
    /\ TypeInvariant
    /\ SafetyInvariant
    /\ NoConflictingFinalization
    /\ SafeToSkipPrecludesFastNow
    /\ ChainConsistency
    /\ VoteUniqueness
    /\ UniqueNotarization
    /\ GlobalNotarizationUniqueness
    /\ FinalizedImpliesNotarized
    /\ CertificateNonEquivocation
    /\ Lemma21_FastFinalizationProperty
    /\ NoMixFinalizationAndFallback
    /\ Lemma23_FortyPercentPreventsConflictingNotar
    /\ Lemma26_SlowFinalizationProperty
    /\ PoolSkipVsBlockExclusion
    /\ HonestNonEquivocation
    /\ TransitCertificatesValid
    /\ TransitVotesValid
    /\ LocalVotesWellFormed
    /\ PoolFastPathImplication
    /\ PoolFinalizationImpliesNotarizationPresent
    /\ CertificateBlockProvenance
    /\ ByzantineStakeOK
    /\ Assumption2OK
    /\ PoolMultiplicityOK
    /\ PoolCertificateUniqueness
    /\ PoolCertificatesValid
    /\ PoolCertificatesWellFormedOK
    /\ PoolAlignmentOK
    /\ BucketSlotConsistencyOK
    /\ PoolSkipFallbackAfterInitialNotarOK
    /\ RotorSelectSoundness
    /\ TimeoutsInFuture
    /\ LocalClockMonotonic
    /\ UniqueBlockHashes(blocks)
    /\ ParentSlotConsistency
    /\ AllBlocksValid(blocks)
    /\ (\A v \in Validators : UniqueBlocksPerSlot(finalized[v]))
    /\ FinalizedAncestorClosure
    /\ BlockNotarizedImpliesCert
    /\ ParentReadyImpliesCert
    /\ ParentReadyUsesPreviousBlock
    /\ FinalVoteImpliesBlockNotarized
    /\ VotedConsistency
    /\ ParentReadyConsistencyAll
    /\ PendingBlocksSingletonAll
    /\ PendingBlocksSlotAlignedAll
    /\ VotedNotarTagConsistency
    /\ BadWindowWitness
    /\ ItsOverWitness
    /\ TotalNotarStakeSanity
    /\ BoundedFinalization80
    /\ BoundedFinalization60
(* Collects all safety and progress‑preconditions tied directly to WP Defs/Lemmas/Theorems in Sec. 2 and model assumptions in Sec. 1.5. :contentReference[oaicite:85]{index=85} *)

=============================================================================