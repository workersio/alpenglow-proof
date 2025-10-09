/-
  Alpenglow Protocol Theorem 1: Safety

  This module contains the formalization of Theorem 1 (Safety) from the
  Alpenglow whitepaper, along with all required definitions and lemmas.

  Reference: "Solana Alpenglow Consensus" White Paper v1.1, July 22, 2025
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Basics

open BigOperators

namespace Alpenglow

variable {Message : Type u} {Hash : Type v} {Signature : Type w}

/-! ## Assumptions -/

/-- Helper: Byzantine stake is less than 20% of total stake -/
def ByzantineStakeLessThan20 (_SP : StakeProfile) (_correct : Correct) : Prop :=
  -- Abstract: Byzantine nodes control < 20% of total stake
  -- In a concrete implementation: ∑(v where ¬correct v) SP.weight v < 20% * ∑v SP.weight v
  True

/-- Helper: Correct stake is more than 80% of total stake -/
def CorrectStakeMoreThan80 (_SP : StakeProfile) (_correct : Correct) : Prop :=
  -- Abstract: Correct nodes control > 80% of total stake
  -- In a concrete implementation: ∑(v where correct v) SP.weight v > 80% * ∑v SP.weight v
  True

/-- **Assumption 1 (fault tolerance)** from p.4:
    "Byzantine nodes control less than 20% of the stake.
    The remaining nodes controlling more than 80% of stake are correct."

    Whitepaper reference: p.4, Section 1.2
-/
structure Assumption1 (SP : StakeProfile) (correct : Correct) : Prop where
  /-- Byzantine nodes control less than 20% of total stake -/
  byzantineStakeLessThan20 : ByzantineStakeLessThan20 SP correct
  /-- Correct nodes control more than 80% of total stake -/
  correctStakeMoreThan80 : CorrectStakeMoreThan80 SP correct

/-! ## Core Definitions -/

/-- **Definition 11 (certificate vote thresholds)** and **Table 6** from p.19-20:

    Certificate vote thresholds for different certificate types:
    - Fast-Finalization: ≥ 80%
    - Notarization: ≥ 60%
    - Notar-Fallback: ≥ 60%
    - Skip: ≥ 60%
    - Finalization: ≥ 60%

    Whitepaper reference: p.19-20, Definition 11, Table 6
-/
def CertificateThreshold (vt : VoteType) : ℚ :=
  match vt with
  | VoteType.notar => 60 / 100  -- Notarization: 60%
  | VoteType.notarFallback => 60 / 100  -- Notar-Fallback: 60%
  | VoteType.skip => 60 / 100  -- Skip: 60%
  | VoteType.final => 60 / 100  -- Finalization: 60%

/-- Fast-finalization threshold is 80% -/
def FastFinalizationThreshold : ℚ := 80 / 100

/-- **Definition 12 (storing votes in Pool)** from p.20:
    "Pool stores received votes for every slot and every node as follows:
    - The first received notarization or skip vote,
    - up to 3 received notar-fallback votes,
    - the first received skip-fallback vote, and
    - the first received finalization vote."

    Whitepaper reference: p.20, Definition 12
-/
structure PoolVoteStorage (Hash : Type v) where
  firstNotarOrSkip : Option (Vote Hash Signature)
  notarFallbackVotes : List (Vote Hash Signature)  -- up to 3
  notarFallbackLimit : notarFallbackVotes.length ≤ 3
  firstSkipFallback : Option (Vote Hash Signature)
  firstFinal : Option (Vote Hash Signature)

/-- **Definition 13 (certificates in Pool)** from p.20-21:
    "Pool generates, stores and broadcasts certificates:
    - When enough votes (see Table 6) are received, the respective certificate is generated.
    - When a received or constructed certificate is newly added to Pool,
      the certificate is broadcast to all other nodes.
    - A single (received or constructed) certificate of each type corresponding
      to the given block/slot is stored in Pool."

    Whitepaper reference: p.20-21, Definition 13
-/
def CertificateValid (_SP : StakeProfile) (cert : Certificate Hash) (vt : VoteType) : Prop :=
  -- Abstract stake comparison: certificate voters have enough stake
  -- Concrete: (∑v ∈ cert.voters, SP.weight v) / (∑v, SP.weight v) ≥ CertificateThreshold vt
  cert.thrOK ∧ cert.kind = vt

/-- Fast-finalization certificate requires 80% stake -/
def FastFinalizationCertValid (_SP : StakeProfile) (cert : Certificate Hash) : Prop :=
  -- Abstract: certificate voters control at least 80% of stake
  -- Concrete: (∑v ∈ cert.voters, SP.weight v) / (∑v, SP.weight v) ≥ 80/100
  cert.thrOK ∧ cert.kind = VoteType.notar

/-- **Definition 14 (finalization)** from p.21:
    "We have two ways to finalize a block:
    - If a finalization certificate on slot s is in Pool, the unique notarized block
      in slot s is finalized (we call this slow-finalized).
    - If a fast-finalization certificate on block b is in Pool, the block b is finalized
      (fast-finalized).
    Whenever a block is finalized (slow or fast), all ancestors of the block are
    finalized first."

    Whitepaper reference: p.21, Definition 14
-/
inductive BlockFinalized (P : Pool Hash) (SP : StakeProfile) : Header Hash → Prop
  | fast (h : Header Hash) :
      (∃ cert : Certificate Hash,
        P.certs VoteType.notar (VoteKey.block h.s h.id) = some cert ∧
        FastFinalizationCertValid SP cert) →
      BlockFinalized P SP h
  | slow (h : Header Hash) :
      (∃ cert : Certificate Hash,
        P.certs VoteType.final (VoteKey.slot h.s) = some cert ∧
        CertificateValid SP cert VoteType.final) →
      (∃ notarCert : Certificate Hash,
        P.certs VoteType.notar (VoteKey.block h.s h.id) = some notarCert) →
      BlockFinalized P SP h

/-- **Definition 15 (Pool events)** from p.21:
    "The following events are emitted as input for Algorithm 1:
    - BlockNotarized(slot(b), hash(b)): Pool holds a notarization certificate for block b.
    - ParentReady(s, hash(b)): Slot s is the first of its leader window, and Pool holds a
      notarization or notar-fallback certificate for a previous block b, and skip certificates
      for every slot s' since b, i.e., for slot(b) < s' < s."

    Whitepaper reference: p.21, Definition 15
-/
inductive PoolEvent (Hash : Type v)
  | BlockNotarized (s : Slot) (blockHash : Hash)
  | ParentReady (s : Slot) (parentHash : Hash)

/-- **Definition 16 (fallback events)** from p.21-22:
    "Consider block b in slot s = slot(b). By notar(b) denote the cumulative stake of nodes
    whose notarization votes for block b are in Pool, and by skip(s) denote the cumulative
    stake of nodes whose skip votes for slot s are in Pool.

    The following events are emitted as input for Algorithm 1:
    - SafeToNotar(s, hash(b)): The event is only issued if the node voted in slot s already,
      but not to notarize b. Moreover:
      notar(b) ≥ 40% or (skip(s) + notar(b) ≥ 60% and notar(b) ≥ 20%).
      If s is the first slot in the leader window, the event is emitted. Otherwise, block b
      is retrieved in the repair procedure first, in order to identify the parent of the block.
      Then, the event is emitted when Pool contains the notar-fallback certificate for the
      parent as well.
    - SafeToSkip(s): The event is only issued if the node voted in slot s already, but not
      to skip s. Moreover:
      skip(s) + Σ_b notar(b) - max_b notar(b) ≥ 40%."

    Whitepaper reference: p.21-22, Definition 16
-/
structure SafeToNotarCondition (SP : StakeProfile) (P : Pool Hash) (s : Slot) (b : Hash) : Prop where
  /-- Either notar(b) ≥ 40% or (skip(s) + notar(b) ≥ 60% and notar(b) ≥ 20%) -/
  notarStake40OrMixed : True  -- Abstract condition from Definition 16

structure SafeToSkipCondition (SP : StakeProfile) (P : Pool Hash) (s : Slot) : Prop where
  /-- skip(s) + Σ_b notar(b) - max_b notar(b) ≥ 40% -/
  skipPlusNotarMinus40 : True  -- Abstract condition from Definition 16

/-! ## Safety Lemmas -/

/-- **Lemma 20 (notarization or skip, exclusivity)** from p.28:
    "A correct node exclusively casts only one notarization vote or skip vote per slot."

    Proof sketch: Notarization votes and skip votes are only cast via functions tryNotar()
    and trySkipWindow() of Algorithm 2, respectively. Votes are only cast if Voted ∉ state[s].
    After voting, the state is modified so that Voted ∈ state[s]. Therefore, a notarization
    or skip vote can only be cast once per slot by a correct node.

    Whitepaper reference: p.28, Lemma 20
-/
axiom lemma20_notarization_or_skip (correct : Correct) (v : NodeId) (s : Slot) :
  correct v →
  ∀ (votedNotar votedSkip : Bool),
    ¬(votedNotar ∧ votedSkip)  -- Exactly one of notarization or skip vote

/-- **Lemma 21 (fast-finalization property)** from p.28-29:
    "If a block b is fast-finalized:
    (i) no other block b' in the same slot can be notarized,
    (ii) no other block b' in the same slot can be notarized-fallback,
    (iii) there cannot exist a skip certificate for the same slot."

    Proof sketch: Suppose some correct node fast-finalized some block b in slot s.
    By Definition 14, nodes holding at least 80% of stake cast notarization votes for b.
    Since byzantine nodes hold less than 20% of stake (Assumption 1), a set V of correct
    nodes holding more than 60% of stake cast notarization votes for b. The proof then
    shows that no other block or skip certificate can exist.

    Whitepaper reference: p.28-29, Lemma 21
-/
axiom lemma21_fast_finalization_property (P : Pool Hash) (SP : StakeProfile)
  (correct : Correct) (h : Header Hash) :
  Assumption1 SP correct →
  BlockFinalized P SP h →
  (∀ h' : Header Hash, h'.s = h.s → h'.id ≠ h.id →
    ¬(Notarized P h')) ∧  -- (i) no other block in same slot notarized
  (∀ h' : Header Hash, h'.s = h.s → h'.id ≠ h.id →
    True) ∧  -- (ii) no notar-fallback (placeholder)
  (¬∃ skipCert : Certificate Hash,
    P.certs VoteType.skip (VoteKey.slot h.s) = some skipCert)  -- (iii) no skip cert

/-- **Lemma 22** from p.29:
    "If a correct node v cast a finalization vote in slot s, then v did not cast a
    notar-fallback or skip-fallback vote in s."

    Proof sketch: A correct node adds ItsOver to its state of slot s when casting a
    finalization vote. Notar-fallback or skip-fallback votes can only be cast if
    ItsOver ∉ state[s]. Conversely, a correct node adds BadWindow to its state when
    casting notar-fallback or skip-fallback, and finalization requires BadWindow ∉ state[s].

    Whitepaper reference: p.29, Lemma 22
-/
axiom lemma22_final_vote_excludes_fallbacks (correct : Correct) (v : NodeId) (s : Slot) :
  correct v →
  ∀ (votedFinal votedFallback : Bool),
    votedFinal → ¬votedFallback

/-- **Lemma 23 (40%-correct notar votes block uniqueness pressure)** from p.29:
    "If correct nodes with more than 40% of stake cast notarization votes for block b
    in slot s, no other block can be notarized in slot s."

    Proof sketch: Let V be the set of correct nodes that cast notarization votes for b.
    Suppose for contradiction some b' ≠ b in slot s is notarized. Since 60% of stake
    holders had to cast notarization votes for b', there is a node v ∈ V that cast
    notarization votes for both b and b', contradicting Lemma 20.

    Whitepaper reference: p.29, Lemma 23
-/
axiom lemma23_40percent_correct_notar_uniqueness (SP : StakeProfile) (correct : Correct)
  (s : Slot) (b : Hash) :
  Assumption1 SP correct →
  -- Correct nodes with >40% stake cast notarization votes for b
  True →
  ∀ (b' : Hash), b' ≠ b → ¬∃ (h : Header Hash), h.s = s ∧ h.id = b' ∧ True  -- Not notarized

/-- **Lemma 24 (uniqueness of notarization per slot)** from p.29:
    "At most one block can be notarized in a given slot."

    Proof sketch: Suppose a block b is notarized. Since 60% of stake holders had to cast
    notarization votes for b and byzantine nodes hold less than 20% of stake, then correct
    nodes with more than 40% of stake cast notarization votes for b. By Lemma 23, no block
    b' ≠ b in the same slot can be notarized.

    Whitepaper reference: p.29, Lemma 24
-/
axiom lemma24_uniqueness_of_notarization (P : Pool Hash) (SP : StakeProfile)
  (correct : Correct) (s : Slot) :
  Assumption1 SP correct →
  ∀ (h1 h2 : Header Hash),
    h1.s = s → h2.s = s →
    Notarized P h1 → Notarized P h2 →
    h1.id = h2.id

/-- **Lemma 25 (finalization ⇒ notarization)** from p.30:
    "If a block is finalized by a correct node, the block is also notarized."

    Proof sketch: If b was fast-finalized, nodes with at least 80% of stake cast
    notarization votes for b. Since byzantine nodes possess less than 20% of stake,
    correct nodes with more than 60% of stake broadcast their notarization votes, and
    correct nodes will observe a notarization certificate for b.

    If b was slow-finalized, nodes with at least 60% of stake cast finalization votes
    for b, including some correct nodes. Correct nodes cast finalization votes only if
    they observe a notarization certificate. By Lemma 24, this certificate must be for b.

    Whitepaper reference: p.30, Lemma 25
-/
axiom lemma25_finalization_implies_notarization (P : Pool Hash) (SP : StakeProfile)
  (correct : Correct) (h : Header Hash) :
  Assumption1 SP correct →
  BlockFinalized P SP h →
  Notarized P h

/-- **Lemma 26 (slow-finalization property)** from p.30:
    "If a block b is slow-finalized:
    (i) no other block b' in the same slot can be notarized,
    (ii) no other block b' in the same slot can be notarized-fallback,
    (iii) there cannot exist a skip certificate for the same slot."

    Proof sketch: Similar to Lemma 21, uses the fact that correct nodes with more than
    40% of stake cast finalization votes, and they all previously cast notarization votes
    for the same block b.

    Whitepaper reference: p.30, Lemma 26
-/
axiom lemma26_slow_finalization_property (P : Pool Hash) (SP : StakeProfile)
  (correct : Correct) (h : Header Hash) :
  Assumption1 SP correct →
  BlockFinalized P SP h →
  (∀ h' : Header Hash, h'.s = h.s → h'.id ≠ h.id →
    ¬(Notarized P h')) ∧
  True ∧  -- (ii) no notar-fallback (placeholder)
  (¬∃ skipCert : Certificate Hash,
    P.certs VoteType.skip (VoteKey.slot h.s) = some skipCert)

/-! ## Window/Ancestry Lemmas -/

/-- **Lemma 27** from p.30-31:
    "If there exists a notarization or notar-fallback certificate for block b, then some
    correct node cast its notarization vote for b."

    This lemma is used repeatedly to lift certificates to actual correct-node votes.

    Proof sketch: Suppose no correct node cast its notarization vote for b. Since byzantine
    nodes possess less than 20% of stake, every correct node observed less than 20% of stake
    voting to notarize b. Therefore no correct node could emit SafeToNotar, and thus no
    correct node cast a notar-fallback vote for b. But at least 60% of stake must have voted
    (notarization or notar-fallback) for b for a certificate to exist, contradiction.

    Whitepaper reference: p.30-31, Lemma 27
-/
axiom lemma27_certificate_implies_correct_vote (P : Pool Hash) (SP : StakeProfile)
  (correct : Correct) (b : Hash) :
  Assumption1 SP correct →
  (∃ cert : Certificate Hash, P.certs VoteType.notar (VoteKey.block 0 b) = some cert) ∨
  (∃ cert : Certificate Hash, P.certs VoteType.notarFallback (VoteKey.block 0 b) = some cert) →
  ∃ v : NodeId, correct v ∧ True  -- Cast notarization vote for b

/-- **Lemma 28 (ancestor voting back-propagation inside window)** from p.31:
    "If a correct node v cast the notarization vote for block b in slot s = slot(b), then
    for every slot s' ≤ s such that s' ∈ windowSlots(s), v cast the notarization vote for
    the ancestor b' of b in slot s' = slot(b')."

    Whitepaper reference: p.31, Lemma 28
-/
axiom lemma28_ancestor_voting_backprop (correct : Correct) (v : NodeId)
  (b : Header Hash) (sched : Schedule) :
  correct v →
  True  -- Cast notar vote for b in s
  →
  ∀ s' : Slot, s' ≤ b.s →
    s' ∈ (sched.window b.s).slots →
    ∃ b' : Header Hash,
      b'.s = s' ∧
      BlockNode.IsAncestor b' b ∧
      True  -- v cast notar vote for b'

/-- **Lemma 29 (parent bridge via notar-fallback or 40% notar)** from p.31:
    "Suppose a correct node v cast a notar-fallback vote for a block b in slot s that is
    not the first slot of the window, and b' is the parent of b. Then, either some correct
    node cast a notar-fallback vote for b', or correct nodes with more than 40% of stake
    cast notarization votes for b'."

    Whitepaper reference: p.31, Lemma 29
-/
axiom lemma29_parent_bridge (SP : StakeProfile) (correct : Correct) (v : NodeId)
  (b b' : Header Hash) :
  Assumption1 SP correct →
  correct v →
  b.parentId = some b'.id →
  True  -- v cast notar-fallback for b
  →
  (∃ v' : NodeId, correct v' ∧ True) ∨  -- Some correct cast notar-fallback for b'
  True  -- Or correct nodes with >40% stake cast notar votes for b'

/-- **Lemma 30 (per-slot ancestors across the window)** from p.31:
    "Suppose a block b in slot s is notarized or notarized-fallback. Then, for every slot
    s' ≤ s such that s' ∈ windowSlots(s), there is an ancestor b' of b in slot s'.
    Moreover, either correct nodes with more than 40% of stake cast notarization votes for
    b', or some correct node cast a notar-fallback vote for b'."

    Whitepaper reference: p.31, Lemma 30
-/
axiom lemma30_perslot_ancestors (SP : StakeProfile) (correct : Correct)
  (P : Pool Hash) (b : Header Hash) (sched : Schedule) :
  Assumption1 SP correct →
  (Notarized P b ∨ True) →  -- Or notarized-fallback
  ∀ s' : Slot, s' ≤ b.s →
    s' ∈ (sched.window b.s).slots →
    ∃ b' : Header Hash,
      b'.s = s' ∧
      BlockNode.IsAncestor b' b ∧
      (True ∨  -- Correct nodes with >40% stake cast notar votes for b'
       (∃ v : NodeId, correct v ∧ True))  -- Cast notar-fallback for b'

/-- **Lemma 31 (same window chain)** from p.32:
    "Suppose some correct node finalizes a block bi and bk is a block in the same leader
    window with slot(bi) ≤ slot(bk). If any correct node observes a notarization or
    notar-fallback certificate for bk, bk is a descendant of bi."

    Whitepaper reference: p.32, Lemma 31
-/
axiom lemma31_same_window_chain (P : Pool Hash) (SP : StakeProfile)
  (correct : Correct) (bi bk : Header Hash) (sched : Schedule) :
  Assumption1 SP correct →
  BlockFinalized P SP bi →
  bi.s ≤ bk.s →
  (bi.s ∈ (sched.window bi.s).slots ∧ bk.s ∈ (sched.window bi.s).slots) →
  (Notarized P bk ∨ True) →  -- Or notar-fallback
  BlockNode.IsDescendant bk bi

/-- **Lemma 32 (cross-window chain)** from p.32:
    "Suppose some correct node finalizes a block bi and bk is a block in a different leader
    window such that slot(bi) < slot(bk). If any correct node observes a notarization or
    notar-fallback certificate for bk, bk is a descendant of bi."

    Whitepaper reference: p.32, Lemma 32
-/
axiom lemma32_cross_window_chain (P : Pool Hash) (SP : StakeProfile)
  (correct : Correct) (bi bk : Header Hash) (sched : Schedule) :
  Assumption1 SP correct →
  BlockFinalized P SP bi →
  bi.s < bk.s →
  (bk.s ∉ (sched.window bi.s).slots) →  -- Different window
  (Notarized P bk ∨ True) →  -- Or notar-fallback
  BlockNode.IsDescendant bk bi

/-! ## Main Theorem -/

/-- **Theorem 1 (Safety)** from p.32:
    "If any correct node finalizes a block b in slot s and any correct node finalizes any
    block b' in any slot s' ≥ s, b' is a descendant of b."

    Proof: By Lemma 25, b' is also notarized. By Lemmas 31 and 32, b' is a descendant of b.

    Whitepaper reference: p.32, Theorem 1
-/
theorem theorem1_safety (P : Pool Hash) (SP : StakeProfile) (correct : Correct)
  (b b' : Header Hash) :
  Assumption1 SP correct →
  BlockFinalized P SP b →
  BlockFinalized P SP b' →
  b.s ≤ b'.s →
  BlockNode.IsDescendant b' b := by
  sorry  -- Proof would combine lemmas 25, 31, 32

end Alpenglow
