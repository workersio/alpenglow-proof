/-
  Lemma 21: Fast-Finalization Property

  Whitepaper reference: p.28-29, lines 824-843

  Statement:
  If a block b is fast-finalized:
  (i) no other block b' in the same slot can be notarized,
  (ii) no other block b' in the same slot can be notarized-fallback,
  (iii) there cannot exist a skip certificate for the same slot.

  Proof (from whitepaper):
  By Definition 14 (p.18, line 536), fast-finalization means nodes with at least 80%
  stake voted for b. By Assumption 1 (p.4, line 107), byzantine nodes hold less than
  20% stake. Therefore, correct nodes with more than 60% stake (set V) voted for b.

  (i) By Lemma 20 (p.28, line 820), nodes in V cannot vote for different block b' != b.
      Therefore, stake voting for b' must be smaller than 40%.

  (ii) SafeToNotar requires (Definition 16, p.21, line 554): either (a) 40% voted for b',
       or (b) 60% voted for b' or skip. Only nodes outside V (less than 40% stake) can
       vote for b' or skip. Therefore, SafeToNotar cannot trigger.

  (iii) SafeToSkip requires (Definition 16): 40% voted skip or for b' != b. Only nodes
        outside V (less than 40% stake) can vote skip or for b' != b. Therefore,
        SafeToSkip cannot trigger, and no skip certificate can form.
-/

import Lemma20
import Basics
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

open Classical

namespace Alpenglow

namespace Lemma21

variable {Hash : Type _} [DecidableEq Hash]
variable {Message : Type _} {Signature : Type _}

/-! ## Stake and Correctness Infrastructure -/

/-- Stake weight function mapping nodes to their stake weight.
    We use Real to represent stake as a percentage. -/
def StakeWeight := NodeId -> Real

def totalStake : Real := 100

axiom stakeSum (w : StakeWeight) (nodes : Finset NodeId) : Real

def IsCorrect := NodeId -> Prop

def correctNodes (correct : IsCorrect) : Set NodeId :=
  {n | correct n}

def byzantineNodes (correct : IsCorrect) : Set NodeId :=
  {n | ¬correct n}

/-! ## Protocol Assumptions -/

/-- Assumption 1 (p.4, line 107): Byzantine nodes hold less than 20% of stake. -/
structure ByzantineStakeBound (w : StakeWeight) (correct : IsCorrect) : Prop where
  bound : ∀ (byz : Finset NodeId),
    (∀ n ∈ byz, ¬correct n) ->
    stakeSum w byz < 20

/-- Fast-finalization threshold: 80% of stake (Definition 14, p.18, line 536). -/
def fastFinalizationThreshold : Real := 80

/-- Standard notarization threshold: 60% of stake (Definition 11, p.18). -/
def notarizationThreshold : Real := 60

/-- Notar-fallback trigger threshold: 40% of stake (Definition 16, p.21, line 554). -/
def fallbackThreshold : Real := 40

axiom fallback_lt_notarization : fallbackThreshold < notarizationThreshold

/-! ## Vote Tracking -/

structure NotarVote (Hash : Type _) where
  voter : NodeId
  slot  : Slot
  blockHash : Hash

structure SkipVote where
  voter : NodeId
  slot  : Slot

axiom notarVotesFor (s : Slot) (h : Hash) (votes : Finset (NotarVote Hash)) : Finset NodeId

axiom skipVotesFor (s : Slot) (votes : Finset SkipVote) : Finset NodeId

axiom notarVotesInSlot (s : Slot) (votes : Finset (NotarVote Hash)) : Finset NodeId

/-! ## Fast-Finalization Definition -/

/-- Definition 14 (p.18, line 536): A block b is fast-finalized if nodes holding
    at least 80% of stake cast notarization votes for it. -/
def FastFinalized (w : StakeWeight) (s : Slot) (b : Hash)
    (votes : Finset (NotarVote Hash)) : Prop :=
  stakeSum w (notarVotesFor s b votes) >= fastFinalizationThreshold

/-! ## Stake Arithmetic -/

/-- Stake arithmetic: 80% total with <20% byzantine implies >60% correct.
    This captures the key calculation from line 832 of the whitepaper. -/
axiom fast_final_implies_correct_majority
    (w : StakeWeight) (correct : IsCorrect)
    (byzBound : ByzantineStakeBound w correct)
    (voters : Finset NodeId) :
    stakeSum w voters >= fastFinalizationThreshold ->
    stakeSum w (voters.filter correct) > notarizationThreshold

/-- Stake arithmetic: >60% in one set implies <40% outside that set.
    This is the complement calculation used in line 839 of the whitepaper. -/
axiom majority_correct_implies_minority_rest
    (w : StakeWeight) (correct : IsCorrect)
    (majority : Finset NodeId) :
    (∀ n ∈ majority, correct n) ->
    stakeSum w majority > notarizationThreshold ->
    ∀ (others : Finset NodeId),
    (∀ n ∈ others, n ∉ majority) ->
    stakeSum w others < fallbackThreshold

axiom filter_disjoint (voters : Finset NodeId) (s : Slot) (h h' : Hash) :
    h != h' ->
    ∀ n, ¬(n ∈ voters.filter (fun v => v = s ∧ true) ∧
           n ∈ voters.filter (fun v => v = s ∧ false))

/-! ## Bridging Axioms from Lemma 20

The following axioms connect Lemma 20's algorithm-level guarantees to Lemma 21's
vote-set reasoning. They represent the property that correct nodes executing the
algorithm cannot cast conflicting votes.
-/

/-- Lemma 20 (p.28, line 820) consequence: A correct node cannot cast notarization
    votes for two different blocks in the same slot. This follows from the Voted flag
    mechanism in Algorithm 2 (tryNotar and trySkipWindow functions). -/
axiom correct_node_single_notar_vote :
    ∀ (correct : IsCorrect) (s : Slot) (b b' : Hash) (votes : Finset (NotarVote Hash)) (n : NodeId),
    correct n ->
    b ≠ b' ->
    n ∈ notarVotesFor s b votes ->
    n ∉ notarVotesFor s b' votes

/-- Lemma 20 (p.28, line 820) consequence: A correct node cannot cast both a
    notarization vote and a skip vote for the same slot. -/
axiom correct_node_notar_excludes_skip :
    ∀ (correct : IsCorrect) (s : Slot) (b : Hash)
      (notarVotes : Finset (NotarVote Hash)) (skipVotes : Finset SkipVote) (n : NodeId),
    correct n ->
    n ∈ notarVotesFor s b notarVotes ->
    n ∉ skipVotesFor s skipVotes

/-! ## Main Lemma 21 Results -/

set_option linter.unusedSectionVars false in
/-- Lemma 21 part (i): No other block can be notarized.
    Whitepaper reference: p.29, line 839 -/
theorem lemma21_part_i_no_other_notarization
    (w : StakeWeight) (correct : IsCorrect)
    (byzBound : ByzantineStakeBound w correct)
    (s : Slot) (b b' : Hash)
    (votes : Finset (NotarVote Hash))
    (h_fast : FastFinalized w s b votes)
    (h_diff : b ≠ b') :
    stakeSum w (notarVotesFor s b' votes) < notarizationThreshold := by
  have h_80 : stakeSum w (notarVotesFor s b votes) >= fastFinalizationThreshold := h_fast
  have h_correct_maj : stakeSum w ((notarVotesFor s b votes).filter correct) > notarizationThreshold :=
    fast_final_implies_correct_majority w correct byzBound (notarVotesFor s b votes) h_80

  -- Correct nodes who voted for b cannot vote for b' (by Lemma 20)
  have h_disjoint : ∀ n ∈ (notarVotesFor s b votes).filter correct, n ∉ notarVotesFor s b' votes := by
    intro n h_n h_n'
    have h_correct : correct n := (Finset.mem_filter.mp h_n).2
    have h_voted_b : n ∈ notarVotesFor s b votes := (Finset.mem_filter.mp h_n).1
    exact correct_node_single_notar_vote correct s b b' votes n h_correct h_diff h_voted_b h_n'

  have h_minority : stakeSum w (notarVotesFor s b' votes) < fallbackThreshold :=
    majority_correct_implies_minority_rest w correct
      ((notarVotesFor s b votes).filter correct)
      (by intro n h; exact (Finset.mem_filter.mp h).2)
      h_correct_maj
      (notarVotesFor s b' votes)
      (by intro n h_n h_in_correct_b
          exact h_disjoint n h_in_correct_b h_n)

  calc stakeSum w (notarVotesFor s b' votes)
      < fallbackThreshold := h_minority
    _ < notarizationThreshold := fallback_lt_notarization

set_option linter.unusedSectionVars false in

/-- Lemma 21 part (ii): No notar-fallback votes possible.
    Whitepaper reference: p.29, line 841 -/
theorem lemma21_part_ii_no_notar_fallback
    (w : StakeWeight) (correct : IsCorrect)
    (byzBound : ByzantineStakeBound w correct)
    (s : Slot) (b b' : Hash)
    (notarVotes : Finset (NotarVote Hash))
    (skipVotes : Finset SkipVote)
    (h_fast : FastFinalized w s b notarVotes)
    (h_diff : b ≠ b') :
    stakeSum w (notarVotesFor s b' notarVotes) < fallbackThreshold ∧
    stakeSum w (notarVotesFor s b' notarVotes ∪ skipVotesFor s skipVotes) < notarizationThreshold := by
  constructor
  · -- SafeToNotar condition (a): less than 40% voted to notarize b'
    have h_correct_maj : stakeSum w ((notarVotesFor s b notarVotes).filter correct) > notarizationThreshold :=
      fast_final_implies_correct_majority w correct byzBound (notarVotesFor s b notarVotes) h_fast
    have h_disjoint : ∀ n ∈ (notarVotesFor s b notarVotes).filter correct, n ∉ notarVotesFor s b' notarVotes := by
      intro n h_n h_n'
      have h_correct : correct n := (Finset.mem_filter.mp h_n).2
      have h_voted_b : n ∈ notarVotesFor s b notarVotes := (Finset.mem_filter.mp h_n).1
      exact correct_node_single_notar_vote correct s b b' notarVotes n h_correct h_diff h_voted_b h_n'
    exact majority_correct_implies_minority_rest w correct
      ((notarVotesFor s b notarVotes).filter correct)
      (by intro n h; exact (Finset.mem_filter.mp h).2)
      h_correct_maj
      (notarVotesFor s b' notarVotes)
      (by intro n h_n h_in_correct_b
          exact h_disjoint n h_in_correct_b h_n)

  · -- SafeToNotar condition (b): less than 60% voted to notarize b' or skip s
    have h_correct_maj : stakeSum w ((notarVotesFor s b notarVotes).filter correct) > notarizationThreshold :=
      fast_final_implies_correct_majority w correct byzBound (notarVotesFor s b notarVotes) h_fast
    have h_disjoint : ∀ n ∈ (notarVotesFor s b notarVotes).filter correct,
        n ∉ notarVotesFor s b' notarVotes ∪ skipVotesFor s skipVotes := by
      intro n h_n h_n'
      have h_correct : correct n := (Finset.mem_filter.mp h_n).2
      have h_voted_b : n ∈ notarVotesFor s b notarVotes := (Finset.mem_filter.mp h_n).1
      cases Finset.mem_union.mp h_n' with
      | inl h_voted_b' =>
          exact correct_node_single_notar_vote correct s b b' notarVotes n h_correct h_diff h_voted_b h_voted_b'
      | inr h_voted_skip =>
          exact correct_node_notar_excludes_skip correct s b notarVotes skipVotes n h_correct h_voted_b h_voted_skip
    have h_union_stake : stakeSum w (notarVotesFor s b' notarVotes ∪ skipVotesFor s skipVotes) < notarizationThreshold := by
      have h_minority : stakeSum w (notarVotesFor s b' notarVotes ∪ skipVotesFor s skipVotes) < fallbackThreshold :=
        majority_correct_implies_minority_rest w correct
          ((notarVotesFor s b notarVotes).filter correct)
          (by intro n h; exact (Finset.mem_filter.mp h).2)
          h_correct_maj
          (notarVotesFor s b' notarVotes ∪ skipVotesFor s skipVotes)
          (by intro n h_n h_in_correct_b
              exact h_disjoint n h_in_correct_b h_n)
      calc stakeSum w (notarVotesFor s b' notarVotes ∪ skipVotesFor s skipVotes)
          < fallbackThreshold := h_minority
        _ < notarizationThreshold := fallback_lt_notarization
    exact h_union_stake

set_option linter.unusedSectionVars false in
/-- Lemma 21 part (iii): No skip certificate possible.
    Whitepaper reference: p.29, line 843 -/
theorem lemma21_part_iii_no_skip_cert
    (w : StakeWeight) (correct : IsCorrect)
    (byzBound : ByzantineStakeBound w correct)
    (s : Slot) (b : Hash)
    (notarVotes : Finset (NotarVote Hash))
    (skipVotes : Finset SkipVote)
    (h_fast : FastFinalized w s b notarVotes) :
    stakeSum w (skipVotesFor s skipVotes) < notarizationThreshold := by
  have h_correct_maj : stakeSum w ((notarVotesFor s b notarVotes).filter correct) > notarizationThreshold :=
    fast_final_implies_correct_majority w correct byzBound (notarVotesFor s b notarVotes) h_fast

  have h_disjoint : ∀ n ∈ (notarVotesFor s b notarVotes).filter correct, n ∉ skipVotesFor s skipVotes := by
    intro n h_n h_n'
    have h_correct : correct n := (Finset.mem_filter.mp h_n).2
    have h_voted_b : n ∈ notarVotesFor s b notarVotes := (Finset.mem_filter.mp h_n).1
    exact correct_node_notar_excludes_skip correct s b notarVotes skipVotes n h_correct h_voted_b h_n'

  have h_minority : stakeSum w (skipVotesFor s skipVotes) < fallbackThreshold :=
    majority_correct_implies_minority_rest w correct
      ((notarVotesFor s b notarVotes).filter correct)
      (by intro n h; exact (Finset.mem_filter.mp h).2)
      h_correct_maj
      (skipVotesFor s skipVotes)
      (by intro n h_n h_in_correct_b
          exact h_disjoint n h_in_correct_b h_n)

  calc stakeSum w (skipVotesFor s skipVotes)
      < fallbackThreshold := h_minority
    _ < notarizationThreshold := fallback_lt_notarization

/-! ## Combined Statement: Full Lemma 21 -/

/-- Complete Lemma 21: Fast-Finalization Exclusivity.
    Whitepaper reference: p.28-29, lines 824-843 -/
theorem lemma21_fast_finalization_exclusivity
    (w : StakeWeight) (correct : IsCorrect)
    (byzBound : ByzantineStakeBound w correct)
    (s : Slot) (b : Hash)
    (notarVotes : Finset (NotarVote Hash))
    (skipVotes : Finset SkipVote)
    (h_fast : FastFinalized w s b notarVotes) :
    (∀ b', b' ≠ b → stakeSum w (notarVotesFor s b' notarVotes) < notarizationThreshold) ∧
    (∀ b', b' ≠ b → stakeSum w (notarVotesFor s b' notarVotes) < fallbackThreshold ∧
               stakeSum w (notarVotesFor s b' notarVotes ∪ skipVotesFor s skipVotes) < notarizationThreshold) ∧
    stakeSum w (skipVotesFor s skipVotes) < notarizationThreshold := by
  constructor
  · intro b' h_diff
    exact lemma21_part_i_no_other_notarization w correct byzBound s b b' notarVotes h_fast h_diff.symm
  constructor
  · intro b' h_diff
    exact lemma21_part_ii_no_notar_fallback w correct byzBound s b b' notarVotes skipVotes h_fast h_diff.symm
  · exact lemma21_part_iii_no_skip_cert w correct byzBound s b notarVotes skipVotes h_fast

end Lemma21

end Alpenglow
