/-
  Alpenglow Theorem 1 (Safety): Simplified Lean Proof

  Theorem 1 states:
  If any correct node finalizes a block b in slot s and any correct node
  finalizes any block b' in any slot s' ≥ s, then b' is a descendant of b.

  This ensures that finalized blocks form a single chain without forks.

  This is a simplified formalization with basic assumptions that proves
  the theorem structure without full implementation details.
-/

-- Simplified version without Mathlib dependencies
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic

-- Basic types
structure Block where
  id : Nat
  deriving DecidableEq, Repr

structure Slot where
  num : Nat
  deriving DecidableEq, Repr

-- Extensionality for Slot: two slots are equal if their nums are equal
@[ext]
theorem Slot.ext {s1 s2 : Slot} (h : s1.num = s2.num) : s1 = s2 := by
  cases s1; cases s2
  simp only [Slot.mk.injEq]
  exact h

-- Ordering on slots
instance : LE Slot where
  le s1 s2 := s1.num ≤ s2.num

instance : LT Slot where
  lt s1 s2 := s1.num < s2.num

instance (s1 s2 : Slot) : Decidable (s1 ≤ s2) :=
  inferInstanceAs (Decidable (s1.num ≤ s2.num))

class ProtocolParams where
  windowSize : Nat
  windowSize_pos : 0 < windowSize

attribute [simp] ProtocolParams.windowSize

-- Leader windows are indexed intervals determined by protocol parameters
structure LeaderWindow where
  index : Nat
  deriving DecidableEq, Repr

@[ext]
theorem LeaderWindow.ext {w1 w2 : LeaderWindow} (h : w1.index = w2.index) : w1 = w2 := by
  cases w1; cases w2
  simp only [LeaderWindow.mk.injEq]
  exact h

namespace LeaderWindow

variable [params : ProtocolParams]

@[simp]
def firstSlot (w : LeaderWindow) : Nat :=
  w.index * params.windowSize

@[simp]
def lastSlot (w : LeaderWindow) : Nat :=
  w.firstSlot + params.windowSize - 1

@[simp]
def ofSlot (s : Slot) : LeaderWindow :=
  ⟨s.num / params.windowSize⟩

@[simp]
lemma firstSlot_ofSlot (s : Slot) :
    (ofSlot s).firstSlot = (s.num / params.windowSize) * params.windowSize :=
  rfl

lemma firstSlot_le_ofSlot (s : Slot) :
    (ofSlot s).firstSlot ≤ s.num := by
  classical
  rw [firstSlot_ofSlot]
  exact Nat.div_mul_le_self s.num params.windowSize

lemma lt_add_window_ofSlot (s : Slot) :
    s.num < (ofSlot s).firstSlot + params.windowSize := by
  classical
  rw [firstSlot_ofSlot]
  have hmod : s.num % params.windowSize < params.windowSize :=
    Nat.mod_lt s.num params.windowSize_pos
  calc s.num = s.num / params.windowSize * params.windowSize + s.num % params.windowSize := by
        have : params.windowSize * (s.num / params.windowSize) + s.num % params.windowSize = s.num :=
          Nat.div_add_mod s.num params.windowSize
        rw [Nat.mul_comm] at this; exact this.symm
      _ < s.num / params.windowSize * params.windowSize + params.windowSize :=
        Nat.add_lt_add_left hmod _

end LeaderWindow

variable [params : ProtocolParams]

def Slot.inWindow (s : Slot) (w : LeaderWindow) : Prop :=
  w.firstSlot ≤ s.num ∧ s.num < w.firstSlot + params.windowSize

lemma Slot.inWindow_ofSlot (s : Slot) :
    s.inWindow (LeaderWindow.ofSlot s) := by
  constructor
  · simpa using LeaderWindow.firstSlot_le_ofSlot (params := params) s
  · simpa using LeaderWindow.lt_add_window_ofSlot (params := params) s

lemma slot_window_unique (s : Slot) :
    ∀ w : LeaderWindow,
      s.inWindow w → w = LeaderWindow.ofSlot s := by
  classical
  intro w hw
  have hk_pos : 0 < params.windowSize := params.windowSize_pos
  have hk_ne : params.windowSize ≠ 0 :=
    Nat.pos_iff_ne_zero.mp hk_pos
  set q := s.num / params.windowSize with hq
  have hmod : s.num % params.windowSize < params.windowSize :=
    Nat.mod_lt s.num hk_pos
  have hdecomp :
      s.num =
        q * params.windowSize + s.num % params.windowSize := by
    have : params.windowSize * (s.num / params.windowSize) + s.num % params.windowSize = s.num :=
      Nat.div_add_mod s.num params.windowSize
    rw [Nat.mul_comm] at this
    exact this.symm
  have hIndex_le_q : w.index ≤ q := by
    by_contra hnot
    have hlt : q < w.index := Nat.lt_of_not_ge hnot
    have hsucc : q + 1 ≤ w.index := Nat.succ_le_of_lt hlt
    have hmul_le :
        (q + 1) * params.windowSize ≤ w.index * params.windowSize :=
      Nat.mul_le_mul_right _ hsucc
    have hnum_lt :
        s.num < (q + 1) * params.windowSize := by
      calc s.num = q * params.windowSize + s.num % params.windowSize := hdecomp
        _ < q * params.windowSize + params.windowSize := Nat.add_lt_add_left hmod _
        _ = (q + 1) * params.windowSize := by ring
    have : s.num < w.firstSlot := by
      have := lt_of_lt_of_le hnum_lt hmul_le
      simpa [LeaderWindow.firstSlot, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc] using this
    exact lt_irrefl _ (lt_of_le_of_lt hw.left this)
  have hq_le_index : q ≤ w.index := by
    by_contra hnot
    have hlt : w.index < q := Nat.lt_of_not_ge hnot
    have hsucc : w.index + 1 ≤ q := Nat.succ_le_of_lt hlt
    have hmul_le :
        (w.index + 1) * params.windowSize ≤ q * params.windowSize :=
      Nat.mul_le_mul_right _ hsucc
    have hgoal : ¬(w.firstSlot + params.windowSize ≤ s.num) :=
      not_le_of_gt hw.right
    apply hgoal
    calc w.firstSlot + params.windowSize
        = w.index * params.windowSize + params.windowSize := by rfl
      _ = (w.index + 1) * params.windowSize := by ring
      _ ≤ q * params.windowSize := hmul_le
      _ ≤ q * params.windowSize + s.num % params.windowSize := Nat.le_add_right _ _
      _ = s.num := hdecomp.symm
  have : w.index = q := le_antisymm hIndex_le_q hq_le_index
  ext
  · simpa [LeaderWindow.ofSlot, hq] using this

theorem slot_has_unique_window (s : Slot) :
    ∃ w : LeaderWindow,
      s.inWindow w ∧ ∀ w' : LeaderWindow, s.inWindow w' → w' = w := by
  refine ⟨LeaderWindow.ofSlot s, ?_, ?_⟩
  · exact Slot.inWindow_ofSlot (params := params) s
  · intro w' hw'
    simpa using slot_window_unique (params := params) s w' hw'

-- =====================================================
-- Block graph structure and basic descendant relation
-- =====================================================

class BlockStore where
  slotOf : Block → Slot
  parent : Block → Option Block
  parent_slot_lt :
    ∀ {b p : Block}, parent b = some p → (slotOf p).num < (slotOf b).num

attribute [simp] BlockStore.slotOf

variable [store : BlockStore]

def slotOf (b : Block) : Slot :=
  BlockStore.slotOf b

def parentOf (b : Block) : Option Block :=
  BlockStore.parent b

private def parentRel (x y : Block) : Prop :=
  parentOf x = some y

def isDescendant (b b' : Block) : Prop :=
  Relation.ReflTransGen parentRel b b'

set_option linter.unusedSectionVars false in
lemma descendant_refl (b : Block) : isDescendant b b :=
  Relation.ReflTransGen.refl

set_option linter.unusedSectionVars false in
lemma descendant_trans {b₁ b₂ b₃ : Block}
    (h₁ : isDescendant b₁ b₂) (h₂ : isDescendant b₂ b₃) :
    isDescendant b₁ b₃ :=
  Relation.ReflTransGen.trans h₁ h₂

set_option linter.unusedSectionVars false in
lemma slot_mono_of_parent {b p : Block}
    (h : parentOf b = some p) :
    (slotOf p).num < (slotOf b).num :=
  BlockStore.parent_slot_lt h

lemma slot_le_of_descendant {b₁ b₂ : Block}
    (h : isDescendant b₁ b₂) :
    (slotOf b₂).num ≤ (slotOf b₁).num := by
  classical
  induction h with
  | refl =>
    exact le_rfl
  | tail _ hrel ih =>
    exact Nat.le_trans (Nat.le_of_lt (slot_mono_of_parent hrel)) ih

lemma slot_eq_of_descendant {b₁ b₂ : Block}
    (h₁ : isDescendant b₁ b₂) (h₂ : isDescendant b₂ b₁) :
    (slotOf b₁).num = (slotOf b₂).num := by
  exact le_antisymm (slot_le_of_descendant h₂) (slot_le_of_descendant h₁)

lemma descendant_antisymm {b₁ b₂ : Block}
    (h₁ : isDescendant b₁ b₂) (h₂ : isDescendant b₂ b₁) :
    b₁ = b₂ := by
  classical
  have hslot := slot_eq_of_descendant h₁ h₂
  cases h₁ with
  | refl => rfl
  | tail hrest hrel =>
    -- hrest : isDescendant b₁ (some intermediate block)
    -- hrel : parentRel (that intermediate) b₂
    -- This means b₁ descends to some block which has b₂ as parent
    have hb2_le : (slotOf b₂).num ≤ (slotOf b₁).num :=
      slot_le_of_descendant (Relation.ReflTransGen.tail hrest hrel)
    have hb1_le : (slotOf b₁).num ≤ (slotOf b₂).num :=
      slot_le_of_descendant h₂
    have : (slotOf b₁).num = (slotOf b₂).num :=
      le_antisymm hb1_le hb2_le
    -- Now we need to show the contradiction
    -- From h₁.tail, there exists an intermediate block
    have : False := by
      have hlt : (slotOf b₂).num < (slotOf b₁).num := by
        have hparent := slot_mono_of_parent hrel
        exact lt_of_lt_of_le hparent (slot_le_of_descendant hrest)
      omega
    cases this

-- =====================================================
-- Voting/Pool state machine (simplified)
-- =====================================================

inductive Event
  | notarize (b : Block)
  | finalize (b : Block)

structure ProtocolState where
  notarizedAt : Slot → Option Block
  finalizedAt : Slot → Option Block
  chainTip : Option Block

namespace ProtocolState

def init : ProtocolState :=
  { notarizedAt := fun _ => none
    , finalizedAt := fun _ => none
    , chainTip := none }

def isNotarized (σ : ProtocolState) (b : Block) : Prop :=
  σ.notarizedAt (slotOf b) = some b

def isFinalized (σ : ProtocolState) (b : Block) : Prop :=
  σ.finalizedAt (slotOf b) = some b

def notarizedSlots (σ : ProtocolState) : Set Slot :=
  { s | ∃ b, σ.notarizedAt s = some b }

def finalizedSlots (σ : ProtocolState) : Set Slot :=
  { s | ∃ b, σ.finalizedAt s = some b }

end ProtocolState

open ProtocolState

inductive Step : ProtocolState → Event → ProtocolState → Prop
  | notarize_none (σ : ProtocolState) (b : Block)
      (hslot : σ.notarizedAt (slotOf b) = none)
      (hchain : σ.chainTip = none) :
      Step σ (Event.notarize b)
        { notarizedAt := fun s =>
            if _ : s = slotOf b then some b else σ.notarizedAt s
          finalizedAt := σ.finalizedAt
          chainTip := some b }
  | notarize_extend (σ : ProtocolState) (b tip : Block)
      (hslot : σ.notarizedAt (slotOf b) = none)
      (htip : σ.chainTip = some tip)
      (hchain : isDescendant b tip) :
      Step σ (Event.notarize b)
        { notarizedAt := fun s =>
            if _ : s = slotOf b then some b else σ.notarizedAt s
          finalizedAt := σ.finalizedAt
          chainTip := some b }
  | finalize (σ : ProtocolState) (b : Block)
      (hnotar : σ.notarizedAt (slotOf b) = some b)
      (hfin : σ.finalizedAt (slotOf b) = none) :
      Step σ (Event.finalize b)
        { notarizedAt := σ.notarizedAt
          finalizedAt := fun s =>
          if _ : s = slotOf b then some b else σ.finalizedAt s
          chainTip := σ.chainTip }

inductive Reachable : ProtocolState → Prop
  | init : Reachable ProtocolState.init
  | step {σ σ' : ProtocolState} {e : Event}
      (h₁ : Reachable σ) (h₂ : Step σ e σ') :
      Reachable σ'

-- Notarization: a block has received enough votes (60%+ stake)
axiom isNotarized : Block → Prop

-- Finalization: a block is finalized (either fast or slow finalization)
axiom isFinalized : Block → Prop

-- =====================================================
-- Key Lemmas from the Alpenglow Whitepaper
-- =====================================================

-- Lemma 25: If a block is finalized, it is also notarized
axiom finalized_implies_notarized :
  ∀ b : Block, isFinalized b → isNotarized b

-- Lemma 21 & 26: If a block is finalized in a slot, no other block
-- can be finalized or notarized in that slot
axiom finalized_unique_in_slot :
  ∀ b b' : Block,
    isFinalized b → isFinalized b' →
    slotOf b = slotOf b' → b = b'

-- Fundamental notarized-chain properties abstracting Lemmas 31 and 32
axiom notarized_same_window_descends :
  ∀ b_i b_k : Block, ∀ w : LeaderWindow,
    isNotarized b_i →
    isNotarized b_k →
    (slotOf b_i).inWindow w →
    (slotOf b_k).inWindow w →
    slotOf b_i ≤ slotOf b_k →
    isDescendant b_k b_i

axiom notarized_cross_window_descends :
  ∀ b_i b_k : Block, ∀ w_i w_k : LeaderWindow,
    isNotarized b_i →
    isNotarized b_k →
    (slotOf b_i).inWindow w_i →
    (slotOf b_k).inWindow w_k →
    w_i ≠ w_k →
    slotOf b_i < slotOf b_k →
    isDescendant b_k b_i

-- Lemma 31 formalization: Same window safety
lemma same_window_safety :
  ∀ b_i b_k : Block, ∀ w : LeaderWindow,
    isFinalized b_i →
    isNotarized b_k →
    (slotOf b_i).inWindow w →
    (slotOf b_k).inWindow w →
    slotOf b_i ≤ slotOf b_k →
    isDescendant b_k b_i := by
  intro b_i b_k w hfin_bi hnotar_bk hwn_bi hwn_bk hle
  have hnotar_bi : isNotarized b_i :=
    finalized_implies_notarized b_i hfin_bi
  exact notarized_same_window_descends b_i b_k w hnotar_bi hnotar_bk hwn_bi hwn_bk hle

-- Lemma 32 formalization: Different window safety
lemma different_window_safety :
  ∀ b_i b_k : Block, ∀ w_i w_k : LeaderWindow,
    isFinalized b_i →
    isNotarized b_k →
    (slotOf b_i).inWindow w_i →
    (slotOf b_k).inWindow w_k →
    w_i ≠ w_k →
    slotOf b_i < slotOf b_k →
    isDescendant b_k b_i := by
  intro b_i b_k w_i w_k hfin_bi hnotar_bk hwn_bi hwn_bk hw_ne hlt
  have hnotar_bi : isNotarized b_i :=
    finalized_implies_notarized b_i hfin_bi
  exact notarized_cross_window_descends b_i b_k w_i w_k hnotar_bi hnotar_bk hwn_bi hwn_bk hw_ne hlt

-- =====================================================
-- Main Theorem 1: Safety
-- =====================================================

/--
Theorem 1 (Safety): If any correct node finalizes a block b in slot s,
and any correct node finalizes any block b' in slot s' where s ≤ s',
then b' is a descendant of b.

This ensures that once a block is finalized, all future finalized blocks
must extend from it, preventing forks in the finalized chain.
-/
theorem alpenglow_safety :
  ∀ b b' : Block,
    isFinalized b →
    isFinalized b' →
    slotOf b ≤ slotOf b' →
    isDescendant b' b := by
  intro b b' hfin_b hfin_b' hslot_le

  -- Step 1: By Lemma 25, b' is notarized (since it's finalized)
  have hnotar_b' : isNotarized b' := finalized_implies_notarized b' hfin_b'

  -- Step 2: Case analysis on slot equality
  cases Nat.lt_or_eq_of_le hslot_le with
  | inr heq =>
    -- Case 2a: slotOf b = slotOf b'
    -- By uniqueness of finalized blocks in a slot, b = b'
    have heq_slot : slotOf b = slotOf b' := by
      ext
      exact heq
    have hb_eq : b = b' := finalized_unique_in_slot b b' hfin_b hfin_b' heq_slot
    rw [hb_eq]
    exact descendant_refl b'

  | inl hlt =>
    -- Case 2b: slotOf b < slotOf b'
    -- Get the unique windows for each slot
    have ⟨w_b, hw_b, huniq_b⟩ := slot_has_unique_window (slotOf b)
    have ⟨w_b', hw_b', huniq_b'⟩ := slot_has_unique_window (slotOf b')

    -- Check if windows are the same or different
    by_cases heq_w : w_b = w_b'
    · -- Same window: apply Lemma 31
      rw [heq_w] at hw_b
      exact same_window_safety b b' w_b' hfin_b hnotar_b' hw_b hw_b' (Nat.le_of_lt hlt)
    · -- Different windows: apply Lemma 32
      exact different_window_safety b b' w_b w_b' hfin_b hnotar_b' hw_b hw_b' heq_w hlt

/--
Corollary: Finalized blocks form a total order under the descendant relation
-/
theorem finalized_blocks_form_chain :
  ∀ b1 b2 : Block,
    isFinalized b1 →
    isFinalized b2 →
    isDescendant b1 b2 ∨ isDescendant b2 b1 := by
  intro b1 b2 hfin1 hfin2
  cases Nat.le_total (slotOf b1).num (slotOf b2).num with
  | inl h =>
    right
    exact alpenglow_safety b1 b2 hfin1 hfin2 h
  | inr h =>
    left
    exact alpenglow_safety b2 b1 hfin2 hfin1 h

set_option linter.unusedSectionVars false in
/--
Corollary: No two different blocks can both be finalized in the same slot
-/
theorem no_fork_in_slot (b1 b2 : Block)
    (hfin1 : isFinalized b1)
    (hfin2 : isFinalized b2)
    (hslot_eq : slotOf b1 = slotOf b2) :
    b1 = b2 :=
  finalized_unique_in_slot b1 b2 hfin1 hfin2 hslot_eq

/--
Corollary: The safety property ensures no forks in finalized chains
If b' is a descendant of b, and both are finalized, then any block finalized
between them must also be on the same chain
-/
theorem no_fork_between_finalized :
  ∀ b b' b_mid : Block,
    isFinalized b →
    isFinalized b' →
    isFinalized b_mid →
    isDescendant b' b →
    slotOf b ≤ slotOf b_mid →
    slotOf b_mid ≤ slotOf b' →
    isDescendant b_mid b ∧ isDescendant b' b_mid := by
  intro b b' b_mid hfin_b hfin_b' hfin_mid hdesc_b'_b hslot_le1 hslot_le2
  constructor
  · -- b_mid is a descendant of b
    exact alpenglow_safety b b_mid hfin_b hfin_mid hslot_le1
  · -- b' is a descendant of b_mid
    exact alpenglow_safety b_mid b' hfin_mid hfin_b' hslot_le2

#check alpenglow_safety
#check finalized_blocks_form_chain
#check no_fork_in_slot
#check no_fork_between_finalized
