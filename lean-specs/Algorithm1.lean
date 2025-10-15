/-
  Algorithm 1 (Votor event loop)
  ==============================

  Ground truth reference: white-paper-origintal.pdf
  - Algorithm 1 (Votor, event loop, single-threaded): page 24, lines 1–25
  - Definition 18 (Votor state): page 23
  - Definition 15 (Pool events): page 21
  - Definition 16 (fallback events): pages 21–22

  The whitepaper's Algorithm 1 describes the main event-driven control loop
  for the Votor voting protocol. Each validator node reacts to a sequence of
  events:

  * Block(s, hash, hash_parent) — Blokstor has received a complete block.
  * Timeout(s) — The local timeout for slot s has expired.
  * BlockNotarized(s, hash(b)) — Pool has generated a notarization certificate.
  * ParentReady(s, hash(b)) — The parent block is ready for the leader window
    starting at s.
  * SafeToNotar(s, hash(b)) — It is safe to cast a notar-fallback vote.
  * SafeToSkip(s) — It is safe to cast a skip-fallback vote.

  This file provides a concrete Lean formalization of Algorithm 1's event
  handlers. The implementation is functional: each handler consumes the
  current validator state, produces an updated state, and returns a list of
  broadcast actions (votes to be sent on the network).

  The event handlers delegate to helper functions defined in Algorithm2.lean
  (TRYNOTAR, CHECKPENDINGBLOCKS, TRYSKIPWINDOW, TRYFINAL, SETTIMEOUTS).
-/

import Basics
import Algorithm2
import Mathlib.Data.Finset.Basic

open Classical

namespace Alpenglow

universe u v

/-! ## Event types -/

/- Events that drive Algorithm 1.  These correspond to the `upon` handlers
    in the whitepaper pseudocode. -/
inductive VotorEvent (Hash : Type _) where
  | block          (s : Slot) (hash : Hash) (hashParent : Option Hash)
  | timeout        (s : Slot)
  | blockNotarized (s : Slot) (hash : Hash)
  | parentReady    (s : Slot) (hash : Hash)
  | safeToNotar    (s : Slot) (hash : Hash)
  | safeToSkip     (s : Slot)
  deriving DecidableEq, Repr

/-! ## Algorithm 1 event handlers -/

section EventHandlers

variable {Hash : Type v} [DecidableEq Hash]

/- Algorithm 1 (white-paper-origintal.pdf:24, lines 1–5): upon Block(s, hash, hash_parent)

    When a block is received:
    1. Try to notarize it immediately
    2. If successful, check pending blocks
    3. Otherwise, if we haven't voted yet, buffer it for later -/
def handleBlock
    (cfg : VotorConfig) (st : VotorState Hash)
    (s : Slot) (hash : Hash) (hashParent : Option Hash) :
    VotorState Hash × List (Broadcast Hash) :=
  let blk : PendingBlock Hash := {
    slot := s
    hash := hash
    parent := hashParent
  }
  match tryNotar cfg st blk with
  | some (st1, broadcasts) =>
      -- Successfully notarized, check pending blocks (line 3)
      let (st2, moreBroadcasts) := checkPendingBlocks cfg st1
      (st2, broadcasts ++ moreBroadcasts)
  | none =>
      -- Could not notarize yet
      if st.hasTag s SlotTag.voted then
        -- Already voted, don't buffer (line 4 condition fails)
        (st, [])
      else
        -- Buffer for later (line 5)
        (st.recordPending blk, [])

/- Algorithm 1 (white-paper-origintal.pdf:24, lines 6–8): upon Timeout(s)

    When a timeout expires for slot s:
    - If we haven't voted yet, skip the entire leader window -/
def handleTimeout
    (cfg : VotorConfig) (st : VotorState Hash)
    (s : Slot) :
    VotorState Hash × List (Broadcast Hash) :=
  if st.hasTag s SlotTag.voted then
    -- Already voted, nothing to do (line 7 condition fails)
    (st, [])
  else
    -- Skip the window (line 8)
    trySkipWindow cfg s st

/- Algorithm 1 (white-paper-origintal.pdf:24, lines 9–11): upon BlockNotarized(s, hash(b))

    When Pool emits a notarization certificate:
    1. Record the notarization in state
    2. Try to cast a finalization vote -/
def handleBlockNotarized
    (st : VotorState Hash)
    (s : Slot) (hash : Hash) :
    VotorState Hash × List (Broadcast Hash) :=
  -- Line 10: add BlockNotarized to state
  let st1 := st.addTag s (SlotTag.blockNotarized hash)
  -- Line 11: try to finalize
  tryFinal st1 s hash

/- Algorithm 1 (white-paper-origintal.pdf:24, lines 12–15): upon ParentReady(s, hash(b))

    When the parent block is ready for a leader window:
    1. Record ParentReady in state
    2. Check pending blocks
    3. Set timeouts for the entire window -/
def handleParentReady
    (cfg : VotorConfig) (st : VotorState Hash)
    (s : Slot) (hash : Hash) :
    VotorState Hash × List (Broadcast Hash) :=
  -- Line 13: add ParentReady to state
  let st1 := st.addTag s (SlotTag.parentReady hash)
  -- Line 14: check pending blocks
  let (st2, broadcasts) := checkPendingBlocks cfg st1
  -- Line 15: set timeouts for the window
  let st3 := setTimeouts cfg s st2
  (st3, broadcasts)

/- Algorithm 1 (white-paper-origintal.pdf:24, lines 16–20): upon SafeToNotar(s, hash(b))

    When it's safe to cast a notar-fallback vote:
    1. Skip the window
    2. If we haven't finalized yet, cast notar-fallback vote and mark BadWindow -/
def handleSafeToNotar
    (cfg : VotorConfig) (st : VotorState Hash)
    (s : Slot) (hash : Hash) :
    VotorState Hash × List (Broadcast Hash) :=
  -- Line 17: skip the window
  let (st1, skipBroadcasts) := trySkipWindow cfg s st
  -- Lines 18-20: if not finalized, cast notar-fallback
  if st1.hasTag s SlotTag.itsOver then
    (st1, skipBroadcasts)
  else
    -- Line 19: broadcast notar-fallback vote
    let broadcasts := skipBroadcasts ++ [Broadcast.notarFallback s hash]
    -- Line 20: add BadWindow to state[s]
    let st2 := st1.addTag s SlotTag.badWindow
    (st2, broadcasts)

/- Algorithm 1 (white-paper-origintal.pdf:24, lines 21–25): upon SafeToSkip(s)

    When it's safe to cast a skip-fallback vote:
    1. Skip the window
    2. If we haven't finalized yet, cast skip-fallback vote and mark BadWindow -/
def handleSafeToSkip
    (cfg : VotorConfig) (st : VotorState Hash)
    (s : Slot) :
    VotorState Hash × List (Broadcast Hash) :=
  -- Line 22: skip the window
  let (st1, skipBroadcasts) := trySkipWindow cfg s st
  -- Lines 23-25: if not finalized, cast skip-fallback
  if st1.hasTag s SlotTag.itsOver then
    (st1, skipBroadcasts)
  else
    -- Line 24: broadcast skip-fallback vote
    let broadcasts := skipBroadcasts ++ [Broadcast.skipFallback s]
    -- Line 25: add BadWindow to state[s]
    let st2 := st1.addTag s SlotTag.badWindow
    (st2, broadcasts)

/- Main event handler that dispatches to the appropriate handler based on
    the event type. -/
def handleEvent
    (cfg : VotorConfig) (st : VotorState Hash)
    (evt : VotorEvent Hash) :
    VotorState Hash × List (Broadcast Hash) :=
  match evt with
  | VotorEvent.block s hash hashParent =>
      handleBlock cfg st s hash hashParent
  | VotorEvent.timeout s =>
      handleTimeout cfg st s
  | VotorEvent.blockNotarized s hash =>
      handleBlockNotarized st s hash
  | VotorEvent.parentReady s hash =>
      handleParentReady cfg st s hash
  | VotorEvent.safeToNotar s hash =>
      handleSafeToNotar cfg st s hash
  | VotorEvent.safeToSkip s =>
      handleSafeToSkip cfg st s

/- Process a sequence of events, accumulating state changes and broadcasts. -/
def processEvents
    (cfg : VotorConfig) (st : VotorState Hash)
    (events : List (VotorEvent Hash)) :
    VotorState Hash × List (Broadcast Hash) :=
  events.foldl
    (fun (currState, accBroadcasts) evt =>
      let (nextState, newBroadcasts) := handleEvent cfg currState evt
      (nextState, accBroadcasts ++ newBroadcasts))
    (st, [])

end EventHandlers

/-! ## Correctness properties (to be proven) -/

section Properties

variable {Hash : Type v} [DecidableEq Hash]

/- A node votes at most once per slot (notarization or skip). -/
def votesOncePerSlot (st : VotorState Hash) : Prop :=
  ∀ s, st.hasTag s SlotTag.voted →
    (∃! hash, st.hasTag s (SlotTag.votedNotar hash)) ∨
    (∀ hash, ¬st.hasTag s (SlotTag.votedNotar hash))

/- If BadWindow is set, the node has cast a fallback vote. -/
def badWindowImpliesFallback (st : VotorState Hash) : Prop :=
  ∀ s, st.hasTag s SlotTag.badWindow →
    st.hasTag s SlotTag.voted

/- If ItsOver is set, the node has voted to notarize. -/
def finalizedImpliesNotarized (st : VotorState Hash) : Prop :=
  ∀ s, st.hasTag s SlotTag.itsOver →
    ∃ hash, st.hasTag s (SlotTag.votedNotar hash)

/- The validator state satisfies basic invariants. -/
def stateInvariant (st : VotorState Hash) : Prop :=
  votesOncePerSlot st ∧
  badWindowImpliesFallback st ∧
  finalizedImpliesNotarized st

end Properties

end Alpenglow
