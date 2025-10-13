/-
  Algorithm 2 (Votor helper functions)
  ====================================

  Ground truth reference: white-paper-origintal.pdf
  - Algorithm 2 (Votor, helper functions): pages 24–25 (Alg. 2 lines 1–30)
  - Definition 17 (timeout schedule): page 23 (formula for Timeout(i))
  - Definition 18 (Votor state markers): page 23 (state[s] flags)

  The whitepaper’s Algorithm 2 collects the local helper routines that every
  validator executes while processing events:

  * `WINDOWSLOTS(s)` enumerates the slots belonging to the leader window
    that contains slot `s` (Alg. 2, line 1; p.24).
  * `SETTIMEOUTS(s)` programs the per-slot timers using the window layout and
    timing parameters `Δ_timeout`, `Δ_block` (Alg. 2, lines 3–5; p.24; Def. 17 p.23).
  * `TRYNOTAR` attempts to cast a notarization vote for the given block.  The
    guard mirrors Alg. 2 lines 8–14 (p.24), while the successful branch also
    delegates to `TRYFINAL` (line 15) and clears the pending-buffer entry.
  * `TRYFINAL` issues a finalization vote once the local state contains the
    notarization certificate for the block and no fallback votes were cast
    in the same slot (Alg. 2, lines 18–21; p.24).
  * `TRYSKIPWINDOW` iterates over the leader window and casts skip votes for
    every slot whose state still lacks the `Voted` flag, marking the window as
    “bad” in the process (Alg. 2, lines 22–27; p.24–25).
  * `CHECKPENDINGBLOCKS` retries notarization for buffered blocks, scanning
    slots in nondecreasing order (Alg. 2, lines 28–30; p.25).

  This file provides a concrete Lean formalization of these routines. We keep
  the implementation deliberately functional: each helper consumes a validator
  state, produces an updated state, and returns a list of broadcast actions
  (votes to be sent on the network). The state and configuration records are
  thin wrappers around the notions introduced in the referenced definitions.
-/

import Basics
import Mathlib.Data.Finset.Basic

open Classical

namespace Alpenglow

universe u v

/-- Slot-level flags stored in `state[s]`.  Each constructor corresponds to one
    of the markers mentioned across Algorithm 2 and Definition 18. -/
inductive SlotTag (Hash : Type _) where
  | parentReady (parent : Hash)
  | voted
  | votedNotar (block : Hash)
  | blockNotarized (block : Hash)
  | itsOver
  | badWindow
  deriving DecidableEq, Repr, Inhabited

/-- Minimal block summary carried through the helper functions.  It mirrors the
    tuple `Block(s, hash, hash_parent)` in Algorithm 2. -/
structure PendingBlock (Hash : Type _) where
  slot   : Slot
  hash   : Hash
  parent : Option Hash
  deriving DecidableEq, Repr

/-- Votes emitted by the helpers. Includes the three kinds used in Algorithm 2
    (Alg. 2 lines 12, 20, 25; p.24) and the fallback kinds driven by Algorithm 1. -/
inductive Broadcast (Hash : Type _) where
  | notar (s : Slot) (hash : Hash)
  | final (s : Slot)
  | skip  (s : Slot)
  | notarFallback (s : Slot) (hash : Hash)
  | skipFallback (s : Slot)
  deriving DecidableEq, Repr

/-- Configuration data required by Algorithm 2:
    * the leader schedule (Definition 18 / Algorithm 2 line 1),
    * timeout parameters Δ_timeout and Δ_block (Definition 17). -/
structure VotorConfig where
  schedule     : Schedule
  deltaTimeout : Nat
  deltaBlock   : Nat

/-- Validator-local state tracking the slot flags, pending blocks, timers, and
    an abstract Pool.  This is the data manipulated by the helper routines. -/
structure VotorState (Hash : Type v) where
  node      : NodeId
  slotState : Slot → Finset (SlotTag Hash)
  pending   : List (PendingBlock Hash)
  pool      : Pool Hash
  clock     : Nat
  timeouts  : Slot → Option Nat

namespace LeaderWindow

/-- First slot of a leader window.  Well-defined because `slots` is nonempty. -/
def firstSlot (w : LeaderWindow) : Slot :=
  match w.slots with
  | []      => 0
  | s :: _  => s

end LeaderWindow

namespace VotorConfig

/-- Slots in the leader window containing `s` (Alg. 2, line 1; p.24). -/
def windowSlots (cfg : VotorConfig) (s : Slot) : List Slot :=
  (cfg.schedule.window s).slots

/-- First slot of the window that contains `s` (used by Alg. 2 line 11; p.24). -/
def windowFirstSlot (cfg : VotorConfig) (s : Slot) : Slot :=
  (cfg.schedule.window s).firstSlot

/-- Boolean predicate indicating whether `s` is the first slot in its window
    (Alg. 2, line 10–11 computes `firstSlot`; p.24). -/
def isFirstSlot (cfg : VotorConfig) (s : Slot) : Bool :=
  decide (cfg.windowFirstSlot s = s)

end VotorConfig

namespace PendingBlock

/-- Remove every entry whose `slot` equals the provided value. -/
def removeSlot {Hash : Type _} (slot : Slot) :
    List (PendingBlock Hash) → List (PendingBlock Hash)
  | [] => []
  | pb :: rest =>
      if pb.slot = slot then
        removeSlot slot rest
      else
        pb :: removeSlot slot rest

/-- Insert `pb` into a list that is already sorted by slot, preserving order. -/
def insertSorted {Hash : Type _} (pb : PendingBlock Hash) :
    List (PendingBlock Hash) → List (PendingBlock Hash)
  | [] => [pb]
  | q :: rest =>
      if pb.slot ≤ q.slot then
        pb :: q :: rest
      else
        q :: insertSorted pb rest

end PendingBlock

namespace VotorState

variable {Hash : Type v} [DecidableEq Hash]

/-- Baseline validator state with empty slot markers, pending buffer, and timers. -/
def init (node : NodeId) (pool : Pool Hash) : VotorState Hash :=
  { node := node
    slotState := fun _ => ∅
    pending := []
    pool := pool
    clock := 0
    timeouts := fun _ => none }

/-- Internal helper to update `slotState[s]`. -/
private def modifySlot (st : VotorState Hash) (slot : Slot)
    (f : Finset (SlotTag Hash) → Finset (SlotTag Hash)) :
    VotorState Hash :=
  { st with slotState := Function.update st.slotState slot (f (st.slotState slot)) }

/-- Internal helper to update the timeout associated with `slot`. -/
private def updateTimeout (st : VotorState Hash) (slot : Slot)
    (value : Option Nat) : VotorState Hash :=
  { st with timeouts := Function.update st.timeouts slot value }

/-- Check whether the given tag is present in `state[slot]`. -/
def hasTag (st : VotorState Hash) (slot : Slot) (tag : SlotTag Hash) : Bool :=
  decide (tag ∈ st.slotState slot)

/-- Insert a slot tag, keeping the remainder of the state unchanged. -/
def addTag (st : VotorState Hash) (slot : Slot) (tag : SlotTag Hash) :
    VotorState Hash :=
  modifySlot st slot (fun s => insert tag s)

/-- Remove pending blocks associated with `slot`. -/
def clearPending (st : VotorState Hash) (slot : Slot) :
    VotorState Hash :=
  { st with pending := PendingBlock.removeSlot slot st.pending }

/-- Record (or replace) the pending block for a slot, keeping the list sorted. -/
def recordPending (st : VotorState Hash) (pb : PendingBlock Hash) :
    VotorState Hash :=
  { st with
      pending :=
        PendingBlock.insertSorted pb
          (PendingBlock.removeSlot pb.slot st.pending) }

/-- Program the timeout for `slot`. Passing `none` clears the timer. -/
def setTimeout (st : VotorState Hash) (slot : Slot) (timestamp : Nat) :
    VotorState Hash :=
  updateTimeout st slot (some timestamp)

/-- Clear the timeout associated with `slot`. -/
def clearTimeout (st : VotorState Hash) (slot : Slot) : VotorState Hash :=
  updateTimeout st slot none

end VotorState

section Helpers

variable {Hash : Type v} [DecidableEq Hash]

/-- Algorithm 2 `TRYFINAL` (lines 18–21; p.24): if
    `BlockNotarized(hash(b)) ∈ state[s]` and `VotedNotar(hash(b)) ∈ state[s]` and
    `BadWindow ∉ state[s]`, then broadcast `FinalVote(s)` and add `ItsOver` to
    `state[s]`. Returns the updated state together with any broadcast. -/
def tryFinal
    (st : VotorState Hash)
    (slot : Slot) (hash : Hash) :
    VotorState Hash × List (Broadcast Hash) :=
  let blockNotarized :=
    st.hasTag slot (SlotTag.blockNotarized hash)
  let votedNotar :=
    st.hasTag slot (SlotTag.votedNotar hash)
  let badWindow :=
    st.hasTag slot SlotTag.badWindow
  if blockNotarized && votedNotar && !badWindow then
    let st1 := st.addTag slot SlotTag.itsOver
    (st1, [Broadcast.final slot])
  else
    (st, [])

/-- Guard of `TRYNOTAR` (Alg. 2 lines 8–14; p.24):
    - if `Voted ∈ state[s]` then return false (handled in `tryNotar` precheck), else
    - compute `firstSlot` boolean; if first slot then require `ParentReady(hash_parent) ∈ state[s]`,
      otherwise require `VotedNotar(hash_parent) ∈ state[s-1]`. -/
private def canNotarize
    (cfg : VotorConfig) (st : VotorState Hash)
    (blk : PendingBlock Hash) : Bool :=
  match blk.parent with
  | none => false
  | some parentHash =>
      if cfg.isFirstSlot blk.slot then
        st.hasTag blk.slot (SlotTag.parentReady parentHash)
      else
        if blk.slot = 0 then
          false
        else
          let previous := blk.slot - 1
          st.hasTag previous (SlotTag.votedNotar parentHash)

/-- Algorithm 2 `TRYNOTAR` (p.24, lines 7–17):
    - lines 8–9: if `Voted ∈ state[s]` then return false (here: `none`).
    - lines 10–11: compute `firstSlot` and test readiness condition.
    - line 12: broadcast `NotarVote(s, hash)`.
    - line 13: add `{Voted, VotedNotar(hash)}` to `state[s]`.
    - line 14: set `pendingBlocks[s] ← ⊥`.
    - line 15: call `tryFinal(s, hash)`.
    - line 16: return true (here: `some ...`). -/
def tryNotar
    (cfg : VotorConfig) (st : VotorState Hash)
    (blk : PendingBlock Hash) :
    Option (VotorState Hash × List (Broadcast Hash)) :=
  if st.hasTag blk.slot SlotTag.voted then
    none
  else if canNotarize cfg st blk then
    match blk.parent with
    | none => none
    | some _ =>
        let st1 := st.addTag blk.slot SlotTag.voted
        let st2 := st1.addTag blk.slot (SlotTag.votedNotar blk.hash)
        let st3 := st2.clearPending blk.slot
        let (st4, finals) := tryFinal st3 blk.slot blk.hash
        some (st4, Broadcast.notar blk.slot blk.hash :: finals)
  else
    none

/-- Algorithm 2 `TRYSKIPWINDOW` (p.24–25, lines 22–27): iterate over `windowSlots(s)`;
    for each `k` with `Voted ∉ state[k]`, broadcast `SkipVote(k)`, add `{Voted,BadWindow}`
    to `state[k]`, and set `pendingBlocks[k] ← ⊥`. Returns the updated state and
    the concatenation of emitted `SkipVote(k)` broadcasts. -/
def trySkipWindow
    (cfg : VotorConfig) (slot : Slot) (st : VotorState Hash) :
    VotorState Hash × List (Broadcast Hash) :=
  (cfg.windowSlots slot).foldl
    (fun acc currentSlot =>
      let (currState, accLogs) := acc
      if currState.hasTag currentSlot SlotTag.voted then
        acc
      else
        let st1 := currState.addTag currentSlot SlotTag.voted
        let st2 := st1.addTag currentSlot SlotTag.badWindow
        let st3 := st2.clearPending currentSlot
        (st3, accLogs ++ [Broadcast.skip currentSlot]))
    (st, [])

/-- Algorithm 2 `SETTIMEOUTS` (p.24, lines 3–5): for `i ∈ windowSlots(s)` schedule
    `Timeout(i)` at `clock() + Δ_timeout + (i − s + 1)·Δ_block`. Here `clock()` is
    `st.clock`, and `Δ_timeout`, `Δ_block` are `cfg.deltaTimeout`, `cfg.deltaBlock`. -/
def setTimeouts
    (cfg : VotorConfig) (first : Slot) (st : VotorState Hash) :
    VotorState Hash :=
  let base := st.clock + cfg.deltaTimeout
  (cfg.windowSlots first).foldl
    (fun acc slot =>
      let offset := slot - first
      let timestamp := base + ((offset + 1) * cfg.deltaBlock)
      acc.setTimeout slot timestamp)
    st

/-- Algorithm 2 `CHECKPENDINGBLOCKS` (p.25, lines 28–30): iterate all `s` with
    `pendingBlocks[s] ≠ ⊥` in nondecreasing `s` and call `tryNotar(pendingBlocks[s])`.
    The state field `pending` is maintained in slot-sorted order. -/
def checkPendingBlocks
    (cfg : VotorConfig) (st : VotorState Hash) :
    VotorState Hash × List (Broadcast Hash) :=
  st.pending.foldl
    (fun acc blk =>
      let (currState, accLogs) := acc
      match tryNotar cfg currState blk with
      | some (nextState, newLogs) =>
          (nextState, accLogs ++ newLogs)
      | none =>
          (currState, accLogs))
    (st, [])

end Helpers

end Alpenglow
