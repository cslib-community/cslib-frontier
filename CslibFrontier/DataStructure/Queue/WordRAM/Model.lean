/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Queue.Spec
public import CslibFrontier.Computability.WordRAM.Defs

/-!
# The FIFO meaning of a two-stack representation

The front stack lists the oldest values first; the rear stack lists the newest values first.
Thus the represented FIFO sequence is `front ++ rear.reverse`. Enqueue pushes onto the rear.
Dequeue pops the front when possible; otherwise it reverses the entire rear into the front
before popping. Reversal is only a mathematical description here: the machine implementation
executes a charged loop, moving one value at a time.

## Main definitions

* `spec`: the existing FIFO specification restricted to fitting words and a fixed capacity.
* `Stacks`, `Stacks.contents`: logical two-stack state (`front` and `rear`) and the FIFO sequence it
  represents.
* `pairStep`: the corresponding transition of the two stacks.

## Main results

* `pairStep_correct`: both the returned answer and the new FIFO sequence match `spec`.
* `pairStep_length_le`: admissible calls preserve the shared capacity bound.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Exercise 10.1-6][CLRS2009].
-/

@[expose] public section

namespace Cslib.DataStructure.Queue.WordRAM

open Cslib.WordRAM Cslib.DataStructure.Queue

/-- A queue admits an enqueue exactly when it has spare capacity and the value fits a word. -/
abbrev spec (w capacity : ℕ) : DataStructure.StateTransitionSpec :=
  DataStructure.StateTransitionSpec.ofFn (queue ℕ).stepFn fun q o => match o with
    | .enqueue v => q.length < capacity ∧ Fits w v
    | .dequeue => True

/-- Logical two-stack state of a FIFO queue: `front` stores the oldest elements in FIFO order and
`rear` stores newly enqueued elements in reverse FIFO order. -/
structure Stacks where
  /-- Oldest elements in FIFO order, popped first by `dequeue`. -/
  front : List ℕ
  /-- Newest elements in reverse FIFO order, reversed into `front` when `front` is empty. -/
  rear : List ℕ
  deriving DecidableEq, Repr

/-- Front is in FIFO order; rear is in reverse FIFO order. -/
def Stacks.contents (s : Stacks) : List ℕ := s.front ++ s.rear.reverse

/-- Mathematical description of the machine's two-stack transition, including an empty pop. -/
def pairStep (s : Stacks) (o : QueueOp ℕ) :
    Stacks × (queue ℕ).Result o :=
  match o with
  | .enqueue v => (⟨s.front, v :: s.rear⟩, ())
  | .dequeue => match s.front with
    | [] => (⟨s.rear.reverse.tail, []⟩, s.rear.reverse.head?)
    | a :: front => (⟨front, s.rear⟩, some a)

/-- Projecting the concrete stack transition gives exactly the specified FIFO step. -/
theorem pairStep_correct (s : Stacks) (o : QueueOp ℕ) :
    ((pairStep s o).1.contents, (pairStep s o).2) = (queue ℕ).stepFn s.contents o := by
  obtain ⟨front, rear⟩ := s
  cases o with
  | enqueue v => simp [pairStep, Stacks.contents, queue, List.reverse_cons, List.append_assoc]
  | dequeue => cases front <;> simp [pairStep, Stacks.contents, queue]

/-- The sum of live stack lengths is the FIFO length, not the size of the reserved regions. -/
theorem Stacks.contents_length (s : Stacks) :
    s.contents.length = s.front.length + s.rear.length := by
  simp [Stacks.contents]

/-- Enqueues require one spare slot; dequeues cannot increase the number of live values. -/
theorem pairStep_length_le {w capacity : ℕ} {s : Stacks}
    (hs : s.contents.length ≤ capacity) (o : QueueOp ℕ)
    (hv : (spec w capacity).valid s.contents o) :
    (pairStep s o).1.contents.length ≤ capacity := by
  have hc := congrArg (fun p => p.1.length) (pairStep_correct s o)
  rw [hc]
  cases o with
  | enqueue v =>
    change (s.contents ++ [v]).length ≤ capacity
    simp only [List.length_append, List.length_singleton]
    exact Nat.succ_le_of_lt hv.1
  | dequeue =>
    change s.contents.tail.length ≤ capacity
    simp only [List.length_tail]
    omega

end Cslib.DataStructure.Queue.WordRAM
