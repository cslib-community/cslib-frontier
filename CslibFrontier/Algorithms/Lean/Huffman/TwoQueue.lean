/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Huffman.Optimality
import Mathlib.Data.List.Sort

/-!
# Two-Queue Huffman Construction

When input symbols are already sorted in nondecreasing order of nonnegative weight, van Leeuwen
([VanLeeuwen1976]) observed that Huffman's algorithm does not need a general priority queue:
maintaining a list `q₁` of unmerged leaves alongside a single FIFO queue `q₂` of merged internal
nodes keeps `q₂` automatically sorted, because consecutive merged pair sums `w(t₁) + w(t₂)` are
monotone nondecreasing under nonnegative weights.

This module provides the pure mathematical construction and optimality theorems; machine-level
Word-RAM running-time bounds (`O(n)` from pre-sorted weights and `O(n log n)` from unsorted weights)
are proved in `CslibFrontier.Algorithms.WordRAM.Huffman`:

1. **Two-list functional FIFO queue (`FifoQueue γ`)** ([CLRS2009], Exercise 10.1-6): `peek?`
   inspects `front.head?` directly under the canonical invariant `front = [] → back = []`, and
   `enqueue` / `dequeue?` satisfy explicit potential-method list-reversal bounds
   (`enqueue_revCost_bound`, `dequeue?_revCost_bound`). Unlike `Std.Queue` (`Init.Data.Queue`,
   which does not maintain `dList = [] → eList = []`, so inspecting the head without committing a
   dequeue would repeatedly reverse `eList`) and `Cslib.DataStructure.Queue` (an abstract
   `Cslib.DataStructure` two-stack module without `peek?`), `FifoQueue` inspects the head directly
   when `popMin` compares the heads of `q₁` and `q₂` and pops `q₁` while leaving `q₂` unchanged.
2. **Cached-weight trees (`WeightedTree α β`)**: each queue entry caches `wt = tree.weight w`, so
   each merge computes `a.wt + b.wt` without re-traversing subtrees.
3. **Van Leeuwen two-queue construction (`huffmanFromSorted`)**: fuel-free step equation
   `twoQueueLoop_step`, queue-list specification `popMin_spec_toList`, and correctness on sorted
   nonnegative inputs (`huffmanFromSorted_spec`).
4. **End-to-end unsorted Huffman construction (`huffman`)**: sorts `syms` with `List.mergeSort` and
   runs `huffmanFromSorted`, producing a tree certified by `IsHuffmanBuild` (hence optimal over all
   `CodeTree`s, all injective `IsPrefixFree` binary codes, and all injective `IsUniquelyDecodable`
   binary codes).

## Main definitions

* `Cslib.Algorithms.Lean.Huffman.FifoQueue`: two-list functional FIFO queue.
* `Cslib.Algorithms.Lean.Huffman.WeightedTree`: `CodeTree α` paired with its cached weight `β`.
* `Cslib.Algorithms.Lean.Huffman.popMin`, `twoQueueLoop`: single minimum-extraction step and main
  merge loop of van Leeuwen's two-queue construction.
* `Cslib.Algorithms.Lean.Huffman.huffmanFromSorted`: two-queue Huffman construction from sorted
  symbols.
* `Cslib.Algorithms.Lean.Huffman.huffman`: Huffman construction from arbitrary symbols via
  `List.mergeSort`.

## Main results

* `Cslib.Algorithms.Lean.Huffman.FifoQueue.enqueue_revCost_bound`,
  `Cslib.Algorithms.Lean.Huffman.FifoQueue.dequeue?_revCost_bound`: potential-method list-reversal
  bounds for `FifoQueue`.
* `Cslib.Algorithms.Lean.Huffman.popMin_spec_toList`, `twoQueueLoop_step`: representation-free
  step specifications for `popMin` and `twoQueueLoop`.
* `Cslib.Algorithms.Lean.Huffman.huffmanFromSorted_spec`: correctness (`IsHuffmanBuild` and leaf
  permutation) on any nonempty sorted symbol list with nonnegative weights.
* `Cslib.Algorithms.Lean.Huffman.huffman_spec`, `huffman_optimal`,
  `huffman_optimal_isPrefixFree`, `huffman_optimal_isUniquelyDecodable`: end-to-end correctness and
  optimality of `huffman`.

## References

* [VanLeeuwen1976] Jan van Leeuwen, *On the Construction of Huffman Trees*, ICALP 1976, pp. 382–410.
* [Huffman1952] David A. Huffman, *A Method for the Construction of Minimum-Redundancy Codes*, 1952.
* [CLRS2009] Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest, and Clifford Stein,
  *Introduction to Algorithms* (3rd ed.), Exercise 10.1-6 and Section 16.3, 2009.
-/

public section

namespace Cslib.Algorithms.Lean.Huffman

/-! ## Two-list functional FIFO queue -/

/-- Two-list functional FIFO queue representing `front ++ back.reverse`. -/
structure FifoQueue (γ : Type*) where
  /-- Dequeue-ready prefix in FIFO order. -/
  front : List γ
  /-- Recently enqueued suffix in reverse FIFO order. -/
  back : List γ
  deriving DecidableEq, Repr

universe u

namespace FifoQueue

variable {γ : Type*}

/-- Empty FIFO queue. -/
@[expose] def empty : FifoQueue γ := ⟨[], []⟩

/-- Abstract FIFO sequence represented by `q`. -/
@[expose] def toList (q : FifoQueue γ) : List γ := q.front ++ q.back.reverse

/-- Number of elements stored in `q`. -/
@[expose] def size (q : FifoQueue γ) : ℕ := q.front.length + q.back.length

/-- Canonical two-list invariant: `front` is empty only when `back` is also empty. -/
def WF (q : FifoQueue γ) : Prop := q.front = [] → q.back = []

/-- Smart constructor restoring `WF` by reversing `back` when `front` becomes empty. -/
def checkf : List γ → List γ → FifoQueue γ
  | [], b => ⟨b.reverse, []⟩
  | f, b => ⟨f, b⟩

/-- Number of list-reversal steps performed by `checkf f b`. -/
def checkfRevCost : List γ → List γ → ℕ
  | [], b => b.length
  | _ :: _, _ => 0

/-- Enqueue `x` at the back of `q`. -/
def enqueue (q : FifoQueue γ) (x : γ) : FifoQueue γ :=
  checkf q.front (x :: q.back)

/-- Peek at the front element of `q` by inspecting `front.head?`. -/
def peek? (q : FifoQueue γ) : Option γ :=
  q.front.head?

/-- Dequeue the front element of `q` if non-empty. -/
def dequeue? (q : FifoQueue γ) : Option (γ × FifoQueue γ) :=
  match q.front with
  | [] => none
  | x :: f => some (x, checkf f q.back)

@[simp] theorem toList_empty : (empty : FifoQueue γ).toList = [] := rfl

@[simp] theorem size_empty : (empty : FifoQueue γ).size = 0 := rfl

theorem wf_empty : (empty : FifoQueue γ).WF := fun _ => rfl

@[simp] theorem toList_checkf (f b : List γ) : (checkf f b).toList = f ++ b.reverse := by
  cases f <;> simp [checkf, toList]

@[simp] theorem size_checkf (f b : List γ) : (checkf f b).size = f.length + b.length := by
  cases f <;> simp [checkf, size]

theorem wf_checkf (f b : List γ) : (checkf f b).WF := by
  cases f with
  | nil => intro _; rfl
  | cons _ _ => intro h; cases h

@[simp] theorem length_toList (q : FifoQueue γ) : q.toList.length = q.size := by
  simp [toList, size]

@[simp] theorem toList_enqueue (q : FifoQueue γ) (x : γ) :
    (q.enqueue x).toList = q.toList ++ [x] := by
  rw [enqueue, toList_checkf, toList]
  simp [List.append_assoc]

@[simp] theorem size_enqueue (q : FifoQueue γ) (x : γ) :
    (q.enqueue x).size = q.size + 1 := by
  rw [enqueue, size_checkf, size, List.length_cons, Nat.add_assoc]

theorem wf_enqueue (q : FifoQueue γ) (x : γ) : (q.enqueue x).WF :=
  wf_checkf q.front (x :: q.back)

theorem toList_eq_nil_of_front_eq_nil {q : FifoQueue γ} (hwf : q.WF) (hf : q.front = []) :
    q.toList = [] := by
  simp [toList, hf, hwf hf]

theorem front_cons_spec {q : FifoQueue γ} {x : γ} {f : List γ} (hf : q.front = x :: f) :
    q.toList = x :: (checkf f q.back).toList ∧ (checkf f q.back).WF :=
  ⟨by rw [toList, hf, toList_checkf, List.cons_append], wf_checkf f q.back⟩

theorem peek?_eq_head? {q : FifoQueue γ} (hwf : q.WF) : q.peek? = q.toList.head? := by
  cases hf : q.front
  · simp [peek?, hf, toList_eq_nil_of_front_eq_nil hwf hf]
  · simp [peek?, toList, hf]

theorem dequeue?_spec {q : FifoQueue γ} (hwf : q.WF) :
    match q.dequeue? with
    | none => q.toList = []
    | some (x, q') => q.toList = x :: q'.toList ∧ q'.WF := by
  unfold dequeue?
  cases hf : q.front with
  | nil => exact toList_eq_nil_of_front_eq_nil hwf hf
  | cons x f => exact front_cons_spec hf

/-- Potential bound for `enqueue` with potential `Φ(q) = q.back.length`:
reversal steps plus `ΔΦ` is at most `1`. -/
theorem enqueue_revCost_bound (q : FifoQueue γ) (x : γ) :
    checkfRevCost q.front (x :: q.back) + (q.enqueue x).back.length ≤ q.back.length + 1 := by
  rw [enqueue]
  cases q.front <;> simp [checkf, checkfRevCost]

/-- Potential bound for `dequeue?` with potential `Φ(q) = q.back.length`:
reversal steps plus `ΔΦ` is `0`. -/
theorem dequeue?_revCost_bound (f b : List γ) :
    checkfRevCost f b + (checkf f b).back.length ≤ b.length := by
  cases f <;> simp [checkf, checkfRevCost]

end FifoQueue

/-! ## Cached-weight trees and van Leeuwen's two-queue loop -/

/-- A `CodeTree α` paired with its cached total weight `wt : β`. -/
structure WeightedTree (α β : Type*) where
  /-- Underlying code tree. -/
  tree : CodeTree α
  /-- Cached subtree weight (`tree.weight w`). -/
  wt : β
  deriving DecidableEq, Repr

/-- Pop a minimum-weight entry from leaf list `q₁` and internal-node queue `q₂` (preferring `q₁` on
ties, as in [VanLeeuwen1976]). Matching directly on `q₂.front` ensures `FifoQueue.checkf` is
evaluated under strict evaluation only in branches that actually dequeue from `q₂`. -/
def popMin {α β : Type u} [LE β] [DecidableRel (· ≤ · : β → β → Prop)]
    (q₁ : List (WeightedTree α β)) (q₂ : FifoQueue (WeightedTree α β)) :
    Option (WeightedTree α β × List (WeightedTree α β) × FifoQueue (WeightedTree α β)) :=
  match q₁, q₂.front with
  | [], [] => none
  | [], y :: f => some (y, [], FifoQueue.checkf f q₂.back)
  | x :: q₁', [] => some (x, q₁', q₂)
  | x :: q₁', y :: f =>
    if x.wt ≤ y.wt then
      some (x, q₁', q₂)
    else
      some (y, x :: q₁', FifoQueue.checkf f q₂.back)

/-- Representation-free specification of `popMin` in terms of `q₂.toList` whenever `q₂.WF` holds. -/
theorem popMin_spec_toList {α β : Type u} [LE β] [DecidableRel (· ≤ · : β → β → Prop)]
    (q₁ : List (WeightedTree α β)) {q₂ : FifoQueue (WeightedTree α β)} (hwf : q₂.WF) :
    match q₁, q₂.toList with
    | [], [] => popMin q₁ q₂ = none
    | [], y :: ys => ∃ q₂', popMin q₁ q₂ = some (y, [], q₂') ∧ q₂'.WF ∧ q₂'.toList = ys
    | x :: xs, [] => popMin q₁ q₂ = some (x, xs, q₂)
    | x :: xs, y :: ys =>
      if x.wt ≤ y.wt then
        popMin q₁ q₂ = some (x, xs, q₂)
      else
        ∃ q₂', popMin q₁ q₂ = some (y, x :: xs, q₂') ∧ q₂'.WF ∧ q₂'.toList = ys := by
  unfold popMin
  cases h2 : q₂.front with
  | nil =>
    have hnil := FifoQueue.toList_eq_nil_of_front_eq_nil hwf h2
    cases q₁ <;> simp [hnil]
  | cons y f =>
    rcases FifoQueue.front_cons_spec h2 with ⟨hto, hwf'⟩
    cases q₁ with
    | nil =>
      rw [hto]
      exact ⟨FifoQueue.checkf f q₂.back, rfl, hwf', rfl⟩
    | cons x xs =>
      rw [hto]
      dsimp only
      split_ifs with hle
      · rfl
      · exact ⟨FifoQueue.checkf f q₂.back, rfl, hwf', rfl⟩

private theorem popMin_size_eq {α β : Type u} [LE β] [DecidableRel (· ≤ · : β → β → Prop)]
    {q₁ q₁' : List (WeightedTree α β)} {q₂ q₂' : FifoQueue (WeightedTree α β)}
    {u : WeightedTree α β}
    (h : popMin q₁ q₂ = some (u, q₁', q₂')) :
    q₁'.length + q₂'.size + 1 = q₁.length + q₂.size := by
  unfold popMin at h
  rcases q₁ with _ | ⟨x, xs⟩ <;> cases h2 : q₂.front <;> simp only [h2] at h
  · cases h
  all_goals
    (try split_ifs at h) <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨_, rfl, rfl⟩ := h <;> (try rw [FifoQueue.size_checkf]) <;>
      simp [FifoQueue.size, h2] <;> omega

/-- Fuel-driven merge loop of van Leeuwen's two-queue Huffman algorithm ([VanLeeuwen1976]). -/
private def twoQueueSteps {α β : Type u} [Add β] [LE β] [DecidableRel (· ≤ · : β → β → Prop)] :
    ℕ → List (WeightedTree α β) → FifoQueue (WeightedTree α β) → Option (CodeTree α)
  | 0, _, _ => none
  | fuel + 1, q₁, q₂ =>
    match popMin q₁ q₂ with
    | none => none
    | some (a, q₁', q₂') =>
      match popMin q₁' q₂' with
      | none => some a.tree
      | some (b, q₁'', q₂'') =>
        twoQueueSteps fuel q₁'' (q₂''.enqueue ⟨.branch a.tree b.tree, a.wt + b.wt⟩)

/-- Main merge loop of van Leeuwen's two-queue Huffman algorithm ([VanLeeuwen1976]). -/
def twoQueueLoop {α β : Type u} [Add β] [LE β] [DecidableRel (· ≤ · : β → β → Prop)]
    (q₁ : List (WeightedTree α β)) (q₂ : FifoQueue (WeightedTree α β)) :
    Option (CodeTree α) :=
  twoQueueSteps (q₁.length + q₂.size) q₁ q₂

private theorem twoQueueSteps_eq_twoQueueLoop {α β : Type u} [Add β] [LE β]
    [DecidableRel (· ≤ · : β → β → Prop)] :
    ∀ (fuel : ℕ) (q₁ : List (WeightedTree α β)) (q₂ : FifoQueue (WeightedTree α β)),
      q₁.length + q₂.size ≤ fuel →
      twoQueueSteps fuel q₁ q₂ = twoQueueLoop q₁ q₂
  | 0, q₁, q₂, hle => by
    unfold twoQueueLoop
    rw [Nat.eq_zero_of_le_zero hle]
  | fuel + 1, q₁, q₂, hle => by
    unfold twoQueueLoop
    rcases hsz : q₁.length + q₂.size with _ | n
    · have hq₁ : q₁ = [] := List.length_eq_zero_iff.mp (by omega)
      have hf : q₂.front = [] := List.length_eq_zero_iff.mp (by rw [FifoQueue.size] at hsz; omega)
      simp [twoQueueSteps, popMin, hq₁, hf]
    · simp only [twoQueueSteps]
      cases hr₁ : popMin q₁ q₂ with
      | none => rfl
      | some res₁ =>
        rcases res₁ with ⟨a, q₁', q₂'⟩
        have hsz₁ := popMin_size_eq hr₁
        dsimp only
        cases hr₂ : popMin q₁' q₂' with
        | none => rfl
        | some res₂ =>
          rcases res₂ with ⟨b, q₁'', q₂''⟩
          have hsz₂ := popMin_size_eq hr₂
          dsimp only
          let q_next := q₂''.enqueue ⟨.branch a.tree b.tree, a.wt + b.wt⟩
          exact (twoQueueSteps_eq_twoQueueLoop fuel q₁'' q_next
              (by simp only [q_next, FifoQueue.size_enqueue]; omega)).trans
            (twoQueueSteps_eq_twoQueueLoop n q₁'' q_next
              (by simp only [q_next, FifoQueue.size_enqueue]; omega)).symm

/-- Fuel-free unfolding equation for `twoQueueLoop`. -/
theorem twoQueueLoop_step {α β : Type u} [Add β] [LE β] [DecidableRel (· ≤ · : β → β → Prop)]
    (q₁ : List (WeightedTree α β)) (q₂ : FifoQueue (WeightedTree α β)) :
    twoQueueLoop q₁ q₂ =
      match popMin q₁ q₂ with
      | none => none
      | some (a, q₁', q₂') =>
        match popMin q₁' q₂' with
        | none => some a.tree
        | some (b, q₁'', q₂'') =>
          twoQueueLoop q₁'' (q₂''.enqueue ⟨.branch a.tree b.tree, a.wt + b.wt⟩) := by
  rw [← twoQueueSteps_eq_twoQueueLoop (q₁.length + q₂.size + 1) q₁ q₂ (Nat.le_succ _)]
  simp only [twoQueueSteps]
  cases hr₁ : popMin q₁ q₂ with
  | none => rfl
  | some res₁ =>
    rcases res₁ with ⟨a, q₁', q₂'⟩
    have hsz₁ := popMin_size_eq hr₁
    dsimp only
    cases hr₂ : popMin q₁' q₂' with
    | none => rfl
    | some res₂ =>
      rcases res₂ with ⟨b, q₁'', q₂''⟩
      have hsz₂ := popMin_size_eq hr₂
      dsimp only
      exact twoQueueSteps_eq_twoQueueLoop _ _ _ (by simp only [FifoQueue.size_enqueue]; omega)

/-- Two-queue Huffman construction from a symbol list `syms` sorted by `w` ([VanLeeuwen1976]). -/
@[expose] def huffmanFromSorted {α β : Type u} [Add β] [LE β]
    [DecidableRel (· ≤ · : β → β → Prop)] (w : α → β) (syms : List α) : Option (CodeTree α) :=
  twoQueueLoop (syms.map fun a => ⟨.leaf a, w a⟩) FifoQueue.empty

/-- Huffman construction from an arbitrary symbol list `syms`, sorting first via `List.mergeSort`
and then running `huffmanFromSorted`. -/
@[expose] def huffman {α β : Type u} [Add β] [LE β] [DecidableRel (· ≤ · : β → β → Prop)]
    (w : α → β) (syms : List α) : Option (CodeTree α) :=
  huffmanFromSorted w (syms.mergeSort fun a b => decide (w a ≤ w b))

/-! ## Correctness of van Leeuwen's two-queue invariant and optimality of `huffman` -/

/-- `IsHuffmanBuild` depends on the starting forest `F` only up to `List.Perm`. -/
theorem IsHuffmanBuild.of_perm {α β : Type*} [Add β] [LE β] {w : α → β}
    {F₁ F₂ : List (CodeTree α)} {T : CodeTree α}
    (hperm : F₁.Perm F₂) (hbuild : IsHuffmanBuild w F₂ T) :
    IsHuffmanBuild w F₁ T := by
  cases hbuild with
  | single =>
    rw [List.Perm.eq_singleton hperm]
    exact .single T
  | step hmin hsub =>
    exact .step ⟨hperm.trans hmin.perm, hmin.weight_le⟩ hsub

private structure TwoQueueInv {α β : Type u} [AddCommMonoid β] [LinearOrder β]
    (w : α → β) (q₁ : List (WeightedTree α β)) (q₂ : FifoQueue (WeightedTree α β)) : Prop where
  wf : q₂.WF
  wt_eq : ∀ e ∈ q₁ ++ q₂.toList, e.wt = e.tree.weight w ∧ 0 ≤ e.wt
  sorted₁ : q₁.Pairwise (fun u v => u.wt ≤ v.wt)
  sorted₂ : q₂.toList.Pairwise (fun u v => u.wt ≤ v.wt)
  q2_le_pair_sum : ∀ u v rest, (q₁ ++ q₂.toList).Perm (u :: v :: rest) →
    ∀ z ∈ q₂.toList, z.wt ≤ u.wt + v.wt

private theorem popMin_correct {α β : Type u} [LinearOrder β]
    {q₁ : List (WeightedTree α β)} {q₂ : FifoQueue (WeightedTree α β)}
    (hwf : q₂.WF)
    (hs₁ : q₁.Pairwise (fun u v => u.wt ≤ v.wt))
    (hs₂ : q₂.toList.Pairwise (fun u v => u.wt ≤ v.wt))
    (hne : q₁ ++ q₂.toList ≠ []) :
    ∃ u q₁' q₂',
      popMin q₁ q₂ = some (u, q₁', q₂') ∧
      q₂'.WF ∧
      q₁'.Pairwise (fun a b => a.wt ≤ b.wt) ∧
      q₂'.toList.Pairwise (fun a b => a.wt ≤ b.wt) ∧
      (∀ z ∈ q₂'.toList, z ∈ q₂.toList) ∧
      (q₁ ++ q₂.toList).Perm (u :: (q₁' ++ q₂'.toList)) ∧
      (∀ z ∈ q₁' ++ q₂'.toList, u.wt ≤ z.wt) := by
  have hspec := popMin_spec_toList q₁ hwf
  rcases h1 : q₁ with _ | ⟨x, xs⟩ <;> rcases h2 : q₂.toList with _ | ⟨y, ys⟩
  · simp [h1, h2] at hne
  · rw [h1, h2] at hspec
    rcases hspec with ⟨q₂', hpop, hwf', hto'⟩
    rw [h2, List.pairwise_cons] at hs₂
    exact ⟨y, [], q₂', hpop, hwf', List.Pairwise.nil, hto' ▸ hs₂.2,
      fun _ hz => List.mem_cons_of_mem y (hto' ▸ hz), hto' ▸ List.Perm.refl _,
      fun z hz => hs₂.1 z (by simpa only [List.nil_append, hto'] using hz)⟩
  · rw [h1, h2] at hspec
    rw [h1, List.pairwise_cons] at hs₁
    refine ⟨x, xs, q₂, hspec, hwf, hs₁.2, h2 ▸ hs₂, fun _ hz => h2 ▸ hz,
      by simp [h2], fun z hz => hs₁.1 z (by simpa only [h2, List.append_nil] using hz)⟩
  · rw [h1, h2] at hspec
    dsimp only at hspec
    have hs₁' := List.pairwise_cons.mp (h1 ▸ hs₁)
    have hs₂' := List.pairwise_cons.mp (h2 ▸ hs₂)
    by_cases hle : x.wt ≤ y.wt
    · simp only [hle, ↓reduceIte] at hspec
      refine ⟨x, xs, q₂, hspec, hwf, hs₁'.2, h2 ▸ hs₂, fun _ hz => h2 ▸ hz,
        by simp [h2], fun z hz => ?_⟩
      rcases List.mem_append.mp hz with hxs | hq2
      · exact hs₁'.1 z hxs
      · rw [h2] at hq2
        rcases List.mem_cons.mp hq2 with rfl | htail
        · exact hle
        · exact le_trans hle (hs₂'.1 z htail)
    · simp only [hle, ↓reduceIte] at hspec
      rcases hspec with ⟨q₂', hpop, hwf', hto'⟩
      have hyx : y.wt ≤ x.wt := le_of_not_ge hle
      refine ⟨y, x :: xs, q₂', hpop, hwf', h1 ▸ hs₁, hto' ▸ hs₂'.2,
        fun _ hz => List.mem_cons_of_mem y (hto' ▸ hz),
        hto' ▸ List.perm_middle, fun z hz => ?_⟩
      rcases List.mem_append.mp hz with hxs | hq2'
      · rcases List.mem_cons.mp hxs with rfl | hxs'
        · exact hyx
        · exact le_trans hyx (hs₁'.1 z hxs')
      · exact hs₂'.1 z (hto' ▸ hq2')

private theorem pairwise_snoc_of_le {γ : Type*} {R : γ → γ → Prop} {L : List γ} {m : γ}
    (hL : L.Pairwise R) (hm : ∀ z ∈ L, R z m) : (L ++ [m]).Pairwise R := by
  rw [List.pairwise_append]
  exact ⟨hL, List.pairwise_singleton R m, fun z hz _ hw => by
    simp only [List.mem_singleton] at hw
    exact hw ▸ hm z hz⟩

private theorem twoQueueLoop_correct {α β : Type u}
    [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    {w : α → β} {q₁ : List (WeightedTree α β)} {q₂ : FifoQueue (WeightedTree α β)}
    (hinv : TwoQueueInv w q₁ q₂)
    (hne : q₁ ++ q₂.toList ≠ []) :
    ∃ T, twoQueueLoop q₁ q₂ = some T ∧
      IsHuffmanBuild w ((q₁ ++ q₂.toList).map WeightedTree.tree) T := by
  suffices h : ∀ (n : ℕ) (l₁ : List (WeightedTree α β)) (l₂ : FifoQueue (WeightedTree α β)),
      l₁.length + l₂.size ≤ n →
      TwoQueueInv w l₁ l₂ →
      l₁ ++ l₂.toList ≠ [] →
      ∃ T, twoQueueLoop l₁ l₂ = some T ∧
        IsHuffmanBuild w ((l₁ ++ l₂.toList).map WeightedTree.tree) T from
    h (q₁.length + q₂.size) q₁ q₂ le_rfl hinv hne
  intro n
  induction n with
  | zero =>
    intro l₁ l₂ h0 _ hne'
    exact (hne' (List.length_eq_zero_iff.mp
      (by rw [List.length_append, FifoQueue.length_toList]; omega))).elim
  | succ n ih =>
    intro l₁ l₂ hle hinv' hne'
    rcases popMin_correct hinv'.wf hinv'.sorted₁ hinv'.sorted₂ hne' with
      ⟨a, l₁', l₂', hr₁, hwf₁, hs₁', hs₂', hsub₁, hperm₁, hmin_a⟩
    have hsz₁ := popMin_size_eq hr₁
    rw [twoQueueLoop_step]
    simp only [hr₁]
    by_cases hne₂ : l₁' ++ l₂'.toList = []
    · obtain ⟨hl₁'_nil, hto_nil⟩ := List.append_eq_nil_iff.mp hne₂
      have hr₂_none : popMin l₁' l₂' = none := by
        simpa [hl₁'_nil, hto_nil] using popMin_spec_toList l₁' hwf₁
      refine ⟨a.tree, by simp [hr₂_none], .of_perm ?_ (.single a.tree)⟩
      simpa only [hne₂, List.map_cons, List.map_nil] using hperm₁.map WeightedTree.tree
    · rcases popMin_correct hwf₁ hs₁' hs₂' hne₂ with
        ⟨b, l₁'', l₂'', hr₂, _, hs₁'', hs₂'', hsub₂, hperm₂, hmin_b⟩
      have hsz₂ := popMin_size_eq hr₂
      simp only [hr₂]
      have hperm_ab : (l₁ ++ l₂.toList).Perm (a :: b :: (l₁'' ++ l₂''.toList)) :=
        hperm₁.trans (hperm₂.cons a)
      have ha_in : a ∈ l₁ ++ l₂.toList := hperm_ab.symm.subset List.mem_cons_self
      have hb_in : b ∈ l₁ ++ l₂.toList :=
        hperm_ab.symm.subset (List.mem_cons_of_mem a List.mem_cons_self)
      have hsub_ab : ∀ {e}, e ∈ l₁'' ++ l₂''.toList → e ∈ l₁ ++ l₂.toList := fun he =>
        hperm_ab.symm.subset (List.mem_cons_of_mem a (List.mem_cons_of_mem b he))
      have hab : a.wt ≤ b.wt := hmin_a b (hperm₂.symm.subset List.mem_cons_self)
      rcases hinv'.wt_eq a ha_in with ⟨ha_wt, ha_nonneg⟩
      rcases hinv'.wt_eq b hb_in with ⟨hb_wt, hb_nonneg⟩
      let m : WeightedTree α β := ⟨.branch a.tree b.tree, a.wt + b.wt⟩
      let q_next := l₂''.enqueue m
      have hq_next_to : q_next.toList = l₂''.toList ++ [m] := FifoQueue.toList_enqueue l₂'' m
      have hq2_le_m : ∀ z ∈ l₂''.toList, z.wt ≤ m.wt := fun z hz =>
        hinv'.q2_le_pair_sum a b _ hperm_ab z (hsub₁ z (hsub₂ z hz))
      have hbm : b.wt ≤ m.wt := by simpa [m] using add_le_add ha_nonneg (le_refl b.wt)
      have hb_le_all_new : ∀ x ∈ l₁'' ++ q_next.toList, b.wt ≤ x.wt := by
        rw [hq_next_to, ← List.append_assoc]
        exact List.forall_mem_append.mpr ⟨hmin_b, List.forall_mem_singleton.mpr hbm⟩
      have hinv_next : TwoQueueInv w l₁'' q_next := by
        refine ⟨FifoQueue.wf_enqueue l₂'' m, ?_, hs₁'',
          hq_next_to ▸ pairwise_snoc_of_le hs₂'' hq2_le_m, ?_⟩
        · rw [hq_next_to, ← List.append_assoc]
          exact List.forall_mem_append.mpr ⟨fun e he => hinv'.wt_eq e (hsub_ab he),
            List.forall_mem_singleton.mpr
              ⟨by simp [m, ha_wt, hb_wt], add_nonneg ha_nonneg hb_nonneg⟩⟩
        · intro u v rest huv z hz
          have hm_uv : m.wt ≤ u.wt + v.wt := add_le_add
            (le_trans hab (hb_le_all_new u (huv.symm.subset List.mem_cons_self)))
            (hb_le_all_new v (huv.symm.subset (List.mem_cons_of_mem u List.mem_cons_self)))
          rw [hq_next_to, List.mem_append, List.mem_singleton] at hz
          rcases hz with hz | rfl
          exacts [(hq2_le_m z hz).trans hm_uv, hm_uv]
      have hne_next : l₁'' ++ q_next.toList ≠ [] := by simp [hq_next_to]
      have hsz_next : l₁''.length + q_next.size ≤ n := by
        simp only [q_next, FifoQueue.size_enqueue]; omega
      rcases ih l₁'' q_next hsz_next hinv_next hne_next with ⟨T, hT_ret, hT_build⟩
      refine ⟨T, hT_ret, ?_⟩
      let F_rest := (l₁'' ++ l₂''.toList).map WeightedTree.tree
      have hmin_pair : IsMinPair w ((l₁ ++ l₂.toList).map WeightedTree.tree)
          a.tree b.tree F_rest := by
        refine ⟨hperm_ab.map WeightedTree.tree, fun t ht => ?_⟩
        rcases List.mem_map.mp ht with ⟨e, he, rfl⟩
        rw [← ha_wt, ← hb_wt, ← (hinv'.wt_eq e (hsub_ab he)).1]
        exact ⟨le_trans hab (hmin_b e he), hmin_b e he⟩
      have hforest_perm : (CodeTree.branch a.tree b.tree :: F_rest).Perm
          ((l₁'' ++ q_next.toList).map WeightedTree.tree) := by
        rw [hq_next_to, ← List.append_assoc, List.map_append, List.map_singleton]
        exact (List.perm_append_singleton m.tree F_rest).symm
      exact IsHuffmanBuild.step hmin_pair (IsHuffmanBuild.of_perm hforest_perm hT_build)

/-- **Correctness of Two-Queue Huffman Construction** ([VanLeeuwen1976]): on any nonempty symbol
list `syms` sorted in nondecreasing order of `w` with nonnegative weights,
`huffmanFromSorted w syms` returns `some T` satisfying `IsHuffmanBuild w (syms.map .leaf) T` and
`T.leaves.Perm syms`. -/
theorem huffmanFromSorted_spec {α β : Type u}
    [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    {w : α → β} {syms : List α}
    (hne : syms ≠ [])
    (hsorted : syms.Pairwise (fun a b => w a ≤ w b))
    (hw : ∀ a ∈ syms, 0 ≤ w a) :
    ∃ T, huffmanFromSorted w syms = some T ∧
      IsHuffmanBuild w (syms.map .leaf) T ∧
      T.leaves.Perm syms := by
  let q₁ := syms.map fun a => (⟨.leaf a, w a⟩ : WeightedTree α β)
  have hinv : TwoQueueInv w q₁ FifoQueue.empty := by
    refine ⟨FifoQueue.wf_empty, ?_, by simpa [q₁, List.pairwise_map] using hsorted, by simp,
      fun _ _ _ _ _ hz => by simp at hz⟩
    intro e he
    simp only [FifoQueue.toList_empty, List.append_nil, q₁, List.mem_map] at he
    rcases he with ⟨a, ha, rfl⟩
    exact ⟨rfl, hw a ha⟩
  rcases twoQueueLoop_correct hinv (by simpa [q₁, FifoQueue.toList_empty] using hne) with
    ⟨T, hT_ret, hT_build⟩
  have hT_build' : IsHuffmanBuild w (syms.map .leaf) T := by
    simpa [q₁, List.map_map, Function.comp_def] using hT_build
  exact ⟨T, hT_ret, hT_build', hT_build'.leaves_perm⟩

/-- **End-to-End Correctness of `huffman`**: on any nonempty symbol list `syms` with nonnegative
weights, `huffman w syms` returns `some T` satisfying `IsHuffmanBuild w (syms.map .leaf) T` and
`T.leaves.Perm syms`. -/
theorem huffman_spec {α β : Type u}
    [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    {w : α → β} {syms : List α}
    (hne : syms ≠ [])
    (hw : ∀ a ∈ syms, 0 ≤ w a) :
    ∃ T, huffman w syms = some T ∧
      IsHuffmanBuild w (syms.map .leaf) T ∧
      T.leaves.Perm syms := by
  let cmp : α → α → Bool := fun a b => decide (w a ≤ w b)
  let sorted := syms.mergeSort cmp
  have hperm : sorted.Perm syms := List.mergeSort_perm syms cmp
  have hsorted_ne : sorted ≠ [] := fun hnil => hne (List.Perm.nil_eq (hnil ▸ hperm)).symm
  have hpw : sorted.Pairwise (fun a b => w a ≤ w b) := by
    have htot : ∀ a b, (cmp a b || cmp b a) = true := by grind
    have htr : ∀ a b c, cmp a b = true → cmp b c = true → cmp a c = true := by grind
    simpa [cmp, decide_eq_true_eq] using List.pairwise_mergeSort htr htot syms
  rcases huffmanFromSorted_spec hsorted_ne hpw (fun a ha => hw a (hperm.subset ha)) with
    ⟨T, hT_eq, hT_build, hT_perm⟩
  exact ⟨T, hT_eq, IsHuffmanBuild.of_perm (hperm.symm.map CodeTree.leaf) hT_build,
    hT_perm.trans hperm⟩

/-- **Optimality of `huffman` over Full Binary Code Trees**: the tree returned by `huffman w syms`
minimizes `weightedPathLength w` among all full binary `CodeTree α`s with leaf multiset `syms`. -/
theorem huffman_optimal {α β : Type u}
    [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    {w : α → β} {syms : List α} {T : CodeTree α}
    (hw : ∀ a ∈ syms, 0 ≤ w a)
    (hT : huffman w syms = some T)
    (T' : CodeTree α) (hT' : T'.leaves.Perm syms) :
    T.weightedPathLength w ≤ T'.weightedPathLength w := by
  have hne : syms ≠ [] := fun hnil => T'.leaves_ne_nil (List.Perm.eq_nil (hnil ▸ hT'))
  rcases huffman_spec hne hw with ⟨T₀, hT₀, hbuild, _⟩
  obtain rfl : T = T₀ := Option.some.inj (hT.symm.trans hT₀)
  exact hbuild.weightedPathLength_le T' hT'

/-- **Optimality of `huffman` over All Prefix-Free Binary Codes**: on distinct symbols `syms` with
nonnegative weights, `huffman w syms` achieves weighted path length at most that of *any* injective
`InformationTheory.IsPrefixFree` binary code. -/
theorem huffman_optimal_isPrefixFree {α β : Type u}
    [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    {syms : List α} (hne : syms ≠ []) (hnodup : syms.Nodup)
    {w : α → β} (hw : ∀ a ∈ syms, 0 ≤ w a)
    {T : CodeTree α} (hT : huffman w syms = some T)
    {code : α → List Bool}
    (hinj : Set.InjOn code {a | a ∈ syms})
    (hpf : InformationTheory.IsPrefixFree (code '' {a | a ∈ syms})) :
    T.weightedPathLength w ≤ (syms.map fun a => (code a).length • w a).sum := by
  rcases huffman_spec hne hw with ⟨T₀, hT₀, hbuild, _⟩
  obtain rfl : T = T₀ := Option.some.inj (hT.symm.trans hT₀)
  exact hbuild.weightedPathLength_le_of_isPrefixFree hne hnodup hw hinj hpf

/-- **Optimality of `huffman` over All Uniquely Decodable Binary Codes**: on distinct symbols `syms`
with nonnegative weights, `huffman w syms` achieves weighted path length at most that of *any*
injective `InformationTheory.IsUniquelyDecodable` binary code. -/
theorem huffman_optimal_isUniquelyDecodable {α β : Type u}
    [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    {syms : List α} (hne : syms ≠ []) (hnodup : syms.Nodup)
    {w : α → β} (hw : ∀ a ∈ syms, 0 ≤ w a)
    {T : CodeTree α} (hT : huffman w syms = some T)
    {code : α → List Bool}
    (hinj : Set.InjOn code {a | a ∈ syms})
    (hud : InformationTheory.IsUniquelyDecodable (code '' {a | a ∈ syms})) :
    T.weightedPathLength w ≤ (syms.map fun a => (code a).length • w a).sum := by
  rcases huffman_spec hne hw with ⟨T₀, hT₀, hbuild, _⟩
  obtain rfl : T = T₀ := Option.some.inj (hT.symm.trans hT₀)
  exact hbuild.weightedPathLength_le_of_isUniquelyDecodable hne hnodup hw hinj hud

end Cslib.Algorithms.Lean.Huffman
