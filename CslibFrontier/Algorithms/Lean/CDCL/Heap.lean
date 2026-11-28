/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Batteries.Data.BinaryHeap
-- `import all` only to unfold `heapifyUp` and `heapifyDown`, whose bodies Batteries does not
-- expose, and to use its unfolding lemmas for `heapifyDown`, in the proofs that the structurally
-- recursive versions compute the same.
import all Batteries.Data.BinaryHeap.Basic
import all Batteries.Data.BinaryHeap.Lemmas
-- `import all` also to use the invariants of `heapifyUp` (`WF.ExceptAt`, `WF.ParentGeChildren`) and
-- its correctness (`heapifyUp_topDown`), for a heap whose order changes at one element.
import all Batteries.Data.BinaryHeap.WF

/-! # Binary heaps the kernel can run

Batteries' binary heaps (`Batteries.BinaryHeap`) come with proofs: inserting and removing the
maximum keep the heap well formed (`Batteries.BinaryHeap.insert_wf`,
`Batteries.BinaryHeap.popMax_wf`), the maximum is at least every element
(`Batteries.BinaryHeap.max_ge_all`), and the operations permute the elements. But their sifting
functions recurse by well-founded recursion, which the kernel does not evaluate, and the CDCL
solver is meant to run in the kernel. So this file defines sifting by structural recursion on a
fuel (`heapifyUpF`, `heapifyDownF`), proves that with enough fuel it computes exactly what
Batteries' functions compute, and defines insertion and removal of the maximum with it
(`Batteries.BinaryHeap.insertF`, `Batteries.BinaryHeap.popMaxF`), equal to Batteries' operations,
so that all of Batteries' theorems apply. The empty heap, the maximum and the larger child are
redefined too (`Batteries.BinaryHeap.emptyF`, `Batteries.BinaryHeap.maxF`,
`Batteries.BinaryHeap.maxChildF`), as Batteries does not expose their bodies to other modules,
which the kernel would need.

## Main definitions

* `Batteries.BinaryHeap.insertF`, `Batteries.BinaryHeap.popMaxF`: insertion and removal of the
  maximum by structural recursion.
* `Batteries.BinaryHeap.emptyF`, `Batteries.BinaryHeap.maxF`: the empty heap and the maximum.

## Main results

* `Batteries.BinaryHeap.insertF_eq`, `Batteries.BinaryHeap.popMaxF_eq`: they are Batteries'
  `insert` and `popMax`.
* `Batteries.BinaryHeap.mem_popMaxF`, `Batteries.BinaryHeap.mem_of_mem_popMaxF`: removing the
  maximum removes it and nothing else.
* `Batteries.BinaryHeap.heapifyUpF_perm`, `Batteries.BinaryHeap.heapifyDownF_perm`: sifting
  permutes the elements.
* `Batteries.BinaryHeap.topDown_heapifyUp_of_isGE`: after the order changed at one element, as when
  the key of a variable alone grew, sifting it up restores the heap.
-/

@[expose] public section

universe u

namespace Batteries.BinaryHeap

variable {α : Type u} [Ord α]

/-- The empty heap, `empty` with an exposed body. -/
def emptyF : BinaryHeap α := ⟨#[]⟩

theorem emptyF_eq : (emptyF : BinaryHeap α) = empty := by unfold emptyF empty; rfl

/-- The maximum, `max` with an exposed body. -/
def maxF (heap : BinaryHeap α) : Option α := heap.arr[0]?

theorem maxF_eq (heap : BinaryHeap α) : heap.maxF = heap.max := by unfold maxF max; rfl

/-- The larger child, `maxChild` with an exposed body. -/
def maxChildF {sz : Nat} (a : Vector α sz) (i : Fin sz) : Option (Fin sz) :=
  let left := 2 * i.val + 1
  let right := left + 1
  if hleft : left < sz then
    if hright : right < sz then
      if compare a[left] a[right] |>.isLT then some ⟨right, hright⟩ else some ⟨left, hleft⟩
    else some ⟨left, hleft⟩
  else none

theorem maxChildF_eq {sz : Nat} (a : Vector α sz) (i : Fin sz) : maxChildF a i = maxChild a i := by
  unfold maxChildF maxChild; rfl

/-- `heapifyUp` by structural recursion on `fuel`. -/
def heapifyUpF : (fuel : Nat) → {sz : Nat} → Vector α sz → Fin sz → Vector α sz
  | 0, _, a, _ => a
  | _ + 1, _, a, ⟨0, _⟩ => a
  | fuel + 1, _, a, ⟨i' + 1, hi⟩ =>
    let j := i' / 2
    if compare a[j] a[i' + 1] |>.isLT then
      heapifyUpF fuel (a.swap (i' + 1) j) ⟨j, by omega⟩
    else a

/-- With fuel above the position, `heapifyUpF` is `heapifyUp`. -/
theorem heapifyUpF_eq : ∀ (fuel : Nat) {sz : Nat} (a : Vector α sz) (i : Fin sz), i.val < fuel →
    heapifyUpF fuel a i = heapifyUp a i
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, _, a, ⟨0, _⟩, _ => by rw [heapifyUpF, heapifyUp.eq_def]
  | fuel + 1, _, a, ⟨i' + 1, hi⟩, h => by
    rw [heapifyUpF, heapifyUp.eq_def]
    simp only [Fin.getElem_fin]
    split
    · exact heapifyUpF_eq fuel _ _ (by simp only at h ⊢; omega)
    · rfl

/-- `heapifyDown` by structural recursion on `fuel`. -/
def heapifyDownF : (fuel : Nat) → {sz : Nat} → Vector α sz → Fin sz → Vector α sz
  | 0, _, a, _ => a
  | fuel + 1, _, a, i =>
    match maxChildF a i with
    | none => a
    | some j =>
      if compare a[i] a[j] |>.isLT then heapifyDownF fuel (a.swap i j) j else a

/-- With fuel above the distance to the end, `heapifyDownF` is `heapifyDown`. -/
theorem heapifyDownF_eq : ∀ (fuel : Nat) {sz : Nat} (a : Vector α sz) (i : Fin sz),
    sz - i.val ≤ fuel → heapifyDownF fuel a i = heapifyDown a i
  | 0, _, _, i, h => absurd h (by have := i.isLt; omega)
  | fuel + 1, _, a, i, h => by
    rw [heapifyDownF]
    split
    · rename_i hn
      rw [maxChildF_eq] at hn
      rw [heapifyDown_eq_of_maxChild_none hn]
    · rename_i j hj
      rw [maxChildF_eq] at hj
      have := maxChild_gt hj
      split
      · rename_i hlt
        rw [heapifyDown_eq_of_lt_child hj hlt]
        exact heapifyDownF_eq fuel _ _ (by omega)
      · rename_i hlt
        rw [heapifyDown_eq_of_not_lt_child hj hlt]

/-- **Insertion** by structural recursion. The size is read before the push, so that the array is
updated in place when the heap is not shared. -/
def insertF (heap : BinaryHeap α) (x : α) : BinaryHeap α :=
  let n := heap.size
  let v := heap.vector.push x
  ⟨heapifyUpF (n + 1) v ⟨n, Nat.lt_succ_self _⟩ |>.toArray⟩

theorem insertF_eq (heap : BinaryHeap α) (x : α) : heap.insertF x = heap.insert x := by
  simp only [insertF, insert]
  rw [heapifyUpF_eq (heap.size + 1) _ _ (Nat.lt_succ_self _)]

/-- **Removing the maximum** by structural recursion. -/
def popMaxF (heap : BinaryHeap α) : BinaryHeap α :=
  if h0 : heap.size = 0 then heap else
    have hs : heap.size - 1 < heap.size := Nat.pred_lt h0
    have h0 : 0 < heap.size := Nat.zero_lt_of_ne_zero h0
    -- the size is read before the swap, so that the array is updated in place
    let n := heap.size
    let v := heap.vector.swap _ _ h0 hs |>.pop
    if h : 0 < n - 1 then
      ⟨heapifyDownF n v ⟨0, h⟩ |>.toArray⟩
    else
      ⟨v.toArray⟩

theorem popMaxF_eq (heap : BinaryHeap α) : heap.popMaxF = heap.popMax := by
  unfold popMaxF popMax
  dsimp only
  split
  · rfl
  · split
    · rw [heapifyDownF_eq heap.size _ _ (by simp only [size] at *; omega)]
    · rfl

/-- The maximum is the first element. -/
theorem eq_getElem_zero_of_max {heap : BinaryHeap α} {x : α} (h : heap.maxF = some x) :
    ∃ hpos : 0 < heap.size, x = heap.arr[0] := by
  rw [maxF_eq] at h
  exact ⟨size_pos_of_max h, max_eq_arr_zero h⟩

theorem mem_of_max {heap : BinaryHeap α} {x : α} (h : heap.maxF = some x) : x ∈ heap := by
  obtain ⟨hpos, rfl⟩ := eq_getElem_zero_of_max h
  exact Array.getElem_mem _

/-- Removing the maximum `x` leaves every other element. -/
theorem mem_popMaxF {heap : BinaryHeap α} {x y : α} (hx : heap.maxF = some x) (hy : y ∈ heap) :
    y = x ∨ y ∈ heap.popMaxF := by
  obtain ⟨hpos, rfl⟩ := eq_getElem_zero_of_max hx
  have : y ∈ heap.arr[0] :: heap.popMax.arr.toList :=
    (popMax_perm hpos).mem_iff.2 (Array.mem_toList_iff.2 hy)
  rw [popMaxF_eq]
  exact (List.mem_cons.1 this).imp_right Array.mem_toList_iff.1

/-- Removing the maximum adds no element. -/
theorem mem_of_mem_popMaxF {heap : BinaryHeap α} {y : α} (hy : y ∈ heap.popMaxF) : y ∈ heap := by
  rw [popMaxF_eq] at hy
  exact mem_of_mem_popMax hy

/-- Sifting up permutes the elements. -/
theorem heapifyUpF_perm : ∀ (fuel : Nat) {sz : Nat} (a : Vector α sz) (i : Fin sz),
    (heapifyUpF fuel a i).Perm a
  | 0, _, _, _ => .refl _
  | _ + 1, _, _, ⟨0, _⟩ => .refl _
  | fuel + 1, _, a, ⟨i' + 1, hi⟩ => by
    rw [heapifyUpF]
    dsimp only
    split
    · exact (heapifyUpF_perm fuel _ _).trans (Vector.swap_perm ..)
    · exact .refl _

/-- Sifting down permutes the elements. -/
theorem heapifyDownF_perm : ∀ (fuel : Nat) {sz : Nat} (a : Vector α sz) (i : Fin sz),
    (heapifyDownF fuel a i).Perm a
  | 0, _, _, _ => .refl _
  | fuel + 1, _, a, i => by
    rw [heapifyDownF]
    split
    · exact .refl _
    · split
      · exact (heapifyDownF_perm fuel _ _).trans (Vector.swap_perm ..)
      · exact .refl _

/-- A well-formed vector makes a well-formed heap. -/
theorem wf_of_topDown {sz : Nat} {v : Vector α sz} (h : WF.TopDown v) : WF ⟨v.toArray⟩ :=
  WF.of_topDown h

end Batteries.BinaryHeap

/-! ### Heaps whose order changes -/

namespace Batteries.BinaryHeap

variable {α : Type u}

/-- **A heap stays a heap in another order**: if every comparison `a[k] ≥ a[j]` in the order `o₁`
holds in the order `o₂`, a heap for `o₁` is one for `o₂`. -/
theorem topDown_of_isGE {o₁ o₂ : Ord α} {sz : Nat} {a : Vector α sz}
    (h : ∀ k j : Fin sz, (@compare α o₁ a[k] a[j]).isGE → (@compare α o₂ a[k] a[j]).isGE)
    (hwf : @WF.TopDown α sz o₁ a) : @WF.TopDown α sz o₂ a := fun i =>
  ⟨fun hl => h i ⟨_, hl⟩ ((hwf i).1 hl), fun hr => h i ⟨_, hr⟩ ((hwf i).2 hr)⟩

/-- **Sifting up after the order changed at one element**: if `a` is a heap for the order `o₁`,
and every comparison `a[k] ≥ a[j]` in `o₁` with `j ≠ i` holds in the order `o₂` (as when the key
of `a[i]` alone grew), sifting `a[i]` up in `o₂` gives a heap for `o₂`. -/
theorem topDown_heapifyUp_of_isGE {o₁ o₂ : Ord α} [h₁ : @Std.TransOrd α o₁]
    [h₂ : @Std.TransOrd α o₂] {sz : Nat} {a : Vector α sz} {i : Fin sz}
    (h : ∀ k j : Fin sz, j ≠ i →
      (@compare α o₁ a[k] a[j]).isGE → (@compare α o₂ a[k] a[j]).isGE)
    (hwf : @WF.TopDown α sz o₁ a) : @WF.TopDown α sz o₂ (@heapifyUp α sz o₂ a i) := by
  have hbu := (@WF.TopDown.iff_bottomUp α sz o₁ a).1 hwf
  let _ := o₂
  refine heapifyUp_topDown (fun j hj hpos => ?_) ?_
  · exact h ⟨_, by omega⟩ j (Ne.symm hj) (hbu j hpos)
  · -- the parent of `i` is at least `a[i]`, which is at least its children
    have hpi : (@compare α o₁ a[(i.val - 1) / 2] a[i]).isGE := by
      by_cases hi : i.val = 0
      · have : (i.val - 1) / 2 = i.val := by omega
        simp only [this, Fin.getElem_fin]
        let _ := o₁
        rw [Std.ReflOrd.compare_self]; rfl
      · exact hbu i (by omega)
    obtain ⟨hl, hr⟩ := hwf i
    constructor
    · intro hl'
      refine h ⟨_, by omega⟩ ⟨_, hl'⟩
        (fun e => by have := congrArg Fin.val e; simp at this; omega) ?_
      exact @Std.TransOrd.isGE_trans α o₁ h₁ _ _ _ hpi (hl hl')
    · intro hr'
      refine h ⟨_, by omega⟩ ⟨_, hr'⟩
        (fun e => by have := congrArg Fin.val e; simp at this; omega) ?_
      exact @Std.TransOrd.isGE_trans α o₁ h₁ _ _ _ hpi (hr hr')

end Batteries.BinaryHeap
