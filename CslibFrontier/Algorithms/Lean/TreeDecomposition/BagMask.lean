/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.TreeDecomposition.Rooted
public import Mathlib.Data.Finset.Sort

/-!
# Subsets of a bag as bit masks

Executable dynamic programs over a tree decomposition index the subsets of a bag by bit masks.
Given an ordering `L : List V` of a bag, `ofMask L m` is the subset whose `i`-th entry is selected
by bit `i` of `m`, and `toMask L S` is the mask of `S`. When `L` has no repetitions these are
inverse bijections between `Finset.range (2 ^ L.length)` and the subsets of `L.toFinset`.

The library has other mask encodings: `Cslib.Algorithms.Lean.Yates.maskSet` and
`Cslib.Algorithms.MatrixMultiplication.Schonhage.MaskTable.maskSet` for subsets of `Fin n`,
`Cslib.Complexity.maskSelect` for a list of Boolean selectors, and Mathlib's `Nat.bitIndices`.
None of them maps numeric masks to subsets of an arbitrary list of vertices by the recursion on
its head that the scan helpers below follow, so the encoding is defined here.

The module also provides the pure scan helpers that executable programs run on masks: membership
by a linear scan of a bag, the parent-bag mask of a child subset, its restriction, the weight of
the entries that are forgotten, and an independence test. Their values are specified against
`ofMask`/`toMask`, while machine-level running-time bounds live in
`CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet`.

`SimpleGraph.RootedTreeDecomposition` stores its bags as `Finset`s, which have no executable
order. `IsBagOrder R L` states that `L i` lists the vertices of `R.bag i` without repetition, and
`sortedBags R` is such an ordering for a linearly ordered vertex type.

## Main definitions

* `Cslib.Algorithms.Lean.TreeDecomposition.ofMask`: the subset of a bag list selected by a mask.
* `Cslib.Algorithms.Lean.TreeDecomposition.toMask`: the mask of a subset.
* `Cslib.Algorithms.Lean.TreeDecomposition.memBag`, `selMemMask`, `keyMask`, `restrictMask`,
  `forgetWeight`, `noAdjMask`, `indepMask`: executable scan helpers on masks.
* `Cslib.Algorithms.Lean.TreeDecomposition.IsBagOrder`: an ordering of the bags of a rooted
  decomposition.
* `Cslib.Algorithms.Lean.TreeDecomposition.sortedBags`: the sorted ordering of the bags.

## Main results

* `Cslib.Algorithms.Lean.TreeDecomposition.ofMask_toMask`,
  `Cslib.Algorithms.Lean.TreeDecomposition.toMask_ofMask`,
  `Cslib.Algorithms.Lean.TreeDecomposition.powerset_toFinset_eq_image`: the bijection between
  masks and subsets.
* `Cslib.Algorithms.Lean.TreeDecomposition.keyMask_eq_toMask`, `restrictMask_eq_toMask`,
  `forgetWeight_eq_sum`, `indepMask_eq_true_iff`: specifications of the mask helpers.
* `Cslib.Algorithms.Lean.TreeDecomposition.isBagOrder_sortedBags`: `sortedBags` is an ordering of
  the bags.
-/

public section

namespace Cslib.Algorithms.Lean.TreeDecomposition

open SimpleGraph

/-! ### Subsets of a bag as bit masks -/

section Mask

variable {V : Type*} [DecidableEq V]

/-- The subset of the list `L` selected by the bit mask `m`: bit `i` of `m` selects `L[i]`. -/
def ofMask : List V → ℕ → Finset V
  | [], _ => ∅
  | v :: L, m => if m % 2 = 1 then insert v (ofMask L (m / 2)) else ofMask L (m / 2)

/-- The bit mask of the elements of `L` that lie in `S`: bit `i` is set when `L[i] ∈ S`. -/
def toMask : List V → Finset V → ℕ
  | [], _ => 0
  | v :: L, S => (if v ∈ S then 1 else 0) + 2 * toMask L S

theorem ofMask_cons (v : V) (L : List V) (m : ℕ) :
    ofMask (v :: L) m = if m % 2 = 1 then insert v (ofMask L (m / 2)) else ofMask L (m / 2) := by
  rw [ofMask]

theorem toMask_cons (v : V) (L : List V) (S : Finset V) :
    toMask (v :: L) S = (if v ∈ S then 1 else 0) + 2 * toMask L S := by
  rw [toMask]

theorem mem_ofMask_cons {v x : V} {L : List V} {m : ℕ} :
    x ∈ ofMask (v :: L) m ↔ (m % 2 = 1 ∧ x = v) ∨ x ∈ ofMask L (m / 2) := by
  rw [ofMask_cons]
  split_ifs with h <;> simp [h]

theorem ofMask_subset (L : List V) (m : ℕ) : ofMask L m ⊆ L.toFinset := by
  induction L generalizing m with
  | nil => exact Finset.empty_subset _
  | cons v L ih =>
    intro x hx
    rw [mem_ofMask_cons] at hx
    rw [List.toFinset_cons, Finset.mem_insert]
    rcases hx with ⟨-, rfl⟩ | hx
    · exact .inl rfl
    · exact .inr (ih _ hx)

theorem toMask_lt (L : List V) (S : Finset V) : toMask L S < 2 ^ L.length := by
  induction L with
  | nil => simp [toMask]
  | cons v L ih =>
    simp only [toMask, List.length_cons, pow_succ]
    split_ifs <;> omega

theorem toMask_congr {L : List V} {S T : Finset V} (h : ∀ x ∈ L, x ∈ S ↔ x ∈ T) :
    toMask L S = toMask L T := by
  induction L with
  | nil => rfl
  | cons v L ih =>
    simp only [toMask]
    rw [ih fun x hx => h x (List.mem_cons_of_mem v hx)]
    by_cases hv : v ∈ S
    · rw [ite_eq_left hv, ite_eq_left ((h v List.mem_cons_self).1 hv)]
    · rw [ite_eq_right hv, ite_eq_right fun hT => hv ((h v List.mem_cons_self).2 hT)]

theorem ofMask_toMask (L : List V) (S : Finset V) : ofMask L (toMask L S) = S ∩ L.toFinset := by
  induction L with
  | nil => simp [ofMask]
  | cons v L ih =>
    have hdiv : ((if v ∈ S then 1 else 0) + 2 * toMask L S) / 2 = toMask L S := by
      split_ifs <;> omega
    by_cases hv : v ∈ S
    · have hmod : ((if v ∈ S then 1 else 0) + 2 * toMask L S) % 2 = 1 := by grind
      simp only [toMask, ofMask, hmod, hdiv, ih, ite_true, List.toFinset_cons]
      rw [Finset.inter_insert_of_mem hv]
    · have hmod : ¬((if v ∈ S then 1 else 0) + 2 * toMask L S) % 2 = 1 := by grind
      simp only [toMask, ofMask, hmod, hdiv, ih, ite_false, List.toFinset_cons]
      rw [Finset.inter_insert_of_notMem hv]

theorem toMask_ofMask {L : List V} (hL : L.Nodup) {m : ℕ} (hm : m < 2 ^ L.length) :
    toMask L (ofMask L m) = m := by
  induction L generalizing m with
  | nil =>
    rw [List.length_nil, pow_zero] at hm
    rw [toMask]
    omega
  | cons v L ih =>
    rw [List.nodup_cons] at hL
    have hm' : m / 2 < 2 ^ L.length := by grind
    have hrest : toMask L (ofMask (v :: L) m) = toMask L (ofMask L (m / 2)) := by
      refine toMask_congr fun x hx => ?_
      have hxv : x ≠ v := fun h => hL.1 (h ▸ hx)
      rw [mem_ofMask_cons]
      simp [hxv]
    have hv : v ∈ ofMask (v :: L) m ↔ m % 2 = 1 := by
      have hvL : v ∉ ofMask L (m / 2) := fun h => hL.1 (List.mem_toFinset.1 (ofMask_subset L _ h))
      rw [mem_ofMask_cons]
      simp [hvL]
    rw [toMask_cons, hrest, ih hL.2 hm']
    by_cases h : m % 2 = 1
    · rw [ite_eq_left (hv.2 h)]
      omega
    · rw [ite_eq_right fun h' => h (hv.1 h')]
      omega

theorem toMask_eq_toMask_iff {L : List V} {S T : Finset V} :
    toMask L S = toMask L T ↔ S ∩ L.toFinset = T ∩ L.toFinset := by
  refine ⟨fun h => by rw [← ofMask_toMask, h, ofMask_toMask], fun h => toMask_congr fun x hx => ?_⟩
  have := congrArg (x ∈ ·) h
  simpa [List.mem_toFinset.2 hx] using this

theorem powerset_toFinset_eq_image (L : List V) :
    L.toFinset.powerset = (Finset.range (2 ^ L.length)).image (ofMask L) := by
  ext S
  simp only [Finset.mem_powerset, Finset.mem_image, Finset.mem_range]
  constructor
  · intro hS
    exact ⟨toMask L S, toMask_lt L S, by rw [ofMask_toMask, Finset.inter_eq_left.2 hS]⟩
  · rintro ⟨m, -, rfl⟩
    exact ofMask_subset L m

end Mask

/-! ### Scan helpers on masks -/

section Loops

variable {V : Type*} [DecidableEq V]

/-- Membership test by a linear scan of `L`. -/
@[expose] def memBag (x : V) : List V → Bool
  | [] => false
  | u :: L => decide (x = u) || memBag x L

/-- Membership in the subset of `L` selected by the mask `m`, by a linear scan of `L`. -/
@[expose] def selMemMask (x : V) : List V → ℕ → Bool
  | [], _ => false
  | u :: L, m => (decide (m % 2 = 1) && decide (x = u)) || selMemMask x L (m / 2)

/-- The parent-bag mask of the child subset selected by `t`: for each entry `u` of the parent bag
`LP`, test whether `u` is selected in the child bag `LB`. -/
@[expose] def keyMask (LB : List V) : List V → ℕ → ℕ
  | [], _ => 0
  | u :: LP, t => (if selMemMask u LB t then 1 else 0) + 2 * keyMask LB LP t

/-- The parent-bag mask of `S ∩ B`, where `S` is the parent subset selected by `s` and `B` is the
set of entries of the child bag `LB`. -/
@[expose] def restrictMask (LB : List V) : List V → ℕ → ℕ
  | [], _ => 0
  | u :: LP, s =>
    (if s % 2 = 1 ∧ memBag u LB = true then 1 else 0) + 2 * restrictMask LB LP (s / 2)

/-- The total weight of the entries selected by `t` from the child bag `LB` that are not in the
parent bag `LP`. -/
@[expose] def forgetWeight (w : V → ℕ) (LP : List V) : List V → ℕ → ℕ
  | [], _ => 0
  | u :: LB, t =>
    (if t % 2 = 1 ∧ memBag u LP = false then w u else 0) + forgetWeight w LP LB (t / 2)

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Whether `x` has no neighbour in the subset of `L` selected by `m`. -/
@[expose] def noAdjMask (x : V) : List V → ℕ → Bool
  | [], _ => true
  | u :: L, m => noAdjMask x L (m / 2) && !(decide (m % 2 = 1) && decide (G.Adj x u))

/-- Whether the subset of `L` selected by `m` is independent. -/
@[expose] def indepMask : List V → ℕ → Bool
  | [], _ => true
  | u :: L, m => indepMask L (m / 2) && (!decide (m % 2 = 1) || noAdjMask G u L (m / 2))

end Loops

/-! ### Orderings of the bags -/

section BagOrder

variable {V : Type*} {G : SimpleGraph V} {n : ℕ} [DecidableEq V]

/-- `L` lists the bags of `R`: each `L i` lists the vertices of `R.bag i` without repetition. -/
@[expose] def IsBagOrder (R : G.RootedTreeDecomposition n) (L : Fin (n + 1) → List V) : Prop :=
  ∀ i, (L i).Nodup ∧ (L i).toFinset = R.bag i

instance (R : G.RootedTreeDecomposition n) (L : Fin (n + 1) → List V) :
    Decidable (IsBagOrder R L) :=
  inferInstanceAs (Decidable (∀ i, (L i).Nodup ∧ (L i).toFinset = R.bag i))

/-- The bags of `R` sorted in increasing order. -/
def sortedBags [LinearOrder V] (R : G.RootedTreeDecomposition n) (i : Fin (n + 1)) : List V :=
  (R.bag i).sort

theorem isBagOrder_sortedBags [LinearOrder V] (R : G.RootedTreeDecomposition n) :
    IsBagOrder R (sortedBags R) := fun _ =>
  ⟨Finset.sort_nodup _ _, Finset.sort_toFinset _ _⟩

end BagOrder

/-! ### Specifications of the scan helpers -/

section LoopSpecs

variable {V : Type*} [DecidableEq V]

@[simp]
theorem memBag_eq_decide (x : V) (L : List V) : memBag x L = decide (x ∈ L) := by
  induction L with
  | nil => rfl
  | cons u L ih => simp [memBag, ih, List.mem_cons]

@[simp]
theorem selMemMask_eq_decide (x : V) (L : List V) (m : ℕ) :
    selMemMask x L m = decide (x ∈ ofMask L m) := by
  induction L generalizing m with
  | nil => simp [selMemMask, ofMask]
  | cons u L ih => simp [selMemMask, ih, mem_ofMask_cons]

@[simp]
theorem keyMask_eq_toMask (LB LP : List V) (t : ℕ) :
    keyMask LB LP t = toMask LP (ofMask LB t) := by
  induction LP with
  | nil => rfl
  | cons u LP ih => simp [keyMask, ih, toMask]

theorem restrictMask_eq_toMask (LB : List V) {LP : List V} (hLP : LP.Nodup) (s : ℕ) :
    restrictMask LB LP s = toMask LP (ofMask LP s ∩ LB.toFinset) := by
  induction LP generalizing s with
  | nil => rfl
  | cons u LP ih =>
    obtain ⟨hu, hLP⟩ := List.nodup_cons.1 hLP
    simp only [restrictMask, memBag_eq_decide, ih hLP, decide_eq_true_eq, toMask]
    have hmem : u ∈ ofMask (u :: LP) s ∩ LB.toFinset ↔ s % 2 = 1 ∧ u ∈ LB := by
      rw [Finset.mem_inter, mem_ofMask_cons, List.mem_toFinset]
      constructor
      · rintro ⟨⟨h, -⟩ | h, h'⟩
        · exact ⟨h, h'⟩
        · exact absurd (List.mem_toFinset.1 (ofMask_subset LP _ h)) hu
      · rintro ⟨h, h'⟩
        exact ⟨.inl ⟨h, rfl⟩, h'⟩
    rw [toMask_congr (S := ofMask (u :: LP) s ∩ LB.toFinset)
      (T := ofMask LP (s / 2) ∩ LB.toFinset) fun x hx => ?_]
    · simp only [hmem]
    · have hxu : x ≠ u := fun h => hu (h ▸ hx)
      simp [mem_ofMask_cons, hxu]

theorem forgetWeight_eq_sum (w : V → ℕ) (LP : List V) {LB : List V} (hLB : LB.Nodup) (t : ℕ) :
    forgetWeight w LP LB t = ∑ v ∈ ofMask LB t \ LP.toFinset, w v := by
  induction LB generalizing t with
  | nil => simp [forgetWeight, ofMask]
  | cons u LB ih =>
    obtain ⟨hu, hLB⟩ := List.nodup_cons.1 hLB
    simp only [forgetWeight, memBag_eq_decide, ih hLB]
    have huA : u ∉ ofMask LB (t / 2) \ LP.toFinset := fun h =>
      hu (List.mem_toFinset.1 (ofMask_subset LB _ (Finset.mem_sdiff.1 h).1))
    rw [ofMask_cons]
    by_cases ht : t % 2 = 1 <;> by_cases huP : u ∈ LP
    · simp [ht, huP, Finset.insert_sdiff_of_mem _ (List.mem_toFinset.2 huP)]
    · rw [ite_eq_left ht, Finset.insert_sdiff_of_notMem _ (fun h => huP (List.mem_toFinset.1 h)),
        Finset.sum_insert huA]
      simp [ht, huP]
    · simp [ht]
    · simp [ht]

theorem noAdjMask_eq_true_iff (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) (L : List V)
    (m : ℕ) : noAdjMask G x L m = true ↔ ∀ y ∈ ofMask L m, ¬G.Adj x y := by
  induction L generalizing m with
  | nil => simp [noAdjMask, ofMask]
  | cons u L ih =>
    simp only [noAdjMask, Bool.and_eq_true, ih, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not, mem_ofMask_cons]
    constructor
    · rintro ⟨h, h'⟩ y (⟨hm, rfl⟩ | hy)
      · rcases h' with h' | h'
        · exact absurd hm h'
        · exact h'
      · exact h y hy
    · intro h
      refine ⟨fun y hy => h y (.inr hy), ?_⟩
      by_cases hm : m % 2 = 1
      · exact .inr (h u (.inl ⟨hm, rfl⟩))
      · exact .inl hm

theorem indepMask_eq_true_iff (G : SimpleGraph V) [DecidableRel G.Adj] (L : List V) (m : ℕ) :
    indepMask G L m = true ↔ G.IsIndepSet (↑(ofMask L m) : Set V) := by
  induction L generalizing m with
  | nil => simp [indepMask, ofMask]
  | cons u L ih =>
    simp only [indepMask, Bool.and_eq_true, ih, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, noAdjMask_eq_true_iff]
    rw [ofMask_cons]
    by_cases hm : m % 2 = 1
    · rw [ite_eq_left hm, Finset.coe_insert]
      simp only [isIndepSet_iff]
      rw [Set.pairwise_insert]
      constructor
      · rintro ⟨h, h' | h'⟩
        · exact absurd hm h'
        · exact ⟨h, fun b hb _ => ⟨h' b hb, fun hba => h' b hb hba.symm⟩⟩
      · rintro ⟨h, h'⟩
        refine ⟨h, .inr fun y hy hadj => ?_⟩
        exact (h' y hy (G.ne_of_adj hadj)).1 hadj
    · simp [hm]

end LoopSpecs

end Cslib.Algorithms.Lean.TreeDecomposition
