/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.CrossingCover.CoverLifting
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Alternating non-backtracking walk bound for vertex covers of subcubic graphs

Let `D` be a finite simple graph of maximum degree at most `3`, and let
`B = {v | D.degree v = 3}` be its set of degree-`3` vertices. For every **odd** truncation order
`J ≥ 1`, we prove the deterministic inequality

```text
2 * simpleVertexCover D
  ≤ ∑ j ∈ Icc 1 J, (-1) ^ (j + 1) * dirNBCount D j + altErrConst J * #B,
```

where `dirNBCount D j` counts the **directed non-backtracking walks** of length `j` in `D`, and
`altErrConst J` depends only on `J` (`2 + ∑_{j ∈ Icc 1 J, Even j} (j + 1) * 3 * 2 ^ (j - 1)`).

## Proof overview

1. **Degree `≤ 2` (`two_mul_simpleVertexCover_le_alternating_of_maxDeg_two`):**
   We induct on the number of edges of `D`.
   - If `D` has no edges, both sides are `0`.
   - If `D` has a vertex of degree `1`, following the unique non-backtracking path from it until the
     opposite degree-`1` endpoint produces a closed path component `P` on `r ≥ 2` vertices. Both
     sides split additively across `P` and its complement (`dirNBCount_restrict_add`), so it remains
     to verify the alternating identity on a single path: every `P_r` (`r` vertices) admits a vertex
     cover of size `r / 2` (the odd-indexed vertices) and has `2 * (r - j)` directed
     non-backtracking walks of length `j`, so for odd `J = 2m + 1` the alternating sum equals
     `2 * (r / 2)` when `r - 1 ≤ J` and `2 * (r - 1 - m)` when `r - 1 > J`, always at least
     `2 * (r / 2)`.
   - Otherwise every vertex of `D` has degree `0` or `2`. Letting `A = {v | D.degree v = 2}`, every
     directed non-backtracking walk of length `j ≥ 1` extends uniquely by one step (choosing the
     unique neighbor distinct from the predecessor), so `dirNBCount D j = 2 * #A` for *all* `j ≥ 1`.
     For any odd `J`, the alternating sum telescopes directly to `2 * #A ≥ 2 * simpleVertexCover D`,
     since `A` itself covers all edges of `D`.

2. **Deleting degree-`3` vertices (`two_mul_simpleVertexCover_le_alternating`):**
   Removing all edges incident to `B = {v | D.degree v = 3}` leaves a subgraph `D'` of maximum
   degree at most `2` with `simpleVertexCover D ≤ simpleVertexCover D' + #B`. For odd `j`,
   `dirNBCount D' j ≤ dirNBCount D j` is a drop of the right sign. For even `j`, every walk in
   `D` missing from `D'` visits some `v ∈ B` at some index `s : Fin (j + 1)`, and counting outward
   from `s` yields at most `3 * 2 ^ (j - 1)` non-backtracking walks per `(v, s)`.

## Main definitions

* `Cslib.Circuits.Frontier.CrossingCover.IsSimpleVertexCover`: vertex cover of a `SimpleGraph`.
* `Cslib.Circuits.Frontier.CrossingCover.simpleVertexCover`: minimum vertex cover cardinality.
* `Cslib.Circuits.Frontier.CrossingCover.crossingGraph`: bipartite crossing subgraph of `(H, b)`.
* `Cslib.Circuits.Frontier.CrossingCover.dirNBCount`: count of directed non-backtracking walks.
* `Cslib.Circuits.Frontier.CrossingCover.altErrConst`: explicit error multiplier for degree-`3`
  vertices in the truncated alternating sum.

## Main results

* `Cslib.Circuits.Frontier.CrossingCover.two_mul_simpleVertexCover_le_alternating_of_maxDeg_two`
* `Cslib.Circuits.Frontier.CrossingCover.two_mul_simpleVertexCover_le_alternating`
-/

public section

namespace Cslib.Circuits.Frontier.CrossingCover

open Finset

section BasicDefs

variable {V : Type*}

/-- A `Finset V` is a vertex cover of a simple graph `D` if every edge of `D` has at least one
endpoint in `C`. -/
def IsSimpleVertexCover (D : SimpleGraph V) (C : Finset V) : Prop :=
  ∀ u v : V, D.Adj u v → u ∈ C ∨ v ∈ C

/-- Minimum vertex-cover cardinality of a finite simple graph `D`. -/
noncomputable def simpleVertexCover (D : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ C : Finset V, IsSimpleVertexCover D C ∧ C.card = k}

theorem simpleVertexCover_le_card {D : SimpleGraph V} {C : Finset V}
    (hC : IsSimpleVertexCover D C) :
    simpleVertexCover D ≤ C.card :=
  Nat.sInf_le ⟨C, hC, rfl⟩

theorem exists_simpleVertexCover_eq [Finite V] (D : SimpleGraph V) :
    ∃ C : Finset V, IsSimpleVertexCover D C ∧ C.card = simpleVertexCover D := by
  classical
  have hne : {k : ℕ | ∃ C : Finset V, IsSimpleVertexCover D C ∧ C.card = k}.Nonempty := by
    have := Fintype.ofFinite V
    exact ⟨(univ : Finset V).card, univ, fun _ _ _ => Or.inl (mem_univ _), rfl⟩
  exact Nat.sInf_mem hne

/-- The bipartite crossing subgraph of `H` induced by a bipartition `b : V → Bool`: retains the
edges of `H` whose endpoints receive distinct labels under `b`. -/
@[expose] def crossingGraph (H : SimpleGraph V) (b : V → Bool) : SimpleGraph V where
  Adj u v := H.Adj u v ∧ b u ≠ b v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

theorem crossingGraph_adj_iff (H : SimpleGraph V) (b : V → Bool) (u v : V) :
    (crossingGraph H b).Adj u v ↔ H.Adj u v ∧ b u ≠ b v :=
  Iff.rfl

/-- Restrict `D` to edges with both endpoints inside a `Finset V`. -/
private def restrictEdges (D : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj u v := D.Adj u v ∧ u ∈ S ∧ v ∈ S
  symm := ⟨fun _ _ ⟨hadj, hu, hv⟩ => ⟨hadj.symm, hv, hu⟩⟩
  loopless := ⟨fun v h => D.loopless.irrefl v h.1⟩

/-- A `Finset V` is a union of connected components of `D` if no edge crosses its boundary. -/
private def IsEdgeClosed (D : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u v : V, D.Adj u v → u ∈ S → v ∈ S

private theorem isEdgeClosed_compl {D : SimpleGraph V} {S : Finset V}
    (hS : IsEdgeClosed D S) (u v : V) (huv : D.Adj u v) (hu : u ∉ S) : v ∉ S :=
  fun hv => hu (hS v u huv.symm hv)

/-- The number of directed non-backtracking walks of length `j` in `D`. -/
@[expose] noncomputable def dirNBCount [Fintype V] (D : SimpleGraph V) (j : ℕ) : ℕ :=
  open Classical in (univ.filter fun w : Fin (j + 1) → V => IsNBWalk D j w).card

/-- The finset of degree-`3` vertices of a simple graph `D`. -/
@[expose] noncomputable def degThreeSet [Fintype V] (D : SimpleGraph V) : Finset V :=
  open Classical in univ.filter fun v => D.degree v = 3

/-- Explicit constant multiplying `#(degThreeSet D)` in the alternating-sum bound for odd `J`. -/
@[expose] def altErrConst (J : ℕ) : ℕ :=
  2 + ∑ j ∈ Icc 1 J, if Even j then (j + 1) * 3 * 2 ^ (j - 1) else 0

end BasicDefs

section Arithmetic

private lemma path_alt_sum_aux (r : ℕ) :
    ∀ m : ℕ,
      ∑ j ∈ Icc 1 (2 * m + 1), (-1 : ℤ) ^ (j + 1) * ((r - j : ℕ) : ℤ) =
        if r ≤ 2 * m + 2 then ((r / 2 : ℕ) : ℤ) else ((r - 1 - m : ℕ) : ℤ) := by
  intro m
  induction m with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, Icc_self, sum_singleton]
    have h1 : ((-1 : ℤ) ^ (1 + 1)) = 1 := by norm_num
    rw [h1, one_mul]
    split_ifs with hr <;> omega
  | succ m ih =>
    have hsplit : Icc 1 (2 * (m + 1) + 1) =
        insert (2 * m + 3) (insert (2 * m + 2) (Icc 1 (2 * m + 1))) := by
      ext j; simp only [mem_Icc, mem_insert]; omega
    have hnot1 : 2 * m + 3 ∉ insert (2 * m + 2) (Icc 1 (2 * m + 1)) := by
      simp only [mem_insert, mem_Icc]; omega
    have hnot2 : 2 * m + 2 ∉ Icc 1 (2 * m + 1) := by
      simp only [mem_Icc]; omega
    rw [hsplit, sum_insert hnot1, sum_insert hnot2, ih]
    have hs1 : (-1 : ℤ) ^ (2 * m + 3 + 1) = 1 := by
      have : Even (2 * m + 3 + 1) := ⟨m + 2, by omega⟩
      exact Even.neg_one_pow this
    have hs2 : (-1 : ℤ) ^ (2 * m + 2 + 1) = -1 := by
      have : Odd (2 * m + 2 + 1) := ⟨m + 1, by omega⟩
      exact Odd.neg_one_pow this
    rw [hs1, hs2, one_mul, neg_one_mul]
    split_ifs with h1 h2 <;> omega

/-- Alternating sum of directed non-backtracking walk counts on a path of `r` vertices (`r ≥ 1`)
always dominates `2 * (r / 2)` for every odd truncation `J`. -/
private theorem path_alt_sum_ge (r J : ℕ) (hJ : Odd J) :
    (2 * (r / 2) : ℤ) ≤
      ∑ j ∈ Icc 1 J, (-1 : ℤ) ^ (j + 1) * (2 * ((r - j : ℕ) : ℤ)) := by
  obtain ⟨m, rfl⟩ := hJ
  have hfac : ∑ j ∈ Icc 1 (2 * m + 1), (-1 : ℤ) ^ (j + 1) * (2 * ((r - j : ℕ) : ℤ)) =
      2 * ∑ j ∈ Icc 1 (2 * m + 1), (-1 : ℤ) ^ (j + 1) * ((r - j : ℕ) : ℤ) := by
    rw [mul_sum]
    refine sum_congr rfl fun j _ => by ring
  rw [hfac, path_alt_sum_aux r m]
  split_ifs with hr <;> omega

private lemma const_alt_sum_odd (c : ℤ) (J : ℕ) (hJ : Odd J) :
    ∑ j ∈ Icc 1 J, (-1 : ℤ) ^ (j + 1) * c = c := by
  obtain ⟨m, rfl⟩ := hJ
  induction m with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, Icc_self, sum_singleton]
    norm_num
  | succ m ih =>
    have hsplit : Icc 1 (2 * (m + 1) + 1) =
        insert (2 * m + 3) (insert (2 * m + 2) (Icc 1 (2 * m + 1))) := by
      ext j; simp only [mem_Icc, mem_insert]; omega
    have hnot1 : 2 * m + 3 ∉ insert (2 * m + 2) (Icc 1 (2 * m + 1)) := by
      simp only [mem_insert, mem_Icc]; omega
    have hnot2 : 2 * m + 2 ∉ Icc 1 (2 * m + 1) := by
      simp only [mem_Icc]; omega
    rw [hsplit, sum_insert hnot1, sum_insert hnot2, ih]
    have hs1 : (-1 : ℤ) ^ (2 * m + 3 + 1) = 1 := Even.neg_one_pow ⟨m + 2, by omega⟩
    have hs2 : (-1 : ℤ) ^ (2 * m + 2 + 1) = -1 := Odd.neg_one_pow ⟨m + 1, by omega⟩
    rw [hs1, hs2]; ring

end Arithmetic

section ComponentSplitting

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
private lemma restrictEdges_degree_le (D : SimpleGraph V) (S : Finset V) (v : V) :
    open Classical in (restrictEdges D S).degree v ≤ D.degree v := by
  classical
  simp only [SimpleGraph.degree]
  refine card_le_card fun u hu => ?_
  rw [SimpleGraph.mem_neighborFinset] at hu ⊢
  exact hu.1

omit [DecidableEq V] in
private lemma restrictEdges_edgeFinset_sub (D : SimpleGraph V) (S : Finset V) :
    open Classical in (restrictEdges D S).edgeFinset ⊆ D.edgeFinset := by
  classical
  intro e he
  rw [SimpleGraph.mem_edgeFinset] at he ⊢
  induction e using Sym2.ind with
  | _ u v => exact he.1

private lemma restrictEdges_edgeFinset_lt {D : SimpleGraph V} {S : Finset V}
    {u v : V} (huv : D.Adj u v) (hu : u ∈ S) :
    open Classical in (restrictEdges D Sᶜ).edgeFinset.card < D.edgeFinset.card := by
  classical
  refine card_lt_card ⟨restrictEdges_edgeFinset_sub D Sᶜ, ?_⟩
  rw [not_subset]
  refine ⟨s(u, v), SimpleGraph.mem_edgeFinset.mpr huv, fun h => ?_⟩
  have h' : (restrictEdges D Sᶜ).Adj u v := SimpleGraph.mem_edgeFinset.mp h
  exact (mem_compl.mp h'.2.1) hu

private lemma simpleVertexCover_split {D : SimpleGraph V} {S : Finset V}
    (hS : IsEdgeClosed D S) :
    simpleVertexCover D ≤ simpleVertexCover (restrictEdges D S) +
      simpleVertexCover (restrictEdges D Sᶜ) := by
  obtain ⟨C₁, hC₁, hc₁⟩ := exists_simpleVertexCover_eq (restrictEdges D S)
  obtain ⟨C₂, hC₂, hc₂⟩ := exists_simpleVertexCover_eq (restrictEdges D Sᶜ)
  have hcov : IsSimpleVertexCover D (C₁ ∪ C₂) := by
    intro u v huv
    by_cases hu : u ∈ S
    · have hv : v ∈ S := hS u v huv hu
      rcases hC₁ u v ⟨huv, hu, hv⟩ with h | h
      · exact Or.inl (mem_union_left C₂ h)
      · exact Or.inr (mem_union_left C₂ h)
    · have hv : v ∉ S := isEdgeClosed_compl hS u v huv hu
      rcases hC₂ u v ⟨huv, mem_compl.mpr hu, mem_compl.mpr hv⟩ with h | h
      · exact Or.inl (mem_union_right C₁ h)
      · exact Or.inr (mem_union_right C₁ h)
  calc simpleVertexCover D ≤ (C₁ ∪ C₂).card := simpleVertexCover_le_card hcov
    _ ≤ C₁.card + C₂.card := card_union_le C₁ C₂
    _ = simpleVertexCover (restrictEdges D S) + simpleVertexCover (restrictEdges D Sᶜ) := by
        rw [hc₁, hc₂]

private lemma dirNBCount_split {D : SimpleGraph V} {S : Finset V}
    (hS : IsEdgeClosed D S) {j : ℕ} (hj : 1 ≤ j) :
    dirNBCount D j = dirNBCount (restrictEdges D S) j +
      dirNBCount (restrictEdges D Sᶜ) j := by
  classical
  let W : Finset (Fin (j + 1) → V) := univ.filter fun w => IsNBWalk D j w
  let W₁ : Finset (Fin (j + 1) → V) :=
    univ.filter fun w => IsNBWalk (restrictEdges D S) j w
  let W₂ : Finset (Fin (j + 1) → V) :=
    univ.filter fun w => IsNBWalk (restrictEdges D Sᶜ) j w
  have hmem_all : ∀ w, IsNBWalk D j w →
      (w 0 ∈ S → ∀ i : Fin (j + 1), w i ∈ S) ∧
        (w 0 ∉ S → ∀ i : Fin (j + 1), w i ∉ S) := by
    intro w hw
    constructor
    · intro h0 i
      induction i using Fin.induction with
      | zero => exact h0
      | succ k ih => exact hS _ _ (hw.1 k) ih
    · intro h0 i
      induction i using Fin.induction with
      | zero => exact h0
      | succ k ih => exact isEdgeClosed_compl hS _ _ (hw.1 k) ih
  have hdisj : Disjoint W₁ W₂ := disjoint_left.mpr fun w h1 h2 => by
    have h1' : IsNBWalk (restrictEdges D S) j w := (mem_filter.mp h1).2
    have h2' : IsNBWalk (restrictEdges D Sᶜ) j w := (mem_filter.mp h2).2
    have hi : 0 < j := hj
    have hs1 := (h1'.1 ⟨0, hi⟩).2.1
    have hs2 := (h2'.1 ⟨0, hi⟩).2.1
    exact (mem_compl.mp hs2) hs1
  have hunion : W = W₁ ∪ W₂ := by
    ext w
    simp only [W, W₁, W₂, mem_union, mem_filter, mem_univ, true_and]
    constructor
    · intro hw
      by_cases h0 : w 0 ∈ S
      · left
        have hstay := (hmem_all w hw).1 h0
        exact ⟨fun i => ⟨hw.1 i, hstay i.castSucc, hstay i.succ⟩, hw.2⟩
      · right
        have hstay := (hmem_all w hw).2 h0
        exact ⟨fun i => ⟨hw.1 i, mem_compl.mpr (hstay i.castSucc),
          mem_compl.mpr (hstay i.succ)⟩, hw.2⟩
    · rintro (hw | hw)
      · exact ⟨fun i => (hw.1 i).1, hw.2⟩
      · exact ⟨fun i => (hw.1 i).1, hw.2⟩
  change W.card = W₁.card + W₂.card
  rw [hunion, card_union_of_disjoint hdisj]

end ComponentSplitting

section TwoRegular

variable {V : Type*} [Fintype V]

private lemma dirNBCount_one (D : SimpleGraph V) :
    open Classical in dirNBCount D 1 = ∑ v : V, D.degree v := by
  classical
  have hbij : (univ.filter fun w : Fin 2 → V => IsNBWalk D 1 w).card =
      ∑ v : V, (D.neighborFinset v).card := by
    rw [← card_sigma]
    refine Finset.card_bij (fun w _ => ⟨w 0, w 1⟩) ?_ ?_ ?_
    · intro w hw
      have hnb := (mem_filter.mp hw).2
      refine mem_sigma.mpr ⟨mem_univ _, (D.mem_neighborFinset _ _).mpr (hnb.1 ⟨0, by omega⟩)⟩
    · intro w₁ _ w₂ _ heq
      ext i; fin_cases i
      · exact congrArg Sigma.fst heq
      · simpa using congrArg Sigma.snd heq
    · intro ⟨u, v⟩ h
      have huv : D.Adj u v := (D.mem_neighborFinset _ _).mp (mem_sigma.mp h).2
      refine ⟨fun i : Fin 2 => if i = 0 then u else v,
        mem_filter.mpr ⟨mem_univ _, fun i => ?_, fun i hi => by omega⟩, rfl⟩
      fin_cases i; exact huv
  change (univ.filter fun w : Fin 2 → V => IsNBWalk D 1 w).card = _
  rw [hbij]; rfl

private lemma dirNBCount_succ_of_deg_zero_or_two (D : SimpleGraph V)
    (h02 : ∀ v : V, open Classical in D.degree v = 0 ∨ D.degree v = 2)
    (j : ℕ) (hj : 1 ≤ j) :
    dirNBCount D (j + 1) = dirNBCount D j := by
  classical
  change (univ.filter fun w : Fin (j + 2) → V => IsNBWalk D (j + 1) w).card =
    (univ.filter fun w : Fin (j + 1) → V => IsNBWalk D j w).card
  refine card_bij (fun w _ => fun i : Fin (j + 1) => w i.castSucc) ?_ ?_ ?_
  · intro w hw
    have hnb := (mem_filter.mp hw).2
    refine mem_filter.mpr ⟨mem_univ _, fun i => hnb.1 i.castSucc, fun i hi => ?_⟩
    exact hnb.2 i (by omega)
  · intro w₁ hw₁ w₂ hw₂ heq
    have h1 := (mem_filter.mp hw₁).2
    have h2 := (mem_filter.mp hw₂).2
    have hagree : ∀ i : Fin (j + 1), w₁ i.castSucc = w₂ i.castSucc := fun i => congrFun heq i
    have hu : w₁ ⟨j, by omega⟩ = w₂ ⟨j, by omega⟩ := hagree ⟨j, by omega⟩
    have hp : w₁ ⟨j - 1, by omega⟩ = w₂ ⟨j - 1, by omega⟩ := hagree ⟨j - 1, by omega⟩
    have hlast : w₁ ⟨j + 1, by omega⟩ = w₂ ⟨j + 1, by omega⟩ := by
      set u := w₁ ⟨j, by omega⟩
      set p := w₁ ⟨j - 1, by omega⟩
      have hadj_p : D.Adj u p := by
        have := (h1.1 ⟨j - 1, by omega⟩).symm
        simpa [u, p, show j - 1 + 1 = j by omega] using this
      have hdeg2 : D.degree u = 2 := by
        rcases h02 u with h0 | h2d
        · have hmem : p ∈ D.neighborFinset u := (D.mem_neighborFinset _ _).mpr hadj_p
          have hpos : 0 < (D.neighborFinset u).card := card_pos.mpr ⟨p, hmem⟩
          rw [SimpleGraph.degree] at h0; omega
        · exact h2d
      have h1a : w₁ ⟨j + 1, by omega⟩ ∈ (D.neighborFinset u).erase p := by
        refine mem_erase.mpr ⟨?_, (D.mem_neighborFinset _ _).mpr (h1.1 ⟨j, by omega⟩)⟩
        have hne := h1.2 (j - 1) (by omega)
        simpa [p, show j - 1 + 2 = j + 1 by omega] using hne.symm
      have h2a : w₂ ⟨j + 1, by omega⟩ ∈ (D.neighborFinset u).erase p := by
        refine mem_erase.mpr ⟨?_, (D.mem_neighborFinset _ _).mpr ?_⟩
        · have hne := h2.2 (j - 1) (by omega)
          rw [← hp] at hne
          simpa [p, show j - 1 + 2 = j + 1 by omega] using hne.symm
        · rw [hu]; exact h2.1 ⟨j, by omega⟩
      have hcard1 : ((D.neighborFinset u).erase p).card = 1 := by
        rw [card_erase_of_mem ((D.mem_neighborFinset _ _).mpr hadj_p)]
        rw [SimpleGraph.degree] at hdeg2; omega
      obtain ⟨q, hq⟩ := card_eq_one.mp hcard1
      rw [hq, mem_singleton] at h1a h2a
      exact h1a.trans h2a.symm
    ext i
    by_cases hlt : i.val < j + 1
    · exact hagree ⟨i.val, hlt⟩
    · have hi_lt : i.val < j + 2 := i.isLt
      have hieq : i = ⟨j + 1, by omega⟩ := Fin.ext (show i.val = j + 1 by omega)
      rw [hieq]; exact hlast
  · intro w' hw'
    have hnb := (mem_filter.mp hw').2
    set u := w' ⟨j, by omega⟩
    set p := w' ⟨j - 1, by omega⟩
    have hadj_p : D.Adj u p := by
      have := (hnb.1 ⟨j - 1, by omega⟩).symm
      simpa [u, p, show j - 1 + 1 = j by omega] using this
    have hdeg2 : D.degree u = 2 := by
      rcases h02 u with h0 | h2d
      · have hpos : 0 < (D.neighborFinset u).card :=
          card_pos.mpr ⟨p, (D.mem_neighborFinset _ _).mpr hadj_p⟩
        rw [SimpleGraph.degree] at h0; omega
      · exact h2d
    have hcard1 : ((D.neighborFinset u).erase p).card = 1 := by
      rw [card_erase_of_mem ((D.mem_neighborFinset _ _).mpr hadj_p)]
      rw [SimpleGraph.degree] at hdeg2; omega
    obtain ⟨q, hq⟩ := card_pos.mp (by omega : 0 < ((D.neighborFinset u).erase p).card)
    have hqp : q ≠ p := (mem_erase.mp hq).1
    have hqu : D.Adj u q := (D.mem_neighborFinset _ _).mp (mem_erase.mp hq).2
    let w : Fin (j + 2) → V := fun i =>
      if h : i.val < j + 1 then w' ⟨i.val, h⟩ else q
    refine ⟨w, mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩, ?_⟩
    · intro i
      by_cases hi : i.val < j
      · simp only [w, Fin.val_castSucc, Fin.val_succ, show i.val < j + 1 by omega, ↓reduceDIte,
          show i.val + 1 < j + 1 by omega]
        exact hnb.1 ⟨i.val, hi⟩
      · have hieq : i.val = j := by omega
        simp only [w, Fin.val_castSucc, Fin.val_succ, hieq, show j < j + 1 by omega, ↓reduceDIte,
          show ¬(j + 1 < j + 1) by omega]
        exact hqu
    · intro i hi
      by_cases hlt : i + 2 < j + 1
      · simp only [w, show i < j + 1 by omega, show i + 2 < j + 1 by omega, ↓reduceDIte]
        exact hnb.2 i (by omega)
      · have hieq : i = j - 1 := by omega
        simp only [w, hieq, show j - 1 < j + 1 by omega,
          show ¬(j - 1 + 2 < j + 1) by omega, ↓reduceDIte]
        exact hqp.symm
    · ext i; simp only [w, Fin.val_castSucc, i.isLt, ↓reduceDIte]

private lemma two_mul_simpleVertexCover_le_of_deg_zero_or_two (D : SimpleGraph V)
    (h02 : ∀ v : V, open Classical in D.degree v = 0 ∨ D.degree v = 2)
    (J : ℕ) (hJ : Odd J) :
    (2 * simpleVertexCover D : ℤ) ≤
      ∑ j ∈ Icc 1 J, (-1 : ℤ) ^ (j + 1) * (dirNBCount D j : ℤ) := by
  classical
  let A : Finset V := univ.filter fun v => D.degree v = 2
  have h1 : dirNBCount D 1 = 2 * A.card := by
    rw [dirNBCount_one]
    have hsplit : ∑ v : V, D.degree v = ∑ v ∈ A, D.degree v := by
      symm; refine sum_subset (subset_univ A) fun v _ hv => ?_
      rcases h02 v with h0 | h2
      · exact h0
      · exact (hv (mem_filter.mpr ⟨mem_univ v, h2⟩)).elim
    rw [hsplit, sum_congr rfl fun v hv => (mem_filter.mp hv).2, sum_const, smul_eq_mul, mul_comm]
  have hconst : ∀ j : ℕ, 1 ≤ j → dirNBCount D j = 2 * A.card := by
    intro j hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    induction k with
    | zero => simpa using h1
    | succ k ih =>
      rw [dirNBCount_succ_of_deg_zero_or_two D h02 (k + 1) (by omega)]
      exact ih (by omega)
  have hsum : ∑ j ∈ Icc 1 J, (-1 : ℤ) ^ (j + 1) * (dirNBCount D j : ℤ) = (2 * A.card : ℤ) := by
    rw [sum_congr rfl fun j hj => by rw [hconst j (mem_Icc.mp hj).1]]
    exact const_alt_sum_odd ((2 * A.card : ℕ) : ℤ) J hJ
  have hcov : IsSimpleVertexCover D A := fun u v huv => by
    left; refine mem_filter.mpr ⟨mem_univ u, ?_⟩
    rcases h02 u with h0 | h2
    · have hpos : 0 < (D.neighborFinset u).card :=
        card_pos.mpr ⟨v, (D.mem_neighborFinset _ _).mpr huv⟩
      rw [SimpleGraph.degree] at h0; omega
    · exact h2
  have hle := simpleVertexCover_le_card hcov
  rw [hsum]; omega

end TwoRegular

section PathComponents

variable {V : Type*} [Fintype V]

private structure DegOnePath (D : SimpleGraph V) (p : List V) : Prop where
  nodup : p.Nodup
  len_ge : 2 ≤ p.length
  adj : ∀ i : ℕ, (h : i + 1 < p.length) → D.Adj p[i] p[i + 1]
  deg_first : open Classical in D.degree p[0] = 1
  deg_inner : ∀ i : ℕ, 0 < i → (h : i + 1 < p.length) → open Classical in D.degree p[i] = 2
  deg_last : open Classical in D.degree p[p.length - 1] = 1

/-- In a graph of maximum degree `2`, let `p` be a path whose first vertex has degree `1`. A
neighbour of the last vertex of `p` other than its predecessor is not on `p`. -/
private lemma notMem_of_adj_last (D : SimpleGraph V)
    (h2 : ∀ v : V, open Classical in D.degree v ≤ 2) (p : List V)
    (hnd : p.Nodup) (hlen : 2 ≤ p.length)
    (hadj : ∀ i : ℕ, (h : i + 1 < p.length) → D.Adj p[i] p[i + 1])
    (hd0 : open Classical in D.degree (p[0]'(by omega)) = 1) {nxt : V}
    (hadj_nxt : D.Adj p[p.length - 1] nxt) (hne_prev : nxt ≠ p[p.length - 2]) :
    nxt ∉ p := by
  classical
  intro hmem
  set last := p[p.length - 1]
  set prev := p[p.length - 2]
  obtain ⟨idx, hidx, hget⟩ := List.getElem_of_mem hmem
  by_cases hi0 : idx = 0
  · subst hi0
    have h1 : p[1] ∈ D.neighborFinset p[0] :=
      (D.mem_neighborFinset _ _).mpr (hadj 0 (by omega))
    have h2' : last ∈ D.neighborFinset p[0] :=
      (D.mem_neighborFinset _ _).mpr (hget ▸ hadj_nxt.symm)
    obtain ⟨y, hy⟩ := card_eq_one.mp (show (D.neighborFinset p[0]).card = 1 from hd0)
    rw [hy, mem_singleton] at h1 h2'
    have hleq : p[p.length - 1] = p[1] := h2'.trans h1.symm
    have hidx_eq : p.length - 1 = 1 := hnd.getElem_inj_iff.mp hleq
    have hprev_eq : prev = p[0] := by simp [prev, show p.length - 2 = 0 by omega]
    exact hne_prev (hget.symm.trans hprev_eq.symm)
  · by_cases hil : idx = p.length - 1
    · exact D.loopless.irrefl last (by simp [last, ← hil, hget] at hadj_nxt)
    · by_cases hip : idx = p.length - 2
      · exact hne_prev (by simp [prev, ← hip, hget])
      · have hsub : ({p[idx - 1], p[idx + 1], last} : Finset V) ⊆ D.neighborFinset p[idx] :=
          fun w hw => by
            simp only [mem_insert, mem_singleton] at hw
            rcases hw with rfl | rfl | rfl
            · exact (D.mem_neighborFinset _ _).mpr
                (by simpa [show idx - 1 + 1 = idx by omega]
                  using (hadj (idx - 1) (by omega)).symm)
            · exact (D.mem_neighborFinset _ _).mpr (hadj idx (by omega))
            · exact (D.mem_neighborFinset _ _).mpr (hget ▸ hadj_nxt.symm)
        have hne1 : p[idx - 1] ≠ p[idx + 1] := fun h => by
          have := hnd.getElem_inj_iff.mp h; omega
        have hne2 : p[idx - 1] ≠ last := fun h => by
          have := hnd.getElem_inj_iff.mp h; omega
        have hne3 : p[idx + 1] ≠ last := fun h => by
          have := hnd.getElem_inj_iff.mp h; omega
        have hcard3 : ({p[idx - 1], p[idx + 1], last} : Finset V).card = 3 := by
          rw [card_insert_of_notMem (by simp [hne1, hne2]),
            card_insert_of_notMem (by simp [hne3]), card_singleton]
        have hle3 : 3 ≤ D.degree p[idx] := by
          rw [SimpleGraph.degree, ← hcard3]; exact card_le_card hsub
        have hle2 := h2 p[idx]; omega

private lemma extend_path_to_deg_one (D : SimpleGraph V)
    (h2 : ∀ v : V, open Classical in D.degree v ≤ 2) :
    ∀ k : ℕ, ∀ p : List V,
      Fintype.card V - p.length = k →
      p.Nodup → (hlen : 2 ≤ p.length) →
      (∀ i : ℕ, (h : i + 1 < p.length) → D.Adj p[i] p[i + 1]) →
      (open Classical in D.degree (p[0]'(by omega)) = 1) →
      (∀ i : ℕ, 0 < i → (h : i + 1 < p.length) → open Classical in D.degree p[i] = 2) →
      ∃ q : List V, DegOnePath D q := by
  classical
  intro k
  induction k with
  | zero =>
    intro p hk hnd hlen hadj hd0 hdi
    have hcard_eq : p.length = Fintype.card V := by
      have hle : p.length ≤ Fintype.card V := by
        calc p.length = p.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
          _ ≤ (univ : Finset V).card := card_le_card (subset_univ _)
          _ = Fintype.card V := card_univ
      omega
    have hlast_pos : 0 < D.degree p[p.length - 1] := by
      have ha : D.Adj p[p.length - 1] p[p.length - 2] := by
        have := (hadj (p.length - 2) (by omega)).symm
        simpa [show p.length - 2 + 1 = p.length - 1 by omega] using this
      rw [SimpleGraph.degree]
      exact card_pos.mpr ⟨_, (D.mem_neighborFinset _ _).mpr ha⟩
    have hlast_ne_two : D.degree p[p.length - 1] ≠ 2 := by
      intro hd2
      set last := p[p.length - 1]
      set prev := p[p.length - 2]
      have ha_prev : D.Adj last prev := by
        have := (hadj (p.length - 2) (by omega)).symm
        simpa [last, prev, show p.length - 2 + 1 = p.length - 1 by omega] using this
      have hc : ((D.neighborFinset last).erase prev).card = 1 := by
        rw [card_erase_of_mem ((D.mem_neighborFinset _ _).mpr ha_prev)]
        rw [SimpleGraph.degree] at hd2; omega
      obtain ⟨nxt, hnxt⟩ := card_pos.mp (by omega : 0 < ((D.neighborFinset last).erase prev).card)
      have hne_prev : nxt ≠ prev := (mem_erase.mp hnxt).1
      have hadj_nxt : D.Adj last nxt := (D.mem_neighborFinset _ _).mp (mem_erase.mp hnxt).2
      have hmem_p : nxt ∈ p := by
        have heq_univ : p.toFinset = univ := eq_univ_of_card _ (by
          rw [List.toFinset_card_of_nodup hnd, hcard_eq])
        exact List.mem_toFinset.mp (heq_univ ▸ mem_univ nxt)
      exact notMem_of_adj_last D h2 p hnd hlen hadj hd0 hadj_nxt hne_prev hmem_p
    have hdeg_le := h2 p[p.length - 1]
    exact ⟨p, ⟨hnd, hlen, hadj, hd0, hdi, by omega⟩⟩
  | succ k ih =>
    intro p hk hnd hlen hadj hd0 hdi
    have hlast_pos : 0 < D.degree p[p.length - 1] := by
      have ha : D.Adj p[p.length - 1] p[p.length - 2] := by
        have := (hadj (p.length - 2) (by omega)).symm
        simpa [show p.length - 2 + 1 = p.length - 1 by omega] using this
      rw [SimpleGraph.degree]
      exact card_pos.mpr ⟨_, (D.mem_neighborFinset _ _).mpr ha⟩
    by_cases hdeg1 : D.degree p[p.length - 1] = 1
    · exact ⟨p, ⟨hnd, hlen, hadj, hd0, hdi, hdeg1⟩⟩
    · have hd2 : D.degree p[p.length - 1] = 2 := by have := h2 p[p.length - 1]; omega
      set last := p[p.length - 1]
      set prev := p[p.length - 2]
      have ha_prev : D.Adj last prev := by
        have := (hadj (p.length - 2) (by omega)).symm
        simpa [last, prev, show p.length - 2 + 1 = p.length - 1 by omega] using this
      have hc : ((D.neighborFinset last).erase prev).card = 1 := by
        rw [card_erase_of_mem ((D.mem_neighborFinset _ _).mpr ha_prev)]
        rw [SimpleGraph.degree] at hd2; omega
      obtain ⟨nxt, hnxt⟩ := card_pos.mp (by omega : 0 < ((D.neighborFinset last).erase prev).card)
      have hne_prev : nxt ≠ prev := (mem_erase.mp hnxt).1
      have hadj_nxt : D.Adj last nxt := (D.mem_neighborFinset _ _).mp (mem_erase.mp hnxt).2
      have hnot_mem : nxt ∉ p :=
        notMem_of_adj_last D h2 p hnd hlen hadj hd0 hadj_nxt hne_prev
      let p' := p ++ [nxt]
      have hnd' : p'.Nodup := hnd.append (List.nodup_singleton nxt) fun _ h1 h2 =>
        hnot_mem (by simpa [List.mem_singleton.mp h2] using h1)
      have hlen' : p'.length = p.length + 1 := by simp [p']
      refine ih p' (by omega) hnd' (by omega) ?_ ?_ ?_
      · intro i hi
        by_cases hil : i + 1 < p.length
        · rw [List.getElem_append_left (by omega), List.getElem_append_left hil]
          exact hadj i hil
        · have hieq : i = p.length - 1 := by omega
          subst hieq
          have hget1 : p'[p.length - 1] = p[p.length - 1] := List.getElem_append_left (by omega)
          have hget2 : p'[p.length - 1 + 1] = nxt := by
            have he : p.length - 1 + 1 = p.length := by omega
            simp [p', he]
          rw [hget1, hget2]; exact hadj_nxt
      · rw [List.getElem_append_left (by omega)]; exact hd0
      · intro i hi0 hi
        by_cases hil : i + 1 < p.length
        · rw [List.getElem_append_left (by omega)]; exact hdi i hi0 hil
        · have hieq : i = p.length - 1 := by omega
          subst hieq
          rw [List.getElem_append_left (by omega)]; exact hd2

private lemma exists_degOnePath {D : SimpleGraph V}
    (h2 : ∀ v : V, open Classical in D.degree v ≤ 2)
    {v₀ : V} (hv₀ : open Classical in D.degree v₀ = 1) :
    ∃ p : List V, DegOnePath D p := by
  classical
  have hc : (D.neighborFinset v₀).card = 1 := hv₀
  obtain ⟨v₁, hv₁⟩ := card_pos.mp (by omega : 0 < (D.neighborFinset v₀).card)
  have hadj : D.Adj v₀ v₁ := (D.mem_neighborFinset _ _).mp hv₁
  have hne : v₀ ≠ v₁ := D.ne_of_adj hadj
  refine extend_path_to_deg_one D h2 (Fintype.card V - 2) [v₀, v₁] rfl
    (by simp [hne]) le_rfl ?_ ?_ ?_
  · intro i hi
    have : i = 0 := by simpa using hi
    subst this; exact hadj
  · simpa using hv₀
  · intro i hi0 hi; simp at hi; omega

private lemma degOnePath_isEdgeClosed [DecidableEq V] {D : SimpleGraph V} {p : List V}
    (hp : DegOnePath D p) :
    IsEdgeClosed D p.toFinset := by
  classical
  intro u v huv hu
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hu)
  have hvmem : v ∈ D.neighborFinset p[i] := (D.mem_neighborFinset _ _).mpr huv
  have hp2 := hp.len_ge
  by_cases hi0 : i = 0
  · subst hi0
    have h1 : p[1] ∈ D.neighborFinset p[0] :=
      (D.mem_neighborFinset _ _).mpr (hp.adj 0 (by omega))
    obtain ⟨y, hy⟩ := card_eq_one.mp (show (D.neighborFinset p[0]).card = 1 from hp.deg_first)
    rw [hy, mem_singleton] at hvmem h1
    rw [hvmem, ← h1]
    exact List.mem_toFinset.mpr (List.getElem_mem (by omega))
  · by_cases hil : i = p.length - 1
    · subst hil
      have h1 : p[p.length - 2] ∈ D.neighborFinset p[p.length - 1] :=
        (D.mem_neighborFinset _ _).mpr
          (by simpa [show p.length - 2 + 1 = p.length - 1 by omega]
            using (hp.adj (p.length - 2) (by omega)).symm)
      obtain ⟨y, hy⟩ := card_eq_one.mp
        (show (D.neighborFinset p[p.length - 1]).card = 1 from hp.deg_last)
      rw [hy, mem_singleton] at hvmem h1
      rw [hvmem, ← h1]
      exact List.mem_toFinset.mpr (List.getElem_mem (by have := hp.len_ge; omega))
    · have h1 : p[i - 1] ∈ D.neighborFinset p[i] :=
        (D.mem_neighborFinset _ _).mpr
          (by simpa [show i - 1 + 1 = i by omega] using (hp.adj (i - 1) (by omega)).symm)
      have h2 : p[i + 1] ∈ D.neighborFinset p[i] :=
        (D.mem_neighborFinset _ _).mpr (hp.adj i (by omega))
      have hne : p[i - 1] ≠ p[i + 1] := fun h => by
        have := hp.nodup.getElem_inj_iff.mp h; omega
      have hsub : ({p[i - 1], p[i + 1]} : Finset V) ⊆ D.neighborFinset p[i] := by
        intro w hw; simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl <;> assumption
      have heq : ({p[i - 1], p[i + 1]} : Finset V) = D.neighborFinset p[i] :=
        eq_of_subset_of_card_le hsub (by
          rw [card_pair hne, ← SimpleGraph.degree, hp.deg_inner i (by omega) (by omega)])
      rw [← heq, mem_insert, mem_singleton] at hvmem
      rcases hvmem with rfl | rfl
      · exact List.mem_toFinset.mpr (List.getElem_mem (by omega))
      · exact List.mem_toFinset.mpr (List.getElem_mem (by omega))

private lemma degOnePath_adj_idx_iff {D : SimpleGraph V} {p : List V} (hp : DegOnePath D p)
    {i k : ℕ} (hi : i < p.length) (hk : k < p.length) :
    D.Adj p[i] p[k] ↔ (k = i + 1 ∨ i = k + 1) := by
  classical
  constructor
  · intro hadj
    have hmem : p[k] ∈ D.neighborFinset p[i] := (D.mem_neighborFinset _ _).mpr hadj
    have hp2 := hp.len_ge
    by_cases hi0 : i = 0
    · subst hi0
      have h1 : p[1] ∈ D.neighborFinset p[0] :=
        (D.mem_neighborFinset _ _).mpr (hp.adj 0 (by omega))
      obtain ⟨y, hy⟩ := card_eq_one.mp (show (D.neighborFinset p[0]).card = 1 from hp.deg_first)
      rw [hy, mem_singleton] at hmem h1
      left; exact hp.nodup.getElem_inj_iff.mp (hmem.trans h1.symm)
    · by_cases hil : i = p.length - 1
      · subst hil
        have h1 : p[p.length - 2] ∈ D.neighborFinset p[p.length - 1] :=
          (D.mem_neighborFinset _ _).mpr
            (by simpa [show p.length - 2 + 1 = p.length - 1 by omega]
              using (hp.adj (p.length - 2) (by omega)).symm)
        obtain ⟨y, hy⟩ := card_eq_one.mp
          (show (D.neighborFinset p[p.length - 1]).card = 1 from hp.deg_last)
        rw [hy, mem_singleton] at hmem h1
        have hkeq := hp.nodup.getElem_inj_iff.mp (hmem.trans h1.symm)
        right; omega
      · have h1 : p[i - 1] ∈ D.neighborFinset p[i] :=
          (D.mem_neighborFinset _ _).mpr
            (by simpa [show i - 1 + 1 = i by omega] using (hp.adj (i - 1) (by omega)).symm)
        have h2 : p[i + 1] ∈ D.neighborFinset p[i] :=
          (D.mem_neighborFinset _ _).mpr (hp.adj i (by omega))
        have hne : p[i - 1] ≠ p[i + 1] := fun h => by
          have := hp.nodup.getElem_inj_iff.mp h; omega
        have heq : ({p[i - 1], p[i + 1]} : Finset V) = D.neighborFinset p[i] :=
          eq_of_subset_of_card_le (by
            intro w hw; simp only [mem_insert, mem_singleton] at hw
            rcases hw with rfl | rfl <;> assumption)
            (by rw [card_pair hne, ← SimpleGraph.degree, hp.deg_inner i (by omega) (by omega)])
        rw [← heq, mem_insert, mem_singleton] at hmem
        rcases hmem with h | h
        · have := hp.nodup.getElem_inj_iff.mp h; right; omega
        · have := hp.nodup.getElem_inj_iff.mp h; left; omega
  · rintro (rfl | rfl)
    · exact hp.adj i hk
    · exact (hp.adj k hi).symm

private lemma degOnePath_vertexCover_le [DecidableEq V] {D : SimpleGraph V} {p : List V}
    (hp : DegOnePath D p) :
    simpleVertexCover (restrictEdges D p.toFinset) ≤ p.length / 2 := by
  classical
  let oddIdx : Finset ℕ := (range p.length).filter (fun i => i % 2 = 1)
  have hcard_le : oddIdx.card = p.length / 2 := by
    have hbij : ∀ n : ℕ, ((range n).filter fun i => i % 2 = 1).card = n / 2 := by
      intro n; induction n with
      | zero => simp
      | succ n ih =>
        rw [range_add_one, filter_insert]
        split_ifs with h
        · rw [card_insert_of_notMem (by simp), ih]; omega
        · rw [ih]; omega
    exact hbij p.length
  let C : Finset V := (Finset.univ.filter fun i : Fin p.length => i.val % 2 = 1).image
    fun i => p[i.val]
  have hC_card : C.card ≤ p.length / 2 := by
    calc C.card ≤ (univ.filter fun i : Fin p.length => i.val % 2 = 1).card := card_image_le
      _ = oddIdx.card := by
        refine card_bij (fun i _ => i.val) ?_ ?_ ?_
        · intro i hi; simp [oddIdx, i.isLt, (mem_filter.mp hi).2]
        · intro a _ b _ h; exact Fin.ext h
        · intro n hn
          have hn' := mem_filter.mp hn
          exact ⟨⟨n, mem_range.mp hn'.1⟩, mem_filter.mpr ⟨mem_univ _, hn'.2⟩, rfl⟩
      _ = p.length / 2 := hcard_le
  have hcov : IsSimpleVertexCover (restrictEdges D p.toFinset) C := by
    intro u v ⟨huv, hu, hv⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hu)
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hv)
    have hadj := (degOnePath_adj_idx_iff hp hi hk).mp huv
    rcases hadj with rfl | rfl
    · by_cases ho : i % 2 = 1
      · exact Or.inl (mem_image.mpr ⟨⟨i, hi⟩, mem_filter.mpr ⟨mem_univ _, ho⟩, rfl⟩)
      · exact Or.inr (mem_image.mpr ⟨⟨i + 1, hk⟩,
          mem_filter.mpr ⟨mem_univ _, show (i + 1) % 2 = 1 by omega⟩, rfl⟩)
    · by_cases ho : k % 2 = 1
      · exact Or.inr (mem_image.mpr ⟨⟨k, hk⟩, mem_filter.mpr ⟨mem_univ _, ho⟩, rfl⟩)
      · exact Or.inl (mem_image.mpr ⟨⟨k + 1, hi⟩,
          mem_filter.mpr ⟨mem_univ _, show (k + 1) % 2 = 1 by omega⟩, rfl⟩)
  exact (simpleVertexCover_le_card hcov).trans hC_card

private lemma degOnePath_dirNBCount [DecidableEq V] {D : SimpleGraph V} {p : List V}
    (hp : DegOnePath D p) (j : ℕ) (hj : 1 ≤ j) :
    dirNBCount (restrictEdges D p.toFinset) j = 2 * (p.length - j) := by
  classical
  let P := restrictEdges D p.toFinset
  let W : Finset (Fin (j + 1) → V) := univ.filter fun w => IsNBWalk P j w
  let S : Finset (Bool × Fin (p.length - j)) := univ
  have hScard : S.card = 2 * (p.length - j) := by
    simp [S, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  let f : Bool × Fin (p.length - j) → (Fin (j + 1) → V) := fun ⟨dir, a⟩ t =>
    if dir then p[a.val + t.val]'(by have := a.isLt; have := t.isLt; omega)
    else p[a.val + j - t.val]'(by have := a.isLt; have := t.isLt; omega)
  symm
  change 2 * (p.length - j) = W.card
  rw [← hScard]
  refine card_bij (fun x _ => f x) ?_ ?_ ?_
  · rintro ⟨dir, a⟩ _
    refine mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩
    · intro i
      cases dir
      · simp only [f, Bool.false_eq_true, ↓reduceIte, Fin.val_castSucc, Fin.val_succ]
        have hadj : D.Adj p[a.val + j - (i.val + 1)] p[a.val + j - i.val] := by
          have ha := hp.adj (a.val + j - (i.val + 1)) (by have := a.isLt; have := i.isLt; omega)
          have heq : a.val + j - (i.val + 1) + 1 = a.val + j - i.val := by
            have := i.isLt; omega
          simpa [heq] using ha
        exact ⟨hadj.symm, List.mem_toFinset.mpr (List.getElem_mem _),
          List.mem_toFinset.mpr (List.getElem_mem _)⟩
      · simp only [f, ↓reduceIte, Fin.val_castSucc, Fin.val_succ]
        exact ⟨hp.adj (a.val + i.val) (by have := a.isLt; have := i.isLt; omega),
          List.mem_toFinset.mpr (List.getElem_mem _),
          List.mem_toFinset.mpr (List.getElem_mem _)⟩
    · intro i hi heq
      cases dir
      · simp only [f, Bool.false_eq_true, ↓reduceIte] at heq
        have := hp.nodup.getElem_inj_iff.mp heq; omega
      · simp only [f, ↓reduceIte] at heq
        have := hp.nodup.getElem_inj_iff.mp heq; omega
  · rintro ⟨d₁, a₁⟩ _ ⟨d₂, a₂⟩ _ heq
    have h0 := congrFun heq ⟨0, by omega⟩
    have h1 := congrFun heq ⟨1, by omega⟩
    cases d₁ <;> cases d₂
    · simp only [f, Bool.false_eq_true, ↓reduceIte] at h0
      have hi := hp.nodup.getElem_inj_iff.mp h0
      exact Prod.ext rfl (Fin.ext (show a₁.val = a₂.val by omega))
    · simp only [f, Bool.false_eq_true, ↓reduceIte] at h0 h1
      have i0 := hp.nodup.getElem_inj_iff.mp h0
      have i1 := hp.nodup.getElem_inj_iff.mp h1
      omega
    · simp only [f, Bool.false_eq_true, ↓reduceIte] at h0 h1
      have i0 := hp.nodup.getElem_inj_iff.mp h0
      have i1 := hp.nodup.getElem_inj_iff.mp h1
      omega
    · simp only [f, ↓reduceIte] at h0
      have hi := hp.nodup.getElem_inj_iff.mp h0
      exact Prod.ext rfl (Fin.ext (show a₁.val = a₂.val by omega))
  · intro w hw
    have hnb := (mem_filter.mp hw).2
    have hmem : ∀ t : Fin (j + 1), w t ∈ p := fun t => by
      by_cases ht : t.val < j
      · exact List.mem_toFinset.mp (hnb.1 ⟨t.val, ht⟩).2.1
      · have ht_lt : t.val < j + 1 := t.isLt
        have hteq : t = ⟨j, by omega⟩ := Fin.ext (show t.val = j by omega)
        rw [hteq]
        have hstep := (hnb.1 ⟨j - 1, by omega⟩).2.2
        simpa [show j - 1 + 1 = j by omega] using List.mem_toFinset.mp hstep
    let idx (t : ℕ) : ℕ := if h : t ≤ j then p.idxOf (w ⟨t, by omega⟩) else 0
    have hlt : ∀ t, t ≤ j → idx t < p.length := fun t ht => by
      simp only [idx, ht, ↓reduceDIte]
      exact List.idxOf_lt_length_of_mem (hmem ⟨t, by omega⟩)
    have hget : ∀ t (ht : t ≤ j), p[idx t]'(hlt t ht) = w ⟨t, by omega⟩ := fun t ht => by
      have h1 : idx t = p.idxOf (w ⟨t, by omega⟩) := by simp [idx, ht]
      simp [h1]
    have hstep : ∀ t, t < j → idx (t + 1) = idx t + 1 ∨ idx t = idx (t + 1) + 1 := fun t ht => by
      have hadj : D.Adj (p[idx t]'(hlt t (by omega)))
          (p[idx (t + 1)]'(hlt (t + 1) (by omega))) := by
        rw [hget t (by omega), hget (t + 1) (by omega)]
        exact (hnb.1 ⟨t, ht⟩).1
      exact (degOnePath_adj_idx_iff hp (hlt t (by omega)) (hlt (t + 1) (by omega))).mp hadj
    rcases hstep 0 (by omega) with h01 | h10
    · have hfwd : ∀ t, t ≤ j → idx t = idx 0 + t := by
        intro t
        induction t using Nat.strong_induction_on with
        | ind t ih =>
          intro ht
          match t with
          | 0 => simp
          | 1 => simpa using h01
          | s + 2 =>
            have hs0 := ih s (by omega) (by omega)
            have hs1 := ih (s + 1) (by omega) (by omega)
            have hstep' := hstep (s + 1) (by omega)
            rw [show s + 1 + 1 = s + 2 from rfl] at hstep'
            rcases hstep' with hup | hdn
            · omega
            · exfalso
              have heq_i : idx s = idx (s + 2) := by omega
              have hne_w : w ⟨s, by omega⟩ ≠ w ⟨s + 2, by omega⟩ := hnb.2 s (by omega)
              apply hne_w
              rw [← hget s (by omega), ← hget (s + 2) ht]
              simp only [heq_i]
      have haj : idx 0 < p.length - j := by
        have := hlt j le_rfl; have := hfwd j le_rfl; omega
      refine ⟨(true, ⟨idx 0, haj⟩), mem_univ _, ?_⟩
      ext t; simp only [f, ↓reduceIte]
      have ht := hfwd t.val (by have := t.isLt; omega)
      have hge := hget t.val (by have := t.isLt; omega)
      simpa [ht] using hge
    · have hbwd : ∀ t, t ≤ j → idx t + t = idx 0 := by
        intro t
        induction t using Nat.strong_induction_on with
        | ind t ih =>
          intro ht
          match t with
          | 0 => simp
          | 1 => simpa [add_comm] using h10.symm
          | s + 2 =>
            have hs0 := ih s (by omega) (by omega)
            have hs1 := ih (s + 1) (by omega) (by omega)
            have hstep' := hstep (s + 1) (by omega)
            rw [show s + 1 + 1 = s + 2 from rfl] at hstep'
            rcases hstep' with hup | hdn
            · exfalso
              have heq_i : idx s = idx (s + 2) := by omega
              have hne_w : w ⟨s, by omega⟩ ≠ w ⟨s + 2, by omega⟩ := hnb.2 s (by omega)
              apply hne_w
              rw [← hget s (by omega), ← hget (s + 2) ht]
              simp only [heq_i]
            · omega
      have haj_ge : j ≤ idx 0 := by
        have := hbwd j le_rfl; omega
      have ha_lt : idx 0 - j < p.length - j := by
        have := hlt 0 (by omega); omega
      refine ⟨(false, ⟨idx 0 - j, ha_lt⟩), mem_univ _, ?_⟩
      ext t; simp only [f, Bool.false_eq_true, ↓reduceIte]
      have ht := hbwd t.val (by have := t.isLt; omega)
      have hge := hget t.val (by have := t.isLt; omega)
      have heq_i : idx 0 - j + j - t.val = idx t.val := by omega
      simpa [heq_i] using hge

end PathComponents

section AlternatingMain

variable {V : Type*} [Fintype V]

/-- For every finite simple graph `D` of maximum degree at most `2` and every **odd** `J ≥ 1`,
twice the minimum vertex-cover size is bounded above by the alternating sum of directed
non-backtracking walk counts. -/
theorem two_mul_simpleVertexCover_le_alternating_of_maxDeg_two (D : SimpleGraph V)
    (h2 : ∀ v : V, open Classical in D.degree v ≤ 2) (J : ℕ) (hJ : Odd J) :
    (2 * simpleVertexCover D : ℤ) ≤
      ∑ j ∈ Icc 1 J, (-1 : ℤ) ^ (j + 1) * (dirNBCount D j : ℤ) := by
  classical
  have hmain : ∀ m : ℕ, ∀ (D : SimpleGraph V),
      D.edgeFinset.card = m → (∀ v : V, D.degree v ≤ 2) →
      (2 * simpleVertexCover D : ℤ) ≤
        ∑ j ∈ Icc 1 J, (-1 : ℤ) ^ (j + 1) * (dirNBCount D j : ℤ) := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro D hm h2D
      by_cases hdeg1 : ∃ v : V, D.degree v = 1
      · obtain ⟨v₀, hv₀⟩ := hdeg1
        obtain ⟨p, hp⟩ := exists_degOnePath h2D hv₀
        have hcl : IsEdgeClosed D p.toFinset := degOnePath_isEdgeClosed hp
        have hp2 := hp.len_ge
        have he_adj : D.Adj p[0] p[1] := hp.adj 0 (by omega)
        have hlt : (restrictEdges D p.toFinsetᶜ).edgeFinset.card < m := by
          rw [← hm]
          exact restrictEdges_edgeFinset_lt he_adj
            (List.mem_toFinset.mpr (List.getElem_mem (by have := hp.len_ge; omega)))
        have hrest := ih _ hlt (restrictEdges D p.toFinsetᶜ) rfl fun v =>
          (restrictEdges_degree_le D p.toFinsetᶜ v).trans (h2D v)
        have hcov := simpleVertexCover_split hcl
        have hP_cov := degOnePath_vertexCover_le hp
        have hP_sum : (2 * (p.length / 2) : ℤ) ≤
            ∑ j ∈ Icc 1 J, (-1 : ℤ) ^ (j + 1) *
              (dirNBCount (restrictEdges D p.toFinset) j : ℤ) := by
          have heq : ∑ j ∈ Icc 1 J, (-1 : ℤ) ^ (j + 1) *
              (dirNBCount (restrictEdges D p.toFinset) j : ℤ) =
              ∑ j ∈ Icc 1 J, (-1 : ℤ) ^ (j + 1) * (2 * ((p.length - j : ℕ) : ℤ)) :=
            sum_congr rfl fun j hj => by
              rw [degOnePath_dirNBCount hp j (mem_Icc.mp hj).1]
              push_cast; ring
          rw [heq]; exact path_alt_sum_ge p.length J hJ
        have hsum_split : ∑ j ∈ Icc 1 J, (-1 : ℤ) ^ (j + 1) * (dirNBCount D j : ℤ) =
            (∑ j ∈ Icc 1 J, (-1 : ℤ) ^ (j + 1) *
              (dirNBCount (restrictEdges D p.toFinset) j : ℤ)) +
            (∑ j ∈ Icc 1 J, (-1 : ℤ) ^ (j + 1) *
              (dirNBCount (restrictEdges D p.toFinsetᶜ) j : ℤ)) := by
          rw [← sum_add_distrib]
          refine sum_congr rfl fun j hj => ?_
          rw [dirNBCount_split hcl (mem_Icc.mp hj).1]
          push_cast; ring
        omega
      · push Not at hdeg1
        have h02 : ∀ v : V, D.degree v = 0 ∨ D.degree v = 2 := fun v => by
          have := h2D v; have := hdeg1 v; omega
        exact two_mul_simpleVertexCover_le_of_deg_zero_or_two D h02 J hJ
  exact hmain D.edgeFinset.card D rfl h2

end AlternatingMain

section DegreeThreeRemoval

variable {V : Type*} [Fintype V]

/-- One-step extension bound. In a graph of maximum degree `3`, a family `T` of non-backtracking
walks of length `k + 2` whose truncations lie in a family `S` of non-backtracking walks of length
`k + 1` has at most `2 * |S|` members: the last vertex is a neighbour of the previous one other
than the one before it. -/
private lemma card_nbWalk_extend_le (D : SimpleGraph V)
    (h3 : ∀ v : V, open Classical in D.degree v ≤ 3) (k : ℕ)
    (S : Finset (Fin (k + 2) → V)) (T : Finset (Fin (k + 3) → V))
    (hS : ∀ w' ∈ S, IsNBWalk D (k + 1) w')
    (hT : ∀ w ∈ T, IsNBWalk D (k + 2) w ∧ (fun i : Fin (k + 2) => w i.castSucc) ∈ S) :
    T.card ≤ S.card * 2 := by
  classical
  let fiber (w' : Fin (k + 2) → V) : Finset (Fin (k + 3) → V) :=
    univ.filter fun w => IsNBWalk D (k + 2) w ∧
      (∀ i : Fin (k + 2), w i.castSucc = w' i)
  have hsub : T ⊆ S.biUnion fiber := by
    intro w hw
    obtain ⟨hnb, hmem⟩ := hT w hw
    exact mem_biUnion.mpr ⟨_, hmem, mem_filter.mpr ⟨mem_univ _, hnb, fun _ => rfl⟩⟩
  have hfib_le : ∀ w' ∈ S, (fiber w').card ≤ 2 := fun w' hw' => by
    have hnb' := hS w' hw'
    let a := w' ⟨k + 1, by omega⟩
    let p := w' ⟨k, by omega⟩
    have hap : D.Adj a p := (hnb'.1 ⟨k, by omega⟩).symm
    have hle : (fiber w').card ≤ ((D.neighborFinset a).erase p).card := by
      refine card_le_card_of_injOn (fun w => w ⟨k + 2, by omega⟩) ?_ ?_
      · intro w hw
        have ⟨hnb, hag⟩ := (mem_filter.mp hw).2
        refine mem_coe.mpr (mem_erase.mpr ⟨?_, (D.mem_neighborFinset _ _).mpr ?_⟩)
        · have hne := hnb.2 k (by omega)
          rw [show w ⟨k, by omega⟩ = p from hag ⟨k, by omega⟩] at hne
          exact hne.symm
        · rw [show a = w ⟨k + 1, by omega⟩ from (hag ⟨k + 1, by omega⟩).symm]
          exact hnb.1 ⟨k + 1, by omega⟩
      · intro w₁ hw₁ w₂ hw₂ heq
        have ha₁ := (mem_filter.mp hw₁).2.2
        have ha₂ := (mem_filter.mp hw₂).2.2
        ext i
        by_cases hi : i.val < k + 2
        · exact (ha₁ ⟨i.val, hi⟩).trans (ha₂ ⟨i.val, hi⟩).symm
        · have hilt : i.val < k + 3 := i.isLt
          have hieq : i = ⟨k + 2, by omega⟩ := Fin.ext (show i.val = k + 2 by omega)
          rw [hieq]; exact heq
    have hce : ((D.neighborFinset a).erase p).card = D.degree a - 1 := by
      rw [card_erase_of_mem ((D.mem_neighborFinset _ _).mpr hap), SimpleGraph.degree]
    have := h3 a; omega
  calc T.card ≤ (S.biUnion fiber).card := card_le_card hsub
    _ ≤ ∑ w' ∈ S, (fiber w').card := card_biUnion_le
    _ ≤ ∑ _w' ∈ S, 2 := sum_le_sum hfib_le
    _ = S.card * 2 := by rw [sum_const, smul_eq_mul]

private lemma card_nbWalk_from_start_le (D : SimpleGraph V)
    (h3 : ∀ v : V, open Classical in D.degree v ≤ 3) :
    ∀ (k : ℕ) (v₀ : V),
      open Classical in
      (univ.filter fun w : Fin (k + 1) → V => IsNBWalk D k w ∧ w 0 = v₀).card ≤
        if k = 0 then 1 else 3 * 2 ^ (k - 1) := by
  classical
  intro k
  induction k with
  | zero =>
    intro v₀
    simp only [↓reduceIte]
    have hsub : (univ.filter fun w : Fin 1 → V => IsNBWalk D 0 w ∧ w 0 = v₀) ⊆
        ({fun _ : Fin 1 => v₀} : Finset (Fin 1 → V)) := fun w hw => by
      rw [mem_singleton]; ext i; fin_cases i; exact (mem_filter.mp hw).2.2
    exact (card_le_card hsub).trans (by simp)
  | succ k ih =>
    intro v₀
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    cases k with
    | zero =>
      simp only [pow_zero, mul_one]
      let f : (Fin 2 → V) → V := fun w => w 1
      have h1 : (univ.filter fun w : Fin 2 → V => IsNBWalk D 1 w ∧ w 0 = v₀).card ≤
          (D.neighborFinset v₀).card := by
        refine card_le_card_of_injOn f (fun w hw => ?_) (fun w₁ hw₁ w₂ hw₂ heq => ?_)
        · have hw' := (mem_filter.mp hw).2
          rw [mem_coe, SimpleGraph.mem_neighborFinset, ← hw'.2]
          exact hw'.1.1 ⟨0, by omega⟩
        · ext i; fin_cases i
          · exact (mem_filter.mp hw₁).2.2.trans (mem_filter.mp hw₂).2.2.symm
          · exact heq
      exact h1.trans (h3 v₀)
    | succ k =>
      have hk := ih v₀
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel] at hk
      refine le_trans (card_nbWalk_extend_le D h3 k
        (univ.filter fun w => IsNBWalk D (k + 1) w ∧ w 0 = v₀) _
        (fun w' hw' => (mem_filter.mp hw').2.1) fun w hw => ?_) ?_
      · have ⟨hnb, h0⟩ := (mem_filter.mp hw).2
        refine ⟨hnb, mem_filter.mpr ⟨mem_univ _, ?_, h0⟩⟩
        exact ⟨fun i => hnb.1 i.castSucc, fun i hi => hnb.2 i (by omega)⟩
      · calc _ ≤ (3 * 2 ^ k) * 2 := Nat.mul_le_mul_right 2 hk
          _ = 3 * 2 ^ (k + 1) := by ring

private lemma card_nbWalk_from_two_le (D : SimpleGraph V)
    (h3 : ∀ v : V, open Classical in D.degree v ≤ 3) (u prev : V) (hadj : D.Adj u prev) :
    ∀ (k : ℕ),
      open Classical in
      (univ.filter fun w : Fin (k + 1) → V =>
        IsNBWalk D k w ∧ w 0 = u ∧
          (∀ h : 0 < k, w ⟨1, by omega⟩ ≠ prev)).card ≤ 2 ^ k := by
  classical
  intro k
  induction k with
  | zero =>
    simp only [pow_zero]
    have hsub : (univ.filter fun w : Fin 1 → V =>
        IsNBWalk D 0 w ∧ w 0 = u ∧ ∀ h : 0 < 0, w ⟨1, by omega⟩ ≠ prev) ⊆
        ({fun _ : Fin 1 => u} : Finset (Fin 1 → V)) := fun w hw => by
      rw [mem_singleton]; ext i; fin_cases i; exact (mem_filter.mp hw).2.2.1
    exact (card_le_card hsub).trans (by simp)
  | succ k ih =>
    cases k with
    | zero =>
      have hle : (univ.filter fun w : Fin 2 → V => IsNBWalk D 1 w ∧ w 0 = u ∧
          (∀ _ : 0 < 1, w ⟨1, by omega⟩ ≠ prev)).card ≤
          ((D.neighborFinset u).erase prev).card := by
        refine card_le_card_of_injOn (fun w => w 1) ?_ ?_
        · intro w hw
          have ⟨hnb, h0, hne⟩ := (mem_filter.mp hw).2
          refine mem_coe.mpr (mem_erase.mpr ⟨hne (by omega),
            (D.mem_neighborFinset _ _).mpr ?_⟩)
          simpa [h0] using hnb.1 ⟨0, by omega⟩
        · intro w₁ hw₁ w₂ hw₂ heq
          ext i; fin_cases i
          · exact (mem_filter.mp hw₁).2.2.1.trans (mem_filter.mp hw₂).2.2.1.symm
          · exact heq
      have hce : ((D.neighborFinset u).erase prev).card = D.degree u - 1 := by
        rw [card_erase_of_mem ((D.mem_neighborFinset _ _).mpr hadj), SimpleGraph.degree]
      have hdeg := h3 u
      exact hle.trans (by rw [hce]; exact (by omega : D.degree u - 1 ≤ 2 ^ (0 + 1)))
    | succ k =>
      refine le_trans (card_nbWalk_extend_le D h3 k
        (univ.filter fun w => IsNBWalk D (k + 1) w ∧ w 0 = u ∧
          (∀ _ : 0 < k + 1, w ⟨1, by omega⟩ ≠ prev)) _
        (fun w' hw' => (mem_filter.mp hw').2.1) fun w hw => ?_) ?_
      · have ⟨hnb, h0, hne⟩ := (mem_filter.mp hw).2
        refine ⟨hnb, mem_filter.mpr ⟨mem_univ _, ?_, h0, fun _ => hne (by omega)⟩⟩
        exact ⟨fun i => hnb.1 i.castSucc, fun i hi => hnb.2 i (by omega)⟩
      · calc _ ≤ (2 ^ (k + 1)) * 2 := Nat.mul_le_mul_right 2 ih
          _ = 2 ^ (k + 2) := by ring

private lemma card_nbWalk_through_at_le (D : SimpleGraph V)
    (h3 : ∀ v : V, open Classical in D.degree v ≤ 3)
    (j : ℕ) (hj : 1 ≤ j) (s : Fin (j + 1)) (v₀ : V) :
    open Classical in
    (univ.filter fun w : Fin (j + 1) → V => IsNBWalk D j w ∧ w s = v₀).card ≤
      3 * 2 ^ (j - 1) := by
  classical
  by_cases hs0 : s.val = 0
  · have hseq : s = 0 := Fin.ext hs0
    subst hseq
    have h := card_nbWalk_from_start_le D h3 j v₀
    have hne : j ≠ 0 := by omega
    simpa [hne] using h
  · let leftW (w : Fin (j + 1) → V) : Fin (s.val + 1) → V :=
      fun i => w ⟨s.val - i.val, by have := s.isLt; omega⟩
    let Sleft : Finset (Fin (s.val + 1) → V) :=
      univ.filter fun u => IsNBWalk D s.val u ∧ u 0 = v₀
    have hleft_card : Sleft.card ≤ 3 * 2 ^ (s.val - 1) := by
      have h := card_nbWalk_from_start_le D h3 s.val v₀
      have hne : s.val ≠ 0 := hs0
      simpa [Sleft, hne] using h
    let fiber (u : Fin (s.val + 1) → V) : Finset (Fin (j + 1) → V) :=
      univ.filter fun w => IsNBWalk D j w ∧ leftW w = u
    have hsub : (univ.filter fun w : Fin (j + 1) → V => IsNBWalk D j w ∧ w s = v₀) ⊆
        Sleft.biUnion fiber := by
      intro w hw
      have ⟨hnb, hws⟩ := (mem_filter.mp hw).2
      refine mem_biUnion.mpr ⟨leftW w, mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩,
        mem_filter.mpr ⟨mem_univ _, hnb, rfl⟩⟩
      · refine ⟨fun i => ?_, fun i hi => ?_⟩
        · have hadj := (hnb.1 ⟨s.val - (i.val + 1), by have := s.isLt; have := i.isLt; omega⟩).symm
          have heq : s.val - (i.val + 1) + 1 = s.val - i.val := by
            have := i.isLt; omega
          simpa [leftW, heq] using hadj
        · have hne := hnb.2 (s.val - (i + 2)) (by have := s.isLt; omega)
          have heq : s.val - (i + 2) + 2 = s.val - i := by omega
          simpa [leftW, heq] using hne.symm
      · simpa [leftW] using hws
    have hfib_le : ∀ u ∈ Sleft, (fiber u).card ≤ 2 ^ (j - s.val) := fun u hu => by
      have ⟨hunb, hu0⟩ := (mem_filter.mp hu).2
      have hprev_adj : D.Adj v₀ (u ⟨1, by omega⟩) := by
        rw [← hu0]; exact hunb.1 ⟨0, by omega⟩
      let rightW (w : Fin (j + 1) → V) : Fin (j - s.val + 1) → V :=
        fun i => w ⟨s.val + i.val, by have := s.isLt; have := i.isLt; omega⟩
      have hinj : (fiber u).card ≤
          (univ.filter fun r : Fin (j - s.val + 1) → V =>
            IsNBWalk D (j - s.val) r ∧ r 0 = v₀ ∧
              (∀ _ : 0 < j - s.val, r ⟨1, by omega⟩ ≠ u ⟨1, by omega⟩)).card := by
        refine card_le_card_of_injOn rightW ?_ ?_
        · intro w hw
          have ⟨hnb, hlu⟩ := (mem_filter.mp hw).2
          have h0 : w ⟨s.val, by have := s.isLt; omega⟩ = v₀ := by
            have := congrFun hlu 0; simpa [leftW, hu0] using this
          refine mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, ⟨fun i => ?_, fun i hi => ?_⟩, ?_, ?_⟩)
          · have hadj := hnb.1 ⟨s.val + i.val, by have := i.isLt; omega⟩
            simpa [rightW, add_assoc] using hadj
          · have hne := hnb.2 (s.val + i) (by omega)
            simpa [rightW, add_assoc] using hne
          · simpa [rightW] using h0
          · intro hpos
            have hne := hnb.2 (s.val - 1) (by omega)
            have hu1 : u ⟨1, by omega⟩ = w ⟨s.val - 1, by have := s.isLt; omega⟩ := by
              have := congrFun hlu ⟨1, by omega⟩; simpa [leftW] using this.symm
            rw [hu1]
            have heq : s.val - 1 + 2 = s.val + 1 := by omega
            simpa [rightW, heq] using hne.symm
        · intro w₁ hw₁ w₂ hw₂ heq
          have hl1 := (mem_filter.mp hw₁).2.2
          have hl2 := (mem_filter.mp hw₂).2.2
          ext i
          by_cases hi : i.val ≤ s.val
          · have h1 := congrFun (hl1.trans hl2.symm) ⟨s.val - i.val, by omega⟩
            simpa [leftW, show s.val - (s.val - i.val) = i.val by omega] using h1
          · have h1 := congrFun heq ⟨i.val - s.val, by have := i.isLt; omega⟩
            simpa [rightW, show s.val + (i.val - s.val) = i.val by omega] using h1
      exact hinj.trans (card_nbWalk_from_two_le D h3 v₀ (u ⟨1, by omega⟩) hprev_adj (j - s.val))
    calc _ ≤ (Sleft.biUnion fiber).card := card_le_card hsub
      _ ≤ ∑ u ∈ Sleft, (fiber u).card := card_biUnion_le
      _ ≤ ∑ _u ∈ Sleft, 2 ^ (j - s.val) := sum_le_sum hfib_le
      _ = Sleft.card * 2 ^ (j - s.val) := by rw [sum_const, smul_eq_mul]
      _ ≤ (3 * 2 ^ (s.val - 1)) * 2 ^ (j - s.val) := Nat.mul_le_mul_right _ hleft_card
      _ = 3 * 2 ^ (j - 1) := by
        rw [mul_assoc, ← pow_add, show s.val - 1 + (j - s.val) = j - 1 by
          have := s.isLt; omega]

/-- **Subcubic alternating non-backtracking bound.** For every finite simple graph `D` of maximum
degree at most `3` and every **odd** `J ≥ 1`, twice its minimum vertex-cover cardinality is
bounded above by the alternating sum of directed non-backtracking walk counts up to length `J`,
plus `altErrConst J` times the number of degree-`3` vertices of `D`. -/
theorem two_mul_simpleVertexCover_le_alternating (D : SimpleGraph V)
    (h3 : ∀ v : V, open Classical in D.degree v ≤ 3) (J : ℕ) (hJ : Odd J) :
    (2 * simpleVertexCover D : ℤ) ≤
      (∑ j ∈ Icc 1 J, (-1 : ℤ) ^ (j + 1) * (dirNBCount D j : ℤ)) +
        (altErrConst J * (degThreeSet D).card : ℤ) := by
  classical
  let B : Finset V := degThreeSet D
  let D' : SimpleGraph V := restrictEdges D Bᶜ
  have h2 : ∀ v : V, D'.degree v ≤ 2 := by
    intro v
    by_cases hv : v ∈ B
    · have h0 : D'.degree v = 0 := by
        rw [SimpleGraph.degree, card_eq_zero]
        ext u; simp only [SimpleGraph.mem_neighborFinset, notMem_empty, iff_false]
        intro hadj; exact (mem_compl.mp hadj.2.1) hv
      omega
    · have hne : D.degree v ≠ 3 := fun h => hv (by simpa [B, degThreeSet] using h)
      have hle := (restrictEdges_degree_le D Bᶜ v).trans (h3 v)
      have hlt : D.degree v ≤ 2 := by have := h3 v; omega
      exact (restrictEdges_degree_le D Bᶜ v).trans hlt
  have hcov_drop : simpleVertexCover D ≤ simpleVertexCover D' + B.card := by
    obtain ⟨C', hC', hc'⟩ := exists_simpleVertexCover_eq D'
    have hcov : IsSimpleVertexCover D (C' ∪ B) := by
      intro u v huv
      by_cases hu : u ∈ B
      · exact Or.inl (mem_union_right C' hu)
      · by_cases hv : v ∈ B
        · exact Or.inr (mem_union_right C' hv)
        · rcases hC' u v ⟨huv, mem_compl.mpr hu, mem_compl.mpr hv⟩ with h | h
          · exact Or.inl (mem_union_left B h)
          · exact Or.inr (mem_union_left B h)
    calc simpleVertexCover D ≤ (C' ∪ B).card := simpleVertexCover_le_card hcov
      _ ≤ C'.card + B.card := card_union_le C' B
      _ = simpleVertexCover D' + B.card := by rw [hc']
  have hsub_le : ∀ j : ℕ, 1 ≤ j → dirNBCount D' j ≤ dirNBCount D j := fun j _ => by
    refine card_le_card fun w hw => ?_
    have hnb := (mem_filter.mp hw).2
    exact mem_filter.mpr ⟨mem_univ _, fun i => (hnb.1 i).1, hnb.2⟩
  have hdiff_le : ∀ j : ℕ, 1 ≤ j →
      dirNBCount D j - dirNBCount D' j ≤ (j + 1) * 3 * 2 ^ (j - 1) * B.card := by
    intro j hj
    let W : Finset (Fin (j + 1) → V) := univ.filter fun w => IsNBWalk D j w
    let W' : Finset (Fin (j + 1) → V) := univ.filter fun w => IsNBWalk D' j w
    have hsub : W' ⊆ W := fun w hw => by
      have hnb := (mem_filter.mp hw).2
      exact mem_filter.mpr ⟨mem_univ _, fun i => (hnb.1 i).1, hnb.2⟩
    have hcov_diff : W \ W' ⊆ (B ×ˢ (univ : Finset (Fin (j + 1)))).biUnion fun p =>
        univ.filter fun w => IsNBWalk D j w ∧ w p.2 = p.1 := by
      intro w hw
      have hW := (mem_filter.mp (mem_sdiff.mp hw).1).2
      have hnotW' := (mem_sdiff.mp hw).2
      have hex : ∃ s : Fin (j + 1), w s ∈ B := by
        by_contra hnone
        push Not at hnone
        apply hnotW'
        exact mem_filter.mpr ⟨mem_univ _, fun i =>
          ⟨hW.1 i, mem_compl.mpr (hnone i.castSucc), mem_compl.mpr (hnone i.succ)⟩, hW.2⟩
      obtain ⟨s, hs⟩ := hex
      exact mem_biUnion.mpr ⟨(w s, s), mem_product.mpr ⟨hs, mem_univ s⟩,
        mem_filter.mpr ⟨mem_univ _, hW, rfl⟩⟩
    change W.card - W'.card ≤ _
    rw [← card_sdiff_of_subset hsub]
    calc (W \ W').card
        ≤ ((B ×ˢ (univ : Finset (Fin (j + 1)))).biUnion fun p =>
            univ.filter fun w => IsNBWalk D j w ∧ w p.2 = p.1).card :=
          card_le_card hcov_diff
      _ ≤ ∑ p ∈ B ×ˢ (univ : Finset (Fin (j + 1))),
            (univ.filter fun w => IsNBWalk D j w ∧ w p.2 = p.1).card := card_biUnion_le
      _ ≤ ∑ _p ∈ B ×ˢ (univ : Finset (Fin (j + 1))), 3 * 2 ^ (j - 1) :=
          sum_le_sum fun p _ => card_nbWalk_through_at_le D h3 j hj p.2 p.1
      _ = (B ×ˢ (univ : Finset (Fin (j + 1)))).card * (3 * 2 ^ (j - 1)) := by
          rw [sum_const, smul_eq_mul]
      _ = (j + 1) * 3 * 2 ^ (j - 1) * B.card := by
          rw [card_product, card_univ, Fintype.card_fin]; ring
  have hterm : ∀ j ∈ Icc 1 J,
      (-1 : ℤ) ^ (j + 1) * (dirNBCount D' j : ℤ) ≤
        (-1 : ℤ) ^ (j + 1) * (dirNBCount D j : ℤ) +
          ((if Even j then (j + 1) * 3 * 2 ^ (j - 1) else 0 : ℕ) : ℤ) * (B.card : ℤ) := by
    intro j hj
    have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
    have hle := hsub_le j hj1
    by_cases hev : Even j
    · have hpow : (-1 : ℤ) ^ (j + 1) = -1 := by
        obtain ⟨k, hk⟩ := hev
        exact Odd.neg_one_pow ⟨k, by omega⟩
      have hd := hdiff_le j hj1
      simp only [hev, ↓reduceIte, hpow, neg_one_mul]
      omega
    · have hodd : Odd j := Nat.not_even_iff_odd.mp hev
      have hpow : (-1 : ℤ) ^ (j + 1) = 1 := by
        obtain ⟨k, hk⟩ := hodd
        exact Even.neg_one_pow ⟨k + 1, by omega⟩
      simp only [hev, ↓reduceIte, hpow, one_mul, Nat.cast_zero, zero_mul, add_zero]
      exact_mod_cast hle
  have hsum_le : ∑ j ∈ Icc 1 J, (-1 : ℤ) ^ (j + 1) * (dirNBCount D' j : ℤ) ≤
      (∑ j ∈ Icc 1 J, (-1 : ℤ) ^ (j + 1) * (dirNBCount D j : ℤ)) +
        ((∑ j ∈ Icc 1 J, if Even j then (j + 1) * 3 * 2 ^ (j - 1) else 0 : ℕ) : ℤ) *
          (B.card : ℤ) := by
    have h1 := sum_le_sum hterm
    rw [sum_add_distrib, ← sum_mul] at h1
    simpa [Nat.cast_sum] using h1
  have hD' := two_mul_simpleVertexCover_le_alternating_of_maxDeg_two D' h2 J hJ
  have herr : (altErrConst J : ℤ) * (B.card : ℤ) = 2 * (B.card : ℤ) +
      ((∑ j ∈ Icc 1 J, if Even j then (j + 1) * 3 * 2 ^ (j - 1) else 0 : ℕ) : ℤ) *
        (B.card : ℤ) := by
    simp only [altErrConst]; push_cast; ring
  have hB_eq : (degThreeSet D).card = B.card := rfl
  linarith

omit [Fintype V] in
/-- On `crossingGraph H b`, vertex covers coincide with crossing vertex covers of `(H, b)`. -/
theorem simpleVertexCover_crossingGraph (H : SimpleGraph V) (b : V → Bool) :
    simpleVertexCover (crossingGraph H b) = simpleCrossingCover H b := by
  simp only [simpleVertexCover, simpleCrossingCover]
  congr 1; ext k
  exact exists_congr fun C => and_congr_left' <| by
    simp only [IsSimpleVertexCover, IsSimpleCrossingCover, crossingGraph_adj_iff]
    exact ⟨fun h u v huv hne => h u v ⟨huv, hne⟩, fun h u v ⟨huv, hne⟩ => h u v huv hne⟩

omit [Fintype V] in
/-- A walk in `crossingGraph H b` is non-backtracking iff it is a non-backtracking walk in `H`
whose vertex labels alternate at every step. -/
theorem isNBWalk_crossingGraph_iff (H : SimpleGraph V) (b : V → Bool) (j : ℕ)
    (w : Fin (j + 1) → V) :
    IsNBWalk (crossingGraph H b) j w ↔
      IsNBWalk H j w ∧ ∀ i : Fin j, b (w i.castSucc) ≠ b (w i.succ) := by
  simp only [IsNBWalk, crossingGraph_adj_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨fun i => (h1 i).1, h2⟩, fun i => (h1 i).2⟩
  · rintro ⟨⟨h1, h2⟩, hb⟩; exact ⟨fun i => ⟨h1 i, hb i⟩, h2⟩

/-- Specialization of `two_mul_simpleVertexCover_le_alternating` to `crossingGraph H b` on a
subcubic simple graph `H`. -/
theorem two_mul_simpleCrossingCover_le_alternating (H : SimpleGraph V)
    (h3 : ∀ v : V, open Classical in H.degree v ≤ 3) (b : V → Bool) (J : ℕ) (hJ : Odd J) :
    (2 * simpleCrossingCover H b : ℤ) ≤
      (∑ j ∈ Icc 1 J, (-1 : ℤ) ^ (j + 1) * (dirNBCount (crossingGraph H b) j : ℤ)) +
        (altErrConst J * (degThreeSet (crossingGraph H b)).card : ℤ) := by
  classical
  rw [← simpleVertexCover_crossingGraph H b]
  refine two_mul_simpleVertexCover_le_alternating (crossingGraph H b) (fun v => ?_) J hJ
  have hle : (crossingGraph H b).degree v ≤ H.degree v := by
    simp only [SimpleGraph.degree]
    exact card_le_card fun u hu => by
      rw [SimpleGraph.mem_neighborFinset] at hu ⊢
      exact hu.1
  exact hle.trans (h3 v)

end DegreeThreeRemoval

end Cslib.Circuits.Frontier.CrossingCover
