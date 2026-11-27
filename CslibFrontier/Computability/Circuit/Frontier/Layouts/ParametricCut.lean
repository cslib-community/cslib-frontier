/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Local
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Switched.SwitchedLayout
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Parametric min-cut monotonicity and one-sided median cut injections

This module establishes two deterministic structural properties of threshold cuts on finite
multigraphs used in Gaussian sweep and local-improvement layouts:

1. **Parametric random-field Ising (`s`–`t`) min-cut monotonicity** (`IsRFIMMinCut.subset_of_lt`,
   `rfimMinCut_mono`). On *every* finite multigraph `G` (self-loops, parallel edges, and odd cycles
   allowed), for any vertex scores `y : V → ℝ` and coupling `α > 0`, the parametric energy
   `rfimEnergy G y α t S = |δ_G(S)| + α ∑_{v ∈ S} (y v - t)` is submodular, its minimizers at each
   threshold `t` have a unique minimal element `rfimMinCut G y α t`, and strict threshold increase
   `t₁ < t₂` forces *every* minimizer at `t₁` to be contained in *every* minimizer at `t₂` without
   any tie-breaking assumption.

2. **One-sided median key `lowerKey G y v = max (y v) (nbrMedian G y v)`** on loopless cubic
   multigraphs (`ncard_edgeCut_lowerSublevel_add_two_mul`, `ncard_edgeCut_lowerSublevel_eq`,
   `ncard_edgeCut_lowerSublevel_le_innerFrontier`, `ncard_lowerKey_eq_le_four`). Counting incident
   edges with multiplicity, each degree-`3` vertex has a unique neighbor median `nbrMedian G y v`.
   Setting `lowerSublevel G y t = {v | lowerKey G y v ≤ t}`, an explicit injective edge-to-vertex
   charging map into `U₁(t) ⊔ U₂(t) ⊆ innerFrontierSet G y t` proves the exact identity
   `|δ(L_-(t))| + 2 |E(U₂(t), U₂(t))| = |U₁(t)| + |U₂(t)|`, hence
   `|δ(L_-(t))| = |U₁(t)| + |U₂(t)| - 2 |E(U₂(t), U₂(t))| ≤ |innerFrontier(G, y, t)|` on all
   loopless cubic multigraphs (parallel edges allowed), while injective vertex scores have tie
   groups `{v | lowerKey G y v = c}` of size at most `4`.

## Main definitions

* `Cslib.Circuits.Frontier.Multigraph.rfimEnergy`, `IsRFIMMinCut`, `rfimMinCut`: parametric RFIM
  cut energy, its minimizers, and the canonical minimal minimizer `S_α(t)`.
* `Cslib.Circuits.Frontier.Multigraph.nbrMedian`, `lowerKey`, `upperKey`, `lowerSublevel`,
  `upperSublevel`: multiplicity-aware neighbor median and one-sided median keys and sublevel cuts.
* `Cslib.Circuits.Frontier.Multigraph.innerCrossDeg`, `innerFrontierClass`, `innerFrontierSet`,
  `internalEdges`: crossing degree at level `t`, classes `U_k(t)`, inner frontier, and internal
  edges `E(W, W)`.

## Main results

* `Cslib.Circuits.Frontier.Multigraph.ncard_edgeCut_inter_add_union_le`: submodularity of
  multigraph edge cuts.
* `Cslib.Circuits.Frontier.Multigraph.IsRFIMMinCut.subset_of_lt`,
  `Cslib.Circuits.Frontier.Multigraph.rfimMinCut_mono`: unconditional parametric min-cut
  monotonicity `t₁ < t₂ → S_α(t₁) ⊆ S_α(t₂)`.
* `Cslib.Circuits.Frontier.Multigraph.ncard_lowerKey_eq_le_four`,
  `Cslib.Circuits.Frontier.Multigraph.ncard_upperKey_eq_le_four`: tie groups of `lowerKey` and
  `upperKey` under injective vertex scores have size at most `4`.
* `Cslib.Circuits.Frontier.Multigraph.ncard_edgeCut_lowerSublevel_add_two_mul`,
  `Cslib.Circuits.Frontier.Multigraph.ncard_edgeCut_lowerSublevel_eq`,
  `Cslib.Circuits.Frontier.Multigraph.ncard_edgeCut_lowerSublevel_le_innerFrontier`,
  `Cslib.Circuits.Frontier.Multigraph.ncard_edgeCut_lowerSublevel_le_switched_innerFrontier`:
  exact `U₁`/`U₂` cut identity and `innerFrontier` bound on loopless cubic multigraphs.

The multigraph parametric RFIM formulation and the multiplicity-aware `lowerKey` `U₁`/`U₂` cut
identity and tie-group bound are original to this library, extending the switched inner-frontier
analysis of Gaspers [Gaspers2026].

## References

* [S. Gaspers, *Pathwidth of Sparse Graphs via Linear Programming and Randomness*][Gaspers2026]
-/

public section

namespace Cslib.Circuits.Frontier.Multigraph

open Set

variable {V E : Type*}

/-! ### Part 1: Submodularity and parametric RFIM min-cut monotonicity -/

section RFIM

/-- **Submodularity of multigraph edge cuts.** For any two vertex sets `A` and `B`,
`|δ(A ∩ B)| + |δ(A ∪ B)| ≤ |δ(A)| + |δ(B)|`. Self-loops and parallel edges are allowed. -/
theorem ncard_edgeCut_inter_add_union_le [Finite E] (G : Multigraph V E) (A B : Set V) :
    (G.edgeCut (A ∩ B)).ncard + (G.edgeCut (A ∪ B)).ncard ≤
      (G.edgeCut A).ncard + (G.edgeCut B).ncard := by
  have hle₁ : (G.edgeCut (A ∩ B) ∪ G.edgeCut (A ∪ B)).ncard ≤
      (G.edgeCut A ∪ G.edgeCut B).ncard := ncard_le_ncard fun e => by
    simp only [mem_union, mem_edgeCut, mem_inter_iff]; tauto
  have hle₂ : (G.edgeCut (A ∩ B) ∩ G.edgeCut (A ∪ B)).ncard ≤
      (G.edgeCut A ∩ G.edgeCut B).ncard := ncard_le_ncard fun e => by
    simp only [mem_inter_iff, mem_edgeCut, mem_union]; tauto
  have h₁ := ncard_union_add_ncard_inter (G.edgeCut (A ∩ B)) (G.edgeCut (A ∪ B))
  have h₂ := ncard_union_add_ncard_inter (G.edgeCut A) (G.edgeCut B)
  omega

/-- Parametric random-field Ising (`s`–`t` cut) energy
`E_{α, t}(S) = |δ_G(S)| + α ∑_{v ∈ S} (y v - t)`. -/
@[expose] noncomputable def rfimEnergy (G : Multigraph V E) (y : V → ℝ) (α t : ℝ)
    (S : Finset V) : ℝ :=
  ((G.edgeCut (S : Set V)).ncard : ℝ) + α * ∑ v ∈ S, (y v - t)

/-- `S` is a global minimizer of `rfimEnergy G y α t`. -/
@[expose] def IsRFIMMinCut (G : Multigraph V E) (y : V → ℝ) (α t : ℝ) (S : Finset V) : Prop :=
  ∀ T : Finset V, G.rfimEnergy y α t S ≤ G.rfimEnergy y α t T

/-- Crossing inequality for `rfimEnergy` across two thresholds `t₁` and `t₂`:
`(E_{α,t₁}(A ∩ B) - E_{α,t₁}(A)) + (E_{α,t₂}(A ∪ B) - E_{α,t₂}(B)) ≤ -α (t₂ - t₁) |A \ B|`. -/
theorem rfimEnergy_crossing_le [DecidableEq V] [Finite E] (G : Multigraph V E) (y : V → ℝ)
    (α t₁ t₂ : ℝ) (A B : Finset V) :
    (G.rfimEnergy y α t₁ (A ∩ B) - G.rfimEnergy y α t₁ A) +
      (G.rfimEnergy y α t₂ (A ∪ B) - G.rfimEnergy y α t₂ B) ≤
      -α * (t₂ - t₁) * ((A \ B).card : ℝ) := by
  simp only [rfimEnergy]
  have hcut : ((G.edgeCut ((A ∩ B : Finset V) : Set V)).ncard : ℝ) +
      ((G.edgeCut ((A ∪ B : Finset V) : Set V)).ncard : ℝ) ≤
      ((G.edgeCut (A : Set V)).ncard : ℝ) + ((G.edgeCut (B : Set V)).ncard : ℝ) := by
    rw [Finset.coe_inter, Finset.coe_union]
    exact_mod_cast G.ncard_edgeCut_inter_add_union_le (A : Set V) (B : Set V)
  have hA : ∑ v ∈ A, (y v - t₁) = (∑ v ∈ A ∩ B, (y v - t₁)) + ∑ v ∈ A \ B, (y v - t₁) := by
    conv_lhs => rw [← Finset.sdiff_union_inter A B]
    rw [Finset.sum_union (Finset.disjoint_sdiff_inter A B), add_comm]
  have hB : ∑ v ∈ A ∪ B, (y v - t₂) =
      (∑ v ∈ A \ B, (y v - t₂)) + ∑ v ∈ B, (y v - t₂) := by
    rw [← Finset.sdiff_union_self_eq_union, Finset.sum_union
      (Finset.disjoint_left.mpr fun _ h₁ h₂ => (Finset.mem_sdiff.mp h₁).2 h₂)]
  have hdiff : (∑ v ∈ A \ B, (y v - t₂)) - (∑ v ∈ A \ B, (y v - t₁)) =
      -(t₂ - t₁) * ((A \ B).card : ℝ) := by
    simp only [← Finset.sum_sub_distrib, sub_sub_sub_cancel_left, Finset.sum_const, nsmul_eq_mul]
    ring
  linarith [congrArg (α * ·) hA, congrArg (α * ·) hB, congrArg (α * ·) hdiff]

/-- At any fixed threshold `t` and coupling `α`, `rfimEnergy G y α t` is submodular. -/
theorem rfimEnergy_inter_add_union_le [DecidableEq V] [Finite E] (G : Multigraph V E)
    (y : V → ℝ) (α t : ℝ) (A B : Finset V) :
    G.rfimEnergy y α t (A ∩ B) + G.rfimEnergy y α t (A ∪ B) ≤
      G.rfimEnergy y α t A + G.rfimEnergy y α t B := by
  linarith [G.rfimEnergy_crossing_le y α t t A B]

/-- **Unconditional parametric RFIM min-cut monotonicity.** For every finite multigraph `G`,
scores `y : V → ℝ`, coupling `α > 0`, and strict threshold order `t₁ < t₂`, *every* minimizer `A`
of `E_{α, t₁}` is contained in *every* minimizer `B` of `E_{α, t₂}`, with no tie-breaking
assumption. -/
theorem IsRFIMMinCut.subset_of_lt [Finite E] {G : Multigraph V E} {y : V → ℝ} {α t₁ t₂ : ℝ}
    {A B : Finset V} (hA : G.IsRFIMMinCut y α t₁ A) (hB : G.IsRFIMMinCut y α t₂ B)
    (hα : 0 < α) (ht : t₁ < t₂) : A ⊆ B := by
  classical
  intro v hvA
  by_contra hvB
  have hpos : 0 < α * (t₂ - t₁) * ((A \ B).card : ℝ) := mul_pos (mul_pos hα (sub_pos.mpr ht))
    (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hvA, hvB⟩⟩))
  linarith [G.rfimEnergy_crossing_le y α t₁ t₂ A B, hA (A ∩ B), hB (A ∪ B)]

/-- Minimizers of `rfimEnergy G y α t` are closed under intersection. -/
theorem IsRFIMMinCut.inter [DecidableEq V] [Finite E] {G : Multigraph V E} {y : V → ℝ} {α t : ℝ}
    {A B : Finset V} (hA : G.IsRFIMMinCut y α t A) (hB : G.IsRFIMMinCut y α t B) :
    G.IsRFIMMinCut y α t (A ∩ B) := by
  intro T
  linarith [G.rfimEnergy_inter_add_union_le y α t A B, hB (A ∪ B), hA T]

/-- Minimizers of `rfimEnergy G y α t` are closed under union. -/
theorem IsRFIMMinCut.union [DecidableEq V] [Finite E] {G : Multigraph V E} {y : V → ℝ} {α t : ℝ}
    {A B : Finset V} (hA : G.IsRFIMMinCut y α t A) (hB : G.IsRFIMMinCut y α t B) :
    G.IsRFIMMinCut y α t (A ∪ B) := by
  intro T
  linarith [G.rfimEnergy_inter_add_union_le y α t A B, hA (A ∩ B), hB T]

/-- Existence of a global minimizer of `rfimEnergy G y α t`. -/
theorem exists_isRFIMMinCut [Finite V] (G : Multigraph V E) (y : V → ℝ) (α t : ℝ) :
    ∃ S : Finset V, G.IsRFIMMinCut y α t S := by
  have := Fintype.ofFinite V
  obtain ⟨S, -, hS⟩ := Finset.exists_min_image (Finset.univ : Finset (Finset V))
    (G.rfimEnergy y α t) ⟨∅, Finset.mem_univ ∅⟩
  exact ⟨S, fun T => hS T (Finset.mem_univ T)⟩

/-- Canonical minimal minimizer `S_α(t)` of `rfimEnergy G y α t`: the intersection of all global
minimizers. -/
noncomputable def rfimMinCut [Finite V] (G : Multigraph V E) (y : V → ℝ) (α t : ℝ) : Finset V := by
  classical
  letI := Fintype.ofFinite V
  exact (Finset.univ.filter (G.IsRFIMMinCut y α t)).inf id

/-- The canonical `rfimMinCut G y α t` is itself a global minimizer of `rfimEnergy G y α t`. -/
theorem isRFIMMinCut_rfimMinCut [Finite V] [Finite E] (G : Multigraph V E) (y : V → ℝ)
    (α t : ℝ) : G.IsRFIMMinCut y α t (G.rfimMinCut y α t) := by
  classical
  unfold rfimMinCut
  let _ := Fintype.ofFinite V
  obtain ⟨S₀, hS₀⟩ := G.exists_isRFIMMinCut y α t
  have hclosed (s : Finset (Finset V)) (hs : s.Nonempty) :
      (∀ S ∈ s, G.IsRFIMMinCut y α t S) → G.IsRFIMMinCut y α t (s.inf id) := by
    induction hs using Finset.Nonempty.cons_induction with
    | singleton a => exact fun ha => by simpa using ha a (Finset.mem_singleton_self a)
    | cons a s _ _ ih =>
      intro hall
      rw [Finset.inf_cons]
      exact (hall a (Finset.mem_cons_self a s)).inter
        (ih fun b hb => hall b (Finset.mem_cons_of_mem hb))
  exact hclosed _ ⟨S₀, Finset.mem_filter.mpr ⟨Finset.mem_univ S₀, hS₀⟩⟩
    fun S hS => (Finset.mem_filter.mp hS).2

/-- `rfimMinCut G y α t` is contained in every global minimizer at `(α, t)`. -/
theorem rfimMinCut_subset [Finite V] {G : Multigraph V E} {y : V → ℝ} {α t : ℝ} {S : Finset V}
    (hS : G.IsRFIMMinCut y α t S) : G.rfimMinCut y α t ⊆ S := by
  classical
  unfold rfimMinCut
  let _ := Fintype.ofFinite V
  exact Finset.inf_le (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS⟩)

/-- **Monotonicity of `S_α(t)`.** For every finite multigraph `G`, scores `y : V → ℝ`, and
coupling `α > 0`, the minimal minimizer `t ↦ G.rfimMinCut y α t` is monotone (`t₁ ≤ t₂ →
S_α(t₁) ⊆ S_α(t₂)`). -/
theorem rfimMinCut_mono [Finite V] [Finite E] (G : Multigraph V E) (y : V → ℝ) {α : ℝ}
    (hα : 0 < α) : Monotone (G.rfimMinCut y α) := by
  intro t₁ t₂ ht
  rcases eq_or_lt_of_le ht with rfl | hlt
  · exact Finset.Subset.refl _
  · exact (G.isRFIMMinCut_rfimMinCut y α t₁).subset_of_lt
      (G.isRFIMMinCut_rfimMinCut y α t₂) hα hlt

end RFIM

/-! ### Part 2: One-sided median key `max(y_v, med₃(N(v)))`, tie bound, and `innerFrontier` cut
injection -/

section MedianKey

variable [DecidableEq V] {α : Type*} [LinearOrder α]

/-- At a vertex incident to three edges, a neighbor median exists (counting parallel edges with
multiplicity). -/
theorem exists_isMedianAt (G : Multigraph V E) (y : V → α) {v : V}
    (hv : (G.incidenceSet v).ncard = 3) : ∃ m : α, G.IsMedianAt y v m := by
  obtain ⟨e₀, e₁, e₂, h01, h02, h12, hs⟩ := ncard_eq_three.mp hv
  exact ⟨_, G.isMedianAt_median3 y h01 h02 h12 hs⟩

variable [Finite E]

omit [DecidableEq V] [LinearOrder α] in
private theorem ncard_sep_add_not (s : Set E) (p : E → Prop) :
    {e ∈ s | p e}.ncard + {e ∈ s | ¬p e}.ncard = s.ncard := by
  have hdisj : Disjoint {e ∈ s | p e} {e ∈ s | ¬p e} :=
    disjoint_left.mpr fun _ ha hb => hb.2 ha.2
  have hunion : {e ∈ s | p e} ∪ {e ∈ s | ¬p e} = s := by
    ext e
    by_cases hp : p e <;> simp [hp]
  rw [← ncard_union_eq hdisj, hunion]

/-- At a vertex incident to three edges, the neighbor median is unique. -/
theorem IsMedianAt.eq_of_ncard_eq_three {G : Multigraph V E} {y : V → α} {v : V} {m₁ m₂ : α}
    (h₁ : G.IsMedianAt y v m₁) (h₂ : G.IsMedianAt y v m₂)
    (hv : (G.incidenceSet v).ncard = 3) : m₁ = m₂ := by
  suffices hle : ∀ {a b : α}, G.IsMedianAt y v a → G.IsMedianAt y v b → ¬(a < b) from
    le_antisymm (not_lt.mp (hle h₂ h₁)) (not_lt.mp (hle h₁ h₂))
  intro a b ha hb hab
  have hp₁ := (ncard_sep_add_not (G.incidenceSet v) fun e => y (G.otherEnd v e) ≤ a).trans hv
  have hp₂ := (ncard_sep_add_not (G.incidenceSet v) fun e => b ≤ y (G.otherEnd v e)).trans hv
  simp only [not_le] at hp₁ hp₂
  have := ha.1
  have := hb.2
  have hdisj : Disjoint {e ∈ G.incidenceSet v | y (G.otherEnd v e) ≤ a}
      {e ∈ G.incidenceSet v | b ≤ y (G.otherEnd v e)} :=
    disjoint_left.mpr fun _ he₁ he₂ => (he₁.2.trans_lt hab).not_ge he₂.2
  have hsub : {e ∈ G.incidenceSet v | y (G.otherEnd v e) ≤ a} ∪
      {e ∈ G.incidenceSet v | b ≤ y (G.otherEnd v e)} ⊆ G.incidenceSet v :=
    union_subset (fun _ h => h.1) fun _ h => h.1
  have htot := (ncard_union_eq hdisj).symm.trans_le ((ncard_le_ncard hsub).trans_eq hv)
  omega

omit [Finite E] in
/-- Canonical multiplicity-aware neighbor median `med₃(N(v))` at a degree-`3` vertex `v` (selected
nonconstructively via `Classical.choose` from `exists_isMedianAt`, which is unique by
`IsMedianAt.eq_of_ncard_eq_three`, and falling back to `y v` if `(G.incidenceSet v).ncard ≠ 3`). -/
noncomputable def nbrMedian (G : Multigraph V E) (y : V → α) (v : V) : α := by
  classical
  exact if hv : (G.incidenceSet v).ncard = 3 then
    Classical.choose (G.exists_isMedianAt y hv)
  else y v

omit [Finite E] in
/-- At any degree-`3` vertex, `nbrMedian` satisfies `IsMedianAt`. -/
theorem isMedianAt_nbrMedian (G : Multigraph V E) (y : V → α) {v : V}
    (hv : (G.incidenceSet v).ncard = 3) : G.IsMedianAt y v (G.nbrMedian y v) := by
  classical
  rw [nbrMedian, dite_eq_left_of_eq_true (eq_true hv)]
  exact Classical.choose_spec (G.exists_isMedianAt y hv)

/-- Explicit formula for `nbrMedian` on any enumeration `{e₀, e₁, e₂}` of `G.incidenceSet v`. -/
theorem nbrMedian_eq_median3 (G : Multigraph V E) (y : V → α) {v : V} {e₀ e₁ e₂ : E}
    (h01 : e₀ ≠ e₁) (h02 : e₀ ≠ e₂) (h12 : e₁ ≠ e₂) (hv : G.incidenceSet v = {e₀, e₁, e₂}) :
    G.nbrMedian y v =
      median3 (y (G.otherEnd v e₀)) (y (G.otherEnd v e₁)) (y (G.otherEnd v e₂)) := by
  have hcard : (G.incidenceSet v).ncard = 3 := by
    rw [hv, ncard_insert_of_notMem (by simp [h01, h02]), ncard_pair h12]
  exact (G.isMedianAt_nbrMedian y hcard).eq_of_ncard_eq_three
    (G.isMedianAt_median3 y h01 h02 h12 hv) hcard

/-- At any degree-`3` vertex, `nbrMedian G y v` equals the score of one of the incident neighbors.
-/
theorem exists_nbrMedian_eq_otherEnd (G : Multigraph V E) (y : V → α) {v : V}
    (hv : (G.incidenceSet v).ncard = 3) :
    ∃ e ∈ G.incidenceSet v, G.nbrMedian y v = y (G.otherEnd v e) := by
  obtain ⟨e₀, e₁, e₂, h01, h02, h12, hs⟩ := ncard_eq_three.mp hv
  rw [G.nbrMedian_eq_median3 y h01 h02 h12 hs]
  have hmem (a b c : α) : median3 a b c = a ∨ median3 a b c = b ∨ median3 a b c = c := by
    rcases le_total a b with hab | hab <;> rcases le_total b c with hbc | hbc <;>
      rcases le_total a c with hac | hac <;> simp [median3, hab, hbc, hac]
  rcases hmem (y (G.otherEnd v e₀)) (y (G.otherEnd v e₁)) (y (G.otherEnd v e₂)) with
      h | h | h
  exacts [⟨e₀, by simp [hs], h⟩, ⟨e₁, by simp [hs], h⟩, ⟨e₂, by simp [hs], h⟩]

omit [Finite E] in
/-- Lower one-sided median key `key_-(v) = max (y v) (med₃(N(v)))`. -/
@[expose] noncomputable def lowerKey (G : Multigraph V E) (y : V → α) (v : V) : α :=
  max (y v) (G.nbrMedian y v)

omit [Finite E] in
/-- Upper one-sided median key `key_+(v) = min (y v) (med₃(N(v)))`. -/
@[expose] noncomputable def upperKey (G : Multigraph V E) (y : V → α) (v : V) : α :=
  min (y v) (G.nbrMedian y v)

omit [Finite E] in
/-- Lower sublevel set `L_-(t) = {v | key_-(v) ≤ t}`. -/
@[expose] def lowerSublevel (G : Multigraph V E) (y : V → α) (t : α) : Set V :=
  {v | G.lowerKey y v ≤ t}

omit [Finite E] in
/-- Upper sublevel set `L_+(t) = {v | key_+(v) ≤ t}`. -/
@[expose] def upperSublevel (G : Multigraph V E) (y : V → α) (t : α) : Set V :=
  {v | G.upperKey y v ≤ t}

omit [Finite E] in
/-- Monotonicity of `L_-(t)` in the threshold `t`. -/
theorem lowerSublevel_mono (G : Multigraph V E) (y : V → α) : Monotone (G.lowerSublevel y) :=
  fun _ _ ht _ hv => hv.trans ht

omit [Finite E] in
/-- Monotonicity of `L_+(t)` in the threshold `t`. -/
theorem upperSublevel_mono (G : Multigraph V E) (y : V → α) : Monotone (G.upperSublevel y) :=
  fun _ _ ht _ hv => hv.trans ht

omit [Finite E] in
/-- Every lower sublevel set is contained in the corresponding upper sublevel set:
`L_-(t) ⊆ L_+(t)`. -/
theorem lowerSublevel_subset_upperSublevel (G : Multigraph V E) (y : V → α) (t : α) :
    G.lowerSublevel y t ⊆ G.upperSublevel y t :=
  fun _ hv => min_le_max.trans hv

omit [Finite E] [LinearOrder α] in
private theorem mem_incidenceSet_otherEnd_eq {G : Multigraph V E} {v w : V} {e : E}
    (he : e ∈ G.incidenceSet v) (hw : G.otherEnd v e = w) :
    e ∈ G.incidenceSet w ∧ (v = w ∨ G.otherEnd w e = v) := by
  unfold otherEnd at hw ⊢
  by_cases hs : G.src e = v
  · simp only [hs, ↓reduceIte] at hw
    exact ⟨Or.inr hw, or_iff_not_imp_left.mpr fun hvw => (ite_eq_right (hs.trans_ne hvw)).trans hs⟩
  · have ht : G.tgt e = v := he.resolve_left hs
    simp only [hs, ↓reduceIte] at hw
    exact ⟨Or.inl hw, Or.inr (by simp [hw, ht])⟩

private theorem ncard_key_eq_le_four (G : Multigraph V E)
    (h3 : ∀ v, (G.incidenceSet v).ncard = 3) {y : V → α} (hy : Function.Injective y)
    (key : V → α) (hchoice : ∀ v, key v = y v ∨ key v = G.nbrMedian y v) (c : α) :
    {v : V | key v = c}.ncard ≤ 4 := by
  rcases {v : V | key v = c}.eq_empty_or_nonempty with hemp | ⟨v₀, hv₀⟩
  · simp [hemp]
  · obtain ⟨w, rfl⟩ : ∃ w : V, y w = c := by
      simp only [mem_ofPred_eq] at hv₀
      rcases hchoice v₀ with hm | hm
      · exact ⟨v₀, hm.symm.trans hv₀⟩
      · obtain ⟨e, -, he⟩ := G.exists_nbrMedian_eq_otherEnd y (h3 v₀)
        exact ⟨G.otherEnd v₀ e, he.symm.trans (hm.symm.trans hv₀)⟩
    have hsub : {v : V | key v = y w} ⊆
        insert w ((G.otherEnd w) '' G.incidenceSet w) := by
      intro v hv
      simp only [mem_ofPred_eq] at hv
      rcases hchoice v with hm | hm
      · exact Or.inl (hy (hm.symm.trans hv))
      · obtain ⟨e, hev, heq⟩ := G.exists_nbrMedian_eq_otherEnd y (h3 v)
        have hvw : G.otherEnd v e = w := hy (heq.symm.trans (hm.symm.trans hv))
        obtain ⟨hew, hvw_eq | hov⟩ := mem_incidenceSet_otherEnd_eq hev hvw
        · exact Or.inl hvw_eq
        · exact Or.inr ⟨e, hew, hov⟩
    calc {v : V | key v = y w}.ncard
        ≤ (insert w ((G.otherEnd w) '' G.incidenceSet w)).ncard := ncard_le_ncard hsub
      _ ≤ ((G.otherEnd w) '' G.incidenceSet w).ncard + 1 := ncard_insert_le _ _
      _ ≤ (G.incidenceSet w).ncard + 1 := Nat.add_le_add_right (ncard_image_le (toFinite _)) 1
      _ = 4 := by rw [h3 w]

/-- **Tie-group bound `≤ 4` for `lowerKey`.** When `y` is injective on a degree-`3` multigraph,
at most `4` vertices can share any key value `c` under `lowerKey G y` (parallel edges allowed). -/
theorem ncard_lowerKey_eq_le_four (G : Multigraph V E)
    (h3 : ∀ v, (G.incidenceSet v).ncard = 3) {y : V → α} (hy : Function.Injective y) (c : α) :
    {v : V | G.lowerKey y v = c}.ncard ≤ 4 :=
  G.ncard_key_eq_le_four h3 hy (G.lowerKey y) (fun v => max_choice (y v) (G.nbrMedian y v)) c

/-- **Tie-group bound `≤ 4` for `upperKey`.** When `y` is injective on a degree-`3` multigraph,
at most `4` vertices can share any key value `c` under `upperKey G y` (parallel edges allowed). -/
theorem ncard_upperKey_eq_le_four (G : Multigraph V E)
    (h3 : ∀ v, (G.incidenceSet v).ncard = 3) {y : V → α} (hy : Function.Injective y) (c : α) :
    {v : V | G.upperKey y v = c}.ncard ≤ 4 :=
  G.ncard_key_eq_le_four h3 hy (G.upperKey y) (fun v => min_choice (y v) (G.nbrMedian y v)) c

/-! ### Crossing degrees, `U_k(t)` classes, and exact `innerFrontier` cut injection -/

omit [Finite E] in
/-- Number of incident edges at `v` (counted with multiplicity) whose other endpoint scores
strictly above `t`. -/
@[expose] noncomputable def innerCrossDeg (G : Multigraph V E) (y : V → α) (t : α) (v : V) : ℕ :=
  {e ∈ G.incidenceSet v | t < y (G.otherEnd v e)}.ncard

omit [Finite E] in
/-- Class `U_k(t)` of lower vertices (`y v ≤ t`) with exactly `k` incident edges entering
`{y > t}`. -/
@[expose] def innerFrontierClass (G : Multigraph V E) (y : V → α) (t : α) (k : ℕ) : Set V :=
  {v | y v ≤ t ∧ G.innerCrossDeg y t v = k}

omit [Finite E] in
/-- Multigraph inner frontier at threshold `t`: vertices with `y v ≤ t` and at least one incident
edge whose other endpoint has `t < y w`. -/
@[expose] def innerFrontierSet (G : Multigraph V E) (y : V → α) (t : α) : Set V :=
  {v | y v ≤ t ∧ ∃ e ∈ G.incidenceSet v, t < y (G.otherEnd v e)}

omit [DecidableEq V] [Finite E] [LinearOrder α] in
/-- Edges with both endpoints in `W` (`E(W, W)`). -/
@[expose] def internalEdges (G : Multigraph V E) (W : Set V) : Set E :=
  {e | G.src e ∈ W ∧ G.tgt e ∈ W}

private theorem innerCrossDeg_add_low_eq {G : Multigraph V E} {v : V} {d : ℕ}
    (hv : (G.incidenceSet v).ncard = d) (y : V → α) (t : α) :
    G.innerCrossDeg y t v + {e ∈ G.incidenceSet v | y (G.otherEnd v e) ≤ t}.ncard = d := by
  simpa only [innerCrossDeg, not_lt] using
    (ncard_sep_add_not (G.incidenceSet v) fun e => t < y (G.otherEnd v e)).trans hv

/-- On a degree-`3` vertex `v`, `nbrMedian G y v ≤ t` holds iff at most one incident edge at `v`
enters `{y > t}`. -/
theorem nbrMedian_le_iff_innerCrossDeg_le_one (G : Multigraph V E) (y : V → α) {v : V}
    (hv : (G.incidenceSet v).ncard = 3) (t : α) :
    G.nbrMedian y v ≤ t ↔ G.innerCrossDeg y t v ≤ 1 := by
  obtain ⟨hm₁, hm₂⟩ := G.isMedianAt_nbrMedian y hv
  refine ⟨fun hmt => ?_, fun hdeg => by_contra fun hnot => ?_⟩
  · have hsum := innerCrossDeg_add_low_eq hv y (G.nbrMedian y v)
    rw [innerCrossDeg] at hsum ⊢
    have hle : {e ∈ G.incidenceSet v | t < y (G.otherEnd v e)}.ncard ≤
        {e ∈ G.incidenceSet v | G.nbrMedian y v < y (G.otherEnd v e)}.ncard :=
      ncard_le_ncard fun e he => ⟨he.1, hmt.trans_lt he.2⟩
    omega
  · have hsum := (ncard_sep_add_not (G.incidenceSet v)
      fun e => G.nbrMedian y v ≤ y (G.otherEnd v e)).trans hv
    simp only [not_le] at hsum hnot
    have hle : {e ∈ G.incidenceSet v | G.nbrMedian y v ≤ y (G.otherEnd v e)}.ncard ≤
        G.innerCrossDeg y t v := ncard_le_ncard fun e he => ⟨he.1, hnot.trans_le he.2⟩
    omega

/-- Exact characterization of `L_-(t)` on a cubic multigraph: `v ∈ L_-(t)` iff `y v ≤ t` and
`innerCrossDeg G y t v ≤ 1`. -/
theorem mem_lowerSublevel_iff (G : Multigraph V E) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    (y : V → α) (t : α) (v : V) :
    v ∈ G.lowerSublevel y t ↔ y v ≤ t ∧ G.innerCrossDeg y t v ≤ 1 := by
  rw [lowerSublevel, mem_ofPred_eq, lowerKey, max_le_iff,
    G.nbrMedian_le_iff_innerCrossDeg_le_one y (h3 v) t]

/-- `innerCrossDeg G y t v` is bounded by `(G.incidenceSet v).ncard`. -/
theorem innerCrossDeg_le_ncard_incidenceSet (G : Multigraph V E) (y : V → α) (t : α) (v : V) :
    G.innerCrossDeg y t v ≤ (G.incidenceSet v).ncard :=
  ncard_le_ncard fun _ h => h.1

/-- `v ∈ innerFrontierSet G y t` iff `y v ≤ t` and `1 ≤ innerCrossDeg G y t v`. -/
theorem mem_innerFrontierSet_iff (G : Multigraph V E) (y : V → α) (t : α) (v : V) :
    v ∈ G.innerFrontierSet y t ↔ y v ≤ t ∧ 1 ≤ G.innerCrossDeg y t v := by
  rw [innerFrontierSet, mem_ofPred_eq, innerCrossDeg, Nat.one_le_iff_ne_zero, ← pos_iff_ne_zero,
    ncard_pos (toFinite _)]
  rfl

/-- Partition of `innerFrontierSet` on a cubic multigraph into the disjoint classes
`U₁(t) ∪ U₂(t) ∪ U₃(t)`. -/
theorem innerFrontierSet_eq_union (G : Multigraph V E) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    (y : V → α) (t : α) :
    G.innerFrontierSet y t =
      G.innerFrontierClass y t 1 ∪ G.innerFrontierClass y t 2 ∪ G.innerFrontierClass y t 3 := by
  ext v
  rw [G.mem_innerFrontierSet_iff]
  simp only [mem_union, innerFrontierClass, mem_ofPred_eq, ← and_or_left]
  have hle := (G.innerCrossDeg_le_ncard_incidenceSet y t v).trans_eq (h3 v)
  exact and_congr_right fun _ => by omega

omit [Finite E] [LinearOrder α] in
private theorem otherEnd_symm_of_loopless {G : Multigraph V E} (hloop : G.Loopless) {v : V}
    {e : E} (he : e ∈ G.incidenceSet v) :
    G.otherEnd v e ≠ v ∧ e ∈ G.incidenceSet (G.otherEnd v e) ∧
      G.otherEnd (G.otherEnd v e) e = v := by
  have hne := hloop e
  unfold otherEnd
  rcases he with rfl | rfl
  · simp [hne, Ne.symm hne, mem_incidenceSet]
  · simp [hne, mem_incidenceSet]

/-- **Exact `L_-(t)` edge-cut identity on loopless cubic multigraphs.** Every loopless cubic
multigraph `G` (parallel edges allowed) satisfies
`|δ(L_-(t))| + 2 |E(U₂(t), U₂(t))| = |U₁(t)| + |U₂(t)|`,
proved via the deterministic injection sending `e = {a, b} ∈ δ(L_-(t))` (`a ∈ L_-(t)`,
`b ∉ L_-(t)`) to `a ∈ U₁(t)` if `t < y b` and to `b ∈ U₂(t)` if `y b ≤ t`. -/
theorem ncard_edgeCut_lowerSublevel_add_two_mul [Finite V] (G : Multigraph V E)
    (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3) (y : V → α) (t : α) :
    (G.edgeCut (G.lowerSublevel y t)).ncard +
      2 * (G.internalEdges (G.innerFrontierClass y t 2)).ncard =
      (G.innerFrontierClass y t 1).ncard + (G.innerFrontierClass y t 2).ncard := by
  classical
  set L := G.lowerSublevel y t
  set U₁ := G.innerFrontierClass y t 1
  set U₂ := G.innerFrontierClass y t 2
  set E₂₂ := G.internalEdges U₂
  have hL (v : V) : v ∈ L ↔ y v ≤ t ∧ G.innerCrossDeg y t v ≤ 1 := G.mem_lowerSublevel_iff h3 y t v
  have hU₂L {v : V} (hv : v ∈ U₂) : v ∉ L := fun h => by
    have := ((hL v).mp h).2; have := hv.2; omega
  -- A lower vertex outside `L` has at most one incident edge to a lower vertex.
  have hlow_eq {u : V} (hy : y u ≤ t) (hu : u ∉ L) {e₁ e₂ : E} (h₁ : e₁ ∈ G.incidenceSet u)
      (hy₁ : y (G.otherEnd u e₁) ≤ t) (h₂ : e₂ ∈ G.incidenceSet u)
      (hy₂ : y (G.otherEnd u e₂) ≤ t) : e₁ = e₂ := by
    have := innerCrossDeg_add_low_eq (h3 u) y t
    have : ¬G.innerCrossDeg y t u ≤ 1 := fun h => hu ((hL u).mpr ⟨hy, h⟩)
    exact (ncard_le_one (s := {e ∈ G.incidenceSet u | y (G.otherEnd u e) ≤ t}) (toFinite _)).mp
      (by omega) e₁ ⟨h₁, hy₁⟩ e₂ ⟨h₂, hy₂⟩
  have hyE₂₂ {u : V} {e : E} (he : e ∈ E₂₂) : y (G.otherEnd u e) ≤ t := by
    unfold otherEnd; split_ifs; exacts [he.2.1, he.1.1]
  let inEnd (e : E) : V := if G.src e ∈ L then G.src e else G.tgt e
  let outEnd (e : E) : V := if G.src e ∈ L then G.tgt e else G.src e
  let charge (e : E) : V := if t < y (outEnd e) then inEnd e else outEnd e
  have hends {e : E} (he : e ∈ G.edgeCut L) :
      inEnd e ∈ L ∧ outEnd e ∉ L ∧ e ∈ G.incidenceSet (inEnd e) ∧
        e ∈ G.incidenceSet (outEnd e) ∧ G.otherEnd (inEnd e) e = outEnd e ∧
        G.otherEnd (outEnd e) e = inEnd e := by
    rw [mem_edgeCut] at he
    have hne := hloop e
    by_cases hs : G.src e ∈ L
    · simp only [inEnd, outEnd, ite_eq_left hs]
      exact ⟨hs, fun ht => he (iff_of_true hs ht), Or.inl rfl, Or.inr rfl, by simp [otherEnd],
        by simp [otherEnd, hne]⟩
    · simp only [inEnd, outEnd, ite_eq_right hs]
      exact ⟨by_contra fun ht => he (iff_of_false hs ht), hs, Or.inr rfl, Or.inl rfl,
        by simp [otherEnd, hne], by simp [otherEnd]⟩
  have hend_eq {e : E} {u : V} (he : e ∈ G.edgeCut L) (hinc : e ∈ G.incidenceSet u) :
      (u ∈ L → inEnd e = u) ∧ (u ∉ L → outEnd e = u) := by
    obtain ⟨hin, hout, -⟩ := hends he
    have hmem : inEnd e = u ∨ outEnd e = u := by
      simp only [inEnd, outEnd]; split_ifs; exacts [hinc, hinc.symm]
    exact ⟨fun hu => hmem.resolve_right fun h => hout (h ▸ hu),
      fun hu => hmem.resolve_left fun h => hu (h ▸ hin)⟩
  have hdisjU : Disjoint U₁ U₂ :=
    disjoint_left.mpr fun _ h₁ h₂ => by
      simp only [U₁, U₂, innerFrontierClass, mem_ofPred_eq] at h₁ h₂
      omega
  -- 1. `charge` maps `G.edgeCut L` into `U₁ ∪ U₂`.
  have hmaps : MapsTo charge (G.edgeCut L) (U₁ ∪ U₂) := by
    intro e he
    obtain ⟨hin, hout, he_in, he_out, hov_in, hov_out⟩ := hends he
    obtain ⟨hy_in, hdeg_in⟩ := (hL _).mp hin
    by_cases hgt : t < y (outEnd e) <;> simp only [charge, hgt, ↓reduceIte]
    · exact Or.inl ⟨hy_in, le_antisymm hdeg_in
        ((ncard_pos (toFinite _)).mpr ⟨e, he_in, by rwa [hov_in]⟩)⟩
    · have hy_out : y (outEnd e) ≤ t := not_lt.mp hgt
      have : ¬G.innerCrossDeg y t (outEnd e) ≤ 1 := fun h1 => hout ((hL _).mpr ⟨hy_out, h1⟩)
      have : 0 < {e' ∈ G.incidenceSet (outEnd e) | y (G.otherEnd (outEnd e) e') ≤ t}.ncard :=
        (ncard_pos (toFinite _)).mpr ⟨e, he_out, by rwa [hov_out]⟩
      have := innerCrossDeg_add_low_eq (h3 (outEnd e)) y t
      exact Or.inr ⟨hy_out, by omega⟩
  -- 2. `charge` is injective on `G.edgeCut L`.
  have hinj : InjOn charge (G.edgeCut L) := by
    intro e₁ he₁ e₂ he₂ heq
    obtain ⟨hin₁, hout₁, he_in₁, he_out₁, hov_in₁, hov_out₁⟩ := hends he₁
    obtain ⟨hin₂, hout₂, he_in₂, he_out₂, hov_in₂, hov_out₂⟩ := hends he₂
    by_cases hgt₁ : t < y (outEnd e₁) <;> by_cases hgt₂ : t < y (outEnd e₂) <;>
      simp only [charge, hgt₁, hgt₂, ↓reduceIte] at heq
    · have hle1 : {e ∈ G.incidenceSet (inEnd e₁) | t < y (G.otherEnd (inEnd e₁) e)}.ncard ≤ 1 :=
        ((hL _).mp hin₁).2
      exact (ncard_le_one (toFinite _)).mp hle1 e₁ ⟨he_in₁, by rwa [hov_in₁]⟩ e₂
        ⟨heq ▸ he_in₂, by rw [heq, hov_in₂]; exact hgt₂⟩
    · exact absurd (heq ▸ hin₁) hout₂
    · exact absurd (heq ▸ hin₂) hout₁
    · exact hlow_eq (not_lt.mp hgt₁) hout₁ he_out₁ (by rw [hov_out₁]; exact ((hL _).mp hin₁).1)
        (heq ▸ he_out₂) (by rw [heq, hov_out₂]; exact ((hL _).mp hin₂).1)
  -- 3. Identify `(U₁ ∪ U₂) \ (charge '' G.edgeCut L)` as the endpoints of `E₂₂`.
  let U₂int : Set V := {u ∈ U₂ | ∃ e ∈ E₂₂, e ∈ G.incidenceSet u}
  have hcompl : (U₁ ∪ U₂) \ (charge '' G.edgeCut L) = U₂int := by
    ext u
    simp only [mem_sdiff, mem_union, mem_image, U₂int, mem_sep_iff]
    constructor
    · rintro ⟨⟨hyu, hdeg1⟩ | hu2, hnot⟩
      · obtain ⟨e, he_inc, hgt⟩ : {e ∈ G.incidenceSet u | t < y (G.otherEnd u e)}.Nonempty :=
          nonempty_of_ncard_ne_zero (by rw [← innerCrossDeg, hdeg1]; omega)
        have huL : u ∈ L := (hL u).mpr ⟨hyu, hdeg1.le⟩
        have he_cut : e ∈ G.edgeCut L := (G.mem_edgeCut_iff_otherEnd he_inc).mpr fun h =>
          hgt.not_ge ((hL _).mp (h.mp huL)).1
        have hu_eq := (hend_eq he_cut he_inc).1 huL
        have hout_eq : outEnd e = G.otherEnd u e := by rw [← (hends he_cut).2.2.2.2.1, hu_eq]
        exact absurd ⟨e, he_cut, by simp only [charge, hout_eq, hgt, ↓reduceIte, hu_eq]⟩ hnot
      · refine ⟨hu2, ?_⟩
        have := innerCrossDeg_add_low_eq (h3 u) y t
        have := hu2.2
        obtain ⟨e, he_inc, hyz⟩ : {e ∈ G.incidenceSet u | y (G.otherEnd u e) ≤ t}.Nonempty :=
          nonempty_of_ncard_ne_zero (by omega)
        obtain ⟨-, he_z, hov_z⟩ := otherEnd_symm_of_loopless hloop he_inc
        by_cases hzL : G.otherEnd u e ∈ L
        · have he_cut : e ∈ G.edgeCut L := (G.mem_edgeCut_iff_otherEnd he_inc).mpr fun h =>
            hU₂L hu2 (h.mpr hzL)
          refine absurd ⟨e, he_cut, ?_⟩ hnot
          simp only [charge, (hend_eq he_cut he_inc).2 (hU₂L hu2), not_lt.mpr hu2.1, ↓reduceIte]
        · have hz2 : G.otherEnd u e ∈ U₂ := by
            have := innerCrossDeg_add_low_eq (h3 (G.otherEnd u e)) y t
            have : ¬G.innerCrossDeg y t (G.otherEnd u e) ≤ 1 := fun h1 =>
              hzL ((hL _).mpr ⟨hyz, h1⟩)
            have : 0 < {e' ∈ G.incidenceSet (G.otherEnd u e) |
                y (G.otherEnd (G.otherEnd u e) e') ≤ t}.ncard :=
              (ncard_pos (toFinite _)).mpr ⟨e, he_z, by rw [hov_z]; exact hu2.1⟩
            exact ⟨hyz, by omega⟩
          refine ⟨e, ?_, he_inc⟩
          unfold otherEnd at hz2
          split_ifs at hz2 with hs
          exacts [⟨hs ▸ hu2, hz2⟩, ⟨hz2, he_inc.resolve_left hs ▸ hu2⟩]
    · rintro ⟨hu2, e, he22, he_inc⟩
      refine ⟨Or.inr hu2, ?_⟩
      rintro ⟨e', he'_cut, hcharge⟩
      obtain ⟨hin', -, -, he_out', -, hov_out'⟩ := hends he'_cut
      by_cases hgt' : t < y (outEnd e') <;> simp only [charge, hgt', ↓reduceIte] at hcharge
      · exact hU₂L hu2 (hcharge ▸ hin')
      · subst hcharge
        obtain rfl := hlow_eq hu2.1 (hU₂L hu2) he_out'
          (by rw [hov_out']; exact ((hL _).mp hin').1) he_inc (hyE₂₂ he22)
        exact hU₂L (show inEnd e' ∈ U₂ by simp only [inEnd]; split_ifs; exacts [he22.1, he22.2])
          hin'
  -- 4. `E₂₂` is a matching on `U₂int`, so `U₂int.ncard = 2 * E₂₂.ncard`.
  have hcard_U₂int : U₂int.ncard = 2 * E₂₂.ncard := by
    have := Fintype.ofFinite V
    have := Fintype.ofFinite E
    let F_U : Finset V := Finset.univ.filter (· ∈ U₂int)
    let F_E : Finset E := Finset.univ.filter (· ∈ E₂₂)
    have hcU : U₂int.ncard = F_U.card := by simp [← ncard_coe_finset, F_U]
    have hcE : E₂₂.ncard = F_E.card := by simp [← ncard_coe_finset, F_E]
    rw [hcU, hcE]
    have h1 : F_U.card = ∑ u ∈ F_U, ∑ e ∈ F_E, if e ∈ G.incidenceSet u then 1 else 0 := by
      rw [Finset.card_eq_sum_ones]
      refine Finset.sum_congr rfl fun u hu => ?_
      obtain ⟨hu2, e₀, he₀E, he₀I⟩ := (Finset.mem_filter.mp hu).2
      rw [Finset.sum_eq_single_of_mem e₀ (Finset.mem_filter.mpr ⟨Finset.mem_univ e₀, he₀E⟩)
        fun e' he' hne => ?_]
      · simp [he₀I]
      · refine ite_eq_right_iff.mpr fun hi' => absurd ?_ hne
        exact hlow_eq hu2.1 (hU₂L hu2) hi' (hyE₂₂ (Finset.mem_filter.mp he').2) he₀I (hyE₂₂ he₀E)
    have h2 : (∑ e ∈ F_E, ∑ u ∈ F_U, if e ∈ G.incidenceSet u then 1 else 0) = 2 * F_E.card := by
      rw [Finset.card_eq_sum_ones, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e he => ?_
      obtain ⟨hs2, ht2⟩ := (Finset.mem_filter.mp he).2
      rw [Finset.sum_boole, mul_one]
      have hpair : F_U.filter (fun u => e ∈ G.incidenceSet u) = {G.src e, G.tgt e} := by
        ext u
        simp only [Finset.mem_filter, F_U, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, mem_incidenceSet]
        refine ⟨fun ⟨_, h⟩ => h.imp Eq.symm Eq.symm, ?_⟩
        rintro (rfl | rfl)
        exacts [⟨⟨hs2, e, ⟨hs2, ht2⟩, Or.inl rfl⟩, Or.inl rfl⟩,
          ⟨⟨ht2, e, ⟨hs2, ht2⟩, Or.inr rfl⟩, Or.inr rfl⟩]
      rw [hpair, Finset.card_pair (hloop e)]
      rfl
    rw [h1, Finset.sum_comm, h2]
  -- 5. Combine `hinj.ncard_image` with `(charge '' δ(L)) ⊔ U₂int = U₁ ⊔ U₂`.
  have hpart := Set.ncard_sdiff_add_ncard_of_subset hmaps.image_subset (toFinite _)
  rw [hinj.ncard_image, hcompl, hcard_U₂int, ncard_union_eq hdisjU] at hpart
  omega

/-- Subtracted form of the exact `L_-(t)` edge-cut identity:
`|δ(L_-(t))| = |U₁(t)| + |U₂(t)| - 2 |E(U₂(t), U₂(t))|`. -/
theorem ncard_edgeCut_lowerSublevel_eq [Finite V] (G : Multigraph V E) (hloop : G.Loopless)
    (h3 : ∀ v, (G.incidenceSet v).ncard = 3) (y : V → α) (t : α) :
    (G.edgeCut (G.lowerSublevel y t)).ncard =
      (G.innerFrontierClass y t 1).ncard + (G.innerFrontierClass y t 2).ncard -
        2 * (G.internalEdges (G.innerFrontierClass y t 2)).ncard := by
  have h := G.ncard_edgeCut_lowerSublevel_add_two_mul hloop h3 y t
  omega

/-- **Deterministic `innerFrontier` edge-cut bound for `L_-(t)`.** On every loopless cubic
multigraph `G` (parallel edges allowed), `|δ(L_-(t))| ≤ |innerFrontierSet G y t|`. -/
theorem ncard_edgeCut_lowerSublevel_le_innerFrontier [Finite V] (G : Multigraph V E)
    (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3) (y : V → α) (t : α) :
    (G.edgeCut (G.lowerSublevel y t)).ncard ≤ (G.innerFrontierSet y t).ncard := by
  have hcut := G.ncard_edgeCut_lowerSublevel_add_two_mul hloop h3 y t
  have hsub : G.innerFrontierClass y t 1 ∪ G.innerFrontierClass y t 2 ⊆
      G.innerFrontierSet y t := G.innerFrontierSet_eq_union h3 y t ▸ subset_union_left
  have hdisj : Disjoint (G.innerFrontierClass y t 1) (G.innerFrontierClass y t 2) :=
    disjoint_left.mpr fun _ h₁ h₂ => by
      simp only [innerFrontierClass, mem_ofPred_eq] at h₁ h₂; omega
  have hle := (ncard_union_eq hdisj).symm.trans_le (ncard_le_ncard hsub)
  omega

omit [Finite E] in
/-- Agreement between `Multigraph.innerFrontierSet` and `Switched.innerFrontier` on
`G.toSimpleGraph` for `Fin n` vertices and real scores. -/
theorem coe_switched_innerFrontier_eq {n : ℕ} (G : Multigraph (Fin n) E) (y : Fin n → ℝ)
    (t : ℝ) :
    ((Switched.innerFrontier G.toSimpleGraph y t : Finset (Fin n)) : Set (Fin n)) =
      G.innerFrontierSet y t := by
  ext u
  simp only [Finset.mem_coe, Switched.innerFrontier, Finset.mem_filter, Finset.mem_univ, true_and,
    innerFrontierSet, mem_ofPred_eq, toSimpleGraph_adj]
  refine and_congr_right fun hyu => ?_
  constructor
  · rintro ⟨w, ⟨huw, e, hends⟩, htw⟩
    rcases Sym2.eq_iff.mp hends with ⟨hs, ht_eq⟩ | ⟨hs, ht_eq⟩
    · exact ⟨e, Or.inl hs, by simp [otherEnd, hs, ht_eq, htw]⟩
    · exact ⟨e, Or.inr ht_eq, by simp [otherEnd, hs, huw.symm, htw]⟩
  · rintro ⟨e, he_inc, htw⟩
    refine ⟨G.otherEnd u e, ⟨fun heq => (hyu.trans_lt htw).ne (congrArg y heq), e, ?_⟩, htw⟩
    unfold otherEnd
    rcases he_inc with hs | ht_eq
    · simp [ends, hs]
    · by_cases hs : G.src e = u <;> simp [ends, hs, ht_eq, Sym2.eq_swap]

/-- Specialization of `ncard_edgeCut_lowerSublevel_le_innerFrontier` to `Fin n` and
`Switched.innerFrontier`: `|δ(L_-(t))| ≤ |Switched.innerFrontier G.toSimpleGraph y t|`. -/
theorem ncard_edgeCut_lowerSublevel_le_switched_innerFrontier {n : ℕ} (G : Multigraph (Fin n) E)
    (hloop : G.Loopless) (h3 : ∀ v, (G.incidenceSet v).ncard = 3) (y : Fin n → ℝ) (t : ℝ) :
    (G.edgeCut (G.lowerSublevel y t)).ncard ≤
      (Switched.innerFrontier G.toSimpleGraph y t).card := by
  have h := G.ncard_edgeCut_lowerSublevel_le_innerFrontier hloop h3 y t
  rwa [← G.coe_switched_innerFrontier_eq y t, ncard_coe_finset] at h

end MedianKey

end Cslib.Circuits.Frontier.Multigraph
