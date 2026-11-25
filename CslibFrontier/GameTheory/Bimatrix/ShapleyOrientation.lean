/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.VertexOrientation
public import CslibFrontier.GameTheory.Bimatrix.LemkeHowson
public import Mathlib.Data.Finset.Sort
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Basic.Sign.Basic
public import Mathlib.Basic.Sign.Defs
import Mathlib.Tactic.Ring

/-!
# Shapley's orientation of Lemke–Howson paths

This module formalizes the determinant-based orientation (index) of the Lemke–Howson graph due to
Shapley [Shapley1974] (see also [vonStengel2007, Section 3.12]).

For two nondegenerate bounded polyhedra `A₁ *ᵥ x ≤ b₁` (`ι₁`-dimensional) and `A₂ *ᵥ y ≤ b₂`
(`ι₂`-dimensional) whose constraint rows share a label set `κ` of cardinality `m + n` with missing
label `k₀`, each active half-edge `(p, side)` out of a `LemkeHowson.Node` carries an orientation
sign `halfEdgeIndex ∈ {-1, 1}` defined by the product of the permutation sign matching the
combined tight bases (replacing the leaving label by `k₀` on the active side) and the signs of the
two basis determinants.

## Main definitions

* `Cslib.GameTheory.LemkeHowson.signOfK`: `{-1, 0, 1}` sign of an element of an ordered field.
* `Cslib.GameTheory.LemkeHowson.leaveLabel`: the label dropped on an active half-edge (`k₀` at a
  completely labelled node, otherwise the unique duplicate tight label).
* `Cslib.GameTheory.LemkeHowson.halfEdgeFun`: the label assignment `Fin m ⊕ Fin n → κ` for side
  `false` (`A₁`) or `true` (`A₂`).
* `Cslib.GameTheory.LemkeHowson.halfEdgeIndex`: Shapley's determinant orientation sign
  `∈ {-1, 0, 1}` on `(T₁, T₂, side)`.

## Main results

* `Cslib.GameTheory.LemkeHowson.halfEdgeFun_bijective_of_acl`: active half-edges induce bijections.
* `Cslib.GameTheory.LemkeHowson.halfEdgeIndex_ne_zero`: every active half-edge has sign `±1`.
* `Cslib.GameTheory.LemkeHowson.halfEdgeIndex_true_eq_neg_false`: at every degree-2 node (not
  completely labelled), the two incident half-edges carry opposite signs.
* `Cslib.GameTheory.LemkeHowson.halfEdgeIndex_pivot_left_eq_neg` and
  `Cslib.GameTheory.LemkeHowson.halfEdgeIndex_pivot_right_eq_neg`: moving across any edge of
  `LemkeHowson.graph` flips the half-edge sign, so path endpoints have opposite index.
* `Cslib.GameTheory.LemkeHowson.halfEdgeIndex_zero_zero`: on canonical nonnegativity bases
  (`-I_m`, `-I_n`), the origin `(0, 0)` has orientation `(-1) ^ (m + n)`.

## References

* [L. S. Shapley, *A note on the Lemke–Howson algorithm*][Shapley1974]
* [B. von Stengel, *Equilibrium computation for two-player games in strategic and extensive form*,
  Section 3.12][vonStengel2007]
-/

public section

namespace Cslib.GameTheory.LemkeHowson

open Matrix

private lemma det_submatrix_col_equiv {κ ι R : Type*} [CommRing R] [Fintype ι]
    {k : ℕ} (A : Matrix κ ι R) (f : Fin k → κ) (e : Fin k ≃ ι) :
    open Classical in
    (A.submatrix f e).det = (A.submatrix (f ∘ e.symm) id).det := by
  classical
  rw [show A.submatrix f e = (A.submatrix (f ∘ e.symm) id).submatrix e e by ext; simp,
    Matrix.det_submatrix_equiv_self]

section Signs

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Ordered-field sign in `{-1, 0, 1}`. -/
@[expose] def signOfK (c : K) : ℤ :=
  SignType.sign c

theorem signOfK_mul (a b : K) : signOfK (a * b) = signOfK a * signOfK b := by
  simp only [signOfK, sign_mul, SignType.coe_mul]

omit [IsStrictOrderedRing K] in
theorem signOfK_ne_zero {a : K} (ha : a ≠ 0) : signOfK a ≠ 0 := by
  rcases lt_or_gt_of_ne ha with h | h <;> simp [signOfK, h]

omit [IsStrictOrderedRing K] in
theorem signOfK_sq {a : K} (ha : a ≠ 0) : signOfK a * signOfK a = 1 := by
  rcases lt_or_gt_of_ne ha with h | h <;> simp [signOfK, h]

theorem signOfK_eq_neg_of_mul_lt_zero {a b : K} (h : a * b < 0) :
    signOfK b = -signOfK a := by
  have ha : a ≠ 0 := fun ha0 => by simp [ha0] at h
  have hmul : signOfK a * signOfK b = -1 := by rw [← signOfK_mul]; simp [signOfK, h]
  calc signOfK b = signOfK a * signOfK a * signOfK b := by rw [signOfK_sq ha, one_mul]
    _ = -signOfK a := by rw [mul_assoc, hmul, mul_neg_one]

theorem signOfK_intCast (z : ℤ) : signOfK (z : K) = z.sign := by
  rw [signOfK, sign_intCast, ← Int.sign_eq_sign]

theorem signOfK_neg_one_pow (k : ℕ) : signOfK ((-1 : K) ^ k) = (-1 : ℤ) ^ k := by
  rw [signOfK, sign_pow, SignType.coe_pow,
    show (-1 : K) = ((-1 : ℤ) : K) by simp, sign_intCast, ← Int.sign_eq_sign]
  rfl
end Signs

section HalfEdge

variable {κ : Type*} [Fintype κ] [DecidableEq κ] [LinearOrder κ]

/-- The label dropped when leaving `(T₁, T₂)`: `k₀` when `k₀ ∈ T₁ ∪ T₂` (the completely labelled
case), and otherwise the minimum element of `T₁ ∩ T₂` (the unique duplicate label when `k₀`-almost
completely labelled). -/
@[expose] def leaveLabel (T₁ T₂ : Finset κ) (k₀ : κ) : κ :=
  if k₀ ∈ T₁ ∪ T₂ then k₀
  else if hne : (T₁ ∩ T₂).Nonempty then (T₁ ∩ T₂).min' hne else k₀

/-- The label assignment `Fin m ⊕ Fin n → κ` attached to half-edge `(T₁, T₂, side)`: it enumerates
`T₁` and `T₂` in increasing order, substituting `k₀` for `leaveLabel T₁ T₂ k₀` on the chosen
side. -/
@[expose] def halfEdgeFun {m n : ℕ} (T₁ T₂ : Finset κ) (hT₁ : T₁.card = m) (hT₂ : T₂.card = n)
    (k₀ : κ) (side : Bool) : Fin m ⊕ Fin n → κ :=
  let ord₁ := (T₁.orderIsoOfFin hT₁).toEquiv
  let ord₂ := (T₂.orderIsoOfFin hT₂).toEquiv
  let l := leaveLabel T₁ T₂ k₀
  match side with
  | false => Sum.elim (fun i => if (ord₁ i : κ) = l then k₀ else (ord₁ i : κ))
      (fun j => (ord₂ j : κ))
  | true => Sum.elim (fun i => (ord₁ i : κ))
      (fun j => if (ord₂ j : κ) = l then k₀ else (ord₂ j : κ))

omit [LinearOrder κ] in
private lemma card_inter_eq_one_of_acl {m n : ℕ} (hcard : Fintype.card κ = m + n)
    {T₁ T₂ : Finset κ} (hT₁ : T₁.card = m) (hT₂ : T₂.card = n) {k₀ : κ}
    (hacl : ∀ k, k ≠ k₀ → k ∈ T₁ ∨ k ∈ T₂) (hk₀ : k₀ ∉ T₁ ∪ T₂) :
    (T₁ ∩ T₂).card = 1 := by
  have hunion : T₁ ∪ T₂ = Finset.univ.erase k₀ := by
    ext k; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun h hkeq => hk₀ (Finset.mem_union.2 (hkeq ▸ h)), hacl k⟩
  have hadd := Finset.card_union_add_card_inter T₁ T₂
  rw [hT₁, hT₂, hunion, Finset.card_erase_of_mem (Finset.mem_univ k₀), Finset.card_univ,
    hcard] at hadd
  have : 0 < Fintype.card κ := Fintype.card_pos_iff.2 ⟨k₀⟩
  omega

omit [LinearOrder κ] in
lemma inter_eq_empty_of_mem_union {m n : ℕ} (hcard : Fintype.card κ = m + n)
    {T₁ T₂ : Finset κ} (hT₁ : T₁.card = m) (hT₂ : T₂.card = n) {k₀ : κ}
    (hacl : ∀ k, k ≠ k₀ → k ∈ T₁ ∨ k ∈ T₂) (hk₀ : k₀ ∈ T₁ ∪ T₂) :
    T₁ ∩ T₂ = ∅ := by
  have hunion : T₁ ∪ T₂ = Finset.univ := by
    ext k; simp only [Finset.mem_univ, iff_true, Finset.mem_union]
    exact if hk : k = k₀ then hk ▸ Finset.mem_union.1 hk₀ else hacl k hk
  have hadd := Finset.card_union_add_card_inter T₁ T₂
  rw [hT₁, hT₂, hunion, Finset.card_univ, hcard] at hadd
  exact Finset.card_eq_zero.1 (by omega)

lemma mem_inter_of_acl_not_mem {m n : ℕ} (hcard : Fintype.card κ = m + n)
    {T₁ T₂ : Finset κ} (hT₁ : T₁.card = m) (hT₂ : T₂.card = n) {k₀ : κ}
    (hacl : ∀ k, k ≠ k₀ → k ∈ T₁ ∨ k ∈ T₂) (hk₀ : k₀ ∉ T₁ ∪ T₂) :
    leaveLabel T₁ T₂ k₀ ∈ T₁ ∩ T₂ ∧ T₁ ∩ T₂ = {leaveLabel T₁ T₂ k₀} := by
  obtain ⟨l, hl⟩ := Finset.card_eq_one.1 (card_inter_eq_one_of_acl hcard hT₁ hT₂ hacl hk₀)
  have hne : (T₁ ∩ T₂).Nonempty := ⟨l, by simp [hl]⟩
  have hleave : leaveLabel T₁ T₂ k₀ = l := by
    rw [leaveLabel, ite_eq_right hk₀, dite_eq_left hne]; simp [hl]
  exact hleave ▸ ⟨by simp [hl], hl⟩

private lemma halfEdgeFun_bijective_left {m n : ℕ} (hcard : Fintype.card κ = m + n)
    {T₁ T₂ : Finset κ} (hT₁ : T₁.card = m) (hT₂ : T₂.card = n) {k₀ : κ}
    (hacl : ∀ k, k ≠ k₀ → k ∈ T₁ ∨ k ∈ T₂) (hact : k₀ ∉ T₂) :
    Function.Bijective (halfEdgeFun T₁ T₂ hT₁ hT₂ k₀ false) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun a b hab => ?_, by simp [hcard]⟩
  let ord₁ := (T₁.orderIsoOfFin hT₁).toEquiv
  let ord₂ := (T₂.orderIsoOfFin hT₂).toEquiv
  by_cases hk₀ : k₀ ∈ T₁ ∪ T₂
  · have hdisj := Finset.eq_empty_iff_forall_notMem.1
      (inter_eq_empty_of_mem_union hcard hT₁ hT₂ hacl hk₀)
    have hval (x) : halfEdgeFun T₁ T₂ hT₁ hT₂ k₀ false x =
        Sum.elim (fun i => (ord₁ i : κ)) (fun j => (ord₂ j : κ)) x := by
      rcases x with i | j
      · simp only [halfEdgeFun, Sum.elim_inl, leaveLabel, hk₀, ↓reduceIte]
        split_ifs with h; · exact h.symm
        · rfl
      · rfl
    rw [hval a, hval b] at hab
    rcases a with i₁ | j₁ <;> rcases b with i₂ | j₂ <;>
      simp only [Sum.elim_inl, Sum.elim_inr] at hab
    · exact congrArg Sum.inl (ord₁.injective (Subtype.ext hab))
    · exact absurd (Finset.mem_inter.2 ⟨(ord₁ i₁).2, hab ▸ (ord₂ j₂).2⟩) (hdisj _)
    · exact absurd (Finset.mem_inter.2 ⟨hab ▸ (ord₁ i₂).2, (ord₂ j₁).2⟩) (hdisj _)
    · exact congrArg Sum.inr (ord₂.injective (Subtype.ext hab))
  · obtain ⟨_, hinter⟩ := mem_inter_of_acl_not_mem hcard hT₁ hT₂ hacl hk₀
    set l := leaveLabel T₁ T₂ k₀
    have hk₀1 : k₀ ∉ T₁ := fun h => hk₀ (Finset.mem_union.2 (.inl h))
    have hcross (i : Fin m) (j : Fin n)
        (h : (if (ord₁ i : κ) = l then k₀ else (ord₁ i : κ)) = (ord₂ j : κ)) : False := by
      split_ifs at h with h1
      · exact hact (h ▸ (ord₂ j).2)
      · have hm : (ord₁ i : κ) ∈ T₁ ∩ T₂ := Finset.mem_inter.2 ⟨(ord₁ i).2, h ▸ (ord₂ j).2⟩
        rw [hinter, Finset.mem_singleton] at hm; exact h1 hm
    rcases a with i₁ | j₁ <;> rcases b with i₂ | j₂
    · simp only [halfEdgeFun, Sum.elim_inl] at hab; split_ifs at hab with h1 h2
      · exact congrArg Sum.inl (ord₁.injective (Subtype.ext (h1.trans h2.symm)))
      · exact absurd (hab.symm ▸ (ord₁ i₂).2) hk₀1
      · exact absurd (hab ▸ (ord₁ i₁).2) hk₀1
      · exact congrArg Sum.inl (ord₁.injective (Subtype.ext hab))
    · exact (hcross i₁ j₂ hab).elim
    · exact (hcross i₂ j₁ hab.symm).elim
    · exact congrArg Sum.inr (ord₂.injective (Subtype.ext hab))

omit [Fintype κ] in
/-- Helper for swapping left and right tight bases along `Equiv.sumComm`. -/
private lemma halfEdgeFun_swap {m n : ℕ} (T₁ T₂ : Finset κ) (hT₁ : T₁.card = m)
    (hT₂ : T₂.card = n) (k₀ : κ) (side : Bool) :
    halfEdgeFun T₂ T₁ hT₂ hT₁ k₀ (!side) =
      halfEdgeFun T₁ T₂ hT₁ hT₂ k₀ side ∘ Equiv.sumComm (Fin n) (Fin m) := by
  funext x
  have hleave : leaveLabel T₂ T₁ k₀ = leaveLabel T₁ T₂ k₀ := by
    simp only [leaveLabel, Finset.union_comm T₂ T₁, Finset.inter_comm T₂ T₁]
  cases side <;> rcases x with i | j <;>
    simp only [halfEdgeFun, Bool.not_false, Bool.not_true, Function.comp_apply,
      Equiv.sumComm_apply, Sum.swap_inl, Sum.swap_inr, Sum.elim_inl, Sum.elim_inr, hleave]

theorem halfEdgeFun_bijective_of_acl {m n : ℕ} (hcard : Fintype.card κ = m + n)
    {T₁ T₂ : Finset κ} (hT₁ : T₁.card = m) (hT₂ : T₂.card = n) {k₀ : κ}
    (hacl : ∀ k, k ≠ k₀ → k ∈ T₁ ∨ k ∈ T₂) {side : Bool}
    (hact : if side then k₀ ∉ T₁ else k₀ ∉ T₂) :
    Function.Bijective (halfEdgeFun T₁ T₂ hT₁ hT₂ k₀ side) := by
  cases side
  · exact halfEdgeFun_bijective_left hcard hT₁ hT₂ hacl hact
  · have hswap := halfEdgeFun_bijective_left (by omega : Fintype.card κ = n + m) hT₂ hT₁
      (fun k hk => (hacl k hk).symm) hact
    have hcomp := halfEdgeFun_swap T₂ T₁ hT₂ hT₁ k₀ false
    simp only [Bool.not_false] at hcomp
    exact hcomp ▸ hswap.comp (Equiv.sumComm (Fin m) (Fin n)).bijective

end HalfEdge

section Orientation

variable {ι₁ ι₂ κ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Fintype ι₁] [Fintype ι₂] [Fintype κ] [DecidableEq κ] [LinearOrder κ]

/-- Shapley's orientation sign (`-1` or `1`, or `0` on invalid/inactive inputs) for a half-edge
`(T₁, T₂, side)` of two polyhedra `A₁`, `A₂`. -/
@[expose] noncomputable def halfEdgeIndex {m n : ℕ} (A₁ : Matrix κ ι₁ K) (A₂ : Matrix κ ι₂ K)
    (e₁ : Fin m ≃ ι₁) (e₂ : Fin n ≃ ι₂) (ref : Fin m ⊕ Fin n ≃ κ)
    (T₁ T₂ : Finset κ) (hT₁ : T₁.card = m) (hT₂ : T₂.card = n)
    (k₀ : κ) (side : Bool) : ℤ :=
  open Classical in
  if hbij : Function.Bijective (halfEdgeFun T₁ T₂ hT₁ hT₂ k₀ side) then
    let π : Equiv.Perm (Fin m ⊕ Fin n) := (Equiv.ofBijective _ hbij).trans ref.symm
    let M₁ := A₁.submatrix (fun i => (T₁.orderIsoOfFin hT₁ i : κ)) e₁
    let M₂ := A₂.submatrix (fun j => (T₂.orderIsoOfFin hT₂ j : κ)) e₂
    (Equiv.Perm.sign π : ℤ) * signOfK M₁.det * signOfK M₂.det
  else 0

omit [IsStrictOrderedRing K] [Fintype ι₁] [Fintype ι₂] in
private lemma halfEdgeIndex_swap {m n : ℕ} (A₁ : Matrix κ ι₁ K) (A₂ : Matrix κ ι₂ K)
    (e₁ : Fin m ≃ ι₁) (e₂ : Fin n ≃ ι₂) (ref : Fin m ⊕ Fin n ≃ κ)
    (T₁ T₂ : Finset κ) (hT₁ : T₁.card = m) (hT₂ : T₂.card = n)
    (k₀ : κ) (side : Bool) :
    halfEdgeIndex A₂ A₁ e₂ e₁ ((Equiv.sumComm (Fin n) (Fin m)).trans ref) T₂ T₁ hT₂ hT₁ k₀
        (!side) =
      halfEdgeIndex A₁ A₂ e₁ e₂ ref T₁ T₂ hT₁ hT₂ k₀ side := by
  classical
  have hcomp := halfEdgeFun_swap T₁ T₂ hT₁ hT₂ k₀ side
  by_cases hbij : Function.Bijective (halfEdgeFun T₁ T₂ hT₁ hT₂ k₀ side)
  · have hbij' : Function.Bijective (halfEdgeFun T₂ T₁ hT₂ hT₁ k₀ (!side)) :=
      hcomp ▸ hbij.comp (Equiv.sumComm (Fin n) (Fin m)).bijective
    rw [halfEdgeIndex, dite_eq_left hbij', halfEdgeIndex, dite_eq_left hbij]; dsimp only
    have hπ : (Equiv.ofBijective _ hbij').trans ((Equiv.sumComm (Fin n) (Fin m)).trans ref).symm =
        Equiv.permCongr (Equiv.sumComm (Fin m) (Fin n))
          ((Equiv.ofBijective _ hbij).trans ref.symm) := by
      ext x; simp [hcomp, Equiv.permCongr_apply]
    rw [hπ, Equiv.Perm.sign_permCongr]; ring
  · have hbij' : ¬ Function.Bijective (halfEdgeFun T₂ T₁ hT₂ hT₁ k₀ (!side)) := fun h => by
      have hc2 := halfEdgeFun_swap T₂ T₁ hT₂ hT₁ k₀ (!side)
      simp only [Bool.not_not] at hc2
      exact hbij (hc2 ▸ h.comp (Equiv.sumComm (Fin m) (Fin n)).bijective)
    rw [halfEdgeIndex, dite_eq_right hbij', halfEdgeIndex, dite_eq_right hbij]

omit [DecidableEq κ] [IsStrictOrderedRing K] in
private lemma det_tight_submatrix_ne_zero {k : ℕ} {ι : Type*} [Fintype ι]
    {A : Matrix κ ι K} {b : κ → K} {z : ι → K} (hz : IsVertex A b z) (e : Fin k ≃ ι)
    (hT : (tightRows A b z).card = k) :
    (A.submatrix (fun i => ((tightRows A b z).orderIsoOfFin hT i : κ)) e).det ≠ 0 := by
  classical
  rw [det_submatrix_col_equiv]
  exact hz.det_submatrix_ne_zero (e.symm.trans ((tightRows A b z).orderIsoOfFin hT).toEquiv)

private lemma units_coe_sign (u : ℤˣ) : (u : ℤ).sign = (u : ℤ) := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

omit [IsStrictOrderedRing K] in
/-- Every active half-edge of a `LemkeHowson.Node` has nonzero (`±1`) orientation index. -/
theorem halfEdgeIndex_ne_zero {m n : ℕ}
    {A₁ : Matrix κ ι₁ K} {b₁ : κ → K} {A₂ : Matrix κ ι₂ K} {b₂ : κ → K}
    (e₁ : Fin m ≃ ι₁) (e₂ : Fin n ≃ ι₂) (ref : Fin m ⊕ Fin n ≃ κ)
    (hcard : Fintype.card κ = m + n) {k₀ : κ} (p : Node A₁ b₁ A₂ b₂ k₀)
    {hT₁ : (tightRows A₁ b₁ p.x).card = m} {hT₂ : (tightRows A₂ b₂ p.y).card = n}
    {side : Bool} (hact : if side then k₀ ∉ tightRows A₁ b₁ p.x else k₀ ∉ tightRows A₂ b₂ p.y) :
    halfEdgeIndex A₁ A₂ e₁ e₂ ref (tightRows A₁ b₁ p.x) (tightRows A₂ b₂ p.y) hT₁ hT₂ k₀ side ≠
      0 := by
  classical
  have hbij := halfEdgeFun_bijective_of_acl hcard hT₁ hT₂ p.almostCompletelyLabeled hact
  rw [halfEdgeIndex, dite_eq_left hbij]
  dsimp only
  exact mul_ne_zero
    (mul_ne_zero (by simp [Units.ne_zero])
      (signOfK_ne_zero (det_tight_submatrix_ne_zero p.isVertex_x e₁ hT₁)))
    (signOfK_ne_zero (det_tight_submatrix_ne_zero p.isVertex_y e₂ hT₂))

omit [IsStrictOrderedRing K] in
/-- At a non-completely-labelled node (degree `2`), the two incident half-edges carry opposite
orientation indices. -/
theorem halfEdgeIndex_true_eq_neg_false {m n : ℕ}
    {A₁ : Matrix κ ι₁ K} {b₁ : κ → K} {A₂ : Matrix κ ι₂ K} {b₂ : κ → K}
    (e₁ : Fin m ≃ ι₁) (e₂ : Fin n ≃ ι₂) (ref : Fin m ⊕ Fin n ≃ κ)
    (hcard : Fintype.card κ = m + n) {k₀ : κ} (p : Node A₁ b₁ A₂ b₂ k₀)
    {hT₁ : (tightRows A₁ b₁ p.x).card = m} {hT₂ : (tightRows A₂ b₂ p.y).card = n}
    (hncl : ¬ CompletelyLabeled A₁ b₁ A₂ b₂ p.x p.y) :
    halfEdgeIndex A₁ A₂ e₁ e₂ ref (tightRows A₁ b₁ p.x) (tightRows A₂ b₂ p.y) hT₁ hT₂ k₀ true =
      -halfEdgeIndex A₁ A₂ e₁ e₂ ref (tightRows A₁ b₁ p.x) (tightRows A₂ b₂ p.y) hT₁ hT₂ k₀
        false := by
  classical
  set T₁ := tightRows A₁ b₁ p.x
  set T₂ := tightRows A₂ b₂ p.y
  have hk₀ : k₀ ∉ T₁ ∪ T₂ := fun hmem => hncl <| completelyLabeled_iff.2 fun k =>
    if hk : k = k₀ then Finset.mem_union.1 (hk ▸ hmem) else p.almostCompletelyLabeled k hk
  have hk₀1 : k₀ ∉ T₁ := fun h => hk₀ (Finset.mem_union.2 (.inl h))
  have hk₀2 : k₀ ∉ T₂ := fun h => hk₀ (Finset.mem_union.2 (.inr h))
  have hbij_f :=
    halfEdgeFun_bijective_of_acl hcard hT₁ hT₂ p.almostCompletelyLabeled (side := false) hk₀2
  have hbij_t :=
    halfEdgeFun_bijective_of_acl hcard hT₁ hT₂ p.almostCompletelyLabeled (side := true) hk₀1
  obtain ⟨hmem, _⟩ := mem_inter_of_acl_not_mem hcard hT₁ hT₂ p.almostCompletelyLabeled hk₀
  set l := leaveLabel T₁ T₂ k₀
  have hl₁ : l ∈ T₁ := (Finset.mem_inter.1 hmem).1
  have hl₂ : l ∈ T₂ := (Finset.mem_inter.1 hmem).2
  let ord₁ := (T₁.orderIsoOfFin hT₁).toEquiv
  let ord₂ := (T₂.orderIsoOfFin hT₂).toEquiv
  set a : Fin m := ord₁.symm ⟨l, hl₁⟩
  set b : Fin n := ord₂.symm ⟨l, hl₂⟩
  have ha : (ord₁ a : κ) = l := congrArg Subtype.val (ord₁.apply_symm_apply ⟨l, hl₁⟩)
  have hb : (ord₂ b : κ) = l := congrArg Subtype.val (ord₂.apply_symm_apply ⟨l, hl₂⟩)
  have hswap_fun : halfEdgeFun T₁ T₂ hT₁ hT₂ k₀ true =
      halfEdgeFun T₁ T₂ hT₁ hT₂ k₀ false ∘ Equiv.swap (Sum.inl a) (Sum.inr b) := by
    funext x
    rcases x with i | j
    · by_cases hi : i = a
      · subst hi
        dsimp only [halfEdgeFun, Function.comp_apply]
        rw [Equiv.swap_apply_left, Sum.elim_inl, Sum.elim_inr]
        exact ha.trans hb.symm
      · have hne_l : ((T₁.orderIsoOfFin hT₁).toEquiv i : κ) ≠ leaveLabel T₁ T₂ k₀ := fun h =>
          hi (ord₁.injective (Subtype.ext (h.trans ha.symm)))
        have hs : Equiv.swap (Sum.inl a) (Sum.inr b) (Sum.inl i) = Sum.inl i :=
          Equiv.swap_apply_of_ne_of_ne (by simpa using hi) (by simp)
        dsimp only [halfEdgeFun, Function.comp_apply]
        rw [hs]
        dsimp only [Sum.elim_inl]
        exact (ite_eq_right hne_l).symm
    · by_cases hj : j = b
      · subst hj
        dsimp only [halfEdgeFun, Function.comp_apply]
        rw [Equiv.swap_apply_right]
        dsimp only [Sum.elim_inl, Sum.elim_inr]
        have ha' : ((T₁.orderIsoOfFin hT₁).toEquiv a : κ) = leaveLabel T₁ T₂ k₀ := ha
        have hb' : ((T₂.orderIsoOfFin hT₂).toEquiv b : κ) = leaveLabel T₁ T₂ k₀ := hb
        rw [ite_eq_left hb', ite_eq_left ha']
      · have hne_l : ((T₂.orderIsoOfFin hT₂).toEquiv j : κ) ≠ leaveLabel T₁ T₂ k₀ := fun h =>
          hj (ord₂.injective (Subtype.ext (h.trans hb.symm)))
        have hs : Equiv.swap (Sum.inl a) (Sum.inr b) (Sum.inr j) = Sum.inr j :=
          Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using hj)
        dsimp only [halfEdgeFun, Function.comp_apply]
        rw [hs]
        dsimp only [Sum.elim_inr]
        exact ite_eq_right hne_l
  rw [halfEdgeIndex, dite_eq_left hbij_t, halfEdgeIndex, dite_eq_left hbij_f]
  dsimp only
  set π_f := (Equiv.ofBijective _ hbij_f).trans ref.symm
  set π_t := (Equiv.ofBijective _ hbij_t).trans ref.symm
  have hπ : π_t = π_f * Equiv.swap (Sum.inl a) (Sum.inr b) := by
    ext x
    simp only [π_t, π_f, Equiv.Perm.mul_apply, Equiv.trans_apply, Equiv.ofBijective_apply,
      hswap_fun, Function.comp_apply]
  have hsign : (Equiv.Perm.sign π_t : ℤ) = -(Equiv.Perm.sign π_f : ℤ) := by
    rw [hπ, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by simp)]; simp [Units.val_neg]
  change (Equiv.Perm.sign π_t : ℤ) * _ * _ = -((Equiv.Perm.sign π_f : ℤ) * _ * _)
  rw [hsign]; ring

omit [Fintype κ] [LinearOrder κ] in
private lemma exists_unique_entering_of_pivot {m : ℕ} {T₁ T₁' : Finset κ} {l : κ}
    (hT₁ : T₁.card = m) (hT₁' : T₁'.card = m) (hl : l ∈ T₁) (_hl' : l ∉ T₁')
    (hsub : T₁.erase l ⊆ T₁') :
    ∃ (l' : κ) (_hl'mem : l' ∈ T₁'), T₁.erase l = T₁'.erase l' := by
  have hsdiff : (T₁' \ T₁.erase l).card = 1 := by
    have hadd := Finset.card_sdiff_add_card_inter T₁' (T₁.erase l)
    rw [Finset.inter_eq_right.2 hsub, hT₁', Finset.card_erase_of_mem hl, hT₁] at hadd
    have : 1 ≤ m := hT₁ ▸ Finset.card_pos.2 ⟨l, hl⟩
    omega
  obtain ⟨l', hl's⟩ := Finset.card_eq_one.1 hsdiff
  have hl'm : l' ∈ T₁' \ T₁.erase l := hl's ▸ Finset.mem_singleton_self l'
  refine ⟨l', (Finset.mem_sdiff.1 hl'm).1, ?_⟩
  ext k; simp only [Finset.mem_erase]
  refine ⟨fun hk => ⟨fun h => (Finset.mem_sdiff.1 hl'm).2 (h ▸ Finset.mem_erase.2 hk),
    hsub (Finset.mem_erase.2 hk)⟩, fun ⟨hkne, hkT'⟩ => ?_⟩
  by_contra hnot
  have hks : k ∈ T₁' \ T₁.erase l :=
    Finset.mem_sdiff.2 ⟨hkT', fun hm => hnot (Finset.mem_erase.1 hm)⟩
  exact hkne (Finset.mem_singleton.1 (hl's ▸ hks))

private lemma leaveLabel_eq_dropped {m n : ℕ} (hcard : Fintype.card κ = m + n)
    {T₁ T₁' T₂ : Finset κ} (hT₁ : T₁.card = m) (hT₂ : T₂.card = n) {k₀ l : κ}
    (hacl : ∀ k, k ≠ k₀ → k ∈ T₁ ∨ k ∈ T₂) (hacl' : ∀ k, k ≠ k₀ → k ∈ T₁' ∨ k ∈ T₂)
    (hk₀2 : k₀ ∉ T₂) (hl : l ∈ T₁) (hl' : l ∉ T₁') :
    leaveLabel T₁ T₂ k₀ = l := by
  have hl_or : l ≠ k₀ → l ∈ T₂ := fun hne => (hacl' l hne).resolve_left hl'
  by_cases hk₀1 : k₀ ∈ T₁
  · have hmem_u : k₀ ∈ T₁ ∪ T₂ := Finset.mem_union.2 (.inl hk₀1)
    have hdisj := Finset.eq_empty_iff_forall_notMem.1
      (inter_eq_empty_of_mem_union hcard hT₁ hT₂ hacl hmem_u)
    have hl_eq : l = k₀ := by_contra fun hne =>
      hdisj l (Finset.mem_inter.2 ⟨hl, hl_or hne⟩)
    simp [leaveLabel, hmem_u, hl_eq]
  · have hk₀ : k₀ ∉ T₁ ∪ T₂ := fun h => (Finset.mem_union.1 h).elim hk₀1 hk₀2
    obtain ⟨_, hinter⟩ := mem_inter_of_acl_not_mem hcard hT₁ hT₂ hacl hk₀
    have hl_inter : l ∈ T₁ ∩ T₂ := Finset.mem_inter.2 ⟨hl, hl_or fun h => hk₀1 (h ▸ hl)⟩
    exact (Finset.mem_singleton.1 (hinter ▸ hl_inter)).symm

/-- Moving across a left (`A₁`) pivot edge of `LemkeHowson.graph` reverses
`halfEdgeIndex · false`. -/
theorem halfEdgeIndex_pivot_left_eq_neg {m n : ℕ}
    {A₁ : Matrix κ ι₁ K} {b₁ : κ → K} {A₂ : Matrix κ ι₂ K} {b₂ : κ → K}
    (hnd₁ : IsNondegenerateSystem A₁ b₁)
    (e₁ : Fin m ≃ ι₁) (e₂ : Fin n ≃ ι₂) (ref : Fin m ⊕ Fin n ≃ κ)
    (hcard : Fintype.card κ = m + n) {k₀ : κ} {p q : Node A₁ b₁ A₂ b₂ k₀}
    {hT₁p : (tightRows A₁ b₁ p.x).card = m} {hT₁q : (tightRows A₁ b₁ q.x).card = m}
    {hT₂p : (tightRows A₂ b₂ p.y).card = n} {hT₂q : (tightRows A₂ b₂ q.y).card = n}
    (hqy : p.y = q.y) (hne : p.x ≠ q.x) (hadj : (graph A₁ b₁ A₂ b₂ k₀).Adj p q) :
    halfEdgeIndex A₁ A₂ e₁ e₂ ref (tightRows A₁ b₁ q.x) (tightRows A₂ b₂ q.y) hT₁q hT₂q k₀
        false =
      -halfEdgeIndex A₁ A₂ e₁ e₂ ref (tightRows A₁ b₁ p.x) (tightRows A₂ b₂ p.y) hT₁p hT₂p k₀
        false := by
  classical
  have hvertexAdj : VertexAdj A₁ b₁ p.x q.x :=
    (graph_adj.1 hadj).elim (fun h => absurd h.1 hne) And.right
  set T₁p := tightRows A₁ b₁ p.x
  set T₁q := tightRows A₁ b₁ q.x
  set T₂p := tightRows A₂ b₂ p.y
  have hacl_q : ∀ k, k ≠ k₀ → k ∈ T₁q ∨ k ∈ T₂p := fun k hk => by
    simpa only [T₂p, hqy] using q.almostCompletelyLabeled k hk
  obtain ⟨l, hlp, hlq⟩ := Finset.not_subset.1
    fun h => hne (p.isVertex_x.eq_of_tightRows_subset h).symm
  have hsub : T₁p.erase l ⊆ T₁q := by
    have hinter_sub : T₁p ∩ T₁q ⊆ T₁p.erase l := fun k hk =>
      Finset.mem_erase.2 ⟨fun h => hlq (h ▸ (Finset.mem_inter.1 hk).2), (Finset.mem_inter.1 hk).1⟩
    rcases vertexAdj_iff.1 hvertexAdj with ⟨-, -, -, hcard_inter⟩
    change Fintype.card ι₁ ≤ (T₁p ∩ T₁q).card + 1 at hcard_inter
    have : Fintype.card ι₁ = m := (p.isVertex_x.card_tightRows hnd₁).symm.trans hT₁p
    have heq := Finset.eq_of_subset_of_card_le hinter_sub (by
      rw [Finset.card_erase_of_mem hlp, hT₁p]
      omega)
    exact heq ▸ Finset.inter_subset_right
  obtain ⟨l', hl'q, herase⟩ := exists_unique_entering_of_pivot hT₁p hT₁q hlp hlq hsub
  have hl'p : l' ∉ T₁p := fun hmem =>
    Finset.notMem_erase l' T₁q (herase ▸ Finset.mem_erase.2 ⟨fun h => hlq (h ▸ hl'q), hmem⟩)
  have hk₀2 : k₀ ∉ T₂p := fun hk2 => by
    have hdisj := Finset.eq_empty_iff_forall_notMem.1 (inter_eq_empty_of_mem_union hcard
      hT₁p hT₂p p.almostCompletelyLabeled (Finset.mem_union.2 (.inr hk2)))
    have hl2 : l ∉ T₂p := fun h => hdisj l (Finset.mem_inter.2 ⟨hlp, h⟩)
    exact (hacl_q l fun h => hl2 (h ▸ hk2)).elim hlq hl2
  have hleave_p := leaveLabel_eq_dropped hcard hT₁p hT₂p p.almostCompletelyLabeled hacl_q hk₀2
    hlp hlq
  have hleave_q := leaveLabel_eq_dropped hcard hT₁q hT₂p hacl_q p.almostCompletelyLabeled hk₀2
    hl'q hl'p
  suffices h : ∀ (T₂q : Finset κ) (hT₂q' : T₂q.card = n), T₂q = T₂p →
      halfEdgeIndex A₁ A₂ e₁ e₂ ref T₁q T₂q hT₁q hT₂q' k₀ false =
        -halfEdgeIndex A₁ A₂ e₁ e₂ ref T₁p T₂p hT₁p hT₂p k₀ false from
    h (tightRows A₂ b₂ q.y) hT₂q (by rw [← hqy])
  rintro _ hT₂q' rfl
  have hbij_p :=
    halfEdgeFun_bijective_of_acl hcard hT₁p hT₂p p.almostCompletelyLabeled (side := false) hk₀2
  have hbij_q := halfEdgeFun_bijective_of_acl hcard hT₁q hT₂p hacl_q (side := false) hk₀2
  rw [halfEdgeIndex, dite_eq_left hbij_q, halfEdgeIndex, dite_eq_left hbij_p]; dsimp only
  let ord₁p := (T₁p.orderIsoOfFin hT₁p).toEquiv
  let ord₁q := (T₁q.orderIsoOfFin hT₁q).toEquiv
  let e_piv : Fin m ≃ T₁q := pivotBasisEquiv ord₁p hlp hl'q herase
  set σ₁ : Equiv.Perm (Fin m) := e_piv.trans ord₁q.symm
  have hfun_comp (x : Fin m ⊕ Fin n) :
      halfEdgeFun T₁q T₂p hT₁q hT₂q' k₀ false (Equiv.sumCongr σ₁ (Equiv.refl (Fin n)) x) =
        halfEdgeFun T₁p T₂p hT₁p hT₂p k₀ false x := by
    rcases x with i | j
    swap
    · rfl
    dsimp only [Equiv.sumCongr_apply, Sum.map_inl, halfEdgeFun, Sum.elim_inl]
    rw [hleave_p, hleave_q]
    change (if (ord₁q (σ₁ i) : κ) = l' then k₀ else (ord₁q (σ₁ i) : κ)) =
      if (ord₁p i : κ) = l then k₀ else (ord₁p i : κ)
    have hσ_eq : (ord₁q (σ₁ i) : κ) = (e_piv i : κ) :=
      congrArg Subtype.val (ord₁q.apply_symm_apply (e_piv i))
    rw [hσ_eq, coe_pivotBasisEquiv_apply ord₁p hlp hl'q herase i]
    by_cases hi : i = ord₁p.symm ⟨l, hlp⟩
    · subst hi
      rw [congrArg Subtype.val (ord₁p.apply_symm_apply ⟨l, hlp⟩)]
      simp only [↓reduceIte]
    · have hor_ne_l : (ord₁p i : κ) ≠ l := fun h =>
        hi (ord₁p.injective (Subtype.ext (by simpa only [Equiv.apply_symm_apply] using h)))
      have hor_ne_l' : (ord₁p i : κ) ≠ l' :=
        (Finset.mem_erase.1 (herase ▸ Finset.mem_erase.2 ⟨hor_ne_l, (ord₁p i).2⟩)).1
      simp [hi, hor_ne_l, hor_ne_l']
  set π_p := (Equiv.ofBijective _ hbij_p).trans ref.symm
  set π_q := (Equiv.ofBijective _ hbij_q).trans ref.symm
  have hπ : π_p = π_q * Equiv.sumCongr σ₁ (Equiv.refl (Fin n)) := by
    ext x
    simp only [π_p, π_q, Equiv.Perm.mul_apply, Equiv.trans_apply, Equiv.ofBijective_apply,
      hfun_comp]
  have hsign_pi : (Equiv.Perm.sign π_p : ℤ) =
      (Equiv.Perm.sign π_q : ℤ) * (Equiv.Perm.sign σ₁ : ℤ) := by
    rw [hπ, Equiv.Perm.sign_mul, Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_refl, mul_one]
    simp [Units.val_mul]
  let M₁p := A₁.submatrix (fun i => (T₁p.orderIsoOfFin hT₁p i : κ)) e₁
  let M₁q := A₁.submatrix (fun i => (T₁q.orderIsoOfFin hT₁q i : κ)) e₁
  let e₁' : ι₁ ≃ T₁p := e₁.symm.trans ord₁p
  let e₂' : ι₁ ≃ T₁q := e₁.symm.trans ord₁q
  have hdet_lt := p.isVertex_x.det_submatrix_pivot_mul_lt_zero q.isVertex_x hne hlp hl'q herase
    e₁' e₂'
  dsimp only at hdet_lt
  have hM₁p_det : (A₁.submatrix (fun i => (e₁' i : κ)) id).det = M₁p.det :=
    (det_submatrix_col_equiv A₁ (fun i => (ord₁p i : κ)) e₁).symm
  have hM₁q_det : (A₁.submatrix (fun i => (e₂' i : κ)) id).det = M₁q.det :=
    (det_submatrix_col_equiv A₁ (fun i => (ord₁q i : κ)) e₁).symm
  have hperm_eq : (pivotBasisEquiv e₁' hlp hl'q herase).trans e₂'.symm =
      e₁.permCongr σ₁ := by
    ext i
    apply congrArg (fun z => e₁ (ord₁q.symm z))
    apply Subtype.ext
    rw [coe_pivotBasisEquiv_apply, coe_pivotBasisEquiv_apply]
    change (if i = e₁ (ord₁p.symm ⟨l, hlp⟩) then l' else (ord₁p (e₁.symm i) : κ)) =
      if e₁.symm i = ord₁p.symm ⟨l, hlp⟩ then l' else (ord₁p (e₁.symm i) : κ)
    simp only [← Equiv.symm_apply_eq e₁]
  rw [hM₁p_det, hM₁q_det, hperm_eq, Equiv.Perm.sign_permCongr] at hdet_lt
  have hsign_det : (Equiv.Perm.sign σ₁ : ℤ) * (signOfK M₁p.det * signOfK M₁q.det) = -1 := by
    have hneg1 : signOfK (((Equiv.Perm.sign σ₁ : ℤ) : K) * (M₁p.det * M₁q.det)) = -1 := by
      rw [signOfK, sign_neg hdet_lt]; rfl
    rwa [signOfK_mul, signOfK_mul, signOfK_intCast, units_coe_sign] at hneg1
  have hM₁q_ne : M₁q.det ≠ 0 := hM₁q_det ▸ q.isVertex_x.det_submatrix_ne_zero e₂'
  have h1 : signOfK M₁q.det = -((Equiv.Perm.sign σ₁ : ℤ) * signOfK M₁p.det) := by
    calc signOfK M₁q.det
        = -((Equiv.Perm.sign σ₁ : ℤ) * (signOfK M₁p.det * signOfK M₁q.det)) *
            signOfK M₁q.det := by rw [hsign_det]; ring
      _ = -((Equiv.Perm.sign σ₁ : ℤ) * signOfK M₁p.det) *
            (signOfK M₁q.det * signOfK M₁q.det) := by ring
      _ = -((Equiv.Perm.sign σ₁ : ℤ) * signOfK M₁p.det) := by rw [signOfK_sq hM₁q_ne, mul_one]
  change (Equiv.Perm.sign π_q : ℤ) * signOfK M₁q.det * _ =
    -((Equiv.Perm.sign π_p : ℤ) * signOfK M₁p.det * _)
  rw [h1, hsign_pi]; ring

/-- Moving across a right (`A₂`) pivot edge of `LemkeHowson.graph` reverses
`halfEdgeIndex · true`. -/
theorem halfEdgeIndex_pivot_right_eq_neg {m n : ℕ}
    {A₁ : Matrix κ ι₁ K} {b₁ : κ → K} {A₂ : Matrix κ ι₂ K} {b₂ : κ → K}
    (hnd₂ : IsNondegenerateSystem A₂ b₂)
    (e₁ : Fin m ≃ ι₁) (e₂ : Fin n ≃ ι₂) (ref : Fin m ⊕ Fin n ≃ κ)
    (hcard : Fintype.card κ = m + n) {k₀ : κ} {p q : Node A₁ b₁ A₂ b₂ k₀}
    {hT₁p : (tightRows A₁ b₁ p.x).card = m} {hT₁q : (tightRows A₁ b₁ q.x).card = m}
    {hT₂p : (tightRows A₂ b₂ p.y).card = n} {hT₂q : (tightRows A₂ b₂ q.y).card = n}
    (hpx : p.x = q.x) (hne : p.y ≠ q.y) (hadj : (graph A₁ b₁ A₂ b₂ k₀).Adj p q) :
    halfEdgeIndex A₁ A₂ e₁ e₂ ref (tightRows A₁ b₁ q.x) (tightRows A₂ b₂ q.y) hT₁q hT₂q k₀
        true =
      -halfEdgeIndex A₁ A₂ e₁ e₂ ref (tightRows A₁ b₁ p.x) (tightRows A₂ b₂ p.y) hT₁p hT₂p k₀
        true := by
  let p' : Node A₂ b₂ A₁ b₁ k₀ :=
    ⟨p.y, p.x, p.isVertex_y, p.isVertex_x, fun j hj => (p.almostCompletelyLabeled j hj).symm⟩
  let q' : Node A₂ b₂ A₁ b₁ k₀ :=
    ⟨q.y, q.x, q.isVertex_y, q.isVertex_x, fun j hj => (q.almostCompletelyLabeled j hj).symm⟩
  have hadj' : (graph A₂ b₂ A₁ b₁ k₀).Adj p' q' := by
    rcases (graph_adj.1 hadj) with ⟨hx, ha⟩ | ⟨hy, _⟩
    · exact graph_adj.2 (.inr ⟨hx, ha⟩)
    · exact absurd hy.symm (fun h => hne h.symm)
  have hsw_p := halfEdgeIndex_swap A₁ A₂ e₁ e₂ ref (tightRows A₁ b₁ p.x) (tightRows A₂ b₂ p.y)
    hT₁p hT₂p k₀ true
  have hsw_q := halfEdgeIndex_swap A₁ A₂ e₁ e₂ ref (tightRows A₁ b₁ q.x) (tightRows A₂ b₂ q.y)
    hT₁q hT₂q k₀ true
  simp only [Bool.not_true] at hsw_p hsw_q
  rw [← hsw_p, ← hsw_q]
  exact halfEdgeIndex_pivot_left_eq_neg hnd₂ e₂ e₁ ((Equiv.sumComm (Fin n) (Fin m)).trans ref)
    (by omega) (p := p') (q := q') (hT₁p := hT₂p) (hT₁q := hT₂q) (hT₂p := hT₁p) (hT₂q := hT₁q)
    hpx hne hadj'

omit [Fintype κ] [Fintype ι₁] [Fintype ι₂] in
private lemma exists_perm_signOfK_neg_one_submatrix {k : ℕ} {ι : Type*}
    (A : Matrix κ ι K) (e : Fin k ≃ ι) {f : Fin k → κ} (hf : Function.Injective f)
    {T : Finset κ} (hT : T.card = k) (hT_eq : T = Finset.univ.image f)
    (hA : A.submatrix f e = -1) :
    ∃ σ : Equiv.Perm (Fin k),
      (∀ i : Fin k, ((T.orderIsoOfFin hT).toEquiv i : κ) = f (σ i)) ∧
        signOfK (A.submatrix (fun i => (T.orderIsoOfFin hT i : κ)) e).det =
          (Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ k := by
  classical
  let eT : Fin k ≃ T := Equiv.ofBijective
    (fun i => ⟨f i, hT_eq ▸ Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun _ _ h => hf (congrArg Subtype.val h), by simp [Fintype.card_coe, hT]⟩)
  let σ : Equiv.Perm (Fin k) := (T.orderIsoOfFin hT).toEquiv.trans eT.symm
  have hσ_val : ∀ i : Fin k, ((T.orderIsoOfFin hT).toEquiv i : κ) = f (σ i) := fun i =>
    (congrArg Subtype.val (eT.apply_symm_apply ((T.orderIsoOfFin hT).toEquiv i))).symm
  have hM : A.submatrix (fun i => (T.orderIsoOfFin hT i : κ)) e =
      (-1 : Matrix (Fin k) (Fin k) K).submatrix σ id := by
    ext i j
    change A ((T.orderIsoOfFin hT).toEquiv i : κ) (e j) = (-1 : Matrix (Fin k) (Fin k) K) (σ i) j
    rw [hσ_val i, ← hA]
    rfl
  refine ⟨σ, hσ_val, ?_⟩
  rw [hM, Matrix.det_permute, Matrix.det_neg, Matrix.det_one, Fintype.card_fin, mul_one,
    signOfK_mul, signOfK_intCast, units_coe_sign, signOfK_neg_one_pow]

omit [Fintype ι₁] [Fintype ι₂] in
/-- When `T₁` and `T₂` select the `Sum.inl` and `Sum.inr` blocks of `ref`, and the corresponding
basis submatrices are `-1`, the orientation index equals `(-1) ^ (m + n)` for every `k₀` and
`side`. -/
theorem halfEdgeIndex_zero_zero {m n : ℕ}
    (A₁ : Matrix κ ι₁ K) (A₂ : Matrix κ ι₂ K)
    (e₁ : Fin m ≃ ι₁) (e₂ : Fin n ≃ ι₂) (ref : Fin m ⊕ Fin n ≃ κ)
    {T₁ T₂ : Finset κ} (hT₁ : T₁.card = m) (hT₂ : T₂.card = n)
    (hT₁_eq : T₁ = Finset.univ.image (ref ∘ Sum.inl))
    (hT₂_eq : T₂ = Finset.univ.image (ref ∘ Sum.inr))
    (hA₁ : A₁.submatrix (ref ∘ Sum.inl) e₁ = -1)
    (hA₂ : A₂.submatrix (ref ∘ Sum.inr) e₂ = -1)
    (k₀ : κ) (side : Bool) :
    halfEdgeIndex A₁ A₂ e₁ e₂ ref T₁ T₂ hT₁ hT₂ k₀ side = (-1 : ℤ) ^ (m + n) := by
  classical
  have huniv : T₁ ∪ T₂ = Finset.univ := by
    ext k
    simp only [Finset.mem_union, Finset.mem_univ, iff_true, hT₁_eq, hT₂_eq, Finset.mem_image,
      Function.comp_apply, true_and]
    rcases hx : ref.symm k with i | j
    · exact .inl ⟨i, by rw [← hx, Equiv.apply_symm_apply]⟩
    · exact .inr ⟨j, by rw [← hx, Equiv.apply_symm_apply]⟩
  have hleave : leaveLabel T₁ T₂ k₀ = k₀ := by simp [leaveLabel, huniv]
  obtain ⟨σ₁, hσ₁_val, hs₁⟩ := exists_perm_signOfK_neg_one_submatrix A₁ e₁
    (ref.injective.comp Sum.inl_injective) hT₁ hT₁_eq hA₁
  obtain ⟨σ₂, hσ₂_val, hs₂⟩ := exists_perm_signOfK_neg_one_submatrix A₂ e₂
    (ref.injective.comp Sum.inr_injective) hT₂ hT₂_eq hA₂
  have hcomp : halfEdgeFun T₁ T₂ hT₁ hT₂ k₀ side = ref ∘ Equiv.sumCongr σ₁ σ₂ := by
    funext x
    cases side <;> rcases x with i | j <;>
      dsimp only [halfEdgeFun, Function.comp_apply, Equiv.sumCongr_apply, Sum.map_inl,
        Sum.map_inr, Sum.elim_inl, Sum.elim_inr]
    · rw [hleave]
      split_ifs with h
      · exact h.symm.trans (hσ₁_val i)
      · exact hσ₁_val i
    · exact hσ₂_val j
    · exact hσ₁_val i
    · rw [hleave]
      split_ifs with h
      · exact h.symm.trans (hσ₂_val j)
      · exact hσ₂_val j
  have hbij : Function.Bijective (halfEdgeFun T₁ T₂ hT₁ hT₂ k₀ side) :=
    hcomp ▸ ref.bijective.comp (Equiv.sumCongr σ₁ σ₂).bijective
  rw [halfEdgeIndex, dite_eq_left hbij]; dsimp only
  have hπ : (Equiv.ofBijective _ hbij).trans ref.symm = Equiv.sumCongr σ₁ σ₂ := by
    ext x; simp [hcomp]
  rw [hπ, Equiv.Perm.sign_sumCongr, Units.val_mul, hs₁, hs₂]
  calc ((Equiv.Perm.sign σ₁ : ℤ) * (Equiv.Perm.sign σ₂ : ℤ)) *
        ((Equiv.Perm.sign σ₁ : ℤ) * (-1 : ℤ) ^ m) *
        ((Equiv.Perm.sign σ₂ : ℤ) * (-1 : ℤ) ^ n)
      = ((Equiv.Perm.sign σ₁ : ℤ) * (Equiv.Perm.sign σ₁ : ℤ)) *
          ((Equiv.Perm.sign σ₂ : ℤ) * (Equiv.Perm.sign σ₂ : ℤ)) *
          ((-1 : ℤ) ^ m * (-1 : ℤ) ^ n) := by ring
    _ = (-1 : ℤ) ^ (m + n) := by
        rw [Int.units_coe_mul_self, Int.units_coe_mul_self, ← pow_add]; ring

end Orientation

end Cslib.GameTheory.LemkeHowson
