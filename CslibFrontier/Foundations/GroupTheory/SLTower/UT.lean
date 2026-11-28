/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.WittVector.IsPoly

/-!
# The unitriangular group over `F₂`

`Cslib.SLTower.SL2 h` is `SL_h(F₂)` (which equals `GL_h(F₂)`), and `Cslib.SLTower.U h` its
subgroup of upper unitriangular matrices. The simple root elements `1 + E_{j,j+1}`
(`Cslib.SLTower.x`) generate the towers of the source; `U h` has order `2^(h(h−1)/2)`.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Tower.UT`.

## Main definitions

* `Cslib.SLTower.U h`: the upper unitriangular matrices, as a subgroup of `SL_h(F₂)`
  (membership: `Cslib.SLTower.mem_U`).
* `Cslib.SLTower.x h j`: the simple root element `1 + E_{j,j+1}`.
* `Cslib.SLTower.equivU h`: `U h` is parametrized by its entries above the diagonal.

## Main results

* `Cslib.SLTower.card_U`: `|U h| = 2^(h(h−1)/2)`.
-/

public section

namespace Cslib.SLTower

open Matrix Finset

/-- The group SL_h(F₂) = GL_h(F₂). -/
abbrev SL2 (h : ℕ) : Type := Matrix.SpecialLinearGroup (Fin h) (ZMod 2)

/-- Upper unitriangular matrices, as a submonoid of `SL_h(F₂)`. -/
private def UMonoid (h : ℕ) : Submonoid (SL2 h) where
  carrier := {A | ∀ i j, (j < i → A.val i j = 0) ∧ A.val i i = 1}
  one_mem' := fun i j => ⟨fun hij => Matrix.one_apply_ne hij.ne', Matrix.one_apply_eq i⟩
  mul_mem' := by
    intro A B hA hB i j
    have h1 : ∀ i j k, j < i → A.val i k * B.val k j = 0 := by
      intro i j k hij
      rcases lt_or_ge k i with hk | hk
      · rw [(hA i k).1 hk, zero_mul]
      · rw [(hB k j).1 (lt_of_lt_of_le hij hk), mul_zero]
    refine ⟨fun hij => ?_, ?_⟩
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
      exact Finset.sum_eq_zero fun k _ => h1 i j k hij
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Finset.sum_eq_single i]
      · rw [(hA i i).2, (hB i i).2, one_mul]
      · intro k _ hk
        rcases lt_or_gt_of_ne hk with h | h
        · rw [(hA i k).1 h, zero_mul]
        · rw [(hB k i).1 h, mul_zero]
      · simp

/-- Upper unitriangular matrices: the submonoid, closed under inverses since `SL_h(F₂)` is
finite. -/
def U (h : ℕ) : Subgroup (SL2 h) :=
  { UMonoid h with
    inv_mem' := fun {a} ha => by
      -- in a finite group `a⁻¹ = a ^ (orderOf a - 1)`
      have e : a⁻¹ = a ^ (orderOf a - 1) := by
        refine inv_eq_of_mul_eq_one_left ?_
        rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos a), pow_orderOf_eq_one]
      rw [e]
      exact (UMonoid h).pow_mem ha _ }

theorem mem_U {h : ℕ} {A : SL2 h} : A ∈ U h ↔ ∀ i j, (j < i → A.val i j = 0) ∧ A.val i i = 1 :=
  Iff.rfl

/-- The index j as a row. -/
@[expose] def lo {h : ℕ} (j : Fin (h - 1)) : Fin h := ⟨j.val, by omega⟩

/-- The index j + 1 as a column. -/
@[expose] def hi {h : ℕ} (j : Fin (h - 1)) : Fin h := ⟨j.val + 1, by omega⟩

theorem lo_lt_hi {h : ℕ} (j : Fin (h - 1)) : lo j < hi j := by
  rw [Fin.lt_def]; simp [lo, hi]

theorem lo_ne_hi {h : ℕ} (j : Fin (h - 1)) : lo j ≠ hi j := (lo_lt_hi j).ne

/-- The simple root elements 1 + E_{j,j+1}. -/
@[expose] def x (h : ℕ) (j : Fin (h - 1)) : U h :=
  ⟨⟨Matrix.transvection (lo j) (hi j) 1, Matrix.det_transvection_of_ne _ _ (lo_ne_hi j) 1⟩, by
    intro a b
    refine ⟨fun hab => ?_, ?_⟩
    · simp only [Matrix.transvection, Matrix.add_apply]
      rw [Matrix.one_apply_ne hab.ne', Matrix.single_apply_of_ne, add_zero]
      rintro ⟨rfl, rfl⟩
      exact absurd hab (lo_lt_hi j).not_gt
    · simp only [Matrix.transvection, Matrix.add_apply]
      rw [Matrix.one_apply_eq, Matrix.single_apply_of_ne, add_zero]
      rintro ⟨h1, h2⟩
      exact lo_ne_hi j (h1.trans h2.symm)⟩

theorem x_val (h : ℕ) (j : Fin (h - 1)) :
    ((x h j : SL2 h) : Matrix (Fin h) (Fin h) (ZMod 2)) = 1 + Matrix.single (lo j) (hi j) 1 := by
        rfl

/-- The entries above the diagonal are free. -/
noncomputable def equivU (h : ℕ) : U h ≃ ({p : Fin h × Fin h // p.1 < p.2} → ZMod 2) where
  toFun A | ⟨(i, j), _⟩ => ((A : SL2 h) : Matrix (Fin h) (Fin h) (ZMod 2)) i j
  invFun f :=
      ⟨⟨Matrix.of fun i j => if hij : i < j then f ⟨(i, j), hij⟩ else if i = j then 1 else 0, by
      rw [Matrix.det_of_isUpperTriangular]
      · simp
      · intro i j hij
        have hij' : j < i := hij
        simp [not_lt_of_gt hij', hij'.ne']⟩, by
    intro i j
    refine ⟨fun hij => ?_, ?_⟩
    · simp [not_lt_of_gt hij, hij.ne']
    · simp⟩
  left_inv A := by
    refine Subtype.ext (Subtype.ext ?_)
    ext i j
    simp only [Matrix.of_apply]
    split_ifs with h1 h2
    · rfl
    · rw [h2]; exact ((A.property j j).2).symm
    · exact ((A.property i j).1 (lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2))).symm
  right_inv f := by
    funext p
    obtain ⟨⟨i, j⟩, hij⟩ := p
    have hij' : i < j := hij
    simp [hij']

noncomputable instance (h : ℕ) : Fintype (U h) := Fintype.ofFinite _

/-- The order of U h. -/
theorem card_U (h : ℕ) : Fintype.card (U h) = 2 ^ (h * (h - 1) / 2) := by
  rw [Fintype.card_congr (equivU h), Fintype.card_fun, ZMod.card, Fintype.card_subtype,
    Fintype.card_product_filter_lt, Fintype.card_fin, Nat.choose_two_right]

end Cslib.SLTower
