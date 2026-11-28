/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.GroupTheory.SLTower.Chain

/-!
# Coordinates for the actions of the unitriangular subgroups

Every element of `SL_h(F₂)` gets a coordinate in `U h` for the left action of the `i`-th
unitriangular subgroup (`Cslib.SLTower.coQ`), and the free involutions given by the generators
and by the simple root elements get a choice of one element in every pair
(`Cslib.SLTower.FQ`, `Cslib.SLTower.FU`).

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Tower.Coord`.

## Main definitions

* `Cslib.SLTower.thQ i`: the `i`-th unitriangular subgroup inside `SL_h(F₂)`.
* `Cslib.SLTower.coQ i`: the coordinate for its left action.
* `Cslib.SLTower.FQ h2 k`, `Cslib.SLTower.FU l`: the first elements of the pairs.

## Main results

* `Cslib.SLTower.coQ_mul`: the coordinate is equivariant.
* `Cslib.SLTower.FQ_iff`, `Cslib.SLTower.FU_iff`: exactly one element of every pair is first.
-/

public section

namespace Cslib.SLTower

/-- Coordinates for the left action of a subgroup. -/
theorem exists_coord {P Q : Type*} [Group P] [Group Q] (φ : P →* Q) (hφ : Function.Injective φ) :
    ∃ co : Q → P, ∀ p q, co (φ p * q) = p * co q := by
  let r : Setoid Q :=
    { r := fun q q' => ∃ p, q' = φ p * q
      iseqv :=
          ⟨fun q => ⟨1, by simp⟩,
              fun {q q'} ⟨p, hp⟩ => ⟨p⁻¹, by rw [hp, map_inv, inv_mul_cancel_left]⟩,
        fun {q q' q''} ⟨p, hp⟩ ⟨p', hp'⟩ => ⟨p' * p, by rw [hp', hp, map_mul, mul_assoc]⟩⟩ }
  have h1 : ∀ q : Q, ∃ p,
      q = φ p * (Quotient.mk r q).out := fun q => Quotient.exact (Quotient.out_eq (Quotient.mk r q))
  choose co hco using h1
  refine ⟨co, fun p q => hφ ?_⟩
  have h2 : Quotient.mk r (φ p * q) = Quotient.mk r q :=
    (Quotient.sound (s := r) ⟨p, rfl⟩).symm
  have h3 : φ (co (φ p * q)) * (Quotient.mk r q).out = φ p * q := by
    simpa only [h2] using (hco (φ p * q)).symm
  apply mul_right_cancel (b := (Quotient.mk r q).out)
  rw [h3, map_mul, mul_assoc, ← hco q]

/-- One element of every pair of a free involution. -/
theorem exists_first {Q : Type*} [Finite Q] (i : Q → Q) (hi : ∀ q, i (i q) = q)
    (hne : ∀ q, i q ≠ q) :
    ∃ F : Q → Prop, ∀ q, F (i q) ↔ ¬ F q := by
  obtain ⟨N, ⟨φ⟩⟩ := Finite.exists_equiv_fin Q
  refine ⟨fun q => φ q < φ (i q), fun q => ?_⟩
  simp only [hi, not_lt, le_iff_lt_or_eq]
  exact ⟨Or.inl, fun h => h.resolve_right fun e => hne q (φ.injective e)⟩

variable {h n : ℕ} [NeZero h]

/-- The image of the i-th unitriangular subgroup in SL_h(F₂). -/
@[expose] noncomputable def thQ (i : Fin h) : U h →* SL2 h := (evG : G h 0 →* SL2 h).comp (th i)

theorem evG_th (i : Fin h) (u : U h) : evG (th i u : G h n) = thQ i u := by
  refine Subtype.ext ?_
  ext a b
  rw [thQ]
  change (evG (th0 i u.1 : G h n)).1 a b = (evG (th0 i u.1 : G h 0)).1 a b
  rw [evG_th0, evG_th0]

theorem thQ_injective (i : Fin h) : Function.Injective (thQ i : U h →* SL2 h) := by
  intro u v e
  exact Subtype.ext (evG_th0_injective (n := 0) i e)

/-- The coordinate of an element of SL_h(F₂) at its vertex of type i. -/
noncomputable def coQ (i : Fin h) : SL2 h → U h := (exists_coord (thQ i) (thQ_injective i)).choose

theorem coQ_mul (i : Fin h) (u : U h) (q : SL2 h) : coQ i (thQ i u * q) = u * coQ i q :=
  (exists_coord (thQ i) (thQ_injective i)).choose_spec u q

omit [NeZero h] in
theorem x_ne_one (l : Fin (h - 1)) : x h l ≠ 1 := by
  intro e
  have h1 := congrFun (congrFun (congrArg (fun u : U h => u.1.1) e) (lo l)) (hi l)
  simp [x_val, Matrix.one_apply_ne (lo_ne_hi l)] at h1

omit [NeZero h] in
theorem x_mul_self (l : Fin (h - 1)) : x h l * x h l = 1 := by
  refine Subtype.ext (Subtype.ext ?_)
  refine (Matrix.transvection_mul_transvection_same _ _ (lo_ne_hi l) (1 : ZMod 2) 1).trans ?_
  rw [show (1 : ZMod 2) + 1 = 0 from rfl, Matrix.transvection_zero]
  rfl

theorem exists_other (h2 : 2 ≤ h) (k : Fin h) : ∃ i : Fin h, k ≠ i :=
  ⟨k - 1, (sub_one_ne h2 k).symm⟩

theorem gen_ne (h2 : 2 ≤ h) (k : Fin h) : evG (gen h2 k : G h n) ≠ 1 := by
  obtain ⟨i, hi⟩ := exists_other h2 k
  obtain ⟨l, rfl⟩ := exists_sh hi
  rw [← th_x h2 i l]
  intro e
  exact x_ne_one l (evG_th_eq_one e)

/-- The first chambers of the pairs of type k. -/
theorem exists_firstQ (h2 : 2 ≤ h) (k : Fin h) :
    ∃ F : SL2 h → Prop, ∀ q, F (evG (gen h2 k : G h 0) * q) ↔ ¬ F q := by
  refine exists_first _ (fun q => ?_) fun q e => ?_
  · rw [← mul_assoc, ← map_mul, gen_mul_self, map_one, one_mul]
  · exact gen_ne (n := 0) h2 k (by simpa using e)

/-- The first chambers of the pairs of type k. -/
def FQ (h2 : 2 ≤ h) (k : Fin h) : SL2 h → Prop := (exists_firstQ h2 k).choose

theorem evG_gen (h2 : 2 ≤ h) (k : Fin h) : evG (gen h2 k : G h n) = evG (gen h2 k : G h 0) := by
  obtain ⟨i, hi⟩ := exists_other h2 k
  obtain ⟨l, rfl⟩ := exists_sh hi
  rw [← th_x h2 i l, ← th_x h2 i l, evG_th, evG_th]

theorem FQ_iff (h2 : 2 ≤ h) (k : Fin h) (q : SL2 h) : FQ h2 k (evG (gen h2 k : G h n) * q) ↔
    ¬ FQ h2 k q := by
  rw [evG_gen]
  exact (exists_firstQ h2 k).choose_spec q

omit [NeZero h] in
theorem exists_firstU (l : Fin (h - 1)) : ∃ F : U h → Prop, ∀ u, F (x h l * u) ↔ ¬ F u := by
  refine exists_first _ (fun u => ?_) fun u e => ?_
  · rw [← mul_assoc, x_mul_self, one_mul]
  · exact x_ne_one l (by simpa using e)

/-- The first elements of the pairs {u, x_l u}. -/
def FU (l : Fin (h - 1)) : U h → Prop := (exists_firstU l).choose

omit [NeZero h] in
theorem FU_iff (l : Fin (h - 1)) (u : U h) : FU l (x h l * u) ↔ ¬ FU l u :=
    (exists_firstU l).choose_spec u

end Cslib.SLTower
