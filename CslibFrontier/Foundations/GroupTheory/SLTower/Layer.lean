/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.GroupTheory.SLTower.Grp
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.WittVector.IsPoly

/-!
# The layers `1 + s^(n+1) A`

The kernel of the reduction `G h (n + 1) → G h n` consists of the matrices `1 + s^(n+1) A` with
`A` of trace zero over `F₂` (`Cslib.SLTower.lay`); it has order `2^(h² − 1)`, and the reduction
is onto. By induction, `|G h n| = |SL_h(F₂)| · 2^((h² − 1) n)`, and the kernel of the value at
`s = 0` is a 2-group of order `2^((h² − 1) n)`.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Tower.Layer`.

## Main definitions

* `Cslib.SLTower.redG`: the reduction of the groups.
* `Cslib.SLTower.lay A hA`: the element `1 + s^(n+1) A` for `A` of trace zero.

## Main results

* `Cslib.SLTower.exists_lay`, `Cslib.SLTower.redG_surjective`: the kernel and the image of the
  reduction.
* `Cslib.SLTower.card_G`, `Cslib.SLTower.card_ker_evG`: the orders.
-/

public section

namespace Cslib.SLTower

open Matrix Finset

variable {h n : ℕ} [NeZero h]

/-- Reduction of the groups. -/
noncomputable def redG : G h (n + 1) →* G h n := Matrix.SpecialLinearGroup.map (red (n + 1))

omit [NeZero h] in
theorem redG_apply (g : G h (n + 1)) (a b : Fin h) :
    (redG g).val a b = red (n + 1) (g.val a b) := by
    rfl

theorem s_sq (n : ℕ) : (s (n + 2) ^ (n + 1)) ^ 2 = 0 := by
  rw [← pow_mul]
  exact s_pow_ge (by omega)

/-- The matrix 1 + s^{n+1} A. -/
@[expose] noncomputable def layMat (n : ℕ) (A : Matrix (Fin h) (Fin h) (ZMod 2)) : Matrix (Fin h)
    (Fin h)
    (R (n + 2)) :=
  1 + s (n + 2) ^ (n + 1) • A.map (cst (n + 2))

omit [NeZero h] in
theorem det_layMat (A : Matrix (Fin h) (Fin h) (ZMod 2)) :
    (layMat n A).det = 1 + cst (n + 2) A.trace * s (n + 2) ^ (n + 1) := by
  rw [layMat, Matrix.det_one_add_smul, s_sq, mul_zero, add_zero]
  congr 2
  simp [Matrix.trace, map_sum]

omit [NeZero h] in
theorem layMat_mul (A B : Matrix (Fin h) (Fin h) (ZMod 2)) : layMat n A * layMat n B =
    layMat n (A + B) := by
  have h1 : s (n + 2) ^ (n + 1) * s (n + 2) ^ (n + 1) = 0 := by rw [← sq, s_sq]
  rw [layMat, layMat, layMat, add_mul, mul_add, mul_add, one_mul, one_mul, mul_one,
      smul_mul_smul_comm, h1,
    zero_smul, add_zero, Matrix.map_add _ (map_add _), smul_add]
  abel

/-- The element 1 + s^{n+1} A. -/
noncomputable def lay (A : Matrix (Fin h) (Fin h) (ZMod 2)) (hA : A.trace = 0) : G h (n + 1) :=
  ⟨layMat n A, by rw [det_layMat, hA, map_zero, zero_mul, add_zero]⟩

omit [NeZero h] in
theorem lay_val (A : Matrix (Fin h) (Fin h) (ZMod 2)) (hA : A.trace = 0) : (lay (n := n) A hA).val =
    layMat n A := by rfl

omit [NeZero h] in
theorem lay_mul (A B : Matrix (Fin h) (Fin h) (ZMod 2)) (hA : A.trace = 0) (hB : B.trace = 0) :
    lay (n := n) A hA * lay B hB = lay (A + B) (by rw [trace_add, hA, hB, add_zero]) :=
  Subtype.ext (layMat_mul A B)

omit [NeZero h] in
theorem layMat_injective : Function.Injective (layMat (h := h) n) := by
  intro A B e
  ext a b
  have h1 := congrFun (congrFun e a) b
  simp only [layMat, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h1
  have hx : s (n + 2) ^ (n + 1) * cst (n + 2) (A a b - B a b) = 0 := by
    rw [map_sub, mul_sub, add_left_cancel h1, sub_self]
  refine sub_eq_zero.1 ?_
  generalize A a b - B a b = x at hx ⊢
  fin_cases x
  · rfl
  · change s (n + 2) ^ (n + 1) * cst (n + 2) 1 = 0 at hx
    rw [map_one, mul_one] at hx
    exact absurd hx (s_pow_ne (by omega))

theorem red_s_pow (n : ℕ) : red (n + 1) (s (n + 2) ^ (n + 1)) = 0 := by
  rw [map_pow, red_s]
  exact s_pow_self _

omit [NeZero h] in
theorem redG_lay (A : Matrix (Fin h) (Fin h) (ZMod 2))
    (hA : A.trace = 0) : redG (lay (n := n) A hA) = 1 := by
  refine Subtype.ext (Matrix.ext fun a b => ?_)
  rw [redG_apply, lay_val, layMat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add,
    map_mul, red_s_pow, zero_mul, add_zero]
  by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

omit [NeZero h] in
/-- The kernel of the reduction is the layer. -/
theorem exists_lay {g : G h (n + 1)} (hg : redG g = 1) : ∃ A hA, g = lay A hA := by
  have h1 (a b : Fin h) : ∃ c : ZMod 2, g.val a b = (1 : Matrix (Fin h) (Fin h) (R (n + 2))) a b +
      s (n + 2) ^ (n + 1) * cst (n + 2) c := by
    obtain ⟨c, hc⟩ := exists_of_red_eq_zero (m := n + 1)
      (x := g.val a b - (1 : Matrix (Fin h) (Fin h) (R (n + 2))) a b) (by
        rw [map_sub, ← redG_apply, hg]
        by_cases hab : a = b <;> simp [Matrix.one_apply, hab])
    refine ⟨c, ?_⟩
    rw [mul_comm, ← hc]; abel
  choose A hA using h1
  have e : g.val = layMat n (Matrix.of A) :=
    Matrix.ext fun a b => by
      rw [hA, layMat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; rfl
  refine ⟨Matrix.of A, by_contra fun hne => ?_, Subtype.ext e⟩
  have h3 := congrArg (· - 1) g.property
  rw [e, det_layMat, add_sub_cancel_left, sub_self] at h3
  have h4 : (Matrix.of A).trace = 1 := by
    generalize (Matrix.of A).trace = x at hne
    fin_cases x
    · exact absurd rfl hne
    · rfl
  rw [h4, map_one, one_mul] at h3
  exact s_pow_ne (by omega) h3

/-- The reduction is onto. -/
theorem redG_surjective : Function.Surjective (redG : G h (n + 1) →* G h n) := by
  intro g
  choose f hf using red_surjective (n + 1)
  let A : Matrix (Fin h) (Fin h) (R (n + 2)) := g.val.map f
  have hA : A.map (red (n + 1)) = g.val := Matrix.ext fun a b => by simp [A, hf]
  have hd : red (n + 1) A.det = 1 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hA, g.property]
  have hdd : A.det * A.det = 1 := by
    obtain ⟨c, hc⟩ := exists_of_red_eq_zero (m := n + 1) (x := A.det - 1)
      (by rw [map_sub, hd, map_one, sub_self])
    rw [show A.det = 1 + cst (n + 2) c * s (n + 2) ^ (n + 1) by rw [← hc]; ring]
    linear_combination (cst (n + 2) c) ^ 2 * s_sq n +
      (cst (n + 2) c * s (n + 2) ^ (n + 1)) * two_eq_zero (n + 2)
  let B : Matrix (Fin h) (Fin h) (R (n + 2)) := A.updateRow 0 (A.det • A 0)
  have hB : B.det = 1 := by rw [Matrix.det_updateRow_smul, Matrix.updateRow_eq_self, hdd]
  refine ⟨(⟨B, hB⟩ : G h (n + 1)), Subtype.ext (Matrix.ext fun a b => ?_)⟩
  refine (redG_apply (⟨B, hB⟩ : G h (n + 1)) a b).trans ?_
  have h4 : red (n + 1) (A a b) = g.val a b := congrFun (congrFun hA a) b
  by_cases ha : a = 0
  · subst ha
    simp only [B, Matrix.updateRow_self, Pi.smul_apply, smul_eq_mul, map_mul, hd, one_mul, h4]
  · simp only [B, Matrix.updateRow_ne ha, h4]

/-- The trace-zero matrices. -/
def tr0 (h : ℕ) : AddSubgroup (Matrix (Fin h) (Fin h) (ZMod 2)) :=
    (Matrix.traceAddMonoidHom (Fin h) (ZMod 2)).ker

theorem card_tr0 : Nat.card (tr0 h) = 2 ^ (h ^ 2 - 1) := by
  have h1 := AddSubgroup.card_mul_index (tr0 h)
  have h2 : (tr0 h).index = 2 := by
    rw [tr0, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 fun c =>
      ⟨Matrix.single 0 0 c, by simp⟩, AddSubgroup.card_top, Nat.card_zmod]
  have h3 : Nat.card (Matrix (Fin h) (Fin h) (ZMod 2)) = 2 ^ (h ^ 2) := by
    rw [Nat.card_eq_fintype_card]
    change Fintype.card (Fin h → Fin h → ZMod 2) = _
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, ← pow_mul, sq]
  rw [h2, h3] at h1
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.one_le_pow _ _ (NeZero.pos h) : 1 ≤ h ^ 2)
  rw [hk, pow_add, pow_one] at h1
  rw [hk, Nat.add_sub_cancel_left]; omega

theorem card_ker_redG : Nat.card (redG : G h (n + 1) →* G h n).ker = 2 ^ (h ^ 2 - 1) := by
  rw [← card_tr0]
  refine (Nat.card_congr <| Equiv.ofBijective
    (fun A : tr0 h => ⟨lay A.val A.property, redG_lay A.val A.property⟩)
    ⟨fun A B e => Subtype.ext <| layMat_injective <|
      congrArg (fun g : (redG : G h (n + 1) →* G h n).ker => g.val.val) e,
     fun ⟨g, hg⟩ => ?_⟩).symm
  obtain ⟨A, hA, hgA⟩ := exists_lay hg
  exact ⟨⟨A, hA⟩, Subtype.ext hgA.symm⟩

theorem card_G_succ : Nat.card (G h (n + 1)) = Nat.card (G h n) * 2 ^ (h ^ 2 - 1) := by
  have h1 := Subgroup.card_mul_index (redG : G h (n + 1) →* G h n).ker
  rw [card_ker_redG, Subgroup.index_ker, MonoidHom.range_eq_top.2 redG_surjective,
      Subgroup.card_top] at h1
  rw [← h1, mul_comm]

theorem evG_bijective_zero : Function.Bijective (evG : G h 0 →* SL2 h) :=
  ⟨fun g g' e => Subtype.ext <| Matrix.ext fun a b => by
      rw [eq_cst_ev (g.val a b), eq_cst_ev (g'.val a b), ← evG_apply, ← evG_apply, e],
    fun A => ⟨th0 0 A, Subtype.ext <| Matrix.ext fun a b => by rw [evG_th0, sub_zero, sub_zero]⟩⟩

theorem evG_surjective : Function.Surjective (evG : G h n →* SL2 h) :=
  fun A => ⟨th0 0 A, Subtype.ext <| Matrix.ext fun a b => by rw [evG_th0, sub_zero, sub_zero]⟩

/-- The order of the group. -/
theorem card_G (h n : ℕ) [NeZero h] : Nat.card (G h n) = Nat.card (SL2 h) * 2 ^
    ((h ^ 2 - 1) * n) := by
  induction n with
  | zero =>
    rw [mul_zero, pow_zero, mul_one]
    exact Nat.card_congr (Equiv.ofBijective _ evG_bijective_zero)
  | succ n ih => rw [card_G_succ, ih, mul_assoc, ← pow_add, mul_add, mul_one]

/-- The kernel of the value at s = 0 is a 2-group. -/
theorem card_ker_evG : Nat.card (evG : G h n →* SL2 h).ker = 2 ^ ((h ^ 2 - 1) * n) := by
  have h1 := Subgroup.card_mul_index (evG : G h n →* SL2 h).ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 evG_surjective, Subgroup.card_top, card_G,
      mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1

end Cslib.SLTower
