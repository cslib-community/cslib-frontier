/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Equivalent
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Upper functionals and spectral points

An *upper functional* on the parties `I` (`Cslib.PartyTensor.UpperFunctional`) is a real
function `P ≥ 0` on the tensors over `I` with `P 1 = 1`, `P (s * t) ≤ P s * P t`, and
`P s ≤ ∑ k, P (b k)` whenever `s` is covered by the family `b`. A *spectral point*
(`Cslib.PartyTensor.SpectralPoint`) is a multiplicative upper functional,
`F (s * t) = F s * F t`. With the empty family, an upper functional is `0` at a tensor whose
array is `0` (`UpperFunctional.eq_zero`). Spectral points in this sense form a larger class than
the points of Strassen's asymptotic spectrum, which are in addition additive under direct sums and
normalized on unit tensors.

An upper functional is monotone for restriction and constant on equivalence classes, at least `1`
at a nonzero tensor and at most the rank; a spectral point is multiplicative on products of
families and on powers, and can be pulled back along a map of parties (`SpectralPoint.pull`,
`t ↦ φ (π t)`). Over a field, the *support point* is `1` at every tensor with a nonzero entry and
`0` at the zero tensor (`SpectralPoint.support`, the first example after Definition A.1).

The rank in coordinates: `t ≤ unit K I r` holds exactly when `t` is a sum of `r` products of
vectors (`PartyTensor.le_unit_iff`), if there is a party.

## Main definitions

* `Cslib.PartyTensor.UpperFunctional`: upper functionals.
* `Cslib.PartyTensor.SpectralPoint`: spectral points, multiplicative upper functionals.
* `Cslib.PartyTensor.SpectralPoint.pull`: the pull-back along a map of parties.
* `Cslib.PartyTensor.SpectralPoint.support`: the support point.

## Main results

* `Cslib.PartyTensor.UpperFunctional.monotone`, `Cslib.PartyTensor.UpperFunctional.congr`:
  monotone for restriction, equal on equivalent tensors.
* `Cslib.PartyTensor.UpperFunctional.one_le`, `Cslib.PartyTensor.UpperFunctional.le_of_le_unit`,
  `Cslib.PartyTensor.UpperFunctional.le_card`: `1 ≤ P t ≤ rank t ≤ #entries` for a nonzero `t`.
* `Cslib.PartyTensor.SpectralPoint.map_prod`, `Cslib.PartyTensor.SpectralPoint.map_pow`:
  multiplicativity on families and powers.
* `Cslib.PartyTensor.le_unit_iff`: rank bounds in coordinates.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Definition A.1 and §A.4 of the paper; modules `Ov.Core.Tensor` (`Spec`), `Ov.Core.Spec`,
  `Ov.Duality.PreSpec` (`PreSpec` is an upper functional)
-/

public section

namespace Cslib.PartyTensor

open Finset

variable {K : Type} [CommSemiring K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
  [DecidableEq J]

/-! ### Rank -/

/-- Rank in coordinates: `t` is a restriction of the unit tensor of size `r` if and only if it is
a sum of `r` products of vectors. -/
theorem le_unit_iff [Nonempty I] {t : PartyTensor K I} {r : ℕ} :
    t ≤ unit K I r ↔ ∃ u : Fin r → ∀ p, t.Index p → K, ∀ x, t.entry x = ∑ s, ∏ p, u s p (x p) := by
  have key (L : ∀ p, t.Index p → Fin r → K) (x : ∀ p, t.Index p) :
      localApply L (unit K I r).entry x = ∑ s, ∏ p, L p (x p) s := by
    let p₀ : I := Classical.arbitrary I
    symm
    refine Finset.sum_of_injOn (fun s _ => s) (fun a _ b _ h => congr_fun h p₀)
      (fun _ _ => by simp) (fun y _ hy => ?_) (fun s _ => by simp [unit_entry])
    rw [unit_entry, ite_eq_right fun h => hy ⟨y p₀, by simp, funext fun p => h p₀ p⟩, mul_zero]
  exact ⟨fun ⟨L, hL⟩ => ⟨fun s p a => L p a s, fun x => (hL x).trans (key L x)⟩,
    fun ⟨u, hu⟩ => ⟨fun p a s => u s p a,
      fun x => (hu x).trans (key (fun p a s => u s p a) x).symm⟩⟩

/-- A tensor of rank at most `r` is covered by `r` copies of `1`. -/
theorem coveredBy_one_of_le_unit [Nonempty I] {t : PartyTensor K I} {r : ℕ}
    (h : t ≤ unit K I r) : t.CoveredBy fun _ : Fin r => (1 : PartyTensor K I) := by
  obtain ⟨u, hu⟩ := le_unit_iff.1 h
  exact coveredBy_iff.2 ⟨fun s x => ∏ p, u s p (x p), hu,
    fun s => le_of_map (fun p a => u s p a) (fun _ _ => ()) fun _ => (mul_one _).symm⟩

/-- Every tensor has rank at most the number of its entries. -/
theorem le_unit_card [Nonempty I] (t : PartyTensor K I) :
    t ≤ unit K I (Fintype.card (∀ p, t.Index p)) := by
  classical
  let p₀ : I := Classical.arbitrary I
  let e := (Fintype.equivFin (∀ p, t.Index p)).symm
  refine le_unit_iff.2
    ⟨fun s p a => if a = e s p then (if p = p₀ then t.entry (e s) else 1) else 0, fun x => ?_⟩
  rw [Finset.sum_eq_single (e.symm x) (fun s _ hs => ?_) (by simp)]
  · simp
  obtain ⟨p, hp⟩ := Function.ne_iff.1 (show x ≠ e s from fun h => hs (by simp [h]))
  exact Finset.prod_eq_zero (Finset.mem_univ p) (ite_eq_right hp)

/-! ### Upper functionals -/

/-- An *upper functional* on the tensors over the parties `I`: a real function `P ≥ 0` with
`P 1 = 1`, `P (s * t) ≤ P s * P t`, and `P s ≤ ∑ k, P (b k)` whenever `s` is covered by the
`b k`. -/
structure UpperFunctional (K : Type) [CommSemiring K] (I : Type) [Fintype I] [DecidableEq I] where
  /-- The value of the upper functional at a tensor. -/
  toFun : PartyTensor K I → ℝ
  nonneg : ∀ t, 0 ≤ toFun t
  map_one : toFun 1 = 1
  map_mul_le : ∀ s t, toFun (s * t) ≤ toFun s * toFun t
  le_sum : ∀ {κ : Type} [Fintype κ] (s : PartyTensor K I) (b : κ → PartyTensor K I),
    s.CoveredBy b → toFun s ≤ ∑ k, toFun (b k)

/-- A *spectral point* on the tensors over the parties `I`: a multiplicative upper functional. -/
structure SpectralPoint (K : Type) [CommSemiring K] (I : Type) [Fintype I] [DecidableEq I]
    extends UpperFunctional K I where
  map_mul : ∀ s t, toFun (s * t) = toFun s * toFun t
  map_mul_le s t := (map_mul s t).le

namespace UpperFunctional

instance : CoeFun (UpperFunctional K I) fun _ => PartyTensor K I → ℝ := ⟨UpperFunctional.toFun⟩

variable (P : UpperFunctional K I)

/-- An upper functional is monotone for restriction. -/
theorem monotone : Monotone P := fun s t h => by
  simpa using P.le_sum s _ (CoveredBy.single h)

/-- Equivalent tensors have the same value. -/
theorem congr {s t : PartyTensor K I} (h : AntisymmRel (· ≤ ·) s t) : P s = P t :=
  le_antisymm (P.monotone h.1) (P.monotone h.2)

/-- An upper functional is `0` at a tensor whose array is `0`. -/
theorem eq_zero {t : PartyTensor K I} (h : ∀ x, t.entry x = 0) : P t = 0 :=
  le_antisymm (by simpa using P.le_sum t (fun k : Empty => k.elim) (.of_entry_eq_zero h _))
    (P.nonneg t)

/-- An upper functional is subadditive for sums of arrays. -/
theorem le_sum_entry {κ : Type} [Fintype κ] (s : PartyTensor K I) (v : κ → (∀ p, s.Index p) → K)
    (h : ∀ x, s.entry x = ∑ k, v k x) : P s ≤ ∑ k, P (s.withEntry (v k)) :=
  P.le_sum s _ (CoveredBy.withEntry s v h)

/-- An upper functional is at least `1` at a tensor with a nonzero entry, if there is a party. -/
theorem one_le {K : Type} [Field K] (P : UpperFunctional K I) [Nonempty I] {t : PartyTensor K I}
    {y : ∀ p, t.Index p} (h : t.entry y ≠ 0) : 1 ≤ P t :=
  P.map_one ▸ P.monotone (one_le_of_entry_ne_zero h)

/-- An upper functional is at most the rank. -/
theorem le_of_le_unit [Nonempty I] {t : PartyTensor K I} {r : ℕ} (h : t ≤ unit K I r) :
    P t ≤ r := by
  simpa [P.map_one] using P.le_sum t _ (coveredBy_one_of_le_unit h)

/-- An upper functional is at most the number of entries. -/
theorem le_card [Nonempty I] (t : PartyTensor K I) : P t ≤ Fintype.card (∀ p, t.Index p) :=
  P.le_of_le_unit (le_unit_card t)

/-- A restriction of a product is at most the product of the values. -/
theorem le_mul {s t u : PartyTensor K I} (h : s ≤ t * u) : P s ≤ P t * P u :=
  (P.monotone h).trans (P.map_mul_le t u)

/-- An upper functional as a function on classes. -/
@[expose] def lift (P : UpperFunctional K I) : Antisymmetrization (PartyTensor K I) (· ≤ ·) → ℝ :=
  Quotient.lift P fun _ _ => P.congr

@[simp] theorem lift_toAntisymmetrization (P : UpperFunctional K I) (t : PartyTensor K I) :
    P.lift (toAntisymmetrization (· ≤ ·) t) = P t := rfl

end UpperFunctional

namespace SpectralPoint

instance : CoeFun (SpectralPoint K I) fun _ => PartyTensor K I → ℝ := ⟨fun F => F.toFun⟩

variable (F : SpectralPoint K I)

/-- A spectral point as a monoid homomorphism from the classes of tensors to `ℝ`. -/
@[expose] def toMonoidHom : Antisymmetrization (PartyTensor K I) (· ≤ ·) →* ℝ where
  toFun := F.lift
  map_one' := F.map_one
  map_mul' x y := by
    induction x using Antisymmetrization.ind
    induction y using Antisymmetrization.ind
    exact F.map_mul _ _

@[simp] theorem toMonoidHom_toAntisymmetrization (t : PartyTensor K I) :
    F.toMonoidHom (toAntisymmetrization (· ≤ ·) t) = F t := rfl

/-- A spectral point at the product of a family. -/
theorem map_prod {κ : Type} [Fintype κ] [DecidableEq κ] (b : κ → PartyTensor K I) :
    F (prod b) = ∏ k, F (b k) := by
  simp only [← toMonoidHom_toAntisymmetrization, toAntisymmetrization_prod, _root_.map_prod]

/-- A spectral point at a power. -/
theorem map_pow (t : PartyTensor K I) (k : ℕ) : F (t ^ k) = F t ^ k := by
  simp only [← toMonoidHom_toAntisymmetrization, toAntisymmetrization_pow, _root_.map_pow]

/-- A restriction of the product of a family is at most the product of the values. -/
theorem le_prod {κ : Type} [Fintype κ] [DecidableEq κ] {s : PartyTensor K I}
    {b : κ → PartyTensor K I} (h : s ≤ prod b) : F s ≤ ∏ k, F (b k) :=
  F.map_prod b ▸ F.monotone h

/-- The pull-back of a spectral point along a map `π` of parties: a tensor over `J` has the
value of its push-forward, in which the leg `j` is held by `π j`. -/
@[expose] def pull (π : J → I) : SpectralPoint K J where
  toFun t := F (push π t)
  nonneg _ := F.nonneg _
  map_one := by rw [F.congr (antisymmRel_push_one π), F.map_one]
  map_mul s t := by rw [F.congr (antisymmRel_push_mul π s t), F.map_mul]
  le_sum s b h := F.le_sum _ _ (h.push π)

@[simp] theorem pull_apply (π : J → I) (t : PartyTensor K J) : F.pull π t = F (push π t) := rfl

private theorem entry_eq_zero_of_coveredBy {κ : Type} [Fintype κ] {s : PartyTensor K I}
    {b : κ → PartyTensor K I} (h : s.CoveredBy b) (hb : ∀ k y, (b k).entry y = 0) (x) :
    s.entry x = 0 := by
  obtain ⟨L, hL⟩ := h
  rw [hL x]
  exact Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun y _ => by simp [hb k y]

open Classical in
/-- The *support point*: `1` at every tensor with a nonzero entry and `0` at the zero tensor (the
first example after Definition A.1). -/
noncomputable def support (K : Type) [Field K] (I : Type) [Fintype I] [DecidableEq I] :
    SpectralPoint K I where
  toFun t := if ∃ x, t.entry x ≠ 0 then 1 else 0
  nonneg t := by split_ifs <;> norm_num
  map_one := ite_eq_left ⟨fun _ => (), one_ne_zero⟩
  map_mul s t := by
    have key : (∃ z, (s * t).entry z ≠ 0) ↔ (∃ x, s.entry x ≠ 0) ∧ ∃ y, t.entry y ≠ 0 := by
      constructor
      · rintro ⟨z, hz⟩
        rw [mul_entry] at hz
        exact ⟨⟨_, left_ne_zero_of_mul hz⟩, _, right_ne_zero_of_mul hz⟩
      · rintro ⟨⟨x, hx⟩, y, hy⟩
        exact ⟨fun p => (x p, y p), mul_ne_zero hx hy⟩
    by_cases hs : ∃ x, s.entry x ≠ 0 <;> by_cases ht : ∃ y, t.entry y ≠ 0 <;> simp [key, hs, ht]
  le_sum s b h := by
    have h0 : ∀ k, (0 : ℝ) ≤ if ∃ x, (b k).entry x ≠ 0 then 1 else 0 := fun k => by
      split_ifs <;> norm_num
    split_ifs with hs
    · by_contra hlt
      obtain ⟨x, hx⟩ := hs
      refine hx (entry_eq_zero_of_coveredBy h (fun k y => ?_) x)
      by_contra hy
      have := Finset.single_le_sum (fun k _ => h0 k) (Finset.mem_univ k)
      rw [ite_eq_left ⟨y, hy⟩] at this
      linarith
    · exact Finset.sum_nonneg fun k _ => h0 k

open Classical in
@[simp] theorem support_apply {K : Type} [Field K] (t : PartyTensor K I) :
    support K I t = if ∃ x, t.entry x ≠ 0 then 1 else 0 := by
  rfl

end SpectralPoint

end Cslib.PartyTensor
