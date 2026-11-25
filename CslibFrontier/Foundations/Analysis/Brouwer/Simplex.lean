/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Topology/MetricSpace/Brouwer.lean`)

public import CslibFrontier.Foundations.Analysis.Brouwer
import Mathlib.Algebra.BigOperators.Field

/-!
# Brouwer's fixed-point theorem on products of simplices

`Cslib.Brouwer.exists_isFixedPt_cube` is Brouwer's fixed-point theorem for the cube
`[0, 1] ^ n`. This file transfers it to the cube over any finite index type and to finite
products of standard simplices, the spaces of mixed strategy profiles of finite games.

The transfer is by retraction: if every continuous self-map of `A` has a fixed point and `B` is a
retract of `A` (there are continuous `φ : A → B` and `ψ : B → A` with `φ ∘ ψ = id` on `B`), then a
fixed point of `ψ ∘ f ∘ φ` is mapped by `φ` to a fixed point of `f`. A product of simplices is a
retract of the cube on the disjoint union of their vertex sets: the retraction clips each block of
coordinates at `0` and rescales it or spreads the missing mass uniformly.

Points of simplices are plain vectors with nonnegative entries summing to `1`, rather than
Mathlib's `Convexity.StdSimplex`, so that they can be fed to continuous maps on `ι → ℝ`.

## Main results

* `Cslib.Brouwer.exists_isFixedPt_of_leftInvOn`: the fixed-point property passes to retracts.
* `Cslib.Brouwer.exists_isFixedPt_cube_of_finite`: Brouwer's theorem for the cube `[0, 1] ^ κ`
  for a finite type `κ`.
* `Cslib.Brouwer.exists_isFixedPt_pi_simplex`: **Brouwer's fixed-point theorem** for a finite
  product of standard simplices.

Arbitrary compact convex sets are not treated here.
-/

public section

namespace Cslib.Brouwer

open Set Finset Function

/-- The fixed-point property passes to retracts: if every continuous self-map of `A` has a fixed
point, and `φ` and `ψ` are continuous maps between `A` and `B` with `φ ∘ ψ = id` on `B`, then
every continuous self-map of `B` has a fixed point. -/
theorem exists_isFixedPt_of_leftInvOn {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y}
    (hA : ∀ g : X → X, MapsTo g A A → ContinuousOn g A → ∃ x ∈ A, IsFixedPt g x)
    {φ : X → Y} {ψ : Y → X} (hφ : MapsTo φ A B) (hψ : MapsTo ψ B A) (hφc : ContinuousOn φ A)
    (hψc : ContinuousOn ψ B) (hinv : LeftInvOn φ ψ B) {f : Y → Y} (hf : MapsTo f B B)
    (hfc : ContinuousOn f B) : ∃ y ∈ B, IsFixedPt f y := by
  obtain ⟨x, hx, hfix⟩ := hA (ψ ∘ f ∘ φ) (hψ.comp (hf.comp hφ))
    (hψc.comp (hfc.comp hφc hφ) (hf.comp hφ))
  exact ⟨φ x, hφ hx, (hinv (hf (hφ hx))).symm.trans (congrArg φ hfix)⟩

/-- **Brouwer's fixed-point theorem** for the cube `[0, 1] ^ κ` over a finite type `κ`. -/
theorem exists_isFixedPt_cube_of_finite {κ : Type*} [Finite κ] {f : (κ → ℝ) → κ → ℝ}
    (hf : MapsTo f (Icc 0 1) (Icc 0 1)) (hc : ContinuousOn f (Icc 0 1)) :
    ∃ x ∈ Icc (0 : κ → ℝ) 1, IsFixedPt f x := by
  have := Fintype.ofFinite κ
  let e := Fintype.equivFin κ
  exact exists_isFixedPt_of_leftInvOn (A := Icc (0 : Fin (Fintype.card κ) → ℝ) 1)
    (B := Icc (0 : κ → ℝ) 1) (fun _ hg hgc => exists_isFixedPt_cube hg hgc)
    (φ := fun x k => x (e k)) (ψ := fun y j => y (e.symm j))
    (fun x hx => ⟨fun k => hx.1 (e k), fun k => hx.2 (e k)⟩)
    (fun y hy => ⟨fun j => hy.1 (e.symm j), fun j => hy.2 (e.symm j)⟩)
    (continuous_pi fun k => continuous_apply (e k)).continuousOn
    (continuous_pi fun j => continuous_apply (e.symm j)).continuousOn
    (fun y _ => funext fun k => congrArg y (e.symm_apply_apply k)) hf hc

/-- The total positive mass `∑ k, max (x k) 0` of a vector. -/
private noncomputable def posMass {κ : Type*} [Fintype κ] (x : κ → ℝ) : ℝ :=
  ∑ k, max (x k) 0

/-- A retraction of `κ → ℝ` onto the standard simplex: clip at `0`, then scale down if the mass
exceeds `1`, and spread the missing mass uniformly if it is below `1`. -/
private noncomputable def simplexRetraction {κ : Type*} [Fintype κ] (x : κ → ℝ) (k : κ) : ℝ :=
  max (x k) 0 / max (posMass x) 1 + (1 - min (posMass x) 1) / Fintype.card κ

private theorem continuous_posMass {κ : Type*} [Fintype κ] :
    Continuous (posMass : (κ → ℝ) → ℝ) :=
  continuous_finsetSum _ fun k _ => (continuous_apply k).max continuous_const

private theorem continuous_simplexRetraction {κ : Type*} [Fintype κ] (k : κ) :
    Continuous fun x : κ → ℝ => simplexRetraction x k :=
  (((continuous_apply k).max continuous_const).div₀ (continuous_posMass.max continuous_const)
    fun _ => (zero_lt_one.trans_le (le_max_right _ _)).ne').add
    (((continuous_const.sub (continuous_posMass.min continuous_const))).div_const _)

private theorem simplexRetraction_nonneg {κ : Type*} [Fintype κ] (x : κ → ℝ) (k : κ) :
    0 ≤ simplexRetraction x k :=
  add_nonneg (div_nonneg (le_max_right _ _) (zero_le_one.trans (le_max_right _ _)))
    (div_nonneg (sub_nonneg.2 (min_le_right _ _)) (Nat.cast_nonneg _))

private theorem sum_simplexRetraction {κ : Type*} [Fintype κ] [Nonempty κ] (x : κ → ℝ) :
    ∑ k, simplexRetraction x k = 1 := by
  have hcard : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  unfold simplexRetraction
  rw [sum_add_distrib, ← sum_div, sum_const, card_univ, nsmul_eq_mul, mul_div_cancel₀ _ hcard]
  change posMass x / max (posMass x) 1 + (1 - min (posMass x) 1) = 1
  rcases le_total (posMass x) 1 with h | h
  · rw [max_eq_right h, min_eq_left h, div_one]; ring
  · rw [max_eq_left h, min_eq_right h, div_self (zero_lt_one.trans_le h).ne']; ring

private theorem simplexRetraction_eq {κ : Type*} [Fintype κ] {x : κ → ℝ}
    (hx₀ : ∀ k, 0 ≤ x k) (hx₁ : ∑ k, x k = 1) : simplexRetraction x = x := by
  have hm : posMass x = 1 := (sum_congr rfl fun k _ => max_eq_left (hx₀ k)).trans hx₁
  funext k
  unfold simplexRetraction
  rw [hm, max_self, min_self, sub_self, zero_div, add_zero, div_one, max_eq_left (hx₀ k)]

/-- **Brouwer's fixed-point theorem** for a finite product of standard simplices: a continuous map
of the set of families `p i`, each with nonnegative entries summing to `1`, into itself has a
fixed point. -/
theorem exists_isFixedPt_pi_simplex {ι : Type*} [Finite ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)] {f : (∀ i, S i → ℝ) → ∀ i, S i → ℝ}
    (hf : MapsTo f {p | ∀ i, (∀ a, 0 ≤ p i a) ∧ ∑ a, p i a = 1}
      {p | ∀ i, (∀ a, 0 ≤ p i a) ∧ ∑ a, p i a = 1})
    (hc : ContinuousOn f {p | ∀ i, (∀ a, 0 ≤ p i a) ∧ ∑ a, p i a = 1}) :
    ∃ p : ∀ i, S i → ℝ, (∀ i, (∀ a, 0 ≤ p i a) ∧ ∑ a, p i a = 1) ∧ IsFixedPt f p := by
  have := Fintype.ofFinite ι
  refine exists_isFixedPt_of_leftInvOn (A := Icc (0 : (Σ i, S i) → ℝ) 1)
    (fun _ hg hgc => exists_isFixedPt_cube_of_finite hg hgc)
    (φ := fun z i => simplexRetraction fun a => z ⟨i, a⟩) (ψ := fun p z => p z.1 z.2)
    ?_ ?_ ?_
    (continuous_pi fun z => (continuous_apply z.2).comp (continuous_apply z.1)).continuousOn
    (fun p hp => funext fun i => simplexRetraction_eq (hp i).1 (hp i).2) hf hc
  · exact fun _ _ _ => ⟨simplexRetraction_nonneg _, sum_simplexRetraction _⟩
  · exact fun p hp => ⟨fun z => (hp z.1).1 z.2, fun z =>
      (single_le_sum (f := p z.1) (fun a _ => (hp z.1).1 a) (mem_univ z.2)).trans_eq (hp z.1).2⟩
  · exact (continuous_pi fun i => continuous_pi fun a => (continuous_simplexRetraction a).comp
      (f := fun z : (Σ i, S i) → ℝ => fun b => z ⟨i, b⟩)
      (continuous_pi fun _ => continuous_apply _)).continuousOn

end Cslib.Brouwer
