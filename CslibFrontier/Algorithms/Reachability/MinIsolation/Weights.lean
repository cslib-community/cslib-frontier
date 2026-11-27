/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Nat.TwoAdicInterval
public import Mathlib.Logic.Function.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Seed derivatives of Hoza's weights

A column has a binary codeword. The seed masks its bits. A base-six place value gives
priority to earlier bits, and a power of six determined by the layer's 2-adic
multiplicity gives priority to the unique maximal internal layer
[Hoza2026NLUL, §2.1, Eq. (1)].

For a nonempty family of paths passing through the same column at the maximal layer,
the minimum path weight has the derivative bounds of [Hoza2026NLUL, Lemma 2.3].
The family is supplied here by its finite set and its column at each internal layer.

## Main definitions

* `Cslib.Reachability.Hoza.vertexWeight`: seeded weight of a layer and column.
* `Cslib.Reachability.Hoza.intervalWeight`: sum of weights over the internal layers.
* `Cslib.Reachability.Hoza.minIntervalWeight`: minimum over a nonempty finite path family.

## Main results

* `Cslib.Reachability.Hoza.minIntervalWeight_update_bounds`: the two-sided
  derivative bound, expressed without subtraction.
-/

public section

namespace Cslib.Reachability.Hoza

open Finset Function

variable {V P : Type*} {ℓ : ℕ}

/-- Apply Hoza's layer-dependent factor to an already accumulated base-six weight. The
vertex weight and streaming scan handle the layer-zero case separately. -/
@[expose] def scaleAccumulatedWeight (layer accumulator : ℕ) : ℕ :=
  6 ^ padicValNat 2 layer * accumulator

/-- The coefficient of one codeword bit in a positive layer. -/
@[expose] def coefficient (i : ℕ) (j : Fin ℓ) : ℕ :=
  scaleAccumulatedWeight i (6 ^ (ℓ - (j.val + 1)))

/-- The vertex weight in [Hoza2026NLUL, Eq. (1)]. Layer zero has weight zero. -/
@[expose] def vertexWeight (code : V → Fin ℓ → Bool) (seed : Fin ℓ → Bool)
    (i : ℕ) (v : V) : ℕ :=
  if i = 0 then 0 else ∑ j, coefficient i j * (code v j).toNat * (seed j).toNat

/-- Sum the weights of the columns visited at the specified layers. -/
@[expose] def intervalWeight (code : V → Fin ℓ → Bool) (seed : Fin ℓ → Bool)
    (layers : Finset ℕ) (column : ℕ → V) : ℕ :=
  ∑ i ∈ layers, vertexWeight code seed i (column i)

private theorem vertexWeight_update (code : V → Fin ℓ → Bool) (seed : Fin ℓ → Bool)
    (i : ℕ) (v : V) (hi : i ≠ 0) (j : Fin ℓ) :
    vertexWeight code (update seed j true) i v =
      vertexWeight code (update seed j false) i v + coefficient i j * (code v j).toNat := by
  let delta := coefficient i j * (code v j).toNat
  have hdelta : (∑ k : Fin ℓ, if k = j then delta else 0) = delta := by simp
  simp only [vertexWeight, hi, ↓reduceIte]
  change _ = _ + delta
  rw [← hdelta, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  by_cases h : k = j
  · subst k
    simp [delta]
  · simp [h]

private theorem intervalWeight_update (code : V → Fin ℓ → Bool) (seed : Fin ℓ → Bool)
    (layers : Finset ℕ) (hpos : ∀ i ∈ layers, i ≠ 0) (column : ℕ → V) (j : Fin ℓ) :
    intervalWeight code (update seed j true) layers column =
      intervalWeight code (update seed j false) layers column +
        ∑ i ∈ layers, coefficient i j * (code (column i) j).toNat := by
  rw [intervalWeight, intervalWeight, ← sum_add_distrib]
  exact sum_congr rfl fun i hi => vertexWeight_update code seed i (column i) (hpos i hi) j

private theorem intervalWeight_update_bounds (code : V → Fin ℓ → Bool) (seed : Fin ℓ → Bool)
    {a b mid : ℕ} (ha : 0 < a) (hm : mid ∈ Icc a b)
    (hmax : ∀ i ∈ Icc a b, multiplicity 2 i ≤ multiplicity 2 mid)
    (column : ℕ → V) (j : Fin ℓ) :
    intervalWeight code (update seed j false) (Icc a b) column +
        coefficient mid j * (code (column mid) j).toNat ≤
      intervalWeight code (update seed j true) (Icc a b) column ∧
    intervalWeight code (update seed j true) (Icc a b) column ≤
      intervalWeight code (update seed j false) (Icc a b) column +
        coefficient mid j * (code (column mid) j).toNat + coefficient mid j / 2 := by
  rw [intervalWeight_update code seed _ (fun i hi => (ha.trans_le (mem_Icc.mp hi).1).ne') column j,
    ← sum_erase_add _ _ hm]
  have hsum : (∑ i ∈ (Icc a b).erase mid, coefficient i j * (code (column i) j).toNat) ≤
      (∑ i ∈ (Icc a b).erase mid, (6 : ℕ) ^ multiplicity 2 i) * 6 ^ (ℓ - (j.val + 1)) := by
    rw [sum_mul]
    refine sum_le_sum fun i _ => ?_
    cases code (column i) j <;> simp [coefficient, scaleAccumulatedWeight, Nat.padicValNat_def]
  have htail := Nat.two_mul_sum_six_pow_multiplicity_erase_le ha hm hmax
  have hscaled := Nat.mul_le_mul_right (6 ^ (ℓ - (j.val + 1))) htail
  rw [Nat.mul_assoc] at hscaled
  have hdouble := (Nat.mul_le_mul_left 2 hsum).trans hscaled
  simp only [coefficient, scaleAccumulatedWeight, Nat.padicValNat_def] at *
  omega

/-- The minimum weight of a member of a nonempty finite path family. -/
noncomputable def minIntervalWeight (code : V → Fin ℓ → Bool) (seed : Fin ℓ → Bool)
    (layers : Finset ℕ) (column : P → ℕ → V) (paths : Finset P) (hne : paths.Nonempty) : ℕ :=
  (paths.image fun p => intervalWeight code seed layers (column p)).min' (hne.image _)

/-- The minimum interval weight is no larger than the weight of any member. -/
theorem minIntervalWeight_le (code : V → Fin ℓ → Bool) (seed : Fin ℓ → Bool)
    (layers : Finset ℕ) (column : P → ℕ → V) {paths : Finset P} (hne : paths.Nonempty)
    {p : P} (hp : p ∈ paths) :
    minIntervalWeight code seed layers column paths hne ≤
      intervalWeight code seed layers (column p) :=
  min'_le _ _ (mem_image_of_mem _ hp)

/-- Some member of a nonempty path family attains its minimum interval weight. -/
theorem exists_minIntervalWeight (code : V → Fin ℓ → Bool) (seed : Fin ℓ → Bool)
    (layers : Finset ℕ) (column : P → ℕ → V) {paths : Finset P} (hne : paths.Nonempty) :
    ∃ p ∈ paths, intervalWeight code seed layers (column p) =
      minIntervalWeight code seed layers column paths hne :=
  mem_image.mp (min'_mem _ _)

/-- If all paths visit column `v` at the dominant layer, the change in their minimum
on switching bit `j` from zero to one lies between the contribution of that vertex
and that contribution plus half the dominant coefficient. -/
theorem minIntervalWeight_update_bounds (code : V → Fin ℓ → Bool) (seed : Fin ℓ → Bool)
    {a b mid : ℕ} (ha : 0 < a) (hm : mid ∈ Icc a b)
    (hmax : ∀ i ∈ Icc a b, multiplicity 2 i ≤ multiplicity 2 mid)
    (column : P → ℕ → V) {paths : Finset P} (hne : paths.Nonempty)
    (v : V) (hcolumn : ∀ p ∈ paths, column p mid = v) (j : Fin ℓ) :
    let d₀ := minIntervalWeight code (update seed j false) (Icc a b) column paths hne
    let d₁ := minIntervalWeight code (update seed j true) (Icc a b) column paths hne
    d₀ + coefficient mid j * (code v j).toNat ≤ d₁ ∧
      d₁ ≤ d₀ + coefficient mid j * (code v j).toNat + coefficient mid j / 2 := by
  obtain ⟨p₀, hp₀, h₀⟩ := exists_minIntervalWeight code (update seed j false) (Icc a b) column hne
  obtain ⟨p₁, hp₁, h₁⟩ := exists_minIntervalWeight code (update seed j true) (Icc a b) column hne
  have hb₀ := (intervalWeight_update_bounds code seed ha hm hmax (column p₀) j).2
  have hb₁ := (intervalWeight_update_bounds code seed ha hm hmax (column p₁) j).1
  rw [h₀, hcolumn p₀ hp₀] at hb₀
  rw [h₁, hcolumn p₁ hp₁] at hb₁
  exact ⟨(Nat.add_le_add_right (minIntervalWeight_le code _ _ column hne hp₁) _).trans hb₁,
    (minIntervalWeight_le code _ _ column hne hp₀).trans hb₀⟩

end Cslib.Reachability.Hoza
