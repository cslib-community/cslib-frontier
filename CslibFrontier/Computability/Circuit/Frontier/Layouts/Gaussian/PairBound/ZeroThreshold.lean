/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Matching
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Switched.Disintegration
import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Zero-threshold maximality of the Gaussian matched-pair cost

For any four unit vectors `u : Fin 4 → E` in a finite-dimensional real inner product space `E`,
the expected two-vertex threshold cost of `(⟪u 0, x⟫, ⟪u 1, x⟫, ⟪u 2, x⟫, ⟪u 3, x⟫)` under
`x ~ stdGaussian E` is maximized at threshold `t = 0` (`pairCost_le_zero`).

The proof avoids derivatives and singular covariance limits:

1. **Submodularity and complement symmetry (`maskCost_submodular`, `maskCost_compl`).** Viewing
   `twoVertexCost` as a function `maskCost : Finset (Fin 4) → ℕ` of the below-threshold coordinate
   set `{k | ⟪u k, x⟫ < t}`, complementation preserves `maskCost` and enlarging the background set
   `T ⊆ Fin 4 \ B` can only decrease every block jump `maskCost (T ∪ B) - maskCost T`.
2. **Reflection `t ↦ -t`.** Negating `x ↦ -x` sends `{k | ⟪u k, -x⟫ < -t}` to
   `Finset.univ \ {k | ⟪u k, x⟫ < t}` outside the null hyperplane union `⋃ k, {x | ⟪u k, x⟫ = t}`,
   so `pairCost u (-t) = pairCost u t`.
3. **Finite step-jump telescoping and Gaussian disintegration (`pairCost_le_zero_of_nonneg`).** For
   `t ≥ 0`, grouping equal vectors into equivalence blocks `B i = {k | u k = u i}` telescopes
   `maskCost {k | ⟪u k, x⟫ < t} - maskCost {k | ⟪u k, x⟫ < 0}` almost surely over block
   representatives `i` with `0 < ⟪u i, x⟫ < t`. Disintegrating along `u i`
   (`Switched.real_disintegrate`), for each `z > 0` and `j ∉ B i` Cauchy–Schwarz gives
   `⟪u i, u j⟫ < 1`, hence `-(1 - ⟪u i, u j⟫) z < (1 - ⟪u i, u j⟫) z`. Submodularity and
   reflection `x ↦ -x` on the orthogonal remainder force each conditional jump expectation to be
   nonpositive.

## Main definitions

* `Cslib.Circuits.Frontier.Gaussian.PairBound.anyStradSet`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.bothStradSet`: threshold straddling events in `E`
  for a `4`-tuple of vectors `u : Fin 4 → E`.
* `Cslib.Circuits.Frontier.Gaussian.PairBound.pairCost`: expected two-vertex matched-pair cost at
  threshold `t` under `stdGaussian E`.

## Main results

* `Cslib.Circuits.Frontier.Gaussian.PairBound.pairCost_le_zero`: `pairCost u t ≤ pairCost u 0`
  whenever `∀ i, ‖u i‖ = 1`.
-/

public section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

namespace Cslib.Circuits.Frontier.Gaussian.PairBound

open Cslib.Circuits.Frontier.Switched

/-! ### Boolean submodularity and complement symmetry on `Finset (Fin 4)` -/

/-- Set-indexed two-vertex cut cost on subsets of `Fin 4`, pairing `{0, 1}` and `{2, 3}`. -/
private def maskCost (S : Finset (Fin 4)) : ℕ :=
  twoVertexCost (decide (0 ∈ S)) (decide (1 ∈ S)) (decide (2 ∈ S)) (decide (3 ∈ S))

private theorem maskCost_compl (S : Finset (Fin 4)) :
    maskCost (Finset.univ \ S) = maskCost S := by
  have h : ∀ b0 b1 b2 b3 : Bool,
      twoVertexCost (!b0) (!b1) (!b2) (!b3) = twoVertexCost b0 b1 b2 b3 := by decide
  simpa [maskCost, Finset.mem_sdiff, Finset.mem_univ, true_and] using
    h (decide (0 ∈ S)) (decide (1 ∈ S)) (decide (2 ∈ S)) (decide (3 ∈ S))

private def codeAt (c0 c1 c2 c3 : Fin 4) : Fin 4 → Fin 4
  | 0 => c0
  | 1 => c1
  | 2 => c2
  | 3 => c3

/-- Encoding of `(B, T₁, T₂)` with `T₁ ⊆ T₂` and `Disjoint T₂ B` as `Fin 4 → Fin 4` (`0`: in `B`,
`1`: in `T₁`, `2`: in `T₂ \ T₁`, `3`: outside) for fast kernel `decide`. -/
private def codeCheck (c0 c1 c2 c3 : Fin 4) : Bool :=
  let c := codeAt c0 c1 c2 c3
  let t1 (k : Fin 4) : Bool := c k == 1
  let t2 (k : Fin 4) : Bool := (c k == 1) || (c k == 2)
  let t1B (k : Fin 4) : Bool := (c k == 1) || (c k == 0)
  let t2B (k : Fin 4) : Bool := (c k == 1) || (c k == 2) || (c k == 0)
  decide ((twoVertexCost (t2B 0) (t2B 1) (t2B 2) (t2B 3) : ℤ) -
      twoVertexCost (t2 0) (t2 1) (t2 2) (t2 3) ≤
    (twoVertexCost (t1B 0) (t1B 1) (t1B 2) (t1B 3) : ℤ) -
      twoVertexCost (t1 0) (t1 1) (t1 2) (t1 3))

private theorem codeCheck_all : ∀ c0 c1 c2 c3 : Fin 4, codeCheck c0 c1 c2 c3 = true := by
  decide

private theorem maskCost_submodular {B T₁ T₂ : Finset (Fin 4)} (hsub : T₁ ⊆ T₂)
    (hdisj : Disjoint T₂ B) :
    (maskCost (T₂ ∪ B) : ℝ) - maskCost T₂ ≤ (maskCost (T₁ ∪ B) : ℝ) - maskCost T₁ := by
  let c (k : Fin 4) : Fin 4 :=
    if k ∈ B then 0 else if k ∈ T₁ then 1 else if k ∈ T₂ then 2 else 3
  have hc := of_decide_eq_true (codeCheck_all (c 0) (c 1) (c 2) (c 3))
  have hc_eq (k : Fin 4) : codeAt (c 0) (c 1) (c 2) (c 3) k = c k := by
    fin_cases k <;> rfl
  have ht1 (k : Fin 4) : (codeAt (c 0) (c 1) (c 2) (c 3) k == 1) = decide (k ∈ T₁) := by
    rw [hc_eq]
    have hkB : k ∈ T₁ → k ∉ B := fun hk => Finset.disjoint_left.mp hdisj (hsub hk)
    dsimp [c]
    by_cases hB : k ∈ B <;> by_cases h1 : k ∈ T₁ <;> by_cases h2 : k ∈ T₂
    · exact (hkB h1 hB).elim
    · exact (hkB h1 hB).elim
    · simp [hB, h1]
    · simp [hB, h1]
    · simp [hB, h1]
    · simp [hB, h1]
    · simp [hB, h1, h2]
    · simp [hB, h1, h2]
  have ht2 (k : Fin 4) :
      ((codeAt (c 0) (c 1) (c 2) (c 3) k == 1) || (codeAt (c 0) (c 1) (c 2) (c 3) k == 2)) =
        decide (k ∈ T₂) := by
    rw [hc_eq]
    have hkB : k ∈ T₂ → k ∉ B := fun hk => Finset.disjoint_left.mp hdisj hk
    have hk12 : k ∈ T₁ → k ∈ T₂ := fun hk => hsub hk
    dsimp [c]
    by_cases hB : k ∈ B <;> by_cases h1 : k ∈ T₁ <;> by_cases h2 : k ∈ T₂
    · exact (hkB h2 hB).elim
    · exact (h2 (hk12 h1)).elim
    · exact (hkB h2 hB).elim
    · simp [hB, h2]
    · simp [hB, h1, h2]
    · exact (h2 (hk12 h1)).elim
    · simp [hB, h1, h2]
    · simp [hB, h1, h2]
  have ht1B (k : Fin 4) :
      ((codeAt (c 0) (c 1) (c 2) (c 3) k == 1) || (codeAt (c 0) (c 1) (c 2) (c 3) k == 0)) =
        decide (k ∈ T₁ ∪ B) := by
    rw [hc_eq]
    dsimp [c]
    by_cases hB : k ∈ B <;> by_cases h1 : k ∈ T₁ <;> by_cases h2 : k ∈ T₂ <;>
      simp [Finset.mem_union, hB, h1, h2]
  have ht2B (k : Fin 4) :
      ((codeAt (c 0) (c 1) (c 2) (c 3) k == 1) || (codeAt (c 0) (c 1) (c 2) (c 3) k == 2) ||
        (codeAt (c 0) (c 1) (c 2) (c 3) k == 0)) = decide (k ∈ T₂ ∪ B) := by
    rw [hc_eq]
    have hk12 : k ∈ T₁ → k ∈ T₂ := fun hk => hsub hk
    dsimp [c]
    by_cases hB : k ∈ B <;> by_cases h1 : k ∈ T₁ <;> by_cases h2 : k ∈ T₂
    · simp [Finset.mem_union, hB]
    · simp [Finset.mem_union, hB]
    · simp [Finset.mem_union, hB]
    · simp [Finset.mem_union, hB]
    · simp [Finset.mem_union, hB, h1, h2]
    · exact (h2 (hk12 h1)).elim
    · simp [Finset.mem_union, hB, h1, h2]
    · simp [Finset.mem_union, hB, h1, h2]
  dsimp [codeCheck] at hc
  rw [ht2B 0, ht2B 1, ht2B 2, ht2B 3, ht2 0, ht2 1, ht2 2, ht2 3,
    ht1B 0, ht1B 1, ht1B 2, ht1B 3, ht1 0, ht1 1, ht1 2, ht1 3] at hc
  have hcast : ((maskCost (T₂ ∪ B) : ℤ) - maskCost T₂ : ℝ) ≤
      ((maskCost (T₁ ∪ B) : ℤ) - maskCost T₁ : ℝ) := by exact_mod_cast hc
  simpa using hcast

/-! ### Equivalence blocks of `u : Fin 4 → α` -/

private noncomputable def eqBlock {α : Type*} (u : Fin 4 → α) (i : Fin 4) : Finset (Fin 4) :=
  letI := Classical.propDecidable
  Finset.univ.filter fun k => u k = u i

private noncomputable def eqReps {α : Type*} (u : Fin 4 → α) : Finset (Fin 4) :=
  letI := Classical.propDecidable
  Finset.univ.filter fun i => ∀ k : Fin 4, u k = u i → i ≤ k

private theorem mem_eqReps_min {α : Type*} (u : Fin 4 → α) (k : Fin 4) :
    ∃ i ∈ eqReps u, u k = u i := by
  classical
  have hne : (eqBlock u k).Nonempty := ⟨k, by simp [eqBlock]⟩
  have hmin : u ((eqBlock u k).min' hne) = u k := by
    simpa [eqBlock] using (eqBlock u k).min'_mem hne
  refine ⟨(eqBlock u k).min' hne, ?_, hmin.symm⟩
  simp only [eqReps, Finset.mem_filter, Finset.mem_univ, true_and]
  intro j hj
  exact (eqBlock u k).min'_le j (by simp [eqBlock, hj.trans hmin])

private theorem eq_of_mem_eqReps {α : Type*} {u : Fin 4 → α} {i j : Fin 4}
    (hi : i ∈ eqReps u) (hj : j ∈ eqReps u) (h : u i = u j) : i = j := by
  simp only [eqReps, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  exact le_antisymm (hi j h.symm) (hj i h)

/-! ### Connection between `maskCost` and straddling indicators -/

section Space

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Event in `E` that `(⟪u 0, x⟫, ..., ⟪u 3, x⟫)` straddles threshold `t`. -/
@[expose] def anyStradSet (u : Fin 4 → E) (t : ℝ) : Set E :=
  {x | StraddlesOn (fun i : Fin 4 => ⟪u i, x⟫) t univ}

/-- Event in `E` that both `{0, 1}` and `{2, 3}` straddle threshold `t`. -/
@[expose] def bothStradSet (u : Fin 4 → E) (t : ℝ) : Set E :=
  {x | StraddlesOn (fun i : Fin 4 => ⟪u i, x⟫) t {0, 1} ∧
       StraddlesOn (fun i : Fin 4 => ⟪u i, x⟫) t {2, 3}}

/-- Expected matched-pair two-vertex cost of `u : Fin 4 → E` at threshold `t` under
`stdGaussian E`. -/
@[expose] noncomputable def pairCost (u : Fin 4 → E) (t : ℝ) : ℝ :=
  (stdGaussian E).real (anyStradSet u t) + (stdGaussian E).real (bothStradSet u t)

omit [FiniteDimensional ℝ E] in
private theorem measurableSet_straddlesOn_inner (u : Fin 4 → E) (t : ℝ) (S : Set (Fin 4)) :
    MeasurableSet {x : E | StraddlesOn (fun i => ⟪u i, x⟫) t S} := by
  have heq : {x : E | StraddlesOn (fun i => ⟪u i, x⟫) t S} =
      (⋃ i ∈ S, {x | ⟪u i, x⟫ < t}) ∩ (⋃ i ∈ S, {x | t ≤ ⟪u i, x⟫}) := by
    ext x; simp [StraddlesOn]
  rw [heq]
  exact ((toFinite S).measurableSet_biUnion fun i _ =>
      measurableSet_lt (by fun_prop) measurable_const).inter
    ((toFinite S).measurableSet_biUnion fun i _ =>
      measurableSet_le measurable_const (by fun_prop))

omit [FiniteDimensional ℝ E] in
theorem measurableSet_anyStradSet (u : Fin 4 → E) (t : ℝ) : MeasurableSet (anyStradSet u t) :=
  measurableSet_straddlesOn_inner u t univ

omit [FiniteDimensional ℝ E] in
theorem measurableSet_bothStradSet (u : Fin 4 → E) (t : ℝ) : MeasurableSet (bothStradSet u t) :=
  (measurableSet_straddlesOn_inner u t {0, 1}).inter (measurableSet_straddlesOn_inner u t {2, 3})

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem indicator_sum_eq_maskCost (u : Fin 4 → E) (t : ℝ) (x : E) :
    (anyStradSet u t).indicator (1 : E → ℝ) x + (bothStradSet u t).indicator (1 : E → ℝ) x =
      (maskCost (Finset.univ.filter fun k : Fin 4 => ⟪u k, x⟫ < t) : ℝ) := by
  classical
  let S := Finset.univ.filter fun k : Fin 4 => ⟪u k, x⟫ < t
  have hmem (k : Fin 4) : (k ∈ S) ↔ ⟪u k, x⟫ < t := by simp [S]
  have hany : (x ∈ anyStradSet u t) ↔
      ((decide (0 ∈ S) && decide (1 ∈ S) && decide (2 ∈ S) && decide (3 ∈ S)) = false ∧
       (decide (0 ∈ S) || decide (1 ∈ S) || decide (2 ∈ S) || decide (3 ∈ S)) = true) := by
    simp only [anyStradSet, mem_ofPred_eq, StraddlesOn, mem_univ, true_and, not_lt.symm, ← hmem]
    constructor
    · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
      fin_cases i <;> fin_cases j <;> simp_all
    · rintro ⟨h1, h2⟩
      by_cases b0 : 0 ∈ S <;> by_cases b1 : 1 ∈ S <;> by_cases b2 : 2 ∈ S <;> by_cases b3 : 3 ∈ S
      · simp [b0, b1, b2, b3] at h1
      · exact ⟨⟨0, b0⟩, ⟨3, b3⟩⟩
      · exact ⟨⟨0, b0⟩, ⟨2, b2⟩⟩
      · exact ⟨⟨0, b0⟩, ⟨2, b2⟩⟩
      · exact ⟨⟨0, b0⟩, ⟨1, b1⟩⟩
      · exact ⟨⟨0, b0⟩, ⟨1, b1⟩⟩
      · exact ⟨⟨0, b0⟩, ⟨1, b1⟩⟩
      · exact ⟨⟨0, b0⟩, ⟨1, b1⟩⟩
      · exact ⟨⟨1, b1⟩, ⟨0, b0⟩⟩
      · exact ⟨⟨1, b1⟩, ⟨0, b0⟩⟩
      · exact ⟨⟨1, b1⟩, ⟨0, b0⟩⟩
      · exact ⟨⟨1, b1⟩, ⟨0, b0⟩⟩
      · exact ⟨⟨2, b2⟩, ⟨0, b0⟩⟩
      · exact ⟨⟨2, b2⟩, ⟨0, b0⟩⟩
      · exact ⟨⟨3, b3⟩, ⟨0, b0⟩⟩
      · simp [b0, b1, b2, b3] at h2
  have hboth : (x ∈ bothStradSet u t) ↔
      (decide (0 ∈ S) != decide (1 ∈ S)) = true ∧ (decide (2 ∈ S) != decide (3 ∈ S)) = true := by
    simp only [bothStradSet, mem_ofPred_eq, StraddlesOn, mem_insert_iff, mem_singleton_iff,
      not_lt.symm, ← hmem]
    constructor
    · rintro ⟨⟨⟨i, hi1, hi2⟩, ⟨j, hj1, hj2⟩⟩, ⟨⟨k, hk1, hk2⟩, ⟨l, hl1, hl2⟩⟩⟩
      rcases hi1 with rfl | rfl <;> rcases hj1 with rfl | rfl <;>
        rcases hk1 with rfl | rfl <;> rcases hl1 with rfl | rfl <;> simp_all
    · rintro ⟨h01, h23⟩
      refine ⟨?_, ?_⟩
      · by_cases b0 : 0 ∈ S <;> by_cases b1 : 1 ∈ S <;> simp [b0, b1] at h01
        · exact ⟨⟨0, Or.inl rfl, b0⟩, ⟨1, Or.inr rfl, b1⟩⟩
        · exact ⟨⟨1, Or.inr rfl, b1⟩, ⟨0, Or.inl rfl, b0⟩⟩
      · by_cases b2 : 2 ∈ S <;> by_cases b3 : 3 ∈ S <;> simp [b2, b3] at h23
        · exact ⟨⟨2, Or.inl rfl, b2⟩, ⟨3, Or.inr rfl, b3⟩⟩
        · exact ⟨⟨3, Or.inr rfl, b3⟩, ⟨2, Or.inl rfl, b2⟩⟩
  have hbool : ∀ b0 b1 b2 b3 : Bool,
      (if (b0 && b1 && b2 && b3) = false ∧ (b0 || b1 || b2 || b3) = true then (1 : ℕ) else 0) +
      (if (b0 != b1) = true ∧ (b2 != b3) = true then 1 else 0) =
      twoVertexCost b0 b1 b2 b3 := by decide
  have hinst :
      ((if x ∈ anyStradSet u t then (1 : ℕ) else 0) +
        if x ∈ bothStradSet u t then 1 else 0) = maskCost S := by
    simpa only [hany, hboth, maskCost] using
      hbool (decide (0 ∈ S)) (decide (1 ∈ S)) (decide (2 ∈ S)) (decide (3 ∈ S))
  have hcast : ((if x ∈ anyStradSet u t then (1 : ℝ) else 0) +
      if x ∈ bothStradSet u t then (1 : ℝ) else 0) = (maskCost S : ℝ) := by
    exact_mod_cast hinst
  simpa only [indicator_apply, Pi.one_apply, S] using hcast

private theorem pairCost_eq_integral_maskCost (u : Fin 4 → E) (t : ℝ) :
    pairCost u t = ∫ x, (maskCost (Finset.univ.filter fun k => ⟪u k, x⟫ < t) : ℝ)
      ∂stdGaussian E := by
  have hA := measurableSet_anyStradSet u t
  have hB := measurableSet_bothStradSet u t
  have hintA : Integrable ((anyStradSet u t).indicator (1 : E → ℝ)) (stdGaussian E) :=
    (integrable_const (1 : ℝ)).indicator hA
  have hintB : Integrable ((bothStradSet u t).indicator (1 : E → ℝ)) (stdGaussian E) :=
    (integrable_const (1 : ℝ)).indicator hB
  rw [pairCost, ← integral_indicator_one hA, ← integral_indicator_one hB,
    ← integral_add hintA hintB]
  exact integral_congr_ae (ae_of_all _ (indicator_sum_eq_maskCost u t))

private theorem integrable_maskCost (u : Fin 4 → E) (t : ℝ) :
    Integrable (fun x => (maskCost (Finset.univ.filter fun k => ⟪u k, x⟫ < t) : ℝ))
      (stdGaussian E) := by
  have hA := measurableSet_anyStradSet u t
  have hB := measurableSet_bothStradSet u t
  exact (((integrable_const (1 : ℝ)).indicator hA).add
    ((integrable_const (1 : ℝ)).indicator hB)).congr
    (ae_of_all _ (indicator_sum_eq_maskCost u t))

/-- Integral representation of `pairCost` via `twoVertexCost`. -/
theorem pairCost_eq_integral_twoVertexCost (u : Fin 4 → E) (t : ℝ) :
    pairCost u t = ∫ x, (twoVertexCost (decide (⟪u 0, x⟫ < t)) (decide (⟪u 1, x⟫ < t))
      (decide (⟪u 2, x⟫ < t)) (decide (⟪u 3, x⟫ < t)) : ℝ) ∂stdGaussian E := by
  rw [pairCost_eq_integral_maskCost]
  congr with x
  simp [maskCost]

/-- Integrability of the pointwise `twoVertexCost` threshold indicator under `stdGaussian E`. -/
theorem integrable_twoVertexCost (u : Fin 4 → E) (t : ℝ) :
    Integrable (fun x => (twoVertexCost (decide (⟪u 0, x⟫ < t)) (decide (⟪u 1, x⟫ < t))
      (decide (⟪u 2, x⟫ < t)) (decide (⟪u 3, x⟫ < t)) : ℝ)) (stdGaussian E) := by
  simpa [maskCost] using integrable_maskCost u t

private theorem stdGaussian_inner_ne_const_ae {v : E} (hv : v ≠ 0) (c : ℝ) :
    ∀ᵐ x ∂stdGaussian E, ⟪v, x⟫ ≠ c := by
  rw [ae_iff]
  have hset : {x : E | ¬⟪v, x⟫ ≠ c} = {x : E | ⟪v, x⟫ ∈ ({c} : Set ℝ)} := by ext x; simp
  rw [hset]
  have hle := stdGaussian_inner_mem_le hv (measurableSet_singleton c)
  simpa only [Real.volume_singleton, mul_zero, nonpos_iff_eq_zero] using hle

/-- **Reflection symmetry `t ↦ -t`.** For nonzero vectors `u`, `pairCost u (-t) = pairCost u t`. -/
private theorem pairCost_neg {u : Fin 4 → E} (hu : ∀ i, u i ≠ 0) (t : ℝ) :
    pairCost u (-t) = pairCost u t := by
  rw [pairCost_eq_integral_maskCost, pairCost_eq_integral_maskCost]
  let f : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.neg ℝ
  have hmp : MeasurePreserving f (stdGaussian E) (stdGaussian E) :=
    ⟨f.continuous.measurable, stdGaussian_map f⟩
  have hemb : MeasurableEmbedding f := f.toHomeomorph.measurableEmbedding
  rw [← hmp.integral_comp hemb]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ x ∂stdGaussian E, ∀ k : Fin 4, ⟪u k, x⟫ ≠ t :=
    eventually_all.mpr fun k => stdGaussian_inner_ne_const_ae (hu k) t
  filter_upwards [hae] with x hx
  have hset : (Finset.univ.filter fun k : Fin 4 => ⟪u k, f x⟫ < -t) =
      Finset.univ \ (Finset.univ.filter fun k : Fin 4 => ⟪u k, x⟫ < t) := by
    ext k
    have hfx : f x = -x := rfl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, hfx,
      inner_neg_right, neg_lt_neg_iff, not_lt]
    exact ⟨fun h => h.le, fun h => lt_of_le_of_ne h (hx k).symm⟩
  rw [hset, maskCost_compl]

/-! ### Finite step-jump telescoping for `0 ≤ t` -/

open Classical in
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem maskCost_telescope {u : Fin 4 → E} {x : E} {t : ℝ} (ht : 0 ≤ t)
    (h0 : ∀ k, ⟪u k, x⟫ ≠ 0) (hne : ∀ i j, u i ≠ u j → ⟪u i, x⟫ ≠ ⟪u j, x⟫) :
    (maskCost (Finset.univ.filter fun k => ⟪u k, x⟫ < t) : ℝ) -
        maskCost (Finset.univ.filter fun k => ⟪u k, x⟫ < 0) =
      ∑ i ∈ eqReps u,
        if 0 < ⟪u i, x⟫ ∧ ⟪u i, x⟫ < t then
          (maskCost ((Finset.univ.filter fun j => u j ≠ u i ∧ ⟪u j, x⟫ < ⟪u i, x⟫) ∪
              eqBlock u i) : ℝ) -
            maskCost (Finset.univ.filter fun j => u j ≠ u i ∧ ⟪u j, x⟫ < ⟪u i, x⟫)
        else 0 := by
  let S₀ : Finset (Fin 4) := Finset.univ.filter fun k => ⟪u k, x⟫ < 0
  let A : Finset (Fin 4) := (eqReps u).filter fun i => 0 < ⟪u i, x⟫ ∧ ⟪u i, x⟫ < t
  have hind : ∀ (n : ℕ) (R : Finset (Fin 4)), R.card = n → R ⊆ A →
      (∀ i ∈ R, ∀ j ∈ A, ⟪u j, x⟫ < ⟪u i, x⟫ → j ∈ R) →
      (maskCost (S₀ ∪ R.biUnion (eqBlock u)) : ℝ) - maskCost S₀ =
        ∑ i ∈ R, ((maskCost ((Finset.univ.filter fun j => u j ≠ u i ∧ ⟪u j, x⟫ < ⟪u i, x⟫) ∪
            eqBlock u i) : ℝ) -
          maskCost (Finset.univ.filter fun j => u j ≠ u i ∧ ⟪u j, x⟫ < ⟪u i, x⟫)) := by
    intro n
    induction n with
    | zero =>
      intro R hcard _ _
      rw [Finset.card_eq_zero.mp hcard]
      simp
    | succ n ih =>
      intro R hcard hRA hdown
      have hRne : R.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨im, himR, hmax⟩ := R.exists_max_image (fun i => ⟪u i, x⟫) hRne
      let R' := R.erase im
      have hcard' : R'.card = n := by rw [Finset.card_erase_of_mem himR, hcard]; omega
      have hR'A : R' ⊆ A := (Finset.erase_subset im R).trans hRA
      have himA : im ∈ A := hRA himR
      have him_rep : im ∈ eqReps u := (Finset.mem_filter.mp himA).1
      have him_pos : 0 < ⟪u im, x⟫ ∧ ⟪u im, x⟫ < t := (Finset.mem_filter.mp himA).2
      have hlt_im : ∀ j ∈ R', ⟪u j, x⟫ < ⟪u im, x⟫ := by
        intro j hj
        have hjR : j ∈ R := Finset.mem_of_mem_erase hj
        have hjne : j ≠ im := Finset.ne_of_mem_erase hj
        have hujeq : u j ≠ u im := fun heq =>
          hjne (eq_of_mem_eqReps (Finset.mem_filter.mp (hRA hjR)).1 him_rep heq)
        exact lt_of_le_of_ne (hmax j hjR) (hne j im hujeq)
      have hdown' : ∀ i ∈ R', ∀ j ∈ A, ⟪u j, x⟫ < ⟪u i, x⟫ → j ∈ R' := by
        intro i hi j hj hji
        have hjR : j ∈ R := hdown i (Finset.mem_of_mem_erase hi) j hj hji
        refine Finset.mem_erase.mpr ⟨?_, hjR⟩
        rintro rfl
        exact lt_asymm (hlt_im i hi) hji
      have hbase_eq : S₀ ∪ R'.biUnion (eqBlock u) =
          Finset.univ.filter fun j => u j ≠ u im ∧ ⟪u j, x⟫ < ⟪u im, x⟫ := by
        ext k
        simp only [S₀, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_biUnion, eqBlock]
        constructor
        · rintro (hk0 | ⟨j, hjR', hkj⟩)
          · refine ⟨fun heq => ?_, hk0.trans him_pos.1⟩
            rw [heq] at hk0
            exact lt_asymm hk0 him_pos.1
          · have hjne : j ≠ im := Finset.ne_of_mem_erase hjR'
            have hujeq : u j ≠ u im := fun heq =>
              hjne (eq_of_mem_eqReps (Finset.mem_filter.mp (hR'A hjR')).1 him_rep heq)
            rw [hkj]
            exact ⟨hujeq, hlt_im j hjR'⟩
        · rintro ⟨hk_ne, hk_lt⟩
          rcases lt_trichotomy ⟪u k, x⟫ 0 with hk0 | hk0 | hk0
          · exact Or.inl hk0
          · exact (h0 k hk0).elim
          · obtain ⟨j, hj_rep, hkj⟩ := mem_eqReps_min u k
            right
            refine ⟨j, ?_, hkj⟩
            have hjA : j ∈ A := Finset.mem_filter.mpr
              ⟨hj_rep, by rwa [← hkj], (by rwa [← hkj] : ⟪u j, x⟫ < ⟪u im, x⟫).trans him_pos.2⟩
            have hjR : j ∈ R := hdown im himR j hjA (by rwa [← hkj])
            refine Finset.mem_erase.mpr ⟨fun hjeq => hk_ne ?_, hjR⟩
            rw [hkj, hjeq]
      have hunion : S₀ ∪ R.biUnion (eqBlock u) =
          (S₀ ∪ R'.biUnion (eqBlock u)) ∪ eqBlock u im := by
        ext k
        simp only [Finset.mem_union, Finset.mem_biUnion, R', Finset.mem_erase]
        constructor
        · rintro (hk | ⟨j, hj, hkj⟩)
          · exact Or.inl (Or.inl hk)
          · by_cases hjeq : j = im
            · exact Or.inr (hjeq ▸ hkj)
            · exact Or.inl (Or.inr ⟨j, ⟨hjeq, hj⟩, hkj⟩)
        · rintro ((hk | ⟨j, ⟨_, hj⟩, hkj⟩) | hkim)
          · exact Or.inl hk
          · exact Or.inr ⟨j, hj, hkj⟩
          · exact Or.inr ⟨im, himR, hkim⟩
      have step := ih R' hcard' hR'A hdown'
      rw [← Finset.sum_erase_add _ _ himR, ← step, hunion, hbase_eq]
      ring
  have htot : S₀ ∪ A.biUnion (eqBlock u) = Finset.univ.filter fun k => ⟪u k, x⟫ < t := by
    ext k
    simp only [S₀, A, eqBlock, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion]
    constructor
    · rintro (hk0 | ⟨i, ⟨_, _, hit⟩, hki⟩)
      · exact hk0.trans_le ht
      · rwa [hki]
    · intro hkt
      rcases lt_trichotomy ⟪u k, x⟫ 0 with hk0 | hk0 | hk0
      · exact Or.inl hk0
      · exact (h0 k hk0).elim
      · obtain ⟨i, hi_rep, hki⟩ := mem_eqReps_min u k
        exact Or.inr ⟨i, ⟨hi_rep, by rwa [← hki], by rwa [← hki]⟩, hki⟩
  have hmain := hind A.card A rfl Finset.Subset.rfl (fun _ _ _ hj _ => hj)
  rw [htot] at hmain
  rw [hmain, ← Finset.sum_filter]

/-! ### Disintegration and nonpositivity of each block jump -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem inner_lt_one_of_ne {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hne : b ≠ a) :
    ⟪a, b⟫ < 1 := by
  have hpos : 0 < ‖a - b‖ ^ 2 := sq_pos_of_pos (norm_sub_pos_iff.mpr hne.symm)
  rw [norm_sub_sq_real, ha, hb] at hpos
  linarith

open Classical in
private theorem jump_integral_nonpos {u : Fin 4 → E} (hu : ∀ k, ‖u k‖ = 1) {t : ℝ} (i : Fin 4) :
    ∫ x, (if 0 < ⟪u i, x⟫ ∧ ⟪u i, x⟫ < t then
        (maskCost ((Finset.univ.filter fun j => u j ≠ u i ∧ ⟪u j, x⟫ < ⟪u i, x⟫) ∪
            eqBlock u i) : ℝ) -
          maskCost (Finset.univ.filter fun j => u j ≠ u i ∧ ⟪u j, x⟫ < ⟪u i, x⟫)
      else 0) ∂stdGaussian E ≤ 0 := by
  let B := eqBlock u i
  let U := Finset.univ \ B
  let Δ (T : Finset (Fin 4)) : ℝ := (maskCost (T ∪ B) : ℝ) - maskCost T
  let Tset (z : ℝ) (w : E) : Finset (Fin 4) :=
    U.filter fun j => ⟪u j, w⟫ < (1 - ⟪u i, u j⟫) * z
  have hrem_eq (x : E) :
      (Finset.univ.filter fun j => u j ≠ u i ∧ ⟪u j, x⟫ < ⟪u i, x⟫) =
        Tset ⟪u i, x⟫ (remainder (u i) x) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Tset, U, Finset.mem_sdiff, B,
      eqBlock, remainder, inner_sub_right, real_inner_smul_right, real_inner_comm (u i) (u j)]
    exact and_congr_right fun _ => ⟨fun h => by linarith, fun h => by linarith⟩
  let S (T : Finset (Fin 4)) : Set (ℝ × E) :=
    {p | (0 < p.1 ∧ p.1 < t) ∧ Tset p.1 p.2 = T}
  have hS_meas {T : Finset (Fin 4)} (hTU : T ⊆ U) : MeasurableSet (S T) := by
    have heq : S T = {p : ℝ × E | 0 < p.1 ∧ p.1 < t} ∩
        (⋂ j ∈ T, {p : ℝ × E | ⟪u j, p.2⟫ < (1 - ⟪u i, u j⟫) * p.1}) ∩
        (⋂ j ∈ U \ T, {p : ℝ × E | (1 - ⟪u i, u j⟫) * p.1 ≤ ⟪u j, p.2⟫}) := by
      ext p
      simp only [S, mem_inter_iff, mem_ofPred_eq, mem_iInter, Finset.mem_sdiff, ← not_lt]
      constructor
      · rintro ⟨hp, rfl⟩
        exact ⟨⟨hp, fun j hj => (Finset.mem_filter.mp hj).2⟩,
          fun j hj hlt => hj.2 (Finset.mem_filter.mpr ⟨hj.1, hlt⟩)⟩
      · rintro ⟨⟨hp, h1⟩, h2⟩
        refine ⟨hp, ?_⟩
        ext j
        exact ⟨fun hj => by
          by_contra hjT
          exact h2 j ⟨(Finset.mem_filter.mp hj).1, hjT⟩ (Finset.mem_filter.mp hj).2,
          fun hjT => Finset.mem_filter.mpr ⟨hTU hjT, h1 j hjT⟩⟩
    rw [heq]
    have hm0 : MeasurableSet {p : ℝ × E | 0 < p.1 ∧ p.1 < t} :=
      (measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_lt measurable_fst measurable_const)
    have hm1 : MeasurableSet (⋂ j ∈ T, {p : ℝ × E | ⟪u j, p.2⟫ < (1 - ⟪u i, u j⟫) * p.1}) :=
      T.measurableSet_biInter fun j _ =>
        measurableSet_lt (by fun_prop : Measurable fun p : ℝ × E => ⟪u j, p.2⟫)
          (by fun_prop : Measurable fun p : ℝ × E => (1 - ⟪u i, u j⟫) * p.1)
    have hm2 : MeasurableSet (⋂ j ∈ U \ T, {p : ℝ × E | (1 - ⟪u i, u j⟫) * p.1 ≤ ⟪u j, p.2⟫}) :=
      (U \ T).measurableSet_biInter fun j _ =>
        measurableSet_le (by fun_prop : Measurable fun p : ℝ × E => (1 - ⟪u i, u j⟫) * p.1)
          (by fun_prop : Measurable fun p : ℝ × E => ⟪u j, p.2⟫)
    exact (hm0.inter hm1).inter hm2
  let Ev (T : Finset (Fin 4)) : Set E := {x | (⟪u i, x⟫, remainder (u i) x) ∈ S T}
  have hEv_meas {T : Finset (Fin 4)} (hTU : T ⊆ U) : MeasurableSet (Ev T) := by
    have hm : Measurable fun x : E => (⟪u i, x⟫, remainder (u i) x) := by
      unfold remainder; fun_prop
    exact hm (hS_meas hTU)
  have hpt_decomp (x : E) :
      (if 0 < ⟪u i, x⟫ ∧ ⟪u i, x⟫ < t then
          (maskCost ((Finset.univ.filter fun j => u j ≠ u i ∧ ⟪u j, x⟫ < ⟪u i, x⟫) ∪ B) : ℝ) -
            maskCost (Finset.univ.filter fun j => u j ≠ u i ∧ ⟪u j, x⟫ < ⟪u i, x⟫)
        else 0) =
      ∑ T ∈ U.powerset, Δ T * (Ev T).indicator (1 : E → ℝ) x := by
    rw [hrem_eq x]
    have hmem : Tset ⟪u i, x⟫ (remainder (u i) x) ∈ U.powerset :=
      Finset.mem_powerset.mpr (Finset.filter_subset _ _)
    split_ifs with hx
    · rw [Finset.sum_eq_single (Tset ⟪u i, x⟫ (remainder (u i) x))]
      · have hmemEv : x ∈ Ev (Tset ⟪u i, x⟫ (remainder (u i) x)) := ⟨hx, rfl⟩
        simp [Δ, indicator_of_mem hmemEv]
      · intro T _ hne
        have hnmem : x ∉ Ev T := fun h => hne h.2.symm
        simp [indicator_of_notMem hnmem]
      · intro h; exact (h hmem).elim
    · symm
      refine Finset.sum_eq_zero fun T _ => ?_
      have hnmem : x ∉ Ev T := fun h => hx h.1
      simp [indicator_of_notMem hnmem]
  have hint_Ev {T : Finset (Fin 4)} (hT : T ∈ U.powerset) :
      Integrable (fun x => Δ T * (Ev T).indicator (1 : E → ℝ) x) (stdGaussian E) :=
    ((integrable_const (1 : ℝ)).indicator (hEv_meas (Finset.mem_powerset.mp hT))).const_mul _
  simp_rw [show eqBlock u i = B from rfl, hpt_decomp]
  rw [integral_finsetSum _ fun T hT => hint_Ev hT]
  have hterm (T : Finset (Fin 4)) (hT : T ∈ U.powerset) :
      ∫ x, Δ T * (Ev T).indicator (1 : E → ℝ) x ∂stdGaussian E =
        ∫ z, Δ T * (stdGaussian E).real {x | (z, remainder (u i) x) ∈ S T} ∂gaussianReal 0 1 := by
    rw [integral_const_mul, integral_indicator_one (hEv_meas (Finset.mem_powerset.mp hT)),
      real_disintegrate (hu i) (hS_meas (Finset.mem_powerset.mp hT)), ← integral_const_mul]
  rw [Finset.sum_congr rfl hterm]
  have hint_cond {T : Finset (Fin 4)} (hT : T ∈ U.powerset) :
      Integrable (fun z => Δ T * (stdGaussian E).real {x | (z, remainder (u i) x) ∈ S T})
        (gaussianReal 0 1) := by
    have hm := measurable_cond (a := u i) (hS_meas (Finset.mem_powerset.mp hT))
    have hb : Integrable (fun z => (stdGaussian E).real {x | (z, remainder (u i) x) ∈ S T})
        (gaussianReal 0 1) := by
      refine Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun z => ?_)
      rw [Real.norm_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
    exact hb.const_mul _
  rw [← integral_finsetSum _ fun T hT => hint_cond hT]
  refine integral_nonpos fun z => ?_
  by_cases hz : 0 < z ∧ z < t
  · let Fz (T : Finset (Fin 4)) : Set E := {x | Tset z (remainder (u i) x) = T}
    have hFz_eq (T : Finset (Fin 4)) : {x | (z, remainder (u i) x) ∈ S T} = Fz T := by
      ext x; simp [S, hz, Fz]
    have hFz_meas {T : Finset (Fin 4)} (hTU : T ⊆ U) : MeasurableSet (Fz T) := by
      rw [← hFz_eq]
      have hm : Measurable fun x : E => (z, remainder (u i) x) := by
        unfold remainder; fun_prop
      exact hm (hS_meas hTU)
    have hptz (x : E) : Δ (Tset z (remainder (u i) x)) =
        ∑ T ∈ U.powerset, Δ T * (Fz T).indicator (1 : E → ℝ) x := by
      have hmem : Tset z (remainder (u i) x) ∈ U.powerset :=
        Finset.mem_powerset.mpr (Finset.filter_subset _ _)
      rw [Finset.sum_eq_single (Tset z (remainder (u i) x))]
      · have hm : x ∈ Fz (Tset z (remainder (u i) x)) := rfl
        simp [indicator_of_mem hm]
      · intro T _ hne
        have hnm : x ∉ Fz T := fun h => hne h.symm
        simp [indicator_of_notMem hnm]
      · intro h; exact (h hmem).elim
    have hint_Fz {T : Finset (Fin 4)} (hT : T ∈ U.powerset) :
        Integrable (fun x => Δ T * (Fz T).indicator (1 : E → ℝ) x) (stdGaussian E) :=
      ((integrable_const (1 : ℝ)).indicator (hFz_meas (Finset.mem_powerset.mp hT))).const_mul _
    have hsum_int :
        (∑ T ∈ U.powerset, Δ T * (stdGaussian E).real {x | (z, remainder (u i) x) ∈ S T}) =
          ∫ x, Δ (Tset z (remainder (u i) x)) ∂stdGaussian E := by
      simp_rw [hFz_eq, hptz]
      symm
      rw [integral_finsetSum _ fun T hT => hint_Fz hT]
      refine Finset.sum_congr rfl fun T hT => ?_
      rw [integral_const_mul, integral_indicator_one (hFz_meas (Finset.mem_powerset.mp hT))]
    have hint_z : Integrable (fun x => Δ (Tset z (remainder (u i) x))) (stdGaussian E) :=
      (integrable_finsetSum _ fun T hT => hint_Fz hT).congr (ae_of_all _ fun x => (hptz x).symm)
    rw [hsum_int]
    let f : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.neg ℝ
    have hmp : MeasurePreserving f (stdGaussian E) (stdGaussian E) :=
      ⟨f.continuous.measurable, stdGaussian_map f⟩
    have hemb : MeasurableEmbedding f := f.toHomeomorph.measurableEmbedding
    have hrefl : ∫ x, Δ (Tset z (remainder (u i) (f x))) ∂stdGaussian E =
        ∫ x, Δ (Tset z (remainder (u i) x)) ∂stdGaussian E :=
      hmp.integral_comp hemb (fun x => Δ (Tset z (remainder (u i) x)))
    have hsum_nonpos : ∀ x : E,
        Δ (Tset z (remainder (u i) x)) + Δ (Tset z (remainder (u i) (f x))) ≤ 0 := by
      intro x
      let T₁ := Tset z (remainder (u i) x)
      let T₂ := Tset z (remainder (u i) (f x))
      have hsub : U \ T₂ ⊆ T₁ := by
        intro j hj
        obtain ⟨hjU, hjnot⟩ := Finset.mem_sdiff.mp hj
        have hjne : u j ≠ u i := by
          have := (Finset.mem_sdiff.mp hjU).2
          simpa [B, eqBlock] using this
        have hlt1 : ⟪u i, u j⟫ < 1 := inner_lt_one_of_ne (hu i) (hu j) hjne
        have hpos_z : 0 < (1 - ⟪u i, u j⟫) * z := mul_pos (by linarith) hz.1
        have hrem_neg : remainder (u i) (f x) = -remainder (u i) x := by
          have hfx : f x = -x := rfl
          rw [hfx, remainder, remainder, inner_neg_right, neg_smul]
          abel
        have hge : (1 - ⟪u i, u j⟫) * z ≤ -⟪u j, remainder (u i) x⟫ := by
          have h := mt (fun hlt => Finset.mem_filter.mpr ⟨hjU, hlt⟩) hjnot
          rw [hrem_neg, inner_neg_right] at h
          exact not_lt.mp h
        exact Finset.mem_filter.mpr ⟨hjU, by linarith⟩
      have hdisj1 : Disjoint T₁ B :=
        Finset.disjoint_left.mpr fun j hj => (Finset.mem_sdiff.mp (Finset.mem_filter.mp hj).1).2
      have hsubmod := maskCost_submodular hsub hdisj1
      have hT₂U : T₂ ⊆ U := Finset.filter_subset _ _
      have heq1 : (U \ T₂) ∪ B = Finset.univ \ T₂ := by
        ext j
        simp only [U, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
        constructor
        · rintro ((⟨-, hjT⟩) | hjB)
          · exact hjT
          · exact fun hjT => (Finset.mem_sdiff.mp (hT₂U hjT)).2 hjB
        · intro hjT
          by_cases hjB : j ∈ B
          · exact Or.inr hjB
          · exact Or.inl ⟨hjB, hjT⟩
      have heq2 : U \ T₂ = Finset.univ \ (T₂ ∪ B) := by
        ext j
        simp [U, Finset.mem_sdiff, Finset.mem_union, and_comm]
      have hΔcompl : Δ (U \ T₂) = -Δ T₂ := by
        dsimp [Δ]
        rw [heq1, heq2, maskCost_compl, maskCost_compl]
        ring
      linarith
    have hint_zf : Integrable (fun x => Δ (Tset z (remainder (u i) (f x)))) (stdGaussian E) :=
      (hmp.integrable_comp_emb hemb).mpr hint_z
    have hint_sum := integral_add hint_z hint_zf
    have h2 : ∫ x, Δ (Tset z (remainder (u i) x)) ∂stdGaussian E +
        ∫ x, Δ (Tset z (remainder (u i) (f x))) ∂stdGaussian E ≤ 0 := by
      rw [← hint_sum]
      exact integral_nonpos hsum_nonpos
    simp only [Pi.zero_apply]
    linarith
  · have hemp (T : Finset (Fin 4)) : {x | (z, remainder (u i) x) ∈ S T} = ∅ := by
      ext x; simp [S, hz]
    simp [hemp]

open Classical in
private theorem pairCost_le_zero_of_nonneg {u : Fin 4 → E} (hu : ∀ k, ‖u k‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) : pairCost u t ≤ pairCost u 0 := by
  have hu_ne (k : Fin 4) : u k ≠ 0 := fun h => by simpa [h] using hu k
  have hae0 : ∀ᵐ x ∂stdGaussian E, ∀ k : Fin 4, ⟪u k, x⟫ ≠ 0 :=
    eventually_all.mpr fun k => stdGaussian_inner_ne_const_ae (hu_ne k) 0
  have hae_ne : ∀ᵐ x ∂stdGaussian E, ∀ i j : Fin 4, u i ≠ u j → ⟪u i, x⟫ ≠ ⟪u j, x⟫ := by
    refine eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
    by_cases hij : u i = u j
    · exact ae_of_all _ fun _ h => (h hij).elim
    · filter_upwards [stdGaussian_inner_ne_const_ae (sub_ne_zero.mpr hij) 0] with x hx _
      rwa [inner_sub_left, sub_ne_zero] at hx
  rw [pairCost_eq_integral_maskCost, pairCost_eq_integral_maskCost, ← sub_nonpos,
    ← integral_sub (integrable_maskCost u t) (integrable_maskCost u 0)]
  have hcongr : ∫ x, ((maskCost (Finset.univ.filter fun k => ⟪u k, x⟫ < t) : ℝ) -
        maskCost (Finset.univ.filter fun k => ⟪u k, x⟫ < 0)) ∂stdGaussian E =
      ∫ x, (∑ i ∈ eqReps u,
        if 0 < ⟪u i, x⟫ ∧ ⟪u i, x⟫ < t then
          (maskCost ((Finset.univ.filter fun j => u j ≠ u i ∧ ⟪u j, x⟫ < ⟪u i, x⟫) ∪
              eqBlock u i) : ℝ) -
            maskCost (Finset.univ.filter fun j => u j ≠ u i ∧ ⟪u j, x⟫ < ⟪u i, x⟫)
        else 0) ∂stdGaussian E := by
    refine integral_congr_ae ?_
    filter_upwards [hae0, hae_ne] with x hx0 hxne
    exact maskCost_telescope ht hx0 hxne
  rw [hcongr]
  have hint_jump (i : Fin 4) : Integrable (fun x =>
      if 0 < ⟪u i, x⟫ ∧ ⟪u i, x⟫ < t then
        (maskCost ((Finset.univ.filter fun j => u j ≠ u i ∧ ⟪u j, x⟫ < ⟪u i, x⟫) ∪
            eqBlock u i) : ℝ) -
          maskCost (Finset.univ.filter fun j => u j ≠ u i ∧ ⟪u j, x⟫ < ⟪u i, x⟫)
      else 0) (stdGaussian E) := by
    let B := eqBlock u i
    let U := Finset.univ \ B
    let Δ (T : Finset (Fin 4)) : ℝ := (maskCost (T ∪ B) : ℝ) - maskCost T
    let Ev (T : Finset (Fin 4)) : Set E :=
      {x | (0 < ⟪u i, x⟫ ∧ ⟪u i, x⟫ < t) ∧
        (Finset.univ.filter fun j => u j ≠ u i ∧ ⟪u j, x⟫ < ⟪u i, x⟫) = T}
    have hEv_m {T : Finset (Fin 4)} (hTU : T ⊆ U) : MeasurableSet (Ev T) := by
      have heq : Ev T = {x : E | 0 < ⟪u i, x⟫ ∧ ⟪u i, x⟫ < t} ∩
          (⋂ j ∈ T, {x : E | ⟪u j, x⟫ < ⟪u i, x⟫}) ∩
          (⋂ j ∈ U \ T, {x : E | ⟪u i, x⟫ ≤ ⟪u j, x⟫}) := by
        ext x
        simp only [Ev, mem_inter_iff, mem_ofPred_eq, mem_iInter, Finset.mem_sdiff, ← not_lt]
        constructor
        · rintro ⟨hx, rfl⟩
          exact ⟨⟨hx, fun j hj => (Finset.mem_filter.mp hj).2.2⟩, fun j hj hlt =>
            hj.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ j,
              by simpa [U, B, eqBlock] using hj.1, hlt⟩)⟩
        · rintro ⟨⟨hx, h1⟩, h2⟩
          refine ⟨hx, ?_⟩
          ext j
          exact ⟨fun hj => by
            by_contra hjT
            have hjU : j ∈ U := by
              simpa [U, B, eqBlock] using (Finset.mem_filter.mp hj).2.1
            exact h2 j ⟨hjU, hjT⟩ (Finset.mem_filter.mp hj).2.2,
            fun hjT => Finset.mem_filter.mpr ⟨Finset.mem_univ j,
              by simpa [U, B, eqBlock] using hTU hjT, h1 j hjT⟩⟩
      rw [heq]
      have hm0 : MeasurableSet {x : E | 0 < ⟪u i, x⟫ ∧ ⟪u i, x⟫ < t} :=
        (measurableSet_lt measurable_const (by fun_prop : Measurable fun x : E => ⟪u i, x⟫)).inter
          (measurableSet_lt (by fun_prop : Measurable fun x : E => ⟪u i, x⟫) measurable_const)
      have hm1 : MeasurableSet (⋂ j ∈ T, {x : E | ⟪u j, x⟫ < ⟪u i, x⟫}) :=
        T.measurableSet_biInter fun j _ =>
          measurableSet_lt (by fun_prop : Measurable fun x : E => ⟪u j, x⟫)
            (by fun_prop : Measurable fun x : E => ⟪u i, x⟫)
      have hm2 : MeasurableSet (⋂ j ∈ U \ T, {x : E | ⟪u i, x⟫ ≤ ⟪u j, x⟫}) :=
        (U \ T).measurableSet_biInter fun j _ =>
          measurableSet_le (by fun_prop : Measurable fun x : E => ⟪u i, x⟫)
            (by fun_prop : Measurable fun x : E => ⟪u j, x⟫)
      exact (hm0.inter hm1).inter hm2
    have hpt (x : E) :
        (if 0 < ⟪u i, x⟫ ∧ ⟪u i, x⟫ < t then
            (maskCost ((Finset.univ.filter fun j => u j ≠ u i ∧ ⟪u j, x⟫ < ⟪u i, x⟫) ∪ B) : ℝ) -
              maskCost (Finset.univ.filter fun j => u j ≠ u i ∧ ⟪u j, x⟫ < ⟪u i, x⟫)
          else 0) =
        ∑ T ∈ U.powerset, Δ T * (Ev T).indicator (1 : E → ℝ) x := by
      let Tx := Finset.univ.filter fun j => u j ≠ u i ∧ ⟪u j, x⟫ < ⟪u i, x⟫
      have hTx : Tx ∈ U.powerset := Finset.mem_powerset.mpr fun j hj => by
        simpa [Tx, U, B, eqBlock] using (Finset.mem_filter.mp hj).2.1
      split_ifs with hx
      · rw [Finset.sum_eq_single Tx]
        · have hm : x ∈ Ev Tx := ⟨hx, rfl⟩
          simp [Δ, Tx, indicator_of_mem hm]
        · intro T _ hne
          have hnm : x ∉ Ev T := fun h => hne h.2.symm
          simp [indicator_of_notMem hnm]
        · intro h; exact (h hTx).elim
      · symm
        refine Finset.sum_eq_zero fun T _ => ?_
        have hnm : x ∉ Ev T := fun h => hx h.1
        simp [indicator_of_notMem hnm]
    exact (integrable_finsetSum _ fun T hT =>
      ((integrable_const (1 : ℝ)).indicator (hEv_m (Finset.mem_powerset.mp hT))).const_mul _
      ).congr (ae_of_all _ fun x => (hpt x).symm)
  rw [integral_finsetSum _ fun i _ => hint_jump i]
  exact Finset.sum_nonpos fun i _ => jump_integral_nonpos hu i

/-- **Zero-threshold maximality.** For any four unit vectors `u : Fin 4 → E` and any threshold
`t : ℝ`, `pairCost u t ≤ pairCost u 0`. -/
theorem pairCost_le_zero {u : Fin 4 → E} (hu : ∀ i, ‖u i‖ = 1) (t : ℝ) :
    pairCost u t ≤ pairCost u 0 := by
  rcases le_total 0 t with ht | ht
  · exact pairCost_le_zero_of_nonneg hu ht
  · have hu_ne (i : Fin 4) : u i ≠ 0 := fun h => by simpa [h] using hu i
    have hneg := pairCost_neg hu_ne (-t)
    rw [neg_neg] at hneg
    rw [hneg]
    exact pairCost_le_zero_of_nonneg hu (by linarith)

end Space

end Cslib.Circuits.Frontier.Gaussian.PairBound
