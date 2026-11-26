/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.CAT0.Toolkit
public import CslibFrontier.Probability.MarkovChain.Spectral
import CslibFrontier.Probability.PMF.ToReal

/-!
# Smoothing finite stationary walks in CAT(0) spaces

For a finite chain `P` with stationary law `π`, `crossEnergy π P x z` is the mean squared distance
between the two endpoints of a stationary step, placed by `x` and `z`. Taking the barycenter of
each transition row removes its variance from the energy of a longer walk. Summing that inequality
and choosing a time in the first half of the walk gives `exists_cat0_smoothing`.

This proves the lemma “Smoothing a walk” in [OpenAI2026HamiltonianPermanent], section
“A logarithmic lower bound for the Poincaré constant” (`entropy.tex`, lines 36–103). The demand
in its second assertion is represented by another chain with stationary law `π`.
-/

public section

namespace Cslib.Probability.MarkovChain

open Finset Cslib.CAT0 Cslib.Probability.PMF

/-- Average the cumulative variance budget over the first and second halves of the walk. -/
private theorem exists_small_variance_step {s : ℕ} (hs : 0 < s) (u q e : ℕ → ℝ)
    (hu : ∀ j, 0 ≤ u j) (hq : ∀ j, 0 ≤ q j) (he0 : e 0 = 0)
    (hbudget : ∀ j, u j + ∑ i ∈ range j, q i ≤ e j) :
    ∃ g < s, u g + s * q g ≤ (∑ j ∈ range (s + s), e (j + 1)) / s := by
  have hhalf : (∑ g ∈ range s, u g) ≤ ∑ g ∈ range s, e (g + 1) := by
    calc _ ≤ ∑ g ∈ range s, e g := sum_le_sum fun g _ =>
           (le_add_of_nonneg_right (sum_nonneg fun i _ => hq i)).trans (hbudget g)
         _ ≤ _ := by
           have hshift := sum_range_succ' e s
           rw [sum_range_succ, he0, add_zero] at hshift
           have : 0 ≤ e s := (add_nonneg (hu _) (sum_nonneg fun i _ => hq i)).trans (hbudget s)
           linarith
  have hlater (g : ℕ) : ∑ i ∈ range s, q i ≤ e (s + g + 1) :=
    (sum_le_sum_of_subset_of_nonneg (range_mono (by lia : s ≤ s + g + 1))
      (fun i _ _ => hq i)).trans
      ((le_add_of_nonneg_left (hu _)).trans (hbudget _))
  have hqhalf := sum_le_sum (s := range s) fun g _ => hlater g
  simp only [sum_const, card_range, nsmul_eq_mul] at hqhalf
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  apply (show (∃ g ∈ range s, _) → _ from fun ⟨g, hg, h⟩ => ⟨g, mem_range.mp hg, h⟩)
  apply exists_le_of_sum_le (nonempty_range_iff.2 hs.ne')
  rw [sum_const, card_range, nsmul_eq_mul, mul_div_cancel₀ _ hs', sum_add_distrib, ← mul_sum,
    sum_range_add]
  exact add_le_add hhalf hqhalf

variable {V X : Type*} [Fintype V] [MetricSpace X]

/-- Mean squared distance for a joint law given by an initial distribution and a step. -/
@[expose] noncomputable def crossEnergy (π : PMF V) (K : MarkovChain V) (x z : V → X) : ℝ :=
  ∑ i, (π i).toReal * K.stepOp (fun j => dist (x i) (z j) ^ 2) i

/-- Squared-distance energy is nonnegative. -/
theorem crossEnergy_nonneg (π : PMF V) (K : MarkovChain V) (x z : V → X) :
    0 ≤ crossEnergy π K x z := by
  simp only [crossEnergy, stepOp_apply]
  exact sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg
    (sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))

/-- One barycentric step removes its variance from the energy of a longer walk. -/
theorem crossEnergy_variance_step {π : PMF V} {K : MarkovChain V} (hK : K.IsStationary π)
    (A : MarkovChain V) (x z b : V → X)
    (hb : ∀ j, IsBarycenter (fun k => (A j k).toReal) z (b j)) :
    crossEnergy π K x b + crossEnergy π A b z ≤ crossEnergy π (K * A) x z := by
  let f (j : V) := A.stepOp (fun k => dist (b j) (z k) ^ 2) j
  have hf : (∑ i, (π i).toReal * K.stepOp f i) = crossEnergy π A b z := hK.sum_mul_stepOp f
  calc
    _ = ∑ i, (π i).toReal * K.stepOp (fun j => dist (x i) (b j) ^ 2 + f j) i := by
      rw [← hf]
      simp [crossEnergy, stepOp_apply, mul_add, sum_add_distrib]
    _ ≤ _ := by
      simp only [crossEnergy, map_mul, mul_apply_eq_comp, stepOp_apply]
      refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      refine sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      simpa only [f, stepOp_apply, sum_toReal, one_mul, add_comm] using hb j (x i)

private theorem cumulative_variance {π : PMF V} {A : MarkovChain V} (hstat : A.IsStationary π)
    (x : V → X) (z : ℕ → V → X)
    (hb : ∀ g j, IsBarycenter (fun k => (A j k).toReal) (z g) (z (g + 1) j)) (h g : ℕ) :
    crossEnergy π 1 x (z (g + h)) +
      ∑ k ∈ range h, crossEnergy π A (z (g + k + 1)) (z (g + k)) ≤
        crossEnergy π (A ^ h) x (z g) := by
  induction h generalizing g with
  | zero => simp
  | succ h ih =>
    have hstep := crossEnergy_variance_step (hstat.pow h) A x (z g) (z (g + 1)) (hb g)
    have hi := ih (g + 1)
    rw [sum_range_succ', pow_succ]
    refine le_trans ?_ hstep
    simpa only [Nat.add_assoc, Nat.add_comm 1, Nat.add_zero, add_assoc] using
      add_le_add hi (le_refl (crossEnergy π A (z (g + 1)) (z g)))

private theorem energy_le_four_lazy (π : PMF V) (P : MarkovChain V) (z b : V → X) :
    crossEnergy π P z z ≤ 4 * crossEnergy π P.lazy b z := by
  simp only [crossEnergy, stepOp_lazy_apply, mul_sum]
  refine sum_le_sum fun i _ => ?_
  let f (j : V) := dist (b i) (z j) ^ 2
  have hlocal : P.stepOp (fun j => dist (z i) (z j) ^ 2) i ≤
      P.stepOp ((2 : ℝ) • ((fun _ => f i) + f)) i := by
    simp only [stepOp_apply]
    apply sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    change dist (z i) (z j) ^ 2 ≤ 2 * (f i + f j)
    exact ((sq_le_sq₀ dist_nonneg (add_nonneg dist_nonneg dist_nonneg)).mpr
      (dist_triangle_left (z i) (z j) (b i))).trans add_sq_le
  rw [map_smul, map_add, P.stepOp_const] at hlocal
  change _ ≤ 2 * (f i + P.stepOp f i) at hlocal
  calc
    _ ≤ (π i).toReal * (2 * (f i + P.stepOp f i)) :=
      mul_le_mul_of_nonneg_left hlocal ENNReal.toReal_nonneg
    _ = _ := by dsimp [f]; ring

/-- For every even time `2s ≥ 2`, a CAT(0) placement can be smoothed with cost at most
sixteen times its mean squared displacement over the first `2s` lazy walk lengths. -/
theorem exists_cat0_smoothing [CompleteCAT0Space X] (P : MarkovChain V) (π : PMF V)
    (hπ : P.IsStationary π) (x : V → X) {s : ℕ} (hs : 0 < s) :
    ∃ y : V → X, crossEnergy π 1 x y + (2 * s : ℝ) * crossEnergy π P y y ≤
      16 * (∑ j ∈ range (s + s), crossEnergy π (P.lazy ^ (j + 1)) x x) / (2 * s : ℝ) := by
  classical
  let : Nonempty X := ⟨x π.support_nonempty.choose⟩
  let A := P.lazy
  let B (z : V → X) (i : V) := (exists_isBarycenter (fun j => (A i j).toReal)
    (fun _ => ENNReal.toReal_nonneg) z).choose
  let z (g : ℕ) := B^[g] x
  have hb (g : ℕ) (i : V) : IsBarycenter (fun j => (A i j).toReal) (z g) (z (g + 1) i) := by
    change IsBarycenter _ _ (B^[g + 1] x i)
    rw [Function.iterate_succ_apply']
    exact (exists_isBarycenter _ (fun _ => ENNReal.toReal_nonneg) _).choose_spec
  let u (g : ℕ) := crossEnergy π 1 x (z g)
  let q (g : ℕ) := crossEnergy π A (z (g + 1)) (z g)
  let e (h : ℕ) := crossEnergy π (A ^ h) x x
  have he0 : e 0 = 0 := by simp [e, crossEnergy]
  have hbudget (h : ℕ) : u h + ∑ i ∈ range h, q i ≤ e h := by
    simpa only [u, q, e, A, Nat.zero_add, show z 0 = x by rfl] using
      cumulative_variance hπ.lazy x z hb h 0
  obtain ⟨g, _, hg⟩ := exists_small_variance_step hs u q e (fun _ => crossEnergy_nonneg ..)
    (fun _ => crossEnergy_nonneg ..) he0 hbudget
  refine ⟨z g, ?_⟩
  have huv : 0 ≤ u g := crossEnergy_nonneg ..
  have hle : crossEnergy π P (z g) (z g) ≤ 4 * q g := energy_le_four_lazy π P (z g) (z (g + 1))
  have hs' : 0 < (s : ℝ) := by exact_mod_cast hs
  calc
    _ ≤ u g + 2 * s * (4 * q g) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hle (by positivity))
    _ ≤ 8 * (u g + s * q g) := by linarith
    _ ≤ _ := by
      calc _ ≤ 8 * ((∑ j ∈ range (s + s), e (j + 1)) / s) :=
             mul_le_mul_of_nonneg_left hg (by norm_num)
           _ = _ := by dsimp [e, A]; ring

/-- Moving both endpoints of a stationary joint law costs at most three times the sum of the
two mean squared endpoint moves and the mean squared distance between the new endpoints. -/
theorem crossEnergy_three {π : PMF V} {D : MarkovChain V} (hD : D.IsStationary π) (x y : V → X) :
    crossEnergy π D x x ≤ 3 * (2 * crossEnergy π 1 x y + crossEnergy π D y y) := by
  let f i := dist (x i) (y i) ^ 2
  have hdiag : crossEnergy π 1 x y = ∑ i, (π i).toReal * f i := by simp [crossEnergy, f]
  calc
    _ ≤ ∑ i, (π i).toReal *
        D.stepOp ((3 : ℝ) • ((fun _ => f i) + (fun j => dist (y i) (y j) ^ 2) + f)) i := by
      simp only [crossEnergy, stepOp_apply]
      refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      refine sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      have ht : dist (x i) (x j) ≤ dist (x i) (y i) + dist (y i) (y j) + dist (x j) (y j) :=
        (dist_triangle_right _ _ (y j)).trans
          (add_le_add (dist_triangle _ (y i) _) (le_refl _))
      have hsq := (sq_le_sq₀ dist_nonneg (by positivity)).mpr ht
      change _ ≤ 3 * (f i + dist (y i) (y j) ^ 2 + f j)
      dsimp only [f]
      nlinarith only [hsq, sq_nonneg (dist (x i) (y i) - dist (y i) (y j)),
        sq_nonneg (dist (x i) (y i) - dist (x j) (y j)),
        sq_nonneg (dist (y i) (y j) - dist (x j) (y j))]
    _ = _ := by
      rw [hdiag]
      simp only [map_smul, map_add, stepOp_const, Pi.smul_apply, Pi.add_apply,
        smul_eq_mul, mul_left_comm _ (3 : ℝ), ← mul_sum, mul_add, sum_add_distrib,
        hD.sum_mul_stepOp f, crossEnergy]
      ring

/-- A comparison against one step passes to the time-averaged lazy walk. -/
theorem energy_comparison_lazy_average [CompleteCAT0Space X] {P D : MarkovChain V} {π : PMF V}
    (hP : P.IsStationary π) (hD : D.IsStationary π) {β : ℝ}
    (hcomp : ∀ y : V → X, crossEnergy π D y y ≤ β * crossEnergy π P y y)
    {s : ℕ} (hs : 0 < s) (x : V → X) :
    crossEnergy π D x x ≤ 48 * max 2 (β / (2 * s)) *
      ((∑ j ∈ range (s + s), crossEnergy π (P.lazy ^ (j + 1)) x x) / (2 * s)) := by
  obtain ⟨y, h⟩ := exists_cat0_smoothing P π hP x hs
  let κ := max 2 (β / (2 * s))
  have ht : 0 < (2 * s : ℝ) := by positivity
  have hκ : 0 ≤ κ := (by norm_num : (0 : ℝ) ≤ 2).trans (le_max_left _ _)
  have hb : β ≤ κ * (2 * s) := (div_le_iff₀ ht).mp (le_max_right _ _)
  have hu := crossEnergy_nonneg π 1 x y
  have he := crossEnergy_nonneg π P y y
  calc _ ≤ 3 * (2 * crossEnergy π 1 x y + crossEnergy π D y y) := crossEnergy_three hD x y
       _ ≤ 3 * (κ * (crossEnergy π 1 x y + 2 * s * crossEnergy π P y y)) := by
         rw [mul_add κ, ← mul_assoc κ]
         exact mul_le_mul_of_nonneg_left (add_le_add
           (mul_le_mul_of_nonneg_right (le_max_left _ _) hu)
           ((hcomp y).trans (mul_le_mul_of_nonneg_right hb he))) (by norm_num)
       _ ≤ 3 * (κ * (16 * (∑ j ∈ range (s + s), _) / (2 * s))) := by gcongr
       _ = _ := by dsimp [κ]; ring

end Cslib.Probability.MarkovChain
