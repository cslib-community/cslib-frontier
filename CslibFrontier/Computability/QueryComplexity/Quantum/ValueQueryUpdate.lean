/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.ValueAdversary
public import CslibFrontier.Foundations.Quantum.Measurement.Overlap
public import CslibFrontier.Foundations.Quantum.Measurement.Restrict
public import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Chebyshev

/-!
# Changing one entry of a coherent value oracle

The query-magnitude argument of [Bennett et al., Theorem 3.3][BBBV1997] bounds the effect of
changing oracle answers on the state of a quantum algorithm. Here each symbol selects a unitary
on the response register, which includes a multi-bit XOR oracle and arbitrary workspace.

After T coherent queries, the adversary produces a classical message by measuring its state.
The challenger samples an address from a message-dependent distribution with point probabilities
at most δ and reveals the address. Refreshing the oracle there changes the final acceptance
probability by at most 2 T √δ. The continuation has the residual quantum state and the current
table. The bound covers one programming event.
-/

public section

namespace Cslib.Quantum

open Finset
open scoped BigOperators NNReal

variable {ι V W α : Type*} [Fintype ι] [Fintype V] [Fintype W] [DecidableEq ι]
variable (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
variable (H : ι → α)

/-- Replacing a single table entry changes only its query slice. -/
theorem norm_valueOracle_update_sub_le (ψ : ValueState ι V W) (i : ι) (v : α) :
    ‖valueOracle step (Function.update H i v) ψ - valueOracle step H ψ‖ ≤
      2 * ‖querySlice i ψ‖ := by
  let u := valueOracle step (Function.update H i v) ψ
  let w := valueOracle step H ψ
  have hslice (j : ι) : querySlice j (u - w) = querySlice j u - querySlice j w := rfl
  have he : ‖u - w‖ ^ 2 = ‖querySlice i u - querySlice i w‖ ^ 2 := by
    rw [← sum_sq_norm_querySlice, sum_eq_single i, hslice]
    · intro j _ hji
      have hz : querySlice j u = querySlice j w := by
        ext ⟨a, b⟩
        simp only [u, w, querySlice_apply, valueOracle_apply, Function.update_of_ne hji]
      simp [hslice, hz]
    · simp
  calc
    ‖u - w‖ = ‖querySlice i u - querySlice i w‖ :=
      (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he
    _ ≤ ‖querySlice i u‖ + ‖querySlice i w‖ := norm_sub_le _ _
    _ = _ := by simp [u, w, two_mul]

variable (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) (ψ : ValueState ι V W)

/-- The distance from changing one table entry is at most twice the sum of the unmodified
run's query amplitudes at that index. -/
theorem norm_runValue_update_sub_le (i : ι) (v : α) (T : ℕ) :
    ‖runValue step U ψ (Function.update H i v) T - runValue step U ψ H T‖ ≤
      2 * ∑ t ∈ range T, ‖querySlice i (runValue step U ψ H t)‖ := by
  induction T with
  | zero => simp [runValue]
  | succ T ih =>
    let u := runValue step U ψ (Function.update H i v) T
    let w := runValue step U ψ H T
    rw [runValue, runValue, ← map_sub, LinearIsometry.norm_map, sum_range_succ, mul_add]
    change ‖valueOracle step _ u - valueOracle step H w‖ ≤ _
    calc
      _ ≤ ‖valueOracle step (Function.update H i v) u -
            valueOracle step (Function.update H i v) w‖ +
          ‖valueOracle step (Function.update H i v) w - valueOracle step H w‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by
        rw [← map_sub, LinearIsometryEquiv.norm_map]
        exact add_le_add ih (norm_valueOracle_update_sub_le step H w i v)

private theorem sum_sq_runValue_update_sub_le (hψ : ‖ψ‖ = 1) (T : ℕ) (v : α) :
    ∑ i, ‖runValue step U ψ (Function.update H i v) T - runValue step U ψ H T‖ ^ 2 ≤
      4 * (T : ℝ) ^ 2 := by
  let s := fun i t => ‖querySlice i (runValue step U ψ H t)‖
  calc
    _ ≤ ∑ i, (2 * ∑ t ∈ range T, s i t) ^ 2 :=
      sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (norm_runValue_update_sub_le ..) 2
    _ ≤ ∑ i, 4 * (T * ∑ t ∈ range T, s i t ^ 2) := by
      refine sum_le_sum fun i _ => ?_
      rw [mul_pow]
      norm_num
      simpa using sq_sum_le_card_mul_sum_sq (s := range T) (f := s i)
    _ = _ := by
      rw [← mul_sum, ← mul_sum, sum_comm]
      simp only [s, sum_sq_norm_querySlice, norm_runValue, hψ, one_pow, sum_const, card_range,
        nsmul_eq_mul, mul_one]
      ring

/-- Squared norms sum to the input norm squared across the fibers of a basis readout. -/
theorem sum_sq_norm_projOutcomes_fibers {B M : Type*} [Fintype B] [Fintype M] [DecidableEq M]
    (readout : B → M) (ϕ : EuclideanSpace ℂ B) :
    ∑ m, ‖projOutcomes (fun x => readout x = m) ϕ‖ ^ 2 = ‖ϕ‖ ^ 2 := by
  simp_rw [norm_projOutcomes_sq]
  rw [EuclideanSpace.norm_sq_eq]
  simp only [measureProb, sum_filter]
  rw [sum_comm]
  simp

private theorem abs_weighted_measureProb_sub_le {J κ : Type*} [Fintype J] [Fintype κ]
    (w : J → ℝ≥0) (a b : J → EuclideanSpace ℂ κ) (accept : J → Finset κ)
    (ha : ∑ j, (w j : ℝ) * ‖a j‖ ^ 2 = 1) (hb : ∑ j, (w j : ℝ) * ‖b j‖ ^ 2 = 1) :
    |(∑ j, (w j : ℝ) * measureProb (a j) (accept j)) -
      ∑ j, (w j : ℝ) * measureProb (b j) (accept j)| ≤
      Real.sqrt (∑ j, (w j : ℝ) * ‖a j - b j‖ ^ 2) := by
  classical
  let pack (u : J → EuclideanSpace ℂ κ) : EuclideanSpace ℂ (J × κ) :=
    WithLp.toLp 2 fun jk => (Real.sqrt (w jk.1) : ℂ) * (u jk.1).ofLp jk.2
  let event (S : J → Finset κ) := univ.filter fun jk : J × κ => jk.2 ∈ S jk.1
  have mass (u : J → EuclideanSpace ℂ κ) (S : J → Finset κ) :
      measureProb (pack u) (event S) = ∑ j, (w j : ℝ) * measureProb (u j) (S j) := by
    simp only [pack, event, measureProb, sum_filter, Fintype.sum_prod_type,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (w _).coe_nonneg, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [← sum_filter]
    simp
  have normsq (u : J → EuclideanSpace ℂ κ) : ‖pack u‖ ^ 2 = ∑ j, (w j : ℝ) * ‖u j‖ ^ 2 := by
    simpa [event, measureProb_univ] using mass u (fun _ => univ)
  have normalized (u : J → EuclideanSpace ℂ κ) (hu : ∑ j, (w j : ℝ) * ‖u j‖ ^ 2 = 1) :
      ‖pack u‖ = 1 := by nlinarith [normsq u, norm_nonneg (pack u)]
  have sub : pack a - pack b = pack (fun j => a j - b j) := by
    ext ⟨j, k⟩
    simp [pack, PiLp.sub_apply, mul_sub]
  have h := abs_measureProb_sub_le_norm_sub (normalized a ha) (normalized b hb) (event accept)
  rw [mass, mass, sub] at h
  simpa only [← normsq, Real.sqrt_sq (norm_nonneg _)] using h

/-- A fresh table update at a sampled address after a normalized family of retained
measurement branches. The full private coin giving the address remains available to the
continuation. The weighted change of the final Born probability is controlled by the proven
squared sensitivity of the prefix under a single table update. -/
theorem abs_branch_refresh_le {M Y B κ : Type*} [Fintype M] [Fintype Y] [Fintype B]
    [Fintype κ] [Fintype α] [Nonempty α]
    (branch : (ι → α) → M → EuclideanSpace ℂ B) (norm : ∀ H, ∑ m, ‖branch H m‖ ^ 2 = 1)
    {cost : ℝ} (hcost : 0 ≤ cost)
    (sensitivity : ∀ H v, ∑ i, ∑ m, ‖branch (Function.update H i v) m - branch H m‖ ^ 2 ≤ cost ^ 2)
    (p : M → PMF Y) (address : M → Y → ι) {δ : ℝ≥0}
    (hp : ∀ m i, (((p m).map (address m)) i).toReal ≤ δ)
    (post : (ι → α) → M → Y → EuclideanSpace ℂ B →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (accept : (ι → α) → M → Y → Finset κ) :
    |(𝔼 hv : (ι → α) × α, ∑ m, ∑ y, (p m y).toReal *
        measureProb (post (Function.update hv.1 (address m y) hv.2) m y (branch hv.1 m))
          (accept (Function.update hv.1 (address m y) hv.2) m y)) -
      (𝔼 hv : (ι → α) × α, ∑ m, ∑ y, (p m y).toReal *
        measureProb (post hv.1 m y (branch hv.1 m)) (accept hv.1 m y))| ≤ cost * Real.sqrt δ := by
  classical
  let D := (ι → α) × α
  let change (x : D) (i : ι) := Function.update x.1 i x.2
  let avg (f : (ι → α) → (ι → α) → M → Y → ℝ) :=
    𝔼 hv : D, ∑ m, ∑ i, (p m i).toReal * f hv.1 (change hv (address m i)) m i
  have swap (f : (ι → α) → (ι → α) → M → Y → ℝ) : avg f = avg (fun H G => f G H) := by
    have hswap (m : M) (i : Y) : (𝔼 hv : D, (p m i).toReal * f hv.1 (change hv (address m i)) m i) =
        𝔼 hv : D, (p m i).toReal * f (change hv (address m i)) hv.1 m i := by
      let g (hv : D) : D := (change hv (address m i), hv.1 (address m i))
      have hg : Function.Involutive g := by rintro ⟨a, v⟩; simp [g, change]
      apply Fintype.expect_equiv hg.toPerm
      intro hv
      simp [g, change, Function.Involutive.toPerm]
    unfold avg
    simp_rw [expect_sum_comm, hswap]
  let J := D × M × Y
  let w (j : J) : ℝ≥0 := (Fintype.card D : ℝ≥0)⁻¹ * (p j.2.1 j.2.2).toNNReal
  have weights (f : J → ℝ) :
      (∑ j : J, (w j : ℝ) * f j) =
        𝔼 hv : D, ∑ m, ∑ i, (p m i).toReal * f (hv, m, i) := by
    simp only [J, w, Fintype.sum_prod_type, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_natCast,
      Fintype.expect_eq_sum_div_card, div_eq_inv_mul, mul_sum, mul_assoc]
    rfl
  let a (j : J) := post j.1.1 j.2.1 j.2.2 (branch (change j.1 (address j.2.1 j.2.2)) j.2.1)
  let b (j : J) := post j.1.1 j.2.1 j.2.2 (branch j.1.1 j.2.1)
  let S (j : J) := accept j.1.1 j.2.1 j.2.2
  have base (H : ι → α) : (∑ m, ∑ i, (p m i).toReal * ‖branch H m‖ ^ 2) = 1 := by
    simpa only [← sum_mul, Probability.PMF.sum_toReal, one_mul] using norm H
  have hb : ∑ j, (w j : ℝ) * ‖b j‖ ^ 2 = 1 := by
    simp only [b, LinearIsometry.norm_map, weights, base, Fintype.expect_const]
  have ha : ∑ j, (w j : ℝ) * ‖a j‖ ^ 2 = 1 := by
    simp only [a, LinearIsometry.norm_map, weights]
    change avg (fun _ G m _ => ‖branch G m‖ ^ 2) = 1
    calc
      _ = _ := swap (fun _ G m _ => ‖branch G m‖ ^ 2)
      _ = 1 := by simp [avg, base]
  let score (H G : ι → α) (m : M) (i : Y) :=
    measureProb (post G m i (branch H m)) (accept G m i)
  change |avg score - _| ≤ _
  rw [swap score]
  have probabil := abs_weighted_measureProb_sub_le w a b S ha hb
  change |(∑ j : J, (w j : ℝ) * score (change j.1 (address j.2.1 j.2.2)) j.1.1 j.2.1 j.2.2) -
    ∑ j : J, (w j : ℝ) * score j.1.1 j.1.1 j.2.1 j.2.2| ≤ _ at probabil
  rw [weights, weights] at probabil
  refine probabil.trans ?_
  simp only [a, b, ← map_sub, LinearIsometry.norm_map, weights]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt δ.coe_nonneg]
  refine expect_le univ_nonempty fun x _ => ?_
  change (∑ m, ∑ y, (p m y).toReal * ‖branch (change x (address m y)) m - branch x.1 m‖ ^ 2) ≤ _
  have transport (m : M) := Probability.PMF.sum_map_mul (p m) (address m)
    (fun i => ‖branch (change x i) m - branch x.1 m‖ ^ 2)
  simp_rw [← transport]
  rw [sum_comm]
  calc
    _ ≤ ∑ i, ∑ m, (δ : ℝ) * ‖branch (change x i) m - branch x.1 m‖ ^ 2 := by
      gcongr with i _ m
      exact hp m i
    _ ≤ _ := by
      simp only [← mul_sum, mul_comm (cost ^ 2)]
      exact mul_le_mul_of_nonneg_left (sensitivity x.1 x.2) δ.coe_nonneg

omit H in
/-- One reprogramming after a classical message is measured from the quantum adversary's state.
Conditioned on the message, the challenger draws an address from its specified distribution,
with point masses bounded by δ. The continuation sees the message, address and current table.
Its distinguishing advantage after T prior coherent queries is at most `2 T √δ`. -/
theorem abs_readout_reprogrammed_measureProb_sub_le {M κ : Type*} [Fintype M] [DecidableEq M]
    [Fintype κ] [Fintype α] [Nonempty α] (hψ : ‖ψ‖ = 1) (T : ℕ)
    (readout : ι × V × W → M) (p : M → PMF ι) {δ : ℝ≥0} (hp : ∀ m i, (p m i).toReal ≤ δ)
    (post : (ι → α) → M → ι → ValueState ι V W →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (accept : (ι → α) → M → ι → Finset κ) :
    |(𝔼 hv : (ι → α) × α, ∑ m, ∑ i, (p m i).toReal *
        measureProb (post (Function.update hv.1 i hv.2) m i
          (projOutcomes (fun x => readout x = m) (runValue step U ψ hv.1 T)))
          (accept (Function.update hv.1 i hv.2) m i)) -
      (𝔼 hv : (ι → α) × α, ∑ m, ∑ i, (p m i).toReal *
        measureProb (post hv.1 m i
          (projOutcomes (fun x => readout x = m) (runValue step U ψ hv.1 T)))
          (accept hv.1 m i))| ≤ 2 * T * Real.sqrt δ := by
  let branch (H : ι → α) (m : M) :=
    projOutcomes (fun x => readout x = m) (runValue step U ψ H T)
  have total (H : ι → α) : ∑ m, ‖branch H m‖ ^ 2 = 1 := by
    simp only [branch, sum_sq_norm_projOutcomes_fibers, norm_runValue, hψ, one_pow]
  have sensitive (H : ι → α) (v : α) :
      ∑ i, ∑ m, ‖branch (Function.update H i v) m - branch H m‖ ^ 2 ≤ (2 * T : ℝ) ^ 2 := by
    simp only [branch, ← map_sub, sum_sq_norm_projOutcomes_fibers]
    convert sum_sq_runValue_update_sub_le step H U ψ hψ T v using 1; ring
  exact abs_branch_refresh_le branch total (by positivity) sensitive p (fun _ => id)
    (by simpa only [PMF.map_id] using hp) post accept

omit H in
/-- One reprogramming in a finite quantum random oracle. After `T` coherent queries to a
uniform table, the challenger reveals an independently drawn point and optionally refreshes its
value. Both continuations see the point and the current table and may act on the retained state.
The bound applies to their final measurement, including table- and point-dependent tests. -/
theorem abs_reprogrammed_measureProb_sub_le {κ : Type*} [Fintype κ] [Fintype α] [Nonempty α]
    (hψ : ‖ψ‖ = 1) (T : ℕ) (p : PMF ι) {δ : ℝ} (hp : ∀ i, (p i).toReal ≤ δ)
    (post : (ι → α) → ι → ValueState ι V W →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (accept : (ι → α) → ι → Finset κ) :
    |(𝔼 hv : (ι → α) × α, ∑ i, (p i).toReal *
        measureProb (post (Function.update hv.1 i hv.2) i (runValue step U ψ hv.1 T))
          (accept (Function.update hv.1 i hv.2) i)) -
      (𝔼 hv : (ι → α) × α, ∑ i, (p i).toReal *
        measureProb (post hv.1 i (runValue step U ψ hv.1 T)) (accept hv.1 i))| ≤
      2 * T * Real.sqrt δ := by
  have proj (u : ValueState ι V W) : projOutcomes (fun _ => True) u = u := by
    ext x
    simp
  have hδ := ENNReal.toReal_nonneg.trans (hp p.support_nonempty.choose)
  have bound :=
    abs_readout_reprogrammed_measureProb_sub_le step U ψ hψ T (fun _ => ())
      (fun _ => p) (δ := ⟨δ, hδ⟩) (fun _ => hp) (fun H _ => post H) (fun H _ => accept H)
  simp only [Fintype.sum_unique, proj] at bound
  convert bound using 1
  rfl

end Cslib.Quantum
