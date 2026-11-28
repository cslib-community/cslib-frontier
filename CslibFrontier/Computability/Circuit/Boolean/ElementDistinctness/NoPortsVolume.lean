/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ElementDistinctness.RoutingGrid
public import CslibFrontier.Computability.Circuit.Boolean.ElementDistinctness.VolumeToSize
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.SpectralPorts
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Element distinctness in the absence of metric ports

Let `p` be the volume per delivered bit in a joint realization of tagged permutations on
`2 ^ h` records. Its rectangle has order at least `2 ^ h`, degree at most a constant times
`h p`, and squared-distance Poincaré bound at most a constant times `p²`. In the absence of
metric ports the logarithmic obstruction gives one finite inequality,
`h ≤ C p² log(2 + h p)`. Since the logarithm grows slower than each positive power,
`p > h ^ ε` eventually for every `ε < 1/2`.

The signed projection from element distinctness keeps the graph. Applying the routing
inequality at an exponent strictly between `ε` and `1/2` absorbs the width shift and the
ratio of record lengths. The same exponent reaches the full binary Boolean circuit basis.

This proves the no-ports case of [OpenAI2026MatrixExponentNineFourths, Theorem 2.2] through
the independent-pair obstruction of [OpenAI2026HamiltonianPermanent, Theorem 4.2].
-/

public section

namespace Cslib.Circuits.Boolean.ElementDistinctness

open Filter

/-- Normalize the graph order bound for a graph of degree three times `q`, where
`q ≤ 13 h p` and `p` is the price per payload bit. -/
private theorem exists_graph_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {h q : ℕ} {p : ℝ}, 0 < h → 0 < q → 1 ≤ p → (q : ℝ) ≤ 13 * h * p →
      2 ^ h ≤ (24 * q) ^ (2 * ⌈7000 * (1 + 12 * (2 * ((q : ℝ) * 3 / h)) ^ 2)⌉₊) →
      (h : ℝ) ≤ C * p ^ 2 * Real.log (2 + h * p) := by
  let a : ℝ := 12 * (2 * (3 * 13)) ^ 2
  let c : ℝ := 2 * (7000 * (1 + a) + 1)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < c := by dsimp [c, a]; positivity
  refine ⟨10 * c / Real.log 2, by positivity, fun {h q p} hh hq hp hcap hsize => ?_⟩
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hp' : 0 < p := by linarith
  let b := 12 * (2 * ((q : ℝ) * 3 / h)) ^ 2
  have hratio : (q : ℝ) * 3 / h ≤ 3 * 13 * p :=
    (div_le_iff₀ hh').mpr (by nlinarith only [hcap])
  have hb : b ≤ a * p ^ 2 := calc
    _ ≤ 12 * (2 * (3 * 13 * p)) ^ 2 := by dsimp [b]; gcongr
    _ = _ := by dsimp [a]; ring
  have hceil : 2 * (⌈7000 * (1 + b)⌉₊ : ℝ) ≤ c * p ^ 2 := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ 7000 * (1 + b) by dsimp [b]; positivity)
    dsimp only [c]
    nlinarith only [hceil, hb, one_le_pow₀ hp (n := 2)]
  have hdegree : Real.log (24 * (q : ℝ)) ≤ 10 * Real.log (2 + h * p) := by
    rw [← show Real.log ((2 + h * p) ^ 10) = 10 * Real.log (2 + h * p) by
      rw [Real.log_pow]; norm_num]
    apply Real.log_le_log (by positivity)
    calc
      _ ≤ 312 * ((h : ℝ) * p) := by linarith only [hcap]
      _ ≤ (2 + (h : ℝ) * p) ^ 9 * (2 + h * p) := by
        apply mul_le_mul _ (by linarith) (by positivity) (by positivity)
        exact (show (312 : ℝ) ≤ 2 ^ 9 by norm_num).trans
          (pow_le_pow_left₀ (by norm_num) (by nlinarith only [mul_nonneg hh'.le hp'.le]) _)
      _ = _ := (pow_succ _ _).symm
  change 2 ^ h ≤ (24 * q) ^ (2 * ⌈7000 * (1 + b)⌉₊) at hsize
  have hsizeR : (2 : ℝ) ^ h ≤ (24 * (q : ℝ)) ^ (2 * ⌈7000 * (1 + b)⌉₊) := by
    exact_mod_cast hsize
  have hl := Real.log_le_log (by positivity) hsizeR
  rw [Real.log_pow, Real.log_pow, Nat.cast_mul, Nat.cast_ofNat] at hl
  have hf := hl.trans (mul_le_mul hceil hdegree (Real.log_nonneg (by linarith)) (by positivity))
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hlog2]
  linarith only [hf]

private theorem eventually_rpow_lt_of_log_bound {C ε : ℝ} (hC : 0 < C) (hε : ε < 1 / 2) :
    ∀ᶠ h : ℕ in atTop, ∀ p : ℝ, 0 ≤ p →
      (h : ℝ) ≤ C * p ^ 2 * Real.log (2 + h * p) → (h : ℝ) ^ ε < p := by
  have small := (isLittleO_log_rpow_atTop (show 0 < 1 - 2 * ε by linarith)).const_mul_left
    (3 * C)
  have hlim := small.eventuallyLT_norm_of_eventually_pos (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact norm_pos_iff.mpr (Real.rpow_pos_of_pos hx _).ne')
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually hlim,
    eventually_ge_atTop 2] with h hlim hh
  have hh' : (2 : ℝ) ≤ h := by exact_mod_cast hh
  have hh1 : (1 : ℝ) ≤ h := by linarith
  have hh0 : (0 : ℝ) < h := by positivity
  have hlog := Real.log_nonneg hh1
  have hlim' : 3 * C * Real.log h < (h : ℝ) ^ (1 - 2 * ε) := by
    simpa only [Real.norm_of_nonneg (show 0 ≤ 3 * C * Real.log h by positivity),
      Real.norm_of_nonneg (Real.rpow_nonneg hh0.le _)] using hlim
  intro p hp hcost
  by_contra! hcheap
  have hph := hcheap.trans (Real.rpow_le_self_of_one_le hh1 (by linarith))
  have hlogp : Real.log (2 + h * p) ≤ 3 * Real.log h := by
    rw [← show Real.log ((h : ℝ) ^ 3) = 3 * Real.log h by rw [Real.log_pow]; norm_num]
    apply Real.log_le_log (by positivity)
    have hh2 : 2 ≤ (h : ℝ) ^ 2 := by nlinarith only [sq_nonneg ((h : ℝ) - 2), hh']
    have hc := mul_le_mul_of_nonneg_left hh' (sq_nonneg (h : ℝ))
    nlinarith only [hh2, hc, mul_le_mul_of_nonneg_left hph hh0.le]
  have hlogp0 : 0 ≤ Real.log (2 + h * p) :=
    Real.log_nonneg (by nlinarith only [mul_nonneg hh0.le hp])
  have hbig : (h : ℝ) < h := calc
    _ ≤ C * p ^ 2 * Real.log (2 + h * p) := hcost
    _ ≤ C * ((h : ℝ) ^ ε) ^ 2 * (3 * Real.log h) := by gcongr
    _ = (3 * C * Real.log h) * (h : ℝ) ^ (2 * ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hh0.le]
      norm_num
      ring_nf
    _ < (h : ℝ) ^ (1 - 2 * ε) * (h : ℝ) ^ (2 * ε) :=
      mul_lt_mul_of_pos_right hlim' (Real.rpow_pos_of_pos hh0 _)
    _ = _ := by rw [← Real.rpow_add hh0]; norm_num
  exact hbig.false

open Frontier

section MetricTargets

universe u

variable (K : Type) [Field K] {ι : Type*} (X : ι → Type u)
  [∀ i, MetricSpace (X i)] [hCAT : ∀ i, CompleteCAT0Space (X i)]
  (hprice : ∀ i, PartyTensor.IsPrice K (dist : X i → X i → ℝ))
  (hno : ¬RotationMap.HasPorts X)

include hCAT hprice hno

open scoped Classical in
/-- Without metric ports, the volume per delivered bit `p` satisfies
`h ≤ C p² log(2 + h p)` on every positive-width tagged-permutation batch in the dyadic range. -/
theorem exists_routing_volume_log_bound_of_not_metricPorts :
    ∃ C : ℝ, 0 < C ∧ ∀ {h t : ℕ}, 0 < h → 0 < t → t ≤ 2 * 2 ^ h → ∀ {V E : Type}
      [Fintype V] [Fintype E] [DecidableEq E] (N : OpenBitNetwork K (Fin t × RoutingBit h) V E),
      N.Trivalent → (∀ z, N.contraction z =
        ∏ a : Fin t, if TaggedPermutation (fun q => z (a, q)) then 1 else 0) →
      let p := (N.volume : ℝ) / (t * 2 ^ h * h)
      (h : ℝ) ≤ C * p ^ 2 * Real.log (2 + h * p) := by
  obtain ⟨C, hC, bound⟩ := exists_graph_log_bound
  refine ⟨C, hC, fun {h t} hh ht htr {V E} _ _ _ N hN hT => ?_⟩
  let : NeZero h := ⟨hh.ne'⟩
  obtain ⟨k, hk, _, ht4, R, hR⟩ := exists_regular_of_taggedPermutation.{u} ht htr N hN hT
  let S := Fin (2 ^ k) × Fin (2 ^ k) × Fin (2 ^ (h - k))
  let B := 2 ^ k * 2 ^ h
  let q := Fintype.card V / B + 1 + 8 * h
  let p := (N.volume : ℝ) / (t * 2 ^ h * h)
  have hcost : (N.volume : ℝ) = t * 2 ^ h * h * p := by dsimp [p]; field_simp
  have leftBits : 3 * (t * 2 ^ h * h) ≤ N.volume := by
    simp only [OpenBitNetwork.volume, Nat.card_eq_fintype_card, Fintype.card_prod,
      Fintype.card_fin, card_routingBit]
    nlinarith
  have hp : 1 ≤ p := by
    dsimp only [p]
    apply (le_div_iff₀ (by positivity)).mpr
    exact (show 1 * ((t : ℝ) * 2 ^ h * h) ≤ 3 * ((t : ℝ) * 2 ^ h * h) by
      gcongr; norm_num).trans (by exact_mod_cast leftBits)
  have hB : Fintype.card S = B := by
    simp only [S, B, Fintype.card_prod, Fintype.card_fin]
    rw [← pow_add, Nat.add_sub_of_le hk]
  have horder : 2 ^ h ≤ Fintype.card S := by
    rw [hB]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  have hS : 2 ≤ Fintype.card S :=
    (show 2 ≤ 2 ^ h by simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hh).trans horder
  have hqpos : 0 < q := by dsimp [q]; lia
  let : NeZero q := ⟨hqpos.ne'⟩
  have hmetric : ∀ i, R.HasPoincareBound (X i) (12 * (2 * ((q : ℝ) * 3 / h)) ^ 2) :=
    fun i => hR (X i) (hprice i)
  have hg := R.card_lt_pow_of_not_hasPorts (by positivity) hS hmetric hno
  have hdegree : 8 * Fintype.card (Fin q × Fin 3) = 24 * q := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    lia
  change Fintype.card S < (8 * Fintype.card (Fin q × Fin 3)) ^ _ at hg
  rw [hdegree] at hg
  apply bound hh hqpos hp _ (horder.trans hg.le)
  have hV : Fintype.card V ≤ N.volume := by
    simp only [OpenBitNetwork.volume, Nat.card_eq_fintype_card]
    lia
  have hcap : ((Fintype.card V / B : ℕ) : ℝ) ≤ 4 * h * p := by
    apply (le_of_mul_le_mul_right · (by dsimp [B]; positivity : (0 : ℝ) < B))
    calc
      _ ≤ (N.volume : ℝ) := by exact_mod_cast (Nat.div_mul_le_self (Fintype.card V) B).trans hV
      _ = _ := hcost
      _ ≤ _ := by
        have ht4' : (t : ℝ) ≤ 4 * (2 : ℝ) ^ k := by exact_mod_cast ht4
        dsimp [B]
        push_cast
        have hm := mul_le_mul_of_nonneg_right ht4'
          (show 0 ≤ (2 : ℝ) ^ h * h * p by positivity)
        linarith only [hm]
  dsimp [q]
  push_cast
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hp' := le_mul_of_one_le_right (Nat.cast_nonneg h : (0 : ℝ) ≤ h) hp
  linarith only [hcap, hp', hh']

open scoped Classical in
/-- A routing batch pays more than `h ^ ε` per delivered bit for every `ε < 1/2`,
uniformly for all batch sizes between one and twice the number of addresses. -/
theorem eventually_routing_volume_of_not_metricPorts {ε : ℝ} (hε : ε < 1 / 2) :
    ∀ᶠ h : ℕ in atTop, ∀ t : ℕ, 0 < t → t ≤ 2 * 2 ^ h → ∀ {V E : Type} [Fintype V]
      [Fintype E] [DecidableEq E] (N : OpenBitNetwork K (Fin t × RoutingBit h) V E),
      N.Trivalent → (∀ z, N.contraction z =
        ∏ a : Fin t, if TaggedPermutation (fun q => z (a, q)) then 1 else 0) →
      (t : ℝ) * 2 ^ h * h * (h : ℝ) ^ ε < N.volume := by
  obtain ⟨C, hC, hbound⟩ := exists_routing_volume_log_bound_of_not_metricPorts K X hprice hno
  filter_upwards [eventually_rpow_lt_of_log_bound hC hε, eventually_gt_atTop 0] with h rate hh
  intro t ht htr V E _ _ _ N hN hT
  have hp := rate _ (by positivity) (hbound hh ht htr N hN hT)
  exact (lt_div_iff₀' (by positivity)).mp hp

omit hCAT hprice hno in
private theorem shifted_input_bits_le {ε δ : ℝ} (hε : ε ≤ 1) {h : ℕ} (hh : 0 < h)
    (hgap : 16 ≤ (h : ℝ) ^ (δ - ε)) :
    ((2 ^ (h + 1) * (2 * (h + 1)) : ℕ) : ℝ) * ((h + 1 : ℕ) : ℝ) ^ ε ≤
      (2 : ℝ) ^ h * h * (h : ℝ) ^ δ := by
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  let ratio := ((h : ℝ) + 1) / h
  have hr1 : 1 ≤ ratio := (le_div_iff₀ hh0).mpr (by linarith)
  have hr2 : ratio ≤ 2 := (div_le_iff₀ hh0).mpr (by linarith)
  have hsucc : ((h : ℝ) + 1) ^ ε ≤ 2 * (h : ℝ) ^ ε := calc
    _ = (ratio * h) ^ ε := congrArg (fun x : ℝ => x ^ ε) (div_mul_cancel₀ _ hh0.ne').symm
    _ = ratio ^ ε * (h : ℝ) ^ ε := Real.mul_rpow (by dsimp [ratio]; positivity) hh0.le
    _ ≤ _ := mul_le_mul_of_nonneg_right ((Real.rpow_le_self_of_one_le hr1 hε).trans hr2)
      (Real.rpow_nonneg hh0.le _)
  have hscale : 16 * (h : ℝ) ^ ε ≤ (h : ℝ) ^ δ := calc
    _ ≤ (h : ℝ) ^ (δ - ε) * (h : ℝ) ^ ε :=
      mul_le_mul_of_nonneg_right hgap (Real.rpow_nonneg hh0.le _)
    _ = _ := by rw [← Real.rpow_add hh0, sub_add_cancel]
  push_cast
  rw [pow_succ]
  calc
    _ ≤ (2 : ℝ) ^ h * 2 * (2 * (h + 1)) * (2 * (h : ℝ) ^ ε) := by gcongr
    _ ≤ (2 : ℝ) ^ h * h * (16 * (h : ℝ) ^ ε) := by
      have hc := mul_le_mul_of_nonneg_right (show 8 * ((h : ℝ) + 1) ≤ 16 * h by linarith)
        (show 0 ≤ (2 : ℝ) ^ h * (h : ℝ) ^ ε by positivity)
      linarith only [hc]
    _ ≤ _ := by gcongr

open scoped Classical in
/-- The same exponent below one half applies to dyadic element distinctness, uniformly over
joint trivalent batches up to the number of records. -/
theorem eventually_elementDistinctness_volume_of_not_metricPorts {ε : ℝ} (hε : ε < 1 / 2) :
    ∀ᶠ w : ℕ in atTop, ∀ t : ℕ, 0 < t → t ≤ 2 ^ w → ∀ {V E : Type} [Fintype V]
      [Fintype E] [DecidableEq E] (N : OpenBitNetwork K (Fin t × Fin (2 ^ w * (2 * w))) V E),
      N.Trivalent → (∀ z, N.contraction z = ∏ i : Fin t,
        if elementDistinctness (2 ^ w) (2 * w) (fun q => z (i, q)) then 1 else 0) →
      (t : ℝ) * (2 ^ w * (2 * w) : ℕ) * (w : ℝ) ^ ε < N.volume := by
  let δ := (ε + 1 / 2) / 2
  have hd : δ < 1 / 2 := by dsimp [δ]; linarith
  have hgap : 0 < δ - ε := by dsimp [δ]; linarith
  have hpred := tendsto_sub_atTop_nat 1
  have router := hpred.eventually (eventually_routing_volume_of_not_metricPorts K X hprice hno hd)
  have gap := (tendsto_rpow_atTop hgap).comp ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hpred)
  filter_upwards [router, gap.eventually_ge_atTop 16, eventually_ge_atTop 2] with w hr hg hw
  obtain ⟨h, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : w ≠ 0)
  change 16 ≤ ((h + 1 - 1 : ℕ) : ℝ) ^ (δ - ε) at hg
  simp only [Nat.succ_sub_one] at hr hg
  intro t ht htr V E _ _ _ N hN hD
  obtain ⟨M, _, hM, hv, hT⟩ := exists_taggedPermutationNetwork N hN hD
  have hc := hr t ht (by simpa only [pow_succ, Nat.mul_comm] using htr) M hM hT
  have hs := mul_le_mul_of_nonneg_left
    (shifted_input_bits_le (by linarith : ε ≤ 1) (by lia) hg) (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
  exact (by simpa only [mul_assoc] using hs : _ ≤ (t : ℝ) * 2 ^ h * h * (h : ℝ) ^ δ).trans_lt
    (hc.trans_le (by exact_mod_cast hv))

end MetricTargets

variable (K : Type) [Field K] (hno : ¬PartyTensor.HasPorts K)

include hno

open scoped Classical in
/-- Over a field without ports, a dyadic element-distinctness batch of up to `2 ^ w` lists
costs more than its exterior bit count times `w ^ ε` for each `ε < 1 / 2` and all large `w`. -/
theorem eventually_elementDistinctness_volume_of_not_hasPorts {ε : ℝ} (hε : ε < 1 / 2) :
    ∀ᶠ w : ℕ in atTop, ∀ t : ℕ, 0 < t → t ≤ 2 ^ w → ∀ {V E : Type} [Fintype V]
      [Fintype E] [DecidableEq E] (N : OpenBitNetwork K (Fin t × Fin (2 ^ w * (2 * w))) V E),
      N.Trivalent → (∀ z, N.contraction z = ∏ i : Fin t,
        if elementDistinctness (2 ^ w) (2 * w) (fun q => z (i, q)) then 1 else 0) →
      (t : ℝ) * (2 ^ w * (2 * w) : ℕ) * (w : ℝ) ^ ε < N.volume :=
  eventually_elementDistinctness_volume_of_not_metricPorts K
    (fun X : PartyTensor.HadamardPriceSpace.{0} K => X.Carrier) (fun X => X.isPrice)
    (fun hp => hno ((PartyTensor.hasPorts_iff_metricPorts K).mpr hp)) hε

/-- Over a field without ports, all sufficiently large record counts have Boolean circuit
size greater than `N (log₂ N)^ε / 128` for every `ε < 1/2`, at unrestricted depth and fan-out. -/
theorem eventually_complexity_of_not_hasPorts {ε : ℝ} (hε : ε < 1 / 2) :
    ∀ᶠ m : ℕ in atTop, let N := m * (2 * Nat.clog 2 m)
      1 / 128 * N * (Real.logb 2 N) ^ ε <
        complexity (fullInterpretation (k := 2))
          (single (elementDistinctness m (2 * Nat.clog 2 m))) := by
  let δ := max ε (1 / 4)
  have hδ : 0 < δ := (show (0 : ℝ) < 1 / 4 by norm_num).trans_le (le_max_right _ _)
  have hd : δ < 1 / 2 := max_lt hε (by norm_num)
  have upper := eventual_complexity_of_single_copy_volume K (ε := δ) (a := 1) hδ zero_lt_one
  have hvol := eventually_elementDistinctness_volume_of_not_hasPorts K hno hd
  have lower := upper (by
    filter_upwards [hvol] with w hw
    intro V E _ _ _ N hN hD
    let I := Fin (2 ^ w * (2 * w))
    let e : Fin 1 × I ≃ I := Equiv.uniqueProd _ _
    obtain ⟨M, hM, hv, hc⟩ := N.exists_reindex hN e
    have hMcon (x : Fin 1 × I → Bool) : M.contraction x = ∏ i : Fin 1,
        if elementDistinctness (2 ^ w) (2 * w) (fun q => x (i, q)) then 1 else 0 := by
      rw [hc, hD, Fin.prod_univ_one]
      rfl
    have hs := hw 1 (by decide) Nat.one_le_two_pow M hM hMcon
    simpa only [Nat.cast_one, hv] using hs.le)
  have h4 : (4 : ℝ) ^ δ ≤ 2 := calc
    _ ≤ (4 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hd.le
    _ = _ := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
      norm_num
  have hco : (1 : ℝ) / 128 ≤ 1 / (64 * 4 ^ δ) := by
    gcongr
    linarith
  filter_upwards [lower, eventually_gt_atTop 1] with m hm hm1
  let N := m * (2 * Nat.clog 2 m)
  have hN : 2 ≤ N := (show 2 ≤ m by lia).trans
    (Nat.le_mul_of_pos_right _ (Nat.mul_pos (by decide) (Nat.clog_pos (by decide) hm1)))
  have hlog : 1 ≤ Real.logb 2 N := by
    rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by exact_mod_cast hN)
  apply lt_of_le_of_lt _ hm
  change 1 / 128 * (N : ℝ) * (Real.logb 2 N) ^ ε ≤
    1 / (64 * 4 ^ δ) * N * (Real.logb 2 N) ^ δ
  exact mul_le_mul (mul_le_mul_of_nonneg_right hco (Nat.cast_nonneg N))
    (Real.rpow_le_rpow_of_exponent_le hlog (le_max_left _ _))
    (Real.rpow_nonneg (by linarith) _) (by positivity)

end Cslib.Circuits.Boolean.ElementDistinctness
