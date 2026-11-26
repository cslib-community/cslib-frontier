/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Threshold
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import CslibFrontier.Foundations.BooleanAnalysis.Fibers
public import CslibFrontier.Computability.Communication.TopDown.Rectangle
public import CslibFrontier.Computability.Communication.TopDown.Adversary
import CslibFrontier.Foundations.Analysis.BernoulliInequality
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import Mathlib.Data.Fintype.Powerset
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Choose.Sum

/-!
# Top-down lower bounds for majority

The two Hamming layers on either side of the threshold of strict majority (`strictMajority`, which
is false at a tie) have entropy deficit `O(log n)`, and from every point at least half of the
coordinates lead to the other layer by one flip. This gives bilateral density limits at rate
`16 / n`, so Korten's adversary applies, and the logarithmic initial deficit keeps the exponent
`1 / (d - 1)`: no protocol with `d` messages of `ε n ^ (1 / (d - 1))` bits solves the
Karchmer–Wigderson game of strict majority on `n` bits for large `n`
(`not_solvesKW_strictMajority`). This extends the parity argument of Korten
[Korten2026].

## Main definitions

* `Cslib.Communication.strictMajorityDeficitBound`: the deficit of the starting layers.

## Main results

* `Cslib.Communication.RoundProtocol.not_solvesKW_strictMajority`: the bound with explicit
  constants.
* `Cslib.Communication.not_solvesKW_strictMajority`: the communication lower bound for
  strict majority.

## References

* [O. Korten, *Top-Down Lower Bounds for All Depths*][Korten2026]
-/

@[expose] public section

/-! ### Hamming layers and the initial majority deficit

Strict majority (`strictMajority`) is false at a tie, so the two layers at weights `n / 2` and
`n / 2 + 1` straddle its threshold.
-/

namespace Cslib.Communication

open BitString
open Finset
open Filter Asymptotics

/-- A common deficit and density-limit bound for the two majority boundary layers.
The logarithmic term bounds their entropy deficit; `128` bounds the mask size. -/
noncomputable def strictMajorityDeficitBound (n : ℕ) : ℝ :=
  128 + Real.logb 2 (2 * ((n : ℝ) + 1))

/-! ### Absorbing the logarithmic initial deficit

The middle-layer deficit bound is little-o of every positive power of `n`.
Thus replacing the parity deficit `1` with this logarithmic bound preserves
the exponent `1/(d-1)` in a `d`-round communication lower bound.
-/

private theorem strictMajorityDeficitBound_eventually_le {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → strictMajorityDeficitBound n ≤ c * (n : ℝ) ^ r := by
  have hlog := isLittleO_log_rpow_atTop hr
  have hs := (Real.isLittleO_const_log_atTop (c := (130 : ℝ)).trans hlog).add
    (hlog.const_mul_left (Real.log 2)⁻¹)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually (hs.def hc))
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0 : ℝ) < n := by linarith
  have hbound := hN n (by omega)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnpos.le _)] at hbound
  have hlogb : Real.logb 2 (2 * ((n : ℝ) + 1)) ≤ 2 + (Real.log 2)⁻¹ * Real.log n := by
    calc Real.logb 2 (2 * ((n : ℝ) + 1))
        ≤ Real.logb 2 (4 * (n : ℝ)) :=
          Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)
      _ = Real.logb 2 ((2 : ℝ) ^ (2 : ℕ)) + Real.logb 2 n := by
          rw [Real.logb_mul (by norm_num) hnpos.ne']; norm_num
      _ = 2 + (Real.log 2)⁻¹ * Real.log n := by
          rw [Real.logb_two_pow, Real.logb, div_eq_mul_inv, mul_comm]; norm_num
  unfold strictMajorityDeficitBound
  exact (show 128 + Real.logb 2 (2 * ((n : ℝ) + 1)) ≤
    130 + (Real.log 2)⁻¹ * Real.log n by linarith).trans ((le_abs_self _).trans hbound)

private theorem finite_budget_with_deficit_of_cost {n d : ℕ} (hd : 0 < d) {m k : ℝ}
    (hm : 0 ≤ m) (hk : 0 ≤ k)
    (hcost : m ≤ (n : ℝ) ^ ((d : ℝ)⁻¹) / (128 * (32768 * (194 : ℝ) ^ d)))
    (hkcost : k ≤ (n : ℝ) ^ ((d : ℝ)⁻¹) / (128 * (32768 * (194 : ℝ) ^ d))) :
    64 * (32768 * (194 : ℝ) ^ d * (m + k)) ^ d ≤ (n : ℝ) := by
  let C : ℝ := 32768 * (194 : ℝ) ^ d
  have hstep : 64 * (C * (m + k)) ≤ (n : ℝ) ^ ((d : ℝ)⁻¹) := by
    have hsum : m + k ≤ (n : ℝ) ^ ((d : ℝ)⁻¹) / (64 * C) := by
      calc m + k
          ≤ (n : ℝ) ^ ((d : ℝ)⁻¹) / (128 * C) + (n : ℝ) ^ ((d : ℝ)⁻¹) / (128 * C) :=
            add_le_add hcost hkcost
        _ = (n : ℝ) ^ ((d : ℝ)⁻¹) / (64 * C) := by ring
    simpa only [mul_assoc] using (le_div_iff₀' (by positivity : 0 < 64 * C)).mp hsum
  calc 64 * (C * (m + k)) ^ d
      ≤ 64 ^ d * (C * (m + k)) ^ d := by
        gcongr; exact le_self_pow₀ (by norm_num) hd.ne'
    _ = (64 * (C * (m + k))) ^ d := (mul_pow ..).symm
    _ ≤ ((n : ℝ) ^ ((d : ℝ)⁻¹)) ^ d := by gcongr
    _ = n := Real.rpow_inv_natCast_pow (by positivity) hd.ne'

/-! ### The two layers around the threshold of strict majority

The largest binomial coefficient is at least `2^n/(n+1)`, and its upper
neighbor is at least half as large. This gives a logarithmic entropy
deficit for both boundary layers, for even as well as odd input sizes.
-/

private theorem le_strictMajorityDeficitBound (n : ℕ) : 128 ≤ strictMajorityDeficitBound n := by
  exact le_add_of_nonneg_right <| Real.logb_nonneg (by norm_num)
    (by linarith [Nat.cast_nonneg (α := ℝ) n])

private theorem two_pow_le_succ_mul_choose_half (n : ℕ) : 2 ^ n ≤ (n + 1) * n.choose (n / 2) := by
  calc
    _ = ∑ r ∈ range (n + 1), n.choose r := (Nat.sum_range_choose n).symm
    _ ≤ ∑ _r ∈ range (n + 1), n.choose (n / 2) :=
      sum_le_sum (fun r _ => Nat.choose_le_middle r n)
    _ = _ := by simp

private theorem choose_half_le_two_mul_choose_half_succ {n : ℕ} (hn : 2 ≤ n) :
    n.choose (n / 2) ≤ 2 * n.choose (n / 2 + 1) := by
  refine Nat.le_of_mul_le_mul_right ?_ (show 0 < n - n / 2 by omega)
  calc n.choose (n / 2) * (n - n / 2)
      = n.choose (n / 2 + 1) * (n / 2 + 1) := (Nat.choose_succ_right_eq n (n / 2)).symm
    _ ≤ n.choose (n / 2 + 1) * (2 * (n - n / 2)) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 * n.choose (n / 2 + 1) * (n - n / 2) := by ring

private theorem weightLayer_deficit {n r : ℕ} (hr : r ≤ n)
    (hcard : 2 ^ n ≤ (2 * (n + 1)) * n.choose r) :
    (weightLayer n r).Nonempty ∧
      uniformDeficit (weightLayer n r) ≤ strictMajorityDeficitBound n := by
  have hne : (weightLayer n r).Nonempty := weightLayer_nonempty hr
  refine ⟨hne, ((uniformDeficit_le_iff hne).mpr ?_).trans (le_add_of_nonneg_left (by norm_num))⟩
  simp only [Fintype.card_fin, card_weightLayer]
  rw [Real.rpow_sub (by norm_num), Real.rpow_natCast,
    Real.rpow_logb (by norm_num) (by norm_num) (by positivity), div_le_iff₀ (by positivity)]
  exact_mod_cast (mul_comm (2 * (n + 1)) _ ▸ hcard)

private theorem majority_layers_deficit {n : ℕ} (hn : 2 ≤ n) :
    ((weightLayer n (n / 2)).Nonempty ∧
      uniformDeficit (weightLayer n (n / 2)) ≤ strictMajorityDeficitBound n) ∧
    ((weightLayer n (n / 2 + 1)).Nonempty ∧
      uniformDeficit (weightLayer n (n / 2 + 1)) ≤ strictMajorityDeficitBound n) := by
  have hmid := two_pow_le_succ_mul_choose_half n
  refine ⟨weightLayer_deficit (by omega) (hmid.trans ?_),
    weightLayer_deficit (by omega) (hmid.trans ?_)⟩
  · rw [mul_assoc]; exact Nat.le_mul_of_pos_left _ (by decide)
  · calc (n + 1) * n.choose (n / 2)
        ≤ (n + 1) * (2 * n.choose (n / 2 + 1)) :=
          Nat.mul_le_mul_left _ (choose_half_le_two_mul_choose_half_succ hn)
      _ = 2 * (n + 1) * n.choose (n / 2 + 1) := by ring

/-! ### Density limits from many single-bit neighbors

At rate `16/n`, a mask hits any set of at least `n/2` coordinates with
probability at least `8/9`. Its expected size is `16`, so the probability
that it has more than `128` coordinates is at most `1/8`. A selected
single-bit neighbor then gives fiber density at least `2^(-128)`.

Applying this to the two middle Hamming layers initializes Korten's top-down adversary for strict
majority, extending his initialization for parity [Korten2026].
-/

private theorem coordinateDensity_of_neighbor {n : ℕ} (X : Finset (Fin n → Bool))
    (P x : Fin n → Bool) (i : Fin n) (hi : P i = true)
    (hx : Function.update x i (!x i) ∈ X) (hsmall : weight P ≤ 128) :
    (2 : ℝ) ^ (-(128 : ℝ)) ≤ coordinateDensity X P x := by
  have he : completePattern P x (fun j => Function.update x i (!x i) j) =
      Function.update x i (!x i) := funext fun j => by
    rcases eq_or_ne j i with rfl | hj
    · simp [completePattern, hi]
    · by_cases hP : P j = true <;> simp [completePattern, hP, Function.update_of_ne hj]
  have hne : (coordinateFiber X P x).Nonempty := ⟨_, mem_filter.mpr ⟨mem_univ _, by rwa [he]⟩⟩
  have hc : (1 : ℝ) ≤ (coordinateFiber X P x).card := by exact_mod_cast card_pos.mpr hne
  rw [coordinateDensity, Fintype.card_subtype]
  change (2 : ℝ) ^ (-(128 : ℝ)) ≤ (coordinateFiber X P x).card / (2 : ℝ) ^ weight P
  rw [le_div_iff₀ (by positivity)]
  have hpw := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hsmall
  calc _ ≤ (2 : ℝ) ^ (-(128 : ℝ)) * (2 : ℝ) ^ (128 : ℕ) := by gcongr
    _ = 1 := by rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]; norm_num
    _ ≤ _ := hc

private theorem isDensityLimit_of_many_neighbors {n : ℕ} (hn : 16 ≤ n)
    (X : Finset (Fin n → Bool)) (x s : Fin n → Bool) (hs : n ≤ 2 * weight s)
    (hneighbor : ∀ i, s i = true → Function.update x i (!x i) ∈ X) :
    IsDensityLimit X (16 / n) 128 x := by
  let p : ℝ := 16 / n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hp' : p ≤ 1 := (div_le_one hnpos).mpr (by exact_mod_cast hn)
  have hmean : (n : ℝ) * p = 16 := by dsimp [p]; field_simp
  have hhit : 8 ≤ (weight s : ℝ) * p := by
    have := mul_le_mul_of_nonneg_right (by exact_mod_cast hs : (n : ℝ) ≤ 2 * weight s) hp
    linarith
  have hnone : (1 - p) ^ weight s ≤ 1 / 9 := by
    have hmul : (1 - p) ^ weight s * 9 ≤ 1 :=
      (mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg (sub_nonneg.mpr hp') _)).trans
        (Real.one_sub_pow_mul_one_add_mul_le_one hp' (weight s))
    linarith
  have hpoint (P : Fin n → Bool) :
      (if ∃ i, s i = true ∧ P i = true then (1 : ℝ) else 0) -
        (1 / 128) * (weight P : ℝ) ≤
      if (2 : ℝ) ^ (-(128 : ℝ)) ≤ coordinateDensity X P x then 1 else 0 := by
    have hw : (0 : ℝ) ≤ weight P := Nat.cast_nonneg _
    split_ifs with h1 h2 h2
    any_goals linarith
    obtain ⟨i, hi, hPi⟩ := h1
    have hgt : 128 < weight P := not_le.mp fun hle =>
      h2 (coordinateDensity_of_neighbor X P x i hPi (hneighbor i hi) hle)
    linarith [show (128 : ℝ) < weight P by exact_mod_cast hgt]
  have hh := bernoulliAverage_mono hp hp' hpoint
  have hhits : bernoulliAverage p (fun P : Fin n → Bool =>
      if ∃ i, s i = true ∧ P i = true then (1 : ℝ) else 0) = 1 - (1 - p) ^ weight s := by
    convert bernoulliAverage_hits p s
  rw [bernoulliAverage_sub, hhits, bernoulliAverage_const_mul, bernoulliAverage_weight,
    Fintype.card_fin, hmean] at hh
  unfold IsDensityLimit
  change (3 : ℝ) / 4 ≤ bernoulliAverage p _
  linarith

private theorem majority_layers_limits {n : ℕ} (hn : 16 ≤ n) :
    (∀ x ∈ weightLayer n (n / 2),
      IsDensityLimit (weightLayer n (n / 2 + 1)) (16 / n) (strictMajorityDeficitBound n) x) ∧
    (∀ y ∈ weightLayer n (n / 2 + 1),
      IsDensityLimit (weightLayer n (n / 2)) (16 / n) (strictMajorityDeficitBound n) y) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : (16 : ℝ) / n ≤ 1 := (div_le_one hnpos).mpr (by exact_mod_cast hn)
  constructor
  · intro x hx
    have hx' : weight x = n / 2 := mem_weightLayer.mp hx
    refine (isDensityLimit_of_many_neighbors hn (weightLayer n (n / 2 + 1)) x (fun i => !x i)
      (by rw [weight_not, Fintype.card_fin, hx']; omega) fun i hi => ?_).mono_right
      (by positivity) hp (le_strictMajorityDeficitBound n)
    have hi' : x i = false := by simpa using hi
    simp only [mem_weightLayer, hi', Bool.not_false, weight_update_true hi', hx']
  · intro y hy
    have hy' : weight y = n / 2 + 1 := mem_weightLayer.mp hy
    refine (isDensityLimit_of_many_neighbors hn (weightLayer n (n / 2)) y y
      (by rw [hy']; omega) fun i hi => ?_).mono_right
      (by positivity) hp (le_strictMajorityDeficitBound n)
    simp only [mem_weightLayer, hi, Bool.not_true]
    have := weight_update_false hi
    omega

/-! ### The communication lower bound for strict majority

The bilateral density adversary starts from the two layers around the threshold, and the power-law
budget absorbs their logarithmic entropy deficit. This extends the argument of Korten
[Korten2026], whose Theorem 3 is the case of parity.
-/

namespace RoundProtocol

variable {M : Type*} [Fintype M]

/-- The bound for strict majority with explicit constants: no protocol with `d + 1` messages of at
most `m` bits solves the Karchmer–Wigderson game of strict majority on `n` bits when
`64 (32768 · 194 ^ d (m + strictMajorityDeficitBound n)) ^ d ≤ n`. -/
theorem not_solvesKW_strictMajority {n d : ℕ} (P : KWRoundProtocol (Fin n) M (d + 1))
    {m : ℝ} (hM : (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m) (hm : 0 ≤ m)
    (hsize : 64 * (32768 * (194 : ℝ) ^ d * (m + strictMajorityDeficitBound n)) ^ d ≤ (n : ℝ)) :
    ¬ P.SolvesKW (strictMajority n) := by
  have hk := le_strictMajorityDeficitBound n
  have hC : 1 ≤ 32768 * (194 : ℝ) ^ d * (m + strictMajorityDeficitBound n) := by
    have : (1 : ℝ) ≤ 194 ^ d := one_le_pow₀ (by norm_num)
    calc (1 : ℝ) ≤ 32768 * 1 * 128 := by norm_num
      _ ≤ 32768 * (194 : ℝ) ^ d * (m + strictMajorityDeficitBound n) := by gcongr; linarith
  have hn64 : (64 : ℝ) ≤ n := (le_mul_of_one_le_right (by norm_num) (one_le_pow₀ hC)).trans hsize
  have hn16 : 16 ≤ n := by exact_mod_cast (show (16 : ℝ) ≤ n by linarith)
  have hnpos : (0 : ℝ) < n := by linarith
  have ⟨hX, hY⟩ := majority_layers_deficit (show 2 ≤ n by omega)
  have ⟨hleft, hright⟩ := majority_layers_limits hn16
  have hbudget :
      (32768 * (194 : ℝ) ^ d * (m + strictMajorityDeficitBound n)) ^ d * (16 / n) ≤ 1 / 4 := by
    rw [← mul_div_assoc, div_le_iff₀ hnpos]; linarith
  intro hsol
  refine P.not_solves_bilateral_density hM hm (by linarith)
    (by positivity) hX.1 hY.1 hX.2 hY.2 hleft hright hbudget fun x hx y hy => hsol x y
      (strictMajority_eq_false_iff.mpr (mem_weightLayer.mp hx).le)
      (strictMajority_eq_true_iff.mpr (by have := mem_weightLayer.mp hy; omega))

end RoundProtocol

universe u in
/-- **The communication lower bound for strict majority**, extending
[Korten, Theorem 3][Korten2026]: for every `d ≥ 2` there is `ε > 0` such that, for all large `n`, no
protocol with `d` messages from an alphabet of at most `2 ^ (ε n ^ (1 / (d - 1)))` letters solves
the Karchmer–Wigderson game of strict majority on `n` bits. -/
theorem not_solvesKW_strictMajority (rounds : ℕ) (hrounds : 2 ≤ rounds) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ {M : Type u} [Fintype M],
      (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ) ^ (((rounds - 1 : ℕ) : ℝ)⁻¹)) →
        ∀ P : KWRoundProtocol (Fin n) M rounds, ¬ P.SolvesKW (strictMajority n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show rounds ≠ 0 by omega)
  have hd : 0 < d := by omega
  let ε : ℝ := 1 / (128 * (32768 * (194 : ℝ) ^ d))
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨N, hN⟩ := strictMajorityDeficitBound_eventually_le
    (show (0 : ℝ) < (d : ℝ)⁻¹ by positivity) hε
  refine ⟨ε, hε, N, fun n hn M _ hM P => ?_⟩
  have hm : 0 ≤ ε * (n : ℝ) ^ (((d + 1 - 1 : ℕ) : ℝ)⁻¹) := by positivity
  apply P.not_solvesKW_strictMajority hM hm
  have hk := le_strictMajorityDeficitBound n
  apply finite_budget_with_deficit_of_cost hd hm (by linarith)
  · simp only [ε, Nat.add_sub_cancel]
    exact le_of_eq (by ring)
  · simpa only [ε, one_div, div_eq_mul_inv, mul_comm, one_mul] using hN n hn

end Cslib.Communication
