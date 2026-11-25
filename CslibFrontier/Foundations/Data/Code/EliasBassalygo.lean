/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.Basic
public import CslibFrontier.Foundations.Data.Code.Linear
public import CslibFrontier.Foundations.Data.Code.ListDecoding.JohnsonBound
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Foundations.Data.Code.HammingBound
import CslibFrontier.Foundations.Data.Code.Johnson
import CslibFrontier.Foundations.Data.Nat.Choose.Entropy
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Elias–Bassalygo bound

Let `C` be a code of length `n` over an alphabet of `q` letters, and let
`V = ∑_{j ≤ e} (n choose j) (q - 1) ^ j` be the volume of a Hamming ball of radius `e`. Every
codeword lies in `V` balls of radius `e`, so on average a ball of radius `e` contains
`|C| V / q ^ n` codewords, and some ball contains at least that many
(`Cslib.Code.exists_card_mul_sum_choose_le_pow_mul`) [GuruswamiRudraSudan2019, Lemma 8.1.2]. If the
code has minimum distance at least `d` and `q e ≤ (q - 1) n`, the q-ary Johnson bound
(`Cslib.Code.card_filter_hammingDist_le_mul_le_of_mul_le`) bounds the number of codewords in that
ball, which gives the **Elias–Bassalygo bound** [Bassalygo1965], [GuruswamiRudraSudan2019,
Section 8.1] in finite form:
`|C| V ((q - 1) (n - e) ^ 2 + e ^ 2 - (q - 1) n (n - d)) ≤ q ^ n (q - 1) n d`
(`Cslib.Code.card_mul_sum_choose_mul_le`). Below the q-ary Johnson radius, that is when
`(q - 1) n (n - d) < (q - 1) (n - e) ^ 2 + e ^ 2`, this reads `|C| V ≤ q ^ n (q - 1) n d`
(`Cslib.Code.card_mul_sum_choose_le`): the Hamming bound `|C| V ≤ q ^ n` at a radius that may
exceed half the minimum distance, at the price of a polynomial factor.

Combining `Cslib.Code.card_mul_sum_choose_le` with the `q`-ary Johnson-radius bridge
`Cslib.Code.mul_le_sub_one_mul_and_lt_of_lt_johnsonRadius` and the single-term entropy lower bound
`Cslib.exp_mul_qaryEntropy_le_succ_mul_choose_mul_pow`
(`CslibFrontier.Foundations.Data.Nat.Choose.Entropy`) gives the finite rate upper bound
`rate C ≤ 1 - H_q(e / n) / log q + log_q((q - 1) n d (n + 1)) / n` for every `e / n < J_q(d / n)`
(`Cslib.Code.rate_le_of_lt_johnsonRadius`), and passing to the limit as `n → ∞` yields the
asymptotic **Elias–Bassalygo rate bound**
`rate (C s) ≤ 1 - H_q(J_q(δ)) / log q + ε` eventually along a filter
(`Cslib.Code.eventually_rate_le_one_sub_qaryEntropy_johnsonRadius`).

## Main results

* `Cslib.Code.exists_card_mul_sum_choose_le_pow_mul`: some Hamming ball contains its share of the
  codewords.
* `Cslib.Code.card_mul_sum_choose_mul_le`, `Cslib.Code.card_mul_sum_choose_le`: the
  Elias–Bassalygo bound in finite form.
* `Cslib.Code.rate_le_of_lt_johnsonRadius`: the finite Elias–Bassalygo rate upper bound for any
  radius strictly below the `q`-ary Johnson radius.
* `Cslib.Code.eventually_rate_le_one_sub_qaryEntropy_johnsonRadius`: the asymptotic
  Elias–Bassalygo rate upper bound as the block length tends to infinity.

## References

* [L. A. Bassalygo, *New upper bounds for error-correcting codes*][Bassalygo1965]
  (locator unverified)
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*][GuruswamiRudraSudan2019]
  (locator unverified for the rate bounds)
-/

public section

namespace Cslib.Code

open Finset

section Finite

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] [Nonempty α]

/-- **Some Hamming ball contains its share of the code** [GuruswamiRudraSudan2019, Lemma 8.1.2]:
for a code `C` of length `n` over `q` letters and a radius `e`, some word `w` has at least
`|C| V / q ^ n` codewords within distance `e`, where `V = ∑_{j ≤ e} (n choose j) (q - 1) ^ j` is
the volume of a Hamming ball of radius `e`. -/
theorem exists_card_mul_sum_choose_le_pow_mul (C : Finset (ι → α)) (e : ℕ) :
    ∃ w : ι → α, #C * ∑ j ∈ range (e + 1), (Fintype.card ι).choose j * (Fintype.card α - 1) ^ j ≤
      Fintype.card α ^ Fintype.card ι * #{c ∈ C | hammingDist c w ≤ e} := by
  classical
  set V := ∑ j ∈ range (e + 1), (Fintype.card ι).choose j * (Fintype.card α - 1) ^ j
  have hball (x : ι → α) : #{y : ι → α | hammingDist x y ≤ e} = V := by
    rw [card_filter_hammingDist_le_eq_sum]
    exact sum_congr rfl fun j _ =>
      card_filter_hammingDist_eq_choose_mul_pow (β := fun _ => α) (fun _ => rfl) x j
  -- count the pairs `(w, c)` with `c ∈ C` within distance `e` of `w`
  have hcount : ∑ w : ι → α, #{c ∈ C | hammingDist c w ≤ e} = #C * V :=
    calc ∑ w : ι → α, #{c ∈ C | hammingDist c w ≤ e}
        = ∑ c ∈ C, #{w : ι → α | hammingDist c w ≤ e} := by
          simp only [card_filter]
          exact sum_comm
      _ = ∑ _c ∈ C, V := sum_congr rfl fun c _ => hball c
      _ = #C * V := by rw [sum_const, smul_eq_mul]
  have hsum : ∑ _w : ι → α, #C * V ≤
      ∑ w : ι → α, Fintype.card α ^ Fintype.card ι * #{c ∈ C | hammingDist c w ≤ e} := by
    rw [sum_const, card_univ, Fintype.card_fun, smul_eq_mul, ← mul_sum, hcount]
  obtain ⟨w, -, hw⟩ := exists_le_of_sum_le univ_nonempty hsum
  exact ⟨w, hw⟩

/-- **The Elias–Bassalygo bound**, finite form [Bassalygo1965], [GuruswamiRudraSudan2019,
Section 8.1]: a code `C` of length `n` and minimum distance at least `d` over `q` letters
satisfies `|C| V ((q - 1) (n - e) ^ 2 + e ^ 2 - (q - 1) n (n - d)) ≤ q ^ n (q - 1) n d` for every
radius `e` with `q e ≤ (q - 1) n`, where `V = ∑_{j ≤ e} (n choose j) (q - 1) ^ j` is the volume of
a Hamming ball of radius `e`. -/
theorem card_mul_sum_choose_mul_le {C : Finset (ι → α)} {d : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α))) {e : ℕ}
    (he : Fintype.card α * e ≤ (Fintype.card α - 1) * Fintype.card ι) :
    #C * (∑ j ∈ range (e + 1), (Fintype.card ι).choose j * (Fintype.card α - 1) ^ j) *
        ((Fintype.card α - 1) * (Fintype.card ι - e) ^ 2 + e ^ 2 -
          (Fintype.card α - 1) * Fintype.card ι * (Fintype.card ι - d)) ≤
      Fintype.card α ^ Fintype.card ι * ((Fintype.card α - 1) * Fintype.card ι * d) := by
  obtain ⟨w, hw⟩ := exists_card_mul_sum_choose_le_pow_mul C e
  calc _ ≤ Fintype.card α ^ Fintype.card ι * #{c ∈ C | hammingDist c w ≤ e} *
        ((Fintype.card α - 1) * (Fintype.card ι - e) ^ 2 + e ^ 2 -
          (Fintype.card α - 1) * Fintype.card ι * (Fintype.card ι - d)) :=
        Nat.mul_le_mul_right _ hw
    _ ≤ _ := by
        rw [mul_assoc]
        exact Nat.mul_le_mul_left _ (card_filter_hammingDist_le_mul_le_of_mul_le hd w he)

/-- **The Elias–Bassalygo bound**, finite form below the q-ary Johnson radius [Bassalygo1965],
[GuruswamiRudraSudan2019, Section 8.1]: if `q e ≤ (q - 1) n` and
`(q - 1) n (n - d) < (q - 1) (n - e) ^ 2 + e ^ 2`, a code `C` of length `n` and minimum distance at
least `d` over `q` letters satisfies `|C| V ≤ q ^ n (q - 1) n d`, where
`V = ∑_{j ≤ e} (n choose j) (q - 1) ^ j` is the volume of a Hamming ball of radius `e`. -/
theorem card_mul_sum_choose_le {C : Finset (ι → α)} {d e : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α)))
    (he : Fintype.card α * e ≤ (Fintype.card α - 1) * Fintype.card ι)
    (h : (Fintype.card α - 1) * Fintype.card ι * (Fintype.card ι - d) <
      (Fintype.card α - 1) * (Fintype.card ι - e) ^ 2 + e ^ 2) :
    #C * ∑ j ∈ range (e + 1), (Fintype.card ι).choose j * (Fintype.card α - 1) ^ j ≤
      Fintype.card α ^ Fintype.card ι * ((Fintype.card α - 1) * Fintype.card ι * d) := by
  obtain ⟨w, hw⟩ := exists_card_mul_sum_choose_le_pow_mul C e
  exact hw.trans (Nat.mul_le_mul_left _ (card_filter_hammingDist_le_le_of_mul_le hd he h w))

end Finite

/-! ### Finite and asymptotic rate bounds -/

section Rate

open Filter

variable {ι α : Type*}

/-- **Finite Elias–Bassalygo rate bound** [Bassalygo1965] (locator unverified),
[GuruswamiRudraSudan2019] (locator unverified): for a code `C` of length `n ≥ 1` and minimum
distance at least `d ≤ n` over an alphabet of `q ≥ 2` letters, any integer radius `e` strictly below
the `q`-ary Johnson radius (`e / n < J_q(d / n)`) satisfies
`rate C ≤ 1 - H_q(e / n) / log q + log_q ((q - 1) * n * d * (n + 1)) / n`. -/
theorem rate_le_of_lt_johnsonRadius [Fintype ι] [Nonempty ι] [Fintype α] [DecidableEq α]
    (hq : 2 ≤ Fintype.card α) {C : Finset (ι → α)} {d e : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α))) (hdn : d ≤ Fintype.card ι)
    (he : (e : ℝ) / Fintype.card ι <
      johnsonRadius (Fintype.card α) ((d : ℝ) / Fintype.card ι)) :
    rate (C : Set (ι → α)) ≤
      1 - Real.qaryEntropy (Fintype.card α) ((e : ℝ) / Fintype.card ι) /
          Real.log (Fintype.card α) +
        Real.logb (Fintype.card α)
            (((Fintype.card α : ℝ) - 1) * Fintype.card ι * d * (Fintype.card ι + 1)) /
          Fintype.card ι := by
  set n : ℕ := Fintype.card ι
  set q : ℕ := Fintype.card α
  have hn0 : 0 < n := Fintype.card_pos
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  have hqR : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hlogq : 0 < Real.log q := Real.log_pos hqR
  have hhyp := mul_le_sub_one_mul_and_lt_of_lt_johnsonRadius hq hn0 hdn he
  have hen : e ≤ n :=
    Nat.le_of_mul_le_mul_left (hhyp.1.trans (Nat.mul_le_mul_right n (Nat.sub_le q 1))) (by omega)
  have hd0 : 0 < d := by
    by_contra hd0'
    obtain rfl : d = 0 := by omega
    have hzero : johnsonRadius q (((0 : ℕ) : ℝ) / n) = 0 := by simp
    rw [hzero] at he
    have : (0 : ℝ) ≤ ((e : ℕ) : ℝ) / n := by positivity
    linarith
  rcases Nat.eq_zero_or_pos #C with hC0 | hCpos
  · have hrate0 : rate (C : Set (ι → α)) = 0 := by simp [rate, hC0]
    rw [hrate0]
    have h1 : 0 ≤ 1 - Real.qaryEntropy q ((e : ℝ) / n) / Real.log q := by
      rw [sub_nonneg, div_le_one hlogq]
      exact qaryEntropy_le_log hq (by positivity) ((div_le_one hnR).2 (by exact_mod_cast hen))
    have hfac : 1 ≤ ((q : ℝ) - 1) * n * d * (n + 1) := by
      have hqR2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
      have hq1 : (1 : ℝ) ≤ (q : ℝ) - 1 := by linarith
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
      have hn2 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
      have h12 : 1 ≤ ((q : ℝ) - 1) * n := one_le_mul_of_one_le_of_one_le hq1 hn1
      have h123 : 1 ≤ ((q : ℝ) - 1) * n * d := one_le_mul_of_one_le_of_one_le h12 hd1
      exact one_le_mul_of_one_le_of_one_le h123 hn2
    have hlog_nn : 0 ≤ Real.logb q (((q : ℝ) - 1) * n * d * (n + 1)) / n :=
      div_nonneg (Real.logb_nonneg hqR hfac) hnR.le
    linarith
  have : Nonempty α := Fintype.card_pos_iff.1 (by omega)
  have heb := card_mul_sum_choose_le hd hhyp.1 hhyp.2
  set V : ℕ := ∑ j ∈ range (e + 1), n.choose j * (q - 1) ^ j
  have hV_term : ((n.choose e : ℝ) * ((q : ℝ) - 1) ^ e) ≤ (V : ℝ) := by
    have hsub : n.choose e * (q - 1) ^ e ≤ V :=
      Finset.single_le_sum (f := fun j => n.choose j * (q - 1) ^ j)
        (fun _ _ => Nat.zero_le _) (mem_range.2 (Nat.lt_succ_self e))
    have hcast : ((n.choose e * (q - 1) ^ e : ℕ) : ℝ) ≤ (V : ℝ) := by exact_mod_cast hsub
    push_cast [Nat.cast_sub (by omega : 1 ≤ q)] at hcast
    exact hcast
  have hvol : Real.exp (n * Real.qaryEntropy q ((e : ℝ) / n)) ≤ (n + 1 : ℝ) * V :=
    (exp_mul_qaryEntropy_le_succ_mul_choose_mul_pow hq hen).trans
      (mul_le_mul_of_nonneg_left hV_term (by positivity))
  have hcomb : (#C : ℝ) * Real.exp (n * Real.qaryEntropy q ((e : ℝ) / n)) ≤
      (q : ℝ) ^ n * (((q : ℝ) - 1) * n * d * (n + 1)) := by
    have hebR : ((#C * V : ℕ) : ℝ) ≤ ((q ^ n * ((q - 1) * n * d) : ℕ) : ℝ) := by
      exact_mod_cast heb
    push_cast [Nat.cast_sub (by omega : 1 ≤ q)] at hebR
    calc (#C : ℝ) * Real.exp (n * Real.qaryEntropy q ((e : ℝ) / n))
        ≤ (#C : ℝ) * ((n + 1 : ℝ) * V) :=
          mul_le_mul_of_nonneg_left hvol (Nat.cast_nonneg _)
      _ = ((#C : ℝ) * V) * (n + 1 : ℝ) := by ring
      _ ≤ ((q : ℝ) ^ n * (((q : ℝ) - 1) * n * d)) * (n + 1 : ℝ) :=
          mul_le_mul_of_nonneg_right hebR (by positivity)
      _ = (q : ℝ) ^ n * (((q : ℝ) - 1) * n * d * (n + 1)) := by ring
  have hCR : (0 : ℝ) < #C := Nat.cast_pos.2 hCpos
  have hqR2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hlog :
      Real.logb q (#C : ℝ) +
          (n : ℝ) * Real.qaryEntropy q ((e : ℝ) / n) / Real.log q ≤
        n + Real.logb q (((q : ℝ) - 1) * n * d * (n + 1)) := by
    have h1 := Real.logb_le_logb_of_le hqR (by positivity) hcomb
    rw [Real.logb_mul hCR.ne' (Real.exp_pos _).ne',
      Real.logb_mul (pow_ne_zero n (by positivity)) (by positivity),
      Real.logb_self_pow (zero_lt_one.trans hqR) hqR.ne'] at h1
    have hexp : Real.logb q (Real.exp (n * Real.qaryEntropy q ((e : ℝ) / n))) =
        (n : ℝ) * Real.qaryEntropy q ((e : ℝ) / n) / Real.log q := by
      rw [Real.logb, Real.log_exp]
    linarith [h1, hexp]
  have hrate_eq : rate (C : Set (ι → α)) = Real.logb q (#C : ℝ) / n := by
    simp only [rate, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    rfl
  rw [hrate_eq]
  have hdiv := div_le_div_of_nonneg_right hlog hnR.le
  rw [add_div, add_div, div_self hnR.ne'] at hdiv
  have hent_div : (n : ℝ) * Real.qaryEntropy q ((e : ℝ) / n) / Real.log q / n =
      Real.qaryEntropy q ((e : ℝ) / n) / Real.log q := by
    field_simp [hnR.ne']
  rw [hent_div] at hdiv
  linarith

/-- **The asymptotic Elias–Bassalygo bound** [Bassalygo1965] (locator unverified),
[GuruswamiRudraSudan2019] (locator unverified): for any family of codes `C s` over `q ≥ 2` letters
whose block lengths `n_s = |ιs s|` tend to infinity along a filter `l` and whose relative minimum
distances are at least `δ` (`0 ≤ δ ≤ 1 - 1 / q`),
`rate (C s) ≤ 1 - H_q(J_q(δ)) / log q + ε` holds eventually along `l` for every `ε > 0`. -/
theorem eventually_rate_le_one_sub_qaryEntropy_johnsonRadius
    {σ : Type*} {ιs : σ → Type*} [∀ s, Fintype (ιs s)] [Fintype α] [DecidableEq α] [Nontrivial α]
    {l : Filter σ} {C : ∀ s, Finset (ιs s → α)} {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : (Fintype.card α : ℝ) * δ ≤ Fintype.card α - 1)
    (hC : ∀ s, ∀ x ∈ C s, ∀ y ∈ C s, x ≠ y → δ * Fintype.card (ιs s) ≤ hammingDist x y)
    (hn : Tendsto (fun s => Fintype.card (ιs s)) l atTop) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in l, rate (C s : Set (ιs s → α)) ≤
      1 - Real.qaryEntropy (Fintype.card α) (johnsonRadius (Fintype.card α) δ) /
        Real.log (Fintype.card α) + ε := by
  classical
  set q : ℕ := Fintype.card α
  have hq : 2 ≤ q := Fintype.one_lt_card
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hlogq : 0 < Real.log q := Real.log_pos hqR
  have hnR : Tendsto (fun s => (Fintype.card (ιs s) : ℝ)) l atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  rcases hδ0.eq_or_lt with rfl | hδpos
  · filter_upwards [hn.eventually_ge_atTop 1] with s hs1
    have hnpos : (0 : ℝ) < Fintype.card (ιs s) := Nat.cast_pos.2 hs1
    have htriv : rate (C s : Set (ιs s → α)) ≤ 1 := by
      simp only [rate, Nat.card_coe_set_eq, Set.ncard_coe_finset]
      rcases Nat.eq_zero_or_pos #(C s) with h0 | h0
      · simp [h0]
      have hle : (#(C s) : ℝ) ≤ (q : ℝ) ^ Fintype.card (ιs s) := by
        have := card_le_univ (C s)
        rw [Fintype.card_fun] at this
        exact_mod_cast this
      calc Real.logb q #(C s) / Fintype.card (ιs s)
          ≤ Real.logb q ((q : ℝ) ^ Fintype.card (ιs s)) / Fintype.card (ιs s) :=
            div_le_div_of_nonneg_right (Real.logb_le_logb_of_le hqR (by exact_mod_cast h0) hle)
              hnpos.le
        _ = 1 := by
            rw [Real.logb_self_pow (zero_lt_one.trans hqR) hqR.ne', div_self hnpos.ne']
    simpa [johnsonRadius_zero_right] using htriv.trans (by linarith)
  have hδθ : δ ≤ 1 - 1 / (q : ℝ) := by
    have hq0 : (0 : ℝ) < q := by positivity
    rw [le_sub_iff_add_le, ← mul_le_mul_iff_of_pos_left hq0]
    calc (q : ℝ) * (δ + 1 / q) = q * δ + 1 := by field_simp [hq0.ne']
      _ ≤ q := by linarith
      _ = q * 1 := by ring
  set J : ℝ := johnsonRadius q δ
  have hJpos : 0 < J := by
    have hq1 : 0 < (q : ℝ) - 1 := by linarith
    have hθ : 0 < 1 - 1 / (q : ℝ) := sub_pos.2 ((div_lt_one (zero_lt_one.trans hqR)).2 hqR)
    have hlt : 1 - (q : ℝ) * δ / ((q : ℝ) - 1) < 1 := by
      have : 0 < (q : ℝ) * δ / ((q : ℝ) - 1) := by positivity
      linarith
    have hsqrt : Real.sqrt (1 - (q : ℝ) * δ / ((q : ℝ) - 1)) < 1 := by
      rcases le_or_gt (1 - (q : ℝ) * δ / ((q : ℝ) - 1)) 0 with hle | hpos
      · rw [Real.sqrt_eq_zero_of_nonpos hle]
        exact zero_lt_one
      · have hsq : Real.sqrt (1 - (q : ℝ) * δ / ((q : ℝ) - 1)) ^ 2 =
            1 - (q : ℝ) * δ / ((q : ℝ) - 1) := Real.sq_sqrt hpos.le
        have hnn : 0 ≤ Real.sqrt (1 - (q : ℝ) * δ / ((q : ℝ) - 1)) := Real.sqrt_nonneg _
        nlinarith
    exact mul_pos hθ (sub_pos.2 hsqrt)
  -- Use continuity of `Real.qaryEntropy q` at `J` to keep `H_q(e/n)` within `ε / 2 * log q`.
  have hcont := (Real.qaryEntropy_continuous (q := q)).tendsto J
  rw [Metric.tendsto_nhds_nhds] at hcont
  obtain ⟨η₀, hη₀pos, hη₀⟩ := hcont (ε / 2 * Real.log q) (by positivity)
  set η : ℝ := min (η₀ / 2) J
  have hηpos : 0 < η := lt_min (half_pos hη₀pos) hJpos
  have hη_le_η₀ : η < η₀ := (min_le_left _ _).trans_lt (half_lt_self hη₀pos)
  have hη_le_J : η ≤ J := min_le_right _ _
  have h_n1 : ∀ᶠ s in l, 1 ≤ Fintype.card (ιs s) := hn.eventually_ge_atTop 1
  have h_nη : ∀ᶠ s in l, 2 / η ≤ (Fintype.card (ιs s) : ℝ) := hnR.eventually_ge_atTop _
  have h_nconst :
      ∀ᶠ s in l, Real.log (2 * q) ≤ ε / 4 * Real.log q * (Fintype.card (ιs s) : ℝ) :=
    (hnR.eventually_ge_atTop (Real.log (2 * q) / (ε / 4 * Real.log q))).mono fun s hs => by
      have h1 : Real.log (2 * q) ≤ (Fintype.card (ιs s) : ℝ) * (ε / 4 * Real.log q) :=
        (div_le_iff₀ (by positivity)).1 hs
      linarith
  have h_nlog :
      ∀ᶠ s in l, Real.log (Fintype.card (ιs s)) ≤
        ε / 12 * Real.log q * (Fintype.card (ιs s) : ℝ) := by
    have := Real.isLittleO_log_id_atTop.bound (c := ε / 12 * Real.log q) (by positivity)
    filter_upwards [hnR.eventually this, hnR.eventually_ge_atTop 1] with s hs hs1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_nonneg (Real.log_nonneg hs1),
      abs_of_nonneg (by linarith)] at hs
    exact hs
  filter_upwards [h_n1, h_nη, h_nconst, h_nlog] with s hs1 hsη hsconst hslog
  have : Nonempty (ιs s) := Fintype.card_pos_iff.1 hs1
  set n : ℕ := Fintype.card (ιs s)
  have hn0 : 0 < n := hs1
  have hnR' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  set d : ℕ := ⌈δ * n⌉₊
  have hδlt1 : δ < 1 := by
    have : 0 < 1 / (q : ℝ) := by positivity
    linarith
  have hdn : d ≤ n := Nat.ceil_le.2 (by nlinarith)
  have hdmin : (d : ℕ∞) ≤ minDist (C s : Set (ιs s → α)) := by
    rw [le_minDist_iff]
    intro x hx y hy hxy
    exact_mod_cast Nat.ceil_le.2 (hC s x hx y hy hxy)
  have hδd : δ ≤ (d : ℝ) / n := (le_div_iff₀ hnR').2 (Nat.le_ceil _)
  have hJd : J ≤ johnsonRadius q ((d : ℝ) / n) := johnsonRadius_mono_right hqR hδd
  set e : ℕ := ⌊(J - η / 2) * n⌋₊
  have hJη0 : 0 ≤ J - η / 2 := by linarith
  have he_le : (e : ℝ) ≤ (J - η / 2) * n := Nat.floor_le (mul_nonneg hJη0 hnR'.le)
  have he_lt : (J - η / 2) * n - 1 < e := sub_lt_iff_lt_add.2 (Nat.lt_floor_add_one _)
  have h1_le_halfηn : 1 ≤ η / 2 * n := by
    have := mul_le_mul_of_nonneg_left hsη (by positivity : 0 ≤ η / 2)
    have hsimp : η / 2 * (2 / η) = 1 := by field_simp [hηpos.ne']
    linarith
  have he_lower : J - η ≤ (e : ℝ) / n := by
    rw [le_div_iff₀ hnR']
    linarith
  have he_upper : (e : ℝ) / n ≤ J - η / 2 := (div_le_iff₀ hnR').2 he_le
  have he_radius : (e : ℝ) / n < johnsonRadius q ((d : ℝ) / n) := by linarith
  have hfinite := rate_le_of_lt_johnsonRadius (C := C s) hq hdmin hdn he_radius
  have hdistJ : dist ((e : ℝ) / n) J < η₀ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hent : |Real.qaryEntropy q ((e : ℝ) / n) - Real.qaryEntropy q J| < ε / 2 * Real.log q := by
    simpa only [Real.dist_eq] using hη₀ hdistJ
  have hent' :
      1 - Real.qaryEntropy q ((e : ℝ) / n) / Real.log q ≤
        1 - Real.qaryEntropy q J / Real.log q + ε / 2 := by
    have hlt : Real.qaryEntropy q J - Real.qaryEntropy q ((e : ℝ) / n) ≤ ε / 2 * Real.log q := by
      linarith [(abs_lt.1 hent).1]
    have hdiv := div_le_div_of_nonneg_right hlt hlogq.le
    rw [mul_div_cancel_right₀ _ hlogq.ne', sub_div] at hdiv
    linarith
  have hpoly :
      ((q : ℝ) - 1) * n * d * (n + 1) ≤ (2 * q) * (n : ℝ) ^ 3 := by
    have hq1_le : (q : ℝ) - 1 ≤ q := by linarith
    have hd_le : (d : ℝ) ≤ n := by exact_mod_cast hdn
    have hn1_le : (n : ℝ) + 1 ≤ 2 * n := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn0
      linarith
    have hq1_nn : 0 ≤ (q : ℝ) - 1 := by
      have : (2 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    calc ((q : ℝ) - 1) * n * d * (n + 1)
        ≤ (q : ℝ) * n * n * (2 * n) := by gcongr
      _ = (2 * q) * (n : ℝ) ^ 3 := by ring
  have hpoly_pos : 0 < ((q : ℝ) - 1) * n * d * (n + 1) := by
    have hd0 : 0 < d := by
      rw [Nat.ceil_pos]
      exact mul_pos hδpos hnR'
    have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
      have : (2 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    positivity
  have htail :
      Real.logb q (((q : ℝ) - 1) * n * d * (n + 1)) / n ≤ ε / 2 := by
    have hlog_le : Real.logb q (((q : ℝ) - 1) * n * d * (n + 1)) ≤
        Real.logb q ((2 * q) * (n : ℝ) ^ 3) :=
      Real.logb_le_logb_of_le hqR hpoly_pos hpoly
    have hlog_eq : Real.logb q ((2 * q) * (n : ℝ) ^ 3) =
        (Real.log (2 * q) + 3 * Real.log n) / Real.log q := by
      rw [Real.logb, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      ring
    have hnum : Real.log (2 * q) + 3 * Real.log n ≤ ε / 2 * Real.log q * n := by linarith
    calc Real.logb q (((q : ℝ) - 1) * n * d * (n + 1)) / n
        ≤ ((Real.log (2 * q) + 3 * Real.log n) / Real.log q) / n := by
          gcongr
          linarith [hlog_le, hlog_eq]
      _ ≤ (ε / 2 * Real.log q * n / Real.log q) / n := by gcongr
      _ = ε / 2 := by field_simp [hlogq.ne', hnR'.ne']
  dsimp only [q, n] at hent' htail ⊢
  linarith

end Rate

end Cslib.Code
