/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.TargetCollisionResistant
public import CslibFrontier.Foundations.Data.BitString.List.Operations
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString.ReplaceRow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PadicVal
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Extension
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Foundations.Data.BitString.List.Rows
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Uniform

/-!
# Shoup XOR-masking composition (`[Shoup2000]`, `[HHRVW2020]` Lemma 5.7)

This module formalizes Shoup's XOR-masking composition theorem (`[Shoup2000]`; restated as
`[HHRVW2020]`, Section 5.1.4, Lemma 5.7, pp. 29–30), stretching a target collision-resistant
shrinking compression function
$H_K : \{0, 1\}^{b + s} \to \{0, 1\}^b$ ($s \ge 1$) to $t$ sequential steps with a single shared
subkey $K$ and $\lfloor \log_2 t \rfloor + 1$ public $b$-bit XOR masks (`O(|K| + b log t)` total
key bits):

1. **XOR-masked sequential cascade (`shoupState`, `shoupCascade`,
   `exists_shoupCascade_step_collision`)**: iterates `i = 1, ..., t` with mask
   `BitString.listRow b (padicValNat 2 i) masks` and `s`-bit chunk `shoupChunk b s i x`,
   extracting an in-range step collision (`1 ≤ i ≤ t`) from any fixed-length message collision
   when `b ≤ L ≤ b + t * s`.
2. **Mask-reconstruction bijection (`shoupPackMasks`, `shoupStepInput_shoupPackMasks`,
   `uniformList_map_shoupPackMasks`, `computableInPolyTime_shoupPackMasks`)**: reconstructs the
   XOR masks via one downward scan using binary trailing-zero (`padicValNat 2`) last-occurrence
   breakpoints, proving both that step `iStar` receives
   `listRow b (padicValNat 2 iStar) T ++ shoupChunk b s iStar x` and that `T ↦ shoupPackMasks ... T`
   preserves `BitString.uniformList (shoupMasksLen b t)` via an explicit left-inverse.
3. **Target collision-resistant composition (`shoupComposeKeyLen`, `shoupComposeEval`,
   `shoupComposeChoose`, `shoupComposeFindWith`, `shoupComposeAdversary`,
   `targetCollisionResistantOn_shoupCompose`)**: packages `[Shoup2000]` / `[HHRVW2020]` Lemma 5.7
   with `O(|y| log t)` key length (`shoupComposeKeyLen_le`) and explicit multiplicative loss
   `dyadicSize (t n)`, exposing the pre-key and post-key reduction stages so downstream candidate
   concatenations can reuse them directly.

## Main definitions

* `Cslib.Crypto.shoupMaskCount`, `Cslib.Crypto.shoupMasksLen`: number and total bit length of the
  $\lfloor \log_2 t \rfloor + 1$ XOR masks.
* `Cslib.Crypto.shoupChunk`, `Cslib.Crypto.shoupStepInput`, `Cslib.Crypto.shoupState`,
  `Cslib.Crypto.shoupCascade`: Shoup's $\nu_2(i)$-indexed XOR-masked sequential cascade.
* `Cslib.Crypto.shoupPackMasks`: polynomial-time mask-reconstruction algorithm (`[Shoup2000]`;
  `[HHRVW2020]`, Section 5.1.4, Lemma 5.7, pp. 29–30).
* `Cslib.Crypto.shoupComposeKeyLen`, `Cslib.Crypto.shoupComposeEval`,
  `Cslib.Crypto.shoupComposeChoose`, `Cslib.Crypto.shoupComposeFindWith`,
  `Cslib.Crypto.shoupComposeAdversary`: standalone `[HHRVW2020]` Lemma 5.7 construction and
  reduction stages.

## Main results

* `Cslib.Crypto.exists_shoupCascade_step_collision`: deterministic step-collision extractor from a
  distinct equal-length message collision on `shoupCascade`.
* `Cslib.Crypto.shoupStepInput_shoupPackMasks`: planted target input at step `iStar`.
* `Cslib.Crypto.uniformList_map_shoupPackMasks`: exact uniform distribution of constructed masks.
* `Cslib.Crypto.shoupComposeKeyLen_le`: `keyLen n + (Nat.log 2 (t n) + 1) * b n ≤
  (Nat.log 2 (t n) + 2) * keyLen n` when `b n ≤ keyLen n` (`O(|y| log t)` bound).
* `Cslib.Crypto.succProbability_targetCollisionGame_shoupCompose_le`,
  `Cslib.Crypto.targetCollisionResistantOn_shoupCompose`: `[Shoup2000]` / `[HHRVW2020]`
  Lemma 5.7 concrete and asymptotic security theorems with loss `dyadicSize (t n)`.

## References

* [V. Shoup, *A Composition Theorem for Universal One-Way Hash Functions*, EUROCRYPT 2000,
  LNCS 1807, pp. 445–452][Shoup2000]
* [I. Haitner, T. Holenstein, O. Reingold, S. Vadhan, H. Wee, *Inaccessible Entropy II: IE
  Functions and Universal One-Way Hashing*, Section 5.1.4, Lemma 5.7, pp. 29–30][HHRVW2020]
-/

public section

namespace Cslib.Crypto

open Cslib.Probability Finset ProbComp Turing.MultiTapeTM
open scoped BigOperators ENNReal NNReal

/-! ### 2-adic valuation combinatorics (`[Shoup2000]`; `[HHRVW2020]`, Lemma 5.7, pp. 29–30) -/

private theorem two_prime_fact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem pow_mul_div_padicValNat_odd {m v : ℕ} (hm : 1 ≤ m) (hv : padicValNat 2 m = v) :
    2 ^ v * (m / 2 ^ v) = m ∧ (m / 2 ^ v) % 2 = 1 := by
  have := two_prime_fact
  have hv_mult : multiplicity 2 m = v := Nat.padicValNat_def.symm.trans hv
  have hm_eq : 2 ^ v * (m / 2 ^ v) = m := Nat.mul_div_cancel' (hv_mult ▸ pow_multiplicity_dvd 2 m)
  have hnd : ¬ 2 ^ (v + 1) ∣ m := hv_mult ▸ pow_succ_multiplicity_not_dvd (p := 2) (by omega)
  rw [← hm_eq, pow_succ] at hnd
  have h2 : ¬ 2 ∣ m / 2 ^ v := fun h => hnd (mul_dvd_mul_left (2 ^ v) h)
  exact ⟨hm_eq, by omega⟩

private theorem shoup_fact1 {A B : ℕ} (hA : 1 ≤ A) (hAB : A < B)
    (hv : padicValNat 2 A = padicValNat 2 B) :
    ∃ C, A < C ∧ C < B ∧ padicValNat 2 A < padicValNat 2 C := by
  have := two_prime_fact
  set v := padicValNat 2 A
  obtain ⟨hA_eq, ha_odd⟩ := pow_mul_div_padicValNat_odd hA (rfl : padicValNat 2 A = v)
  obtain ⟨hB_eq, hb_odd⟩ := pow_mul_div_padicValNat_odd (by omega) hv.symm
  set a := A / 2 ^ v
  set b := B / 2 ^ v
  have hpow : 0 < 2 ^ v := Nat.two_pow_pos v
  have hab : a < b := Nat.lt_of_mul_lt_mul_left (by rw [hA_eq, hB_eq]; exact hAB)
  refine ⟨2 ^ v * (a + 1),
    by rw [← hA_eq]; exact Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self _) hpow,
    by rw [← hB_eq]; exact Nat.mul_lt_mul_of_pos_left (by omega) hpow, ?_⟩
  rw [Nat.padicValNat_def]
  exact (multiplicity_dvd_iff_le (by positivity)).mp
    (pow_succ 2 v ▸ mul_dvd_mul_left (2 ^ v) (show 2 ∣ a + 1 by omega))

private theorem shoup_fact2 {A B ν : ℕ} (_hA : 1 ≤ A) (hAB : A < B)
    (hν : ν < min (padicValNat 2 A) (padicValNat 2 B)) :
    ∃ C, A < C ∧ C < B ∧ padicValNat 2 C = ν := by
  have := two_prime_fact
  obtain ⟨qa, hqa⟩ := (multiplicity_dvd_iff_le (by omega)).mpr
    (Nat.padicValNat_def (p := 2) ▸ (Nat.lt_min.mp hν).1)
  obtain ⟨qb, hqb⟩ := (multiplicity_dvd_iff_le (by omega)).mpr
    (Nat.padicValNat_def (p := 2) ▸ (Nat.lt_min.mp hν).2)
  have hq : qa < qb := Nat.lt_of_mul_lt_mul_left (hqa.symm ▸ hqb.symm ▸ hAB)
  have hstep : A + 2 ^ (ν + 1) ≤ B := by
    calc A + 2 ^ (ν + 1) = 2 ^ (ν + 1) * (qa + 1) := by rw [hqa, mul_add, mul_one]
      _ ≤ 2 ^ (ν + 1) * qb := Nat.mul_le_mul_left _ hq
      _ = B := hqb.symm
  have hpow : 0 < 2 ^ ν := Nat.two_pow_pos ν
  have h2pow : 2 ^ (ν + 1) = 2 * 2 ^ ν := pow_succ' 2 ν
  refine ⟨A + 2 ^ ν, by omega, by omega, ?_⟩
  rw [show A + 2 ^ ν = 2 ^ ν * (2 * qa + 1) by rw [hqa, pow_succ]; ring,
    Nat.padicValNat_def, Nat.multiplicity_mul hpow.ne' (by omega),
    Nat.multiplicity_prime_pow, multiplicity_eq_zero_of_not_dvd (by omega), add_zero]

private def shoupIsLastOcc (iStar k : ℕ) : Bool :=
  decide (1 ≤ k ∧ k ≤ iStar ∧ iStar < k + 2 ^ (padicValNat 2 k + 1))

private def shoupLastOcc (iStar j : ℕ) : ℕ :=
  let q := iStar / 2 ^ j
  2 ^ j * (if q % 2 = 1 then q else q - 1)

private theorem shoupIsLastOcc_self {iStar : ℕ} (hi : 1 ≤ iStar) :
    shoupIsLastOcc iStar iStar = true := by
  simp only [shoupIsLastOcc, decide_eq_true_eq]
  exact ⟨hi, le_rfl, Nat.lt_add_of_pos_right (Nat.two_pow_pos _)⟩

private theorem shoupIsLastOcc_unique {iStar k m : ℕ} (hk : shoupIsLastOcc iStar k = true)
    (hkm : k ≤ m) (hmi : m ≤ iStar) (hv : padicValNat 2 m = padicValNat 2 k) : m = k := by
  simp only [shoupIsLastOcc, decide_eq_true_eq] at hk
  set v := padicValNat 2 k
  obtain ⟨hk_eq, ha_odd⟩ := pow_mul_div_padicValNat_odd hk.1 (rfl : padicValNat 2 k = v)
  obtain ⟨hm_eq, hb_odd⟩ := pow_mul_div_padicValNat_odd (by omega) hv
  set a := k / 2 ^ v; set b := m / 2 ^ v
  have hle : a ≤ b := Nat.le_of_mul_le_mul_left
    (by change 2 ^ v * a ≤ 2 ^ v * b; rw [hk_eq, hm_eq]; exact hkm) (Nat.two_pow_pos v)
  have hlt : b < a + 2 := Nat.lt_of_mul_lt_mul_left (a := 2 ^ v) <| by
    have : k + 2 ^ (v + 1) = 2 ^ v * (a + 2) := by rw [← hk_eq, pow_succ]; ring
    change 2 ^ v * b < _; rw [hm_eq]; omega
  rw [← hm_eq, ← hk_eq, show b = a by omega]

private theorem shoupLastOcc_ge {iStar k : ℕ} (hk : 1 ≤ k) (hki : k ≤ iStar) :
    k ≤ shoupLastOcc iStar (padicValNat 2 k) := by
  obtain ⟨hk_eq, hka_odd⟩ := pow_mul_div_padicValNat_odd hk rfl
  have hkq : k / 2 ^ padicValNat 2 k ≤ iStar / 2 ^ padicValNat 2 k := Nat.div_le_div_right hki
  unfold shoupLastOcc
  calc k = 2 ^ padicValNat 2 k * (k / 2 ^ padicValNat 2 k) := hk_eq.symm
    _ ≤ _ := Nat.mul_le_mul_left _ (by split_ifs <;> omega)

private theorem shoupLastOcc_le {iStar j : ℕ} : shoupLastOcc iStar j ≤ iStar := by
  dsimp only [shoupLastOcc]
  split_ifs
  · exact Nat.mul_div_le iStar (2 ^ j)
  · exact (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans (Nat.mul_div_le iStar (2 ^ j))

private theorem shoupLastOcc_oddPart {iStar j : ℕ} (hi : 1 ≤ iStar)
    (hj : j ≤ Nat.log 2 iStar) :
    let q := iStar / 2 ^ j
    let oddQ := if q % 2 = 1 then q else q - 1
    0 < 2 ^ j ∧ 1 ≤ oddQ ∧ oddQ % 2 = 1 := by
  have hpow : 0 < 2 ^ j := Nat.two_pow_pos j
  have hq : 1 ≤ iStar / 2 ^ j := Nat.div_pos
    ((Nat.pow_le_pow_right (by decide) hj).trans (Nat.pow_log_le_self 2 (by omega))) hpow
  exact ⟨hpow, by split_ifs <;> omega, by split_ifs <;> omega⟩

private theorem padicValNat_two_shoupLastOcc {iStar j : ℕ} (hi : 1 ≤ iStar)
    (hj : j ≤ Nat.log 2 iStar) : padicValNat 2 (shoupLastOcc iStar j) = j := by
  have := two_prime_fact
  obtain ⟨hpow, hodd_pos, hodd_mod⟩ := shoupLastOcc_oddPart hi hj
  dsimp only [shoupLastOcc]
  rw [Nat.padicValNat_def, Nat.multiplicity_mul hpow.ne' (by omega),
    Nat.multiplicity_prime_pow, multiplicity_eq_zero_of_not_dvd (by omega), add_zero]

private theorem shoupIsLastOcc_shoupLastOcc {iStar j : ℕ} (hi : 1 ≤ iStar)
    (hj : j ≤ Nat.log 2 iStar) : shoupIsLastOcc iStar (shoupLastOcc iStar j) = true := by
  obtain ⟨hpow, hodd_pos, _⟩ := shoupLastOcc_oddPart hi hj
  simp only [shoupIsLastOcc, decide_eq_true_eq, padicValNat_two_shoupLastOcc hi hj]
  refine ⟨Nat.mul_pos hpow hodd_pos, shoupLastOcc_le, ?_⟩
  have hdm := Nat.div_add_mod iStar (2 ^ j)
  have hml := Nat.mod_lt iStar hpow
  have hle : iStar / 2 ^ j + 1 ≤
      (if (iStar / 2 ^ j) % 2 = 1 then iStar / 2 ^ j else iStar / 2 ^ j - 1) + 2 := by
    split_ifs <;> omega
  calc iStar < 2 ^ j * (iStar / 2 ^ j + 1) := by rw [mul_add, mul_one]; omega
    _ ≤ 2 ^ j * _ := Nat.mul_le_mul_left _ hle
    _ = shoupLastOcc iStar j + 2 ^ (j + 1) := by dsimp only [shoupLastOcc]; rw [pow_succ]; ring

private theorem shoupLastOcc_padicValNat_eq {iStar k : ℕ} (hk : shoupIsLastOcc iStar k = true) :
    shoupLastOcc iStar (padicValNat 2 k) = k := by
  have hk' := (decide_eq_true_eq.mp hk)
  exact shoupIsLastOcc_unique hk (shoupLastOcc_ge hk'.1 hk'.2.1) shoupLastOcc_le
    (padicValNat_two_shoupLastOcc (by omega)
      (Nat.padicValNat_def ▸ (multiplicity_le_nat_log k).trans (Nat.log_mono_right hk'.2.1)))

private theorem shoupLastOcc_gt_between {iStar lo hi i : ℕ}
    (hhi_last : shoupIsLastOcc iStar hi = true)
    (hbetween : ∀ m, lo < m → m < hi → shoupIsLastOcc iStar m = false)
    (h1 : 1 ≤ i) (hlo : lo < i) (hhi : i < hi) :
    hi < shoupLastOcc iStar (padicValNat 2 i) := by
  have hhi_info := decide_eq_true_eq.mp hhi_last
  have lastOcc_ge_hi : ∀ m, 1 ≤ m → lo < m → m < hi →
      let q := shoupLastOcc iStar (padicValNat 2 m)
      hi ≤ q ∧ padicValNat 2 q = padicValNat 2 m := by
    intro m hm1 hmlo hmhi
    have hlog : padicValNat 2 m ≤ Nat.log 2 iStar :=
      Nat.padicValNat_def ▸
        (multiplicity_le_nat_log m).trans (Nat.log_mono_right (hmhi.le.trans hhi_info.2.1))
    have hql := shoupIsLastOcc_shoupLastOcc (by omega) hlog
    refine ⟨not_lt.mp fun hlt => ?_, padicValNat_two_shoupLastOcc (by omega) hlog⟩
    have hge : m ≤ shoupLastOcc iStar (padicValNat 2 m) :=
      shoupLastOcc_ge hm1 (hmhi.le.trans hhi_info.2.1)
    have hf := hbetween _ (lt_of_lt_of_le hmlo hge) hlt
    rw [hql] at hf; exact Bool.false_ne_true hf.symm
  obtain ⟨hp_ge, hp_val⟩ := lastOcc_ge_hi i h1 hlo hhi
  refine lt_of_le_of_ne hp_ge fun hpeq => ?_
  have hv_iB : padicValNat 2 i = padicValNat 2 hi := by rw [← hp_val, ← hpeq]
  obtain ⟨C₀, hC₀1, hC₀2, hC₀v⟩ := shoup_fact1 h1 hhi hv_iB
  let S := (Finset.Ioo i hi).filter fun c => padicValNat 2 i < padicValNat 2 c
  obtain ⟨C, hCm, hCmax⟩ := S.exists_max_image (padicValNat 2)
    ⟨C₀, Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨hC₀1, hC₀2⟩, hC₀v⟩⟩
  have ⟨hClt, hCv⟩ := (Finset.mem_filter.mp hCm)
  have ⟨hiC, Chi⟩ := Finset.mem_Ioo.mp hClt
  set D := shoupLastOcc iStar (padicValNat 2 C)
  obtain ⟨hD_ge, hD_val⟩ := lastOcc_ge_hi C (by omega) (hlo.trans hiC) Chi
  have hBD : hi < D := lt_of_le_of_ne hD_ge fun h => by
    change padicValNat 2 D = _ at hD_val
    rw [← h, ← hv_iB] at hD_val; omega
  obtain ⟨E, hCE, hED, hEv⟩ := shoup_fact1 (by omega) (Chi.trans hBD) hD_val.symm
  have hBE : hi < E := not_le.mp fun hle => (eq_or_lt_of_le hle).elim
    (fun h => by rw [h, ← hv_iB] at hEv; omega)
    (fun hlt => by
      have := hCmax E (Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨hiC.trans hCE, hlt⟩,
        hCv.trans hEv⟩)
      omega)
  obtain ⟨F, hEF, hFD, hFv⟩ := shoup_fact2 (by omega) hED
    (lt_min (hv_iB ▸ hCv.trans hEv) (hv_iB ▸ hD_val ▸ hCv))
  have := shoupIsLastOcc_unique hhi_last (hBE.trans hEF).le (hFD.le.trans shoupLastOcc_le) hFv
  omega

@[fun_prop]
private theorem computableInPolyTime_shoupIsLastOcc {γ : Type} {encIn : γ ↪ List Bool}
    {iStar k : γ → ℕ}
    (hi : ComputableInPolyTime iStar encIn encUnary)
    (hk : ComputableInPolyTime k encIn encUnary) :
    ComputableInPolyTime (fun a => shoupIsLastOcc (iStar a) (k a)) encIn encBool := by
  have hlt : ComputableInPolyTime (fun a => decide (iStar a < k a + 2 ^ (padicValNat 2 (k a) + 1)))
      encIn encBool :=
    ComputableInPolyTime.binary_lt' (ComputableInPolyTime.unary_to_binary.comp hi)
      (ComputableInPolyTime.binary_add' (ComputableInPolyTime.unary_to_binary.comp hk)
        (ComputableInPolyTime.binary_two_pow.comp (by fun_prop)))
  refine (by fun_prop : ComputableInPolyTime (fun a =>
    decide (1 ≤ k a) && decide (k a ≤ iStar a) &&
      decide (iStar a < k a + 2 ^ (padicValNat 2 (k a) + 1))) encIn encBool).of_enc_eq fun a => ?_
  exact congrArg encBool (by simp [shoupIsLastOcc, Bool.and_assoc])

/-! ### Mask-count schedule and XOR-masked cascade (`[Shoup2000]`; `[HHRVW2020]` Lemma 5.7) -/

/-- Number `⌊log₂ t⌋ + 1` of `b`-bit XOR masks needed for a `t`-step Shoup cascade. -/
@[expose] def shoupMaskCount (t : ℕ) : ℕ := Nat.log 2 t + 1

/-- Total mask bit length `(⌊log₂ t⌋ + 1) * b` for `t` steps and chaining width `b`. -/
@[expose] def shoupMasksLen (b t : ℕ) : ℕ := shoupMaskCount t * b

@[fun_prop]
theorem computableInPolyTime_shoupMaskCount {γ : Type} {encIn : γ ↪ List Bool}
    {t : γ → ℕ} (ht : ComputableInPolyTime t encIn encUnary) :
    ComputableInPolyTime (fun a => shoupMaskCount (t a)) encIn encUnary := by
  unfold shoupMaskCount; fun_prop

@[fun_prop]
theorem computableInPolyTime_shoupMasksLen {γ : Type} {encIn : γ ↪ List Bool}
    {b t : γ → ℕ} (hb : ComputableInPolyTime b encIn encUnary)
    (ht : ComputableInPolyTime t encIn encUnary) :
    ComputableInPolyTime (fun a => shoupMasksLen (b a) (t a)) encIn encUnary := by
  unfold shoupMasksLen; fun_prop

/-- `s`-bit message chunk for step `i` (`1 ≤ i ≤ t`) after removing the initial `b`-bit block. -/
@[expose] def shoupChunk (b s i : ℕ) (x : List Bool) : List Bool :=
  BitString.listRow s (i - 1) (x.drop b)

@[simp]
theorem length_shoupChunk (b s i : ℕ) (x : List Bool) :
    (shoupChunk b s i x).length = s :=
  BitString.length_listRow _ _ _

/-- Input to `step` at step `i` (`1 ≤ i ≤ t`): `(state ⊕ M_{ν₂(i)}) ++ chunk_i(x)`. -/
@[expose] def shoupStepInput (b s : ℕ) (masks x : List Bool) (i : ℕ) (state : List Bool) :
    List Bool :=
  BitString.listXor b [state, BitString.listRow b (padicValNat 2 i) masks] ++
    shoupChunk b s i x

@[simp]
theorem length_shoupStepInput (b s : ℕ) (masks x : List Bool) (i : ℕ) (state : List Bool) :
    (shoupStepInput b s masks x i state).length = b + s := by
  simp [shoupStepInput]

@[fun_prop]
theorem computableInPolyTime_shoupStepInput {γ : Type} {encIn : γ ↪ List Bool}
    {b s i : γ → ℕ} {masks x state : γ → List Bool}
    (hb : ComputableInPolyTime b encIn encUnary)
    (hs : ComputableInPolyTime s encIn encUnary)
    (hmasks : ComputableInPolyTime masks encIn encBits)
    (hx : ComputableInPolyTime x encIn encBits)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hstate : ComputableInPolyTime state encIn encBits) :
    ComputableInPolyTime
      (fun a => shoupStepInput (b a) (s a) (masks a) (x a) (i a) (state a))
      encIn encBits := by
  have hmaskRow := ComputableInPolyTime.bitsRowWithInput hb
    (ComputableInPolyTime.unary_padicValNat_two.comp hi) hmasks
  have hchunk := ComputableInPolyTime.bitsRowWithInput hs (hi.unary_sub' (.const 1))
    (ComputableInPolyTime.bitsDropWithInput hx hb)
  exact ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsXorWithInput hb
      (ComputableInPolyTime.cons' hstate
        (ComputableInPolyTime.cons' hmaskRow (.const []))))
    hchunk

/-- Chaining value `h_k` after `k` steps of Shoup's cascade under `step` and `masks`. -/
@[expose] def shoupState (b s : ℕ) (step : List Bool → List Bool) (masks x : List Bool) :
    ℕ → List Bool
  | 0 => BitString.listRow b 0 x
  | k + 1 => step (shoupStepInput b s masks x (k + 1) (shoupState b s step masks x k))

/-- Output of the `t`-step Shoup cascade. -/
@[expose] def shoupCascade (b s t : ℕ) (step : List Bool → List Bool)
    (masks x : List Bool) : List Bool :=
  shoupState b s step masks x t

theorem length_shoupState (b s : ℕ) (step : List Bool → List Bool)
    (hstep : ∀ w, w.length = b + s → (step w).length = b)
    (masks x : List Bool) (k : ℕ) :
    (shoupState b s step masks x k).length = b := by
  cases k with
  | zero => simp [shoupState]
  | succ k => exact hstep _ (length_shoupStepInput _ _ _ _ _ _)

theorem length_shoupCascade (b s t : ℕ) (step : List Bool → List Bool)
    (hstep : ∀ w, w.length = b + s → (step w).length = b)
    (masks x : List Bool) :
    (shoupCascade b s t step masks x).length = b :=
  length_shoupState b s step hstep masks x t

private def shoupIterStep (b s : ℕ) (step : List Bool → List Bool) (masks x : List Bool)
    (acc : ℕ × List Bool) : ℕ × List Bool :=
  let i := acc.1 + 1
  (i, step (shoupStepInput b s masks x i acc.2))

private def shoupAdvance (b s : ℕ) (step : List Bool → List Bool)
    (masks x : List Bool) (lo hi : ℕ) (initH : List Bool) : List Bool :=
  ((shoupIterStep b s step masks x)^[hi - lo] (lo, initH)).2

private theorem fst_iterate_shoupIterStep (b s : ℕ) (step : List Bool → List Bool)
    (masks x : List Bool) (lo : ℕ) (initH : List Bool) (d : ℕ) :
    ((shoupIterStep b s step masks x)^[d] (lo, initH)).1 = lo + d := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [Function.iterate_succ_apply', shoupIterStep, ih]; omega

private theorem shoupAdvance_succ (b s : ℕ) (step : List Bool → List Bool)
    (masks x : List Bool) {lo hi : ℕ} (hlo : lo < hi) (initH : List Bool) :
    shoupAdvance b s step masks x lo hi initH =
      step (shoupStepInput b s masks x hi (shoupAdvance b s step masks x lo (hi - 1) initH)) := by
  dsimp only [shoupAdvance]
  rw [show hi - lo = (hi - 1 - lo) + 1 by omega, Function.iterate_succ_apply']
  dsimp only [shoupIterStep]
  rw [fst_iterate_shoupIterStep, show lo + (hi - 1 - lo) + 1 = hi by omega]

private theorem iterate_shoupIterStep_from (b s : ℕ) (step : List Bool → List Bool)
    (masks x : List Bool) (lo d : ℕ) :
    (shoupIterStep b s step masks x)^[d] (lo, shoupState b s step masks x lo) =
      (lo + d, shoupState b s step masks x (lo + d)) := by
  induction d with
  | zero => simp
  | succ d ih => rw [Function.iterate_succ_apply', ih]; rfl

private theorem shoupAdvance_shoupState {b s : ℕ} (step : List Bool → List Bool)
    (masks x : List Bool) {lo hi : ℕ} (hlo : lo ≤ hi) :
    shoupAdvance b s step masks x lo hi (shoupState b s step masks x lo) =
      shoupState b s step masks x hi := by
  dsimp only [shoupAdvance]
  rw [iterate_shoupIterStep_from, Nat.add_sub_of_le hlo]

private theorem shoupAdvance_congr {b s : ℕ} (step : List Bool → List Bool)
    (m₁ m₂ x : List Bool) {lo hi : ℕ} (_hlo : lo ≤ hi) (initH : List Bool)
    (hagree : ∀ i, lo < i → i ≤ hi →
      BitString.listRow b (padicValNat 2 i) m₁ = BitString.listRow b (padicValNat 2 i) m₂) :
    shoupAdvance b s step m₁ x lo hi initH = shoupAdvance b s step m₂ x lo hi initH := by
  suffices h : ∀ d ≤ hi - lo,
      (shoupIterStep b s step m₁ x)^[d] (lo, initH) =
        (shoupIterStep b s step m₂ x)^[d] (lo, initH) from
    congrArg Prod.snd (h (hi - lo) le_rfl)
  intro d hd
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (Nat.le_of_succ_le hd)]
    dsimp only [shoupIterStep, shoupStepInput]
    rw [fst_iterate_shoupIterStep, hagree _ (by omega) (by omega)]

@[fun_prop]
private theorem computableInPolyTime_shoupAdvance {γ : Type} {encIn : γ ↪ List Bool}
    {b s : γ → ℕ} {step : γ → List Bool → List Bool}
    {masks x : γ → List Bool} {lo hi : γ → ℕ} {initH : γ → List Bool}
    (hb : ComputableInPolyTime b encIn encUnary)
    (hs : ComputableInPolyTime s encIn encUnary)
    (hstep : ComputableInPolyTime (fun p : γ × List Bool => step p.1 p.2)
      (encPair encIn encBits) encBits)
    (hstep_len : ∀ a w, w.length = b a + s a → (step a w).length = b a)
    (hmasks : ComputableInPolyTime masks encIn encBits)
    (hx : ComputableInPolyTime x encIn encBits)
    (hlo : ComputableInPolyTime lo encIn encUnary)
    (hhi : ComputableInPolyTime hi encIn encUnary)
    (hinit : ComputableInPolyTime initH encIn encBits)
    (hinit_len : ∀ a, (initH a).length = b a) :
    ComputableInPolyTime
      (fun a => shoupAdvance (b a) (s a) (step a) (masks a) (x a) (lo a) (hi a) (initH a))
      encIn encBits := by
  let par := fun a => (a, b a, s a, masks a, x a)
  let encPar := encPair encIn
    (encPair encUnary (encPair encUnary (encPair encBits encBits)))
  have hpar : ComputableInPolyTime par encIn encPar := by fun_prop
  let iterF : (γ × ℕ × ℕ × List Bool × List Bool) → ℕ × List Bool → ℕ × List Bool :=
    fun p acc => shoupIterStep p.2.1 p.2.2.1 (step p.1) p.2.2.2.1 p.2.2.2.2 acc
  have hiter_step : ComputableInPolyTime
      (fun q : (γ × ℕ × ℕ × List Bool × List Bool) × (ℕ × List Bool) => iterF q.1 q.2)
      (encPair encPar (encPair encUnary encBits)) (encPair encUnary encBits) := by
    unfold iterF shoupIterStep
    fun_prop
  obtain ⟨heff, _⟩ := ComputableInPolyTime.iterateWith_spec hpar
    (ComputableInPolyTime.unary_sub' hhi hlo)
    (hlo.prod hinit) hiter_step
    (fun a i acc => acc.1 = lo a + i ∧ acc.2.length = b a)
    (fun a => ⟨(Nat.add_zero _).symm, hinit_len a⟩)
    (fun a i acc _ ⟨hacc1, _⟩ => by
      dsimp only [iterF, shoupIterStep, par]
      exact ⟨by omega, hstep_len a _ (length_shoupStepInput _ _ _ _ _ _)⟩)
    (size := fun a => 2 * (lo a + hi a + b a) + 4)
    (ComputableInPolyTime.polyBounded (by fun_prop))
    (fun a i acc hi_lt ⟨hacc1, hacc2⟩ => by
      simp only [length_encPair, encUnary_apply, encBits_apply, List.length_replicate, hacc2]
      omega)
  exact (ComputableInPolyTime.snd encUnary encBits).comp heff

@[fun_prop]
theorem computableInPolyTime_shoupState {γ : Type} {encIn : γ ↪ List Bool}
    {b s t : γ → ℕ} {step : γ → List Bool → List Bool} {masks x : γ → List Bool}
    (hb : ComputableInPolyTime b encIn encUnary)
    (hs : ComputableInPolyTime s encIn encUnary)
    (ht : ComputableInPolyTime t encIn encUnary)
    (hstep : ComputableInPolyTime (fun p : γ × List Bool => step p.1 p.2)
      (encPair encIn encBits) encBits)
    (hstep_len : ∀ a w, w.length = b a + s a → (step a w).length = b a)
    (hmasks : ComputableInPolyTime masks encIn encBits)
    (hx : ComputableInPolyTime x encIn encBits) :
    ComputableInPolyTime
      (fun a => shoupState (b a) (s a) (step a) (masks a) (x a) (t a))
      encIn encBits := by
  have heq (a : γ) :
      shoupState (b a) (s a) (step a) (masks a) (x a) (t a) =
        shoupAdvance (b a) (s a) (step a) (masks a) (x a) 0 (t a)
          (BitString.listRow (b a) 0 (x a)) :=
    (shoupAdvance_shoupState (step a) (masks a) (x a) (Nat.zero_le (t a))).symm
  simpa only [heq] using computableInPolyTime_shoupAdvance hb hs hstep hstep_len hmasks hx
    (.const 0) ht (ComputableInPolyTime.bitsRowWithInput hb (.const 0) hx)
    (fun _ => BitString.length_listRow _ _ _)

@[fun_prop]
theorem computableInPolyTime_shoupCascade {γ : Type} {encIn : γ ↪ List Bool}
    {b s t : γ → ℕ} {step : γ → List Bool → List Bool} {masks x : γ → List Bool}
    (hb : ComputableInPolyTime b encIn encUnary)
    (hs : ComputableInPolyTime s encIn encUnary)
    (ht : ComputableInPolyTime t encIn encUnary)
    (hstep : ComputableInPolyTime (fun p : γ × List Bool => step p.1 p.2)
      (encPair encIn encBits) encBits)
    (hstep_len : ∀ a w, w.length = b a + s a → (step a w).length = b a)
    (hmasks : ComputableInPolyTime masks encIn encBits)
    (hx : ComputableInPolyTime x encIn encBits) :
    ComputableInPolyTime
      (fun a => shoupCascade (b a) (s a) (t a) (step a) (masks a) (x a))
      encIn encBits :=
  computableInPolyTime_shoupState hb hs ht hstep hstep_len hmasks hx

/-- Deterministic step-collision extraction from any equal-length collision on `shoupCascade`. -/
theorem exists_shoupCascade_step_collision {b s t L : ℕ}
    (hs_pos : 1 ≤ s) (hb_le : b ≤ L) (hL_le : L ≤ b + t * s)
    (step : List Bool → List Bool)
    (hstep : ∀ w, w.length = b + s → (step w).length = b)
    (masks x₀ x₁ : List Bool)
    (hx₀ : x₀.length = L) (hx₁ : x₁.length = L) (hne : x₀ ≠ x₁)
    (hcoll : shoupCascade b s t step masks x₀ = shoupCascade b s t step masks x₁) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ t ∧
      shoupStepInput b s masks x₀ i (shoupState b s step masks x₀ (i - 1)) ≠
        shoupStepInput b s masks x₁ i (shoupState b s step masks x₁ (i - 1)) ∧
      step (shoupStepInput b s masks x₀ i (shoupState b s step masks x₀ (i - 1))) =
        step (shoupStepInput b s masks x₁ i (shoupState b s step masks x₁ (i - 1))) := by
  by_contra hno
  push Not at hno
  have hback : ∀ d ≤ t,
      shoupState b s step masks x₀ (t - d) = shoupState b s step masks x₁ (t - d) ∧
      ∀ i, t - d < i → i ≤ t → shoupChunk b s i x₀ = shoupChunk b s i x₁ := by
    intro d
    induction d with
    | zero => intro _; exact ⟨hcoll, fun i h1 h2 => by omega⟩
    | succ d ih =>
      intro hd
      set k := t - (d + 1)
      obtain ⟨hnext, hchunks⟩ := ih (Nat.le_of_succ_le hd)
      rw [show t - d = k + 1 by omega] at hnext hchunks
      have hinp : shoupStepInput b s masks x₀ (k + 1) (shoupState b s step masks x₀ k) =
          shoupStepInput b s masks x₁ (k + 1) (shoupState b s step masks x₁ k) :=
        not_ne_iff.mp fun hne_in => hno (k + 1) (by omega) (by omega) hne_in hnext
      obtain ⟨hxor, hchunk⟩ := List.append_inj hinp (by simp only [BitString.length_listXor])
      refine ⟨(BitString.listXor_pair_left_inj (length_shoupState b s step hstep masks x₀ k)
        (length_shoupState b s step hstep masks x₁ k) _).mp hxor, fun i hi1 hi2 => ?_⟩
      exact (eq_or_lt_of_le (Nat.succ_le_of_lt hi1)).elim (· ▸ hchunk) (hchunks i · hi2)
  obtain ⟨h0, hchunks⟩ := hback t le_rfl
  rw [Nat.sub_self] at h0 hchunks
  have listRow_zero_take (x : List Bool) (hx : x.length = L) :
      BitString.listRow b 0 x = x.take b := by
    rw [BitString.listRow_zero, BitString.ofFn_ofList_eq_take,
      List.take_append_of_le_length (by omega)]
  have htake : x₀.take b = x₁.take b := by
    rw [← listRow_zero_take x₀ hx₀, ← listRow_zero_take x₁ hx₁]; exact h0
  have hdrop : x₀.drop b = x₁.drop b := List.ext_getElem (by simp [hx₀, hx₁]) fun j hj₀ hj₁ => by
    have hj_lt : j < t * s := by rw [List.length_drop, hx₀] at hj₀; omega
    have hq_lt : j / s < t := Nat.div_lt_of_lt_mul (by rwa [mul_comm])
    have hr_lt : j % s < s := Nat.mod_lt j hs_pos
    have hidx := congrArg (fun l => l.getD (j % s) false)
      (hchunks (j / s + 1) (Nat.succ_pos _) hq_lt)
    simp only [shoupChunk, Nat.add_sub_cancel, BitString.getD_listRow hr_lt,
      Nat.div_add_mod' j s, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj₀, List.getElem?_eq_getElem hj₁, Option.getD_some] at hidx
    exact hidx
  exact hne (by rw [← List.take_append_drop b x₀, htake, hdrop, List.take_append_drop])

/-! ### Shoup XOR-mask reconstruction (`[Shoup2000]`; `[HHRVW2020]` Lemma 5.7, p. 30) -/

private structure ShoupPackAcc where
  rem : ℕ
  activeOwner : ℕ
  activeS : List Bool
  masks : List Bool

private enc_structure encShoupPackAcc : ShoupPackAcc where
  rem : encUnary,
  activeOwner : encUnary,
  activeS : encBits,
  masks : encBits

private def shoupPackStep (b s t iStar : ℕ) (step : List Bool → List Bool) (x T : List Bool)
    (acc : ShoupPackAcc) : ShoupPackAcc :=
  let k := acc.rem - 1
  if decide (k = 0) || shoupIsLastOcc iStar k then
    let hk :=
      if decide (k = 0) then BitString.listRow b 0 x
      else step (BitString.listRow b (padicValNat 2 k) T ++ shoupChunk b s k x)
    let hEnd := shoupAdvance b s step acc.masks x k (acc.activeOwner - 1) hk
    let newMask := BitString.listXor b [hEnd, acc.activeS]
    let newMasks := BitString.replaceRow b (shoupMaskCount t)
      (padicValNat 2 acc.activeOwner) newMask acc.masks
    let nextS := BitString.listRow b (padicValNat 2 k) T
    ⟨k, k, nextS, newMasks⟩
  else
    ⟨k, acc.activeOwner, acc.activeS, acc.masks⟩

/-- Shoup's XOR-mask reconstruction algorithm (`[Shoup2000]`; `[HHRVW2020]` Lemma 5.7, p. 30):
given base step `step`, target message `x`, planted collision step `iStar` (`1 ≤ iStar ≤ t`),
and uniform random block vector `T` of length `shoupMasksLen b t`, builds the
`shoupMasksLen b t`-bit mask list `M` satisfying both planted-input equality at `iStar` and exact
uniformity. -/
def shoupPackMasks (b s t iStar : ℕ) (step : List Bool → List Bool)
    (x T : List Bool) : List Bool :=
  let T0 := BitString.listRow (shoupMasksLen b t) 0 T
  ((shoupPackStep b s t iStar step x T0)^[iStar]
    ⟨iStar, iStar, BitString.listRow b (padicValNat 2 iStar) T0, T0⟩).masks

theorem length_shoupPackMasks (b s t iStar : ℕ) (step : List Bool → List Bool)
    (x T : List Bool) :
    (shoupPackMasks b s t iStar step x T).length = shoupMasksLen b t := by
  suffices ∀ m (acc : ShoupPackAcc), acc.masks.length = shoupMasksLen b t →
      ((shoupPackStep b s t iStar step x
        (BitString.listRow (shoupMasksLen b t) 0 T))^[m] acc).masks.length =
        shoupMasksLen b t from
    this iStar _ (BitString.length_listRow _ _ _)
  intro m
  induction m with
  | zero => exact fun _ h => h
  | succ m ih =>
    intro acc h
    rw [Function.iterate_succ_apply]
    apply ih
    dsimp only [shoupPackStep]
    split <;> dsimp only
    · exact BitString.length_replaceRow (BitString.length_listXor _ _) _
    · exact h

private theorem padicValNat_two_lt_maskCount {a t : ℕ} (h : a ≤ t) :
    padicValNat 2 a < shoupMaskCount t :=
  Nat.lt_succ_of_le <|
    Nat.padicValNat_def ▸ (multiplicity_le_nat_log a).trans (Nat.log_mono_right h)

private def shoupSegStart (b s : ℕ) (step : List Bool → List Bool) (x T0 : List Bool)
    (lo : ℕ) : List Bool :=
  if lo = 0 then BitString.listRow b 0 x
  else step (BitString.listRow b (padicValNat 2 lo) T0 ++ shoupChunk b s lo x)

private def ShoupSeg (iStar lo p bound : ℕ) : Prop :=
  bound ≤ lo ∧ lo < p ∧ p ≤ iStar ∧
  (lo = 0 ∨ shoupIsLastOcc iStar lo = true) ∧
  shoupIsLastOcc iStar p = true ∧
  ∀ m, lo < m → m < p → shoupIsLastOcc iStar m = false

private theorem shoupAdvance_replaceRow_congr {b s t iStar own lo p : ℕ}
    (step : List Bool → List Bool) (masks newMask x initH : List Bool)
    (hlen : newMask.length = b) (hit : iStar ≤ t) (hp_le : p ≤ iStar) (hlo : lo < p)
    (hown_le : own ≤ p) (hown_last : shoupIsLastOcc iStar own = true)
    (hp_last : shoupIsLastOcc iStar p = true)
    (hbtw : ∀ m, lo < m → m < p → shoupIsLastOcc iStar m = false) :
    shoupAdvance b s step
        (BitString.replaceRow b (shoupMaskCount t) (padicValNat 2 own) newMask masks) x
        lo (p - 1) initH =
      shoupAdvance b s step masks x lo (p - 1) initH := by
  refine shoupAdvance_congr step _ masks x (by omega) initH fun i hi1 hi2 => ?_
  have hj_lt : padicValNat 2 i < shoupMaskCount t :=
    padicValNat_two_lt_maskCount ((hi2.trans ((Nat.sub_le _ _).trans hp_le)).trans hit)
  rw [BitString.listRow_replaceRow hlen masks hj_lt]
  have hgt : p < shoupLastOcc iStar (padicValNat 2 i) :=
    shoupLastOcc_gt_between hp_last hbtw (by omega) hi1 (by omega)
  have hne : padicValNat 2 i ≠ padicValNat 2 own := fun hjeq => by
    have := shoupLastOcc_padicValNat_eq hown_last
    rw [hjeq, this] at hgt; omega
  simp only [hne, ↓reduceIte]

private def shoupPackInv (b s t iStar : ℕ) (step : List Bool → List Bool) (x T0 : List Bool)
    (m : ℕ) (st : ShoupPackAcc) : Prop :=
  st.rem = iStar - m ∧
  (∀ j, Nat.log 2 iStar < j → j < shoupMaskCount t →
    BitString.listRow b j st.masks = BitString.listRow b j T0) ∧
  (if m < iStar then
    st.rem ≤ st.activeOwner ∧ st.activeOwner ≤ iStar ∧
    shoupIsLastOcc iStar st.activeOwner = true ∧
    (∀ i', st.rem ≤ i' → i' < st.activeOwner → shoupIsLastOcc iStar i' = false) ∧
    st.activeS = BitString.listRow b (padicValNat 2 st.activeOwner) T0
  else st.activeOwner = 0) ∧
  (∀ lo p, ShoupSeg iStar lo p (if m < iStar then st.activeOwner else 0) →
    BitString.listRow b (padicValNat 2 p) st.masks =
      BitString.listXor b
        [shoupAdvance b s step st.masks x lo (p - 1) (shoupSegStart b s step x T0 lo),
         BitString.listRow b (padicValNat 2 p) T0])

private theorem shoupPackStep_preserves_inv {b s t iStar : ℕ} (step : List Bool → List Bool)
    (hit : iStar ≤ t) (x T0 : List Bool) {m : ℕ} (hm : m < iStar) {st : ShoupPackAcc}
    (hinv : shoupPackInv b s t iStar step x T0 m st) :
    shoupPackInv b s t iStar step x T0 (m + 1) (shoupPackStep b s t iStar step x T0 st) := by
  obtain ⟨hrem, hhi_j, hbranch, hsegs⟩ := hinv
  simp only [hm, ↓reduceIte] at hbranch hsegs
  obtain ⟨h_lt_own, h_own_le, h_own_last, h_no_btw, hs_eq⟩ := hbranch
  set k := st.rem - 1
  have hstep_if : shoupPackStep b s t iStar step x T0 st =
      if (decide (k = 0) || shoupIsLastOcc iStar k) = true then
        ⟨k, k, BitString.listRow b (padicValNat 2 k) T0,
          BitString.replaceRow b (shoupMaskCount t) (padicValNat 2 st.activeOwner)
            (BitString.listXor b
              [shoupAdvance b s step st.masks x k (st.activeOwner - 1)
                (if decide (k = 0) then BitString.listRow b 0 x
                  else step (BitString.listRow b (padicValNat 2 k) T0 ++ shoupChunk b s k x)),
                st.activeS])
            st.masks⟩
      else ⟨k, st.activeOwner, st.activeS, st.masks⟩ := rfl
  rw [hstep_if]
  by_cases htrig : (decide (k = 0) || shoupIsLastOcc iStar k) = true
  · simp only [htrig, ↓reduceIte]
    have htrig' : k = 0 ∨ shoupIsLastOcc iStar k = true := by
      simpa only [Bool.or_eq_true, decide_eq_true_eq] using htrig
    have hown_log : padicValNat 2 st.activeOwner ≤ Nat.log 2 iStar :=
      Nat.lt_succ_iff.mp (padicValNat_two_lt_maskCount h_own_le)
    have hown_lt : padicValNat 2 st.activeOwner < shoupMaskCount t :=
      padicValNat_two_lt_maskCount (h_own_le.trans hit)
    set newMask := BitString.listXor b
      [shoupAdvance b s step st.masks x k (st.activeOwner - 1)
        (if decide (k = 0) then BitString.listRow b 0 x
          else step (BitString.listRow b (padicValNat 2 k) T0 ++ shoupChunk b s k x)),
        st.activeS]
    set newMasks := BitString.replaceRow b (shoupMaskCount t)
      (padicValNat 2 st.activeOwner) newMask st.masks
    have hmlen : newMask.length = b := BitString.length_listXor _ _
    have hrow_ne {j : ℕ} (hne : j ≠ padicValNat 2 st.activeOwner) (hj : j < shoupMaskCount t) :
        BitString.listRow b j newMasks = BitString.listRow b j st.masks := by
      simp only [newMasks, BitString.listRow_replaceRow hmlen st.masks hj, hne, ↓reduceIte]
    refine ⟨by dsimp only [k]; omega, fun j hj1 hj2 => by
      rw [hrow_ne (by omega) hj2, hhi_j j hj1 hj2], ?_, ?_⟩
    · by_cases hm1 : m + 1 < iStar
      · simp only [hm1, ↓reduceIte]
        exact ⟨le_rfl, by dsimp only [k]; omega, htrig'.resolve_left (by dsimp only [k]; omega),
          fun _ h1 h2 => by omega, trivial⟩
      · simp only [hm1, ↓reduceIte]; dsimp only [k]; omega
    · intro lo p hseg
      have hb_eq : (if m + 1 < iStar then k else 0) = k := by
        split_ifs
        · rfl
        · dsimp only [k]; omega
      rw [hb_eq] at hseg
      rcases hseg with ⟨h_k_lo, h_lo_p, h_p_le, h_lo_cond, h_p_last, h_btw⟩
      rcases eq_or_lt_of_le h_k_lo with hkeq | hlo_gt
      · have hp_eq : p = st.activeOwner := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have h := h_no_btw p (by omega) hlt; rw [h_p_last] at h; exact Bool.false_ne_true h.symm
          · have h := h_btw _ (by omega) hgt; rw [h_own_last] at h; exact Bool.false_ne_true h.symm
        subst hp_eq
        have hseg_eq : (if decide (k = 0) then BitString.listRow b 0 x
            else step (BitString.listRow b (padicValNat 2 k) T0 ++ shoupChunk b s k x)) =
            shoupSegStart b s step x T0 k := by
          dsimp only [shoupSegStart]; by_cases h0 : k = 0 <;> simp [h0]
        rw [← hkeq, BitString.listRow_replaceRow hmlen st.masks hown_lt]
        simp only [↓reduceIte]
        rw [shoupAdvance_replaceRow_congr step st.masks newMask x _ hmlen hit h_own_le
            (hkeq ▸ h_lo_p) le_rfl h_own_last h_own_last (hkeq ▸ h_btw)]
        dsimp only [newMask]; rw [hseg_eq, hs_eq]
      · have hown_lo : st.activeOwner ≤ lo := not_lt.mp fun hlt =>
          h_lo_cond.elim (by omega) fun hl => by
            have h := h_no_btw lo (by omega) hlt; rw [hl] at h; exact Bool.false_ne_true h.symm
        have hp_ne : padicValNat 2 p ≠ padicValNat 2 st.activeOwner := fun heq => by
          have h1 := shoupLastOcc_padicValNat_eq h_p_last
          rw [heq, shoupLastOcc_padicValNat_eq h_own_last] at h1; omega
        rw [hrow_ne hp_ne (padicValNat_two_lt_maskCount (h_p_le.trans hit)),
          hsegs lo p ⟨hown_lo, h_lo_p, h_p_le, h_lo_cond, h_p_last, h_btw⟩,
          shoupAdvance_replaceRow_congr step st.masks newMask x _ hmlen hit h_p_le h_lo_p
            (hown_lo.trans h_lo_p.le) h_own_last h_p_last h_btw]
  · simp only [Bool.eq_false_iff.mpr htrig, Bool.false_eq_true, ↓reduceIte]
    have hk_ne0 : k ≠ 0 := fun h0 => htrig (by simp [h0])
    have hk_f : shoupIsLastOcc iStar k = false :=
      Bool.eq_false_iff.mpr fun hs => htrig (by simp [hs])
    have hk_def : k = iStar - (m + 1) := by dsimp only [k]; omega
    have hm1 : m + 1 < iStar := by omega
    refine ⟨hk_def, hhi_j, ?_, fun lo p hseg => by
      simp only [hm1, ↓reduceIte] at hseg; exact hsegs lo p hseg⟩
    simp only [hm1, ↓reduceIte]
    exact ⟨by dsimp only [k]; omega, h_own_le, h_own_last, fun i' hi1 hi2 =>
      (eq_or_lt_of_le hi1).elim (· ▸ hk_f) (fun hg => h_no_btw i' (by omega) hi2),
      hs_eq⟩

private theorem shoupPack_prevBreak {iStar k : ℕ} (hk : 0 < k) :
    ∃ lo < k, (lo = 0 ∨ shoupIsLastOcc iStar lo = true) ∧
      ∀ m, lo < m → m < k → shoupIsLastOcc iStar m = false := by
  let S := (Finset.range k).filter fun m => decide (m = 0 ∨ shoupIsLastOcc iStar m = true)
  have hS : S.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, by simp⟩⟩
  have hmem := Finset.max'_mem S hS
  rw [Finset.mem_filter, Finset.mem_range, decide_eq_true_eq] at hmem
  refine ⟨S.max' hS, hmem.1, hmem.2, fun m h1 h2 => by_contra fun hf => ?_⟩
  have := Finset.le_max' S m (Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr h2, decide_eq_true_eq.mpr (Or.inr (Bool.eq_true_of_not_eq_false hf))⟩)
  omega

private theorem shoupPack_breakUniq {iStar lo₁ lo₂ u v : ℕ} (h1u : lo₁ < u) (h2v : lo₂ ≤ v)
    (huv : u = v + 1) (h1c : lo₁ = 0 ∨ shoupIsLastOcc iStar lo₁ = true)
    (h2c : lo₂ = 0 ∨ shoupIsLastOcc iStar lo₂ = true)
    (h1b : ∀ m, lo₁ < m → m < u → shoupIsLastOcc iStar m = false)
    (h2b : ∀ m, lo₂ < m → m ≤ v → shoupIsLastOcc iStar m = false) : lo₂ = lo₁ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rcases h1c with rfl | hl
    · omega
    · have h := h2b lo₁ hlt (by omega); rw [hl] at h; exact Bool.false_ne_true h.symm
  · rcases h2c with rfl | hl
    · omega
    · have h := h1b lo₂ hgt (by omega); rw [hl] at h; exact Bool.false_ne_true h.symm

private theorem shoupState_eq_shoupAdvance {b s iStar : ℕ} (step : List Bool → List Bool)
    (masks x T0 : List Bool)
    (hsegs : ∀ lo p, ShoupSeg iStar lo p 0 →
      BitString.listRow b (padicValNat 2 p) masks =
        BitString.listXor b
          [shoupAdvance b s step masks x lo (p - 1) (shoupSegStart b s step x T0 lo),
           BitString.listRow b (padicValNat 2 p) T0]) :
    ∀ k ≤ iStar, ∃ lo ≤ k, (lo = 0 ∨ shoupIsLastOcc iStar lo = true) ∧
      (∀ m, lo < m → m ≤ k → shoupIsLastOcc iStar m = false) ∧
      shoupState b s step masks x k =
        shoupAdvance b s step masks x lo k (shoupSegStart b s step x T0 lo) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨0, le_rfl, Or.inl rfl, fun _ h1 h2 => by omega, by
      simp only [shoupState, shoupAdvance, shoupSegStart, Nat.sub_self, Function.iterate_zero,
        id_eq, ↓reduceIte]⟩
  | succ k ih =>
    intro hk_le
    obtain ⟨lo, hlo_lt, hlo_c, hbtw⟩ := shoupPack_prevBreak (iStar := iStar) (Nat.succ_pos k)
    obtain ⟨lo', hlo'_le, hlo'_c, hbtw', hst'⟩ := ih (Nat.le_of_succ_le hk_le)
    have hlo_eq : lo' = lo := shoupPack_breakUniq hlo_lt hlo'_le rfl hlo_c hlo'_c hbtw hbtw'
    rw [hlo_eq] at hbtw' hst'
    by_cases hlast : shoupIsLastOcc iStar (k + 1) = true
    · refine ⟨k + 1, le_rfl, Or.inr hlast, fun _ h1 h2 => by omega, ?_⟩
      have hrow := hsegs lo (k + 1) ⟨Nat.zero_le _, hlo_lt, hk_le, hlo_c, hlast, hbtw⟩
      dsimp only [shoupState, shoupStepInput, shoupAdvance, shoupSegStart]
      rw [Nat.sub_self, Function.iterate_zero, id_eq]
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      rw [hst', hrow, Nat.add_sub_cancel,
        BitString.listXor_pair_self_left_of_length _ (BitString.length_listRow _ _ _)]
    · have hf : shoupIsLastOcc iStar (k + 1) = false := Bool.eq_false_of_not_eq_true hlast
      refine ⟨lo, hlo_lt.le, hlo_c, fun m h1 h2 =>
        (eq_or_lt_of_le h2).elim (· ▸ hf) (fun h => hbtw' m h1 (by omega)), ?_⟩
      rw [shoupAdvance_succ b s step masks x hlo_lt, Nat.succ_sub_one, ← hst']; rfl

private theorem shoupPackMasks_spec (b s t iStar : ℕ) (step : List Bool → List Bool)
    (hstep : ∀ w, w.length = b + s → (step w).length = b)
    (hi_pos : 1 ≤ iStar) (hit : iStar ≤ t) (x T : List Bool) :
    let masks := shoupPackMasks b s t iStar step x T
    (∀ j, Nat.log 2 iStar < j → j < shoupMaskCount t →
      BitString.listRow b j masks = BitString.listRow b j T) ∧
    (∀ j ≤ Nat.log 2 iStar,
      let p := shoupLastOcc iStar j
      shoupState b s step masks x (p - 1) =
        BitString.listXor b [BitString.listRow b j masks, BitString.listRow b j T]) := by
  let T0 := BitString.listRow (shoupMasksLen b t) 0 T
  have hinv : ∀ m ≤ iStar, shoupPackInv b s t iStar step x T0 m
      ((shoupPackStep b s t iStar step x T0)^[m]
        ⟨iStar, iStar, BitString.listRow b (padicValNat 2 iStar) T0, T0⟩) := by
    intro m; induction m with
    | zero =>
      intro _
      dsimp only [Function.iterate_zero, id_eq]
      have hpos : 0 < iStar := hi_pos
      refine ⟨by simp, fun _ _ _ => rfl, ?_, fun _ _ hseg => by
        simp only [hpos, ↓reduceIte] at hseg; rcases hseg with ⟨h1, h2, h3, _⟩; omega⟩
      simp only [hpos, ↓reduceIte]
      exact ⟨le_rfl, le_rfl, shoupIsLastOcc_self hi_pos, fun _ h1 h2 => by omega, trivial⟩
    | succ m ih =>
      intro hm; rw [Function.iterate_succ_apply']
      exact shoupPackStep_preserves_inv step hit x T0 hm (ih (Nat.le_of_succ_le hm))
  obtain ⟨_, hhi, _, hsegs⟩ := hinv iStar le_rfl
  simp only [lt_irrefl, ↓reduceIte] at hsegs
  set masks := shoupPackMasks b s t iStar step x T
  have hT0 (j : ℕ) (hj : j < shoupMaskCount t) :
      BitString.listRow b j T0 = BitString.listRow b j T :=
    List.ext_getElem (by simp) fun col hc _ => by
      rw [BitString.length_listRow] at hc
      have hlt : j * b + col < shoupMaskCount t * b := by
        have := Nat.mul_le_mul_right b hj; rw [Nat.succ_mul] at this; omega
      have hget := BitString.getD_listRow_zero (shoupMasksLen b t) T (j * b + col) hlt
      rw [BitString.getElem_listRow hc, BitString.getElem_listRow hc, hget]
  refine ⟨fun j h1 h2 => (hhi j h1 h2).trans (hT0 j h2), fun j hj => ?_⟩
  set p := shoupLastOcc iStar j
  have hp_last : shoupIsLastOcc iStar p = true := shoupIsLastOcc_shoupLastOcc hi_pos hj
  have hp_info := decide_eq_true_eq.mp hp_last
  have hv_p : padicValNat 2 p = j := padicValNat_two_shoupLastOcc hi_pos hj
  obtain ⟨lo, hlo_lt, hlo_c, hbtw⟩ := shoupPack_prevBreak (iStar := iStar) hp_info.1
  obtain ⟨lo', hlo'_le, hlo'_c, hbtw', hst'⟩ := shoupState_eq_shoupAdvance step masks x T0 hsegs
    (p - 1) (by omega)
  have hlo_eq : lo' = lo := shoupPack_breakUniq hlo_lt hlo'_le (by omega) hlo_c hlo'_c hbtw hbtw'
  rw [hlo_eq] at hst'
  have hrow : BitString.listRow b j masks = BitString.listXor b
      [shoupAdvance b s step masks x lo (p - 1) (shoupSegStart b s step x T0 lo),
       BitString.listRow b j T] := by
    have h := hsegs lo p ⟨Nat.zero_le _, hlo_lt, hp_info.2.1, hlo_c, hp_last, hbtw⟩
    rwa [hv_p, hT0 j (Nat.lt_succ_of_le (hj.trans (Nat.log_mono_right hit)))] at h
  have hlen_st : (shoupAdvance b s step masks x lo (p - 1)
      (shoupSegStart b s step x T0 lo)).length = b :=
    hst' ▸ length_shoupState b s step hstep masks x (p - 1)
  change shoupState b s step masks x (p - 1) =
    BitString.listXor b [BitString.listRow b j masks, BitString.listRow b j T]
  rw [hst', hrow, BitString.listXor_pair_comm b (BitString.listXor b _),
    BitString.listXor_pair_comm b (shoupAdvance _ _ _ _ _ _ _ _),
    BitString.listXor_pair_self_left_of_length _ hlen_st]

theorem shoupStepInput_shoupPackMasks {b s t iStar : ℕ}
    (step : List Bool → List Bool) (hstep : ∀ w, w.length = b + s → (step w).length = b)
    (hi_pos : 1 ≤ iStar) (hit : iStar ≤ t) (x T : List Bool) :
    let masks := shoupPackMasks b s t iStar step x T
    shoupStepInput b s masks x iStar (shoupState b s step masks x (iStar - 1)) =
      BitString.listRow b (padicValNat 2 iStar) T ++ shoupChunk b s iStar x := by
  intro masks
  have hp := (shoupPackMasks_spec b s t iStar step hstep hi_pos hit x T).2
    (padicValNat 2 iStar) (Nat.lt_succ_iff.mp (padicValNat_two_lt_maskCount le_rfl))
  rw [shoupLastOcc_padicValNat_eq (shoupIsLastOcc_self hi_pos)] at hp
  dsimp only [shoupStepInput]
  rw [hp, BitString.listXor_pair_comm b (BitString.listXor b _),
    BitString.listXor_pair_self_left_of_length _ (BitString.length_listRow _ _ _)]

private def shoupUnpackMasks (b s t iStar : ℕ) (step : List Bool → List Bool)
    (x masks : List Bool) : List Bool :=
  (List.range (shoupMaskCount t)).flatMap fun j =>
    if decide (j ≤ Nat.log 2 iStar) then
      let p := shoupLastOcc iStar j
      BitString.listXor b
        [shoupState b s step masks x (p - 1), BitString.listRow b j masks]
    else
      BitString.listRow b j masks

private theorem length_shoupUnpackMasks (b s t iStar : ℕ) (step : List Bool → List Bool)
    (x masks : List Bool) :
    (shoupUnpackMasks b s t iStar step x masks).length = shoupMasksLen b t := by
  unfold shoupUnpackMasks shoupMasksLen
  rw [List.length_flatMap]
  have hsum : (List.range (shoupMaskCount t)).map (fun j =>
      (if decide (j ≤ Nat.log 2 iStar) then
        BitString.listXor b
          [shoupState b s step masks x (shoupLastOcc iStar j - 1), BitString.listRow b j masks]
      else BitString.listRow b j masks).length) = List.replicate (shoupMaskCount t) b :=
    List.ext_getElem (by simp) fun i hi _ => by
      simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
      split_ifs <;> simp
  rw [hsum, List.sum_replicate, smul_eq_mul]

private theorem shoupUnpack_shoupPack {b s t iStar : ℕ}
    (step : List Bool → List Bool) (hstep : ∀ w, w.length = b + s → (step w).length = b)
    (hi_pos : 1 ≤ iStar) (hit : iStar ≤ t) (x T : List Bool)
    (hT : T.length = shoupMasksLen b t) :
    shoupUnpackMasks b s t iStar step x (shoupPackMasks b s t iStar step x T) = T := by
  obtain ⟨hhi_m, hlo_m⟩ := shoupPackMasks_spec b s t iStar step hstep hi_pos hit x T
  set masks := shoupPackMasks b s t iStar step x T
  have hrow_eq (j : ℕ) (hj : j < shoupMaskCount t) :
      BitString.listRow b j (shoupUnpackMasks b s t iStar step x masks) =
        BitString.listRow b j T := by
    have hrow := BitString.listRow_flatMap_append (width := b)
      (fun k => if decide (k ≤ Nat.log 2 iStar) then
        BitString.listXor b
          [shoupState b s step masks x (shoupLastOcc iStar k - 1), BitString.listRow b k masks]
      else BitString.listRow b k masks)
      (List.range (shoupMaskCount t)) (fun k _ => by split_ifs <;> simp) [] j (by simpa using hj)
    simp only [List.append_nil, List.getElem_range] at hrow
    change BitString.listRow b j (shoupUnpackMasks b s t iStar step x masks) = _ at hrow
    rw [hrow]
    split_ifs with hle
    · rw [hlo_m j (of_decide_eq_true hle), BitString.listXor_pair_comm b (BitString.listXor b _),
        BitString.listXor_pair_self_left_of_length _ (BitString.length_listRow _ _ _)]
    · exact hhi_m j (Nat.lt_of_not_ge (fun h => hle (decide_eq_true h))) hj
  rw [← BitString.flatten_listRows_of_length (length_shoupUnpackMasks b s t iStar step x masks),
    ← BitString.flatten_listRows_of_length hT]
  congr 1
  refine List.ext_getElem (by simp) fun j hj _ => ?_
  have hj' : j < shoupMaskCount t := by simpa using hj
  simp only [BitString.listRows_eq_ofFn, List.getElem_ofFn, ← BitString.listRow_eq_ofFn]
  exact hrow_eq j hj'

/-- Shoup's mask-reconstruction map preserves `BitString.uniformList (shoupMasksLen b t)`
whenever `1 ≤ iStar ≤ t`. -/
theorem uniformList_map_shoupPackMasks (b s t iStar : ℕ) (step : List Bool → List Bool)
    (hstep : ∀ w, w.length = b + s → (step w).length = b)
    (hi_pos : 1 ≤ iStar) (hit : iStar ≤ t) (x : List Bool) :
    (BitString.uniformList (shoupMasksLen b t)).map (shoupPackMasks b s t iStar step x) =
      BitString.uniformList (shoupMasksLen b t) := by
  let fFin : BitString (shoupMasksLen b t) → BitString (shoupMasksLen b t) :=
    fun T => BitString.ofList (shoupMasksLen b t) (shoupPackMasks b s t iStar step x (List.ofFn T))
  have hinj : Function.Injective fFin := fun T₁ T₂ heq => by
    have hf := congrArg (shoupUnpackMasks b s t iStar step x ∘ List.ofFn) heq
    simp only [Function.comp_apply, fFin,
      BitString.ofFn_ofList (length_shoupPackMasks _ _ _ _ _ _ _),
      shoupUnpack_shoupPack step hstep hi_pos hit x _ List.length_ofFn] at hf
    exact List.ofFn_injective hf
  let e := Equiv.ofBijective fFin (Finite.injective_iff_bijective.mp hinj)
  have hcomp : shoupPackMasks b s t iStar step x ∘ List.ofFn = List.ofFn ∘ e := funext fun T =>
    (BitString.ofFn_ofList (length_shoupPackMasks _ _ _ _ _ _ _)).symm
  rw [BitString.uniformList, PMF.map_comp, hcomp, ← PMF.map_comp,
    PMF.uniformOfFintype_map_equiv e]

@[fun_prop]
theorem computableInPolyTime_shoupPackMasks {γ : Type} {encIn : γ ↪ List Bool}
    {b s t iStar : γ → ℕ} {step : γ → List Bool → List Bool} {x T : γ → List Bool}
    (hb : ComputableInPolyTime b encIn encUnary)
    (hs : ComputableInPolyTime s encIn encUnary)
    (ht : ComputableInPolyTime t encIn encUnary)
    (hi : ComputableInPolyTime iStar encIn encUnary)
    (hstep : ComputableInPolyTime (fun p : γ × List Bool => step p.1 p.2)
      (encPair encIn encBits) encBits)
    (hstep_len : ∀ a w, w.length = b a + s a → (step a w).length = b a)
    (hx : ComputableInPolyTime x encIn encBits)
    (hT : ComputableInPolyTime T encIn encBits) :
    ComputableInPolyTime
      (fun a => shoupPackMasks (b a) (s a) (t a) (iStar a) (step a) (x a) (T a))
      encIn encBits := by
  let T0 (a : γ) := BitString.listRow (shoupMasksLen (b a) (t a)) 0 (T a)
  let encPar := encPair encIn (encPair encUnary (encPair encBits encBits))
  let encQ := encPair encPar encShoupPackAcc
  have hpar_rest := (ComputableInPolyTime.snd encIn _).comp (.fst encPar encShoupPackAcc)
  have hbits_pair := (ComputableInPolyTime.snd encUnary _).comp hpar_rest
  have hq_a := (ComputableInPolyTime.fst encIn _).comp (.fst encPar encShoupPackAcc)
  have hq_b := hb.comp hq_a
  have hq_s := hs.comp hq_a
  have hq_t := ht.comp hq_a
  have hq_i := (ComputableInPolyTime.fst encUnary _).comp hpar_rest
  have hq_x := (ComputableInPolyTime.fst encBits encBits).comp hbits_pair
  have hq_T := (ComputableInPolyTime.snd encBits encBits).comp hbits_pair
  have hq_acc := ComputableInPolyTime.snd encPar encShoupPackAcc
  have hrem := (encShoupPackAcc_rem_polyTime hq_acc).unary_sub' (.const 1)
  have hown := encShoupPackAcc_activeOwner_polyTime hq_acc
  have hactS := encShoupPackAcc_activeS_polyTime hq_acc
  have hmsk := encShoupPackAcc_masks_polyTime hq_acc
  have hnextS := ComputableInPolyTime.bitsRowWithInput hq_b
    (ComputableInPolyTime.unary_padicValNat_two.comp hrem) hq_T
  let hhk (q : (γ × ℕ × List Bool × List Bool) × ShoupPackAcc) : List Bool :=
    if decide (q.2.rem - 1 = 0) then BitString.listRow (b q.1.1) 0 q.1.2.2.1
    else step q.1.1
      (BitString.listRow (b q.1.1) (padicValNat 2 (q.2.rem - 1)) q.1.2.2.2 ++
        shoupChunk (b q.1.1) (s q.1.1) (q.2.rem - 1) q.1.2.2.1)
  have hhk_poly : ComputableInPolyTime hhk encQ encBits :=
    ComputableInPolyTime.ite_decide
      (ComputableInPolyTime.unary_eq' hrem (.const 0))
      (ComputableInPolyTime.bitsRowWithInput hq_b (.const 0) hq_x)
      (hstep.comp (hq_a.prod (ComputableInPolyTime.bitsAppend hnextS
        (ComputableInPolyTime.bitsRowWithInput hq_s (hrem.unary_sub' (.const 1))
          (ComputableInPolyTime.bitsDropWithInput hq_x hq_b)))))
  have hadv := computableInPolyTime_shoupAdvance hq_b hq_s
    (hstep.comp ((hq_a.comp (.fst encQ encBits)).prod (.snd encQ encBits)))
    (fun q w hw => hstep_len q.1.1 w hw) hmsk hq_x hrem
    (hown.unary_sub' (.const 1)) hhk_poly fun q => by
      dsimp only [hhk]; split_ifs
      · exact BitString.length_listRow _ _ _
      · exact hstep_len _ _ (by simp only [shoupChunk, List.length_append,
          BitString.length_listRow])
  have hrep := ComputableInPolyTime.bitsReplaceRowWithInput hq_b
    (computableInPolyTime_shoupMaskCount hq_t)
    (ComputableInPolyTime.unary_padicValNat_two.comp hown)
    (ComputableInPolyTime.bitsXorWithInput hq_b
      (ComputableInPolyTime.cons' hadv (ComputableInPolyTime.cons' hactS (.const []))))
    hmsk
  have hcond : ComputableInPolyTime
      (fun q : (γ × ℕ × List Bool × List Bool) × ShoupPackAcc =>
        decide (q.2.rem - 1 = 0) || shoupIsLastOcc q.1.2.1 (q.2.rem - 1)) encQ encBool :=
    (ComputableInPolyTime.ite' (ComputableInPolyTime.unary_eq' hrem (.const 0)) (.const true)
      (computableInPolyTime_shoupIsLastOcc hq_i hrem)).of_enc_eq fun q =>
        congrArg encBool (by cases decide (q.2.rem - 1 = 0) <;> rfl)
  let iterF : (γ × ℕ × List Bool × List Bool) → ShoupPackAcc → ShoupPackAcc :=
    fun p acc => shoupPackStep (b p.1) (s p.1) (t p.1) p.2.1 (step p.1) p.2.2.1 p.2.2.2 acc
  have hiter_step : ComputableInPolyTime
      (fun q : (γ × ℕ × List Bool × List Bool) × ShoupPackAcc => iterF q.1 q.2)
      encQ encShoupPackAcc := by
    have h_ite := ComputableInPolyTime.ite' hcond
      (encShoupPackAcc_mk_polyTime hrem hrem hnextS hrep)
      (encShoupPackAcc_mk_polyTime hrem hown hactS hmsk)
    exact h_ite
  have hT0 : ComputableInPolyTime T0 encIn encBits :=
    ComputableInPolyTime.bitsRowWithInput
      (computableInPolyTime_shoupMasksLen hb ht) (.const 0) hT
  have hpar : ComputableInPolyTime (fun a : γ => (a, iStar a, x a, T0 a)) encIn encPar := by
    fun_prop
  obtain ⟨heff, _⟩ := ComputableInPolyTime.iterateWith_spec hpar hi
    (encShoupPackAcc_mk_polyTime hi hi
      (ComputableInPolyTime.bitsRowWithInput hb
        (ComputableInPolyTime.unary_padicValNat_two.comp hi) hT0) hT0)
    hiter_step
    (fun a _ acc => acc.rem ≤ iStar a ∧ acc.activeOwner ≤ iStar a ∧
      acc.activeS.length = b a ∧ acc.masks.length = shoupMasksLen (b a) (t a))
    (fun _ => ⟨le_rfl, le_rfl, BitString.length_listRow _ _ _, BitString.length_listRow _ _ _⟩)
    (fun a _ acc _ ⟨h1, h2, h3, h4⟩ => by
      dsimp only [iterF, shoupPackStep]
      by_cases htrig : (decide (acc.rem - 1 = 0) || shoupIsLastOcc (iStar a) (acc.rem - 1)) = true
      · simp only [htrig, ↓reduceIte]
        exact ⟨by omega, by omega, BitString.length_listRow _ _ _,
          BitString.length_replaceRow (BitString.length_listXor _ _) _⟩
      · simp only [htrig, Bool.false_eq_true, ↓reduceIte]
        exact ⟨by omega, h2, h3, h4⟩)
    (size := fun a => 8 * (iStar a + b a + shoupMasksLen (b a) (t a)) + 20)
    (ComputableInPolyTime.polyBounded (by fun_prop))
    fun a _ acc _ ⟨h1, h2, h3, h4⟩ => by
      simp only [encShoupPackAcc_apply, length_encPair, encUnary_apply, encBits_apply,
        List.length_replicate, h3, h4]; omega
  exact encShoupPackAcc_masks_polyTime heff

/-! ### Standalone Shoup composition (`[Shoup2000]`, `[HHRVW2020]` Lemma 5.7) -/

/-- Total key bit-length `baseKeyLen n + (Nat.log 2 (t n) + 1) * outLen n` for `t n`-step Shoup
XOR-masking composition (`[Shoup2000]`; `[HHRVW2020]`, Section 5.1.4, Lemma 5.7, p. 30). -/
@[expose]
def shoupComposeKeyLen (baseKeyLen outLen t : ℕ → ℕ) (n : ℕ) : ℕ :=
  baseKeyLen n + shoupMasksLen (outLen n) (t n)

/-- **`O(|y| log t)` key-length bound**: whenever `outLen n ≤ baseKeyLen n`, the composed key has
length at most `(Nat.log 2 (t n) + 2) * baseKeyLen n`. -/
theorem shoupComposeKeyLen_le {baseKeyLen outLen t : ℕ → ℕ} {n : ℕ}
    (hout_le : outLen n ≤ baseKeyLen n) :
    shoupComposeKeyLen baseKeyLen outLen t n ≤ (Nat.log 2 (t n) + 2) * baseKeyLen n := by
  dsimp only [shoupComposeKeyLen, shoupMasksLen, shoupMaskCount]
  have hmul := Nat.mul_le_mul_left (Nat.log 2 (t n) + 1) hout_le
  linarith

@[fun_prop]
theorem computableInPolyTime_shoupComposeKeyLen
    {γ : Type} {encIn : γ ↪ List Bool}
    {baseKeyLen outLen t : ℕ → ℕ} {f : γ → ℕ}
    (hbase : ComputableInPolyTime baseKeyLen encUnary encUnary)
    (hout : ComputableInPolyTime outLen encUnary encUnary)
    (ht : ComputableInPolyTime t encUnary encUnary)
    (hf : ComputableInPolyTime f encIn encUnary) :
    ComputableInPolyTime (fun a => shoupComposeKeyLen baseKeyLen outLen t (f a))
      encIn encUnary := by
  unfold shoupComposeKeyLen
  have hb := hbase.comp hf
  have ho := hout.comp hf
  have htn := ht.comp hf
  fun_prop

/-- Composed evaluator applying `t n` steps of `shoupCascade` to base evaluator `h n key` where
`key := BitString.listRow (baseKeyLen n) 0 K` and `masks := K.drop (baseKeyLen n)`. -/
@[expose]
def shoupComposeEval (baseKeyLen outLen s t : ℕ → ℕ)
    (h : ℕ → List Bool → List Bool → List Bool)
    (n : ℕ) (K x : List Bool) : List Bool :=
  shoupCascade (outLen n) (s n) (t n) (h n (BitString.listRow (baseKeyLen n) 0 K))
    (K.drop (baseKeyLen n)) x

@[simp]
theorem length_shoupComposeEval {baseKeyLen outLen s t : ℕ → ℕ}
    {h : ℕ → List Bool → List Bool → List Bool} {n : ℕ} {K x : List Bool}
    (h_len : ∀ k w, k.length = baseKeyLen n → w.length = outLen n + s n →
      (h n k w).length = outLen n) :
    (shoupComposeEval baseKeyLen outLen s t h n K x).length = outLen n :=
  length_shoupState (outLen n) (s n) (h n (BitString.listRow (baseKeyLen n) 0 K))
    (fun w => h_len _ w (BitString.length_listRow (baseKeyLen n) 0 K))
    (K.drop (baseKeyLen n)) x (t n)

@[fun_prop]
theorem computableInPolyTime_shoupComposeEval
    {baseKeyLen outLen s t : ℕ → ℕ}
    {h : ℕ → List Bool → List Bool → List Bool}
    (hbase : ComputableInPolyTime baseKeyLen encUnary encUnary)
    (hout : ComputableInPolyTime outLen encUnary encUnary)
    (hs : ComputableInPolyTime s encUnary encUnary)
    (ht : ComputableInPolyTime t encUnary encUnary)
    (hh : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => h p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) encBits)
    (h_len : ∀ n k w, k.length = baseKeyLen n → w.length = outLen n + s n →
      (h n k w).length = outLen n) :
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool =>
        shoupComposeEval baseKeyLen outLen s t h p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) encBits := by
  let hp := ComputableInPolyTime.id' (encIn := encKeyedInput encBits)
  let hn := hp.fst'
  let hK := hp.snd'.fst'
  let hx := hp.snd'.snd'
  let hkey : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool =>
      BitString.listRow (baseKeyLen p.1) 0 p.2.1) (encKeyedInput encBits) encBits := by
    have := hbase.comp hn
    fun_prop
  have hstep : ComputableInPolyTime
      (fun q : (ℕ × List Bool × List Bool) × List Bool =>
        h q.1.1 (BitString.listRow (baseKeyLen q.1.1) 0 q.1.2.1) q.2)
      (encPair (encKeyedInput encBits) encBits) encBits := by
    let qid := ComputableInPolyTime.id' (encIn := encPair (encKeyedInput encBits) encBits)
    exact hh.comp (qid.fst'.fst'.prod ((hkey.comp qid.fst').prod qid.snd'))
  have hstep_len : ∀ q : ℕ × List Bool × List Bool, ∀ w,
      w.length = outLen q.1 + s q.1 →
      (h q.1 (BitString.listRow (baseKeyLen q.1) 0 q.2.1) w).length = outLen q.1 :=
    fun q w hw => h_len q.1 _ w (BitString.length_listRow _ _ _) hw
  exact computableInPolyTime_shoupCascade (hout.comp hn) (hs.comp hn) (ht.comp hn) hstep
    hstep_len (ComputableInPolyTime.bitsDropWithInput hK (hbase.comp hn)) hx

private structure ShoupSavedState where
  iStar : ℕ
  x₀ : List Bool
  advState : List Bool
  T : List Bool

private enc_structure encShoupState : ShoupSavedState where
  iStar : encUnary,
  x₀ : encBits,
  advState : encBits,
  T : encBits

private def shoupStateDecoder : Decoder encShoupState :=
  (Decoder.unary.pair (Decoder.bits.pair (Decoder.bits.pair Decoder.bits))).map
    (fun (iStar, x₀, advState, T) => ⟨iStar, x₀, advState, T⟩)
    (fun s => (s.iStar, s.x₀, s.advState, s.T))
    (fun ⟨_, _, _, _⟩ => rfl)
    (fun _ => rfl)

/-- Pre-key target-selection stage of Shoup's Lemma 5.7 reduction (`[Shoup2000]`; `[HHRVW2020]`,
Section 5.1.4, Lemma 5.7, p. 30): samples a dyadic cascade step guess `rawSlot`, runs
`adversary.choose n`, draws a uniform mask-seed vector `T`, and outputs the `(outLen n + s n)`-bit
planted step target `w₀` together with the encoded state passed to `shoupComposeFindWith`. -/
noncomputable def shoupComposeChoose (outLen s t : ℕ → ℕ)
    (adversary : TargetCollisionFinder) (n : ℕ) : ProbComp (List Bool × List Bool) := do
  let rawSlot ← sampleDyadicIndex (t n)
  let choice ← adversary.choose n
  let T ← BitString.sampleList (shoupMasksLen (outLen n) (t n))
  let iStar := min (rawSlot + 1) (t n)
  let w₀ := BitString.listRow (outLen n) (padicValNat 2 iStar) T ++
    shoupChunk (outLen n) (s n) iStar choice.1
  return (w₀, encShoupState ⟨iStar, choice.1, choice.2, T⟩)

theorem length_fst_of_mem_support_shoupComposeChoose {outLen s t : ℕ → ℕ}
    {adversary : TargetCollisionFinder} {n : ℕ} {p : List Bool × List Bool}
    (hp : p ∈ (ProbComp.eval (shoupComposeChoose outLen s t adversary n)).support) :
    p.1.length = outLen n + s n := by
  simp only [shoupComposeChoose, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hp
  obtain ⟨_, _, _, _, _, _, rfl⟩ := hp
  simp only [List.length_append, BitString.length_listRow, length_shoupChunk]

theorem isPPTOn_shoupComposeChoose {outLen s t : ℕ → ℕ} {adversary : TargetCollisionFinder}
    (hout : ComputableInPolyTime outLen encUnary encUnary)
    (hs : ComputableInPolyTime s encUnary encUnary)
    (ht : ComputableInPolyTime t encUnary encUnary)
    (hchoose : IsPPTOn encUnary (encPair encBits encBits) adversary.choose) :
    IsPPTOn encUnary (encPair encBits encBits) (shoupComposeChoose outLen s t adversary) := by
  let encMid := encPair (encPair encUnary encUnary) (encPair encBits encBits)
  let encFin := encPair encMid encBits
  have hmidN := (ComputableInPolyTime.fst encUnary encUnary).comp
    (ComputableInPolyTime.fst (encPair encUnary encUnary) (encPair encBits encBits))
  have hfn := hmidN.comp (.fst encMid encBits)
  have hchoice := (ComputableInPolyTime.snd (encPair encUnary encUnary)
    (encPair encBits encBits)).comp (.fst encMid encBits)
  have hiS : ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × (List Bool × List Bool)) × List Bool =>
        min (q.1.1.2 + 1) (t q.1.1.1)) encFin encUnary := by fun_prop
  have hx0 := (ComputableInPolyTime.fst encBits encBits).comp hchoice
  have hst := (ComputableInPolyTime.snd encBits encBits).comp hchoice
  have hT := ComputableInPolyTime.snd encMid encBits
  have hw0 := ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsRowWithInput (hout.comp hfn)
      (ComputableInPolyTime.unary_padicValNat_two.comp hiS) hT)
    (ComputableInPolyTime.bitsRowWithInput (hs.comp hfn) (hiS.unary_sub' (.const 1))
      (ComputableInPolyTime.bitsDropWithInput hx0 (hout.comp hfn)))
  have hsE : ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × (List Bool × List Bool)) × List Bool =>
        encShoupState ⟨min (q.1.1.2 + 1) (t q.1.1.1), q.1.2.1, q.1.2.2, q.2⟩) encFin encBits :=
    (encShoupState_mk_polyTime hiS hx0 hst hT).of_enc_eq fun _ => rfl
  exact (isPPTOn_sampleDyadicIndex ht).bind_with
    ((hchoose.preprocess (ComputableInPolyTime.fst encUnary encUnary)).bind_with
      ((computableInPolyTime_shoupMasksLen (hout.comp hmidN) (ht.comp hmidN)).sampleList.bind_with
        (hw0.prod hsE).isPPTOn))

/-- Post-key collision-extraction stage of Shoup's Lemma 5.7 reduction (`[Shoup2000]`;
`[HHRVW2020]`, Section 5.1.4, Lemma 5.7, p. 30): decodes `savedState`, normalizes `k` to
`baseKeyLen` bits, reconstructs the masks via `shoupPackMasks` for `stepOfKey key`, runs
`adversary.find n st.advState (key ++ masks)`, and returns the step-`iStar` input. -/
noncomputable def shoupComposeFindWith (baseKeyLen outLen s t : ℕ)
    (stepOfKey : List Bool → List Bool → List Bool)
    (adversary : TargetCollisionFinder) (n : ℕ) (savedState k : List Bool) :
    ProbComp (List Bool) := do
  let st := shoupStateDecoder.decode savedState
  let key := BitString.listRow baseKeyLen 0 k
  let step := stepOfKey key
  let masks := shoupPackMasks outLen s t st.iStar step st.x₀ st.T
  let x₁ ← adversary.find n st.advState (key ++ masks)
  let prev := shoupState outLen s step masks x₁ (st.iStar - 1)
  return shoupStepInput outLen s masks x₁ st.iStar prev

theorem length_of_mem_support_shoupComposeFindWith {baseKeyLen outLen s t : ℕ}
    {stepOfKey : List Bool → List Bool → List Bool}
    {adversary : TargetCollisionFinder} {n : ℕ} {savedState k w₁ : List Bool}
    (hw₁ : w₁ ∈ (ProbComp.eval
      (shoupComposeFindWith baseKeyLen outLen s t stepOfKey adversary n savedState k)).support) :
    w₁.length = outLen + s := by
  simp only [shoupComposeFindWith, pmf_norm, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff] at hw₁
  obtain ⟨_, _, rfl⟩ := hw₁
  exact length_shoupStepInput _ _ _ _ _ _

theorem isPPTOn_shoupComposeFindWith
    {γ : Type} {encIn : γ ↪ List Bool}
    {baseKeyLen outLen s t n : γ → ℕ}
    {stepOfKey : γ → List Bool → List Bool → List Bool}
    {savedState k : γ → List Bool}
    {adversary : TargetCollisionFinder}
    (hbase : ComputableInPolyTime baseKeyLen encIn encUnary)
    (hout : ComputableInPolyTime outLen encIn encUnary)
    (hs : ComputableInPolyTime s encIn encUnary)
    (ht : ComputableInPolyTime t encIn encUnary)
    (hn : ComputableInPolyTime n encIn encUnary)
    (hstep_key : ComputableInPolyTime
      (fun q : γ × List Bool × List Bool => stepOfKey q.1 q.2.1 q.2.2)
      (encPair encIn (encPair encBits encBits)) encBits)
    (h_len : ∀ a key w, key.length = baseKeyLen a → w.length = outLen a + s a →
      (stepOfKey a key w).length = outLen a)
    (hsaved : ComputableInPolyTime savedState encIn encBits)
    (hk : ComputableInPolyTime k encIn encBits)
    (hfind : IsPPTOn (encPair encUnary (encPair encBits encBits)) encBits
      (fun ⟨m, st, key⟩ => adversary.find m st key)) :
    IsPPTOn encIn encBits fun a =>
      shoupComposeFindWith (baseKeyLen a) (outLen a) (s a) (t a) (stepOfKey a) adversary
        (n a) (savedState a) (k a) := by
  have _ : ComputableInPolyTime (fun a : γ => shoupStateDecoder.decode (savedState a))
      encIn encShoupState := shoupStateDecoder.computableInPolyTime.comp hsaved
  have hstep : ComputableInPolyTime
      (fun q : γ × List Bool => stepOfKey q.1 (BitString.listRow (baseKeyLen q.1) 0 (k q.1)) q.2)
      (encPair encIn encBits) encBits :=
    hstep_key.comp (by fun_prop : ComputableInPolyTime
      (fun q : γ × List Bool => (q.1, BitString.listRow (baseKeyLen q.1) 0 (k q.1), q.2))
      (encPair encIn encBits) (encPair encIn (encPair encBits encBits)))
  have hmasks : ComputableInPolyTime
      (fun a : γ =>
        let st := shoupStateDecoder.decode (savedState a)
        shoupPackMasks (outLen a) (s a) (t a) st.iStar
          (stepOfKey a (BitString.listRow (baseKeyLen a) 0 (k a))) st.x₀ st.T) encIn encBits :=
    computableInPolyTime_shoupPackMasks hout hs ht (by fun_prop) hstep
      (fun a w hw => h_len a _ w (BitString.length_listRow _ _ _) hw) (by fun_prop) (by fun_prop)
  let encQ := encPair encIn encBits
  have hqstep : ComputableInPolyTime
      (fun r : (γ × List Bool) × List Bool =>
        stepOfKey r.1.1 (BitString.listRow (baseKeyLen r.1.1) 0 (k r.1.1)) r.2)
      (encPair encQ encBits) encBits :=
    hstep.comp (by fun_prop : ComputableInPolyTime
      (fun r : (γ × List Bool) × List Bool => (r.1.1, r.2))
      (encPair encQ encBits) (encPair encIn encBits))
  have hqmasks := hmasks.comp (ComputableInPolyTime.fst encIn encBits)
  have hqprev : ComputableInPolyTime
      (fun r : γ × List Bool =>
        let st := shoupStateDecoder.decode (savedState r.1)
        let key := BitString.listRow (baseKeyLen r.1) 0 (k r.1)
        let step := stepOfKey r.1 key
        shoupState (outLen r.1) (s r.1) step
          (shoupPackMasks (outLen r.1) (s r.1) (t r.1) st.iStar step st.x₀ st.T)
          r.2 (st.iStar - 1)) encQ encBits :=
    computableInPolyTime_shoupState (by fun_prop) (by fun_prop) (by fun_prop) hqstep
      (fun r w hw => h_len r.1 _ w (BitString.length_listRow _ _ _) hw) hqmasks (by fun_prop)
  have hret : ComputableInPolyTime
      (fun r : γ × List Bool =>
        let st := shoupStateDecoder.decode (savedState r.1)
        let key := BitString.listRow (baseKeyLen r.1) 0 (k r.1)
        let step := stepOfKey r.1 key
        let masks := shoupPackMasks (outLen r.1) (s r.1) (t r.1) st.iStar step st.x₀ st.T
        shoupStepInput (outLen r.1) (s r.1) masks r.2 st.iStar
          (shoupState (outLen r.1) (s r.1) step masks r.2 (st.iStar - 1))) encQ encBits :=
    computableInPolyTime_shoupStepInput (by fun_prop) (by fun_prop) hqmasks (by fun_prop)
      (by fun_prop) hqprev
  have harg : ComputableInPolyTime (fun a : γ =>
      (n a, (shoupStateDecoder.decode (savedState a)).advState,
        BitString.listRow (baseKeyLen a) 0 (k a) ++
          shoupPackMasks (outLen a) (s a) (t a) (shoupStateDecoder.decode (savedState a)).iStar
            (stepOfKey a (BitString.listRow (baseKeyLen a) 0 (k a)))
            (shoupStateDecoder.decode (savedState a)).x₀
            (shoupStateDecoder.decode (savedState a)).T))
      encIn (encKeyedInput encBits) :=
    hn.prod ((by fun_prop : ComputableInPolyTime
      (fun a : γ => (shoupStateDecoder.decode (savedState a)).advState) encIn encBits).prod
      (ComputableInPolyTime.bitsAppend (by fun_prop) hmasks))
  exact (hfind.preprocess harg).bind_with hret.isPPTOn

/-- Reduction adversary turning a target collision finder on `shoupComposeEval` into a target
collision finder on the underlying shrinking compression function `h`, guessing the colliding step
`1 ≤ iStar ≤ t n` and reconstructing the `log t`-mask vector via `shoupPackMasks` (`[Shoup2000]`;
`[HHRVW2020]`, Section 5.1.4, Lemma 5.7, p. 30). -/
@[expose] noncomputable def shoupComposeAdversary
    (baseKeyLen outLen s t : ℕ → ℕ)
    (h : ℕ → List Bool → List Bool → List Bool)
    (adversary : TargetCollisionFinder) : TargetCollisionFinder where
  choose := shoupComposeChoose outLen s t adversary
  find n savedState k :=
    shoupComposeFindWith (baseKeyLen n) (outLen n) (s n) (t n) (h n) adversary n savedState k

/-- `shoupComposeAdversary` is uniformly strict PPT whenever `adversary` is strict PPT and all
parameters and `h` are polynomial time. -/
theorem isPPT_shoupComposeAdversary
    {baseKeyLen outLen s t : ℕ → ℕ}
    {h : ℕ → List Bool → List Bool → List Bool}
    {adversary : TargetCollisionFinder}
    (hbase : ComputableInPolyTime baseKeyLen encUnary encUnary)
    (hout : ComputableInPolyTime outLen encUnary encUnary)
    (hs : ComputableInPolyTime s encUnary encUnary)
    (ht : ComputableInPolyTime t encUnary encUnary)
    (hh : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => h p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) encBits)
    (h_len : ∀ n k w, k.length = baseKeyLen n → w.length = outLen n + s n →
      (h n k w).length = outLen n)
    (ha : adversary.IsPPT) :
    (shoupComposeAdversary baseKeyLen outLen s t h adversary).IsPPT := by
  refine ⟨isPPTOn_shoupComposeChoose hout hs ht ha.choose, ?_⟩
  let encP := encKeyedInput encBits
  have hstep_key : ComputableInPolyTime
      (fun q : (ℕ × List Bool × List Bool) × List Bool × List Bool => h q.1.1 q.2.1 q.2.2)
      (encPair encP (encPair encBits encBits)) encBits :=
    hh.comp (by fun_prop : ComputableInPolyTime
      (fun q : (ℕ × List Bool × List Bool) × List Bool × List Bool => (q.1.1, q.2))
      (encPair encP (encPair encBits encBits)) encP)
  exact isPPTOn_shoupComposeFindWith (encIn := encP)
    (baseKeyLen := fun p : ℕ × List Bool × List Bool => baseKeyLen p.1)
    (outLen := fun p => outLen p.1) (s := fun p => s p.1) (t := fun p => t p.1) (n := fun p => p.1)
    (savedState := fun p => p.2.1) (k := fun p => p.2.2)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    hstep_key (fun p => h_len p.1) (by fun_prop) (by fun_prop) ha.find

private noncomputable def shoupTargetDist (baseKeyLen outLen t : ℕ → ℕ)
    (adversary : TargetCollisionFinder) (n : ℕ) :
    PMF ((List Bool × List Bool) × List Bool × List Bool) := do
  let choice ← ProbComp.eval (adversary.choose n)
  let K ← BitString.uniformList (shoupComposeKeyLen baseKeyLen outLen t n)
  (ProbComp.eval (adversary.find n choice.2 K)).map fun x₁ => (choice, K, x₁)

private noncomputable def shoupSlotTrial (baseKeyLen outLen s t : ℕ → ℕ)
    (h : ℕ → List Bool → List Bool → List Bool) (adversary : TargetCollisionFinder)
    (n rawSlot : ℕ) : Game := do
  let iStar := min (rawSlot + 1) (t n)
  let choice ← ProbComp.eval (adversary.choose n)
  let T ← BitString.uniformList (shoupMasksLen (outLen n) (t n))
  let k ← BitString.uniformList (baseKeyLen n)
  let step := h n (BitString.listRow (baseKeyLen n) 0 k)
  let masks := shoupPackMasks (outLen n) (s n) (t n) iStar step choice.1 T
  let x₁ ← ProbComp.eval (adversary.find n choice.2 (BitString.listRow (baseKeyLen n) 0 k ++ masks))
  let w₀ := BitString.listRow (outLen n) (padicValNat 2 iStar) T ++
    shoupChunk (outLen n) (s n) iStar choice.1
  let w₁ := shoupStepInput (outLen n) (s n) masks x₁ iStar
    (shoupState (outLen n) (s n) step masks x₁ (iStar - 1))
  PMF.pure (isCollision (h n) (fun m w => w.length == outLen m + s m) n k w₀ w₁)

private def shoupSlotWin (baseKeyLen outLen s t : ℕ → ℕ)
    (h : ℕ → List Bool → List Bool → List Bool) (n rawSlot : ℕ)
    (tup : (List Bool × List Bool) × List Bool × List Bool) : Bool :=
  if rawSlot < t n then
    let iStar := rawSlot + 1
    let k := BitString.listRow (baseKeyLen n) 0 tup.2.1
    let masks := tup.2.1.drop (baseKeyLen n)
    isCollision (h n) (fun m w => w.length == outLen m + s m) n k
      (shoupStepInput (outLen n) (s n) masks tup.1.1 iStar
        (shoupState (outLen n) (s n) (h n k) masks tup.1.1 (iStar - 1)))
      (shoupStepInput (outLen n) (s n) masks tup.2.2 iStar
        (shoupState (outLen n) (s n) (h n k) masks tup.2.2 (iStar - 1)))
  else false

private theorem shoupSlotTrial_eq_map {baseKeyLen outLen s t : ℕ → ℕ}
    {h : ℕ → List Bool → List Bool → List Bool} (adversary : TargetCollisionFinder)
    {n rawSlot : ℕ} (hraw : rawSlot < t n)
    (h_len : ∀ k w, k.length = baseKeyLen n → w.length = outLen n + s n →
      (h n k w).length = outLen n) :
    shoupSlotTrial baseKeyLen outLen s t h adversary n rawSlot =
      (shoupTargetDist baseKeyLen outLen t adversary n).map
        (shoupSlotWin baseKeyLen outLen s t h n rawSlot) := by
  set iStar := rawSlot + 1
  simp only [shoupSlotTrial, shoupTargetDist, Nat.min_eq_left (Nat.succ_le_of_lt hraw), pmf_norm]
  refine PMF.bind_congr_on_support _ _ _ fun choice _ => ?_
  rw [PMF.bind_comm (BitString.uniformList (shoupMasksLen (outLen n) (t n)))
    (BitString.uniformList (baseKeyLen n))]
  have hsplit : (BitString.uniformList (shoupComposeKeyLen baseKeyLen outLen t n)).bind
      (fun K => (ProbComp.eval (adversary.find n choice.2 K)).map fun x₁ =>
        shoupSlotWin baseKeyLen outLen s t h n rawSlot (choice, K, x₁)) =
      (BitString.uniformList (baseKeyLen n)).bind fun k =>
        (BitString.uniformList (shoupMasksLen (outLen n) (t n))).bind fun masks =>
          (ProbComp.eval (adversary.find n choice.2 (k ++ masks))).map fun x₁ =>
            shoupSlotWin baseKeyLen outLen s t h n rawSlot (choice, k ++ masks, x₁) := by
    rw [show shoupComposeKeyLen baseKeyLen outLen t n =
      baseKeyLen n + shoupMasksLen (outLen n) (t n) from rfl]
    refine (PMF.bind_congr_on_support _ _ _ fun K _ => ?_).trans
      (BitString.uniformList_bind_split (baseKeyLen n) (shoupMasksLen (outLen n) (t n))
        fun k masks => (ProbComp.eval (adversary.find n choice.2 (k ++ masks))).map fun x₁ =>
          shoupSlotWin baseKeyLen outLen s t h n rawSlot (choice, k ++ masks, x₁))
    conv_rhs => rw [List.take_append_drop]
  simp only [PMF.map] at hsplit ⊢
  rw [hsplit]
  refine PMF.bind_congr_on_support _ _ _ fun k hk_supp => ?_
  have hk_len : k.length = baseKeyLen n := BitString.length_of_mem_support_uniformList hk_supp
  have hrow_k : BitString.listRow (baseKeyLen n) 0 k = k := by
    rw [BitString.listRow_zero, BitString.ofFn_ofList hk_len]
  have hpack := uniformList_map_shoupPackMasks (outLen n) (s n) (t n) iStar (h n k)
    (fun w hw => h_len k w hk_len hw) (Nat.succ_pos _) hraw choice.1
  calc _ = ((BitString.uniformList (shoupMasksLen (outLen n) (t n))).map
          (shoupPackMasks (outLen n) (s n) (t n) iStar (h n k) choice.1)).bind fun masks =>
          (ProbComp.eval (adversary.find n choice.2 (k ++ masks))).bind fun x₁ =>
            PMF.pure (isCollision (h n) (fun m w => w.length == outLen m + s m) n k
              (shoupStepInput (outLen n) (s n) masks choice.1 iStar
                (shoupState (outLen n) (s n) (h n k) masks choice.1 (iStar - 1)))
              (shoupStepInput (outLen n) (s n) masks x₁ iStar
                (shoupState (outLen n) (s n) (h n k) masks x₁ (iStar - 1)))) := by
        rw [PMF.bind_map]
        refine PMF.bind_congr_on_support _ _ _ fun T _ => by
          dsimp only [Function.comp_apply]
          simp only [hrow_k]
          rw [← shoupStepInput_shoupPackMasks (h n k) (fun w hw => h_len k w hk_len hw)
            (Nat.succ_pos _) hraw choice.1 T]
      _ = _ := by
        rw [hpack]
        refine PMF.bind_congr_on_support _ _ _ fun masks _ => ?_
        have hkm : BitString.listRow (baseKeyLen n) 0 (k ++ masks) = k := by
          rw [BitString.listRow_zero, BitString.ofFn_ofList_eq_take,
            List.take_append_of_le_length (by simp [hk_len]), List.take_left' hk_len]
        simp only [shoupSlotWin, hraw, ↓reduceIte, List.drop_left' hk_len, hkm]
        rfl

/-- **Concrete `[Shoup2000]` / `[HHRVW2020]` Lemma 5.7 reduction**: the target-collision
advantage of `adversary` against `shoupComposeEval` on `L n`-bit inputs (`outLen n ≤ L n ≤
outLen n + t n * s n`) is at most `dyadicSize (t n)` times the target-collision advantage of
`shoupComposeAdversary` against `h` on `(outLen n + s n)`-bit inputs. -/
theorem succProbability_targetCollisionGame_shoupCompose_le
    {baseKeyLen outLen s t L : ℕ → ℕ}
    {h : ℕ → List Bool → List Bool → List Bool}
    (adversary : TargetCollisionFinder) (n : ℕ)
    (hs_pos : 1 ≤ s n)
    (hb_le : outLen n ≤ L n) (hL_le : L n ≤ outLen n + t n * s n)
    (h_len : ∀ k w, k.length = baseKeyLen n → w.length = outLen n + s n →
      (h n k w).length = outLen n) :
    Game.succProbability
      (ProbComp.eval
        (targetCollisionGame (shoupComposeKeyLen baseKeyLen outLen t)
          (shoupComposeEval baseKeyLen outLen s t h)
          (fun m x => x.length == L m) adversary n)) ≤
      (dyadicSize (t n) : ℝ≥0) *
        Game.succProbability
          (ProbComp.eval
            (targetCollisionGame baseKeyLen h
              (fun m w => w.length == outLen m + s m)
              (shoupComposeAdversary baseKeyLen outLen s t h adversary) n)) := by
  set D := dyadicSize (t n)
  set μ := shoupTargetDist baseKeyLen outLen t adversary n
  let winComp (tup : (List Bool × List Bool) × List Bool × List Bool) : Bool :=
    isCollision (shoupComposeEval baseKeyLen outLen s t h n) (fun m x => x.length == L m) n
      tup.2.1 tup.1.1 tup.2.2
  have hcomp_eq : ProbComp.eval (targetCollisionGame (shoupComposeKeyLen baseKeyLen outLen t)
      (shoupComposeEval baseKeyLen outLen s t h) (fun m x => x.length == L m) adversary n) =
      μ.map winComp := by
    simp only [targetCollisionGame, μ, shoupTargetDist, winComp, BitString.eval_sampleList,
      pmf_norm, PMF.map]
  have hred_eq : ProbComp.eval (targetCollisionGame baseKeyLen h
      (fun m w => w.length == outLen m + s m)
      (shoupComposeAdversary baseKeyLen outLen s t h adversary) n) =
      (PMF.uniformOfFintype (Fin D)).bind fun a =>
        shoupSlotTrial baseKeyLen outLen s t h adversary n a.val := by
    simp only [targetCollisionGame, shoupComposeAdversary, shoupComposeChoose,
      shoupComposeFindWith, shoupSlotTrial, eval_sampleDyadicIndex, BitString.eval_sampleList,
      shoupStateDecoder.decode_enc, pmf_norm, PMF.map, Function.comp_def]
    rfl
  have hcover : ∀ tup ∈ μ.support, winComp tup = true →
      (List.range D).any (fun r => shoupSlotWin baseKeyLen outLen s t h n r tup) = true := by
    rintro ⟨choice, K, x₁⟩ _ hW
    obtain ⟨hx₀, hx₁, hne, hcol⟩ := isCollision_eq_true_iff.mp hW
    obtain ⟨i, hi_pos, hi_le, hw_ne, hw_col⟩ := exists_shoupCascade_step_collision
      hs_pos hb_le hL_le (h n (BitString.listRow (baseKeyLen n) 0 K))
      (fun w => h_len _ w (BitString.length_listRow _ 0 K)) (K.drop (baseKeyLen n))
      choice.1 x₁ (by simpa only [beq_iff_eq] using hx₀) (by simpa only [beq_iff_eq] using hx₁)
      hne hcol
    refine List.any_eq_true.mpr ⟨i - 1, List.mem_range.mpr ((by omega : i - 1 < t n).trans
      (lt_dyadicSize (t n))), ?_⟩
    simp only [shoupSlotWin, show i - 1 < t n by omega, ↓reduceIte,
      show i - 1 + 1 = i by omega, isCollision_eq_true_iff, beq_iff_eq,
      length_shoupStepInput, true_and]
    exact ⟨hw_ne, hw_col⟩
  have hsum : (μ.map winComp) true ≤
      ∑ r : Fin D, (shoupSlotTrial baseKeyLen outLen s t h adversary n r.val) true := by
    refine ((PMF.map_true_mono μ hcover).trans
      (PMF.map_any_range_true_le_sum μ D (shoupSlotWin baseKeyLen outLen s t h n))).trans ?_
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_le_sum fun r hr => ?_
    simp only [Finset.mem_range.mp hr, ↓reduceDIte]
    by_cases hraw : r < t n
    · rw [shoupSlotTrial_eq_map adversary hraw h_len]
    · have hWi : (μ.map (shoupSlotWin baseKeyLen outLen s t h n r)) true = 0 :=
        (PMF.apply_eq_zero_iff _ _).mpr fun hm => by
          obtain ⟨_, -, h⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
          simp only [shoupSlotWin, hraw, ↓reduceIte, Bool.false_eq_true] at h
      rw [hWi]; exact zero_le
  have : Nonempty (Fin D) := ⟨⟨0, dyadicSize_pos (t n)⟩⟩
  have hpos : (D : ℝ≥0) ≠ 0 := by exact_mod_cast (dyadicSize_pos (t n)).ne'
  rw [hcomp_eq, hred_eq, Game.succProbability_uniform, Fintype.card_fin, mul_div_cancel₀ _ hpos]
  calc Game.succProbability (μ.map winComp)
      ≤ (∑ r : Fin D, (shoupSlotTrial baseKeyLen outLen s t h adversary n r.val) true).toNNReal :=
        ENNReal.toNNReal_mono (ENNReal.sum_lt_top.mpr fun r _ =>
          (PMF.apply_ne_top _ _).lt_top).ne hsum
    _ = ∑ r : Fin D,
          Game.succProbability (shoupSlotTrial baseKeyLen outLen s t h adversary n r.val) :=
        ENNReal.toNNReal_sum fun r _ => PMF.apply_ne_top _ _

/-- **Asymptotic `[Shoup2000]` / `[HHRVW2020]` Lemma 5.7**: if `h` is target collision
resistant on `(outLen n + s n)`-bit inputs with `1 ≤ s n` and `outLen n ≤ L n ≤
outLen n + t n * s n`, then `shoupComposeEval` is target collision resistant on `L n`-bit inputs
with compact key length `baseKeyLen n + (Nat.log 2 (t n) + 1) * outLen n`. -/
theorem targetCollisionResistantOn_shoupCompose
    {baseKeyLen outLen s t L : ℕ → ℕ}
    {h : ℕ → List Bool → List Bool → List Bool}
    (hbase : ComputableInPolyTime baseKeyLen encUnary encUnary)
    (hout : ComputableInPolyTime outLen encUnary encUnary)
    (hs : ComputableInPolyTime s encUnary encUnary)
    (ht : ComputableInPolyTime t encUnary encUnary)
    (hh : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => h p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) encBits)
    (hs_pos : ∀ n, 1 ≤ s n)
    (hb_le : ∀ n, outLen n ≤ L n) (hL_le : ∀ n, L n ≤ outLen n + t n * s n)
    (h_len : ∀ n k w, k.length = baseKeyLen n → w.length = outLen n + s n →
      (h n k w).length = outLen n)
    (hTCR : TargetCollisionResistantOn baseKeyLen h (fun m w => w.length == outLen m + s m)) :
    TargetCollisionResistantOn (shoupComposeKeyLen baseKeyLen outLen t)
      (shoupComposeEval baseKeyLen outLen s t h) (fun m x => x.length == L m) := by
  apply TargetCollisionResistantOn.of_negligible
  intro adversary hadversary
  have hred_ppt : (shoupComposeAdversary baseKeyLen outLen s t h adversary).IsPPT :=
    isPPT_shoupComposeAdversary hbase hout hs ht hh h_len hadversary
  have hneg := hTCR.negligible (shoupComposeAdversary baseKeyLen outLen s t h adversary) hred_ppt
  have hloss : PolynomiallyBounded (fun n => dyadicSize (t n)) :=
    dyadicSize_polynomiallyBounded.comp ht.polynomiallyBounded
  refine negligible_of_le (hneg.polynomiallyBounded_mul hloss) fun n => ?_
  exact succProbability_targetCollisionGame_shoupCompose_le adversary n
    (hs_pos n) (hb_le n) (hL_le n) (h_len n)

end Cslib.Crypto
