/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.ConfigurationMatrix
public import CslibFrontier.Probability.SaksZhou.Nisan
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Saks–Zhou iteration for randomized logarithmic space

Connects the configuration transition matrix of a fair-coin logspace machine
(`Turing.MultiTapePTM.configMatrix`) to the Nisan-powered Saks–Zhou rounding iteration
(`Cslib.Probability.SaksZhou.dens_snapIter_bitNisanPow_far_le`). For a `BPL` language, the machine
has at most `2 ^ R` reachable views with `R = O(log n)` (`exists_finset_reachable`), so setting
`s = ⌊√R⌋ + 1` levels (`2 ^ (s * s) ≥ 2 ^ R`), `d = 5 R + 5` bits of rounding precision, and
`m = 5 d` gives `bitNisanPow (2 * m) s` iterated `s` times with shared Toeplitz-Nisan hash seeds
and `s` fresh rounding shifts totaling `O(log^{3/2} n)` bits
(`Cslib.Complexity.exists_saksZhouSeeds_of_mem_BPL`).

Only the combinatorial probability and seed-length milestone is proved here:
`exists_saksZhouSeeds_of_mem_BPL` is a step toward `BPL ⊆ DSPACE(log^{3/2} n)`
([#459](https://github.com/cslib-community/cslib-frontier/issues/459),
[#3247](https://github.com/cslib-community/cslib-frontier/issues/3247)), not that space-bounded
inclusion, which additionally requires evaluating `snapIter` of `bitNisanPow` recursively in space
`O(log^{3/2} n)`.

## Main definitions

* `Turing.MultiTapePTM.saksZhouAcceptEst`: the `(init, accept)` vector contraction of the
  Nisan-powered Saks–Zhou iterate of `(1/2) • configMatrix`.

## Main results

* `Turing.MultiTapePTM.dens_saksZhouAcceptEst_far_le`: all but a small fraction of
  `NisanShiftSeed (2 * m) s s d` pairs estimate the `(2 ^ (s * s))`-step acceptance probability
  within `2 ^ (s * s) * |V| * 2 ^ (1 - d)`.
* `Cslib.Complexity.exists_saksZhouSeeds_of_mem_BPL`: a `BPL` language is separated with strict
  majority over `O(log^{3/2} n)`-bit `(hs, z)` pairs of `saksZhouAcceptEst`.

## References

* [N. Nisan, *Pseudorandom generators for space-bounded computation*][Nisan1992]
* [M. Saks and S. Zhou, *BP_H SPACE(S) ⊆ DSPACE(S^{3/2})*][SaksZhou1999]: publisher copy not
  consulted.
* [E. Chattopadhyay and J.-J. Liao, *Optimal Error Pseudodistributions for Read-Once Branching
  Programs*][ChattopadhyayLiao2020], arXiv v4, Appendix A.1
* [W. M. Hoza, *Better Pseudodistributions and Derandomization for Space-Bounded
  Computation*][Hoza2021], Appendix A
-/

public section

namespace Turing.MultiTapePTM

open Cslib Cslib.BitString Cslib.Probability.SaksZhou Matrix

section Estimate

variable {k : ℕ} {State : Type} (machine : MultiTapePTM k Bool State)

private theorem smul_configMatrix_nonneg (V : Finset (FiniteCfg k Bool State)) (x y : V) :
    0 ≤ ((2 : ℝ)⁻¹ • machine.configMatrix ℝ V) x y := by
  classical
  simp only [Matrix.smul_apply, smul_eq_mul, configMatrix, Matrix.coinStepMatrix]
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun b _ => ?_)
  split_ifs <;> norm_num

private theorem sum_smul_configMatrix_eq_one {V : Finset (FiniteCfg k Bool State)}
    (hV : ∀ finite ∈ V, ∀ bit, machine.viewCoinStep finite bit ∈ V) (x : V) :
    ∑ y, ((2 : ℝ)⁻¹ • machine.configMatrix ℝ V) x y = 1 := by
  classical
  have hmv := Matrix.coinStepMatrix_mulVec (R := ℝ) hV (fun _ => (1 : ℝ)) x
  simp only [Matrix.mulVec, dotProduct, mul_one, Fintype.sum_bool, one_add_one_eq_two] at hmv
  simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, configMatrix, hmv]
  norm_num

private theorem exists_smul_configMatrix_mul_card_eq {V : Finset (FiniteCfg k Bool State)}
    {m : ℕ} (hm : 1 ≤ m) (x y : V) :
    ∃ c : ℕ, ((2 : ℝ)⁻¹ • machine.configMatrix ℝ V) x y *
      Fintype.card (BitString (2 * m)) = c := by
  classical
  let cnt : ℕ :=
    ∑ b : Bool, if machine.viewCoinStep (x : FiniteCfg k Bool State) b = y then 1 else 0
  refine ⟨cnt * 2 ^ (2 * m - 1), ?_⟩
  have hcard : Fintype.card (BitString (2 * m)) = 2 ^ (2 * m) := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hpow : (2 : ℕ) ^ (2 * m) = 2 * 2 ^ (2 * m - 1) := by
    rw [← pow_succ', show 2 * m - 1 + 1 = 2 * m by omega]
  have hentry : machine.configMatrix ℝ V x y = (cnt : ℝ) := by
    simp only [configMatrix, Matrix.coinStepMatrix, cnt]
    push_cast
    rfl
  rw [Matrix.smul_apply, smul_eq_mul, hentry, hcard, hpow]
  push_cast
  ring

open scoped Classical in
/-- The Saks–Zhou acceptance probability estimate at parameters `(m, s, d)` on seed-shift pair
`p : NisanShiftSeed (2 * m) s s d`: the entry at the initial view of
`snapIter d (bitNisanPow (2 * m) s · p.1) ((2 : ℝ)⁻¹ • machine.configMatrix ℝ V) s p.2 *ᵥ
acceptVec`. -/
noncomputable def saksZhouAcceptEst {input : List Bool} (V : Finset (FiniteCfg k Bool State))
    (hinit : machine.toNTM.initView input ∈ V) (m s d : ℕ)
    (p : NisanShiftSeed (2 * m) s s d) : ℝ :=
  (snapIter d (fun B => bitNisanPow (2 * m) s B p.1)
    ((2 : ℝ)⁻¹ • machine.configMatrix ℝ V) s p.2 *ᵥ FiniteCfg.acceptVec ℝ V) ⟨_, hinit⟩

private theorem abs_mulVec_acceptVec_sub_le {V : Finset (FiniteCfg k Bool State)}
    (Q R : Matrix V V ℝ) (x : V) :
    |(Q *ᵥ FiniteCfg.acceptVec ℝ V) x - (R *ᵥ FiniteCfg.acceptVec ℝ V) x| ≤
      ∑ y, |Q x y - R x y| := by
  simp only [Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib, ← sub_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [abs_mul]
  have hacc : |FiniteCfg.acceptVec ℝ V y| ≤ 1 := by
    simp only [FiniteCfg.acceptVec]
    split_ifs <;> norm_num
  exact mul_le_of_le_one_right (abs_nonneg _) hacc

/-- **High-probability accuracy of `saksZhouAcceptEst`**: for `1 ≤ s`, `1 ≤ m`, `d ≤ 2 * m`, and
`(|V| + 1) * ((2 ^ s - 1) * (|V| + 1) / 2 ^ m) ≤ ε ^ 2`, all but an
`s * (ε + |V| ^ 2 * (2 ^ d * ε + 2 ^ (-d)))` fraction of `NisanShiftSeed (2 * m) s s d` pairs
produce a `saksZhouAcceptEst` within `2 ^ (s * s) * |V| * 2 ^ (1 - d)` of
`acceptCoins input (2 ^ (s * s)) / 2 ^ (2 ^ (s * s))`. -/
theorem dens_saksZhouAcceptEst_far_le {input : List Bool} {V : Finset (FiniteCfg k Bool State)}
    (hV : ∀ finite ∈ V, ∀ bit, machine.viewCoinStep finite bit ∈ V)
    (hinit : machine.toNTM.initView input ∈ V) {m s d : ℕ} (hs : 1 ≤ s) (hm : 1 ≤ m)
    (hdm : d ≤ 2 * m) {ε : ℝ} (hε : 0 < ε)
    (herr : (V.card + 1 : ℝ) * ((2 ^ s - 1) * (V.card + 1) / 2 ^ m) ≤ ε ^ 2) :
    (Finset.dens (Finset.univ.filter fun p : NisanShiftSeed (2 * m) s s d =>
        (2 : ℝ) ^ (s * s) * (V.card * (2 / 2 ^ d)) <
          |machine.saksZhouAcceptEst V hinit m s d p -
            (machine.acceptCoins input (2 ^ (s * s)) : ℝ) / 2 ^ (2 ^ (s * s))|) : ℝ) ≤
      s * (ε + V.card ^ 2 * (2 ^ d * ε + (2 ^ d)⁻¹)) := by
  classical
  let P : Matrix V V ℝ := (2 : ℝ)⁻¹ • machine.configMatrix ℝ V
  have h0 : ∀ x y, 0 ≤ P x y := smul_configMatrix_nonneg machine V
  have h1 : ∀ x, ∑ y, P x y ≤ 1 := fun x => (sum_smul_configMatrix_eq_one machine hV x).le
  have hM : ∀ x y, ∃ c : ℕ, P x y * Fintype.card (BitString (2 * m)) = c :=
    exists_smul_configMatrix_mul_card_eq machine hm
  have herr' : (Fintype.card V + 1 : ℝ) *
      ((2 ^ s - 1) * (Fintype.card V + 1) / 2 ^ m) ≤ ε ^ 2 := by
    simpa only [Fintype.card_coe] using herr
  have hsz := dens_snapIter_bitNisanPow_far_le d m s s hs hdm h0 h1 hM hε herr'
  have hacc : (machine.acceptCoins input (2 ^ (s * s)) : ℝ) / 2 ^ (2 ^ (s * s)) =
      (P ^ 2 ^ (s * s) *ᵥ FiniteCfg.acceptVec ℝ V) ⟨_, hinit⟩ :=
    machine.acceptCoins_div_eq_configMatrix_pow_mulVec ℝ hV hinit (2 ^ (s * s))
  have hsub : (Finset.univ.filter fun p : NisanShiftSeed (2 * m) s s d =>
        (2 : ℝ) ^ (s * s) * (V.card * (2 / 2 ^ d)) <
          |machine.saksZhouAcceptEst V hinit m s d p -
            (machine.acceptCoins input (2 ^ (s * s)) : ℝ) / 2 ^ (2 ^ (s * s))|) ⊆
      rowFarSet ((2 : ℝ) ^ (s * s) * (Fintype.card V * (2 / 2 ^ d)))
        (fun p : NisanShiftSeed (2 * m) s s d =>
          snapIter d (fun B => bitNisanPow (2 * m) s B p.1) P s p.2) (P ^ 2 ^ (s * s)) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [mem_rowFarSet]
    refine ⟨⟨_, hinit⟩, lt_of_lt_of_le ?_ (abs_mulVec_acceptVec_sub_le _ _ _)⟩
    simpa only [Fintype.card_coe, saksZhouAcceptEst, hacc] using hp.2
  calc (Finset.dens (Finset.univ.filter fun p : NisanShiftSeed (2 * m) s s d =>
          (2 : ℝ) ^ (s * s) * (V.card * (2 / 2 ^ d)) <
            |machine.saksZhouAcceptEst V hinit m s d p -
              (machine.acceptCoins input (2 ^ (s * s)) : ℝ) / 2 ^ (2 ^ (s * s))|) : ℝ)
      ≤ _ := NNRat.cast_le.2 (Finset.dens_le_dens hsub)
    _ ≤ s * (ε + Fintype.card V ^ 2 * (2 ^ d * ε + (2 ^ d)⁻¹)) := hsz
    _ = s * (ε + V.card ^ 2 * (2 ^ d * ε + (2 ^ d)⁻¹)) := by rw [Fintype.card_coe]

end Estimate

end Turing.MultiTapePTM

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapePTM Cslib.Probability.SaksZhou

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

private theorem saksZhou_seed_budget_le (clk ℓ : ℕ) :
    let R := clk * (ℓ + 2) + 1
    let s := Nat.sqrt R + 1
    let d := 5 * R + 5
    let m := 5 * d
    s * (3 * (2 * m) - 1) + s * d ≤
      155 * (2 * clk + 2) ^ 2 * (ℓ + 1) * (Nat.sqrt (ℓ + 1) + 1) := by
  intro R s d m
  have hR_le : R ≤ (2 * clk + 1) * (ℓ + 1) := by
    dsimp only [R]
    nlinarith
  have hR1_le : R + 1 ≤ (2 * clk + 2) * (ℓ + 1) := by
    dsimp only [R]
    nlinarith
  have hlt_sqrt : R < ((2 * clk + 2) * (Nat.sqrt (ℓ + 1) + 1)) ^ 2 := by
    have h1 : ℓ + 1 < (Nat.sqrt (ℓ + 1) + 1) ^ 2 := by
      simpa only [sq] using Nat.lt_succ_sqrt (ℓ + 1)
    have h2 : 2 * clk + 1 ≤ (2 * clk + 2) ^ 2 := by nlinarith
    calc R ≤ (2 * clk + 1) * (ℓ + 1) := hR_le
      _ < (2 * clk + 2) ^ 2 * (Nat.sqrt (ℓ + 1) + 1) ^ 2 := by nlinarith
      _ = ((2 * clk + 2) * (Nat.sqrt (ℓ + 1) + 1)) ^ 2 := by ring
  have hs_le : s ≤ (2 * clk + 2) * (Nat.sqrt (ℓ + 1) + 1) := by
    have hsq : Nat.sqrt R ^ 2 ≤ R := by simpa only [sq] using Nat.sqrt_le R
    have hlt : Nat.sqrt R < (2 * clk + 2) * (Nat.sqrt (ℓ + 1) + 1) := by
      by_contra hge
      have hge' : (2 * clk + 2) * (Nat.sqrt (ℓ + 1) + 1) ≤ Nat.sqrt R := not_lt.1 hge
      have hsq2 := Nat.mul_le_mul hge' hge'
      rw [← sq, ← sq] at hsq2
      omega
    dsimp only [s]
    omega
  have hm_eq : 3 * (2 * m) - 1 + d ≤ 155 * (R + 1) := by
    dsimp only [m, d]
    omega
  calc s * (3 * (2 * m) - 1) + s * d
      = s * (3 * (2 * m) - 1 + d) := by ring
    _ ≤ s * (155 * (R + 1)) := Nat.mul_le_mul_left s hm_eq
    _ ≤ ((2 * clk + 2) * (Nat.sqrt (ℓ + 1) + 1)) * (155 * ((2 * clk + 2) * (ℓ + 1))) :=
        Nat.mul_le_mul hs_le (Nat.mul_le_mul_left 155 hR1_le)
    _ = 155 * (2 * clk + 2) ^ 2 * (ℓ + 1) * (Nat.sqrt (ℓ + 1) + 1) := by ring

private theorem dens_sdiff_subset_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (bad good : Finset Ω) (hsub : Finset.univ \ good ⊆ bad) (hbad : (bad.dens : ℝ) ≤ 1 / 8) :
    (1 : ℝ) / 2 < (good.dens : ℝ) := by
  have hcompl : ((Finset.univ \ good).dens : ℝ) ≤ 1 / 8 :=
    (NNRat.cast_le.2 (Finset.dens_le_dens hsub)).trans hbad
  have h0 : 0 < Fintype.card Ω := Fintype.card_pos
  have hsum : (good.dens : ℝ) + ((Finset.univ \ good).dens : ℝ) = 1 := by
    have hadd : ((Finset.univ \ good).card : ℝ) + good.card = Fintype.card Ω := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card (Finset.subset_univ good)
    simp only [Finset.dens, NNRat.cast_div, NNRat.cast_natCast]
    rw [← add_div, show (good.card : ℝ) + (Finset.univ \ good).card = Fintype.card Ω by linarith,
      div_self (by exact_mod_cast h0.ne')]
  linarith

private theorem saksZhou_one_step_error_le (R d : ℕ) (hR : 1 ≤ R) (hd : d = 5 * R + 5)
    (s Vcard : ℕ) (hs : s = Nat.sqrt R + 1) (hVcard : Vcard ≤ 2 ^ R) :
    (2 : ℝ) ^ (s * s) * ((Vcard : ℝ) * (2 / 2 ^ d)) ≤ 1 / 16 := by
  have hs2 : s * s ≤ 3 * R + 1 := by
    have h1 : Nat.sqrt R * Nat.sqrt R ≤ R := Nat.sqrt_le R
    have h2 : Nat.sqrt R ≤ R := Nat.sqrt_le_self R
    rw [hs]
    nlinarith
  have hnum1 : (2 : ℝ) ^ (s * s) ≤ 2 ^ (3 * R + 1) :=
    pow_le_pow_right₀ (by norm_num) hs2
  have hnum2 : (Vcard : ℝ) ≤ 2 ^ R := by exact_mod_cast hVcard
  have hden : (2 : ℝ) ^ (4 * R + 6) ≤ 2 ^ d := by
    apply pow_le_pow_right₀ (by norm_num)
    omega
  calc (2 : ℝ) ^ (s * s) * ((Vcard : ℝ) * (2 / 2 ^ d))
      ≤ 2 ^ (3 * R + 1) * (2 ^ R * (2 / 2 ^ (4 * R + 6))) := by gcongr
    _ = 1 / 16 := by field_simp; ring

private theorem saksZhou_badSeed_density_le (R d m s Vcard : ℕ) (hR : 1 ≤ R) (hd : d = 5 * R + 5)
    (hm_eq : m = 5 * d) (hs : s = Nat.sqrt R + 1) (hVcard : Vcard ≤ 2 ^ R) :
    let ε : ℝ := (2 : ℝ)⁻¹ ^ (8 * R + 10)
    (Vcard + 1 : ℝ) * ((2 ^ s - 1) * (Vcard + 1) / 2 ^ m) ≤ ε ^ 2 ∧
      (s : ℝ) * (ε + (Vcard : ℝ) ^ 2 * (2 ^ d * ε + (2 ^ d)⁻¹)) ≤ 1 / 8 := by
  intro ε
  have hsR : s ≤ 2 ^ R := by
    have hlt : R < 2 ^ R := Nat.lt_two_pow_self
    have h1 : Nat.sqrt R ≤ R := Nat.sqrt_le_self R
    omega
  have hs_real : (s : ℝ) ≤ 2 ^ R := by exact_mod_cast hsR
  have hV_real : (Vcard : ℝ) ≤ 2 ^ R := by exact_mod_cast hVcard
  have hV1 : (Vcard + 1 : ℝ) ≤ 2 ^ (R + 1) := by
    have h2 : (1 : ℝ) ≤ 2 ^ R := one_le_pow₀ one_le_two
    rw [pow_succ']
    linarith
  have h2s_nonneg : (0 : ℝ) ≤ 2 ^ s - 1 := sub_nonneg.2 (one_le_pow₀ one_le_two)
  have h2s : (2 : ℝ) ^ s - 1 ≤ 2 ^ (R + 1) := by
    have hle : (2 : ℝ) ^ s ≤ 2 ^ (R + 1) := by
      apply pow_le_pow_right₀ (by norm_num)
      have h1 : Nat.sqrt R ≤ R := Nat.sqrt_le_self R
      omega
    linarith
  constructor
  · have hm_ge : 19 * R + 23 ≤ m := by omega
    have h2m : (2 : ℝ) ^ (19 * R + 23) ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm_ge
    have hdiv : (2 : ℝ) ^ (19 * R + 23) =
        (2 ^ (R + 1) * (2 ^ (R + 1) * 2 ^ (R + 1))) * (2 ^ (8 * R + 10)) ^ 2 := by ring
    calc (Vcard + 1 : ℝ) * ((2 ^ s - 1) * (Vcard + 1) / 2 ^ m)
        ≤ 2 ^ (R + 1) * (2 ^ (R + 1) * 2 ^ (R + 1) / 2 ^ (19 * R + 23)) := by gcongr
      _ = ((2 : ℝ)⁻¹ ^ (8 * R + 10)) ^ 2 := by
          rw [mul_div_assoc', hdiv, div_mul_eq_div_div, div_self (by positivity), one_div,
            inv_pow, ← inv_pow]
  · have ht1 : (s : ℝ) * ε ≤ 1 / 24 := by
      have h1 : (2 : ℝ) ^ 17 ≤ 2 ^ (7 * R + 10) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hpow : (2 : ℝ) ^ (8 * R + 10) = 2 ^ R * 2 ^ (7 * R + 10) := by ring
      calc (s : ℝ) * ε ≤ 2 ^ R * (2 : ℝ)⁻¹ ^ (8 * R + 10) := by gcongr
        _ = (2 ^ (7 * R + 10) : ℝ)⁻¹ := by
            rw [inv_pow, hpow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
        _ ≤ (2 ^ 17 : ℝ)⁻¹ := inv_anti₀ (by positivity) h1
        _ ≤ 1 / 24 := by norm_num
    have ht2 : (s : ℝ) * ((Vcard : ℝ) ^ 2 * (2 ^ d * ε)) ≤ 1 / 24 := by
      calc (s : ℝ) * ((Vcard : ℝ) ^ 2 * (2 ^ d * ε))
          ≤ 2 ^ R * ((2 ^ R) ^ 2 * (2 ^ (5 * R + 5) * (2 : ℝ)⁻¹ ^ (8 * R + 10))) := by
              rw [hd]; gcongr
        _ = 1 / 32 := by rw [inv_pow]; field_simp; ring
        _ ≤ 1 / 24 := by norm_num
    have ht3 : (s : ℝ) * ((Vcard : ℝ) ^ 2 * (2 ^ d)⁻¹) ≤ 1 / 24 := by
      have h1 : (2 : ℝ) ^ 7 ≤ 2 ^ (2 * R + 5) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hpow : (2 : ℝ) ^ (5 * R + 5) = (2 ^ R * (2 ^ R) ^ 2) * 2 ^ (2 * R + 5) := by ring
      calc (s : ℝ) * ((Vcard : ℝ) ^ 2 * (2 ^ d)⁻¹)
          ≤ 2 ^ R * ((2 ^ R) ^ 2 * (2 ^ (5 * R + 5))⁻¹) := by rw [hd]; gcongr
        _ = (2 ^ (2 * R + 5) : ℝ)⁻¹ := by
            rw [hpow, mul_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
        _ ≤ (2 ^ 7 : ℝ)⁻¹ := inv_anti₀ (by positivity) h1
        _ ≤ 1 / 24 := by norm_num
    have hexpand : (s : ℝ) * (ε + (Vcard : ℝ) ^ 2 * (2 ^ d * ε + (2 ^ d)⁻¹)) =
        s * ε + s * ((Vcard : ℝ) ^ 2 * (2 ^ d * ε)) + s * ((Vcard : ℝ) ^ 2 * (2 ^ d)⁻¹) := by ring
    rw [hexpand]
    linarith

/-- **Saks–Zhou `O(log^{3/2} n)`-seed reduction for `BPL`**: a step of Saks and Zhou's proof of
`BPL ⊆ DSPACE(log^{3/2} n)` ([#459](https://github.com/cslib-community/cslib-frontier/issues/459),
[#3247](https://github.com/cslib-community/cslib-frontier/issues/3247)), not that inclusion. A `BPL`
language has a fair-coin machine running within `c (log₂ m + 1)` work cells on encoded instances of
length `m` and a clock exponent `clk` such that on every instance `a`, setting
`R = clk (log₂ m + 2) + 1`, `s = ⌊√R⌋ + 1` levels, `d = 5 R + 5` bits of rounding precision, and
blocks of `2 * (5 * d)` bits, the reachable views `V` give a Saks–Zhou iteration using
`O((log₂ m + 1)^{3/2})` total seed-and-shift bits whose output approximates the acceptance
probability within `1/16` for all but at most `1/8` of seeds, strictly separating `a ∈ A`
(fraction `> 1/2`) from `a ∉ A` (fraction `< 1/2`). The space-bounded recursive evaluator remains
open in #459. -/
theorem exists_saksZhouSeeds_of_mem_BPL (h : A ∈ BPL enc) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : MultiTapePTM k Bool State) (c clk : ℕ),
      (∀ a, M.toNTM.RunsInSpace (enc a) (c * (Nat.log2 (enc a).length + 1))) ∧
      ∀ a,
        let R := clk * (Nat.log2 (enc a).length + 2) + 1
        let s := Nat.sqrt R + 1
        let d := 5 * R + 5
        let m := 5 * d
        ∃ (V : Finset (FiniteCfg k Bool State)) (hinit : M.toNTM.initView (enc a) ∈ V),
          (∀ finite ∈ V, ∀ bit, M.viewCoinStep finite bit ∈ V) ∧
          V.card ≤ 2 ^ R ∧
          s * (3 * (2 * m) - 1) + s * d ≤
            155 * (2 * clk + 2) ^ 2 * (Nat.log2 (enc a).length + 1) *
              (Nat.sqrt (Nat.log2 (enc a).length + 1) + 1) ∧
          (Finset.dens (Finset.univ.filter fun
              p : Probability.SaksZhou.NisanShiftSeed (2 * m) s s d =>
              (1 : ℝ) / 16 <
                |M.saksZhouAcceptEst V hinit m s d p -
                  (M.acceptCoins (enc a) (2 ^ (s * s)) : ℝ) / 2 ^ (2 ^ (s * s))|) : ℝ) ≤
            1 / 8 ∧
          (a ∈ A → (1 : ℝ) / 2 < (Finset.dens (Finset.univ.filter fun
              p : Probability.SaksZhou.NisanShiftSeed (2 * m) s s d =>
              (1 : ℝ) / 2 < M.saksZhouAcceptEst V hinit m s d p) : ℝ)) ∧
          (a ∉ A → (Finset.dens (Finset.univ.filter fun
              p : Probability.SaksZhou.NisanShiftSeed (2 * m) s s d =>
              (1 : ℝ) / 2 < M.saksZhouAcceptEst V hinit m s d p) : ℝ) < 1 / 2) := by
  classical
  obtain ⟨k, State, hfin, M, c, hM⟩ := h
  set clk := MultiTapeNTM.logSpaceClockExponent k State c
  refine ⟨k, State, hfin, M, c, clk, fun a => (hM a).1, fun a => ?_⟩
  intro R s d m
  obtain ⟨hs, t, ht, hmem, hnot⟩ := hM a
  obtain ⟨V, hreach, hV, hcard⟩ := M.exists_finset_reachable hs
  have hinit : M.toNTM.initView (enc a) ∈ V := (hreach _).mpr .refl
  have hpoly := MultiTapeNTM.two_pow_coreLengthBound_log_le k State c (enc a).length
  have hT : polyClock clk (enc a).length ≤ 2 ^ R := by
    have hm_lt : 2 * ((enc a).length + 1) ≤ 2 ^ (Nat.log2 (enc a).length + 2) := by
      have := Nat.lt_log2_self (n := (enc a).length)
      rw [pow_succ]
      omega
    rw [polyClock, show R = clk * (Nat.log2 (enc a).length + 2) + 1 from rfl,
      Nat.mul_comm clk, pow_add, pow_one, mul_comm _ 2, pow_mul]
    exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hm_lt clk)
  have hR1 : 1 ≤ R := by dsimp only [R]; omega
  have hs1 : 1 ≤ s := by dsimp only [s]; omega
  have hm1 : 1 ≤ m := by dsimp only [m, d]; omega
  have hdm : d ≤ 2 * m := by dsimp only [m]; omega
  have hRs : R ≤ s * s := by
    have hlt := Nat.lt_succ_sqrt R
    dsimp only [s]
    nlinarith
  have hL : M.toNTM.RunsInTime (enc a) (2 ^ (s * s)) :=
    ((MultiTapeNTM.runsInTime_of_runsInSpace hs ht).mono hpoly).mono
      (hT.trans (Nat.pow_le_pow_right (by decide) hRs))
  have hVcard : V.card ≤ 2 ^ R := hcard.trans hpoly |>.trans hT
  have hfar_le :
      (Finset.dens (Finset.univ.filter fun p : Probability.SaksZhou.NisanShiftSeed (2 * m) s s d =>
        (1 : ℝ) / 16 < |M.saksZhouAcceptEst V hinit m s d p -
          (M.acceptCoins (enc a) (2 ^ (s * s)) : ℝ) / 2 ^ (2 ^ (s * s))|) : ℝ) ≤ 1 / 8 := by
    have herr_step := saksZhou_one_step_error_le R d hR1 rfl s V.card rfl hVcard
    obtain ⟨herr_nisan, herr_bad⟩ :=
      saksZhou_badSeed_density_le R d m s V.card hR1 rfl rfl rfl hVcard
    have hε : (0 : ℝ) < (2 : ℝ)⁻¹ ^ (8 * R + 10) := by positivity
    have hfar := M.dens_saksZhouAcceptEst_far_le hV hinit hs1 hm1 hdm hε herr_nisan
    have hsub : (Finset.univ.filter fun p : Probability.SaksZhou.NisanShiftSeed (2 * m) s s d =>
          (1 : ℝ) / 16 < |M.saksZhouAcceptEst V hinit m s d p -
            (M.acceptCoins (enc a) (2 ^ (s * s)) : ℝ) / 2 ^ (2 ^ (s * s))|) ⊆
        (Finset.univ.filter fun p : Probability.SaksZhou.NisanShiftSeed (2 * m) s s d =>
          (2 : ℝ) ^ (s * s) * (V.card * (2 / 2 ^ d)) < |M.saksZhouAcceptEst V hinit m s d p -
            (M.acceptCoins (enc a) (2 ^ (s * s)) : ℝ) / 2 ^ (2 ^ (s * s))|) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact lt_of_le_of_lt herr_step hp
    exact (NNRat.cast_le.2 (Finset.dens_le_dens hsub)).trans (hfar.trans herr_bad)
  refine ⟨V, hinit, hV, hVcard, saksZhou_seed_budget_le clk _, hfar_le, fun ha => ?_, fun ha => ?_⟩
  · have hacc_nat := (M.two_pow_mul_le_iff ht hL 2 3).mp (hmem ha)
    have hposL : (0 : ℝ) < 2 ^ (2 ^ (s * s)) := by positivity
    have hacc : (2 : ℝ) / 3 ≤
        (M.acceptCoins (enc a) (2 ^ (s * s)) : ℝ) / 2 ^ (2 ^ (s * s)) := by
      rw [div_le_div_iff₀ (by norm_num) hposL]
      exact_mod_cast (by linarith :
        2 * 2 ^ (2 ^ (s * s)) ≤ M.acceptCoins (enc a) (2 ^ (s * s)) * 3)
    have : Nonempty (Probability.SaksZhou.NisanShiftSeed (2 * m) s s d) :=
      ⟨⟨fun _ => (fun _ => false, fun _ => false), fun _ => 0⟩⟩
    refine dens_sdiff_subset_le _ _ (fun p hp => ?_) hfar_le
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hp ⊢
    exact lt_of_lt_of_le (by linarith [hp, hacc]) (neg_le_abs _)
  · have hacc_nat := (M.mul_le_two_pow_iff ht hL 1 3).mp (by simpa using hnot ha)
    have hposL : (0 : ℝ) < 2 ^ (2 ^ (s * s)) := by positivity
    have hacc : (M.acceptCoins (enc a) (2 ^ (s * s)) : ℝ) / 2 ^ (2 ^ (s * s)) ≤ 1 / 3 := by
      rw [div_le_div_iff₀ hposL (by norm_num)]
      exact_mod_cast (by linarith :
        M.acceptCoins (enc a) (2 ^ (s * s)) * 3 ≤ 1 * 2 ^ (2 ^ (s * s)))
    have hsub_maj :
        (Finset.univ.filter fun p : Probability.SaksZhou.NisanShiftSeed (2 * m) s s d =>
          (1 : ℝ) / 2 < M.saksZhouAcceptEst V hinit m s d p) ⊆
        (Finset.univ.filter fun p : Probability.SaksZhou.NisanShiftSeed (2 * m) s s d =>
          (1 : ℝ) / 16 < |M.saksZhouAcceptEst V hinit m s d p -
            (M.acceptCoins (enc a) (2 ^ (s * s)) : ℝ) / 2 ^ (2 ^ (s * s))|) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact lt_of_lt_of_le (by linarith [hp, hacc]) (le_abs_self _)
    have hle := (NNRat.cast_le.2 (Finset.dens_le_dens hsub_maj)).trans hfar_le
    linarith

end Cslib.Complexity
