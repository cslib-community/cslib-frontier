/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.ConfigurationMatrix
public import CslibFrontier.Probability.SaksZhou.Nisan
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
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
`m = 5 d` gives `s` iterations of `bitNisanPow` with shared Toeplitz-Nisan hash seeds
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

namespace Cslib.Probability.SaksZhou

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace

/-- Binary rounding of a counted frequency fits in the workspace used for its counts, scale
and shift. The scale is supplied in binary as the grid denominator `2 ^ d`. -/
theorem computableInSpace_snapCount {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    {scale hits total shift : α → ℕ}
    (hq : ComputableInSpace scale enc encNat S) (hh : ComputableInSpace hits enc encNat S)
    (ht : ComputableInSpace total enc encNat S) (hy : ComputableInSpace shift enc encNat S) :
    ComputableInSpace (fun a => snapCount (scale a) (hits a) (total a) (shift a)) enc encNat S :=
  budget_natDiv (budget_natSub (budget_natMul (budget_natMul hh hq) hq) (budget_natMul hy ht))
    (budget_natMul ht hq)

end Cslib.Probability.SaksZhou

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
  have hpow : Fintype.card (BitString (2 * m)) = 2 * 2 ^ (2 * m - 1) := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ← pow_succ',
      Nat.sub_add_cancel (by omega)]
  simp only [Matrix.smul_apply, smul_eq_mul, configMatrix, Matrix.coinStepMatrix, cnt, hpow]
  push_cast; ring

open scoped Classical in
/-- The Saks–Zhou acceptance probability estimate at parameters `(m, s, d)` on seed-shift pair
`p : NisanShiftSeed (2 * m) s s d`: the entry at the initial view of
the iterated rounded configuration matrix applied to the accept vector, with the states of `V`
numbered by `Fintype.equivFin V`. -/
noncomputable def saksZhouAcceptEst {input : List Bool} (V : Finset (FiniteCfg k Bool State))
    (hinit : machine.toNTM.initView input ∈ V) (m s d : ℕ)
    (p : NisanShiftSeed (2 * m) s s d) : ℝ :=
  (snapIter d (fun B => bitNisanPow (Fintype.equivFin V).symm (2 * m) s B p.1)
    ((2 : ℝ)⁻¹ • machine.configMatrix ℝ V) s p.2 *ᵥ FiniteCfg.acceptVec ℝ V) ⟨_, hinit⟩

private theorem abs_mulVec_acceptVec_sub_le {V : Finset (FiniteCfg k Bool State)}
    (Q R : Matrix V V ℝ) (x : V) :
    |(Q *ᵥ FiniteCfg.acceptVec ℝ V) x - (R *ᵥ FiniteCfg.acceptVec ℝ V) x| ≤
      ∑ y, |Q x y - R x y| := by
  simp only [Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib, ← sub_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  have hacc : |FiniteCfg.acceptVec ℝ V y| ≤ 1 := by
    unfold FiniteCfg.acceptVec
    split_ifs <;> norm_num
  exact abs_mul (Q x y - R x y) _ ▸ mul_le_of_le_one_right (abs_nonneg _) hacc

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
  have hsz := dens_snapIter_bitNisanPow_far_le (Fintype.equivFin V).symm d m s s hs hdm
    (smul_configMatrix_nonneg machine V) (fun x => (sum_smul_configMatrix_eq_one machine hV x).le)
    (exists_smul_configMatrix_mul_card_eq machine hm) hε
    (by simpa only [Fintype.card_coe] using herr)
  have hacc : (machine.acceptCoins input (2 ^ (s * s)) : ℝ) / 2 ^ (2 ^ (s * s)) =
      (P ^ 2 ^ (s * s) *ᵥ FiniteCfg.acceptVec ℝ V) ⟨_, hinit⟩ :=
    machine.acceptCoins_div_eq_configMatrix_pow_mulVec ℝ hV hinit (2 ^ (s * s))
  have hsub : (Finset.univ.filter fun p : NisanShiftSeed (2 * m) s s d =>
        (2 : ℝ) ^ (s * s) * (V.card * (2 / 2 ^ d)) <
          |machine.saksZhouAcceptEst V hinit m s d p -
            (machine.acceptCoins input (2 ^ (s * s)) : ℝ) / 2 ^ (2 ^ (s * s))|) ⊆
      rowFarSet ((2 : ℝ) ^ (s * s) * (Fintype.card V * (2 / 2 ^ d)))
        (fun p : NisanShiftSeed (2 * m) s s d =>
          snapIter d (fun B => bitNisanPow (Fintype.equivFin V).symm (2 * m) s B p.1) P s p.2)
        (P ^ 2 ^ (s * s)) := by
    intro p hp
    refine mem_rowFarSet.mpr ⟨⟨_, hinit⟩, lt_of_lt_of_le ?_ (abs_mulVec_acceptVec_sub_le _ _ _)⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.card_coe, saksZhouAcceptEst,
      hacc] using hp
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
  have hR_le : R ≤ (2 * clk + 1) * (ℓ + 1) := by dsimp only [R]; nlinarith
  have hR1_le : R + 1 ≤ (2 * clk + 2) * (ℓ + 1) := by dsimp only [R]; nlinarith
  have hlt_sqrt : R < ((2 * clk + 2) * (Nat.sqrt (ℓ + 1) + 1)) ^ 2 := by
    have h1 : ℓ + 1 < (Nat.sqrt (ℓ + 1) + 1) ^ 2 := by
      simpa only [sq] using Nat.lt_succ_sqrt (ℓ + 1)
    have h2 : 2 * clk + 1 ≤ (2 * clk + 2) ^ 2 := by nlinarith
    calc R ≤ (2 * clk + 1) * (ℓ + 1) := hR_le
      _ < (2 * clk + 2) ^ 2 * (Nat.sqrt (ℓ + 1) + 1) ^ 2 := by nlinarith
      _ = ((2 * clk + 2) * (Nat.sqrt (ℓ + 1) + 1)) ^ 2 := by ring
  have hs_le : s ≤ (2 * clk + 2) * (Nat.sqrt (ℓ + 1) + 1) :=
    lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _)
      ((by simpa only [sq] using Nat.sqrt_le R : Nat.sqrt R ^ 2 ≤ R).trans_lt hlt_sqrt)
  have hm_eq : 3 * (2 * m) - 1 + d ≤ 155 * (R + 1) := by dsimp only [m, d]; omega
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
  have hsum : (good.dens : ℝ) + ((Finset.univ \ good).dens : ℝ) = 1 := by
    have hadd : (good.card : ℝ) + (Finset.univ \ good).card = Fintype.card Ω := by
      exact_mod_cast (add_comm _ _).trans
        (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ good))
    simp only [Finset.dens, NNRat.cast_div, NNRat.cast_natCast, ← add_div, hadd]
    exact div_self (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  linarith

private theorem saksZhou_one_step_error_le (R d : ℕ) (hR : 1 ≤ R) (hd : d = 5 * R + 5)
    (s Vcard : ℕ) (hs : s = Nat.sqrt R + 1) (hVcard : Vcard ≤ 2 ^ R) :
    (2 : ℝ) ^ (s * s) * ((Vcard : ℝ) * (2 / 2 ^ d)) ≤ 1 / 16 := by
  have hs2 : s * s ≤ 3 * R + 1 := by
    rw [hs]
    nlinarith [Nat.sqrt_le R, Nat.sqrt_le_self R]
  have hnum1 : (2 : ℝ) ^ (s * s) ≤ 2 ^ (3 * R + 1) := pow_le_pow_right₀ one_le_two hs2
  have hnum2 : (Vcard : ℝ) ≤ 2 ^ R := by exact_mod_cast hVcard
  have hden : (2 : ℝ) ^ (4 * R + 6) ≤ 2 ^ d := pow_le_pow_right₀ one_le_two (by omega)
  calc (2 : ℝ) ^ (s * s) * ((Vcard : ℝ) * (2 / 2 ^ d))
      ≤ 2 ^ (3 * R + 1) * (2 ^ R * (2 / 2 ^ (4 * R + 6))) := by gcongr
    _ = 1 / 16 := by field_simp; ring

private theorem saksZhou_badSeed_density_le (R d m s Vcard : ℕ) (hR : 1 ≤ R) (hd : d = 5 * R + 5)
    (hm_eq : m = 5 * d) (hs : s = Nat.sqrt R + 1) (hVcard : Vcard ≤ 2 ^ R) :
    let ε : ℝ := (2 : ℝ)⁻¹ ^ (8 * R + 10)
    (Vcard + 1 : ℝ) * ((2 ^ s - 1) * (Vcard + 1) / 2 ^ m) ≤ ε ^ 2 ∧
      (s : ℝ) * (ε + (Vcard : ℝ) ^ 2 * (2 ^ d * ε + (2 ^ d)⁻¹)) ≤ 1 / 8 := by
  intro ε
  have hsR : s ≤ 2 ^ R := hs ▸ (Nat.sqrt_le_self R).trans_lt Nat.lt_two_pow_self
  have hs_real : (s : ℝ) ≤ 2 ^ R := by exact_mod_cast hsR
  have hV_real : (Vcard : ℝ) ≤ 2 ^ R := by exact_mod_cast hVcard
  have hV1 : (Vcard + 1 : ℝ) ≤ 2 ^ (R + 1) := by
    rw [pow_succ']
    linarith [one_le_pow₀ (n := R) (one_le_two : (1 : ℝ) ≤ 2)]
  have h2s_nonneg : (0 : ℝ) ≤ 2 ^ s - 1 := sub_nonneg.2 (one_le_pow₀ one_le_two)
  have h2s : (2 : ℝ) ^ s - 1 ≤ 2 ^ (R + 1) := by
    linarith [pow_le_pow_right₀ (one_le_two : (1 : ℝ) ≤ 2)
      (hs ▸ Nat.add_le_add_right (Nat.sqrt_le_self R) 1)]
  constructor
  · have h2m : (2 : ℝ) ^ (19 * R + 23) ≤ 2 ^ m := pow_le_pow_right₀ one_le_two (by omega)
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
    rw [mul_add, mul_add]
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
      rw [pow_succ]
      linarith [Nat.lt_log2_self (n := (enc a).length)]
    dsimp only [polyClock, R]
    rw [Nat.mul_comm clk, pow_add, pow_one, mul_comm _ 2, pow_mul]
    exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hm_lt clk)
  have hL : M.toNTM.RunsInTime (enc a) (2 ^ (s * s)) :=
    ((MultiTapeNTM.runsInTime_of_runsInSpace hs ht).mono hpoly).mono
      (hT.trans (Nat.pow_le_pow_right (by decide) (Nat.lt_succ_sqrt R).le))
  have hVcard : V.card ≤ 2 ^ R := hcard.trans hpoly |>.trans hT
  let bad := Finset.univ.filter fun p : Probability.SaksZhou.NisanShiftSeed (2 * m) s s d =>
    (1 : ℝ) / 16 < |M.saksZhouAcceptEst V hinit m s d p -
      (M.acceptCoins (enc a) (2 ^ (s * s)) : ℝ) / 2 ^ (2 ^ (s * s))|
  have hfar_le : (bad.dens : ℝ) ≤ 1 / 8 := by
    have herr_step := saksZhou_one_step_error_le R d (Nat.succ_pos _) rfl s V.card rfl hVcard
    obtain ⟨herr_nisan, herr_bad⟩ :=
      saksZhou_badSeed_density_le R d m s V.card (Nat.succ_pos _ : 1 ≤ R) rfl rfl rfl hVcard
    have hfar := M.dens_saksZhouAcceptEst_far_le hV hinit (Nat.succ_pos _ : 1 ≤ s)
      (Nat.succ_pos _)
      ((Nat.le_mul_of_pos_left d (by decide : 0 < 5)).trans (Nat.le_mul_of_pos_left m two_pos))
      (by positivity) herr_nisan
    refine (NNRat.cast_le.2 (Finset.dens_le_dens fun p hp => ?_)).trans (hfar.trans herr_bad)
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact herr_step.trans_lt hp
  have hposL : (0 : ℝ) < 2 ^ (2 ^ (s * s)) := by positivity
  refine ⟨V, hinit, hV, hVcard, saksZhou_seed_budget_le clk _, hfar_le, fun ha => ?_, fun ha => ?_⟩
  · have hacc : (2 : ℝ) / 3 ≤ (M.acceptCoins (enc a) (2 ^ (s * s)) : ℝ) / 2 ^ (2 ^ (s * s)) := by
      rw [div_le_div_iff₀ (by norm_num) hposL]
      have := (M.two_pow_mul_le_iff ht hL 2 3).mp (hmem ha)
      exact_mod_cast (by omega : 2 * 2 ^ (2 ^ (s * s)) ≤ M.acceptCoins (enc a) (2 ^ (s * s)) * 3)
    have : Nonempty (Probability.SaksZhou.NisanShiftSeed (2 * m) s s d) :=
      ⟨⟨fun _ => (fun _ => false, fun _ => false), fun _ => 0⟩⟩
    refine dens_sdiff_subset_le bad _ (fun p hp => ?_) hfar_le
    simp only [bad, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hp ⊢
    exact lt_of_lt_of_le (by linarith [hp, hacc]) (neg_le_abs _)
  · have hacc : (M.acceptCoins (enc a) (2 ^ (s * s)) : ℝ) / 2 ^ (2 ^ (s * s)) ≤ 1 / 3 := by
      rw [div_le_div_iff₀ hposL (by norm_num)]
      have := (M.mul_le_two_pow_iff ht hL 1 3).mp (by simpa using hnot ha)
      exact_mod_cast (by omega : M.acceptCoins (enc a) (2 ^ (s * s)) * 3 ≤ 1 * 2 ^ (2 ^ (s * s)))
    refine ((NNRat.cast_le.2 (Finset.dens_le_dens fun p hp => ?_)).trans hfar_le).trans_lt
      (by norm_num)
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact lt_of_lt_of_le (by linarith [hp, hacc]) (le_abs_self _)

end Cslib.Complexity
