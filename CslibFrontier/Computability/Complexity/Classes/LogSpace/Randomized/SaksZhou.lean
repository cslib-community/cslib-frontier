/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.CompactMatrix
public import CslibFrontier.Probability.SaksZhou.Nisan
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Saks–Zhou iteration for randomized logarithmic space

The Nisan-powered rounding iteration acts on the compact configuration matrix of a fair-coin
logspace machine (`Turing.MultiTapePTM.ConfigurationGraph.compactCoinMatrix`). For a `BPL`
language, the full radix box and the halting clock are both bounded by `2 ^ R` with `R = O(log n)`.
Setting
`s = ⌊√R⌋ + 1` levels (`2 ^ (s * s) ≥ 2 ^ R`), `d = 5 R + 5` bits of rounding precision, and
`m = 5 d` gives `s` iterations of `bitNisanPow` with shared Toeplitz-Nisan hash seeds
and `s` fresh rounding shifts totaling `O(log^{3/2} n)` bits
(`Cslib.Complexity.exists_saksZhouSeeds_of_mem_BPL`).

The seed reduction is a step toward `BPL ⊆ DSPACE(log^{3/2} n)`. The space inclusion still
requires evaluating `snapIter` of `bitNisanPow` recursively in `O(log^{3/2} n)` space
([#459](https://github.com/cslib-community/cslib-frontier/issues/459)).

## Main definitions

* `Turing.MultiTapePTM.saksZhouAcceptEst`: the `(init, accept)` vector contraction of the
  Nisan-powered Saks–Zhou iterate of the compact transition matrix.

## Main results

* `Turing.MultiTapePTM.dens_saksZhouAcceptEst_far_le`: all but a small fraction of
  `NisanShiftSeed (2 * m) s s d` pairs estimate the `(2 ^ (s * s))`-step acceptance probability
  within `2 ^ (s * s) * N * 2 ^ (1 - d)`, where `N` counts all compact IDs.
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
open MultiTapeNTM.ConfigurationGraph ConfigurationGraph

section Estimate

variable {k : ℕ} {State : Type} [Fintype State] (machine : MultiTapePTM k Bool State)

open scoped Classical in
/-- The rounded Saks–Zhou acceptance estimate on the entire compact configuration box.
Each row is traversed in increasing compact-ID order. The initial vertex is the native start ID,
and the terminal vector selects accepting halts. -/
noncomputable def saksZhouAcceptEst (c : ℕ) {w : List Bool}
    (hs : machine.toNTM.RunsInSpace w (c * (Nat.log2 w.length + 1))) (m s d : ℕ)
    (p : NisanShiftSeed (2 * m) s s d) : ℝ :=
  let B := radix (radixExponent State c) w.length
  (snapIter d (fun Q => bitNisanPow (Equiv.refl _) (2 * m) s Q p.1)
    (compactCoinMatrix machine ℝ B w) s p.2 *ᵥ
    compactAcceptVec (k := k) (State := State) ℝ B w.length) (compactStart machine c hs)

private theorem abs_mulVec_sub_le {ι : Type*} [Fintype ι] (Q R : Matrix ι ι ℝ)
    {v : ι → ℝ} (hv : v ∈ Set.Icc 0 1) (x : ι) :
    |(Q *ᵥ v) x - (R *ᵥ v) x| ≤ ∑ y, |Q x y - R x y| := by
  simp only [Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib, ← sub_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [abs_mul, abs_of_nonneg (hv.1 y)]
  exact mul_le_of_le_one_right (abs_nonneg _) (hv.2 y)

/-- The fraction of seeds giving a large acceptance error on the compact matrix. Its width
`N` counts all radix-box IDs, including malformed IDs and unreachable configurations. -/
theorem dens_saksZhouAcceptEst_far_le (c : ℕ) {w : List Bool}
    (hspace : machine.toNTM.RunsInSpace w (c * (Nat.log2 w.length + 1)))
    {m s d : ℕ} (hs : 1 ≤ s) (hm : 1 ≤ m) (hdm : d ≤ 2 * m) {ε : ℝ} (hε : 0 < ε)
    (herr : let N := vertexBound (k := k) (radix (radixExponent State c) w.length)
      (N + 1 : ℝ) * ((2 ^ s - 1) * (N + 1) / 2 ^ m) ≤ ε ^ 2) :
    let N := vertexBound (k := k) (radix (radixExponent State c) w.length)
    (Finset.dens (Finset.univ.filter fun p : NisanShiftSeed (2 * m) s s d =>
        (2 : ℝ) ^ (s * s) * (N * (2 / 2 ^ d)) <
          |machine.saksZhouAcceptEst c hspace m s d p -
            (machine.acceptCoins w (2 ^ (s * s)) : ℝ) / 2 ^ (2 ^ (s * s))|) : ℝ) ≤
      s * (ε + N ^ 2 * (2 ^ d * ε + (2 ^ d)⁻¹)) := by
  classical
  let B := radix (radixExponent State c) w.length
  let N := vertexBound (k := k) B
  let P := compactCoinMatrix machine ℝ B w
  have hrow (i : Fin N) : ∑ j, P i j ≤ 1 := by
    simpa only [Matrix.mulVec, dotProduct, Pi.one_apply, mul_one] using
      compactCoinMatrix_mulVec_one_le (machine := machine) (R := ℝ) B w i
  have hdy (i j : Fin N) : ∃ t : ℕ, P i j * Fintype.card (BitString (2 * m)) = t := by
    refine ⟨coinCountWithSymbol machine B w.length i j w[queryIndex (k := k) B i]? *
      2 ^ (2 * m - 1), ?_⟩
    have hcard : Fintype.card (BitString (2 * m)) = 2 * 2 ^ (2 * m - 1) := by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ← pow_succ',
        Nat.sub_add_cancel (by omega)]
    rw [hcard]
    simp only [P, compactCoinMatrix, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  have hsz := dens_snapIter_bitNisanPow_far_le (Equiv.refl _) d m s s hs hdm
    (compactCoinMatrix_nonneg B w) hrow hdy hε (by simpa only [Fintype.card_fin] using herr)
  rw [Fintype.card_fin] at hsz
  refine (NNRat.cast_le.2 (Finset.dens_le_dens fun p hp => ?_)).trans hsz
  have hacc := compactCoinMatrix_pow_accept (R := ℝ) c hspace (2 ^ (s * s))
  refine mem_rowFarSet.mpr ⟨compactStart machine c hspace, lt_of_lt_of_le ?_
    (abs_mulVec_sub_le _ _ (compactAcceptVec_mem_Icc (k := k) (State := State) (R := ℝ)
      B w.length) _)⟩
  simpa only [saksZhouAcceptEst, B, N, hacc] using (Finset.mem_filter.mp hp).2

end Estimate

end Turing.MultiTapePTM

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapePTM Cslib.Probability.SaksZhou
open _root_.Turing.MultiTapeNTM.ConfigurationGraph

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
`BPL ⊆ DSPACE(log^{3/2} n)` ([#459](https://github.com/cslib-community/cslib-frontier/issues/459)). A `BPL`
language has a fair-coin machine running within `c (log₂ m + 1)` work cells on encoded instances of
length `m` and a clock exponent `clk` such that on every instance `a`, setting
`R = clk (log₂ m + 2) + 1`, `s = ⌊√R⌋ + 1` levels, `d = 5 R + 5` bits of rounding precision, and
blocks of `2 * (5 * d)` bits, the entire compact radix box gives a Saks–Zhou iteration using
`O((log₂ m + 1)^{3/2})` total seed-and-shift bits whose output approximates the acceptance
probability within `1/16` for all but at most `1/8` of seeds, strictly separating `a ∈ A`
(fraction `> 1/2`) from `a ∉ A` (fraction `< 1/2`). The space-bounded recursive evaluator remains
open in #459. -/
theorem exists_saksZhouSeeds_of_mem_BPL (h : A ∈ BPL enc) :
    ∃ (k : ℕ) (State : Type) (_ : Fintype State) (M : MultiTapePTM k Bool State) (c clk : ℕ),
      ∀ a, ∃ hspace : M.toNTM.RunsInSpace (enc a) (c * (Nat.log2 (enc a).length + 1)),
        let R := clk * (Nat.log2 (enc a).length + 2) + 1
        let s := Nat.sqrt R + 1
        let d := 5 * R + 5
        let m := 5 * d
        vertexBound (k := k) (radix (radixExponent State c) (enc a).length) ≤ 2 ^ R ∧
          s * (3 * (2 * m) - 1) + s * d ≤
            155 * (2 * clk + 2) ^ 2 * (Nat.log2 (enc a).length + 1) *
              (Nat.sqrt (Nat.log2 (enc a).length + 1) + 1) ∧
          (Finset.dens (Finset.univ.filter fun
              p : Probability.SaksZhou.NisanShiftSeed (2 * m) s s d =>
              (1 : ℝ) / 16 <
                |M.saksZhouAcceptEst c hspace m s d p -
                  (M.acceptCoins (enc a) (2 ^ (s * s)) : ℝ) / 2 ^ (2 ^ (s * s))|) : ℝ) ≤
            1 / 8 ∧
          (a ∈ A → (1 : ℝ) / 2 < (Finset.dens (Finset.univ.filter fun
              p : Probability.SaksZhou.NisanShiftSeed (2 * m) s s d =>
              (1 : ℝ) / 2 < M.saksZhouAcceptEst c hspace m s d p) : ℝ)) ∧
          (a ∉ A → (Finset.dens (Finset.univ.filter fun
              p : Probability.SaksZhou.NisanShiftSeed (2 * m) s s d =>
              (1 : ℝ) / 2 < M.saksZhouAcceptEst c hspace m s d p) : ℝ) < 1 / 2) := by
  classical
  obtain ⟨k, State, hfin, M, c, hM⟩ := h
  let : Fintype State := Fintype.ofFinite State
  let D := radixExponent State c
  let e := D * Fintype.card (Register k)
  let clk := max (MultiTapeNTM.logSpaceClockExponent k State c) e
  refine ⟨k, State, inferInstance, M, c, clk, fun a => ⟨(hM a).1, ?_⟩⟩
  intro R s d m
  obtain ⟨hspace, t, ht, hmem, hnot⟩ := hM a
  let n := (enc a).length
  let N := vertexBound (k := k) (radix D n)
  have hpoly := MultiTapeNTM.two_pow_coreLengthBound_log_le k State c n
  have hn : 2 * (n + 1) ≤ 2 ^ (Nat.log2 n + 2) := by
    rw [pow_succ]
    linarith [Nat.lt_log2_self (n := n)]
  have hT : polyClock clk n ≤ 2 ^ R := by
    dsimp only [polyClock, R]
    rw [Nat.mul_comm clk, pow_add, pow_one, mul_comm _ 2, pow_mul]
    exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hn clk)
  have hclock : polyClock (MultiTapeNTM.logSpaceClockExponent k State c) n ≤ polyClock clk n :=
    Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
  have hL : M.toNTM.RunsInTime (enc a) (2 ^ (s * s)) :=
    ((MultiTapeNTM.runsInTime_of_runsInSpace hspace ht).mono (hpoly.trans hclock)).mono
      (hT.trans (Nat.pow_le_pow_right (by decide) (Nat.lt_succ_sqrt R).le))
  have hwidth : N ≤ 2 ^ R := by
    refine le_trans ?_ hT
    dsimp only [N, polyClock]
    rw [vertexBound_eq_pow]
    calc (n + 2) ^ e ≤ (2 * (n + 1)) ^ e := Nat.pow_le_pow_left (by omega) _
      _ ≤ (2 * (n + 1)) ^ clk := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
      _ ≤ _ := Nat.le_mul_of_pos_left _ two_pos
  let bad := Finset.univ.filter fun p : Probability.SaksZhou.NisanShiftSeed (2 * m) s s d =>
    (1 : ℝ) / 16 < |M.saksZhouAcceptEst c hspace m s d p -
      (M.acceptCoins (enc a) (2 ^ (s * s)) : ℝ) / 2 ^ (2 ^ (s * s))|
  have hfar_le : (bad.dens : ℝ) ≤ 1 / 8 := by
    have herr_step := saksZhou_one_step_error_le R d (Nat.succ_pos _) rfl s N rfl hwidth
    obtain ⟨herr_nisan, herr_bad⟩ :=
      saksZhou_badSeed_density_le R d m s N (Nat.succ_pos _ : 1 ≤ R) rfl rfl rfl hwidth
    have hfar := M.dens_saksZhouAcceptEst_far_le c hspace (Nat.succ_pos _ : 1 ≤ s)
      (Nat.succ_pos _)
      ((Nat.le_mul_of_pos_left d (by decide : 0 < 5)).trans (Nat.le_mul_of_pos_left m two_pos))
      (by positivity) herr_nisan
    refine (NNRat.cast_le.2 (Finset.dens_le_dens fun p hp => ?_)).trans (hfar.trans herr_bad)
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact herr_step.trans_lt hp
  have hposL : (0 : ℝ) < 2 ^ (2 ^ (s * s)) := by positivity
  refine ⟨hwidth, saksZhou_seed_budget_le clk _, hfar_le, fun ha => ?_, fun ha => ?_⟩
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
