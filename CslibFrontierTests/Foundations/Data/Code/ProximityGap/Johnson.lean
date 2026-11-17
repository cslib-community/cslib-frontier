/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module

import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests: Johnson-bound proximity gaps for Reed–Solomon codes

Exercises `CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson` via an ordinary `module`
import (without `import all`) across concrete, nonvacuous instances:

1. **Positive-characteristic inseparable contraction (`μ > 1`).** Instantiates
   `Cslib.Code.ProximityGap.exists_separable_contraction` on `Y ^ 2 - Z` over `ZMod 2` and
   `Y ^ 3 - Z` over `ZMod 3`, proving `μ = 2` and `μ = 3` (strictly greater than `1`) and
   `S.natDegree = 1`.
2. **Beyond-unique-decoding positive-characteristic affine line (`ZMod 65537`).** At `n = 5`,
   `k = 2`, `e = 2` (strictly beyond the unique-decoding radius `⌊(5 - 2) / 2⌋ = 1`), `m = 2`,
   `D = 5`, verifies `johnsonCurveBound 5 2 1 5 1 5 = 30807 < 65537`, constructs corrupted words
   `u₀, u₁ ∉ reedSolomon α 2`, applies `exists_correlatedAgreement_line_johnson`, and proves that
   the recovered codeword uniquely matches the underlying linear codeword.
3. **Non-constant integer weights (`W = ![0, 1, 2, 2, 1]`).** Instantiates
   `exists_weighted_correlatedAgreement_line_johnson` over `ZMod 65537` with `M = 2`, `W_tot = 6`,
   `B_W = 5`, and corrupted words outside `reedSolomon α 2`.
4. **Degree-2 curve (`r = 2`) and infinite field (`ℚ`).** Instantiates
   `exists_correlatedAgreement_curve_johnson` on three corrupted words over `ZMod 100003`
   (`johnsonCurveBound 5 2 1 5 2 5 = 64075 < 100003`) and `exists_correlatedAgreement_line_johnson`
   over the infinite field `ℚ` (verifying no hidden `[Fintype F]` assumption).
5. **Finite-field proximity-gap dichotomies (`k = 1`, `e = 1` and `e = 0`, nontrivial RHS `< 1`).**
   Instantiates `proximityGap_line_johnson` over `ZMod 15000017` and
   `proximityGap_line_johnson_of_eta` over the non-prime extension field `GaloisField 5 13`
   (`|𝔽_{5^13}| = 1,220,703,125`) on non-everywhere-close pairs, refutes the everywhere-close
   branch, and establishes nontrivial exceptional fractions strictly below `1`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Foundations.Data.Code.ProximityGap.Johnson

open Cslib Cslib.Code Cslib.Code.ProximityGap Finset Polynomial

instance : Fact (Nat.Prime 2) := ⟨by decide⟩
instance : Fact (Nat.Prime 3) := ⟨by decide⟩
instance : Fact (Nat.Prime 5) := ⟨by decide⟩
instance : Fact (Nat.Prime 65537) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 100003) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 15000017) := ⟨by norm_num⟩

/-! ### 1. Positive-characteristic inseparable contraction (`μ > 1`) -/

/-- Helper: `Y ^ p - Z ∈ F[Z][X][Y]` is irreducible for `p ∈ {2, 3}` over any field `F`. -/
private theorem irreducible_X_pow_sub_C_C_X {F : Type*} [Field F] {p : ℕ} (hp : p = 2 ∨ p = 3) :
    Irreducible (X ^ p - C (C X) : F[X][X][X]) := by
  set R : F[X][X][X] := X ^ p - C (C X)
  have hp_ne : p ≠ 0 := by omega
  have hR_deg : R.natDegree = p := Polynomial.natDegree_X_pow_sub_C _
  have hR_mon : R.Monic := Polynomial.monic_X_pow_sub_C (C X) hp_ne
  have hR_ne : R ≠ 0 := hR_mon.ne_zero
  refine ⟨fun hu => ?_, fun A B hAB => ?_⟩
  · have h0 : R.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  · have hA0 : A ≠ 0 := fun h => hR_ne (by rw [hAB, h, zero_mul])
    have hB0 : B ≠ 0 := fun h => hR_ne (by rw [hAB, h, mul_zero])
    have hdeg : A.natDegree + B.natDegree = p := by
      rw [← Polynomial.natDegree_mul hA0 hB0, ← hAB, hR_deg]
    have hlc : A.leadingCoeff * B.leadingCoeff = 1 := by
      rw [← Polynomial.leadingCoeff_mul, ← hAB]
      exact hR_mon.leadingCoeff
    by_cases hAd0 : A.natDegree = 0
    · left
      rw [Polynomial.eq_C_of_natDegree_eq_zero hAd0]
      have hmul : A.coeff 0 * B.leadingCoeff = 1 := by
        rw [Polynomial.leadingCoeff, hAd0] at hlc
        exact hlc
      have hu : IsUnit (A.coeff 0) :=
        ⟨⟨A.coeff 0, B.leadingCoeff, hmul, mul_comm (A.coeff 0) B.leadingCoeff ▸ hmul⟩, rfl⟩
      exact hu.map Polynomial.C
    · by_cases hBd0 : B.natDegree = 0
      · right
        rw [Polynomial.eq_C_of_natDegree_eq_zero hBd0]
        have hmul : B.coeff 0 * A.leadingCoeff = 1 := by
          rw [mul_comm, Polynomial.leadingCoeff, hBd0] at hlc
          exact hlc
        have hu : IsUnit (B.coeff 0) :=
          ⟨⟨B.coeff 0, A.leadingCoeff, hmul, mul_comm (B.coeff 0) A.leadingCoeff ▸ hmul⟩, rfl⟩
        exact hu.map Polynomial.C
      · -- Neither has degree `0`, so one of `A, B` has degree `1` since `p ∈ {2, 3}`.
        exfalso
        have hex_lin : ∃ L : F[X][X][X], L.natDegree = 1 ∧ IsUnit L.leadingCoeff ∧ L ∣ R := by
          by_cases hA1 : A.natDegree = 1
          · exact ⟨A, hA1,
              ⟨⟨A.leadingCoeff, B.leadingCoeff, hlc,
                mul_comm A.leadingCoeff B.leadingCoeff ▸ hlc⟩, rfl⟩,
              ⟨B, hAB⟩⟩
          · have hB1 : B.natDegree = 1 := by omega
            have hlc' : B.leadingCoeff * A.leadingCoeff = 1 :=
              mul_comm A.leadingCoeff B.leadingCoeff ▸ hlc
            exact ⟨B, hB1, ⟨⟨B.leadingCoeff, A.leadingCoeff, hlc', hlc⟩, rfl⟩,
              ⟨A, hAB.trans (mul_comm A B)⟩⟩
        obtain ⟨L, hL_deg, ⟨uL, huL⟩, ⟨Q, hRQ⟩⟩ := hex_lin
        let r : F[X][X] := -(L.coeff 0) * (uL⁻¹ : (F[X][X])ˣ)
        have hL_eval : L.eval r = 0 := by
          have hL_eq : L = C (L.coeff 0) + C L.leadingCoeff * X := by
            rw [Polynomial.leadingCoeff, hL_deg, add_comm]
            exact Polynomial.eq_X_add_C_of_natDegree_le_one (by omega)
          conv_lhs => rw [hL_eq]
          rw [eval_add, eval_mul, eval_C, eval_C, eval_X, ← huL]
          dsimp only [r]
          calc L.coeff 0 + (uL : F[X][X]) * (-(L.coeff 0) * ↑uL⁻¹)
              = L.coeff 0 - L.coeff 0 * ((uL : F[X][X]) * ↑uL⁻¹) := by ring
            _ = L.coeff 0 - L.coeff 0 * 1 := by rw [Units.mul_inv]
            _ = 0 := by ring
        have hR_eval : R.eval r = 0 := by rw [hRQ, eval_mul, hL_eval, zero_mul]
        have hr_pow : r ^ p = C X := by
          have hsub : r ^ p - C X = 0 := by
            simpa only [R, eval_sub, eval_pow, eval_X, eval_C] using hR_eval
          exact sub_eq_zero.1 hsub
        have h0 : (r.eval 0) ^ p = X := by
          have hev := congrArg (Polynomial.eval (0 : F[X])) hr_pow
          simpa only [eval_pow, eval_C] using hev
        have hdeg_eq : p * (r.eval 0).natDegree = 1 := by
          have h1 := congrArg Polynomial.natDegree h0
          rw [Polynomial.natDegree_pow, Polynomial.natDegree_X] at h1
          exact h1
        rcases hp with rfl | rfl <;> omega

/-- Over `ZMod 2`, separable contraction of the irreducible inseparable polynomial `Y ^ 2 - Z`
forces `μ = 2 > 1` and `S.natDegree = 1`. -/
example :
    let R : (ZMod 2)[X][X][X] := X ^ 2 - C (C X)
    ∃ (μ : ℕ) (S : (ZMod 2)[X][X][X]),
      μ = 2 ∧ S.natDegree = 1 ∧ S.comp (X ^ μ) = R := by
  intro R
  have hR_irred : Irreducible R := irreducible_X_pow_sub_C_C_X (Or.inl rfl)
  have hR_deg : R.natDegree = 2 := Polynomial.natDegree_X_pow_sub_C _
  obtain ⟨μ, S, A, B, Δ, _, hμ_pos, hcomp, hS_deg, hdeg_mul, hΔ_ne, hbez⟩ :=
    exists_separable_contraction hR_irred (by omega)
  have hμ_ne_one : μ ≠ 1 := by
    intro h1
    rw [h1, pow_one, Polynomial.comp_X] at hcomp
    subst hcomp
    have h2xx : (2 : (ZMod 2)[X][X]) = 0 := by
      have h2f : (2 : ZMod 2) = 0 := by decide
      have h2x : (2 : (ZMod 2)[X]) = 0 := by
        rw [← map_ofNat Polynomial.C 2, h2f, map_zero]
      rw [← map_ofNat Polynomial.C 2, h2x, map_zero]
    have hderiv0 : R.derivative = 0 := by
      simp only [R, derivative_sub, derivative_pow, Nat.cast_ofNat, derivative_X, mul_one,
        derivative_C, sub_zero, h2xx, map_zero, zero_mul]
    rw [hderiv0, zero_mul, add_zero] at hbez
    have hA0 : A ≠ 0 := fun h => hΔ_ne (C_eq_zero.1 (by rw [← hbez, h, mul_zero]))
    have hR0 : R ≠ 0 := hR_irred.ne_zero
    have hdeg0 : (R * A).natDegree = 0 := by
      rw [hbez, natDegree_C]
    rw [Polynomial.natDegree_mul hR0 hA0, hR_deg] at hdeg0
    omega
  have hμ2 : μ = 2 := by
    rw [hR_deg] at hdeg_mul
    have hle : μ * 1 ≤ μ * S.natDegree := Nat.mul_le_mul_left μ hS_deg
    omega
  have hS1 : S.natDegree = 1 := by
    rw [hμ2, hR_deg] at hdeg_mul
    omega
  exact ⟨μ, S, hμ2, hS1, hcomp⟩

/-- Over `ZMod 3`, separable contraction of the irreducible inseparable polynomial `Y ^ 3 - Z`
forces `μ = 3 > 1` and `S.natDegree = 1`. -/
example :
    let R : (ZMod 3)[X][X][X] := X ^ 3 - C (C X)
    ∃ (μ : ℕ) (S : (ZMod 3)[X][X][X]),
      μ = 3 ∧ S.natDegree = 1 ∧ S.comp (X ^ μ) = R := by
  intro R
  have hR_irred : Irreducible R := irreducible_X_pow_sub_C_C_X (Or.inr rfl)
  have hR_deg : R.natDegree = 3 := Polynomial.natDegree_X_pow_sub_C _
  obtain ⟨μ, S, A, B, Δ, _, hμ_pos, hcomp, hS_deg, hdeg_mul, hΔ_ne, hbez⟩ :=
    exists_separable_contraction hR_irred (by omega)
  have hμ_ne_one : μ ≠ 1 := by
    intro h1
    rw [h1, pow_one, Polynomial.comp_X] at hcomp
    subst hcomp
    have h3xx : (3 : (ZMod 3)[X][X]) = 0 := by
      have h3f : (3 : ZMod 3) = 0 := by decide
      have h3x : (3 : (ZMod 3)[X]) = 0 := by
        rw [← map_ofNat Polynomial.C 3, h3f, map_zero]
      rw [← map_ofNat Polynomial.C 3, h3x, map_zero]
    have hderiv0 : R.derivative = 0 := by
      simp only [R, derivative_sub, derivative_pow, Nat.cast_ofNat, derivative_X, mul_one,
        derivative_C, sub_zero, h3xx, map_zero, zero_mul]
    rw [hderiv0, zero_mul, add_zero] at hbez
    have hA0 : A ≠ 0 := fun h => hΔ_ne (C_eq_zero.1 (by rw [← hbez, h, mul_zero]))
    have hR0 : R ≠ 0 := hR_irred.ne_zero
    have hdeg0 : (R * A).natDegree = 0 := by
      rw [hbez, natDegree_C]
    rw [Polynomial.natDegree_mul hR0 hA0, hR_deg] at hdeg0
    omega
  have hμ3 : μ = 3 := by
    rw [hR_deg] at hdeg_mul
    have hle : μ * 1 ≤ μ * S.natDegree := Nat.mul_le_mul_left μ hS_deg
    have h1 : μ = 2 ∨ μ = 3 := by omega
    rcases h1 with h2 | h3
    · rw [h2] at hdeg_mul
      omega
    · exact h3
  have hS1 : S.natDegree = 1 := by
    rw [hμ3, hR_deg] at hdeg_mul
    omega
  exact ⟨μ, S, hμ3, hS1, hcomp⟩

/-! ### 2. Shared helpers for concrete Reed–Solomon instances -/

/-- Monomial count `#(Sudan.monomials 1 5) = 21`. -/
private theorem card_monomials_1_5 : #(Sudan.monomials 1 5) = 21 := by decide

/-- Maximum `Y`-degree `maxYDeg 1 5 = 5`. -/
private theorem maxYDeg_1_5 : maxYDeg 1 5 = 5 := by decide

/-- Helper: any polynomial of degree `< 2` evaluates as `p.coeff 0 + p.coeff 1 * x`. -/
private theorem eval_eq_of_degree_lt_two {F : Type*} [Field F] {p : F[X]} (hp : p.degree < (2 : ℕ))
    (x : F) : p.eval x = p.coeff 0 + p.coeff 1 * x := by
  have hdeg : p.natDegree < 2 := by
    by_cases hp0 : p = 0
    · rw [hp0, natDegree_zero]; decide
    · exact (natDegree_lt_iff_degree_lt hp0).2 hp
  rw [eval_eq_sum_range' hdeg, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [pow_zero, mul_one, pow_one]

/-- Helper: any Reed–Solomon codeword of dimension `2` on consecutive points `0, 1, 2, 3, 4`
satisfies the linear relation `c i - 2 * c (i + 1) + c (i + 2) = 0`. -/
private theorem second_diff_zero_of_mem_rs2 {F : Type*} [Field F] {c : Fin 5 → F}
    (hc : c ∈ reedSolomon (fun i : Fin 5 => (i.val : F)) 2) :
    c 1 - 2 * c 2 + c 3 = 0 ∧ c 0 - 2 * c 1 + c 2 = 0 := by
  obtain ⟨p, hp, rfl⟩ := mem_reedSolomon.1 hc
  constructor <;>
    · simp only [eval_eq_of_degree_lt_two hp, Fin.val_zero, Fin.val_one, Fin.val_two,
        show (3 : Fin 5).val = 3 from rfl, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
      ring

/-- Helper: `hammingDist x y ≤ e` whenever `x` and `y` agree on a subset of size `≥ |ι| - e`. -/
private theorem hammingDist_le_of_agree_subset {F ι : Type*} [Fintype ι]
    [DecidableEq F] {x y : ι → F} {A : Finset ι} {e : ℕ} (hA : Fintype.card ι - e ≤ #A)
    (hagree : ∀ i ∈ A, x i = y i) : hammingDist x y ≤ e := by
  classical
  have hsub : Finset.univ.filter (fun i => x i ≠ y i) ⊆ Finset.univ \ A := by
    intro i hi
    refine mem_sdiff.2 ⟨mem_univ i, fun hiA => (mem_filter.1 hi).2 (hagree i hiA)⟩
  have hcard : hammingDist x y ≤ #(Finset.univ \ A) := card_le_card hsub
  rw [Finset.card_sdiff_of_subset (subset_univ A), Finset.card_univ] at hcard
  omega

/-- Helper: `1 + X` defines a codeword in `reedSolomon α 2`. -/
private theorem one_add_X_mem_rs2 {F ι : Type*} [Field F] (α : ι → F) :
    (fun i => (1 + X : F[X]).eval (α i)) ∈ reedSolomon α 2 := by
  refine eval_mem_reedSolomon α ?_
  refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
  · rw [degree_one]; exact Nat.cast_lt.2 (by decide)
  · rw [degree_X]; exact Nat.cast_lt.2 (by decide)

/-- Helper: `2 * X` defines a codeword in `reedSolomon α 2`. -/
private theorem two_mul_X_mem_rs2 {F ι : Type*} [Field F] (α : ι → F) :
    (fun i => (C (2 : F) * X).eval (α i)) ∈ reedSolomon α 2 := by
  refine eval_mem_reedSolomon α ?_
  refine (degree_mul_le _ _).trans_lt ?_
  refine (add_le_add degree_C_le le_rfl).trans_lt ?_
  rw [zero_add, degree_X]
  exact Nat.cast_lt.2 (by decide)

/-! ### 3. Beyond-unique-decoding positive-char affine line over `ZMod 65537` -/

private def α65537 : Fin 5 → ZMod 65537 := fun i => (i.val : ZMod 65537)

private theorem α65537_injective : Function.Injective α65537 := by
  intro i j h
  have hv := congrArg ZMod.val h
  dsimp only [α65537] at hv
  rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv
  exact Fin.ext hv

private def v0_65537 : Fin 5 → ZMod 65537 := fun i => 1 + α65537 i
private def v1_65537 : Fin 5 → ZMod 65537 := fun i => 2 * α65537 i

private def u0_65537 : Fin 5 → ZMod 65537 :=
  fun i => if i.val < 3 then v0_65537 i else v0_65537 i + 1

private def u1_65537 : Fin 5 → ZMod 65537 :=
  fun i => if i.val < 3 then v1_65537 i else v1_65537 i + 2

private theorem v0_65537_mem : v0_65537 ∈ reedSolomon α65537 2 := by
  unfold v0_65537
  simpa only [eval_add, eval_one, eval_X] using one_add_X_mem_rs2 α65537

private theorem v1_65537_mem : v1_65537 ∈ reedSolomon α65537 2 := by
  unfold v1_65537
  simpa only [eval_mul, eval_C, eval_X] using two_mul_X_mem_rs2 α65537

private theorem u0_65537_not_mem : u0_65537 ∉ reedSolomon α65537 2 := by
  intro hmem
  have hdiff := (second_diff_zero_of_mem_rs2 hmem).1
  have hval : u0_65537 1 - 2 * u0_65537 2 + u0_65537 3 = 1 := by decide
  rw [hval] at hdiff
  exact one_ne_zero hdiff

private theorem u1_65537_not_mem : u1_65537 ∉ reedSolomon α65537 2 := by
  intro hmem
  have hdiff := (second_diff_zero_of_mem_rs2 hmem).1
  have hval : u1_65537 1 - 2 * u1_65537 2 + u1_65537 3 = 2 := by decide
  rw [hval] at hdiff
  have h2ne : (2 : ZMod 65537) ≠ 0 := by decide
  exact h2ne hdiff

/-- Strictly-beyond-unique-decoding correlated agreement over `ZMod 65537`: at `n = 5`, `k = 2`,
`e = 2 > 1` (unique decoding radius is `1`), `m = 2`, `D = 5`,
`johnsonCurveBound 5 2 1 5 1 5 = 30807 < 65537`, and `exists_correlatedAgreement_line_johnson`
recovers the exact underlying codeword `v0_65537` from corrupted words `u0_65537, u1_65537 ∉ RS`. -/
example :
    u0_65537 ∉ reedSolomon α65537 2 ∧
    u1_65537 ∉ reedSolomon α65537 2 ∧
    johnsonCurveBound 5 2 1 5 1 5 = 30807 ∧
    ∃ D' : Finset (Fin 5), 3 ≤ #D' ∧
      ∃ w₀ ∈ reedSolomon α65537 2, ∃ w₁ ∈ reedSolomon α65537 2,
        (∀ i ∈ D', u0_65537 i = w₀ i ∧ u1_65537 i = w₁ i) ∧ w₀ = v0_65537 := by
  have hjb : johnsonCurveBound 5 2 1 5 1 5 = 30807 := by
    simp only [johnsonCurveBound, siegelZDeg, card_monomials_1_5, maxYDeg_1_5]
    norm_num
  have hT : johnsonCurveBound (Fintype.card (Fin 5)) 2 (2 - 1) 5 1 (Fintype.card (Fin 5)) <
      #(Finset.univ : Finset (ZMod 65537)) := by
    rw [Fintype.card_fin, Finset.card_univ, ZMod.card]
    change johnsonCurveBound 5 2 1 5 1 5 < 65537
    omega
  have hinterp : Fintype.card (Fin 5) * (2 * (2 + 1) / 2) < #(Sudan.monomials (2 - 1) 5) := by
    rw [Fintype.card_fin]
    change 5 * 3 < #(Sudan.monomials 1 5)
    rw [card_monomials_1_5]
    omega
  have hclose : ∀ z ∈ (Finset.univ : Finset (ZMod 65537)),
      ∃ c ∈ reedSolomon α65537 2, hammingDist (u0_65537 + z • u1_65537) c ≤ 2 := by
    intro z _
    refine ⟨v0_65537 + z • v1_65537,
      Submodule.add_mem _ v0_65537_mem (Submodule.smul_mem _ z v1_65537_mem), ?_⟩
    refine hammingDist_le_of_agree_subset (A := {0, 1, 2}) (by decide) ?_
    intro i hi
    fin_cases hi <;> simp [u0_65537, u1_65537]
  obtain ⟨D', hD', w₀, hw₀, w₁, hw₁, hagree⟩ :=
    exists_correlatedAgreement_line_johnson α65537_injective (k := 2) (e := 2) (m := 2) (D := 5)
      (by omega) (by omega) (by rw [Fintype.card_fin]; omega) hinterp
      (by rw [Fintype.card_fin]; omega) u0_65537 u1_65537 Finset.univ hT hclose
  rw [Fintype.card_fin] at hD'
  -- Prove uniqueness: `w₀ = v0_65537`.
  have hw₀_eq : w₀ = v0_65537 := by
    obtain ⟨p, hp, rfl⟩ := mem_reedSolomon.1 hw₀
    have hD'_sub : D' ⊆ {0, 1, 2} := by
      have hnot_both : ¬ ((3 : Fin 5) ∈ D' ∧ (4 : Fin 5) ∈ D') := by
        rintro ⟨h3, h4⟩
        have hex012 : ∃ i ∈ D', i.val < 3 := by
          by_contra hall
          push Not at hall
          have hsub34 : D' ⊆ {3, 4} := by
            intro i hi
            have := hall i hi
            fin_cases i <;> simp_all
          have := card_le_card hsub34
          have hcard34 : #({3, 4} : Finset (Fin 5)) = 2 := by decide
          omega
        obtain ⟨i₀, hi₀D, hi₀lt⟩ := hex012
        have hp3 := (hagree 3 h3).1
        have hp4 := (hagree 4 h4).1
        have hpi := (hagree i₀ hi₀D).1
        dsimp only at hp3 hp4 hpi
        rw [eval_eq_of_degree_lt_two hp] at hp3 hp4 hpi
        have h3v : u0_65537 3 = 5 := by decide
        have h4v : u0_65537 4 = 6 := by decide
        have ha3 : α65537 3 = 3 := rfl
        have ha4 : α65537 4 = 4 := rfl
        rw [h3v, ha3] at hp3
        rw [h4v, ha4] at hp4
        have hc1 : p.coeff 1 = 1 := by linear_combination hp3 - hp4
        have hc0 : p.coeff 0 = 2 := by linear_combination -hp3 - 3 * hc1
        rw [hc0, hc1, one_mul] at hpi
        simp only [u0_65537, hi₀lt, ↓reduceIte, v0_65537] at hpi
        have h12 : (1 : ZMod 65537) = 2 := by linear_combination hpi
        have hne : (1 : ZMod 65537) ≠ 2 := by decide
        exact hne h12
      -- Since `¬ (3 ∈ D' ∧ 4 ∈ D')` and `#D' ≥ 3`, at least two points of `D'` lie in `{0, 1, 2}`.
      have h2_in : 2 ≤ #(D' ∩ {0, 1, 2}) := by
        have hcompl : D' \ (D' ∩ {0, 1, 2}) ⊆ {3, 4} := by
          intro i hi
          obtain ⟨hiD, hiNot⟩ := mem_sdiff.1 hi
          have : i ∉ ({0, 1, 2} : Finset (Fin 5)) := fun h => hiNot (mem_inter.2 ⟨hiD, h⟩)
          fin_cases i <;> simp_all
        have hlt2 : #(D' \ (D' ∩ {0, 1, 2})) ≤ 1 := by
          by_contra hge
          have hge2 : 2 ≤ #(D' \ (D' ∩ {0, 1, 2})) := by omega
          have heq : D' \ (D' ∩ {0, 1, 2}) = {3, 4} :=
            Finset.eq_of_subset_of_card_le hcompl (by
              have : #({3, 4} : Finset (Fin 5)) = 2 := by decide
              omega)
          have h3s : (3 : Fin 5) ∈ D' \ (D' ∩ {0, 1, 2}) := by rw [heq]; decide
          have h4s : (4 : Fin 5) ∈ D' \ (D' ∩ {0, 1, 2}) := by rw [heq]; decide
          exact hnot_both ⟨(mem_sdiff.1 h3s).1, (mem_sdiff.1 h4s).1⟩
        have hcard_sdiff := Finset.card_sdiff_of_subset (Finset.inter_subset_left (s₁ := D')
          (s₂ := {0, 1, 2}))
        omega
      -- Two distinct points in `D' ∩ {0, 1, 2}` determine `p = 1 + X`, ruling out `3, 4 ∈ D'`.
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < #(D' ∩ {0, 1, 2}))
      have hpa := (hagree a (mem_inter.1 ha).1).1
      have hpb := (hagree b (mem_inter.1 hb).1).1
      have ha_lt : a.val < 3 := by
        have hm := (mem_inter.1 ha).2
        fin_cases a <;> simp_all
      have hb_lt : b.val < 3 := by
        have hm := (mem_inter.1 hb).2
        fin_cases b <;> simp_all
      dsimp only at hpa hpb
      rw [eval_eq_of_degree_lt_two hp] at hpa hpb
      simp only [u0_65537, ha_lt, hb_lt, ↓reduceIte, v0_65537] at hpa hpb
      have hsub_ne : α65537 a - α65537 b ≠ 0 :=
        sub_ne_zero.2 fun heq => hab (α65537_injective heq)
      have hc1 : p.coeff 1 = 1 := by
        have hmul : (p.coeff 1 - 1) * (α65537 a - α65537 b) = 0 := by
          linear_combination -hpa + hpb
        exact sub_eq_zero.1 ((mul_eq_zero.1 hmul).resolve_right hsub_ne)
      have hc0 : p.coeff 0 = 1 := by linear_combination -hpa - α65537 a * hc1
      intro i hiD
      have hpi := (hagree i hiD).1
      dsimp only at hpi
      rw [eval_eq_of_degree_lt_two hp, hc0, hc1, one_mul] at hpi
      by_cases hilt : i.val < 3
      · fin_cases i <;> simp_all
      · simp only [u0_65537, hilt, ↓reduceIte, v0_65537] at hpi
        have h10 : (1 : ZMod 65537) = 0 := by linear_combination hpi
        exact absurd h10 one_ne_zero
    have hD'_eq : D' = {0, 1, 2} :=
      Finset.eq_of_subset_of_card_le hD'_sub (by
        have : #({0, 1, 2} : Finset (Fin 5)) = 3 := by decide
        omega)
    have h0D : (0 : Fin 5) ∈ D' := by rw [hD'_eq]; decide
    have h1D : (1 : Fin 5) ∈ D' := by rw [hD'_eq]; decide
    have hp0 := (hagree 0 h0D).1
    have hp1 := (hagree 1 h1D).1
    dsimp only at hp0 hp1
    rw [eval_eq_of_degree_lt_two hp] at hp0 hp1
    have h0v : u0_65537 0 = 1 := by decide
    have h1v : u0_65537 1 = 2 := by decide
    have ha0 : α65537 0 = 0 := rfl
    have ha1 : α65537 1 = 1 := rfl
    rw [h0v, ha0] at hp0
    rw [h1v, ha1] at hp1
    have hc0 : p.coeff 0 = 1 := by linear_combination -hp0
    have hc1 : p.coeff 1 = 1 := by linear_combination -hp1 - hc0
    funext i
    rw [eval_eq_of_degree_lt_two hp, hc0, hc1, one_mul]
    rfl
  exact ⟨u0_65537_not_mem, u1_65537_not_mem, hjb, D', hD', w₀, hw₀, w₁, hw₁, hagree, hw₀_eq⟩

/-! ### 4. Weighted non-constant correlated agreement (`W = ![0, 1, 2, 2, 1]`) -/

private def W5 : Fin 5 → ℕ := ![0, 1, 2, 2, 1]

private def u0w_65537 : Fin 5 → ZMod 65537 :=
  fun i => if i = 0 ∨ i = 4 then v0_65537 i + 1 else v0_65537 i

private def u1w_65537 : Fin 5 → ZMod 65537 :=
  fun i => if i = 0 ∨ i = 4 then v1_65537 i + 3 else v1_65537 i

private theorem u0w_not_mem : u0w_65537 ∉ reedSolomon α65537 2 := by
  intro hmem
  have hdiff := (second_diff_zero_of_mem_rs2 hmem).2
  have hval : u0w_65537 0 - 2 * u0w_65537 1 + u0w_65537 2 = 1 := by decide
  rw [hval] at hdiff
  exact one_ne_zero hdiff

private theorem u1w_not_mem : u1w_65537 ∉ reedSolomon α65537 2 := by
  intro hmem
  have hdiff := (second_diff_zero_of_mem_rs2 hmem).2
  have hval : u1w_65537 0 - 2 * u1w_65537 1 + u1w_65537 2 = 3 := by decide
  rw [hval] at hdiff
  have h3ne : (3 : ZMod 65537) ≠ 0 := by decide
  exact h3ne hdiff

/-- Non-constant integer weights `W = ![0, 1, 2, 2, 1]` (`M = 2`, `W_tot = 6`, `B_W = 5`) over
`ZMod 65537`, verifying `johnsonCurveBound 5 2 1 5 1 6 = 36932 < 65537`. -/
example :
    u0w_65537 ∉ reedSolomon α65537 2 ∧
    u1w_65537 ∉ reedSolomon α65537 2 ∧
    johnsonCurveBound 5 2 1 5 1 6 = 36932 ∧
    ∃ D' : Finset (Fin 5), 5 ≤ ∑ i ∈ D', W5 i ∧
      ∃ w₀ ∈ reedSolomon α65537 2, ∃ w₁ ∈ reedSolomon α65537 2,
        ∀ i ∈ D', u0w_65537 i = w₀ i ∧ u1w_65537 i = w₁ i := by
  have hjb : johnsonCurveBound 5 2 1 5 1 6 = 36932 := by
    simp only [johnsonCurveBound, siegelZDeg, card_monomials_1_5, maxYDeg_1_5]
    norm_num
  have hT : johnsonCurveBound (Fintype.card (Fin 5)) 2 (2 - 1) 5 1 6 <
      #(Finset.univ : Finset (ZMod 65537)) := by
    rw [Fintype.card_fin, Finset.card_univ, ZMod.card]
    change johnsonCurveBound 5 2 1 5 1 6 < 65537
    omega
  have hinterp : Fintype.card (Fin 5) * (2 * (2 + 1) / 2) < #(Sudan.monomials (2 - 1) 5) := by
    rw [Fintype.card_fin]
    change 5 * 3 < #(Sudan.monomials 1 5)
    rw [card_monomials_1_5]
    omega
  have hW_le : ∀ i, W5 i ≤ 2 := by intro i; fin_cases i <;> decide
  have hW_sum : ∑ i : Fin 5, W5 i ≤ 6 := by decide
  have hclose : ∀ z ∈ (Finset.univ : Finset (ZMod 65537)),
      ∃ c ∈ reedSolomon α65537 2,
        5 ≤ ∑ i ∈ Finset.univ.filter (fun i => (u0w_65537 + z • u1w_65537) i = c i), W5 i := by
    intro z _
    refine ⟨v0_65537 + z • v1_65537,
      Submodule.add_mem _ v0_65537_mem (Submodule.smul_mem _ z v1_65537_mem), ?_⟩
    have hsub : ({1, 2, 3} : Finset (Fin 5)) ⊆
        Finset.univ.filter (fun i => (u0w_65537 + z • u1w_65537) i = (v0_65537 + z • v1_65537) i) :=
      fun i hi => by
        refine mem_filter.2 ⟨mem_univ i, ?_⟩
        fin_cases hi <;> simp [u0w_65537, u1w_65537]
    have hsum5 : (5 : ℕ) ≤ ∑ i ∈ ({1, 2, 3} : Finset (Fin 5)), W5 i := by decide
    exact hsum5.trans (Finset.sum_le_sum_of_subset hsub)
  refine ⟨u0w_not_mem, u1w_not_mem, hjb, ?_⟩
  exact exists_weighted_correlatedAgreement_line_johnson α65537_injective (k := 2) (m := 2) (D := 5)
    (M := 2) (W_tot := 6) (B_W := 5) (by omega) (by omega) (by omega) hW_le hW_sum (by omega)
    hinterp (by omega) u0w_65537 u1w_65537 Finset.univ hT hclose

/-! ### 5. Degree-2 curve (`r = 2`) over `ZMod 100003` and infinite field (`ℚ`) -/

private def α100003 : Fin 5 → ZMod 100003 := fun i => (i.val : ZMod 100003)

private theorem α100003_injective : Function.Injective α100003 := by
  intro i j h
  have hv := congrArg ZMod.val h
  dsimp only [α100003] at hv
  rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv
  exact Fin.ext hv

/-- Degree-2 curve (`r = 2`, three corrupted words outside `reedSolomon`) over `ZMod 100003` at
distance `e = 2 > 1` (`johnsonCurveBound 5 2 1 5 2 5 = 64075 < 100003`). -/
example :
    johnsonCurveBound 5 2 1 5 2 5 = 64075 ∧
    ∃ (u : Fin 3 → (Fin 5 → ZMod 100003)),
      (∀ j, u j ∉ reedSolomon α100003 2) ∧
      ∃ D' : Finset (Fin 5), 3 ≤ #D' ∧
        ∃ v : Fin 3 → (Fin 5 → ZMod 100003), (∀ j, v j ∈ reedSolomon α100003 2) ∧
          ∀ i ∈ D', ∀ j, u j i = v j i := by
  have hjb : johnsonCurveBound 5 2 1 5 2 5 = 64075 := by
    simp only [johnsonCurveBound, siegelZDeg, card_monomials_1_5, maxYDeg_1_5]
    norm_num
  let v0 : Fin 5 → ZMod 100003 := fun i => 1 + α100003 i
  let v1 : Fin 5 → ZMod 100003 := fun i => 2 * α100003 i
  let v2 : Fin 5 → ZMod 100003 := fun i => 1 + 2 * α100003 i
  let vTrue : Fin 3 → (Fin 5 → ZMod 100003) := ![v0, v1, v2]
  let u : Fin 3 → (Fin 5 → ZMod 100003) :=
    fun j i => if i.val < 3 then vTrue j i else vTrue j i + 1
  have hv0 : v0 ∈ reedSolomon α100003 2 := by
    simpa only [v0, eval_add, eval_one, eval_X] using one_add_X_mem_rs2 α100003
  have hv1 : v1 ∈ reedSolomon α100003 2 := by
    simpa only [v1, eval_mul, eval_C, eval_X] using two_mul_X_mem_rs2 α100003
  have hv2 : v2 ∈ reedSolomon α100003 2 := by
    have hconst : (fun _ : Fin 5 => (1 : ZMod 100003)) ∈ reedSolomon α100003 2 := by
      have h1 : (fun i => (1 : (ZMod 100003)[X]).eval (α100003 i)) ∈ reedSolomon α100003 2 := by
        refine eval_mem_reedSolomon α100003 ?_
        rw [degree_one]
        exact Nat.cast_lt.2 (by decide)
      simpa only [eval_one] using h1
    exact Submodule.add_mem _ hconst hv1
  have hvTrue : ∀ j : Fin 3, vTrue j ∈ reedSolomon α100003 2 := by
    intro j
    fin_cases j
    · exact hv0
    · exact hv1
    · exact hv2
  have hu_not : ∀ j : Fin 3, u j ∉ reedSolomon α100003 2 := by
    intro j hmem
    have hdiff := (second_diff_zero_of_mem_rs2 hmem).1
    fin_cases j
    · have hval : u 0 1 - 2 * u 0 2 + u 0 3 = 1 := by
        simp only [u, vTrue, v0, α100003, Matrix.cons_val_zero]
        decide
      exact one_ne_zero (hval.symm.trans hdiff)
    · have hval : u 1 1 - 2 * u 1 2 + u 1 3 = 1 := by
        simp only [u, vTrue, v1, α100003, Matrix.cons_val_one]
        decide
      exact one_ne_zero (hval.symm.trans hdiff)
    · have hval : u 2 1 - 2 * u 2 2 + u 2 3 = 1 := by
        simp only [u, vTrue, v2, α100003, Matrix.cons_val_two]
        decide
      exact one_ne_zero (hval.symm.trans hdiff)
  have hT : johnsonCurveBound (Fintype.card (Fin 5)) 2 (2 - 1) 5 2 (Fintype.card (Fin 5)) <
      #(Finset.univ : Finset (ZMod 100003)) := by
    rw [Fintype.card_fin, Finset.card_univ, ZMod.card]
    change johnsonCurveBound 5 2 1 5 2 5 < 100003
    omega
  have hinterp : Fintype.card (Fin 5) * (2 * (2 + 1) / 2) < #(Sudan.monomials (2 - 1) 5) := by
    rw [Fintype.card_fin]
    change 5 * 3 < #(Sudan.monomials 1 5)
    rw [card_monomials_1_5]
    omega
  have hclose : ∀ z ∈ (Finset.univ : Finset (ZMod 100003)),
      ∃ c ∈ reedSolomon α100003 2,
        hammingDist (∑ j : Fin 3, z ^ (j : ℕ) • u j) c ≤ 2 := by
    intro z _
    refine ⟨∑ j : Fin 3, z ^ (j : ℕ) • vTrue j,
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvTrue j), ?_⟩
    refine hammingDist_le_of_agree_subset (A := {0, 1, 2}) (by decide) ?_
    intro i hi
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    fin_cases hi <;> simp [u]
  obtain ⟨D', hD', v, hv_rs, hagree⟩ :=
    exists_correlatedAgreement_curve_johnson α100003_injective (k := 2) (r := 2) (e := 2) (m := 2)
      (D := 5) (by omega) (by omega) (by rw [Fintype.card_fin]; omega) hinterp
      (by rw [Fintype.card_fin]; omega) u Finset.univ hT hclose
  rw [Fintype.card_fin] at hD'
  exact ⟨hjb, u, hu_not, D', hD', v, hv_rs, hagree⟩

/-- Infinite-field (`ℚ`) beyond-unique-decoding line instantiation, confirming that
`exists_correlatedAgreement_line_johnson` requires no `[Fintype F]` assumption. -/
example :
    let αQ : Fin 5 → ℚ := fun i => (i.val : ℚ)
    ∃ (u₀ u₁ : Fin 5 → ℚ),
      u₀ ∉ reedSolomon αQ 2 ∧ u₁ ∉ reedSolomon αQ 2 ∧
      ∃ D' : Finset (Fin 5), 3 ≤ #D' ∧
        ∃ w₀ ∈ reedSolomon αQ 2, ∃ w₁ ∈ reedSolomon αQ 2,
          ∀ i ∈ D', u₀ i = w₀ i ∧ u₁ i = w₁ i := by
  intro αQ
  have hαQ : Function.Injective αQ := by
    intro i j h
    exact Fin.ext (Nat.cast_injective h)
  let v0 : Fin 5 → ℚ := fun i => 1 + αQ i
  let v1 : Fin 5 → ℚ := fun i => 2 * αQ i
  let u0 : Fin 5 → ℚ := fun i => if i.val < 3 then v0 i else v0 i + 1
  let u1 : Fin 5 → ℚ := fun i => if i.val < 3 then v1 i else v1 i + 2
  have hv0 : v0 ∈ reedSolomon αQ 2 := by
    simpa only [v0, eval_add, eval_one, eval_X] using one_add_X_mem_rs2 αQ
  have hv1 : v1 ∈ reedSolomon αQ 2 := by
    simpa only [v1, eval_mul, eval_C, eval_X] using two_mul_X_mem_rs2 αQ
  have hu0 : u0 ∉ reedSolomon αQ 2 := by
    intro hmem
    have hdiff := (second_diff_zero_of_mem_rs2 hmem).1
    have hval : u0 1 - 2 * u0 2 + u0 3 = 1 := by norm_num [u0, v0, αQ]
    rw [hval] at hdiff
    exact one_ne_zero hdiff
  have hu1 : u1 ∉ reedSolomon αQ 2 := by
    intro hmem
    have hdiff := (second_diff_zero_of_mem_rs2 hmem).1
    have hval : u1 1 - 2 * u1 2 + u1 3 = 2 := by norm_num [u1, v1, αQ]
    rw [hval] at hdiff
    norm_num at hdiff
  let T : Finset ℚ := (Finset.range 30808).image (fun a : ℕ => (a : ℚ))
  have hT_card : #T = 30808 := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  have hjb : johnsonCurveBound 5 2 1 5 1 5 = 30807 := by
    simp only [johnsonCurveBound, siegelZDeg, card_monomials_1_5, maxYDeg_1_5]
    norm_num
  have hT : johnsonCurveBound (Fintype.card (Fin 5)) 2 (2 - 1) 5 1 (Fintype.card (Fin 5)) < #T := by
    rw [Fintype.card_fin, hT_card]
    change johnsonCurveBound 5 2 1 5 1 5 < 30808
    omega
  have hinterp : Fintype.card (Fin 5) * (2 * (2 + 1) / 2) < #(Sudan.monomials (2 - 1) 5) := by
    rw [Fintype.card_fin]
    change 5 * 3 < #(Sudan.monomials 1 5)
    rw [card_monomials_1_5]
    omega
  have hclose : ∀ z ∈ T, ∃ c ∈ reedSolomon αQ 2, hammingDist (u0 + z • u1) c ≤ 2 := by
    intro z _
    refine ⟨v0 + z • v1, Submodule.add_mem _ hv0 (Submodule.smul_mem _ z hv1), ?_⟩
    refine hammingDist_le_of_agree_subset (A := {0, 1, 2}) (by decide) ?_
    intro i hi
    fin_cases hi <;> simp [u0, u1]
  obtain ⟨D', hD', w₀, hw₀, w₁, hw₁, hagree⟩ :=
    exists_correlatedAgreement_line_johnson hαQ (k := 2) (e := 2) (m := 2) (D := 5)
      (by omega) (by omega) (by rw [Fintype.card_fin]; omega) hinterp
      (by rw [Fintype.card_fin]; omega) u0 u1 T hT hclose
  rw [Fintype.card_fin] at hD'
  exact ⟨u0, u1, hu0, hu1, D', hD', w₀, hw₀, w₁, hw₁, hagree⟩

/-! ### 6. Finite-field proximity-gap dichotomies (`k = 1`, `e = 1` and `e = 0`, RHS `< 1`) -/

/-- Helper: every codeword in `reedSolomon α 1` is a constant function. -/
private theorem eq_const_of_mem_rs1 {F ι : Type*} [Field F] {α : ι → F} {c : ι → F}
    (hc : c ∈ reedSolomon α 1) : ∃ a : F, ∀ i, c i = a := by
  obtain ⟨p, hp, rfl⟩ := mem_reedSolomon.1 hc
  refine ⟨p.coeff 0, fun i => ?_⟩
  have hdeg0 : p.natDegree = 0 := by
    by_cases hp0 : p = 0
    · rw [hp0, natDegree_zero]
    · have := (natDegree_lt_iff_degree_lt hp0).2 hp
      omega
  dsimp only
  conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg0]
  rw [eval_C]

/-- Concrete non-everywhere-close instantiation of `proximityGap_line_johnson` over
`ZMod 15000017` (`n = 5`, `k = 1`, `e = 1`, `m = 1`): refutes the everywhere-close branch and
establishes a nontrivial error fraction `≤ 14400000 / 15000017 < 1`. -/
example : open scoped Classical in
    let α : Fin 5 → ZMod 15000017 := fun i => (i.val : ZMod 15000017)
    let u₀ : Fin 5 → ZMod 15000017 := ![0, 0, 1, 2, 3]
    let u₁ : Fin 5 → ZMod 15000017 := 0
    ((#(Finset.univ.filter fun z : ZMod 15000017 =>
        ∃ c ∈ reedSolomon α 1, hammingDist (u₀ + z • u₁) c ≤ 1) : ℝ) /
      (Fintype.card (ZMod 15000017) : ℝ)) < 1 := by
  classical
  intro α u₀ u₁
  have hα : Function.Injective α := by
    intro i j h
    have hv := congrArg ZMod.val h
    dsimp only [α] at hv
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv
    exact Fin.ext hv
  have he : ((1 : ℕ) : ℝ) / (Fintype.card (Fin 5) : ℝ) ≤
      1 - Real.sqrt (((1 : ℕ) : ℝ) / (Fintype.card (Fin 5) : ℝ)) -
        Real.sqrt (((1 : ℕ) : ℝ) / (Fintype.card (Fin 5) : ℝ)) / (2 * ((1 : ℕ) : ℝ)) := by
    rw [Fintype.card_fin]
    have hsq : Real.sqrt ((1 : ℝ) / 5) ≤ 8 / 15 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    push_cast
    linarith
  have hnot_all : ¬ (∀ z : ZMod 15000017,
      ∃ c ∈ reedSolomon α 1, hammingDist (u₀ + z • u₁) c ≤ 1) := by
    intro hall
    obtain ⟨c, hc_rs, hdist⟩ := hall 0
    rw [zero_smul, add_zero] at hdist
    obtain ⟨a, ha⟩ := eq_const_of_mem_rs1 hc_rs
    have hpair : ∀ i j : Fin 5, u₀ i ≠ u₀ j → (u₀ i ≠ c i ∨ u₀ j ≠ c j) := by
      intro i j hne
      by_contra hboth
      push Not at hboth
      exact hne (by rw [hboth.1, hboth.2, ha i, ha j])
    have h23 : u₀ 2 ≠ c 2 ∨ u₀ 3 ≠ c 3 := hpair 2 3 (by decide)
    have h04 : u₀ 0 ≠ c 0 ∨ u₀ 4 ≠ c 4 := hpair 0 4 (by decide)
    have h2 : 2 ≤ hammingDist u₀ c := by
      rcases h23 with hA | hA <;> rcases h04 with hB | hB
      · have hsub : ({2, 0} : Finset (Fin 5)) ⊆ Finset.univ.filter (fun i => u₀ i ≠ c i) := by
          intro i hi; fin_cases hi <;> simp [hA, hB]
        exact (by decide : 2 ≤ #({2, 0} : Finset (Fin 5))).trans (card_le_card hsub)
      · have hsub : ({2, 4} : Finset (Fin 5)) ⊆ Finset.univ.filter (fun i => u₀ i ≠ c i) := by
          intro i hi; fin_cases hi <;> simp [hA, hB]
        exact (by decide : 2 ≤ #({2, 4} : Finset (Fin 5))).trans (card_le_card hsub)
      · have hsub : ({3, 0} : Finset (Fin 5)) ⊆ Finset.univ.filter (fun i => u₀ i ≠ c i) := by
          intro i hi; fin_cases hi <;> simp [hA, hB]
        exact (by decide : 2 ≤ #({3, 0} : Finset (Fin 5))).trans (card_le_card hsub)
      · have hsub : ({3, 4} : Finset (Fin 5)) ⊆ Finset.univ.filter (fun i => u₀ i ≠ c i) := by
          intro i hi; fin_cases hi <;> simp [hA, hB]
        exact (by decide : 2 ≤ #({3, 4} : Finset (Fin 5))).trans (card_le_card hsub)
    omega
  have hgap := proximityGap_line_johnson (e := 1) (k := 1) (m := 1) hα (by omega)
    (by rw [Fintype.card_fin]; omega) (by omega) he u₀ u₁
  have hle := hgap.resolve_left hnot_all
  refine hle.trans_lt ?_
  rw [Fintype.card_fin, ZMod.card]
  norm_num

section ExtensionFieldGap

private noncomputable local instance : Fintype (GaloisField 5 13) := Fintype.ofFinite _

/-- Concrete `k = 1`, `e = 0` boundary instantiation of `proximityGap_line_johnson_of_eta` over
the non-prime finite extension field `GaloisField 5 13` (`|𝔽_{5^13}| = 1,220,703,125`, `n = 4`,
`ρ = 1 / 4`, `η = 1 / 2`): refutes the everywhere-close branch and establishes a nontrivial error
fraction `≤ 471859200 / 5^13 < 1`. -/
example : open scoped Classical in
    let α : Fin 4 → GaloisField 5 13 :=
      fun i => algebraMap (ZMod 5) (GaloisField 5 13) (i.val : ZMod 5)
    let u₀ : Fin 4 → GaloisField 5 13 := α
    let u₁ : Fin 4 → GaloisField 5 13 := 0
    ((#(Finset.univ.filter fun z : GaloisField 5 13 =>
        ∃ c ∈ reedSolomon α 1, hammingDist (u₀ + z • u₁) c ≤ 0) : ℝ) /
      (Fintype.card (GaloisField 5 13) : ℝ)) < 1 := by
  classical
  intro α u₀ u₁
  have hcard : Fintype.card (GaloisField 5 13) = 5 ^ 13 :=
    (Nat.card_eq_fintype_card (α := GaloisField 5 13)).symm.trans (GaloisField.card 5 13 (by omega))
  have hα : Function.Injective α := by
    intro i j h
    have h1 : (i.val : ZMod 5) = (j.val : ZMod 5) :=
      (algebraMap (ZMod 5) (GaloisField 5 13)).injective h
    have hv := congrArg ZMod.val h1
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv
    exact Fin.ext hv
  have he : ((0 : ℕ) : ℝ) / (Fintype.card (Fin 4) : ℝ) ≤
      1 - Real.sqrt (((1 : ℕ) : ℝ) / (Fintype.card (Fin 4) : ℝ)) - (1 / 2 : ℝ) := by
    rw [Fintype.card_fin]
    have hsq : Real.sqrt ((1 : ℝ) / 4) = 1 / 2 := by
      rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
      norm_num
    push_cast
    linarith
  have hnot_all : ¬ (∀ z : GaloisField 5 13,
      ∃ c ∈ reedSolomon α 1, hammingDist (u₀ + z • u₁) c ≤ 0) := by
    intro hall
    obtain ⟨c, hc_rs, hdist⟩ := hall 0
    rw [zero_smul, add_zero] at hdist
    have heq : u₀ = c := hammingDist_eq_zero.1 (Nat.eq_zero_of_le_zero hdist)
    obtain ⟨a, ha⟩ := eq_const_of_mem_rs1 hc_rs
    have h01 : u₀ 0 = u₀ 1 := by rw [heq, ha 0, ha 1]
    have hne : (0 : Fin 4) ≠ 1 := by decide
    exact hne (hα h01)
  have hgap := proximityGap_line_johnson_of_eta (e := 0) (k := 1) (η := 1 / 2) hα (by omega)
    (by rw [Fintype.card_fin]; omega) (by norm_num) he u₀ u₁
  have hle := hgap.resolve_left hnot_all
  refine hle.trans_lt ?_
  rw [Fintype.card_fin, hcard]
  norm_num

end ExtensionFieldGap

/-! ### 7. Scaling and curve/line parameter-packaging helpers -/

/-- Exercises the public scaling and parameter-packaging helpers `johnsonCurveBound_mul_le`,
`johnson_curve_params_bound`, `johnson_line_params_bound`, and `exists_multiplicity_of_eta` used by
downstream M4/M5 modules. -/
example :
    johnsonCurveBound 5 2 1 5 1 16 * 5 ≤ johnsonCurveBound 5 2 1 5 1 5 * 16 ∧
    (∃ m : ℕ, 1 ≤ m ∧
      ((0 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) ≤
        1 - Real.sqrt (((1 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) -
          Real.sqrt (((1 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) / (2 * (m : ℝ)) ∧
      ((m + 1 : ℝ) ^ 6) ≤ 64 / ((1 / 4 : ℝ) ^ 6)) ∧
    (∃ D : ℕ, 5 * (2 * (2 + 1) / 2) < #(Sudan.monomials (1 - 1) D) ∧
      D < 2 * (5 - 1) ∧
      (johnsonCurveBound 5 2 (1 - 1) D 3 5 : ℝ) ≤
        1800 * ((3 : ℕ) : ℝ) * (((1 : ℕ) + 1 : ℝ) ^ 6) * (((5 : ℕ) : ℝ) ^ 2) /
          (((1 : ℕ) : ℝ) / ((5 : ℕ) : ℝ))) := by
  have he_eta : ((0 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) ≤
      1 - Real.sqrt (((1 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) - (1 / 4 : ℝ) := by
    have hsq : Real.sqrt ((1 : ℝ) / 4) = 1 / 2 := by
      rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
      norm_num
    push_cast
    linarith
  refine ⟨johnsonCurveBound_mul_le (by omega),
    exists_multiplicity_of_eta (n := 4) (k := 1) (e := 0) (η := 1 / 4)
      (by omega) (by omega) (by norm_num) he_eta, ?_⟩
  have he : ((1 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) ≤
      1 - Real.sqrt (((1 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) -
        Real.sqrt (((1 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) / (2 * ((1 : ℕ) : ℝ)) := by
    have hsq : Real.sqrt ((1 : ℝ) / 5) ≤ 8 / 15 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    push_cast
    linarith
  obtain ⟨_, hmon, hroot, hbound⟩ := johnson_curve_params_bound (n := 5) (k := 1) (e := 1) (m := 1)
    (r := 3) (by omega) (by omega) (by omega) (by omega) he
  have _hline := johnson_line_params_bound (n := 5) (k := 1) (e := 1) (m := 1)
    (by omega) (by omega) (by omega) he
  exact ⟨_, hmon, hroot, hbound⟩

end CslibFrontierTests.Foundations.Data.Code.ProximityGap.Johnson
