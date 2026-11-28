/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Code.ProximityGap.Johnson.DegZ
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.SeparableDegree

/-!
# Step 3: Separable Contraction of Irreducible Trivariate Polynomials

Contracts an irreducible polynomial `R ∈ F[Z][X][Y]` in positive characteristic to a separable
polynomial `S(Z, X, Y)` with `expand F μ S = R` and produces a Bézout identity
`S * A + S' * B = C Δ` over `F[Z][X]` with explicit degree bounds on `Δ`.

## Main results

* `Cslib.Code.ProximityGap.exists_separable_contraction_and_bezout`: separable contraction with
  Bézout certificate and weighted-degree / `Z`-degree bounds.
-/

public section

namespace Cslib.Code.ProximityGap

open Finset Polynomial Polynomial.Bivariate

variable {F : Type*} [Field F]

theorem coeff_expand_eq_zero_of_not_dvd {R : Type*} [CommSemiring R] {μ : ℕ}
    (hμ : 0 < μ) (p : R[X]) {b : ℕ} (hb : ¬ μ ∣ b) :
    (Polynomial.expand R μ p).coeff b = 0 := by
  rw [Polynomial.coeff_expand hμ, ite_eq_right (fun h => absurd h hb)]

/-- Step 3: Positive-characteristic-safe separable contraction `R = expand (F[Z][X]) μ S` directly
in `F[Z][X][Y]`, together with the nonzero resultant `Δ = Res_Y(S, S')` and Bézout identity
`S * A_bez + S' * B_bez = C Δ`. -/
theorem exists_separable_contraction_and_bezout {d D B_Z : ℕ}
    {R : F[X][X][X]}
    (hR_irred : Irreducible R) (hR_deg : 1 ≤ R.natDegree)
    (hR_wd : weightedDegree d R ≤ D) (hR_degZ : degZ R ≤ B_Z) :
    ∃ (μ : ℕ) (S A_bez B_bez : F[X][X][X]) (Δ : F[X][X]),
      (μ = 1 ∨ ∃ (p e : ℕ), CharP F p ∧ p.Prime ∧ μ = p ^ e) ∧
      1 ≤ μ ∧
      Polynomial.expand (F[X][X]) μ S = R ∧
      1 ≤ S.natDegree ∧
      μ * S.natDegree = R.natDegree ∧
      μ * d ≤ D ∧
      (∀ a b, ((S.coeff b).coeff a) ≠ 0 → a + (μ * d) * b ≤ D) ∧
      degZ S ≤ B_Z ∧
      Δ ≠ 0 ∧
      S * A_bez + S.derivative * B_bez = C Δ ∧
      (S.leadingCoeff * Δ).natDegree ≤ 2 * S.natDegree * D ∧
      degZ₂ (S.leadingCoeff * Δ) ≤ 2 * S.natDegree * B_Z := by
  classical
  let E := FractionRing (F[X][X])
  let ι_E : F[X][X] →+* E := algebraMap (F[X][X]) E
  have hι_E_inj : Function.Injective ι_E := IsFractionRing.injective (F[X][X]) E
  have hR_E_irred : Irreducible (R.map ι_E) :=
    ((hR_irred.isPrimitive (by omega)).irreducible_iff_irreducible_map_fraction_map).1 hR_irred
  obtain ⟨q, hExpF⟩ := ExpChar.exists F
  have hF_to_E : Function.Injective
      (ι_E.comp (Polynomial.C.comp Polynomial.C : F →+* F[X][X])) :=
    hι_E_inj.comp (Polynomial.C_injective.comp Polynomial.C_injective)
  have hExpE : ExpChar E q := expChar_of_injective_ringHom hF_to_E q
  obtain ⟨S_E, hS_E_sep, e_sep, hS_E_exp⟩ := hR_E_irred.hasSeparableContraction q
  set μ := q ^ e_sep
  have hμ_pos : 1 ≤ μ := Nat.one_le_pow e_sep q (expChar_pos F q)
  have hμ_ne : μ ≠ 0 := by omega
  have hμ_char : μ = 1 ∨ ∃ (p e : ℕ), CharP F p ∧ p.Prime ∧ μ = p ^ e := by
    cases hExpF with
    | zero => exact Or.inl (by simp [μ])
    | prime hp => exact Or.inr ⟨q, e_sep, inferInstance, hp, rfl⟩
  set S : F[X][X][X] := Polynomial.contract μ R
  have hexp_S : Polynomial.expand (F[X][X]) μ S = R := by
    ext b : 2
    rw [Polynomial.coeff_expand hμ_pos]
    split_ifs with hdiv
    · rw [Polynomial.coeff_contract hμ_ne, Nat.div_mul_cancel hdiv]
    · exact hι_E_inj <| by
        rw [← coeff_map, ← hS_E_exp, coeff_expand_eq_zero_of_not_dvd hμ_pos S_E hdiv, map_zero]
  have hS_map : S.map ι_E = S_E := by
    ext b
    rw [coeff_map, Polynomial.coeff_contract hμ_ne, ← coeff_map, ← hS_E_exp,
      Polynomial.coeff_expand_mul hμ_pos]
  have hdeg_mul : μ * S.natDegree = R.natDegree := by
    rw [← hexp_S, Polynomial.natDegree_expand, mul_comm]
  have hS_deg : 1 ≤ S.natDegree := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at hdeg_mul; omega
  have hS_wd : ∀ a b, ((S.coeff b).coeff a) ≠ 0 → a + (μ * d) * b ≤ D := fun a b hab => by
    rw [Polynomial.coeff_contract hμ_ne] at hab
    rw [show (μ * d) * b = d * (b * μ) by ring]
    exact (le_weightedDegree (d := d) hab).trans hR_wd
  have hμd_le : μ * d ≤ D := by
    have hlc : S.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 fun h => by simp [h] at hS_deg
    have h1 := hS_wd _ _ (leadingCoeff_ne_zero.2 hlc)
    have h2 := Nat.le_mul_of_pos_right (μ * d) hS_deg
    omega
  have hS_degZ : degZ S ≤ B_Z := degZ_le_iff.2 fun a b => by
    rw [Polynomial.coeff_contract hμ_ne]; exact degZ_le_iff.1 hR_degZ a (b * μ)
  set Δ : F[X][X] := Polynomial.resultant S S.derivative S.natDegree S.derivative.natDegree
  have hΔ_ne : Δ ≠ 0 := resultant_ne_zero_of_isCoprime_map ι_E hι_E_inj
    (by rwa [← Polynomial.derivative_map, hS_map])
  obtain ⟨A_bez, B_bez, _, _, hbez⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant S S.derivative le_rfl le_rfl (Or.inl (by omega))
  have hS_coeff_degX : ∀ b, (S.coeff b).natDegree ≤ D := fun b =>
    natDegree_le_iff_coeff_eq_zero.2 fun a ha =>
      by_contra fun hne => by have := hS_wd a b hne; omega
  exact ⟨μ, S, A_bez, B_bez, Δ, hμ_char, hμ_pos, hexp_S, hS_deg, hdeg_mul, hμd_le, hS_wd, hS_degZ,
    hΔ_ne, hbez,
    (DegBound.natDegree F[X]).leadingCoeff_mul_resultant_derivative_le hS_deg hS_coeff_degX,
    (DegBound.degZ₂ F).leadingCoeff_mul_resultant_derivative_le hS_deg
      (fun b => (degZ₂_coeff_le_degZ S b).trans hS_degZ)⟩

end Cslib.Code.ProximityGap
