/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.Complexity.RealAlgebraic.QuotientTraceEvaluation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Uniform modular traces, empty systems and a repeated-root quotient -/

public section

namespace CslibFrontierTests.RealAlgebraicResidues

open Cslib Cslib.Complexity Cslib.Complexity.RealAlgebraic
open Turing.MultiTapeTM MvPolynomial MvPolynomial.PurePower

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private instance : Fact (Nat.Prime 11) := ⟨by decide⟩

-- Missing exponents are zero; surplus entries do not change the empty product.
example : (indexedPowerProduct 7 0 [9] (fun _ => 4) : ZMod 7) = 1 := by
  rw [indexedPowerProduct_cast]
  simp

-- The empty residue has one summand and recovers its scalar numerator.
example : (residueValue 5 0 2 0 (fun _ => 3) (fun _ _ => 0) : ZMod 5) = 3 := by
  let r : Fin 0 → MvPolynomial (Fin 0) (ZMod 5) := fun _ => 0
  have hr (i : Fin 0) : (r i).totalDegree < 2 := i.elim0
  have hdeg : (C (3 : ZMod 5) : MvPolynomial (Fin 0) (ZMod 5)).totalDegree ≤ 0 :=
    (totalDegree_C _).le
  rw [residueValue_cast (by decide) r hr (C 3) hdeg (by decide)
    (fun _ => 3) (fun _ _ => 0) (by intro s _; simp) (by intro i; exact i.elim0),
    residue_low_degree (by decide) r hr (C 3) hdeg]
  have he : Finsupp.equivFunOnFinite.symm (fun _ : Fin 0 => 2 - 1) = (0 : Fin 0 →₀ ℕ) :=
    Subsingleton.elim _ _
  rw [he]
  simp

-- One machine accepts a binary modulus and power, including their total off-domain defaults.
theorem uniform_empty_trace_mem : (fun w : ℕ × ℕ => quotientTraceValue w.1 0 2 0 w.2
    (fun _ => 3) (fun _ => 1) (fun _ _ => 0)) ∈
    CountingFunction 5 (encPair encNat encNat) encNat := by
  apply quotientTraceValue_mem (a := 0) (p := fun w : ℕ × ℕ => w.1)
    (n := fun _ => 0) (ell := fun _ => 2) (B := fun _ => 0) (k := fun w => w.2)
    (v := fun _ => 3) (J := fun _ => 1) (r := fun _ => 0)
    (Decoder.pair Decoder.nat Decoder.nat)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  all_goals exact CountingFunction.of_polyTime (ComputableInPolyTime.const _)

private noncomputable abbrev lower : Fin 1 → MvPolynomial (Fin 1) (ZMod 11) := fun _ => 0

private theorem lower_degree (i : Fin 1) : (lower i).totalDegree < 2 := by
  simp [lower]

private theorem jacobian_squareZero : jacobian 2 lower = C 2 * X 0 := by
  rw [map_ofNat]
  simp [jacobian, lower]

private theorem residue_X : residue 2 lower (X 0) = 1 := by
  rw [residue_low_degree (by decide) lower lower_degree _ (totalDegree_X_le 0)]
  have he : Finsupp.equivFunOnFinite.symm (fun _ : Fin 1 => 2 - 1) =
      Finsupp.single 0 1 := by
    apply Finsupp.ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp
  rw [he]
  simp [X]

private theorem squareZero_trace_cast (k : ℕ) (hk : k ≤ 1) :
    (quotientTraceValue 11 1 2 (k + 1) k
      (fun z => z[0]?.getD 0) (fun z => 2 * z[0]?.getD 0) (fun _ _ => 0) : ZMod 11) =
      ((multiplicationMatrix (by decide) lower lower_degree (X 0)) ^ k).trace := by
  apply quotientTraceValue_cast 1 (by decide) lower (by intro i; simp [lower]) (X 0)
  · rw [jacobian_squareZero]
    have hX : (X 0 : MvPolynomial (Fin 1) (ZMod 11)).totalDegree ≤ 1 := totalDegree_X_le 0
    have hpow : (X 0 ^ k : MvPolynomial (Fin 1) (ZMod 11)).totalDegree ≤ k := by
      simpa only [Nat.mul_one] using
        (totalDegree_pow (X 0) k).trans (Nat.mul_le_mul_left k hX)
    have hJ : (C 2 * X 0 : MvPolynomial (Fin 1) (ZMod 11)).totalDegree ≤ 1 :=
      (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, Nat.zero_add] using hX)
    exact (totalDegree_mul _ _).trans (Nat.add_le_add hpow hJ)
  · omega
  · intro s _
    simp
  · intro s _
    simp [jacobian_squareZero]
  · intro i s _
    simp [lower]

-- The evaluator computes the traces of 1 and X in F₁₁[X]/(X²), a nonreduced algebra.
example : (quotientTraceValue 11 1 2 1 0
    (fun z => z[0]?.getD 0) (fun z => 2 * z[0]?.getD 0) (fun _ _ => 0) : ZMod 11) = 2 := by
  rw [squareZero_trace_cast 0 (by decide),
    multiplicationMatrix_trace_pow 1 (by decide) lower (by intro i; simp [lower])]
  rw [pow_zero, one_mul, jacobian_squareZero, ← smul_eq_C_mul,
    residue_smul (by decide) lower lower_degree, residue_X]
  simp

example : (quotientTraceValue 11 1 2 2 1
    (fun z => z[0]?.getD 0) (fun z => 2 * z[0]?.getD 0) (fun _ _ => 0) : ZMod 11) = 0 := by
  rw [squareZero_trace_cast 1 (by decide),
    multiplicationMatrix_trace_pow 1 (by decide) lower (by intro i; simp [lower]), pow_one]
  change linear (by decide) lower lower_degree (X 0 * jacobian 2 lower) = 0
  apply linear_mem_ideal
  have hprod : X 0 * jacobian 2 lower = C 2 * (X 0 ^ 2 - lower 0) := by
    rw [jacobian_squareZero]
    simp only [lower, sub_zero]
    ring
  rw [hprod]
  exact (relationIdeal 2 lower).mul_mem_left (C 2) (Ideal.subset_span ⟨0, rfl⟩)

end CslibFrontierTests.RealAlgebraicResidues
