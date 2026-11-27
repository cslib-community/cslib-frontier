/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/
module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalCoefficientEvaluation
import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalParameterEvaluation
import CslibFrontier.Foundations.Algebra.Polynomial.DyadicSignApproximation
import CslibFrontier.Foundations.Algebra.Polynomial.DyadicSignProduct
import CslibFrontier.Foundations.Algebra.Polynomial.DyadicSignProductBounds
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.AlgebraicValueBounds
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.BranchCutoff
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.ConjugateProduct
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.ShiftedLabel
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.SparseIntegerRootLabel
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.SparseRootDeterminant
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.SparseRootProduct
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.ThomSign
import CslibFrontier.Foundations.Algebra.Polynomial.SignLabelPolynomial
import CslibFrontier.Foundations.Algebra.Polynomial.SignLabelPolynomialBounds
import CslibFrontier.Foundations.Analysis.Complex.ConjugateProduct
import CslibFrontier.Foundations.Analysis.MvPolynomial.CriticalDeterminantFeasibility
import CslibFrontier.Foundations.Analysis.MvPolynomial.CriticalMinimumValue
import CslibFrontier.Foundations.Analysis.MvPolynomial.CriticalRootFeasibility
import CslibFrontier.Foundations.Analysis.SignLabelScore
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Charpoly.EvalDeterminant
import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CriticalValuePolynomial
import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CriticalIntegerSpecialization
import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CriticalValueParameterDegree
import CslibFrontier.Foundations.Data.Polynomial.CoeffList
import CslibFrontier.Foundations.Data.MvPolynomial.Degrees
import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.InitialCriticalSeparability
import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.ResidueCoeffNorm
import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.SeparatedCriticalValues
import CslibFrontier.Foundations.RingTheory.Polynomial.ValueResultant
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Constructed critical coefficient certificates and edge cases -/

public section
namespace CslibFrontierTests.RealAlgebraicCriticalCoefficients

open Cslib Cslib.Complexity Cslib.Complexity.RealAlgebraic Turing.MultiTapeTM
open MvPolynomial MvPolynomial.CriticalSystem MvPolynomial.PurePower

private instance : Fact (Nat.Prime 101) := ⟨by decide⟩

-- Above-dimension addresses return zero even for arbitrary evaluators and nonprime moduli.
example (p n ell B m : ℕ) (hm : ell ^ n < m)
    (v J : List ℕ → ℕ) (r : ℕ → List ℕ → ℕ) :
    quotientCharacteristicValue p n ell B m v J r = 0 := by
  simp [quotientCharacteristicValue, traceExponentialCoefficient, Nat.not_le.mpr hm]

-- A single certificate handles binary deformation parameters and coefficient addresses.
example : (fun q : ℕ × ℕ => criticalCoefficientValue 101 1 1 q.1 q.2 (fun _ => 0)) ∈
    CountingFunction 9 (encPair encNat encNat) encNat := by
  simpa using criticalCoefficientValue_mem (a := 0) (Decoder.pair Decoder.nat Decoder.nat)
    (p := fun _ => 101) (n := fun _ => 1) (d := fun _ => 1)
    (u := fun q : ℕ × ℕ => q.1) (m := fun q => q.2) (value := fun _ => 0)
    (.const 101) (.const 1) (.const 1) (by fun_prop) (by fun_prop)
    (CountingFunction.of_polyTime (.const 0))

-- A positive-dimensional instance satisfies all cutoffs, including at zero deformation.
theorem positiveDimensionalInstance (u m : ℕ) : criticalCoefficientValue 101 1 1 u m (fun _ => 0) =
    ((multiplicationMatrix (by decide : 1 ≤ 2)
      (criticalLower 2 (fun i : Fin 1 => ((separatedCenters 2 i : ℕ) : ZMod 101))
        (u : ZMod 101) 0)
      (criticalLower_degree 2 (by decide) _ _ 0 (by simp))
      (deformedPolynomial 2 (fun i : Fin 1 => ((separatedCenters 2 i : ℕ) : ZMod 101))
        (u : ZMod 101) 0)).charpoly.coeff m).val := by
  apply criticalCoefficientValue_eq 1 (by decide) u 0 (by simp) (by decide) (by decide)
  intro y
  simp

-- Reducing the integer quotient modulo 101 preserves the constant coefficient of `X - 1`.
example : quotientCharacteristicValue 101 0 2 0 0 (fun _ => 1) (fun _ => 1)
    (fun _ _ => 0) = 100 := by
  have h := quotientCharacteristicValue_eq_specialization (p := 101) (n := 0) (B := 0) (m := 0)
    (Int.castRingHom (ZMod 101)) 1 (by decide) (fun _ => 0) (by simp)
    (1 : MvPolynomial (Fin 0) ℤ)
    (by intro k _ _; simp [jacobian, Matrix.det_isEmpty]) (by decide) (by decide)
    (fun _ => 1) (fun _ => 1) (fun _ _ => 0)
    (by simp) (by simp [jacobian, Matrix.det_isEmpty]) (by simp)
  have hdim : Fintype.card (NormalIndex 0 2) = 1 := by simp [NormalIndex]
  simpa [Matrix.charpoly_one, hdim, ZMod.val_neg_one] using h

-- The relation X₀² = 102 changes to X₀² = 1 modulo 101. Multiplication by X₀
-- has constant characteristic coefficient -102 over ℤ, which reduces to 100.
example : quotientCharacteristicValue 101 1 2 3 0
    (fun z => z[0]?.getD 0) (fun z => 2 * z[0]?.getD 0) (fun _ _ => 1) = 100 := by
  let r : Fin 1 → MvPolynomial (Fin 1) ℤ := fun _ => C 102
  let x : MvPolynomial (Fin 1) ℤ := X 0
  have hr (i : Fin 1) : (r i).totalDegree ≤ 1 := by
    simp only [r, totalDegree_C, Nat.zero_le]
  have hJ : jacobian 2 r = C 2 * x := by
    rw [jacobian, Matrix.det_fin_one]
    change pderiv (0 : Fin 1) (x ^ 2 - C 102) = C 2 * x
    rw [map_sub, pderiv_C, sub_zero, pderiv_pow]
    norm_num [x, C_eq_natCast]
  have hx : x.totalDegree ≤ 1 := totalDegree_X_le _
  have hCdeg (c : ℤ) : (C c * x).totalDegree ≤ 1 := by
    have hm := totalDegree_mul (C c) x
    rw [totalDegree_C, zero_add] at hm
    exact hm.trans hx
  have hdeg (k : ℕ) (_hk : 1 ≤ k) (hK : k ≤ 2 ^ 1) :
      (x ^ k * jacobian 2 r).totalDegree ≤ 3 := by
    rw [hJ]
    have hk : (x ^ k).totalDegree ≤ 2 := by
      refine (totalDegree_pow x k).trans ?_
      simpa only [pow_one, mul_one] using Nat.mul_le_mul hK hx
    exact (totalDegree_mul _ _).trans (Nat.add_le_add hk (hCdeg 2))
  have h := quotientCharacteristicValue_eq_specialization (p := 101) (n := 1) (B := 3) (m := 0)
    (Int.castRingHom (ZMod 101)) 1 (by decide) r hr x hdeg (by decide) (by decide)
    (fun z => z[0]?.getD 0) (fun z => 2 * z[0]?.getD 0) (fun _ _ => 1)
    (by simp [x]) (by simp [hJ, x]) (by
      intro i s hs
      simp only [r, map_C, eval_C]
      decide)
  let M := multiplicationMatrix (by decide : 1 ≤ 2) r
    (fun i => (hr i).trans_lt (by decide)) x
  have htrace (k : ℕ) : (M ^ k).trace = residue 2 r (x ^ k * (C 2 * x)) := by
    rw [multiplicationMatrix_trace_pow 1 (by decide) r hr, hJ]
  have htop : Finsupp.equivFunOnFinite.symm (fun _ : Fin 1 => 2 - 1) =
      Finsupp.single (0 : Fin 1) 1 := by
    apply Finsupp.ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp
  have ht1 : M.trace = 0 := by
    rw [← pow_one M, htrace, pow_one,
      show x * (C 2 * x) = C 2 * x ^ 2 by ring,
      residue_mul_X_pow (by decide) r (fun i => (hr i).trans_lt (by decide)),
      show r 0 = C 102 from rfl,
      ← map_mul, residue_low_degree (by decide) _ (fun i => (hr i).trans_lt (by decide)) _
        (by rw [totalDegree_C]; decide), htop]
    simp
  have ht2 : (M ^ 2).trace = 204 := by
    rw [htrace, show x ^ 2 * (C 2 * x) = (C 2 * x) * x ^ 2 by ring,
      residue_mul_X_pow (by decide) r (fun i => (hr i).trans_lt (by decide)),
      show r 0 = C 102 from rfl,
      show C 2 * x * C 102 = C 204 * x by rw [mul_right_comm, ← map_mul]; norm_num,
      residue_low_degree (by decide) r (fun i => (hr i).trans_lt (by decide)) _ (hCdeg 204),
      htop, show x = X 0 from rfl, C_mul_X_eq_monomial, coeff_monomial]
    simp
  have hdim : Fintype.card (NormalIndex 1 2) = 2 := by simp [NormalIndex]
  have hnewton := Matrix.charpolyRev_newton M 1
  have hc0 : M.charpolyRev.coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
  have hrev : M.charpolyRev.coeff 2 = M.charpoly.coeff 0 := by
    rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim,
      hdim, Polynomial.revAt_le (by decide : 2 ≤ 2)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_one, ht1, mul_zero,
    hc0, ht2, one_mul, hrev] at hnewton
  have hcoeff : M.charpoly.coeff 0 = -102 := by omega
  change _ = (Int.castRingHom (ZMod 101) (M.charpoly.coeff 0)).val at h
  rw [h, hcoeff]
  decide

-- In one variable, the residue of X₀³ modulo X₀² - U is the parameter U.
-- The norm bound applies with unit relation norm even though the numerator needs reduction.
example :
    let U : Polynomial ℤ := Polynomial.X
    let r : Fin 1 → MvPolynomial (Fin 1) (Polynomial ℤ) := fun _ => C U
    let x : MvPolynomial (Fin 1) (Polynomial ℤ) := X 0
    residue 2 r (x ^ 3) = U ∧ Polynomial.coeffNorm1 (residue 2 r (x ^ 3)) ≤ 4 := by
  intro U r x
  have hU : Polynomial.coeffNorm1 U = 1 := by
    simpa only [U, mul_one, Polynomial.coeffNorm1_one] using
      Polynomial.coeffNorm1_X_mul (1 : Polynomial ℤ)
  have hr (i : Fin 1) : (r i).totalDegree < 2 := by
    simp only [r, totalDegree_C]
    decide
  have hdeg : (x ^ 3).totalDegree ≤ 3 := (totalDegree_pow _ _).trans (by simp [x])
  have h := coeffNorm1_residue_le (B := 3) (R := 1) (by decide : 1 ≤ 2) (by decide)
    r hr (fun _ => by simp [r, hU]) _ hdeg
  have hv := ParameterCoeffNorm.pow_le x 3
  simp only [x, ParameterCoeffNorm.X, one_pow] at hv
  refine ⟨?_, h.trans (by simpa using Nat.mul_le_mul_left 4 hv)⟩
  have hlow : (x * r 0).totalDegree ≤ 1 * (2 - 1) := by
    have hmul := totalDegree_mul x (r 0)
    simpa only [r, x, totalDegree_C, add_zero, totalDegree_X, Nat.reduceSub, one_mul] using hmul
  rw [show x ^ 3 = x * (X (0 : Fin 1)) ^ 2 by dsimp only [x]; ring,
    residue_mul_X_pow (by decide) r hr, residue_low_degree (by decide) r hr _ hlow]
  have htop : Finsupp.equivFunOnFinite.symm (fun _ : Fin 1 => 2 - 1) =
      Finsupp.single (0 : Fin 1) 1 := by
    apply Finsupp.ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp
  rw [htop]
  change (X (0 : Fin 1) * C U).coeff (Finsupp.single 0 1) = U
  rw [mul_comm, C_mul_X_eq_monomial, coeff_monomial, ite_eq_left rfl]

-- In characteristic two the normalized relation is x² = 1 and the potential is x³ − x.
-- Therefore the specialized multiplication operator is zero on the two-dimensional quotient.
example :
    let F : MvPolynomial (Fin 1) ℤ := X 0
    let hF : F.totalDegree ≤ 2 := by simp [F]
    (parametricValuePolynomial (by decide : 1 ≤ 2) F hF).map
        (Polynomial.eval₂RingHom (Int.castRingHom (ZMod 2)) 1) =
      Polynomial.X ^ 2 := by
  intro F hF
  rw [parametricValuePolynomial_map_eval₂]
  let G : MvPolynomial (Fin 1) (ZMod 2) := X 0
  let a (i : Fin 1) : ZMod 2 := separatedCenters 2 i
  let r := criticalLower 2 a 1 G
  let π := projection 2 r
  have ha (i : Fin 1) : a i = 0 := by
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    decide
  have hr : r 0 = 1 := by
    calc
      r 0 = -1 := by simp [r, criticalLower, ha, G]
      _ = C (-(1 : ZMod 2)) := by rw [map_neg, map_one]
      _ = 1 := by rw [show -(1 : ZMod 2) = 1 by decide, map_one]
  have hproj : π (G ^ 2) = 1 := by
    change projection 2 r (X 0 ^ 2) = 1
    rw [map_pow, projection_X_pow, hr, map_one]
  have hpot : potentialPolynomial 2 a = G ^ 3 := by
    simp [potentialPolynomial, ha, G]
  have hdef : deformedPolynomial 2 a 1 G = G ^ 3 - G := by
    rw [deformedPolynomial, hpot, show (((2 + 1 : ℕ) : ZMod 2) * 1) = -1 by decide,
      map_neg, map_one, neg_one_mul, sub_eq_add_neg]
  have hzero : π (deformedPolynomial 2 a 1 G) = 0 := by
    rw [hdef, pow_succ G 2, map_sub, map_mul, hproj, one_mul, sub_self]
  have hdeg : G.totalDegree ≤ 2 := by simp [G]
  have hchar : valuePolynomial (by decide : 1 ≤ 2) a 1 G hdeg = Polynomial.X ^ 2 := by
    have heq : π (deformedPolynomial 2 a 1 G) = π 0 := hzero.trans (map_zero π).symm
    rw [valuePolynomial, multiplicationMatrix_eq_of_projection_eq _ r _ heq,
      map_zero, Matrix.charpoly_zero]
    simp [NormalIndex]
  simpa only [F, G, a, map_X] using hchar

-- Swapping the two square roots of unity changes the potential at the separated centers.
example :
    let a (i : Fin 2) : ℂ := separatedCenters 2 i
    eval (fun i => a i * (if i = 0 then 1 else -1)) (potentialPolynomial 2 a) ≠
      eval (fun i => a i * (if i = 0 then -1 else 1)) (potentialPolynomial 2 a) := by
  intro a h
  have hz (i : Fin 2) : (if i = 0 then (1 : ℂ) else -1) ^ 2 = 1 := by
    split_ifs <;> norm_num
  have hw (i : Fin 2) : (if i = 0 then (-1 : ℂ) else 1) ^ 2 = 1 := by
    split_ifs <;> norm_num
  have he := eq_of_eval_potentialPolynomial_eq_of_pow_eq_one (by decide : 1 ≤ 2) hz hw h
  have h0 := congrFun he 0
  norm_num at h0

-- The initial characteristic polynomial in one variable has two simple roots.
example :
    let F : MvPolynomial (Fin 1) ℤ := X 0
    let hF : F.totalDegree ≤ 2 := by simp [F]
    let q := (parametricValuePolynomial (by decide : 1 ≤ 2) F hF).map
      (Polynomial.eval₂RingHom (Int.castRingHom ℂ) 0)
    q.Separable ∧ q.natDegree = 2 := by
  intro F hF q
  refine ⟨parametricValuePolynomial_at_zero_separable (by decide : 1 ≤ 2) F hF, ?_⟩
  simp only [q, parametricValuePolynomial_map_eval₂, valuePolynomial_natDegree, pow_one]

-- Choose an integer parameter for a nonconstant input and apply both specialization bounds.
example :
    let F : MvPolynomial (Fin 1) ℤ := X 0
    let hF : F.totalDegree ≤ 2 := by simp [F]
    let H := parametricValueCoeffNormExponent 1 2 0
    let a : ℤ := 2 ^ (H + 1)
    let s := criticalParameterExponent 1 2 0
    let q := valuePolynomial (by decide : 1 ≤ 2) (fun i => (separatedCenters 2 i : ℤ))
      (2 ^ s) F hF
    let q' := q.map (Int.castRingHom ℝ)
    q.coeffNorm1 ≤ 2 ^ (H + s * 12) ∧ q'.Separable ∧ q'.eval (a : ℝ) ≠ 0 := by
  intro F hF H a s q q'
  have hb : F.coeffNorm1 ≤ 2 ^ 0 := by simp [F, MvPolynomial.coeffNorm1_X]
  exact ⟨coeffNorm1_valuePolynomial_at_pow_two_le (by decide) F hF hb s,
    valuePolynomial_at_integerParameterExclusion (by decide) F hF hb⟩

-- A finite list of parameter coefficients recovers the linear characteristic coefficient.
example :
    let F : MvPolynomial (Fin 1) ℤ := X 0
    let hF : F.totalDegree ≤ 2 := by simp [F]
    let p := (parametricValuePolynomial (by decide : 1 ≤ 2) F hF).coeff 1
    Polynomial.ofCoeffList (p.coeffsBelow 7) = p := by
  intro F hF p
  apply Polynomial.ofCoeffList_coeffsBelow
  exact (natDegree_parametricValuePolynomial_coeff_le (by decide : 2 ≤ 2) F hF 1).trans_lt
    (by decide)

-- Feed a source-derived parameter residue to the evaluator for a nonconstant input.
example :
    let F : MvPolynomial (Fin 1) ℤ := X 0
    let hF : F.totalDegree ≤ 2 := by simp [F]
    let q := valuePolynomial (by decide : 1 ≤ 2) (fun i => (separatedCenters 2 i : ℤ))
      (2 ^ criticalParameterExponent 1 2 0) F hF
    criticalCoefficientValue 101 1 1 (criticalParameterResidue 101 1 2 0) 0
      (fun y => y[0]?.getD 0) = ((q.map (Int.castRingHom (ZMod 101))).coeff 0).val := by
  intro F hF q
  exact criticalCoefficientValue_at_criticalParameterResidue 1 (by decide) F hF
    (by decide) (by decide) _ (fun y => by simp [F])

-- The minima of a positive input vary continuously and monotonically, and are unbounded.
example :
    let F : MvPolynomial (Fin 1) ℝ := X 0 ^ 2 + 1
    let a : Fin 1 → ℝ := fun _ => 1
    ContinuousOn (criticalMinimumValue 3 a F) (Set.Ici 0) ∧
      MonotoneOn (criticalMinimumValue 3 a F) (Set.Ici 0) ∧
      ¬ ∃ B : ℝ, ∀ u : ℝ, 0 ≤ u → criticalMinimumValue 3 a F u ≤ B := by
  intro F a
  have ha (i : Fin 1) : 0 ≤ a i := by simp [a]
  have hF (x : Fin 1 → ℝ) : 0 ≤ eval x F := by
    simp only [F, map_add, map_pow, eval_X, map_one]
    positivity
  refine ⟨continuousOn_criticalMinimumValue (by decide) (by decide) a ha F hF,
    monotoneOn_criticalMinimumValue (by decide) (by decide) a ha F hF, ?_⟩
  intro hbounded
  have hcriterion := exists_zero_iff_bounded_criticalMinimumValue (ell := 3)
    (by decide) (by decide) a ha F hF
  obtain ⟨x, hx⟩ := hcriterion.mpr hbounded
  simp only [F, map_add, map_pow, eval_X, map_one] at hx
  nlinarith [sq_nonneg (x 0)]

-- The deformation of x² at zero center and parameter one has minimum zero.
example :
    let F : MvPolynomial (Fin 1) ℝ := X 0 ^ 2
    let hF : F.totalDegree ≤ 3 := by simp [F, totalDegree_X_pow]
    (valuePolynomial (by decide : 1 ≤ 3) 0 1 F hF).IsRoot 0 := by
  intro F hF
  have heval (x : Fin 1 → ℝ) :
      eval x (deformedPolynomial 3 0 1 F) = x 0 ^ 4 + 4 * x 0 ^ 2 := by
    norm_num [eval_deformedPolynomial, potentialPolynomial, F, Fin.sum_univ_one]
  have hmin : IsMinOn (fun x => eval x (deformedPolynomial 3 0 1 F)) Set.univ 0 := by
    intro x _
    change eval (0 : Fin 1 → ℝ) (deformedPolynomial 3 0 1 F) ≤
      eval x (deformedPolynomial 3 0 1 F)
    rw [heval, heval]
    norm_num
    positivity
  have hvalue : criticalMinimumValue 3 0 F 1 = 0 := by
    rw [criticalMinimumValue_eq_of_isMinOn 3 0 F 1 hmin, heval]
    norm_num
  have hFn (x : Fin 1 → ℝ) : 0 ≤ eval x F := by
    simp only [F, map_pow, eval_X]
    exact sq_nonneg _
  have hroot := isRoot_valuePolynomial_criticalMinimumValue (by decide : 1 ≤ 3)
    (by decide) 0 (fun _ => le_rfl) F hF hFn 1 zero_le_one
  rwa [hvalue] at hroot

-- For the branch y = u, the finite test compares u = 4 with the cutoff y = 2.
example : ¬ ∃ B : ℝ, ∀ u : ℝ, 0 ≤ u → u ≤ B := by
  let P : Polynomial (Polynomial ℤ) := Polynomial.X - Polynomial.C Polynomial.X
  have hlead : P.leadingCoeff = 1 := Polynomial.leadingCoeff_X_sub_C _
  have hP : P ≠ 0 := by
    intro hz
    simp [hz] at hlead
  have hroot (u : ℝ) :
      P.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℝ) u) u = 0 := by
    simp [P]
  have hR : (P.leadingCoeff.coeffNorm1 : ℝ) + 1 ≤ ((2 : ℤ) : ℝ) := by
    norm_num [hlead, Polynomial.coeffNorm1_one]
  have hX : (Polynomial.X : Polynomial ℤ).coeffNorm1 = 1 := by
    simpa using Polynomial.coeffNorm1_X_mul (1 : Polynomial ℤ)
  have hU : ((P.map (Polynomial.evalRingHom (2 : ℤ))).coeffNorm1 : ℝ) + 1 ≤ 4 := by
    have hbound := Polynomial.coeffNorm1_sub_le Polynomial.X (Polynomial.C (2 : ℤ))
    rw [hX, Polynomial.coeffNorm1_C] at hbound
    have hnorm : (P.map (Polynomial.evalRingHom (2 : ℤ))).coeffNorm1 ≤ 3 := by
      simpa [P] using hbound
    exact_mod_cast (Nat.add_le_add_right hnorm 1)
  have hcut := Polynomial.bounded_root_branch_iff_lt hP
    (monotone_id.monotoneOn _) continuous_id.continuousOn (fun u _ => hroot u) hR hU
  exact fun hb => (by norm_num : ¬ (4 : ℝ) < ((2 : ℤ) : ℝ)) (hcut.mp hb)

-- A square with a real zero gives both a root below the cutoff and a negative determinant.
example :
    let F : MvPolynomial (Fin 1) ℤ := X 0 ^ 2
    let H := parametricValueCoeffNormExponent 1 3 0
    let hF : F.totalDegree ≤ 3 := by simp [F, totalDegree_X_pow]
    let q := valuePolynomial (by decide : 1 ≤ 3) (fun i => (separatedCenters 3 i : ℤ))
      (2 ^ criticalParameterExponent 1 3 0) F hF
    (∃ η : ℝ, η < 2 ^ (H + 1) ∧ (q.map (Int.castRingHom ℝ)).IsRoot η) ∧
      ∃ L : List (Fin (3 ^ 1) × SignType), L.length ≤ 1 * (3 : ℕ).size ∧
        ∃ e : ℕ, e ≤ 3 ^ 1 ∧ criticalLabelDeterminant (by decide) 0 F hF L e < 0 := by
  intro F H hF q
  have hFn (x : Fin 1 → ℝ) : 0 ≤ eval x (F.map (Int.castRingHom ℝ)) := by
    simpa only [F, map_pow, map_X, eval_X] using sq_nonneg (x 0)
  have hb : F.coeffNorm1 ≤ 2 ^ 0 := by
    simpa only [F, MvPolynomial.coeffNorm1_X, one_pow, pow_zero] using
      MvPolynomial.coeffNorm1_pow_le (X (0 : Fin 1) : MvPolynomial (Fin 1) ℤ) 2
  have hz : ∃ x, eval x (F.map (Int.castRingHom ℝ)) = 0 := ⟨0, by simp [F]⟩
  exact ⟨(exists_zero_iff_exists_root_lt_at_integerParameterExclusion
    (by decide) (by decide) F hF hb hFn).mp hz,
    (exists_zero_iff_exists_neg_criticalLabelDeterminant
      (by decide) (by decide) F hF hb hFn).mp hz⟩

-- In the quotient by X₀ = 2, the simple real root of multiplication by X₀ is realized.
example : ∃ x : Fin 1 → ℝ, x 0 = 2 ∧ aeval x (X 0 : MvPolynomial (Fin 1) ℝ) = 2 := by
  let r : Fin 1 → MvPolynomial (Fin 1) ℝ := fun _ => C 2
  have hr (i : Fin 1) : (r i).totalDegree < 1 := by
    simp only [r, totalDegree_C, Nat.zero_lt_one]
  let M := multiplicationMatrix (by decide : 1 ≤ 1) r hr
  have hm : M (X 0) = algebraMap ℝ (Matrix (NormalIndex 1 1) (NormalIndex 1 1) ℝ) 2 := by
    rw [← M.commutes, MvPolynomial.algebraMap_eq]
    apply multiplicationMatrix_eq_of_projection_eq
    simpa only [pow_one, r] using projection_X_pow 1 r 0
  have hdim : Fintype.card (NormalIndex 1 1) = 1 := by simp [NormalIndex]
  have hsimple : (M (X 0)).charpoly.rootMultiplicity 2 = 1 := by
    rw [hm, Matrix.algebraMap_eq_diagonal, Matrix.charpoly_diagonal]
    simp only [Pi.algebraMap_apply, Algebra.algebraMap_self_apply, Finset.prod_const,
      Finset.card_univ, hdim, pow_one, Polynomial.rootMultiplicity_X_sub_C_self]
  obtain ⟨x, hx, hv⟩ :=
    exists_common_zero_of_rootMultiplicity_multiplicationMatrix_eq_one (by decide) r hr
      (X 0) hsimple
  have hx₀ : x 0 = 2 := by
    simpa only [r, aeval_C, Algebra.algebraMap_self_apply, pow_one] using (hx 0).symm
  exact ⟨x, hx₀, hv⟩

-- One derivative sign test suffices to select one of the two roots of x² − 1.
open scoped Classical in
example :
    let p : Polynomial ℝ := Polynomial.X ^ 2 - 1
    let S : Finset ℝ := {-1, 1}
    ∃ L : List (Fin 2 × SignType), L.length ≤ 1 ∧
      ∃ x ∈ S, ∀ y ∈ S, (∀ c ∈ L, p.derivativeSign y (c.1.val + 1) = c.2) ↔ y = x := by
  intro p S
  have hc : p.coeff 2 = 1 := by
    simp [p, Polynomial.coeff_X_pow, Polynomial.coeff_one]
  have hp : p ≠ 0 := fun h => by simp [h] at hc
  have hD : p.natDegree ≤ 2 := (Polynomial.natDegree_sub_le _ _).trans (by simp)
  have hS : S.Nonempty := ⟨-1, by simp [S]⟩
  have hroots (x : ℝ) (hx : x ∈ S) : p.IsRoot x := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> norm_num [p, Polynomial.IsRoot.def]
  exact p.exists_short_derivativeSign_selector hp hD (by decide) hS hroots

-- A nonmonic source with a double root at 1 gives a degree-two resultant with root 3.
example :
    let p : Polynomial ℤ := Polynomial.C 3 * (Polynomial.X - Polynomial.C 1) ^ 2
    let g : Polynomial ℤ := Polynomial.X + Polynomial.C 2
    p.valueResultant g ≠ 0 ∧ (p.valueResultant g).natDegree = 2 ∧
      ((p.valueResultant g).map (Int.castRingHom ℝ)).IsRoot 3 := by
  intro p g
  have hp : p ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr (by decide))
    (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _))
  have hdeg : p.natDegree = 2 := by
    simp only [p, Polynomial.natDegree_C_mul (by decide : (3 : ℤ) ≠ 0),
      Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
  have ha : (p.map (Int.castRingHom ℝ)).IsRoot 1 := by
    norm_num [p, Polynomial.IsRoot.def]
  obtain ⟨h₀, hd⟩ := Polynomial.valueResultant_ne_zero_and_natDegree hp g
  exact ⟨h₀, hd.trans hdeg, by
    simpa [g, show (1 : ℝ) + 2 = 3 by norm_num] using Polynomial.isRoot_valueResultant hp g ha⟩

-- The identity test at the root of 2X − 1 falls in the nonzero dyadic interval.
example :
    let R := (2 : ℝ) ^ Polynomial.algebraicValuePrecision 1 1 2 0
    R⁻¹ ≤ 1 / 2 ∧ 1 / 2 ≤ R := by
  intro R
  let p : Polynomial ℤ := Polynomial.C 2 * Polynomial.X - 1
  let g : Polynomial ℤ := Polynomial.X
  have hp₁ : p.coeff 1 = 2 := by
    norm_num only [p, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X,
      Polynomial.coeff_one, ite_true, ite_false]
  have hp : p ≠ 0 := fun h => by simp [h] at hp₁
  have hD : p.natDegree ≤ 1 := (Polynomial.natDegree_sub_le _ _).trans (by simp)
  have hE : g.natDegree ≤ 1 := by simp [g]
  have hg : g.coeffNorm1 = 1 := by
    simpa only [g, mul_one, Polynomial.coeffNorm1_one] using Polynomial.coeffNorm1_X_mul 1
  have hb : p.coeffNorm1 ≤ 2 ^ 2 := by
    change (Polynomial.C 2 * g - 1).coeffNorm1 ≤ 2 ^ 2
    refine (Polynomial.coeffNorm1_sub_le _ _).trans ?_
    have h := Polynomial.coeffNorm1_C_mul_le 2 g
    rw [hg] at h
    rw [Polynomial.coeffNorm1_one]
    omega
  have hx : p.eval₂ (Int.castRingHom ℝ) (1 / 2) = 0 := by norm_num [p]
  have h := Polynomial.eval₂_eq_zero_or_dyadic_bounds hp hD hE hb (c := 0) (by simp [hg]) hx
  rcases h with hzero | hbounds
  · norm_num [g] at hzero
  · simpa only [R, g, Polynomial.eval₂_X, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      using hbounds

-- A nonintegral input in the dyadic interval has the amplified reflection bound.
example :
    let p := Polynomial.dyadicSignProduct 1 1
    let x : ℝ := 3 / 4
    9 * p.eval₂ (Int.castRingHom ℝ) (-x) ≤ p.eval₂ (Int.castRingHom ℝ) x ∧
      1 ≤ p.eval₂ (Int.castRingHom ℝ) x + p.eval₂ (Int.castRingHom ℝ) (-x) := by
  intro p x
  refine ⟨?_, Polynomial.one_le_eval₂_dyadicSignProduct_add_neg 1 1 x⟩
  have h := Polynomial.eval₂_dyadicSignProduct_neg_le 1 1 (x := x)
    (by norm_num [x]) (by norm_num [x])
  simpa only [p, Nat.mul_one, show (3 : ℝ) ^ 2 = 9 by norm_num] using h

-- The normalized ratio is exact at zero and approximates the negative sign at −3/4.
example :
    Polynomial.dyadicSignApprox 1 1 0 = 0 ∧
      |Polynomial.dyadicSignApprox 1 1 (-(3 / 4)) + 1| ≤ (2 : ℝ) / 9 := by
  refine ⟨Polynomial.dyadicSignApprox_zero 1 1, ?_⟩
  have hx : (-(3 / 4) : ℝ) < 0 := by norm_num
  have h := Polynomial.abs_dyadicSignApprox_sub_sign_le 1 1 (x := -(3 / 4))
    (Or.inr ⟨by norm_num, by norm_num⟩)
  rw [sign_neg hx, SignType.coe_neg_one, sub_neg_eq_add] at h
  simpa only [Nat.mul_one, show (3 : ℝ) ^ 2 = 9 by norm_num, div_eq_mul_inv] using h

-- One approximate negative test accepts the negative target and rejects the positive target.
example :
    let a : Fin 1 → ℝ := fun _ => Polynomial.dyadicSignApprox 1 2 (-(3 / 4))
    (1 : ℝ) / 2 ≤ SignType.labelScore a (fun _ => -1) ∧
      SignType.labelScore a (fun _ => 1) ≤ -(1 : ℝ) / 2 := by
  intro a
  let s : Fin 1 → SignType := fun _ => -1
  have hx : (-(3 / 4) : ℝ) < 0 := by norm_num
  have ha (i : Fin 1) : |a i - (s i : ℝ)| ≤ (4 * (((1 : ℕ) : ℝ) + 1))⁻¹ := by
    have h := Polynomial.abs_dyadicSignApprox_sub_sign_le_inv_four_mul_succ 1 1
      (x := -(3 / 4)) (Or.inr ⟨by norm_num, by norm_num⟩)
    simpa only [sign_neg hx, a, s] using h
  obtain ⟨hmatch, hpos⟩ := SignType.labelScore_margin a s s ha
  obtain ⟨hmiss, hneg⟩ := SignType.labelScore_margin a s (fun _ => 1) ha
  have h₁ := hpos.mpr (fun _ => rfl)
  have h₂ : ¬ 0 < SignType.labelScore a (fun _ => 1) := by
    intro h
    have hsign := hneg.mp h (0 : Fin 1)
    norm_num [s] at hsign
  exact ⟨hmatch.resolve_right (by linarith), hmiss.resolve_left (by linarith)⟩

-- Clearing the denominators gives an integer polynomial that distinguishes the two targets.
example :
    let g : Fin 1 → Polynomial ℤ := fun _ => Polynomial.X
    let y (t : SignType) :=
      (Polynomial.signLabelPolynomial 1 g (fun _ => t)).eval₂ (Int.castRingHom ℝ) (-(3 / 4))
    (1 : ℝ) / 2 ≤ y (-1) ∧ y 1 ≤ -(1 : ℝ) / 2 := by
  intro g y
  let x : ℝ := -(3 / 4)
  have hx : x < 0 := by norm_num [x]
  have hb (i : Fin 1) :
      let v := (g i).eval₂ (Int.castRingHom ℝ) x
      v = 0 ∨ (((2 : ℝ) ^ 1)⁻¹ ≤ |v| ∧ |v| ≤ (2 : ℝ) ^ 1) := by
    norm_num [g, x]
  obtain ⟨hmatch, hpos⟩ := Polynomial.eval₂_signLabelPolynomial_margin 1 g (fun _ => -1) x hb
  obtain ⟨hmiss, hneg⟩ := Polynomial.eval₂_signLabelPolynomial_margin 1 g (fun _ => 1) x hb
  have h₁ : 0 < y (-1) := hpos.mpr fun i => by
    simp only [g, Polynomial.eval₂_X, sign_neg hx]
  have h₂ : ¬ 0 < y 1 := by
    intro h
    have hsign := hneg.mp h (0 : Fin 1)
    simp [g, sign_neg hx] at hsign
  exact ⟨hmatch.resolve_right (by linarith), hmiss.resolve_left (by linarith)⟩

-- Applying the sign product to X² − 1 gives explicit degree and coefficient budgets.
example :
    let g : Polynomial ℤ := Polynomial.X ^ 2 - 1
    let q := (Polynomial.dyadicSignProduct 1 1).comp g
    q.natDegree ≤ 12 ∧ q.coeffNorm1 ≤ 2 ^ 24 := by
  intro g q
  have hD : g.natDegree ≤ 2 := (Polynomial.natDegree_sub_le _ _).trans (by simp)
  have hx : (Polynomial.X : Polynomial ℤ).coeffNorm1 = 1 := by
    simpa only [mul_one, Polynomial.coeffNorm1_one] using Polynomial.coeffNorm1_X_mul 1
  have hg : g.coeffNorm1 ≤ 2 ^ 1 := by
    refine (Polynomial.coeffNorm1_sub_le _ _).trans ?_
    have h := Polynomial.coeffNorm1_pow_le (Polynomial.X : Polynomial ℤ) 2
    rw [hx, one_pow] at h
    rw [Polynomial.coeffNorm1_one]
    omega
  exact Polynomial.dyadicSignProduct_comp_bounds 1 1 g hD hg

-- The integer label of a single identity test has explicit size bounds.
example :
    let g : Fin 1 → Polynomial ℤ := fun _ => Polynomial.X
    let p := Polynomial.signLabelPolynomial 1 g (fun _ => 1)
    p.natDegree ≤ 48 ∧ p.coeffNorm1 ≤ 2 ^ 156 := by
  intro g p
  have hb (i : Fin 1) : (g i).coeffNorm1 ≤ 2 ^ 0 := by
    simpa only [g, mul_one, Polynomial.coeffNorm1_one, pow_zero] using
      (Polynomial.coeffNorm1_X_mul 1).le
  have hDegree : Polynomial.signLabelDegreeBound 1 1 1 = 48 := by decide
  have hNorm : Polynomial.signLabelNormExponent 1 1 0 = 156 := by decide
  simpa only [hDegree, hNorm] using
    Polynomial.signLabelPolynomial_bounds 1 g (fun _ => 1)
      (D := 1) (fun _ => Polynomial.natDegree_X_le) hb

-- One precision covers all derivative orders at the real root of 2X.
example (k : ℕ) :
    let p : Polynomial ℤ := Polynomial.C 2 * Polynomial.X
    let v := (Polynomial.derivative^[k] p).eval₂ (Int.castRingHom ℝ) 0
    let R := (2 : ℝ) ^ Polynomial.algebraicValuePrecision 1 1 1 2
    v = 0 ∨ (R⁻¹ ≤ |v| ∧ |v| ≤ R) := by
  intro p v R
  have hp : p ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr (by decide)) Polynomial.X_ne_zero
  have hD : p.natDegree ≤ 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
  have hb : p.coeffNorm1 ≤ 2 ^ 1 := by
    have h := Polynomial.coeffNorm1_X_mul (Polynomial.C (2 : ℤ))
    rw [mul_comm, Polynomial.coeffNorm1_C] at h
    exact h.le
  have hk := Polynomial.coeffNorm1_iterate_derivative_le_two_pow p hD hb k
  have hbudget : Polynomial.iterateDerivativeNormExponent 1 1 = 2 := by decide
  rw [hbudget] at hk
  exact Polynomial.eval₂_eq_zero_or_dyadic_bounds hp hD
    ((Polynomial.natDegree_iterate_derivative p k).trans ((Nat.sub_le _ _).trans hD)) hb hk
    (by simp [p])

-- With both roots eligible, one derivative test labels just one root of X² − 1.
example :
    let p : Polynomial ℤ := Polynomial.X ^ 2 - 1
    ∃ L : List (Fin 2 × SignType), L.length ≤ 1 ∧ ∃ x : ℝ, x ^ 2 = 1 ∧
      let label := Polynomial.sparseIntegerRootLabel p 1 1 1 L
      0 < label.eval₂ (Int.castRingHom ℝ) x ∧ label.eval₂ (Int.castRingHom ℝ) (-x) < 0 := by
  intro p
  have hp : p ≠ 0 := by
    intro h
    have he := congrArg (fun f : Polynomial ℤ => f.eval 0) h
    simp [p] at he
  have hD : p.natDegree ≤ 2 := (Polynomial.natDegree_sub_le _ _).trans (by simp)
  have hxnorm : (Polynomial.X ^ 2 : Polynomial ℤ).coeffNorm1 ≤ 1 := by
    simpa only [one_mul, Polynomial.coeffNorm1_one] using
      Polynomial.coeffNorm1_mul_X_pow_le (1 : Polynomial ℤ) 2
  have hnorm : p.coeffNorm1 ≤ 2 ^ 1 := (Polynomial.coeffNorm1_sub_le _ _).trans
    (by simpa only [Polynomial.coeffNorm1_one, pow_one, Nat.reduceAdd] using
      Nat.add_le_add_right hxnorm 1)
  obtain ⟨L, hL, x, hx, _, hpos, hneg⟩ := Polynomial.exists_sparseIntegerRootLabel
    (q := 1) hp hD (by decide : 2 ≤ 2 ^ 1) (by simp) hnorm (by simp)
    ⟨1, by simp [p], by simp⟩
  have hx₂ : x ^ 2 = 1 := by simpa [p, sub_eq_zero] using hx
  have hne : -x ≠ x := by
    intro h
    have hx₀ : x = 0 := by linarith
    simp [hx₀] at hx₂
  exact ⟨L, hL, x, hx₂, hpos, hneg (-x) (by simp [p, hx₂]) hne⟩

-- The conjugate pair contributes one, leaving the negative real factor.
open scoped ComplexConjugate in
example :
    let S : Finset ℂ := {Complex.I, -Complex.I, -1}
    (∏ z ∈ S, z) = -1 := by
  classical
  intro S
  have hS : ∀ z ∈ S, conj z ∈ S := by
    intro z hz
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> simp [S]
  calc
    _ = (((∏ z ∈ S.filter (fun z => z.im = 0), z.re) *
        ∏ z ∈ S.filter (fun z => 0 < z.im), Complex.normSq z : ℝ) : ℂ) :=
      Complex.prod_eq_ofReal_mul_prod_normSq S id hS (fun _ _ => rfl)
    _ = -1 := by
      norm_num [S, Finset.filter_insert, Finset.filter_singleton, Complex.normSq_I]

-- A double real root contributes once to the product over distinct roots.
example :
    let p : Polynomial ℝ := (Polynomial.X - Polynomial.C (-1)) ^ 2
    (∏ z ∈ (p.aroots ℂ).toFinset, Polynomial.aeval z (Polynomial.X : Polynomial ℝ)) = -1 := by
  classical
  intro p
  have hp : p ≠ 0 := pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
  have hreal : p.roots.toFinset = {-1} := by
    ext x
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot.def]
    simp [p, add_eq_zero_iff_eq_neg]
  have hcomplex : (p.aroots ℂ).toFinset = {-1} := by
    ext z
    rw [Multiset.mem_toFinset, Polynomial.mem_aroots, and_iff_right hp]
    simp [p, add_eq_zero_iff_eq_neg]
  rw [Polynomial.prod_aeval_aroots_toFinset_eq, hreal, hcomplex]
  norm_num [Finset.filter_singleton]

-- The integer label X vanishes at the source root, so a nonzero shift is needed.
example : ∃ e : ℕ, e ≤ 1 ∧
    Polynomial.aeval (0 : ℂ) (Polynomial.shiftedRootLabel 1 e (Polynomial.X : Polynomial ℤ)) ≠
      0 := by
  obtain ⟨e, he, h⟩ := Polynomial.exists_aeval_shiftedRootLabel_ne_zero (A := ℂ)
    (Polynomial.X : Polynomial ℤ) Polynomial.X Polynomial.natDegree_X_le
  exact ⟨e, he, h 0 (by simp [Polynomial.aroots_X])⟩

-- Every allowed shift reverses the positive sign of the constant label one.
example (e : ℕ) (he : e ≤ 1) :
    SignType.sign ((Polynomial.shiftedRootLabel 1 e (1 : Polynomial ℝ)).eval 0) = -1 := by
  simpa only [Polynomial.eval_one, sign_pos (by norm_num : (0 : ℝ) < 1)] using
    Polynomial.sign_eval_shiftedRootLabel (g := 1) (x := 0) (by decide : 0 < (1 : ℕ)) he
      (Or.inl (by norm_num))

-- The only root of X needs no derivative tests, and a constant test decides qualification.
example (a : ℤ) (ha : a.natAbs ≤ 1) :
    let p : Polynomial ℤ := Polynomial.X
    let q := Polynomial.C a
    (∃ e : ℕ, e ≤ 1 ∧
      (∏ z ∈ (p.aroots ℂ).toFinset,
        Polynomial.aeval z (Polynomial.shiftedRootLabel 1 e
          (Polynomial.sparseIntegerRootLabel p q 0 0 ([] : List (Fin 1 × SignType))))).re < 0) ↔
      0 < a := by
  intro p q
  have hp : p.coeffNorm1 ≤ 2 ^ 0 := by
    simpa only [p, mul_one, Polynomial.coeffNorm1_one, pow_zero] using
      (Polynomial.coeffNorm1_X_mul 1).le
  have hq : q.coeffNorm1 ≤ 2 ^ 0 := by
    simpa only [q, Polynomial.coeffNorm1_C, pow_zero] using ha
  have h := Polynomial.exists_eval₂_pos_at_root_iff_neg_shiftedRootLabel_prod
    (D := 1) (N := 0) Polynomial.X_ne_zero (by decide) Polynomial.natDegree_X_le
    (by decide) (by simp [q]) hp hq
  constructor
  · rintro ⟨e, he, hneg⟩
    obtain ⟨x, _, hx⟩ := h.mpr ⟨[], Nat.zero_le _, e, he, hneg⟩
    have hx' : (0 : ℝ) < (a : ℝ) := by
      simpa only [q, Polynomial.eval₂_C, Int.coe_castRingHom] using hx
    exact_mod_cast hx'
  · intro ha₀
    have ha₀' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha₀
    obtain ⟨L, hL, e, he, hneg⟩ := h.mp
      ⟨0, by simp, by simpa only [q, Polynomial.eval₂_C, Int.coe_castRingHom] using ha₀'⟩
    have hnil := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hL)
    exact ⟨e, he, hnil ▸ hneg⟩

-- Evaluating X − 1 at the matrix with eigenvalues 2 and 3 gives determinant 1 · 2.
example :
    let M : Matrix (Fin 2) (Fin 2) ℚ := Matrix.diagonal ![2, 3]
    (Polynomial.aeval M ((Polynomial.X : Polynomial ℚ) - Polynomial.C 1)).det = 2 := by
  intro M
  have hM : M.charpoly = (Polynomial.X - Polynomial.C 2) * (Polynomial.X - Polynomial.C 3) := by
    simp [M, Matrix.charpoly_diagonal, Fin.prod_univ_two]
  have hs : M.charpoly.Splits := by
    rw [hM]
    exact (Polynomial.Splits.X_sub_C _).mul (Polynomial.Splits.X_sub_C _)
  rw [Matrix.det_aeval_eq_prod_charpoly_roots M _ (Polynomial.Splits.X_sub_C 1) hs, hM,
    Polynomial.roots_mul
      (mul_ne_zero (Polynomial.X_sub_C_ne_zero _) (Polynomial.X_sub_C_ne_zero _)),
    Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C, Multiset.map_add, Multiset.prod_add]
  norm_num

-- The determinant in the zero-variable quotient comes from its one characteristic root.
example :
    let r : Fin 0 → MvPolynomial (Fin 0) ℤ := 0
    let μ := multiplicationMatrix (ell := 1) (by decide) r (fun i => i.elim0)
    let g : Polynomial ℤ := Polynomial.X - Polynomial.C 1
    (μ (Polynomial.aeval (MvPolynomial.C (2 : ℤ)) g)).det = 1 := by
  intro r μ g
  let M := μ (MvPolynomial.C (2 : ℤ))
  have hM : M = Matrix.diagonal (fun _ => (2 : ℤ)) := by
    change μ (MvPolynomial.C (2 : ℤ)) = _
    rw [← MvPolynomial.algebraMap_eq, μ.commutes, Matrix.algebraMap_eq_diagonal]
    rfl
  have hchar : M.charpoly = Polynomial.X - Polynomial.C 2 := by
    rw [hM, Matrix.charpoly_diagonal, Fintype.prod_unique]
  have hcharMap : M.charpoly.map (algebraMap ℤ ℚ) = Polynomial.X - Polynomial.C 2 := by
    rw [hchar, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_ofNat]
  have hg : (g.map (algebraMap ℤ ℚ)).Splits := by
    simpa [g] using Polynomial.Splits.X_sub_C (1 : ℚ)
  have h := Matrix.algebraMap_det_aeval_eq_prod_aroots_toFinset (K := ℚ) M g hg
    (hcharMap ▸ Polynomial.Splits.X_sub_C (2 : ℚ))
    (hcharMap ▸ Polynomial.separable_X_sub_C (x := (2 : ℚ)))
  rw [hchar, Polynomial.aroots_X_sub_C] at h
  have hval : Polynomial.aeval (algebraMap ℤ ℚ 2) g = 1 := by
    norm_num [g, Polynomial.aeval_def, algebraMap_int_eq]
  rw [Multiset.toFinset_singleton, Finset.prod_singleton, hval] at h
  have hcast : ((Polynomial.aeval M g).det : ℚ) = 1 := by
    simpa only [algebraMap_int_eq, Int.coe_castRingHom] using h
  have hsrc : (Polynomial.aeval M g).det = 1 := by exact_mod_cast hcast
  simpa only [M, Polynomial.aeval_algHom_apply] using hsrc

-- The actual rank-one quotient determinant detects the root of its characteristic polynomial.
example :
    let r : Fin 0 → MvPolynomial (Fin 0) ℤ := 0
    let μ := multiplicationMatrix (ell := 1) (by decide) r (fun i => i.elim0)
    let p := (μ 0).charpoly
    ∃ e : ℕ, e ≤ 1 ∧
      (μ (Polynomial.aeval (0 : MvPolynomial (Fin 0) ℤ) (Polynomial.shiftedRootLabel 1 e
        (Polynomial.sparseIntegerRootLabel p 1 0 0 ([] : List (Fin 1 × SignType)))))).det < 0 := by
  intro r μ p
  let M := μ 0
  have hcard : Fintype.card (NormalIndex 0 1) = 1 := Fintype.card_unique
  have hchar : M.charpoly = Polynomial.X := by
    simp only [M, map_zero, Matrix.charpoly_zero, hcard, pow_one]
  have hMb : M.charpoly.coeffNorm1 ≤ 2 ^ 0 := by
    simpa only [hchar, mul_one, Polynomial.coeffNorm1_one, pow_zero] using
      (Polynomial.coeffNorm1_X_mul 1).le
  have hsep : (M.charpoly.map (algebraMap ℤ ℂ)).Separable := by
    rw [hchar, Polynomial.map_X]
    exact Polynomial.separable_X
  have h := Matrix.exists_eval₂_pos_at_charpoly_root_iff_neg_shiftedRootLabel_det M
    (q := 1) (N := 0) (by decide) hcard.le (by decide) (by simp) hMb (by simp) hsep
  obtain ⟨L, hL, e, he, hneg⟩ := h.mp ⟨0, by simp [hchar], by simp⟩
  have hnil := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hL)
  subst L
  exact ⟨e, he, by simpa only [p, M, Polynomial.aeval_algHom_apply] using hneg⟩

end CslibFrontierTests.RealAlgebraicCriticalCoefficients
