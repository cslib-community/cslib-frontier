/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/
module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalCoefficientEvaluation
import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalParameterEvaluation
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.BranchCutoff
import CslibFrontier.Foundations.Analysis.MvPolynomial.CriticalMinimumValue
import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CriticalValuePolynomial
import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CriticalIntegerSpecialization
import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CriticalValueParameterDegree
import CslibFrontier.Foundations.Data.Polynomial.CoeffList
import CslibFrontier.Foundations.Data.MvPolynomial.Degrees
import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.InitialCriticalSeparability
import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.ResidueCoeffNorm
import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.SeparatedCriticalValues
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

end CslibFrontierTests.RealAlgebraicCriticalCoefficients
