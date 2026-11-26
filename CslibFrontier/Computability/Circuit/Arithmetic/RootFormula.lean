/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.FormulaInterpolation
public import CslibFrontier.Foundations.Data.MvPolynomial.LowDegreeRoot
import CslibFrontier.Foundations.Data.MvPolynomial.LastVariable

/-!
# Roots of formulas of constant product-depth

Let `F` be a formula `Cslib.Circuits.Arithmetic.SPFormula` of sum and product gates of unbounded
fan-in, in the variables `x` and a last variable `y`, computing a nonzero polynomial `P (x, y)` in
characteristic zero, and let `f (x)` be a polynomial with `P (x, f) = 0`. Then `f` has a formula of
product-depth one more than that of `F` and of size polynomial in the size of `F` and the degree
of `f` [BhattacharjeeEtAl2025, Theorem 4.1].

The formula implements the closed formula `MvPolynomial.exists_shift_eq_truncate_sum_of_root`:
for some `j` and some point `x₀`, with `Q` the `j`-th `y`-derivative of `P` shifted by `x₀` in
`x` and by `f (x₀)` in `y`, and `c ≠ 0` the constant term of the coefficient of `y` in `Q`,

`f (x + x₀) = f (x₀) + (∑ m ∈ {1, …, 2 D + 2}, (1 / m) [y ^ (m - 1)] (y - Q / c) ^ m)_{≤ D}`

for `D` the degree of `f`. Every operation in it keeps the product-depth except the powers,
which are one layer of product gates:

* the `j`-th derivative in `y` is `j!` times the coefficient of `t ^ j` of `P (x, y + t)`, an
  interpolation in a new variable `t` (`SPFormula.coeffLast`);
* the shifts are substitutions of affine forms for the inputs (`SPFormula.affineInput`);
* the coefficients in `y` and the truncation to degree at most `D` are interpolations
  (`SPFormula.coeffLast`, `SPFormula.lowPartFormula`) [ChouKumarSolomon2019, Lemma 4.11].

The explicit size bound `SPFormula.rootCost` is original and not optimized.

## Main definitions

* `Cslib.Circuits.Arithmetic.SPFormula.rootCost`: the size bound.

## Main results

* `Cslib.Circuits.Arithmetic.SPFormula.exists_formula_of_root`: a root of a formula of
  product-depth `Δ` has a formula of product-depth `Δ + 1` and of at most
  `rootCost F.nodeCount f.totalDegree` nodes.

## References

* [S. Bhattacharjee, M. Kumar, S. Rai, V. Ramanathan, R. Saptharishi, S. Saraf, *Closure under
  factorization from a result of Furstenberg*][BhattacharjeeEtAl2025], Theorem 4.1 (unrefereed
  preprint)
* [C.-N. Chou, M. Kumar, N. Solomon, *Closure Results for Polynomial
  Factorization*][ChouKumarSolomon2019], Lemma 4.11 (Interpolation for Formulas), in the
  numbering of arXiv:1803.05933v1, §4.6
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic.SPFormula

open Finset MvPolynomial

/-- The size bound of `SPFormula.exists_formula_of_root` for a root of degree `D` of a formula of
`s` nodes. -/
def rootCost (s D : ℕ) : ℕ :=
  2 ^ 36 * (s + 1) ^ 8 * (D + 1) ^ 6

variable {K : Type*} [Field K] {n : ℕ}

/-! ### Polynomials in the last variable -/

/-- `coeffLast i F.nodeCount F` computes the coefficient of `y ^ i` of the polynomial of `F`. -/
private theorem polynomial_coeffLast_nodeCount [CharZero K] (i : ℕ) (F : SPFormula K (n + 1)) :
    (coeffLast i F.nodeCount F).polynomial = (lastVariableEquiv K n F.polynomial).coeff i :=
  polynomial_coeffLast (fun α => (eval_lastVariableEquiv (C α) F.polynomial).symm)
    (by rw [natDegree_lastVariableEquiv]
        exact (degreeOf_le_totalDegree _ _).trans (totalDegree_polynomial_le_nodeCount F)) i

/-- The homogeneous components of degree at most `D` sum to the truncation to degree `D`. -/
private theorem sum_homogeneousComponent_eq_truncateTotalDegree {σ : Type*} (D : ℕ)
    (p : MvPolynomial σ K) :
    ∑ k ∈ range (D + 1), homogeneousComponent k p = truncateTotalDegree D p := by
  ext d
  simp [coeff_homogeneousComponent, coeff_truncateTotalDegree]

/-! ### Shifts -/

/-- Substituting `x_i + a i` for every input `x_i` computes the shift by `a`. -/
private theorem polynomial_substFormula_shift (a : Fin n → K) (F : SPFormula K n) :
    (substFormula (affineInput id (fun _ => 1) a) F).polynomial = shift a F.polynomial := by
  simp only [polynomial_substFormula, polynomial_affineInput, id, C_1, one_mul]
  rfl

/-- Shifting `x` by `x₀` and `y` by `α` shifts the coefficients by `x₀` and the variable by
`α`. -/
private theorem lastVariableEquiv_shift (x₀ : Fin n → K) (α : K)
    (p : MvPolynomial (Fin (n + 1)) K) :
    lastVariableEquiv K n (shift (Fin.lastCases α x₀) p) =
      Polynomial.taylor (C α) ((lastVariableEquiv K n p).map (shift x₀ : _ →ₐ[K] _).toRingHom) := by
  have h : (lastVariableEquiv K n).toRingHom.comp
      (shift (Fin.lastCases α x₀) : _ →ₐ[K] MvPolynomial (Fin (n + 1)) K).toRingHom =
      (Polynomial.taylorAlgHom (C α)).toRingHom.comp ((Polynomial.mapRingHom
        (shift x₀ : _ →ₐ[K] MvPolynomial (Fin n) K).toRingHom).comp
        (lastVariableEquiv K n).toRingHom) :=
    ringHom_ext (fun a => by simp) fun i => by
      refine Fin.lastCases ?_ (fun k => ?_) i <;>
        simp [lastVariableEquiv_X_last, lastVariableEquiv_X_castSucc, shift_X]
  exact RingHom.congr_fun h p

/-! ### Derivatives in the last variable -/

/-- The input `y + t` for the last input `y`, with `t` a new last input, and the input `x_k` for
every other input `x_k`. -/
private def addLastInput : Fin (n + 1) → SPFormula K (n + 2) :=
  Fin.lastCases (add ![1, 1] ![.input (Fin.last n).castSucc, .input (Fin.last (n + 1))])
    fun k => .input k.castSucc.castSucc

/-- `j!` times the coefficient of `t ^ j` of `F (x, y + t)`: the `j`-th derivative of `F` in its
last variable `y`. -/
private noncomputable def derivLast (j : ℕ) (F : SPFormula K (n + 1)) : SPFormula K (n + 1) :=
  add ![(j.factorial : K)]
    ![coeffLast j (substFormula addLastInput F).nodeCount (substFormula addLastInput F)]

private theorem lastVariableEquiv_derivLast [CharZero K] (j : ℕ) (F : SPFormula K (n + 1)) :
    lastVariableEquiv K n (derivLast j F).polynomial =
      Polynomial.derivative^[j] (lastVariableEquiv K n F.polynomial) := by
  have h : (Polynomial.mapRingHom (lastVariableEquiv K n).toRingHom).comp
      ((lastVariableEquiv K (n + 1)).toRingHom.comp
        (aeval fun i => (addLastInput i).polynomial :
          MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin (n + 2)) K).toRingHom) =
      (Polynomial.taylorAlgHom (Polynomial.X : Polynomial (MvPolynomial (Fin n) K))).toRingHom.comp
        ((Polynomial.mapRingHom Polynomial.C).comp (lastVariableEquiv K n).toRingHom) :=
    ringHom_ext (fun a => by simp) fun i => by
      refine Fin.lastCases ?_ (fun k => ?_) i
      · simp [addLastInput, lastVariableEquiv_X_last, lastVariableEquiv_X_castSucc,
          Fin.sum_univ_two, add_comm]
      · simp [addLastInput, lastVariableEquiv_X_castSucc]
  have hj := congrArg (fun q => q.coeff j) (RingHom.congr_fun h F.polynomial)
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe,
    Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.taylorAlgHom_apply,
    Polynomial.taylor_coeff, Polynomial.hasseDeriv_map, Polynomial.eval_map,
    Polynomial.eval₂_C_X] at hj
  change lastVariableEquiv K n
      ((lastVariableEquiv K (n + 1)
        (aeval (fun i => (addLastInput i).polynomial) F.polynomial)).coeff j) =
    (Polynomial.hasseDeriv j) (lastVariableEquiv K n F.polynomial) at hj
  rw [derivLast, polynomial_add, Fin.sum_univ_one, Matrix.cons_val_zero, Matrix.cons_val_zero,
    polynomial_coeffLast_nodeCount, polynomial_substFormula, map_mul, lastVariableEquiv_C, hj,
    ← Polynomial.factorial_smul_hasseDeriv, LinearMap.smul_apply, nsmul_eq_mul, map_natCast,
    map_natCast]

private theorem productDepth_derivLast_le (j : ℕ) (F : SPFormula K (n + 1)) :
    (derivLast j F).productDepth ≤ F.productDepth := by
  rw [derivLast, productDepth_add]
  refine Finset.sup_le fun i _ => ?_
  fin_cases i
  refine (productDepth_coeffLast_le _ _ _).trans <|
    (productDepth_substFormula_le (B := 0) (fun k => ?_) F).trans_eq (add_zero _)
  refine Fin.lastCases ?_ (fun k => by simp [addLastInput]) k
  rw [addLastInput, Fin.lastCases_last, productDepth_add]
  exact Finset.sup_le fun i _ => by fin_cases i <;> simp

private theorem nodeCount_derivLast_le (j : ℕ) (F : SPFormula K (n + 1)) :
    (derivLast j F).nodeCount ≤ (3 * F.nodeCount + 1) * (3 * F.nodeCount) + 2 := by
  have hH : (substFormula addLastInput F).nodeCount ≤ 3 * F.nodeCount :=
    (nodeCount_substFormula_le (S := 3)
      (Fin.lastCases (by simp [addLastInput, Fin.sum_univ_two]) fun _ => by simp [addLastInput])
      (by norm_num) F).trans_eq (mul_comm _ _)
  rw [derivLast, Formula.nodeCount_gate, Fin.sum_univ_one, Matrix.cons_val_zero]
  have := nodeCount_coeffLast_le j (substFormula addLastInput F).nodeCount
    (substFormula addLastInput F)
  nlinarith

/-! ### Roots -/

private theorem succ_mul_add_one_le {x : ℕ} (hx : 1 ≤ x) : (x + 1) * x + 1 ≤ 3 * x ^ 2 := by
  nlinarith

private theorem succ_mul_three_mul_add_le {x : ℕ} (hx : 1 ≤ x) :
    ((x + 1) * (3 * x) + 1 + 2) * 3 ≤ 27 * x ^ 2 := by
  nlinarith

/-- **Roots of formulas of constant product-depth** [BhattacharjeeEtAl2025, Theorem 4.1]. In
characteristic zero, if the polynomial `P (x, y)` of a formula `F` of product-depth at most `Δ`,
with `y` its last variable, is not zero and `P (x, f) = 0`, then `f` has a formula of
product-depth at most `Δ + 1` and of at most `rootCost F.nodeCount f.totalDegree` nodes. -/
theorem exists_formula_of_root [CharZero K] {N Δ : ℕ} {F : SPFormula K (N + 1)}
    (hΔ : F.productDepth ≤ Δ) (hF : F.polynomial ≠ 0) {f : MvPolynomial (Fin N) K}
    (hroot : aeval (Fin.lastCases f X : Fin (N + 1) → MvPolynomial (Fin N) K) F.polynomial = 0) :
    ∃ G : SPFormula K N, G.polynomial = f ∧ G.productDepth ≤ Δ + 1 ∧
      G.nodeCount ≤ rootCost F.nodeCount f.totalDegree := by
  classical
  set D := f.totalDegree
  have hP : lastVariableEquiv K N F.polynomial ≠ 0 := fun h =>
    hF ((lastVariableEquiv K N).injective (h.trans (map_zero _).symm))
  have hPf : (lastVariableEquiv K N F.polynomial).eval f = 0 := by rwa [eval_lastVariableEquiv]
  obtain ⟨j, x₀, -, hshift⟩ := exists_shift_eq_truncate_sum_of_root hP hPf
  set α := eval x₀ f
  set Q := Polynomial.taylor (C α)
    ((Polynomial.derivative^[j] (lastVariableEquiv K N F.polynomial)).map
      (shift x₀ : _ →ₐ[K] _).toRingHom)
  set c := constantCoeff (Q.coeff 1)
  -- The shifted derivative `Q`, of product-depth at most `Δ`.
  set QF := substFormula (affineInput id (fun _ => 1) (Fin.lastCases α x₀)) (derivLast j F)
    with hQF
  have hQFp : lastVariableEquiv K N QF.polynomial = Q := by
    rw [hQF, polynomial_substFormula_shift, lastVariableEquiv_shift, lastVariableEquiv_derivLast]
  -- `y - Q / c`.
  set G₀ : SPFormula K (N + 1) := add ![1, -c⁻¹] ![.input (Fin.last N), QF] with hG₀
  have hG₀p : lastVariableEquiv K N G₀.polynomial = Polynomial.X - Polynomial.C (C c⁻¹) * Q := by
    simp [hG₀, Fin.sum_univ_two, lastVariableEquiv_X_last, hQFp]
    ring
  -- Its powers, the only product gates added.
  set Pm : ℕ → SPFormula K (N + 1) := fun m => prodOn (range (m + 1)) fun _ => G₀ with hPm
  set S : SPFormula K N := sumOn (range (2 * (D + 1))) (fun m => ((m : K) + 1)⁻¹) fun m =>
    coeffLast m (Pm m).nodeCount (Pm m) with hS
  set L := lowPartFormula D S.nodeCount S with hL
  set T : SPFormula K N := add ![1, 1] ![L, const α] with hT
  refine ⟨substFormula (affineInput id (fun _ => 1) fun i => -x₀ i) T, ?_, ?_, ?_⟩
  · have hSp : S.polynomial = ∑ m ∈ range (2 * (D + 1)), ((m : K) + 1)⁻¹ •
        ((Polynomial.X - Polynomial.C (C c⁻¹) * Q) ^ (m + 1)).coeff m := by
      rw [hS, polynomial_sumOn]
      refine sum_congr rfl fun m _ => ?_
      rw [polynomial_coeffLast_nodeCount, hPm, polynomial_prodOn, map_prod, prod_const,
        card_range, hG₀p, smul_eq_C_mul]
    have hTp : T.polynomial = shift x₀ f := by
      rw [hshift D le_rfl, hT, polynomial_add, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, C_1, one_mul, polynomial_const]
      rw [hL, polynomial_lowPartFormula (totalDegree_polynomial_le_nodeCount S),
        sum_homogeneousComponent_eq_truncateTotalDegree, hSp]
      exact add_comm _ _
    rw [polynomial_substFormula_shift, hTp, shift_neg_shift]
  · have hQFd : QF.productDepth ≤ Δ := (productDepth_substFormula_le (B := 0)
        (fun k => (productDepth_affineInput _ _ _ k).le) _).trans
        ((add_zero _).trans_le ((productDepth_derivLast_le j F).trans hΔ))
    have hG₀d : G₀.productDepth ≤ Δ := by
      simp [hG₀, productDepth_add, Fin.forall_fin_two, hQFd]
    have hSd : S.productDepth ≤ Δ + 1 := productDepth_sumOn_le _ fun m _ =>
      (productDepth_coeffLast_le _ _ _).trans (productDepth_prodOn_le fun _ _ => hG₀d)
    have hLd : L.productDepth ≤ Δ + 1 := (productDepth_lowPartFormula_le _ _ _).trans hSd
    have hTd : T.productDepth ≤ Δ + 1 := by
      simp [hT, productDepth_add, Fin.forall_fin_two, hLd]
    exact ((productDepth_substFormula_le (B := 0)
      (fun k => (productDepth_affineInput _ _ _ k).le) _).trans_eq (add_zero _)).trans hTd
  · set s := F.nodeCount with hs
    have hpos : 0 < (D + 1) * (s + 1) ^ 2 := by positivity
    have hDer : _ ≤ (3 * s + 1) * (3 * s) + 2 := nodeCount_derivLast_le j F
    have hQFn : QF.nodeCount ≤ (derivLast j F).nodeCount * 3 :=
      nodeCount_substFormula_le (fun k => (nodeCount_affineInput _ _ _ k).le) (by norm_num) _
    have hG₀b : G₀.nodeCount ≤ 44 * (s + 1) ^ 2 := by
      simp only [hG₀, Formula.nodeCount_gate, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Formula.nodeCount_input]
      nlinarith
    have hcL : ∀ m ∈ range (2 * (D + 1)), (coeffLast m (Pm m).nodeCount (Pm m)).nodeCount ≤
        3 * (89 * ((D + 1) * (s + 1) ^ 2)) ^ 2 := by
      intro m hm
      have hm' : m + 1 ≤ 2 * (D + 1) := mem_range.1 hm
      have hP : (Pm m).nodeCount ≤ 89 * ((D + 1) * (s + 1) ^ 2) := by
        rw [hPm, nodeCount_prodOn, sum_const, card_range, smul_eq_mul]
        calc (m + 1) * G₀.nodeCount + 1 ≤ 2 * (D + 1) * (44 * (s + 1) ^ 2) + 1 := by gcongr
          _ ≤ 89 * ((D + 1) * (s + 1) ^ 2) := by nlinarith
      calc (coeffLast m (Pm m).nodeCount (Pm m)).nodeCount
          ≤ ((Pm m).nodeCount + 1) * (Pm m).nodeCount + 1 := nodeCount_coeffLast_le _ _ _
        _ ≤ (89 * ((D + 1) * (s + 1) ^ 2) + 1) * (89 * ((D + 1) * (s + 1) ^ 2)) + 1 := by
          gcongr
        _ ≤ 3 * (89 * ((D + 1) * (s + 1) ^ 2)) ^ 2 := succ_mul_add_one_le (by omega)
    have hSb : S.nodeCount ≤ 47527 * ((D + 1) ^ 3 * (s + 1) ^ 4) := by
      have hpos' : 0 < (D + 1) ^ 3 * (s + 1) ^ 4 := by positivity
      rw [hS, nodeCount_sumOn]
      calc _ ≤ #(range (2 * (D + 1))) • (3 * (89 * ((D + 1) * (s + 1) ^ 2)) ^ 2) + 1 :=
            Nat.add_le_add_right (sum_le_card_nsmul _ _ _ hcL) 1
        _ = 47526 * ((D + 1) ^ 3 * (s + 1) ^ 4) + 1 := by
          rw [card_range, smul_eq_mul]
          ring
        _ ≤ _ := by omega
    have hS1 : 1 ≤ S.nodeCount := by simp [hS, nodeCount_sumOn]
    have hTn : T.nodeCount = L.nodeCount + 2 := by
      simp [hT, Formula.nodeCount_gate, Fin.sum_univ_two]
    have hLn : L.nodeCount ≤ (S.nodeCount + 1) * (3 * S.nodeCount) + 1 :=
      nodeCount_lowPartFormula_le _ _ _
    calc _ ≤ T.nodeCount * 3 :=
          nodeCount_substFormula_le (fun k => (nodeCount_affineInput _ _ _ k).le) (by norm_num) _
      _ ≤ ((S.nodeCount + 1) * (3 * S.nodeCount) + 1 + 2) * 3 := by omega
      _ ≤ 27 * S.nodeCount ^ 2 := succ_mul_three_mul_add_le hS1
      _ ≤ 27 * (47527 * ((D + 1) ^ 3 * (s + 1) ^ 4)) ^ 2 := by gcongr
      _ = (27 * 47527 ^ 2) * ((s + 1) ^ 8 * (D + 1) ^ 6) := by ring
      _ ≤ 2 ^ 36 * ((s + 1) ^ 8 * (D + 1) ^ 6) := Nat.mul_le_mul_right _ (by norm_num)
      _ = rootCost s D := by simp only [rootCost]; ring

end Cslib.Circuits.Arithmetic.SPFormula
