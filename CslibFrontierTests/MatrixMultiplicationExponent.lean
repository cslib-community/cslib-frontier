/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

import CslibFrontier.Computability.Circuit.Arithmetic.MatrixMultiplication.NineQuarters
import CslibFrontier.Computability.Circuit.Arithmetic.MatrixMultiplication.StrassenRank
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! # The matrix multiplication exponent: checked instances

The trivial algorithm shows that `3` is an admissible exponent over `ℚ`, so the set of admissible
exponents is nonempty; every admissible exponent is at least `2`, so `omega ℚ` is a true infimum
with `2 ≤ omega ℚ ≤ 3`; and the headline gives `omega ℚ ≤ 9 / 4` and circuits of size
`O(n ^ (9/4 + 1/100))`. Over `𝔽₂` a circuit can output the product of every pair of matrices
without computing matrix multiplication in the formal model. Over every field, including `𝔽₂`,
`omega` is the rank exponent. -/

namespace CslibFrontierTests.MatrixMultiplicationExponent

open Cslib.Circuits.Arithmetic.MatrixMultiplication

/-- The trivial algorithm: `3` is admissible. -/
example : AdmissibleExponent ℚ 3 :=
  admissibleExponent_three

/-- Admissible exponents are at least `2`. -/
example : 2 ≤ (3 : ℝ) :=
  two_le_of_admissibleExponent (K := ℚ) admissibleExponent_three

/-- `omega ℚ ≤ 3`. -/
example : omega ℚ ≤ 3 :=
  omega_le_of_admissibleExponent admissibleExponent_three

/-- `omega ℚ ≥ 2`: the infimum is over exponents at least `2`. -/
example : 2 ≤ omega ℚ :=
  le_csInf ⟨3, admissibleExponent_three⟩ fun _ hτ => two_le_of_admissibleExponent hτ

/-- Block recursion on the trivial algorithm for `2 × 2` matrices (`8 ≤ 2 ^ 3`) recovers the
exponent `3`. -/
example : AdmissibleExponent ℚ 3 :=
  admissibleExponent_of_rank (by norm_num) (Cslib.Tensor.rank_mm 2 2 2)
    (by rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num) (by norm_num)

/-- **`ω ≤ 9/4` over `ℚ`.** -/
example : omega ℚ ≤ 9 / 4 :=
  omega_le_nine_quarters ℚ

/-- Circuits of size `O(n ^ (9/4 + 1/100))` for every `n`. -/
example : AdmissibleExponent ℚ (9 / 4 + 1 / 100) :=
  admissibleExponent_nine_quarters ℚ (by norm_num)

/-- The same over any field of characteristic zero, for instance `ℝ`. -/
example : omega ℝ ≤ 9 / 4 :=
  omega_le_nine_quarters ℝ

/-! ### Formal versus semantic correctness

Over `𝔽₂` every element satisfies `c ^ 2 = c`. So a circuit that multiplies the `1 × 1` matrices
`(a)` and `(b)` and squares the result outputs `a b` on every input. It does not compute matrix
multiplication: its output is the polynomial `(X₀ X₁) ^ 2`, not `X₀ X₁`. -/

section Formal

open Cslib.Circuits MvPolynomial

/-- The polynomials in the inputs of `1 × 1` matrix multiplication over `𝔽₂`. -/
private abbrev P := MvPolynomial (Fin (1 * 1 + 1 * 1)) (ZMod 2)

/-- The product of the two inputs, as a function of the inputs. -/
private def ab {U : Type*} [Mul U] (x : Fin (1 * 1 + 1 * 1) → U) : U :=
  leftMatrix x 0 0 * rightMatrix x 0 0

/-- A circuit that outputs the square of the product of the two inputs. -/
private theorem exists_squaring :
    ∃ C : Circuit (arithSignature (ZMod 2)) (1 * 1 + 1 * 1) (1 * 1),
      C.Computes (arithInterpretationWith (ZMod 2) (MvPolynomial.C : ZMod 2 → P))
        fun x _ => ab x * ab x := by
  have h : Synthesis (arithInterpretationWith (ZMod 2) (MvPolynomial.C : ZMod 2 → P))
      (inputs _) {fun x => ab x * ab x} 2 :=
    (Synthesis.arith_mul (s := inputs _) (f := fun x : Fin (1 * 1 + 1 * 1) → P => leftMatrix x 0 0)
      (g := fun x => rightMatrix x 0 0) ⟨_, rfl⟩ ⟨_, rfl⟩).trans
      (Synthesis.arith_mul (f := ab) (g := ab) (Set.mem_union_right _ rfl)
        (Set.mem_union_right _ rfl))
  obtain ⟨C, hC, -⟩ := (h.mono Set.Subset.rfl (fun _ ⟨_, e⟩ => e.symm) le_rfl :
    Synthesis _ (inputs _) (Set.range fun (_ : Fin (1 * 1)) x => ab x * ab x) 2)
      |>.exists_circuit_outputs
  exact ⟨C, hC⟩

/-- The squaring circuit outputs the product of any two `1 × 1` matrices over `𝔽₂`. -/
example : ∃ C : Circuit (arithSignature (ZMod 2)) (1 * 1 + 1 * 1) (1 * 1),
    (∀ A B : Matrix (Fin 1) (Fin 1) (ZMod 2),
      C.eval (arithInterpretation (ZMod 2)) (matrixInputs (ZMod 2) A B) = entry (ZMod 2) (A * B)) ∧
    ¬ ComputesMatMul (ZMod 2) C := by
  obtain ⟨C, hC⟩ := exists_squaring
  refine ⟨C, fun A B => funext fun t => ?_, fun h => ?_⟩
  · change C.eval (arithInterpretationWith (ZMod 2) id) _ t = _
    have e := C.eval_arithInterpretationWith_mvPolynomial id (matrixInputs (ZMod 2) A B) t
    rw [Function.comp_id, hC] at e
    have hl : eval (matrixInputs (ZMod 2) A B) (leftMatrix X 0 0) = A 0 0 := by
      rw [leftMatrix_apply, eval_X]
      exact congrFun (congrFun (leftMatrix_matrixInputs A B) 0) 0
    have hr : eval (matrixInputs (ZMod 2) A B) (rightMatrix X 0 0) = B 0 0 := by
      rw [rightMatrix_apply, eval_X]
      exact congrFun (congrFun (rightMatrix_matrixInputs A B) 0) 0
    have hsq : ∀ c : ZMod 2, c * c = c := by decide
    rw [← e]
    simp only [ab, map_mul, hl, hr, hsq]
    simp [entry, Matrix.mul_apply, Fin.eq_zero]
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have e := congrFun h 0
    rw [hC] at e
    have hx : (ab (X : Fin (1 * 1 + 1 * 1) → P)) ≠ 0 := mul_ne_zero (X_ne_zero _) (X_ne_zero _)
    have hd : (ab (X : Fin (1 * 1 + 1 * 1) → P)).totalDegree = 2 := by
      rw [ab, leftMatrix_apply, rightMatrix_apply,
        totalDegree_mul_of_isDomain (X_ne_zero _) (X_ne_zero _), totalDegree_X, totalDegree_X]
    have he : entry P (leftMatrix X * rightMatrix X) 0 = ab X := by
      simp [entry, Matrix.mul_apply, ab, Fin.eq_zero]
    rw [he] at e
    have := congrArg totalDegree e
    rw [totalDegree_mul_of_isDomain hx hx, hd] at this
    omega

end Formal

/-! ### The exponent is the rank exponent, over every field -/

section RankExponent

open Cslib Cslib.Tensor

/-- The flattening bound: a rank decomposition of `⟨2, 2, 2⟩` has at least `4` terms. -/
example {r : ℕ} (h : Rank r (mm 2 2 2 : Tensor (ZMod 2) _ _ _)) : 4 ≤ r :=
  mul_self_le_of_rank_mm h

/-- Over `𝔽₂`, `omega` is the rank exponent. -/
example : omega (ZMod 2) = rankExponent (ZMod 2) :=
  omega_eq_rankExponent (ZMod 2)

/-- Over `𝔽₂`, circuits below an exponent give rank decompositions below it. -/
example {τ : ℝ} (hτ : omega (ZMod 2) < τ) : ∃ c : ℝ, 0 < c ∧ ∀ D : ℕ, 1 ≤ D →
    ∃ r : ℕ, (r : ℝ) ≤ c * (D : ℝ) ^ τ ∧ Rank r (mm D D D : Tensor (ZMod 2) _ _ _) :=
  exists_rank_mm_le_rpow (ZMod 2) hτ

end RankExponent

end CslibFrontierTests.MatrixMultiplicationExponent
