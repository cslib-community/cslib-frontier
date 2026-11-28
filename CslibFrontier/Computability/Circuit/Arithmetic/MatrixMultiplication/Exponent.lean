/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic
public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Computability.Circuit.Synthesis
import CslibFrontier.Computability.Circuit.Arithmetic.Synthesis
import CslibFrontier.Computability.Circuit.Inputization
import CslibFrontier.Tactic.LinarithCast
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# The exponent of matrix multiplication

A circuit `C : Circuit (arithSignature K) (n * n + n * n) (n * n)` *computes `n × n` matrix
multiplication* (`ComputesMatMul`) when, fed with the variables, the entries of `A` followed by
those of `B` in the row-major numbering `finProdFinEquiv`, its outputs are the entries of `A * B`
as polynomials over `K`. This is the formal model of [Bürgisser, Clausen and
Shokrollahi][BurgisserClausenShokrollahi1997], Chapter 15. Such a circuit computes the product
over every commutative `K`-algebra (`ComputesMatMul.eval_algebra`), in particular on all matrices
over `K` (`ComputesMatMul.eval`). Over a finite field the converse fails: a circuit can output the
right values without the right polynomials. Over an infinite integral domain the two notions agree
(`computesMatMul_iff_eval`). Its size `C.size` counts the gates: additions, multiplications and
constants, each of cost one.

A real `τ` is an *admissible exponent* (`AdmissibleExponent K τ`) when for every `ε > 0` there is
a constant `c` such that, for every `n ≥ 1`, some circuit of size at most `c n ^ (τ + ε)`
computes `n × n` matrix multiplication. The *exponent of matrix multiplication* `omega K` is the
infimum of the admissible exponents. This is the definition of [Pass][Pass2026], §1, with
arithmetic circuits over `K` in place of integer arithmetic, and the formal arithmetic model of
[Bürgisser, Clausen and Shokrollahi][BurgisserClausenShokrollahi1997], Chapter 15.

**Block recursion** (`admissibleExponent_of_rank`, [Strassen][Strassen1969]; [Pass][Pass2026],
proof of Theorem 1.1): a bilinear algorithm with `r` multiplications for `v × v` matrices, that is
`Tensor.Rank r (Tensor.mm v v v)`, gives circuits of size `O(n ^ τ)` whenever `r ≤ v ^ τ` and
`τ > 2`: apply the algorithm to `v × v` arrays of blocks, recursively, with linear encoding and
decoding of the blocks costing `O(r n ^ 2)` per level.

## Main definitions

* `Cslib.Circuits.Arithmetic.MatrixMultiplication.leftMatrix`,
  `Cslib.Circuits.Arithmetic.MatrixMultiplication.rightMatrix`: the two matrices encoded by an
  input vector.
* `Cslib.Circuits.Arithmetic.MatrixMultiplication.ComputesMatMul`
* `Cslib.Circuits.Arithmetic.MatrixMultiplication.AdmissibleExponent`
* `Cslib.Circuits.Arithmetic.MatrixMultiplication.omega`

## Main results

* `Cslib.Circuits.Arithmetic.MatrixMultiplication.ComputesMatMul.eval_algebra`,
  `Cslib.Circuits.Arithmetic.MatrixMultiplication.ComputesMatMul.eval`,
  `Cslib.Circuits.Arithmetic.MatrixMultiplication.computesMatMul_iff_eval`: formal and semantic
  correctness.
* `Cslib.Circuits.Arithmetic.MatrixMultiplication.admissibleExponent_of_rank`: block recursion.
* `Cslib.Circuits.Arithmetic.MatrixMultiplication.two_le_of_admissibleExponent`: every
  admissible exponent is at least `2`, so `omega` is a true infimum.
* `Cslib.Circuits.Arithmetic.MatrixMultiplication.omega_le_of_admissibleExponent`.

## References

* [V. Strassen, *Gaussian elimination is not optimal*][Strassen1969]
* [P. Bürgisser, M. Clausen, M. A. Shokrollahi, *Algebraic Complexity
  Theory*][BurgisserClausenShokrollahi1997], Chapter 15
* [R. Pass, *Matrix Multiplication from Polynomial Packings*][Pass2026], §1 and §4.3
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic.MatrixMultiplication

open Cslib.Circuits Cslib.Tensor

section Encoding

variable {U : Type*} {n : ℕ}

/-- The matrix `A` encoded by an input vector: its first `n * n` entries, row-major. -/
def leftMatrix (x : Fin (n * n + n * n) → U) : Matrix (Fin n) (Fin n) U :=
  Matrix.of fun i j => x (Fin.castAdd (n * n) (finProdFinEquiv (i, j)))

/-- The matrix `B` encoded by an input vector: its last `n * n` entries, row-major. -/
def rightMatrix (x : Fin (n * n + n * n) → U) : Matrix (Fin n) (Fin n) U :=
  Matrix.of fun i j => x (Fin.natAdd (n * n) (finProdFinEquiv (i, j)))

/-- Entry `(i, j)` of the left matrix is input `(i, j)` of the first block. -/
theorem leftMatrix_apply (x : Fin (n * n + n * n) → U) (i j : Fin n) :
    leftMatrix x i j = x (Fin.castAdd (n * n) (finProdFinEquiv (i, j))) := rfl

/-- Entry `(i, j)` of the right matrix is input `(i, j)` of the second block. -/
theorem rightMatrix_apply (x : Fin (n * n + n * n) → U) (i j : Fin n) :
    rightMatrix x i j = x (Fin.natAdd (n * n) (finProdFinEquiv (i, j))) := rfl

/-- Decoding commutes with mapping the entries. -/
theorem map_leftMatrix {V : Type*} (f : U → V) (x : Fin (n * n + n * n) → U) :
    (leftMatrix x).map f = leftMatrix (f ∘ x) := rfl

/-- Decoding commutes with mapping the entries. -/
theorem map_rightMatrix {V : Type*} (f : U → V) (x : Fin (n * n + n * n) → U) :
    (rightMatrix x).map f = rightMatrix (f ∘ x) := rfl

end Encoding

variable (K : Type*) [CommSemiring K]

/-- The entry `t` of a matrix, numbered row-major. -/
def entry {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (t : Fin (n * n)) : K :=
  A (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2

/-- The inputs of a matrix multiplication circuit: the entries of `A` followed by those of
`B`. -/
def matrixInputs {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) : Fin (n * n + n * n) → K :=
  Fin.append (entry K A) (entry K B)

/-- `C` computes `n × n` matrix multiplication *formally*: fed with the variables, the entries of
`A` followed by those of `B`, it outputs the entries of `A * B` as polynomials over `K`
([Bürgisser, Clausen and Shokrollahi][BurgisserClausenShokrollahi1997], Chapter 15). Over a
finite field this is stronger than outputting the right values (`computesMatMul_iff_eval`). -/
def ComputesMatMul {n : ℕ} (C : Circuit (arithSignature K) (n * n + n * n) (n * n)) : Prop :=
  C.eval (arithInterpretationWith K MvPolynomial.C) MvPolynomial.X =
    entry _ (leftMatrix MvPolynomial.X * rightMatrix MvPolynomial.X)

/-- `τ` is an admissible exponent: for every `ε > 0`, circuits of size `O(n ^ (τ + ε))` compute
`n × n` matrix multiplication for every `n ≥ 1`. -/
def AdmissibleExponent (τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
    ∃ C : Circuit (arithSignature K) (n * n + n * n) (n * n),
      ComputesMatMul K C ∧ (C.size : ℝ) ≤ c * (n : ℝ) ^ (τ + ε)

/-- **The exponent of matrix multiplication**: the infimum of the admissible exponents. -/
noncomputable def omega : ℝ :=
  sInf {τ : ℝ | AdmissibleExponent K τ}

variable {K}

/-- Admissibility is monotone. -/
theorem AdmissibleExponent.mono {τ τ' : ℝ} (h : AdmissibleExponent K τ) (hτ : τ ≤ τ') :
    AdmissibleExponent K τ' := by
  intro ε hε
  obtain ⟨c, hc, hC⟩ := h ε hε
  refine ⟨c, hc, fun n hn => ?_⟩
  obtain ⟨C, hC, hsize⟩ := hC n hn
  refine ⟨C, hC, hsize.trans (mul_le_mul_of_nonneg_left ?_ hc.le)⟩
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

/-! ### Formal and semantic correctness -/

section Correctness

variable {n : ℕ} {R : Type*} [CommSemiring R]

omit [CommSemiring R] in
/-- The left matrix encoded by `matrixInputs R A B` is `A`. -/
@[simp] theorem leftMatrix_matrixInputs (A B : Matrix (Fin n) (Fin n) R) :
    leftMatrix (matrixInputs R A B) = A := by
  ext i j
  simp only [leftMatrix, Matrix.of_apply, matrixInputs, Fin.append_left, entry,
    Equiv.symm_apply_apply]

omit [CommSemiring R] in
/-- The right matrix encoded by `matrixInputs R A B` is `B`. -/
@[simp] theorem rightMatrix_matrixInputs (A B : Matrix (Fin n) (Fin n) R) :
    rightMatrix (matrixInputs R A B) = B := by
  ext i j
  simp only [rightMatrix, Matrix.of_apply, matrixInputs, Fin.append_right, entry,
    Equiv.symm_apply_apply]

omit [CommSemiring R] in
/-- The input vector is the encoding of the two matrices it encodes. -/
@[simp] theorem matrixInputs_leftMatrix_rightMatrix (x : Fin (n * n + n * n) → R) :
    matrixInputs R (leftMatrix x) (rightMatrix x) = x := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [matrixInputs, Fin.append_left, entry, leftMatrix_apply, Prod.mk.eta,
      Equiv.apply_symm_apply]
  · simp only [matrixInputs, Fin.append_right, entry, rightMatrix_apply, Prod.mk.eta,
      Equiv.apply_symm_apply]

/-- A ring homomorphism maps the entries of the product of the encoded matrices to those of the
product of the encoded images. -/
private theorem map_entry_mul {S : Type*} [CommSemiring S] (f : R →+* S)
    (x : Fin (n * n + n * n) → R) (t : Fin (n * n)) :
    f (entry R (leftMatrix x * rightMatrix x) t) =
      entry S (leftMatrix (f ∘ x) * rightMatrix (f ∘ x)) t := by
  rw [← map_leftMatrix, ← map_rightMatrix, ← Matrix.map_mul]
  rfl

variable {C : Circuit (arithSignature K) (n * n + n * n) (n * n)}

/-- A circuit computing matrix multiplication formally computes it over every commutative
`K`-algebra `R`, with its constants mapped into `R`. -/
theorem ComputesMatMul.eval_algebra [Algebra K R] (hC : ComputesMatMul K C)
    (A B : Matrix (Fin n) (Fin n) R) :
    C.eval (arithInterpretationWith K (algebraMap K R)) (matrixInputs R A B) = entry R (A * B) := by
  funext t
  let f := MvPolynomial.eval₂Hom (algebraMap K R) (matrixInputs R A B)
  have e := C.eval₂_arithInterpretationWith_mvPolynomial id (algebraMap K R) (matrixInputs R A B) t
  rw [Function.comp_id, Function.comp_id, hC] at e
  have hX : ⇑f ∘ MvPolynomial.X = matrixInputs R A B :=
    funext fun i => MvPolynomial.eval₂Hom_X' _ _ _
  rw [← e, ← MvPolynomial.coe_eval₂Hom, map_entry_mul f, hX, leftMatrix_matrixInputs,
    rightMatrix_matrixInputs]

/-- A circuit computing matrix multiplication formally outputs the product of any two matrices
over `K`. -/
theorem ComputesMatMul.eval (hC : ComputesMatMul K C) (A B : Matrix (Fin n) (Fin n) K) :
    C.eval (arithInterpretation K) (matrixInputs K A B) = entry K (A * B) := by
  have := hC.eval_algebra A B
  rwa [Algebra.algebraMap_self, RingHom.coe_id] at this

end Correctness

/-- Over an infinite integral domain, a circuit computes matrix multiplication formally exactly
when it outputs the product of any two matrices. -/
theorem computesMatMul_iff_eval {K : Type*} [CommRing K] [IsDomain K] [Infinite K] {n : ℕ}
    {C : Circuit (arithSignature K) (n * n + n * n) (n * n)} :
    ComputesMatMul K C ↔ ∀ A B : Matrix (Fin n) (Fin n) K,
      C.eval (arithInterpretation K) (matrixInputs K A B) = entry K (A * B) := by
  refine ⟨fun hC => hC.eval, fun h => ?_⟩
  unfold ComputesMatMul
  funext t
  refine MvPolynomial.funext fun x => ?_
  have e := C.eval_arithInterpretationWith_mvPolynomial id x t
  rw [Function.comp_id] at e
  rw [e, map_entry_mul (MvPolynomial.eval x),
    show ⇑(MvPolynomial.eval x) ∘ MvPolynomial.X = x from funext fun _ => MvPolynomial.eval_X _]
  have := congrFun (h (leftMatrix x) (rightMatrix x)) t
  rw [matrixInputs_leftMatrix_rightMatrix] at this
  exact this

/-! ### Circuits from synthesis bounds -/

section Helpers

variable {n : ℕ} {R : Type*} [CommSemiring R] [Algebra K R]

variable (K) in
/-- The arithmetic basis over `K`, interpreted in a `K`-algebra `R`. -/
private abbrev arithIn (R : Type*) [CommSemiring R] [Algebra K R] :
    Interpretation (arithSignature K) R :=
  arithInterpretationWith K (algebraMap K R)

variable (K) in
/-- The polynomials in the inputs of `n × n` matrix multiplication. -/
private abbrev Poly (n : ℕ) := MvPolynomial (Fin (n * n + n * n)) K

/-- Entry `t` of the product of the two encoded matrices, as a function of the inputs. -/
private def matMulFun (n : ℕ) (t : Fin (n * n)) (x : Fin (n * n + n * n) → R) : R :=
  entry R (leftMatrix x * rightMatrix x) t

omit [CommSemiring R] in
private theorem leftMatrix_mem_inputs (i j : Fin n) :
    (fun x : Fin (n * n + n * n) → R => leftMatrix x i j) ∈ inputs (n * n + n * n) :=
  ⟨Fin.castAdd (n * n) (finProdFinEquiv (i, j)), rfl⟩

omit [CommSemiring R] in
private theorem rightMatrix_mem_inputs (i j : Fin n) :
    (fun x : Fin (n * n + n * n) → R => rightMatrix x i j) ∈ inputs (n * n + n * n) :=
  ⟨Fin.natAdd (n * n) (finProdFinEquiv (i, j)), rfl⟩

/-- A synthesis bound for the entries of the product over the polynomials in the inputs gives a
circuit computing matrix multiplication within the bound. -/
private theorem exists_computesMatMul_of_synthesis {cost : ℕ}
    (h : Synthesis (arithIn K (Poly K n)) (inputs (n * n + n * n)) (Set.range (matMulFun n))
      cost) :
    ∃ C : Circuit (arithSignature K) (n * n + n * n) (n * n),
      ComputesMatMul K C ∧ C.size ≤ cost := by
  obtain ⟨C, hC, hsize⟩ := h.exists_circuit_outputs
  refine ⟨C, ?_, hsize⟩
  unfold ComputesMatMul
  rw [← MvPolynomial.algebraMap_eq]
  exact hC MvPolynomial.X

/-- Zero is available at the cost of one gate. -/
private theorem synthesis_zero {s : Set ((Fin n → R) → R)} :
    Synthesis (arithIn K R) s {fun _ => (0 : R)} 1 := by
  have := Synthesis.arith_const (s := s) (constant := algebraMap K R) (0 : K)
  rwa [map_zero] at this

/-- Multiplying an available function by a constant costs two gates. -/
private theorem synthesis_const_mul {s : Set ((Fin n → R) → R)} (a : K)
    {f : (Fin n → R) → R} (hf : f ∈ s) :
    Synthesis (arithIn K R) s {fun x => algebraMap K R a * f x} 2 :=
  Synthesis.combine (Synthesis.arith_const (constant := algebraMap K R) a) (Synthesis.of_mem hf)
    (Synthesis.arith_mul (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl))

/-- The trivial algorithm: `n × n` matrix multiplication with `2 n ^ 3 + 1` gates. -/
private theorem exists_circuit_trivial (n : ℕ) :
    ∃ C : Circuit (arithSignature K) (n * n + n * n) (n * n),
      ComputesMatMul K C ∧ C.size ≤ 2 * n ^ 3 + 1 := by
  refine exists_computesMatMul_of_synthesis (n := n) ?_
  have h0 : (fun _ => (0 : Poly K n)) ∈ inputs (n * n + n * n) ∪ {fun _ => (0 : Poly K n)} :=
    Set.mem_union_right _ rfl
  have hentry (t : Fin (n * n)) :
      Synthesis (arithIn K (Poly K n)) (inputs (n * n + n * n) ∪ {fun _ => (0 : Poly K n)})
        {matMulFun n t} (n * 2) := by
    have := Synthesis.arith_sum (constant := algebraMap K (Poly K n))
      (Finset.univ : Finset (Fin n))
      (fun j x => leftMatrix x (finProdFinEquiv.symm t).1 j *
        rightMatrix x j (finProdFinEquiv.symm t).2) (fun _ => 1) h0 fun j _ =>
      Synthesis.arith_mul (Set.mem_union_left _ (leftMatrix_mem_inputs _ _))
        (Set.mem_union_left _ (rightMatrix_mem_inputs _ _))
    refine this.mono Set.Subset.rfl (Set.singleton_subset_iff.mpr ?_) (by simp)
    funext x
    simp only [matMulFun, entry, Matrix.mul_apply]
  have := synthesis_zero.trans (Synthesis.family _ _ hentry)
  refine this.mono Set.Subset.rfl Set.Subset.rfl ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  nlinarith [Nat.zero_le n]

end Helpers

/-- The trivial algorithm: `3` is admissible. -/
theorem admissibleExponent_three : AdmissibleExponent K 3 := by
  intro ε hε
  refine ⟨3, by norm_num, fun n hn => ?_⟩
  obtain ⟨C, hC, hsize⟩ := exists_circuit_trivial (K := K) n
  refine ⟨C, hC, ?_⟩
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h3 : (n : ℝ) ^ (3 : ℕ) ≤ (n : ℝ) ^ (3 + ε) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hn' (by push_cast; linarith)
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ (3 : ℕ) := one_le_pow₀ hn'
  calc (C.size : ℝ) ≤ ((2 * n ^ 3 + 1 : ℕ) : ℝ) := by exact_mod_cast hsize
    _ = 2 * (n : ℝ) ^ (3 : ℕ) + 1 := by push_cast; ring
    _ ≤ 3 * (n : ℝ) ^ (3 + ε) := by linarith

section LowerBound

variable [Nontrivial K] {n : ℕ} {C : Circuit (arithSignature K) (n * n + n * n) (n * n)}

/-- Distinct entries of the product are distinct functions of the inputs. -/
private theorem matMulFun_injective : Function.Injective (matMulFun (R := K) n) := by
  intro t t' htt'
  by_contra hne
  have key (A B : Matrix (Fin n) (Fin n) K) : entry K (A * B) t = entry K (A * B) t' := by
    simpa [matMulFun] using
      congrFun htt' (matrixInputs K A B)
  have := key 1 (Matrix.of fun a b => if (a, b) = finProdFinEquiv.symm t then 1 else 0)
  have hne' : finProdFinEquiv.symm t' ≠ finProdFinEquiv.symm t :=
    fun h => hne (finProdFinEquiv.symm.injective h).symm
  rw [Matrix.one_mul] at this
  simp only [entry, Matrix.of_apply, Prod.mk.eta, ite_true, hne', ite_false] at this
  exact one_ne_zero this

/-- No entry of the product is an input. -/
private theorem matMulFun_ne_input (t : Fin (n * n)) (i : Fin (n * n + n * n)) :
    matMulFun (R := K) n t ≠ fun x => x i := by
  intro h
  have key (A B : Matrix (Fin n) (Fin n) K) : entry K (A * B) t = matrixInputs K A B i := by
    simpa [matMulFun] using
      congrFun h (matrixInputs K A B)
  revert key
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> intro key
  · have := key (Matrix.of fun _ _ => 1) 0
    simp only [Matrix.mul_zero, entry, Matrix.zero_apply, matrixInputs, Fin.append_left,
      Matrix.of_apply] at this
    exact zero_ne_one this
  · have := key 0 (Matrix.of fun _ _ => 1)
    simp only [Matrix.zero_mul, entry, Matrix.zero_apply, matrixInputs, Fin.append_right,
      Matrix.of_apply] at this
    exact zero_ne_one this

/-- A circuit computing `n × n` matrix multiplication has at least `n ^ 2` gates: the entries of
the product are `n ^ 2` distinct functions of the inputs, none of them an input. -/
private theorem mul_self_le_size (hC : ComputesMatMul K C) : n * n ≤ C.size := by
  have hcomp : C.Computes (arithInterpretation K) fun x t => matMulFun n t x := fun x => by
    rw [← matrixInputs_leftMatrix_rightMatrix x, hC.eval]
    funext t
    simp [matMulFun]
  have h := (card_nonInputComponents_le_ecomplexity (arithInterpretation K)
    fun x t => matMulFun n t x).trans (ecomplexity_le_of_computes C hcomp)
  rw [card_nonInputComponents_eq matMulFun_injective matMulFun_ne_input] at h
  exact_mod_cast h

end LowerBound

/-- Every admissible exponent is at least `2`: a circuit computing `n × n` matrix multiplication
has at least `n ^ 2` gates, one for each output, since the entries of `A * B` are pairwise
distinct functions of the inputs and none is an input. -/
theorem two_le_of_admissibleExponent [Nontrivial K] {τ : ℝ} (h : AdmissibleExponent K τ) :
    2 ≤ τ := by
  by_contra hτ
  set ε : ℝ := (2 - τ) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨c, hc, hC⟩ := h ε hε0
  -- every `n ≥ 1` satisfies `n ^ ε ≤ c`
  have hle (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) ^ ε ≤ c := by
    obtain ⟨C, hC, hsize⟩ := hC n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hsq : (n : ℝ) ^ ε * (n : ℝ) ^ (τ + ε) ≤ c * (n : ℝ) ^ (τ + ε) := by
      rw [← Real.rpow_add hn']
      have h2 : ε + (τ + ε) = 2 := by rw [hε]; ring
      rw [h2, Real.rpow_two]
      calc (n : ℝ) ^ 2 = ((n * n : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (C.size : ℝ) := by exact_mod_cast mul_self_le_size hC
        _ ≤ c * (n : ℝ) ^ (τ + ε) := hsize
    exact le_of_mul_le_mul_right hsq (Real.rpow_pos_of_pos hn' _)
  -- but `n ^ ε` exceeds `c` for `n` beyond `c ^ (1 / ε)`
  set n : ℕ := ⌈c ^ (1 / ε)⌉₊ + 1 with hn
  have hcn : c ^ (1 / ε) < n := by
    rw [hn, Nat.cast_add, Nat.cast_one]; exact (Nat.le_ceil _).trans_lt (lt_add_one _)
  have hlt : c < (n : ℝ) ^ ε := by
    calc c = (c ^ (1 / ε)) ^ ε := by
          rw [← Real.rpow_mul hc.le, one_div_mul_cancel hε0.ne', Real.rpow_one]
      _ < (n : ℝ) ^ ε := Real.rpow_lt_rpow (Real.rpow_nonneg hc.le _) hcn hε0
  exact absurd (hle n (by omega)) (not_le.mpr hlt)

theorem omega_le_of_admissibleExponent [Nontrivial K] {τ : ℝ} (h : AdmissibleExponent K τ) :
    omega K ≤ τ :=
  csInf_le ⟨2, fun _ hτ => two_le_of_admissibleExponent hτ⟩ h

/-! ### Block recursion -/

section BlockRecursion

variable {v r m : ℕ} {R : Type*} [CommSemiring R] [Algebra K R]

/-- The bilinear map of the unit tensor is coordinatewise multiplication. -/
private theorem bil_unit (u w : Fin r → R) (ν : Fin r) :
    (unit r : Tensor R _ _ _).bil u w ν = u ν * w ν := by
  simp [Tensor.bil, unit_apply, ite_and, ite_mul, Finset.sum_ite_eq']

/-- A bilinear algorithm with `r` multiplications for `v × v` matrices, with encoders `α`, `β`
and decoder `γ` over `K`, works over every commutative `K`-algebra `R`:
`(A * B) i k = ∑ ν, γ (i, k) ν * (∑ x, α ν x * A x) * (∑ y, β ν y * B y)`. -/
private theorem encoders_spec {α β : Matrix (Fin r) (Fin v × Fin v) K}
    {γ : Matrix (Fin v × Fin v) (Fin r) K} (h : restrict α β γ (unit r) = mm v v v)
    (A B : Fin v × Fin v → R) (c : Fin v × Fin v) :
    ∑ j, A (c.1, j) * B (j, c.2) = ∑ ν, algebraMap K R (γ c ν) *
      ((∑ x, algebraMap K R (α ν x) * A x) * (∑ y, algebraMap K R (β ν y) * B y)) := by
  have hR : restrict (α.map (algebraMap K R)) (β.map (algebraMap K R)) (γ.map (algebraMap K R))
      (unit r) = (mm v v v : Tensor R _ _ _) := by
    funext x y z
    have hK := congrFun (congrFun (congrFun h x) y) z
    rw [restrict_unit] at hK ⊢
    calc ∑ k, (α.map (algebraMap K R)) k x * (β.map (algebraMap K R)) k y *
          (γ.map (algebraMap K R)) z k
        = algebraMap K R (∑ k, α k x * β k y * γ z k) := by simp [map_sum, map_mul]
      _ = (mm v v v : Tensor R _ _ _) x y z := by
        rw [hK, mm_apply, mm_apply]
        split_ifs <;> simp
  have := congrFun (congrArg (fun T : Tensor R _ _ _ => T.bil A B) hR) c
  simp only [bil_restrict, bil_mm, Matrix.mulVec, dotProduct, bil_unit, Matrix.map_apply] at this
  exact this.symm

/-- The `ν`-th encoded block of a `v m × v m` matrix, viewed as a `v × v` array of `m × m`
blocks: `∑ x, α ν x • A_x`. -/
private def encode (α : Matrix (Fin r) (Fin v × Fin v) K) (ν : Fin r)
    (A : Matrix (Fin (v * m)) (Fin (v * m)) R) : Matrix (Fin m) (Fin m) R :=
  Matrix.of fun a l => ∑ p : Fin v × Fin v,
    algebraMap K R (α ν p) * A (finProdFinEquiv (p.1, a)) (finProdFinEquiv (p.2, l))

/-- The bilinear algorithm applied blockwise computes the product of `v m × v m` matrices. -/
private theorem mul_apply_eq_sum_encode {α β : Matrix (Fin r) (Fin v × Fin v) K}
    {γ : Matrix (Fin v × Fin v) (Fin r) K}
    (hid : ∀ (A B : Fin v × Fin v → R) (c : Fin v × Fin v),
      ∑ j, A (c.1, j) * B (j, c.2) = ∑ ν, algebraMap K R (γ c ν) *
        ((∑ x, algebraMap K R (α ν x) * A x) * (∑ y, algebraMap K R (β ν y) * B y)))
    (A B : Matrix (Fin (v * m)) (Fin (v * m)) R) (i k : Fin v) (a b : Fin m) :
    (A * B) (finProdFinEquiv (i, a)) (finProdFinEquiv (k, b)) =
      ∑ ν, algebraMap K R (γ (i, k) ν) * (encode α ν A * encode β ν B) a b := by
  have h1 : (A * B) (finProdFinEquiv (i, a)) (finProdFinEquiv (k, b)) =
      ∑ l : Fin m, ∑ j : Fin v, A (finProdFinEquiv (i, a)) (finProdFinEquiv (j, l)) *
        B (finProdFinEquiv (j, l)) (finProdFinEquiv (k, b)) := by
    rw [Matrix.mul_apply, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  have h2 : ∀ ν, (encode α ν A * encode β ν B) a b =
      ∑ l : Fin m, (∑ p, algebraMap K R (α ν p) *
          A (finProdFinEquiv (p.1, a)) (finProdFinEquiv (p.2, l))) *
        (∑ q, algebraMap K R (β ν q) *
          B (finProdFinEquiv (q.1, l)) (finProdFinEquiv (q.2, b))) := fun ν => by
    simp only [Matrix.mul_apply, encode, Matrix.of_apply]
  simp only [h1, h2]
  conv_rhs => enter [2, ν]; rw [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => hid (fun p => A (finProdFinEquiv (p.1, a))
    (finProdFinEquiv (p.2, l))) (fun q => B (finProdFinEquiv (q.1, l)) (finProdFinEquiv (q.2, b)))
    (i, k)

/-- `n × n` matrix multiplication has a circuit of size at most `s`. -/
private def HasCircuit (n s : ℕ) : Prop :=
  ∃ C : Circuit (arithSignature K) (n * n + n * n) (n * n), ComputesMatMul K C ∧ C.size ≤ s

private theorem HasCircuit.congr {n n' s : ℕ} (h : n = n') (hC : HasCircuit (K := K) n s) :
    HasCircuit (K := K) n' s :=
  h ▸ hC

private theorem HasCircuit.mono {n s s' : ℕ} (hC : HasCircuit (K := K) n s) (h : s ≤ s') :
    HasCircuit (K := K) n s' :=
  let ⟨C, hC, hs⟩ := hC
  ⟨C, hC, hs.trans h⟩

/-- The inputs of the `ν`-th block product, encoded from the inputs of the `v m × v m`
multiplication: the entries of `encode α ν A` followed by those of `encode β ν B`. -/
private def encInputs (α β : Matrix (Fin r) (Fin v × Fin v) K) (ν : Fin r)
    (i : Fin (m * m + m * m)) (x : Fin (v * m * (v * m) + v * m * (v * m)) → R) : R :=
  matrixInputs R (encode α ν (leftMatrix x)) (encode β ν (rightMatrix x)) i

/-- Each encoded input is a linear combination of `v ^ 2` inputs: `3 v ^ 2` gates. -/
private theorem synthesis_encInputs (α β : Matrix (Fin r) (Fin v × Fin v) K) (ν : Fin r)
    (i : Fin (m * m + m * m)) :
    Synthesis (arithIn K R)
      (inputs (v * m * (v * m) + v * m * (v * m)) ∪ {fun _ => (0 : R)})
      {encInputs (R := R) α β ν i} (∑ _p : Fin v × Fin v, (2 + 1)) := by
  have h0 : (fun _ => (0 : R)) ∈
      inputs (v * m * (v * m) + v * m * (v * m)) ∪ {fun _ => (0 : R)} :=
    Set.mem_union_right _ rfl
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · have := Synthesis.arith_sum (constant := algebraMap K R) (Finset.univ : Finset (Fin v × Fin v))
      (fun p x => algebraMap K R (α ν p) *
        leftMatrix x (finProdFinEquiv (p.1, (finProdFinEquiv.symm i).1))
          (finProdFinEquiv (p.2, (finProdFinEquiv.symm i).2))) (fun _ => 2) h0 fun p _ =>
        synthesis_const_mul (α ν p) (Set.mem_union_left _ (leftMatrix_mem_inputs _ _))
    refine this.mono Set.Subset.rfl (Set.singleton_subset_iff.mpr ?_) le_rfl
    funext x
    simp only [encInputs, matrixInputs, Fin.append_left, entry, encode, Matrix.of_apply]
  · have := Synthesis.arith_sum (constant := algebraMap K R) (Finset.univ : Finset (Fin v × Fin v))
      (fun p x => algebraMap K R (β ν p) *
        rightMatrix x (finProdFinEquiv (p.1, (finProdFinEquiv.symm i).1))
          (finProdFinEquiv (p.2, (finProdFinEquiv.symm i).2))) (fun _ => 2) h0 fun p _ =>
        synthesis_const_mul (β ν p) (Set.mem_union_left _ (rightMatrix_mem_inputs _ _))
    refine this.mono Set.Subset.rfl (Set.singleton_subset_iff.mpr ?_) le_rfl
    funext x
    simp only [encInputs, matrixInputs, Fin.append_right, entry, encode, Matrix.of_apply]

/-- The entries of the `ν`-th block product, as functions of the inputs. -/
private def blockProd (α β : Matrix (Fin r) (Fin v × Fin v) K) (ν : Fin r) (t : Fin (m * m))
    (x : Fin (v * m * (v * m) + v * m * (v * m)) → R) : R :=
  entry R (encode α ν (leftMatrix x) * encode β ν (rightMatrix x)) t

/-- A circuit for `m × m` multiplication, fed with the encoded inputs, computes the block
products. -/
private theorem synthesis_blockProd {α β : Matrix (Fin r) (Fin v × Fin v) K} (ν : Fin r)
    {C : Circuit (arithSignature K) (m * m + m * m) (m * m)} (hC : ComputesMatMul K C)
    {s : Set ((Fin (v * m * (v * m) + v * m * (v * m)) → R) → R)}
    (hs : ∀ i, encInputs α β ν i ∈ s) :
    Synthesis (arithIn K R) s (Set.range (blockProd α β ν)) C.size := by
  have := Synthesis.circuit (I := arithIn K R) C (encInputs α β ν) hs
  refine this.mono Set.Subset.rfl (le_of_eq ?_) le_rfl
  congr 1 with t x : 2
  simp only [blockProd]
  rw [← congrFun (hC.eval_algebra (encode α ν (leftMatrix x)) (encode β ν (rightMatrix x))) t]
  rfl

/-- The entries of the `v m × v m` product are linear combinations of the block products. -/
private theorem matMulFun_eq_sum {α β : Matrix (Fin r) (Fin v × Fin v) K}
    {γ : Matrix (Fin v × Fin v) (Fin r) K}
    (hid : ∀ (A B : Fin v × Fin v → R) (c : Fin v × Fin v),
      ∑ j, A (c.1, j) * B (j, c.2) = ∑ ν, algebraMap K R (γ c ν) *
        ((∑ x, algebraMap K R (α ν x) * A x) * (∑ y, algebraMap K R (β ν y) * B y)))
    (t : Fin (v * m * (v * m))) (x : Fin (v * m * (v * m) + v * m * (v * m)) → R) :
    matMulFun (v * m) t x =
      ∑ ν, algebraMap K R (γ ((finProdFinEquiv.symm (finProdFinEquiv.symm t).1).1,
          (finProdFinEquiv.symm (finProdFinEquiv.symm t).2).1) ν) *
        blockProd α β ν (finProdFinEquiv ((finProdFinEquiv.symm (finProdFinEquiv.symm t).1).2,
          (finProdFinEquiv.symm (finProdFinEquiv.symm t).2).2)) x := by
  simp only [matMulFun, blockProd, entry, Equiv.symm_apply_apply]
  conv_lhs => rw [← finProdFinEquiv.apply_symm_apply (finProdFinEquiv.symm t).1,
    ← finProdFinEquiv.apply_symm_apply (finProdFinEquiv.symm t).2]
  exact mul_apply_eq_sum_encode hid _ _ _ _ _ _

/-- **The block step**: a circuit of size `s` for `m × m` matrices gives one of size
`r s + 9 r (v m) ^ 2 + 1` for `v m × v m` matrices: encode the `2 r` block inputs
(`6 r v ^ 2 m ^ 2` gates), compute the `r` block products with the given circuit, and decode the
`(v m) ^ 2` outputs (`3 r (v m) ^ 2` gates). -/
private theorem hasCircuit_mul {α β : Matrix (Fin r) (Fin v × Fin v) K}
    {γ : Matrix (Fin v × Fin v) (Fin r) K} (h : restrict α β γ (unit r) = mm v v v)
    {s : ℕ} (hm : HasCircuit (K := K) m s) :
    HasCircuit (K := K) (v * m) (r * s + 9 * r * (v * m) ^ 2 + 1) := by
  classical
  obtain ⟨C, hC, hs⟩ := hm
  refine exists_computesMatMul_of_synthesis (n := v * m) ?_
  have hid := encoders_spec (R := Poly K (v * m)) h
  -- the available functions after each stage
  set s₀ := inputs (v * m * (v * m) + v * m * (v * m)) (U := Poly K (v * m)) with hs₀
  set s₁ : Set ((Fin (v * m * (v * m) + v * m * (v * m)) → Poly K (v * m)) → Poly K (v * m)) :=
    {fun _ => 0} with hs₁
  set s₂ := Set.range fun p : Fin r × Fin (m * m + m * m) =>
    encInputs (R := Poly K (v * m)) α β p.1 p.2 with hs₂
  set s₃ := ⋃ ν, Set.range (blockProd (R := Poly K (v * m)) α β ν) with hs₃
  have S₀ : Synthesis (arithIn K (Poly K (v * m))) s₀ s₁ 1 := synthesis_zero
  have S₁ : Synthesis (arithIn K (Poly K (v * m))) (s₀ ∪ s₁) s₂
      (∑ _p : Fin r × Fin (m * m + m * m), ∑ _q : Fin v × Fin v, (2 + 1)) :=
    Synthesis.family _ _ fun p => synthesis_encInputs α β p.1 p.2
  have henc : ∀ ν i, encInputs α β ν i ∈ s₀ ∪ (s₁ ∪ s₂) := fun ν i =>
    Or.inr (Or.inr ⟨(ν, i), rfl⟩)
  have S₂ : Synthesis (arithIn K (Poly K (v * m))) (s₀ ∪ (s₁ ∪ s₂)) s₃ (∑ _ν : Fin r, C.size) :=
    Synthesis.iUnion _ _ fun ν => synthesis_blockProd ν hC (henc ν)
  have h0 : (fun _ => (0 : Poly K (v * m))) ∈ s₀ ∪ (s₁ ∪ s₂ ∪ s₃) := by simp [hs₁]
  have hbp : ∀ ν t, blockProd α β ν t ∈ s₀ ∪ (s₁ ∪ s₂ ∪ s₃) := fun ν t =>
    Or.inr (Or.inr (Set.mem_iUnion.2 ⟨ν, t, rfl⟩))
  have S₃ : Synthesis (arithIn K (Poly K (v * m))) (s₀ ∪ (s₁ ∪ s₂ ∪ s₃))
      (Set.range (matMulFun (v * m))) (∑ _t : Fin (v * m * (v * m)), ∑ _ν : Fin r, (2 + 1)) := by
    refine Synthesis.family _ _ fun t => ?_
    have := Synthesis.arith_sum (constant := algebraMap K (Poly K (v * m)))
      (Finset.univ : Finset (Fin r))
      (fun ν x => algebraMap K (Poly K (v * m)) (γ ((finProdFinEquiv.symm
          (finProdFinEquiv.symm t).1).1, (finProdFinEquiv.symm (finProdFinEquiv.symm t).2).1) ν) *
        blockProd α β ν (finProdFinEquiv ((finProdFinEquiv.symm (finProdFinEquiv.symm t).1).2,
          (finProdFinEquiv.symm (finProdFinEquiv.symm t).2).2)) x) (fun _ => 2) h0 fun ν _ =>
        synthesis_const_mul _ (hbp ν _)
    refine this.mono Set.Subset.rfl (Set.singleton_subset_iff.mpr ?_) le_rfl
    funext x
    exact matMulFun_eq_sum hid t x
  have := ((S₀.comp S₁).comp S₂).comp S₃
  refine this.mono Set.Subset.rfl Set.subset_union_right ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
  have := Nat.mul_le_mul_left r hs
  nlinarith

/-- Zero padding of a matrix to a larger side. -/
private def padMatrix {n : ℕ} (N : ℕ) (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin N) (Fin N) R :=
  Matrix.of fun i j => if h : i.val < n ∧ j.val < n then A ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

private theorem padMatrix_castLE {n N : ℕ} (hnN : n ≤ N) (A : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) : padMatrix N A (Fin.castLE hnN i) (Fin.castLE hnN j) = A i j := by
  rw [padMatrix, Matrix.of_apply, dite_eq_left ⟨i.isLt, j.isLt⟩]
  rfl

/-- The product of zero-padded matrices is the zero-padded product. -/
private theorem padMatrix_mul {n N : ℕ} (hnN : n ≤ N) (A B : Matrix (Fin n) (Fin n) R)
    (i k : Fin n) :
    (padMatrix N A * padMatrix N B) (Fin.castLE hnN i) (Fin.castLE hnN k) = (A * B) i k := by
  simp only [Matrix.mul_apply]
  symm
  calc ∑ j, A i j * B j k
      = ∑ j, padMatrix N A (Fin.castLE hnN i) (Fin.castLE hnN j) *
          padMatrix N B (Fin.castLE hnN j) (Fin.castLE hnN k) := by
        simp only [padMatrix_castLE]
    _ = ∑ j ∈ (Finset.univ : Finset (Fin n)).map (Fin.castLEEmb hnN),
          padMatrix N A (Fin.castLE hnN i) j * padMatrix N B j (Fin.castLE hnN k) := by
        rw [Finset.sum_map]
        rfl
    _ = ∑ j, padMatrix N A (Fin.castLE hnN i) j * padMatrix N B j (Fin.castLE hnN k) := by
        refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_
        have hjn : ¬ j.val < n := fun h => hj (Finset.mem_map.2 ⟨⟨j.val, h⟩, Finset.mem_univ _,
          Fin.ext rfl⟩)
        simp [padMatrix, hjn]

/-- **Padding**: a circuit for `N × N` matrices gives one for `n × n` matrices, `n ≤ N`, with one
more gate (the zero fed to the padding entries). -/
private theorem hasCircuit_of_le {n N s : ℕ} (hnN : n ≤ N) (hN : HasCircuit (K := K) N s) :
    HasCircuit (K := K) n (s + 1) := by
  classical
  obtain ⟨C, hC, hs⟩ := hN
  refine exists_computesMatMul_of_synthesis (n := n) ?_
  let g : Fin (N * N + N * N) → (Fin (n * n + n * n) → Poly K n) → Poly K n := fun i x =>
    matrixInputs (Poly K n) (padMatrix N (leftMatrix x)) (padMatrix N (rightMatrix x)) i
  have pad_mem (f : (Fin (n * n + n * n) → Poly K n) → Matrix (Fin n) (Fin n) (Poly K n))
      (hf : ∀ i j, (fun x => f x i j) ∈ inputs (n * n + n * n)) (i : Fin (N * N)) :
      (fun x => entry (Poly K n) (padMatrix N (f x)) i) ∈
        inputs (n * n + n * n) ∪ {fun _ => (0 : Poly K n)} := by
    by_cases h : (finProdFinEquiv.symm i).1.val < n ∧ (finProdFinEquiv.symm i).2.val < n
    · apply Set.mem_union_left
      simpa only [entry, padMatrix, Matrix.of_apply, dite_eq_left h] using hf ⟨_, h.1⟩ ⟨_, h.2⟩
    · apply Set.mem_union_right
      simp only [entry, padMatrix, Matrix.of_apply, dite_eq_right h, Set.mem_singleton_iff]
  have hg : ∀ i, g i ∈ inputs (n * n + n * n) ∪ {fun _ => (0 : Poly K n)} := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [g, matrixInputs, Fin.append_left] using
        pad_mem leftMatrix leftMatrix_mem_inputs i
    · simpa only [g, matrixInputs, Fin.append_right] using
        pad_mem rightMatrix rightMatrix_mem_inputs i
  have := synthesis_zero.comp (Synthesis.circuit (I := arithIn K (Poly K n)) C g hg)
  refine this.mono Set.Subset.rfl ?_ (by lia)
  rintro _ ⟨t, rfl⟩
  refine Set.mem_union_right _ ⟨finProdFinEquiv (Fin.castLE hnN (finProdFinEquiv.symm t).1,
    Fin.castLE hnN (finProdFinEquiv.symm t).2), ?_⟩
  funext x
  beta_reduce
  have h1 : (fun i => g i x) =
      matrixInputs (Poly K n) (padMatrix N (leftMatrix x)) (padMatrix N (rightMatrix x)) := rfl
  rw [h1, hC.eval_algebra]
  simp only [matMulFun, entry, Equiv.symm_apply_apply, padMatrix_mul]

end BlockRecursion

/-- **Block recursion** ([Strassen][Strassen1969]; [Pass][Pass2026], §4.3): a bilinear algorithm
with `r` multiplications for `v × v` matrices gives circuits of size `O(n ^ τ)` for every `n`,
when `r ≤ v ^ τ` and `2 < τ`. For every `ε > 0`, with `R = v ^ (τ + ε) > r`, the sizes `S j` of
the circuits for `v ^ j × v ^ j` matrices satisfy `S (j + 1) ≤ r S j + 9 r (v ^ (j + 1)) ^ 2 + 1`,
hence `S j ≤ C R ^ j`; a general `n` is padded to the next power of `v`, which is at most
`v n`. -/
theorem admissibleExponent_of_rank {v r : ℕ} (hv : 2 ≤ v) (hr : Rank r (mm v v v : Tensor K _ _ _))
    {τ : ℝ} (hτ : (r : ℝ) ≤ (v : ℝ) ^ τ) (h2 : 2 < τ) : AdmissibleExponent K τ := by
  classical
  obtain ⟨α, β, γ, hid⟩ := hr
  intro ε hε
  have hv1 : (1 : ℝ) < v := by exact_mod_cast hv
  set R : ℝ := (v : ℝ) ^ (τ + ε) with hR
  have hrR : (r : ℝ) < R :=
    hτ.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hv1 (by linarith))
  have hv2R : (v : ℝ) ^ 2 ≤ R := by
    rw [hR, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hv1.le (by push_cast; linarith)
  have hR1 : 1 ≤ R := le_trans (by nlinarith) hv2R
  have hR0 : 0 < R := by linarith
  have hRr : 0 < R - r := by linarith
  -- the constant of the recursion
  set Cc : ℝ := (9 * r + 1) * R / (R - r) + 3 with hCc
  have hCc3 : 3 ≤ Cc := le_add_of_nonneg_left (div_nonneg (by positivity) hRr.le)
  have hCc0 : 0 < Cc := by linarith
  have hCcR : (9 * r + 1) * R ≤ Cc * (R - r) := by
    rw [hCc, add_mul _ (3 : ℝ), div_mul_cancel₀ _ hRr.ne']
    linarith
  -- circuits for the powers of `v`
  have step : ∀ j : ℕ, ∃ s : ℕ, HasCircuit (K := K) (v ^ j) s ∧ (s : ℝ) ≤ Cc * R ^ j := by
    intro j
    induction j with
    | zero =>
      obtain ⟨C, hC, hCs⟩ := exists_circuit_trivial (K := K) 1
      refine ⟨3, HasCircuit.congr (pow_zero v).symm ⟨C, hC, hCs.trans (by norm_num)⟩, ?_⟩
      simpa using hCc3
    | succ j ih =>
      obtain ⟨s, hs, hsR⟩ := ih
      refine ⟨_, HasCircuit.congr (pow_succ' v j).symm (hasCircuit_mul hid hs), ?_⟩
      have h1 : ((v : ℝ) * (v : ℝ) ^ j) ^ 2 ≤ R ^ (j + 1) := by
        rw [show ((v : ℝ) * (v : ℝ) ^ j) ^ 2 = ((v : ℝ) ^ 2) ^ (j + 1) by ring]
        exact pow_le_pow_left₀ (by positivity) hv2R _
      have h2 : (1 : ℝ) ≤ R ^ (j + 1) := one_le_pow₀ hR1
      have h3 : (r : ℝ) * s ≤ r * (Cc * R ^ j) := by gcongr
      have h4 : 9 * (r : ℝ) * ((v : ℝ) * (v : ℝ) ^ j) ^ 2 ≤ 9 * r * R ^ (j + 1) := by gcongr
      have h5 : (r : ℝ) * (Cc * R ^ j) + (9 * r + 1) * R ^ (j + 1) ≤ Cc * R ^ (j + 1) := by
        have := mul_le_mul_of_nonneg_left hCcR (pow_nonneg hR0.le j)
        rw [pow_succ]
        nlinarith
      cast_nlinarith
  -- the general `n`: pad to the next power of `v`
  refine ⟨Cc * (v : ℝ) ^ (τ + ε) + 1, by positivity, fun n hn => ?_⟩
  set j := Nat.log v n + 1 with hj
  have hnj : n < v ^ j := Nat.lt_pow_succ_log_self (by omega) n
  have hjn : v ^ j ≤ v * n := by
    rw [hj, pow_succ']
    exact Nat.mul_le_mul_left v (Nat.pow_log_le_self v (by omega))
  obtain ⟨s, hs, hsR⟩ := step j
  obtain ⟨C, hC, hCs⟩ := hasCircuit_of_le hnj.le hs
  refine ⟨C, hC, ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ (τ + ε) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by linarith)
  have hRj : R ^ j = ((v ^ j : ℕ) : ℝ) ^ (τ + ε) := by
    rw [hR, ← Real.rpow_mul_natCast (by positivity), mul_comm,
      Real.rpow_natCast_mul (by positivity)]
    push_cast
    rfl
  have hle : ((v ^ j : ℕ) : ℝ) ^ (τ + ε) ≤ ((v * n : ℕ) : ℝ) ^ (τ + ε) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hjn) (by linarith)
  calc (C.size : ℝ) ≤ s + 1 := by exact_mod_cast hCs
    _ ≤ Cc * R ^ j + 1 := by linarith
    _ ≤ Cc * ((v * n : ℕ) : ℝ) ^ (τ + ε) + 1 := by
      rw [hRj]
      exact add_le_add (mul_le_mul_of_nonneg_left hle hCc0.le) le_rfl
    _ = Cc * (v : ℝ) ^ (τ + ε) * (n : ℝ) ^ (τ + ε) + 1 := by
      push_cast
      rw [Real.mul_rpow (by positivity) (by positivity)]
      ring
    _ ≤ (Cc * (v : ℝ) ^ (τ + ε) + 1) * (n : ℝ) ^ (τ + ε) := by
      have : 0 ≤ Cc * (v : ℝ) ^ (τ + ε) := by positivity
      nlinarith

end Cslib.Circuits.Arithmetic.MatrixMultiplication
