/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.SpanProgram.ChangeOfBasis
public import CslibFrontier.Foundations.LinearAlgebra.LinearSolve
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# The algorithm `Lin` and the program `P_L` by elimination

[Boneh and Shoup, Theorem 22.14, p. 981][BonehShoup2023] states two algorithms for a monotone span
program `P` whose parties are `1, …, N`. For an accepted coalition `s`, `Lin(s)` returns vectors
`λ_j` with `∑_{j ∈ s} λ_j M_j = e₁`. For a coalition that is not accepted, `P_L` is a program that
accepts the same coalitions and has left-most column zero in the matrix of every member of `s`.
Both are computed here by one run of elimination on the stacked rows of the members
(`Cslib.LinearAlgebra.vecMulSolve` and `Cslib.LinearAlgebra.kernelVecAt`). The theorem also says
that `Lin` is efficient and that `P_L` is efficiently computable. The results here concern their
values; they are steps toward Theorem 22.14, not the theorem (#5293).

The book proves part (b) by extending a basis of the row space of the coalition. Here `P_L` is
`P` multiplied on the right by the identity matrix whose first column is a kernel vector `v` of
the members' rows with `v₁ = 1`. That matrix is invertible with top row `e₁`, so Lemma 22.15
applies, and it keeps columns `2, …, d` of every matrix unchanged. `shearMatrix` lives in the
span-program namespace because `normalForm` is its only client; it moves to
`Foundations/LinearAlgebra/Matrix/` when a second client appears.

The three algorithms are total. Outside their domains they return what elimination returns:
`recombination_eq_zero_of_not_accepts`, `nullVector_eq_zero_of_accepts` and
`not_accepts_normalForm_of_accepts`. The circuit-size bounds, one field-gate circuit for each
shape of program, are in `CslibFrontier.Computability.Circuit.SpanProgram.EliminationSynthesis`;
the identities of Theorem 22.14 for the shares and the secret are in
`CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.LinearEquivalence`.

## Main definitions

* `Cslib.Circuits.MonotoneSpanProgram.stack`: the rows of the members, stacked.
* `Cslib.Circuits.MonotoneSpanProgram.recombination`: the algorithm `Lin`.
* `Cslib.Circuits.MonotoneSpanProgram.nullVector`: a kernel vector of the members' rows.
* `Cslib.Circuits.MonotoneSpanProgram.shearMatrix`: the identity with its first column replaced.
* `Cslib.Circuits.MonotoneSpanProgram.normalForm`: the program `P_L`.

## Main results

* `Cslib.Circuits.MonotoneSpanProgram.sum_vecMul_recombination`: for an accepted coalition the
  vectors of `Lin` combine the members' rows to `e₁`.
* `Cslib.Circuits.MonotoneSpanProgram.nullVector_zero_eq_one_iff`: the kernel vector has first
  entry one exactly when the coalition is not accepted.
* `Cslib.Circuits.MonotoneSpanProgram.normalForm_matrix_zero`: the zero column of
  Theorem 22.14(b)(ii), a step toward that theorem.
* `Cslib.Circuits.MonotoneSpanProgram.accepts_normalForm`: for a coalition that is not accepted,
  `P_L` accepts the same coalitions as `P`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Theorem 22.14, p. 981.
-/

public section

open scoped Matrix

namespace Cslib.Circuits

namespace MonotoneSpanProgram

variable {F : Type*} [Field F] {N : ℕ}

/-- The rows of the matrices of the members of `s`, stacked in the order of the parties; the
rows of the other parties are replaced by zero. -/
@[expose] def stack (P : MonotoneSpanProgram F (Fin N)) (s : Finset (Fin N)) :
    Matrix (Fin (∑ i, P.rowDim i)) (Fin (P.tailDim + 1)) F :=
  fun k => if (finSigmaFinEquiv.symm k).1 ∈ s then
    P.matrix (finSigmaFinEquiv.symm k).1 (finSigmaFinEquiv.symm k).2 else 0

theorem stack_apply (P : MonotoneSpanProgram F (Fin N)) (s : Finset (Fin N)) (i : Fin N)
    (row : Fin (P.rowDim i)) :
    P.stack s (finSigmaFinEquiv ⟨i, row⟩) = if i ∈ s then P.matrix i row else 0 := by
  have h : finSigmaFinEquiv.symm (finSigmaFinEquiv (⟨i, row⟩ : (i : Fin N) × Fin (P.rowDim i))) =
      ⟨i, row⟩ := Equiv.symm_apply_apply _ _
  simp only [stack]
  rw [h]

theorem vecMul_stack (P : MonotoneSpanProgram F (Fin N)) (s : Finset (Fin N))
    (W : Fin (∑ i, P.rowDim i) → F) :
    W ᵥ* P.stack s = ∑ i ∈ s, (fun row => W (finSigmaFinEquiv ⟨i, row⟩)) ᵥ* P.matrix i := by
  rw [Matrix.vecMul_eq_sum, ← finSigmaFinEquiv.sum_comp, Fintype.sum_sigma]
  simp_rw [stack_apply]
  rw [← Finset.sum_subset (Finset.subset_univ s)]
  · exact Finset.sum_congr rfl fun i hi => by simp [hi, Matrix.vecMul_eq_sum]
  · intro i _ hi
    simp [hi]

theorem stack_mulVec_eq_zero_iff (P : MonotoneSpanProgram F (Fin N)) (s : Finset (Fin N))
    (v : Fin (P.tailDim + 1) → F) :
    P.stack s *ᵥ v = 0 ↔ ∀ i ∈ s, P.matrix i *ᵥ v = 0 := by
  have key : ∀ (i : Fin N) (row : Fin (P.rowDim i)),
      (P.stack s *ᵥ v) (finSigmaFinEquiv ⟨i, row⟩) =
        if i ∈ s then (P.matrix i *ᵥ v) row else 0 := by
    intro i row
    simp only [Matrix.mulVec, stack_apply]
    split_ifs <;> simp
  constructor
  · intro h i hi
    funext row
    have := congrFun h (finSigmaFinEquiv ⟨i, row⟩)
    rwa [key, ite_eq_left hi] at this
  · intro h
    funext k
    obtain ⟨⟨i, row⟩, rfl⟩ := finSigmaFinEquiv.surjective k
    rw [key]
    split_ifs with hi
    · exact congrFun (h i hi) row
    · rfl

/-- The identity matrix with its first column replaced by `v`. For `v 0 = 1` it is invertible
with top row `e₁`; multiplying a matrix `M` by it on the right replaces the first column of `M`
by `M *ᵥ v` and keeps the other columns. -/
@[expose] def shearMatrix {d : ℕ} (v : Fin (d + 1) → F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F :=
  (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) F).updateCol 0 v

theorem det_shearMatrix {d : ℕ} (v : Fin (d + 1) → F) : (shearMatrix v).det = v 0 := by
  rw [shearMatrix, ← Matrix.cramer_apply, Matrix.cramer_one]
  rfl

theorem shearMatrix_zero {d : ℕ} {v : Fin (d + 1) → F} (hv : v 0 = 1) :
    shearMatrix v 0 = Pi.single 0 1 := by
  funext c
  refine Fin.cases ?_ (fun c => ?_) c
  · simp [shearMatrix, hv]
  · simp [shearMatrix, (Fin.succ_ne_zero c).symm]

/-- Multiplying by `shearMatrix v` replaces the first column by the product with `v`. -/
theorem mulRight_shearMatrix_matrix_zero {Party : Type*} (P : MonotoneSpanProgram F Party)
    (v : Fin (P.tailDim + 1) → F) (i : Party) (row : Fin (P.rowDim i)) :
    (P.mulRight (shearMatrix v)).matrix i row 0 = (P.matrix i *ᵥ v) row := by
  change (P.matrix i * shearMatrix v) row 0 = _
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, shearMatrix]

variable [DecidableEq F]

/-- **Algorithm `Lin`** ([BonehShoup2023], Theorem 22.14(a), p. 981): recombination vectors for
the coalition `s`, by elimination on the stacked rows. Party `i` gets the vector
`P.recombination s i`. The rows of a party outside `s` are zero in `stack`, and its vector does
not enter `sum_vecMul_recombination`. When `s` is not accepted, elimination finds no solution
and returns the zero vector for every party (`recombination_eq_zero_of_not_accepts`). -/
@[expose] def recombination (P : MonotoneSpanProgram F (Fin N)) (s : Finset (Fin N)) (i : Fin N) :
    Fin (P.rowDim i) → F :=
  fun row => Cslib.LinearAlgebra.vecMulSolve (P.stack s) P.target (finSigmaFinEquiv ⟨i, row⟩)

/-- For an accepted coalition, the vectors of `recombination` combine the rows of the members to
the target `e₁`. -/
theorem sum_vecMul_recombination (P : MonotoneSpanProgram F (Fin N)) {s : Finset (Fin N)}
    (hs : P.Accepts s) : ∑ i : s, P.recombination s i.1 ᵥ* P.matrix i.1 = P.target := by
  rw [Finset.sum_coe_sort s fun i => P.recombination s i ᵥ* P.matrix i]
  have h := vecMul_stack P s (Cslib.LinearAlgebra.vecMulSolve (P.stack s) P.target)
  rw [show (∑ i ∈ s, P.recombination s i ᵥ* P.matrix i) = _ from h.symm]
  refine Cslib.LinearAlgebra.vecMul_vecMulSolve _ _ ?_
  obtain ⟨w, hw⟩ := (P.accepts_iff_exists_vecMul s).1 hs
  let W' : ((i : Fin N) × Fin (P.rowDim i)) → F := fun p =>
    if h : p.1 ∈ s then w ⟨p.1, h⟩ p.2 else 0
  refine ⟨fun k => W' (finSigmaFinEquiv.symm k), ?_⟩
  rw [vecMul_stack, ← hw, ← Finset.sum_coe_sort s]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  funext row
  rw [Equiv.symm_apply_apply]
  exact dite_eq_left i.2

/-- On a coalition that is not accepted, `recombination` gives every party the zero vector. -/
theorem recombination_eq_zero_of_not_accepts (P : MonotoneSpanProgram F (Fin N))
    {s : Finset (Fin N)} (hs : ¬ P.Accepts s) (i : Fin N) : P.recombination s i = 0 := by
  have h : Cslib.LinearAlgebra.vecMulSolve (P.stack s) P.target = 0 := by
    refine Cslib.LinearAlgebra.vecMulSolve_eq_zero _ _ fun ⟨W, hW⟩ => hs ?_
    refine (P.accepts_iff_exists_vecMul s).2 ⟨fun i row => W (finSigmaFinEquiv ⟨i.1, row⟩), ?_⟩
    rw [Finset.sum_coe_sort s fun i => (fun row => W (finSigmaFinEquiv ⟨i, row⟩)) ᵥ* P.matrix i,
      ← vecMul_stack, hW]
  funext row
  exact congrFun h _

/-- A kernel vector of the matrices of the members of `s` with first entry one, by elimination.
It exists exactly when `s` is not accepted (`nullVector_zero_eq_one_iff`); when `s` is accepted,
elimination returns the zero vector (`nullVector_eq_zero_of_accepts`). -/
@[expose] def nullVector (P : MonotoneSpanProgram F (Fin N)) (s : Finset (Fin N)) :
    Fin (P.tailDim + 1) → F :=
  Cslib.LinearAlgebra.kernelVecAt (P.stack s) 0

theorem matrix_mulVec_nullVector (P : MonotoneSpanProgram F (Fin N)) {s : Finset (Fin N)}
    {i : Fin N} (hi : i ∈ s) : P.matrix i *ᵥ P.nullVector s = 0 :=
  (P.stack_mulVec_eq_zero_iff s _).1 (Cslib.LinearAlgebra.mulVec_kernelVecAt _ _) i hi

/-- The first entry of `nullVector` is one exactly on the coalitions that are not accepted. -/
theorem nullVector_zero_eq_one_iff (P : MonotoneSpanProgram F (Fin N)) (s : Finset (Fin N)) :
    P.nullVector s 0 = 1 ↔ ¬ P.Accepts s := by
  refine ⟨fun h => P.not_accepts_of_exists_nullVector _ h fun _ => P.matrix_mulVec_nullVector,
    fun hs => ?_⟩
  obtain ⟨v, hv0, hv⟩ := P.exists_nullVector_of_not_accepts hs
  exact (Cslib.LinearAlgebra.kernelVecAt_apply_self_eq_one_iff _ _).2
    ⟨v, (P.stack_mulVec_eq_zero_iff s v).2 hv, hv0 ▸ one_ne_zero⟩

/-- On an accepted coalition, `nullVector` is the zero vector. -/
theorem nullVector_eq_zero_of_accepts (P : MonotoneSpanProgram F (Fin N)) {s : Finset (Fin N)}
    (hs : P.Accepts s) : P.nullVector s = 0 := by
  refine Cslib.LinearAlgebra.kernelVecAt_eq_zero _ _ fun v hv => by_contra fun hv0 => ?_
  refine P.not_accepts_of_exists_nullVector ((v 0)⁻¹ • v) (by simp [hv0]) (fun i hi => ?_) hs
  rw [Matrix.mulVec_smul, (P.stack_mulVec_eq_zero_iff s v).1 hv i hi, smul_zero]

/-- For a coalition that is not accepted, `shearMatrix (P.nullVector s)` satisfies the two
hypotheses of Lemma 22.15: it is invertible and its top row is `e₁`. -/
theorem shearMatrix_nullVector_of_not_accepts (P : MonotoneSpanProgram F (Fin N))
    {s : Finset (Fin N)} (hs : ¬ P.Accepts s) :
    IsUnit (shearMatrix (P.nullVector s)).det ∧
      shearMatrix (P.nullVector s) 0 = Pi.single 0 1 := by
  have hv := (P.nullVector_zero_eq_one_iff s).2 hs
  exact ⟨by rw [det_shearMatrix, hv]; exact isUnit_one, shearMatrix_zero hv⟩

/-- **The program `P_L`** ([BonehShoup2023], Theorem 22.14(b), p. 981): the matrices of `P`
multiplied on the right by the identity matrix with first column `P.nullVector s`. For an
accepted `s` the kernel vector is zero, so every matrix of `P.normalForm s` has first column
zero, for members and non-members alike, and the program accepts no coalition
(`not_accepts_normalForm_of_accepts`). -/
@[expose] def normalForm (P : MonotoneSpanProgram F (Fin N)) (s : Finset (Fin N)) :
    MonotoneSpanProgram F (Fin N) :=
  P.mulRight (shearMatrix (P.nullVector s))

/-- The zero column of Theorem 22.14(b)(ii), a step toward [BonehShoup2023], Theorem 22.14
(p. 981), not that theorem: in `P.normalForm s`, the left-most column of the matrix of every
member of `s` is zero. This holds for every `s`. Theorem 22.14(b) also says that `P_L` is
efficiently computable; the only bound is `Cslib.Circuits.Synthesis.full_normalForm`, one
field-gate circuit for each shape of program (#5293). -/
theorem normalForm_matrix_zero (P : MonotoneSpanProgram F (Fin N)) {s : Finset (Fin N)}
    {i : Fin N} (hi : i ∈ s) (row : Fin (P.rowDim i)) :
    (P.normalForm s).matrix i row 0 = 0 := by
  change (P.mulRight (shearMatrix (P.nullVector s))).matrix i row 0 = 0
  rw [mulRight_shearMatrix_matrix_zero, P.matrix_mulVec_nullVector hi]
  rfl

/-- The other columns are those of `P`. -/
theorem normalForm_matrix_succ (P : MonotoneSpanProgram F (Fin N)) (s : Finset (Fin N))
    (i : Fin N) (row : Fin (P.rowDim i)) (c : Fin P.tailDim) :
    (P.normalForm s).matrix i row c.succ = P.matrix i row c.succ := by
  change (P.matrix i * shearMatrix (P.nullVector s)) row c.succ = _
  simp [Matrix.mul_apply, shearMatrix, Matrix.one_apply, Fin.succ_ne_zero]

/-- For a coalition `s` that is not accepted, `P.normalForm s` accepts the same coalitions as
`P`. -/
theorem accepts_normalForm (P : MonotoneSpanProgram F (Fin N)) {s : Finset (Fin N)}
    (hs : ¬ P.Accepts s) (t : Finset (Fin N)) : (P.normalForm s).Accepts t ↔ P.Accepts t :=
  P.accepts_mulRight (P.shearMatrix_nullVector_of_not_accepts hs).1
    (P.shearMatrix_nullVector_of_not_accepts hs).2 t

/-- For an accepted coalition `s`, every matrix of `P.normalForm s` has first column zero, so the
program accepts no coalition. -/
theorem not_accepts_normalForm_of_accepts (P : MonotoneSpanProgram F (Fin N))
    {s : Finset (Fin N)} (hs : P.Accepts s) (t : Finset (Fin N)) :
    ¬ (P.normalForm s).Accepts t := by
  rw [normalForm, P.nullVector_eq_zero_of_accepts hs]
  refine not_accepts_of_exists_nullVector _ (Pi.single 0 1) (by simp) fun i _ => ?_
  rw [Matrix.mulVec_single_one]
  exact funext fun row => (mulRight_shearMatrix_matrix_zero P 0 i row).trans
    (congrFun (Matrix.mulVec_zero _) row)

end MonotoneSpanProgram

end Cslib.Circuits
