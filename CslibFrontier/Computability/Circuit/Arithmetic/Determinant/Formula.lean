/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.DeterminantalComplexity
public import CslibFrontier.Computability.Circuit.Formula
import CslibFrontier.Computability.Circuit.Arithmetic.Determinant.Projection

/-!
# Arithmetic formulas are projections of the determinant

Every arithmetic formula `F : Formula (arithSignature K) n` over a commutative ring `K` computes a
formal polynomial that is a projection of the generic determinant of dimension `F.size + 1`. Here
`size` counts every operation node, including constants, with input leaves free (`input i` has size
`0` and projects from the `1 × 1` generic determinant). Substitution uses `IsProjection`: each
matrix entry is a variable or a scalar, with no outer scalar multiplier on the result.

This is the determinant's formula-simulation property [Valiant, Theorem 1][Valiant1979Algebra;
Orzel et al., Definition 1 and Lemma 4][OrzelSrinivasanTavenasYehudayoff2025]. Valiant (§1–§2,
pp. 249–251) works over a field, counts binary ring operations (`+`, `×`), and states dimension
`|P_i| + 2`; Grenet, Kaltofen, Koiran and Portier (*Symmetric Determinantal Representation of
Formulas and Weakly Skew Circuits*, *Contemporary Mathematics* 556, 61–96, 2012, §1.2 and §2.1)
noted a parallel-edge issue in Valiant's equal-parity addition step and gave a digraph proof of Liu
and Regan's (2006) `e + 1` bound over fields of characteristic not two for green-size-`e` formulas
with at least one addition (with scalar multiplications free and the separate monomial case `e + 2`
in general, `e + 1` for monic products). Orzel et al. work over fields of characteristic other than
two and permit a nonzero scalar multiplier in projections. Neither restriction nor multiplier is
needed here: `IsSubstABP` uses a strictly upper-triangular specialization matrix with a unit
sink-bridge edge for addition (avoiding parallel edges) and `-1` along the subdiagonal of `N - 1`
to absorb cycle signs over every commutative ring `K`.

Consequently, the formal polynomial of `F` (both `F.eval (arithInterpretationWith K C) X` and
`F.toCircuit.polynomial 0`) has determinantal complexity at most `F.size + 1` unconditionally over
every commutative ring `K`.

## Main results

* `Cslib.Circuits.Formula.isProjection_det`: dimension `F.size + 1` suffices;
  `Cslib.Circuits.Formula.isProjection_det_toCircuit` states the same bound for
  `F.toCircuit.polynomial 0`.
* `Cslib.Circuits.Formula.determinantalComplexity_eval_le`,
  `Cslib.Circuits.Formula.determinantalComplexity_toCircuit_le`: the determinantal complexity of the
  polynomial computed by `F` is at most `F.size + 1`.

## References

* [L. G. Valiant, *Completeness classes in algebra*][Valiant1979Algebra], §1–§2, Theorem 1
  (pp. 249–251)
* [I. Orzel et al., *The Algebraic Cost of a Boolean Sum*][OrzelSrinivasanTavenasYehudayoff2025],
  Definition 1 (p. 47:3), Lemma 4 (p. 47:4) and projection conventions (p. 47:5)
* [R. Saptharishi, *A survey of lower bounds in arithmetic circuit
  complexity*][Saptharishi2026Survey], chapter "Algebraic complexity classes", Theorem `thm:vp` and
  Section `sec:formula-to-dets`
-/

public section

namespace Cslib.Circuits.Formula

open MvPolynomial Cslib.Circuits.Arithmetic

universe u

variable {K : Type u} [CommRing K] {n : ℕ}

/-- Every arithmetic formula `F` computes a polynomial with a specialization branching program of
size at most `F.size + 1`. -/
private theorem exists_isSubstABP (F : Formula (arithSignature K) n) :
    ∃ k ≤ F.size, IsSubstABP k (F.eval (arithInterpretationWith K C) X) := by
  induction F with
  | input i =>
    exact ⟨0, le_rfl, .of_isSubstEntry (.X i)⟩
  | gate op args ih =>
    cases op with
    | const c => exact ⟨0, Nat.zero_le _, .of_isSubstEntry (.C c)⟩
    | add | mul =>
      obtain ⟨k₀, h₀, hM₀⟩ := ih 0
      obtain ⟨k₁, h₁, hM₁⟩ := ih 1
      refine ⟨k₀ + k₁ + 1, by simp only [size_gate, Fin.sum_univ_two]; omega, ?_⟩
      first | exact hM₀.add hM₁ | exact hM₀.mul hM₁

/-- **Formula universality for the determinant**: over every commutative ring `K`, the formal
polynomial computed by an arithmetic formula `F` is a projection of the
`(F.size + 1) × (F.size + 1)` generic determinant
[Valiant][Valiant1979Algebra; Orzel et al., Lemma 4][OrzelSrinivasanTavenasYehudayoff2025].
`size` counts operation nodes, including constants, with input leaves free; the linear dimension
bound is proved directly by the branching-program construction. -/
theorem isProjection_det (F : Formula (arithSignature K) n) :
    IsProjection (F.eval (arithInterpretationWith K C) X)
      (genericMatrix K (F.size + 1)).det := by
  obtain ⟨k, hk, hF⟩ := F.exists_isSubstABP
  exact isProjection_det_mono (Nat.add_le_add_right hk 1) hF.isProjection_det

/-- The formal polynomial `F.toCircuit.polynomial 0` of any arithmetic formula `F` over a
commutative ring `K` is a projection of `(genericMatrix K (F.size + 1)).det`. -/
theorem isProjection_det_toCircuit (F : Formula (arithSignature K) n) :
    IsProjection (F.toCircuit.polynomial 0) (genericMatrix K (F.size + 1)).det := by
  simpa only [Circuit.polynomial, eval_toCircuit] using F.isProjection_det

/-- The formal polynomial computed by an arithmetic formula `F` over a commutative ring `K` has
determinantal complexity at most `F.size + 1`. -/
theorem determinantalComplexity_eval_le (F : Formula (arithSignature K) n) :
    determinantalComplexity (F.eval (arithInterpretationWith K C) X) ≤ F.size + 1 :=
  determinantalComplexity_le (hasDeterminantalRepresentation_of_isProjection F.isProjection_det)

/-- The formal polynomial `F.toCircuit.polynomial 0` of an arithmetic formula `F` over a
commutative ring `K` has determinantal complexity at most `F.size + 1`. -/
theorem determinantalComplexity_toCircuit_le (F : Formula (arithSignature K) n) :
    determinantalComplexity (F.toCircuit.polynomial 0) ≤ F.size + 1 :=
  determinantalComplexity_le
    (hasDeterminantalRepresentation_of_isProjection F.isProjection_det_toCircuit)

end Cslib.Circuits.Formula
