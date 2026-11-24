/-
Copyright (c) 2026 Richard Dodson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Dodson
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.SingularLearning.LearningCoefficient
public import CslibFrontier.MachineLearning.SingularLearning.ModularAddition.Fourier
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Tactic.Ring

/-!
# Open problem MAIS-O6: is the Fourier structure of modular addition forced?

A formal statement of open problem MAIS-O6 of [Levine2026, Section 5.1]:

> In a fixed closed ball containing one of these Fourier fits, prove or refute that every exact
> fit of smallest local learning coefficient has this single-frequency form, apart from neurons
> whose contribution vanishes identically.

**This module states the problem. It neither proves nor refutes it.** The proposition
`FourierStructureProblem p H` is the instance at `(p, H)`; the problem is the family of these
instances over odd `p ≥ 3` and `H ≥ 2 p - 1`. Each is a case of the parametrized proposition
`FourierStructureForced p H R`.

## Reading of the source

The source fixes the network, the exception for each neuron whose contribution vanishes
identically, the single-frequency form with one frequency for both tables of a neuron, a fixed
closed ball containing a Fourier fit, and that every exact fit of smallest coefficient in it is
to have the form. The problem's page in the source's repository names
[MAISA6, Conjecture 4.9] as its formalization. That document adds, and this module follows:

* the ball: the closed ball about the origin of radius `R_p = 1 + ‖w^F‖`, where `w^F` is the
  Fourier fit `fourierFit p` of [MAISA6, Lemma 4.2] and the norm is the Euclidean norm of the
  whole parameter vector;
* the range: odd `p ≥ 3` and `H ≥ 2 p - 1`;
* the frequencies `0 ≤ k ≤ (p - 1) / 2`, with `0` allowed (`IsSingleFrequency`);
* the name *active* for a neuron outside the exception (`IsActive`);
* the local learning coefficient at an exact fit is computed in the whole parameter space with
  Lebesgue measure, also at exact fits on the boundary of the ball; the ball restricts only
  which exact fits compete.

Since the exception is per neuron, the statement also covers exact fits in which a group of
active neurons has total contribution zero. For `H ≥ 2 p + 1` such fits exist in the ball: add
to the Fourier fit two neurons with the same tables and opposite nonzero output vectors, small
enough to stay within the radius. The statement asserts that no such fit attains the smallest
coefficient unless those neurons have single-frequency form.

## Deviation from the sources

The local learning coefficient is `Cslib.MachineLearning.learningCoeff`, a volume exponent that
is defined for every function. [MAISA6, Definition 2.5] defines it through the largest pole of a
zeta function, equivalently through the asymptotic form of the sublevel volume. For the
polynomial loss of this problem the definitions agree by the theory of [Watanabe2009], which
rests on resolution of singularities; that agreement is not proved in this library.

## Main definitions

* `Cslib.MachineLearning.ModularAddition.fourierRadius`: the radius `R_p`.
* `Cslib.MachineLearning.ModularAddition.exactFitsInBall`: the exact fits in a closed ball.
* `Cslib.MachineLearning.ModularAddition.FourierStructureForced`: the statement for a given
  width and radius.
* `Cslib.MachineLearning.ModularAddition.FourierStructureProblem`: the statement at the radius
  `R_p`. It is the instance at `(p, H)` of the problem, which is posed for odd `p ≥ 3` and
  `H ≥ 2 p - 1`.

## Main results

* `Cslib.MachineLearning.ModularAddition.exists_isMinOn_exactFitsInBall`: for odd `p` and
  `H ≥ 2 p - 1` the ball contains an exact fit of smallest coefficient, so the statement
  constrains at least one parameter.
* `Cslib.MachineLearning.ModularAddition.not_fourierStructureForced_of_isMinOn`: the direct
  form of a refutation, an exact fit of smallest coefficient with an active neuron not of
  single-frequency form.
* `Cslib.MachineLearning.ModularAddition.not_fourierStructureForced`: one sufficient test for a
  refutation, by strict separation of an upper bound at one exact fit from a lower bound at the
  exact fits of single-frequency form.

## The degenerate case `p = 3`

`fourierStructureForced_three` and `fourierStructureProblem_three` are not results about the
problem. For `p = 3` every table on `ℤ/3` is a constant plus a combination of `cos (2π · / 3)`
and `sin (2π · / 3)`, so every neuron has single-frequency form and the statement holds for
every width and radius without any information about learning coefficients. This degenerate
case is why both sources start at `p = 5` with nine neurons, the first non-vacuous case. In this
library it serves as a check that the definitions behave as intended there.

## References

* [L. Levine, *Math for AI safety: an invitation for mathematicians*, Section 5.1][Levine2026]
* [*Does geometric simplicity force a legible mechanism? Singular geometry of modular
  addition*, agenda MAIS-A6, Section 4][MAISA6]
* [S. Watanabe, *Algebraic Geometry and Statistical Learning Theory*][Watanabe2009]
-/

public section

namespace Cslib.MachineLearning.ModularAddition

open scoped Real
open MeasureTheory

variable {p : ℕ} [NeZero p] {ι : Type} [Fintype ι]

/-! ### The exact fits in a ball -/

/-- The radius `R_p = 1 + ‖w^F‖` of [MAISA6, Section 4], where `w^F` is the Fourier fit at
width `2 p - 1`; the source of the radius is for odd `p ≥ 3`. Padding does not change the norm,
so this is also `1 + ‖w^F_H‖` for the padded fit at any width `H ≥ 2 p - 1`. -/
@[expose] noncomputable def fourierRadius (p : ℕ) [NeZero p] : ℝ := 1 + ‖fourierFit p‖

/-- The exact fits of width `H` in the closed ball of radius `R` about the origin. -/
@[expose] def exactFitsInBall (p H : ℕ) [NeZero p] (R : ℝ) : Set (Params p (Fin H)) :=
  {w | IsExactFit w ∧ ‖w‖ ≤ R}

omit [NeZero p] in
private theorem continuous_net (a b c : ZMod p) :
    Continuous fun w : Params p ι => net w a b c := by
  have hcoord : ∀ x : ι × Fin 3 × ZMod p, Continuous fun w : Params p ι => w x := fun x =>
    (EuclideanSpace.proj (𝕜 := ℝ) x).continuous
  exact continuous_finsetSum _ fun j _ =>
    (hcoord (j, 2, c)).mul (((hcoord (j, 0, a)).add (hcoord (j, 1, b))).pow 2)

omit [NeZero p] in
/-- The exact fits form a closed set. -/
theorem isClosed_setOf_isExactFit : IsClosed {w : Params p ι | IsExactFit w} := by
  simp only [IsExactFit, Set.ofPred_forall]
  exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun c =>
    isClosed_eq (continuous_net a b c) continuous_const

/-- The exact fits in a closed ball form a compact set. -/
theorem isCompact_exactFitsInBall (p H : ℕ) [NeZero p] (R : ℝ) :
    IsCompact (exactFitsInBall p H R) := by
  have heq : exactFitsInBall p H R =
      {w : Params p (Fin H) | IsExactFit w} ∩ Metric.closedBall 0 R := by
    ext w
    simp [exactFitsInBall]
  rw [heq]
  exact (isCompact_closedBall 0 R).inter_left isClosed_setOf_isExactFit

/-- For odd `p` and `H ≥ 2 p - 1`, the Fourier fit padded to width `H` is an exact fit in the
ball of radius `R_p`. -/
theorem exactFitsInBall_fourierRadius_nonempty (hp : Odd p) {H : ℕ} (hH : 2 * p - 1 ≤ H) :
    (exactFitsInBall p H (fourierRadius p)).Nonempty := by
  have hcard : Fintype.card (FourierIndex p) ≤ H := (card_fourierIndex hp).le.trans hH
  let e : FourierIndex p ↪ Fin H :=
    (Fintype.equivFin (FourierIndex p)).toEmbedding.trans (Fin.castLEEmb hcard)
  refine ⟨extend e (fourierFit p), (isExactFit_extend e _).2 (isExactFit_fourierFit hp), ?_⟩
  rw [norm_extend, fourierRadius]
  linarith

/-! ### The statement -/

/-- **The statement of open problem MAIS-O6 for width `H` and radius `R`**
([Levine2026, Section 5.1], in the form of [MAISA6, Conjecture 4.9]): every exact fit in the
closed ball of radius `R` about the origin whose local learning coefficient is smallest among
the exact fits in that ball has all of its active neurons of single-frequency form.

This is a proposition, not a theorem. [Levine2026, Section 5.1] asks for a fixed closed ball
containing a Fourier fit. [MAISA6] fixes `R = R_p` (`FourierStructureProblem`) and treats the
conclusion for every `R ≥ R_p` simultaneously as a stronger extension. The local learning
coefficient is `Cslib.MachineLearning.learningCoeff` of the loss, a volume exponent; see the
module docstring for how this relates to the sources. -/
@[expose] def FourierStructureForced (p H : ℕ) [NeZero p] (R : ℝ) : Prop :=
  ∀ w ∈ exactFitsInBall p H R, IsMinOn (learningCoeff loss) (exactFitsInBall p H R) w →
    ∀ j, IsActive w j → IsSingleFrequency w j

/-- **The instance at `(p, H)` of open problem MAIS-O6** of [Levine2026, Section 5.1], in the
form of [MAISA6, Conjecture 4.9]: every exact fit of width `H` in the closed ball of radius
`R_p = 1 + ‖w^F‖` whose local learning coefficient is smallest among the exact fits in that ball
has all of its active neurons of single-frequency form. The conjecture is the family of these
instances over odd `p ≥ 3` and `H ≥ 2 p - 1`.

This is the statement of an open problem, not a theorem. The definition requires a nonzero
modulus; oddness, `p ≥ 3` and the width bound are conditions on its use as MAIS-O6. Outside
that range the proposition has no source meaning: for `p = 1` it is trivially true, and for
even `p` the parameter `fourierFit p` is not an exact fit, so the radius is not that of a
Fourier fit. As of 2026-11-24 the source lists the problem as open; a numerical counterexample
at `p = 5`, `H = 9` has been reported on the problem's repository and is not certified
(issue 21); this library neither proves nor refutes the statement. -/
@[expose] def FourierStructureProblem (p H : ℕ) [NeZero p] : Prop :=
  FourierStructureForced p H (fourierRadius p)

/-- **A minimizer exists.** For odd `p` and `H ≥ 2 p - 1` the ball of radius `R_p` contains an
exact fit whose local learning coefficient is smallest among the exact fits in the ball: the set
of those exact fits is compact, it contains the padded Fourier fit, and the coefficient is
lower semicontinuous. So `FourierStructureProblem p H` constrains at least one parameter.

This is not the statement that the structural condition can fail. For `p = 3` a minimizer
exists and the condition holds at every parameter (`fourierStructureForced_three`). -/
theorem exists_isMinOn_exactFitsInBall (hp : Odd p) {H : ℕ} (hH : 2 * p - 1 ≤ H) :
    ∃ w ∈ exactFitsInBall p H (fourierRadius p),
      IsMinOn (learningCoeff loss) (exactFitsInBall p H (fourierRadius p)) w :=
  exists_isMinOn_learningCoeff loss (isCompact_exactFitsInBall p H _)
    (exactFitsInBall_fourierRadius_nonempty hp hH)

/-- **A refutation, in direct form.** The statement for a width and a radius fails as soon as
some exact fit in the ball that attains the smallest local learning coefficient has an active
neuron that is not of single-frequency form. This is the negation of the statement read off,
and it also covers the case in which fits of single-frequency form attain the same smallest
value. -/
theorem not_fourierStructureForced_of_isMinOn {H : ℕ} {R : ℝ} {w : Params p (Fin H)}
    (hw : w ∈ exactFitsInBall p H R)
    (hmin : IsMinOn (learningCoeff loss) (exactFitsInBall p H R) w)
    {j : Fin H} (hj : IsActive w j) (hns : ¬ IsSingleFrequency w j) :
    ¬ FourierStructureForced p H R :=
  fun hforced => hns (hforced w hw hmin j hj)

/-- **One sufficient test for a refutation, by strict separation.** To refute the statement for
a width and a radius it is enough to give an exact fit `w` in the ball with an active neuron
that is not of single-frequency form, a bound `c` with `λ(w) ≤ c`, and the bound `c < λ(v)` for
every exact fit `v` in the ball all of whose active neurons have single-frequency form. A
smallest coefficient is attained in the ball, and under these bounds it is not attained at a fit
of single-frequency form.

The test cannot express a tie at the minimum between `w` and a fit of single-frequency form;
`not_fourierStructureForced_of_isMinOn` covers that case. Nothing in this library supplies such
bounds. -/
theorem not_fourierStructureForced {H : ℕ} {R : ℝ} {w : Params p (Fin H)} {c : EReal}
    (hw : w ∈ exactFitsInBall p H R) {j : Fin H} (hj : IsActive w j)
    (hns : ¬ IsSingleFrequency w j) (hupper : learningCoeff loss w ≤ c)
    (hlower : ∀ v ∈ exactFitsInBall p H R,
      (∀ i, IsActive v i → IsSingleFrequency v i) → c < learningCoeff loss v) :
    ¬ FourierStructureForced p H R := by
  intro hforced
  obtain ⟨v, hv, hmin⟩ :=
    exists_isMinOn_learningCoeff loss (isCompact_exactFitsInBall p H R) ⟨w, hw⟩
  by_cases hvw : learningCoeff loss v = learningCoeff loss w
  · -- Then `w` is a minimizer too, and its active neuron contradicts the statement.
    have hminw : IsMinOn (learningCoeff loss) (exactFitsInBall p H R) w := fun u hu => by
      rw [Set.mem_ofPred_eq, ← hvw]
      exact hmin hu
    exact hns (hforced w hw hminw j hj)
  · exact absurd ((hlower v hv (hforced v hv hmin)).trans_le ((hmin hw).trans hupper))
      (lt_irrefl _)

/-! ### The case `p = 3` -/

omit [NeZero p] in
/-- If the tables of frequency `1` are all tables, then every neuron has single-frequency form
and the statement holds for every width and every radius. -/
theorem fourierStructureForced_of_freqSpace_eq_top [NeZero p] (h : freqSpace p 1 = ⊤) (H : ℕ)
    (R : ℝ) : FourierStructureForced p H R :=
  fun _ _ _ _ _ => ⟨1, h ▸ Submodule.mem_top, h ▸ Submodule.mem_top⟩

/-- For `p = 3` the functions `1`, `cos (2π · / 3)` and `sin (2π · / 3)` span all tables. -/
theorem freqSpace_three : freqSpace 3 1 = ⊤ := by
  have e1 : (2 * π * ((1 : ℕ) : ℝ) * ((1 : ZMod 3).val : ℝ) / ((3 : ℕ) : ℝ)) = π - π / 3 := by
    rw [show (1 : ZMod 3).val = 1 from rfl]
    push_cast
    ring
  have e2 : (2 * π * ((1 : ℕ) : ℝ) * ((2 : ZMod 3).val : ℝ) / ((3 : ℕ) : ℝ)) = π / 3 + π := by
    rw [show (2 : ZMod 3).val = 2 from rfl]
    push_cast
    ring
  have hc0 : cosTable 3 1 0 = 1 := by simp [cosTable]
  have hs0 : sinTable 3 1 0 = 0 := by simp [sinTable]
  have hc1 : cosTable 3 1 1 = -(1 / 2) := by
    rw [cosTable, e1, Real.cos_pi_sub, Real.cos_pi_div_three]
  have hs1 : sinTable 3 1 1 = Real.sqrt 3 / 2 := by
    rw [sinTable, e1, Real.sin_pi_sub, Real.sin_pi_div_three]
  have hc2 : cosTable 3 1 2 = -(1 / 2) := by
    rw [cosTable, e2, Real.cos_add_pi, Real.cos_pi_div_three]
  have hs2 : sinTable 3 1 2 = -(Real.sqrt 3 / 2) := by
    rw [sinTable, e2, Real.sin_add_pi, Real.sin_pi_div_three]
  have h3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  refine (Submodule.eq_top_iff').2 fun f => ?_
  have hf : f = ((f 0 + f 1 + f 2) / 3) • (fun _ : ZMod 3 => (1 : ℝ)) +
      ((2 * f 0 - f 1 - f 2) / 3) • cosTable 3 1 + ((f 1 - f 2) / Real.sqrt 3) • sinTable 3 1 := by
    funext a
    obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by
      revert a
      decide
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc0, hs0]
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc1, hs1]
      field_simp
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc2, hs2]
      field_simp
      ring
  rw [hf]
  exact Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (one_mem_freqSpace 3 1))
    (Submodule.smul_mem _ _ (cosTable_mem_freqSpace 3 1)))
    (Submodule.smul_mem _ _ (sinTable_mem_freqSpace 3 1))

/-- The degenerate case `p = 3`. Every table on `ℤ/3` is a constant plus a combination of
`cos (2π · / 3)` and `sin (2π · / 3)`, so every neuron has single-frequency form and the
statement holds for every width and every radius, without any information about learning
coefficients. Both sources name `p = 5` with nine neurons as the first non-vacuous case;
[MAISA6] gives this reason. -/
theorem fourierStructureForced_three (H : ℕ) (R : ℝ) : FourierStructureForced 3 H R :=
  fourierStructureForced_of_freqSpace_eq_top freqSpace_three H R

/-- The degenerate case `p = 3` of `FourierStructureProblem`; see `fourierStructureForced_three`. -/
theorem fourierStructureProblem_three (H : ℕ) : FourierStructureProblem 3 H :=
  fourierStructureForced_three H _

end Cslib.MachineLearning.ModularAddition
