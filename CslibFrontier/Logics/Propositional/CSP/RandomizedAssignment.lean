/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP
public import CslibFrontier.Foundations.BooleanAnalysis.MeanWeight

/-!
# The value of an assignment and of a randomized assignment

The *value* of an assignment `σ : V → D` for a CSP instance `F`, read as a list (multiset) of
constraints, is the fraction of the constraints of `F` that `σ` satisfies
(`Logic.PL.CSP.satFraction`) [O'Donnell, Definition 7.26][ODonnell2014]; it is also the
probability that the tester which checks a uniformly random constraint of `F` accepts `σ`.

Over the Boolean domain, a *randomized assignment* labels each variable `v` with a random sign of
mean `g v ∈ [-1, 1]`, so `true`, the sign `-1`, with probability `(1 - g v) / 2`. A constraint is
satisfied with the probability that its relation holds at independent random bits with the means
`g` of the variables of its scope (`Logic.PL.Constraint.satProb`), position by position, so a
variable that is repeated in a scope is drawn afresh at each position
[O'Donnell, Exercise 7.22][ODonnell2014]. This is the multilinear (Fourier) expansion of the
relation evaluated at those means (`Logic.PL.Constraint.satProb_eq_sum_fourierCoeff`)
[O'Donnell, Exercise 7.20(c)][ODonnell2014], or equivalently its `multilinearExtension` at the
probabilities of `true` (`Logic.PL.Constraint.satProb_eq_eval_multilinearExtension`). The value
of the randomized assignment is the average of these probabilities over the constraints
(`Logic.PL.CSP.expectedSatFraction`). Labelling every variable with the sign of an ordinary
assignment `σ` recovers its value (`Logic.PL.CSP.expectedSatFraction_signVal`). Signs read the
Boolean `true` as `-1`, so `σ` is labelled with means `signVal (σ v)`. For means in `[-1, 1]`
both values lie in `[0, 1]` (`Logic.PL.CSP.expectedSatFraction_mem_Icc`,
`Logic.PL.CSP.satFraction_mem_Icc`).

Both values are one minus the fraction of the constraints that fail, so an empty instance has
value `1`, as for `Complexity.GapTwoCSP`, whose value is `1 - unsatVal`. On a nonempty instance
they are the satisfied fractions (`Logic.PL.CSP.satFraction_of_ne_nil`,
`Logic.PL.CSP.expectedSatFraction_of_ne_nil`).

## Usage

Open `Cslib.Logic.PL`. `F.satFraction sem σ` and `F.expectedSatFraction sem g` take the truth
tables `sem : Rel → List Bool → Bool` of the constraint language; for a constraint with a concrete
relation, compute `satProb` from the multilinear expansion of its predicate
(`Logic.PL.Constraint.satProb_eq_sum_fourierCoeff`), as `Logic.PL.CSP.satProb_paritySem` does for
linear equations. An instance listing one constraint for each outcome of a uniform choice over a
nonempty `Finset` (`s.toList.map c`) has value the expectation over that choice
(`Logic.PL.CSP.satFraction_map_toList`, `Logic.PL.CSP.expectedSatFraction_map_toList`). The checked
clients in [CslibFrontierTests/BooleanAnalysisHastadTest.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisHastadTest.lean)
evaluate a constraint whose scope repeats a variable, which is read position by position, so
`x₀ + x₀ + x₂ = false` at means `1/2, 1/2, 1` holds with probability `5/8`, not `1`.

## Main definitions

* `Cslib.Logic.PL.CSP.satFraction`: the value of an assignment.
* `Cslib.Logic.PL.Constraint.satProb`, `Cslib.Logic.PL.CSP.expectedSatFraction`: the probability
  that a constraint is satisfied by a randomized Boolean assignment, and the value of the
  randomized assignment.

## Main results

* `Cslib.Logic.PL.Constraint.satProb_eq_sum_fourierCoeff`,
  `Cslib.Logic.PL.Constraint.satProb_eq_eval_multilinearExtension`: the multilinear expansion.
* `Cslib.Logic.PL.Constraint.satProb_signVal`, `Cslib.Logic.PL.CSP.expectedSatFraction_signVal`:
  at the signs of an assignment, the value of the assignment.
* `Cslib.Logic.PL.Constraint.satProb_nonneg`, `Cslib.Logic.PL.Constraint.satProb_le_one`,
  `Cslib.Logic.PL.CSP.expectedSatFraction_mem_Icc`, `Cslib.Logic.PL.CSP.satFraction_mem_Icc`:
  the values are probabilities.
* `Cslib.Logic.PL.CSP.satFraction_of_ne_nil`, `Cslib.Logic.PL.CSP.expectedSatFraction_of_ne_nil`:
  the satisfied fractions of a nonempty instance.
* `Cslib.Logic.PL.CSP.satFraction_map_toList`,
  `Cslib.Logic.PL.CSP.expectedSatFraction_map_toList`: the value of an instance listing one
  constraint for each outcome of a uniformly random choice, as an expectation over the choice.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.Logic.PL

open Finset Cslib.BitString
open scoped BigOperators

variable {Rel V D : Type*}

namespace Constraint

/-- The probability that the constraint `c` is satisfied by the randomized assignment `g`: each
position `i` of the scope gets an independent random bit whose sign has mean `g` of the variable
at that position, so `true` with probability `(1 - g v) / 2`, and the relation is evaluated at the
list of these bits [O'Donnell, Exercises 7.20 and 7.22][ODonnell2014]. It is a probability when
`g` takes values in `[-1, 1]` (`satProb_nonneg`, `satProb_le_one`). -/
noncomputable def satProb (sem : Rel → List Bool → Bool) (g : V → ℝ) (c : Constraint Rel V) :
    ℝ :=
  ∑ a : Fin c.scope.length → Bool,
    meanWeight (fun i => g c.scope[i]) a * if sem c.rel (List.ofFn a) then 1 else 0

/-- The defining formula of `satProb`. -/
theorem satProb_def (sem : Rel → List Bool → Bool) (g : V → ℝ) (c : Constraint Rel V) :
    c.satProb sem g = ∑ a : Fin c.scope.length → Bool,
      meanWeight (fun i => g c.scope[i]) a * if sem c.rel (List.ofFn a) then 1 else 0 := by
  rw [satProb]

/-- **The multilinear expansion** [O'Donnell, Exercise 7.20(c)][ODonnell2014]: the probability
that a constraint is satisfied by a randomized assignment is the Fourier expansion of its relation,
read on bit strings of the length of its scope, evaluated at the means of the scope. -/
theorem satProb_eq_sum_fourierCoeff (sem : Rel → List Bool → Bool) (g : V → ℝ)
    (c : Constraint Rel V) :
    c.satProb sem g = ∑ S, fourierCoeff
      (fun a : Fin c.scope.length → Bool => if sem c.rel (List.ofFn a) then 1 else 0) S *
        ∏ i ∈ S, g c.scope[i] :=
  sum_meanWeight_mul_eq_sum_fourierCoeff _ _

/-- The probability that a constraint is satisfied by a randomized assignment is the
`multilinearExtension` of its relation at the probabilities `(1 - g v) / 2` that the positions of
its scope are `true`. -/
theorem satProb_eq_eval_multilinearExtension (sem : Rel → List Bool → Bool) (g : V → ℝ)
    (c : Constraint Rel V) :
    c.satProb sem g = MvPolynomial.eval (fun i : Fin c.scope.length => (1 - g c.scope[i]) / 2)
      (multilinearExtension fun a => if sem c.rel (List.ofFn a) then 1 else 0) :=
  sum_meanWeight_mul_eq_eval_multilinearExtension _ _

/-- At the signs of an assignment `σ`, the probability that a constraint is satisfied is `1` if
`σ` satisfies it and `0` otherwise. -/
theorem satProb_signVal (sem : Rel → List Bool → Bool) (σ : V → Bool) (c : Constraint Rel V) :
    c.satProb sem (fun v => signVal (σ v)) = if c.eval sem σ then 1 else 0 := by
  rw [satProb, Fintype.sum_eq_single (fun i => σ c.scope[i]) fun a ha => by
    rw [meanWeight_signVal, ite_eq_right ha, zero_mul]]
  rw [meanWeight_signVal, ite_eq_left rfl, one_mul, eval]
  simp only [Fin.getElem_fin, List.ofFn_getElem_eq_map]

/-- For a randomized assignment with values in `[-1, 1]`, the probability that a constraint is
satisfied is nonnegative. -/
theorem satProb_nonneg (sem : Rel → List Bool → Bool) {g : V → ℝ} (hg : ∀ v, |g v| ≤ 1)
    (c : Constraint Rel V) : 0 ≤ c.satProb sem g :=
  sum_nonneg fun a _ => mul_nonneg (meanWeight_nonneg (fun i => hg _) a) (by split_ifs <;> simp)

/-- For a randomized assignment with values in `[-1, 1]`, the probability that a constraint is
satisfied is at most one. -/
theorem satProb_le_one (sem : Rel → List Bool → Bool) {g : V → ℝ} (hg : ∀ v, |g v| ≤ 1)
    (c : Constraint Rel V) : c.satProb sem g ≤ 1 := by
  rw [satProb]
  refine (sum_le_sum fun a _ => mul_le_of_le_one_right (meanWeight_nonneg (fun i => hg _) a)
    (by split_ifs <;> simp)).trans_eq (sum_meanWeight _)

end Constraint

namespace CSP

/-- The value of the assignment `σ` for the instance `F`: the fraction of the constraints of `F`,
counted with multiplicity, that `σ` satisfies [O'Donnell, Definition 7.26][ODonnell2014], written
as one minus the fraction that `σ` fails, so that it is `1` for the empty instance. -/
noncomputable def satFraction (sem : Rel → List D → Bool) (σ : V → D) (F : CSP Rel V) : ℝ :=
  1 - (F.countP (fun c => !c.eval sem σ) : ℝ) / F.length

/-- The defining formula of `satFraction`. -/
theorem satFraction_def (sem : Rel → List D → Bool) (σ : V → D) (F : CSP Rel V) :
    F.satFraction sem σ = 1 - (F.countP (fun c => !c.eval sem σ) : ℝ) / F.length := by
  rw [satFraction]

/-- The value of the randomized assignment `g` for the instance `F`: the average, over the
constraints of `F` counted with multiplicity, of the probability that `g` satisfies them
[O'Donnell, Exercise 7.20][ODonnell2014], written as one minus the average probability that they
fail, so that it is `1` for the empty instance. -/
noncomputable def expectedSatFraction (sem : Rel → List Bool → Bool) (g : V → ℝ)
    (F : CSP Rel V) : ℝ :=
  1 - (F.map fun c => 1 - c.satProb sem g).sum / F.length

/-- The defining formula of `expectedSatFraction`. -/
theorem expectedSatFraction_def (sem : Rel → List Bool → Bool) (g : V → ℝ) (F : CSP Rel V) :
    F.expectedSatFraction sem g = 1 - (F.map fun c => 1 - c.satProb sem g).sum / F.length := by
  rw [expectedSatFraction]

/-- The empty instance has value `1`. -/
@[simp] theorem satFraction_nil (sem : Rel → List D → Bool) (σ : V → D) :
    satFraction sem σ ([] : CSP Rel V) = 1 := by
  simp [satFraction]

/-- The empty instance has value `1`. -/
@[simp] theorem expectedSatFraction_nil (sem : Rel → List Bool → Bool) (g : V → ℝ) :
    expectedSatFraction sem g ([] : CSP Rel V) = 1 := by
  simp [expectedSatFraction]

/-- On a nonempty instance, the value of an assignment is the fraction of the constraints it
satisfies. -/
theorem satFraction_of_ne_nil (sem : Rel → List D → Bool) (σ : V → D) {F : CSP Rel V}
    (hF : F ≠ []) :
    F.satFraction sem σ = (F.countP (Constraint.eval sem σ) : ℝ) / F.length := by
  have hlen : (F.length : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (List.length_pos_iff.2 hF).ne'
  have hcount := List.length_eq_countP_add_countP (Constraint.eval sem σ) (l := F)
  have hnot : F.countP (fun c => decide ¬c.eval sem σ = true) = F.countP fun c => !c.eval sem σ :=
    List.countP_congr fun c _ => by cases c.eval sem σ <;> simp
  rw [satFraction, eq_div_iff hlen, sub_mul, div_mul_cancel₀ _ hlen, one_mul, hcount, hnot,
    Nat.cast_add]
  ring

private theorem sum_map_one_sub {α : Type*} (p : α → ℝ) (F : List α) :
    (F.map fun c => 1 - p c).sum = F.length - (F.map p).sum := by
  induction F with
  | nil => simp
  | cons c F ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; push_cast; ring

/-- On a nonempty instance, the value of a randomized assignment is the average probability that
the constraints are satisfied. -/
theorem expectedSatFraction_of_ne_nil (sem : Rel → List Bool → Bool) (g : V → ℝ) {F : CSP Rel V}
    (hF : F ≠ []) :
    F.expectedSatFraction sem g = (F.map (Constraint.satProb sem g)).sum / F.length := by
  have hlen : (F.length : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (List.length_pos_iff.2 hF).ne'
  rw [expectedSatFraction, sum_map_one_sub, sub_div, div_self hlen]
  ring

/-- At the signs of an assignment `σ`, the value of the randomized assignment is the value of
`σ`. -/
theorem expectedSatFraction_signVal (sem : Rel → List Bool → Bool) (σ : V → Bool)
    (F : CSP Rel V) :
    F.expectedSatFraction sem (fun v => signVal (σ v)) = F.satFraction sem σ := by
  rw [expectedSatFraction, satFraction]
  congr 2
  induction F with
  | nil => simp
  | cons c F ih =>
    rw [List.map_cons, List.sum_cons, ih, Constraint.satProb_signVal, List.countP_cons]
    cases c.eval sem σ <;> simp [add_comm]

/-- For a randomized assignment with values in `[-1, 1]`, the value is a probability. -/
theorem expectedSatFraction_mem_Icc (sem : Rel → List Bool → Bool) {g : V → ℝ}
    (hg : ∀ v, |g v| ≤ 1) (F : CSP Rel V) : F.expectedSatFraction sem g ∈ Set.Icc 0 1 := by
  rcases eq_or_ne F [] with rfl | hF
  · simp
  have hlen : (0 : ℝ) < F.length := Nat.cast_pos.2 (List.length_pos_iff.2 hF)
  have hsum : 0 ≤ (F.map (Constraint.satProb sem g)).sum :=
    List.sum_nonneg fun x hx => by
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
      exact c.satProb_nonneg sem hg
  have hsum' : (F.map fun c => 1 - c.satProb sem g).sum ≥ 0 :=
    List.sum_nonneg fun x hx => by
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
      linarith [c.satProb_le_one sem hg]
  rw [expectedSatFraction_of_ne_nil sem g hF]
  refine ⟨div_nonneg hsum hlen.le, (div_le_one hlen).2 ?_⟩
  rw [sum_map_one_sub] at hsum'
  linarith

/-- The value of an assignment is a probability. -/
theorem satFraction_mem_Icc (sem : Rel → List D → Bool) (σ : V → D) (F : CSP Rel V) :
    F.satFraction sem σ ∈ Set.Icc 0 1 := by
  rcases eq_or_ne F [] with rfl | hF
  · simp
  have hlen : (0 : ℝ) < F.length := Nat.cast_pos.2 (List.length_pos_iff.2 hF)
  rw [satFraction_of_ne_nil sem σ hF]
  exact ⟨div_nonneg (Nat.cast_nonneg _) hlen.le,
    (div_le_one hlen).2 (by exact_mod_cast List.countP_le_length)⟩

/-- **An instance listing one constraint per outcome of a random choice**: the value of a
randomized assignment is the expectation, over a uniformly random element `s` of a nonempty
finite set, of the probability that it satisfies the constraint `c s`. -/
theorem expectedSatFraction_map_toList {ι : Type*} (sem : Rel → List Bool → Bool) (g : V → ℝ)
    {s : Finset ι} (hs : s.Nonempty) (c : ι → Constraint Rel V) :
    CSP.expectedSatFraction sem g (s.toList.map c) = 𝔼 i ∈ s, (c i).satProb sem g := by
  rw [expectedSatFraction_of_ne_nil sem g (by simpa using hs.ne_empty), List.map_map,
    sum_map_toList, List.length_map, length_toList, expect_eq_sum_div_card]
  rfl

/-- **An instance listing one constraint per outcome of a random choice**: the value of an
assignment is the probability, over a uniformly random element `s` of a nonempty finite set, that
it satisfies the constraint `c s`. -/
theorem satFraction_map_toList {ι : Type*} (sem : Rel → List D → Bool) (σ : V → D)
    {s : Finset ι} (hs : s.Nonempty) (c : ι → Constraint Rel V) :
    CSP.satFraction sem σ (s.toList.map c) =
      𝔼 i ∈ s, if (c i).eval sem σ then (1 : ℝ) else 0 := by
  rw [satFraction_of_ne_nil sem σ (by simpa using hs.ne_empty), List.countP_map,
    List.length_map, length_toList, expect_eq_sum_div_card, sum_boole]
  congr 2
  rw [List.countP_eq_length_filter, ← Multiset.coe_card, Finset.card_def, Finset.filter_val,
    ← coe_toList, Multiset.filter_coe]
  simp [Function.comp_def]

end CSP

end Cslib.Logic.PL
