/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Formula
public import CslibFrontier.Foundations.Data.BitString.OpenSpherePartition
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Formula selectors for Lupanov's local coding

These are steps of the formula synthesis construction in [Lupanov1961Formulas, Section 4].
They do not state its asymptotic synthesis theorem. A minterm has `n` literal occurrences.
An open sphere can therefore be selected with `n ^ 2` occurrences. On that sphere, an arbitrary
subset of neighbors is selected by a disjunction with one literal per selected coordinate.
The latter fact lets the local coding construction sum the costs of all column patterns to `n`,
rather than charging `n` for every pattern separately.

All objects are native De Morgan formulas. Costs are `Formula.leafSize`, which counts literal
occurrences; they are not gate counts or circuit wire counts. The selector formulas make no
claim about alternating depth.
-/

@[expose] public section

namespace Cslib.Circuits.Formula

open Boolean Finset

variable {n : ℕ}

/-- The conjunction testing an entire assignment. For zero inputs it is constant true. -/
def minterm (z : BitString n) : Formula signature n :=
  andList ((List.finRange n).map (literal z))

/-- A minterm evaluates to true exactly on its assignment. -/
@[simp] theorem eval_minterm (z x : BitString n) :
    (minterm z).eval interpretation x = decide (x = z) := by
  apply Bool.eq_iff_iff.mpr
  simp [minterm, List.all_eq_true, funext_iff]

/-- A minterm has exactly one literal occurrence per input. -/
@[simp] theorem leafSize_minterm (z : BitString n) : (minterm z).leafSize = n := by
  simp [minterm, List.map_map, Function.comp_def]

/-- The disjunction of the minterms of a finite set of assignments. -/
noncomputable def indicator (S : Finset (BitString n)) : Formula signature n :=
  orList (S.toList.map minterm)

/-- The minterm disjunction computes membership in the specified finite set. -/
@[simp] theorem eval_indicator (S : Finset (BitString n)) (x : BitString n) :
    (indicator S).eval interpretation x = decide (x ∈ S) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp [indicator]

/-- The explicit minterm disjunction has `n` leaves per selected assignment. -/
@[simp] theorem leafSize_indicator (S : Finset (BitString n)) :
    (indicator S).leafSize = n * S.card := by
  simp [indicator, List.map_map, Function.comp_def, Nat.mul_comm]

/-- A selector for the open radius-one sphere about `c`: exactly one input bit differs. -/
noncomputable def openSphere (c : BitString n) : Formula signature n :=
  orList ((List.finRange n).map fun i => minterm (BitString.flipOn {i} c))

/-- Open-sphere membership is being a one-bit flip of the center. -/
@[simp] theorem eval_openSphere (c x : BitString n) :
    (openSphere c).eval interpretation x = decide (∃ i, x = BitString.flipOn {i} c) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp [openSphere]

/-- The explicit open-sphere selector uses exactly `n ^ 2` literal occurrences. -/
@[simp] theorem leafSize_openSphere (c : BitString n) : (openSphere c).leafSize = n ^ 2 := by
  simp [openSphere, List.map_map, Function.comp_def, pow_two]

/-- A disjunction selecting the coordinates in `S` where the input differs from `c`. -/
noncomputable def neighborSelector (c : BitString n) (S : Finset (Fin n)) : Formula signature n :=
  orList (S.toList.map fun i => literal (fun j => !c j) i)

/-- The selector uses one literal occurrence per selected coordinate. -/
@[simp] theorem leafSize_neighborSelector (c : BitString n) (S : Finset (Fin n)) :
    (neighborSelector c S).leafSize = S.card := by
  simp [neighborSelector, List.map_map, Function.comp_def]

/-- On the sphere, the selector accepts exactly the neighbors named by `S`. -/
theorem eval_neighborSelector_flip (c : BitString n) (S : Finset (Fin n)) (i : Fin n) :
    (neighborSelector c S).eval interpretation (BitString.flipOn {i} c) = decide (i ∈ S) := by
  classical
  have hbit (j : Fin n) : ((BitString.flipOn {i} c) j == !c j) = decide (j = i) := by
    by_cases h : j = i
    · subst j
      simp
    · rw [BitString.flipOn_singleton_of_ne h]
      cases c j <;> simp [h]
  apply Bool.eq_iff_iff.mpr
  simp [neighborSelector, hbit]

/-- Pattern classes partition the coordinates, so the sum of their selector leaf sizes is `n`.
This is the local accounting step in [Lupanov1961Formulas, §4, equation (11),
printed/PDF p. 10 of the English translation]. -/
theorem sum_leafSize_neighborSelector_fibers {α : Type*} [Fintype α] [DecidableEq α]
    (c : BitString n) (pattern : Fin n → α) :
    ∑ a, (neighborSelector c (univ.filter fun i => pattern i = a)).leafSize = n := by
  simp only [leafSize_neighborSelector, card_filter]
  rw [sum_comm]
  simp

end Cslib.Circuits.Formula
