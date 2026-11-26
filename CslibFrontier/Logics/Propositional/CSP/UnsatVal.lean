/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP
public import Mathlib.Basic.Real.Pointwise
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Positivity

/-!
# Unsatisfiability value of constraint satisfaction problems

The **unsatisfiability value** `CSP.unsatVal sem F` of a CSP instance `F : CSP Rel V` under a
relation semantics `sem : Rel → List D → Bool` is the least proportion of its constraints, counted
with multiplicity, that an assignment `σ : V → D` falsifies. For nonempty domains `D`, the
minimum is attained (`CSP.exists_countUnsat_div_eq_unsatVal`) and vanishes precisely on
satisfiable instances (`CSP.unsatVal_eq_zero_iff`), mirroring `Cslib.Logic.PL.CNF.unsatVal`. The
empty system has value zero, and `1 - F.unsatVal sem` is the maximization value of `F`.

## Main definitions

* `Cslib.Logic.PL.CSP.unsatVal`: the least proportion of violated constraints.

## Main results

* `Cslib.Logic.PL.CSP.unsatVal_le`, `Cslib.Logic.PL.CSP.le_unsatVal_iff`: bounds by per-assignment
  violation proportions.
* `Cslib.Logic.PL.CSP.exists_countUnsat_div_eq_unsatVal`: the infimum is attained.
* `Cslib.Logic.PL.CSP.unsatVal_eq_zero_iff`: value zero characterizes satisfiability.
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {Rel V D : Type*}

/-- The **unsatisfiability value** of a CSP instance: the least proportion of its constraints,
counted with multiplicity, that an assignment falsifies. The empty instance has value zero. -/
noncomputable def CSP.unsatVal (sem : Rel → List D → Bool) (F : CSP Rel V) : ℝ :=
  ⨅ σ : V → D, (F.countP (fun c => !Constraint.eval sem σ c) : ℝ) / F.length

namespace CSP

variable (sem : Rel → List D → Bool) (F : CSP Rel V)

private theorem bddBelow_range_countUnsat_div :
    BddBelow (Set.range fun σ : V → D =>
      (F.countP (fun c => !Constraint.eval sem σ c) : ℝ) / F.length) :=
  ⟨0, Set.forall_mem_range.2 fun _ => by positivity⟩

/-- The value is at most the proportion of constraints falsified by any assignment. -/
theorem unsatVal_le (σ : V → D) :
    F.unsatVal sem ≤ (F.countP (fun c => !Constraint.eval sem σ c) : ℝ) / F.length :=
  ciInf_le (bddBelow_range_countUnsat_div sem F) σ

/-- The value is nonnegative. -/
theorem unsatVal_nonneg : 0 ≤ F.unsatVal sem :=
  Real.iInf_nonneg fun _ => by positivity

/-- The value is at most one. -/
theorem unsatVal_le_one [Nonempty D] : F.unsatVal sem ≤ 1 := by
  refine (unsatVal_le sem F fun _ => Classical.arbitrary D).trans ?_
  rcases Nat.eq_zero_or_pos F.length with h0 | hpos
  · simp [h0]
  · exact (div_le_one (by exact_mod_cast hpos)).2 (by exact_mod_cast List.countP_le_length)

/-- A lower bound on the value bounds the proportion falsified by every assignment. -/
theorem le_unsatVal_iff [Nonempty D] {c : ℝ} :
    c ≤ F.unsatVal sem ↔
      ∀ σ : V → D, c ≤ (F.countP (fun c => !Constraint.eval sem σ c) : ℝ) / F.length :=
  le_ciInf_iff (bddBelow_range_countUnsat_div sem F)

/-- The minimum is attained: the violation proportions take finitely many values. -/
theorem exists_countUnsat_div_eq_unsatVal [Nonempty D] :
    ∃ σ : V → D,
      (F.countP (fun c => !Constraint.eval sem σ c) : ℝ) / F.length = F.unsatVal sem :=
  (Set.range_nonempty _).csInf_mem <|
    (Set.finite_range fun j : Fin (F.length + 1) => (j : ℝ) / F.length).subset <| by
      rintro _ ⟨σ, rfl⟩
      exact ⟨⟨_, Nat.lt_succ_of_le List.countP_le_length⟩, rfl⟩

/-- **The value vanishes exactly on satisfiable instances.** -/
theorem unsatVal_eq_zero_iff [Nonempty D] : F.unsatVal sem = 0 ↔ F.Satisfiable sem := by
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ := exists_countUnsat_div_eq_unsatVal sem F
    rw [h, div_eq_zero_iff, Nat.cast_eq_zero, Nat.cast_eq_zero] at hσ
    rcases hσ with hσ | hσ
    · exact ⟨σ, List.all_eq_true.2 fun c hc => by simpa using List.countP_eq_zero.1 hσ c hc⟩
    · exact ⟨fun _ => Classical.arbitrary D, by rw [List.length_eq_zero_iff.1 hσ]; rfl⟩
  · rintro ⟨σ, hσ⟩
    refine le_antisymm ?_ (unsatVal_nonneg sem F)
    have h0 : F.countP (fun c => !Constraint.eval sem σ c) = 0 :=
      List.countP_eq_zero.2 fun c hc => by simp [List.all_eq_true.1 hσ c hc]
    simpa [h0] using unsatVal_le sem F σ

/-- The empty instance has unsatisfiability value zero. -/
@[simp]
theorem unsatVal_nil [Nonempty D] : CSP.unsatVal sem ([] : CSP Rel V) = 0 :=
  (unsatVal_eq_zero_iff sem []).2 ⟨fun _ => Classical.arbitrary D, rfl⟩

end CSP

end Cslib.Logic.PL
