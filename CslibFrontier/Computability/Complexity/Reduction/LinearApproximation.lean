/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ApproximationSchemes
public import Mathlib.Data.Nat.Dist
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.Lattice.Nat

/-!
# Linear reductions for optimization problems

An L-reduction maps instances and recovers feasible solutions in polynomial time. The
target optimum is bounded by a fixed multiple of the source optimum, and the recovered
solution's absolute error is bounded by a fixed multiple of the target solution's error
[Papadimitriou and Yannakakis, §1, pp. 427–428][PapadimitriouYannakakis1991].
Natural-number factors suffice because increasing a positive real factor to a positive
integer preserves both inequalities.

## Main definitions

* `NPOptimizationProblem.optimum`: minimum or maximum of the feasible objective values.
* `LReduction`: instance and solution maps with constant optimum and error bounds.

## Main results

* `NPOptimizationProblem.exists_optimum`: an optimum is attained.
* `LReduction.refl`, `LReduction.trans`: identity and composition.
* `LReduction.ptas`: a PTAS transfers from target to source.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

namespace NPOptimizationProblem

variable {α β : Type} {encI : α ↪ List Bool} {encS : β ↪ List Bool}
  (problem : NPOptimizationProblem encI encS)

private def values (a : α) : Set ℕ := (fun b => problem.value (a, b)) '' {b | problem.Feasible a b}

private theorem values_finite (a : α) : (problem.values a).Finite := by
  obtain ⟨p, hp⟩ := problem.solution_length_bound
  have h := (List.finite_length_le Bool (p.eval (encI a).length)).preimage encS.injective.injOn
  exact (h.subset fun b hb => hp a b hb).image _

private theorem values_nonempty (a : α) : (problem.values a).Nonempty := by
  obtain ⟨b, hb⟩ := problem.exists_feasible a
  exact ⟨_, b, hb, rfl⟩

/-- The objective value of an optimal feasible solution. -/
noncomputable def optimum (a : α) : ℕ :=
  match problem.goal with
  | .minimize => sInf (problem.values a)
  | .maximize => sSup (problem.values a)

/-- There is a feasible solution with the optimal objective value. -/
theorem exists_optimum (a : α) :
    ∃ b, problem.Feasible a b ∧ problem.value (a, b) = problem.optimum a := by
  change problem.optimum a ∈ problem.values a
  unfold optimum
  split
  · exact Nat.sInf_mem (problem.values_nonempty a)
  · exact (problem.values_nonempty a).csSup_mem (problem.values_finite a)

/-- The optimum is at most the value of any feasible solution to a minimization problem. -/
theorem optimum_le_value {a : α} {b : β} (hgoal : problem.goal = .minimize)
    (hb : problem.Feasible a b) : problem.optimum a ≤ problem.value (a, b) := by
  rw [optimum, hgoal]
  exact Nat.sInf_le ⟨b, hb, rfl⟩

/-- The value of any feasible solution to a maximization problem is at most the optimum. -/
theorem value_le_optimum {a : α} {b : β} (hgoal : problem.goal = .maximize)
    (hb : problem.Feasible a b) : problem.value (a, b) ≤ problem.optimum a := by
  rw [optimum, hgoal]
  exact le_csSup (problem.values_finite a).bddAbove ⟨b, hb, rfl⟩

/-- For a feasible solution, the accuracy bound is equivalent to an absolute error bound
scaled by the inverse accuracy. -/
theorem isApproximate_iff_error {k : ℕ} {a : α} {b : β} :
    problem.IsApproximate k a b ↔ problem.Feasible a b ∧
      k * Nat.dist (problem.value (a, b)) (problem.optimum a) ≤ problem.optimum a := by
  obtain ⟨optimal, hfeasible, hvalue⟩ := problem.exists_optimum a
  unfold IsApproximate
  refine and_congr_right fun hb => ?_
  cases hgoal : problem.goal with
  | minimize =>
    have leValue {other : β} (h : problem.Feasible a other) := problem.optimum_le_value hgoal h
    rw [Nat.dist_eq_sub_of_le_right (leValue hb), Nat.mul_sub_left_distrib]
    have hm := Nat.mul_le_mul_left k (leValue hb)
    constructor
    · intro h
      have bound := h optimal hfeasible
      rw [hvalue, Nat.add_mul, Nat.one_mul] at bound
      omega
    · intro h other hother
      calc
        k * problem.value (a, b) ≤ (k + 1) * problem.optimum a := by
          rw [Nat.add_mul, Nat.one_mul]
          omega
        _ ≤ _ := Nat.mul_le_mul_left _ (leValue hother)
  | maximize =>
    have valueLe {other : β} (h : problem.Feasible a other) := problem.value_le_optimum hgoal h
    rw [Nat.dist_eq_sub_of_le (valueLe hb), Nat.mul_sub_left_distrib]
    constructor
    · intro h
      have bound := h optimal hfeasible
      rw [hvalue, Nat.sub_mul, Nat.one_mul] at bound
      omega
    · intro h other hother
      calc
        (k - 1) * problem.value (a, other) ≤ (k - 1) * problem.optimum a :=
          Nat.mul_le_mul_left _ (valueLe hother)
        _ ≤ _ := by
          rw [Nat.sub_mul, Nat.one_mul]
          omega

end NPOptimizationProblem

variable {α₁ β₁ α₂ β₂ α₃ β₃ : Type}
  {encI₁ : α₁ ↪ List Bool} {encS₁ : β₁ ↪ List Bool}
  {encI₂ : α₂ ↪ List Bool} {encS₂ : β₂ ↪ List Bool}
  {encI₃ : α₃ ↪ List Bool} {encS₃ : β₃ ↪ List Bool}

/-- A polynomial-time L-reduction between two NP optimization problems. -/
structure LReduction
    (A : NPOptimizationProblem encI₁ encS₁) (B : NPOptimizationProblem encI₂ encS₂) where
  /-- The instance map. -/
  mapInstance : α₁ → α₂
  /-- The solution map takes the original instance and a target solution. -/
  recover : α₁ × β₂ → β₁
  /-- The instance map is computable in polynomial time. -/
  computableInPolyTime_mapInstance : ComputableInPolyTime mapInstance encI₁ encI₂
  /-- The solution map is computable in polynomial time. -/
  computableInPolyTime_recover : ComputableInPolyTime recover (encPair encI₁ encS₂) encS₁
  /-- The constant that bounds growth of the optimum. -/
  optimumFactor : ℕ
  /-- The optimum factor is positive. -/
  optimumFactor_pos : 0 < optimumFactor
  /-- The constant that bounds growth of absolute objective error. -/
  errorFactor : ℕ
  /-- The error factor is positive. -/
  errorFactor_pos : 0 < errorFactor
  /-- Recovering a feasible target solution gives a feasible source solution. -/
  feasible_recover : ∀ a b, B.Feasible (mapInstance a) b → A.Feasible a (recover (a, b))
  /-- The target optimum is at most a fixed multiple of the source optimum. -/
  optimum_bound : ∀ a, B.optimum (mapInstance a) ≤ optimumFactor * A.optimum a
  /-- The absolute error at the recovered solution is bounded by the target error. -/
  error_bound : ∀ a b, B.Feasible (mapInstance a) b →
    Nat.dist (A.value (a, recover (a, b))) (A.optimum a) ≤
      errorFactor * Nat.dist (B.value (mapInstance a, b)) (B.optimum (mapInstance a))

namespace LReduction

variable {A : NPOptimizationProblem encI₁ encS₁} {B : NPOptimizationProblem encI₂ encS₂}
  {C : NPOptimizationProblem encI₃ encS₃}

/-- The identity L-reduction. -/
def refl (A : NPOptimizationProblem encI₁ encS₁) : LReduction A A where
  mapInstance := id
  recover := Prod.snd
  computableInPolyTime_mapInstance := ComputableInPolyTime.id'
  computableInPolyTime_recover := ComputableInPolyTime.snd _ _
  optimumFactor := 1
  optimumFactor_pos := Nat.one_pos
  errorFactor := 1
  errorFactor_pos := Nat.one_pos
  feasible_recover _ _ h := h
  optimum_bound _ := by simp
  error_bound _ _ _ := by simp

/-- L-reductions compose, multiplying the optimum and error factors. -/
def trans (r : LReduction A B) (s : LReduction B C) : LReduction A C where
  mapInstance := s.mapInstance ∘ r.mapInstance
  recover p := r.recover (p.1, s.recover (r.mapInstance p.1, p.2))
  computableInPolyTime_mapInstance :=
    s.computableInPolyTime_mapInstance.comp r.computableInPolyTime_mapInstance
  computableInPolyTime_recover := by
    have hsource := ComputableInPolyTime.fst encI₁ encS₃
    have htarget := ComputableInPolyTime.snd encI₁ encS₃
    exact r.computableInPolyTime_recover.comp (hsource.prod
      (s.computableInPolyTime_recover.comp
        ((r.computableInPolyTime_mapInstance.comp hsource).prod htarget)))
  optimumFactor := s.optimumFactor * r.optimumFactor
  optimumFactor_pos := Nat.mul_pos s.optimumFactor_pos r.optimumFactor_pos
  errorFactor := r.errorFactor * s.errorFactor
  errorFactor_pos := Nat.mul_pos r.errorFactor_pos s.errorFactor_pos
  feasible_recover a b h := r.feasible_recover a _ (s.feasible_recover (r.mapInstance a) b h)
  optimum_bound a := by
    calc
      C.optimum (s.mapInstance (r.mapInstance a)) ≤
          s.optimumFactor * B.optimum (r.mapInstance a) := s.optimum_bound _
      _ ≤ s.optimumFactor * (r.optimumFactor * A.optimum a) :=
        Nat.mul_le_mul_left _ (r.optimum_bound a)
      _ = _ := (Nat.mul_assoc _ _ _).symm
  error_bound a b h := by
    have hs := s.feasible_recover (r.mapInstance a) b h
    exact (r.error_bound a _ hs).trans
      ((Nat.mul_le_mul_left _ (s.error_bound (r.mapInstance a) b h)).trans_eq
        (Nat.mul_assoc _ _ _).symm)

/-- The recovered solution has the requested accuracy if the target accuracy is scaled
by the two reduction factors [Papadimitriou and Yannakakis, Proposition 2]
[PapadimitriouYannakakis1991]. -/
theorem isApproximate_recover (r : LReduction A B) {k : ℕ} {a : α₁} {b : β₂}
    (hb : B.IsApproximate (r.optimumFactor * (k * r.errorFactor)) (r.mapInstance a) b) :
    A.IsApproximate k a (r.recover (a, b)) := by
  obtain ⟨hfeasible, herror⟩ := B.isApproximate_iff_error.mp hb
  refine A.isApproximate_iff_error.mpr ⟨r.feasible_recover a b hfeasible,
    Nat.le_of_mul_le_mul_left ?_ r.optimumFactor_pos⟩
  calc
    r.optimumFactor * (k * Nat.dist (A.value (a, r.recover (a, b))) (A.optimum a)) ≤
        (r.optimumFactor * (k * r.errorFactor)) *
          Nat.dist (B.value (r.mapInstance a, b)) (B.optimum (r.mapInstance a)) := by
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left r.optimumFactor
        (Nat.mul_le_mul_left k (r.error_bound a _ hfeasible))
    _ ≤ B.optimum (r.mapInstance a) := herror
    _ ≤ r.optimumFactor * A.optimum a := r.optimum_bound a

/-- A PTAS for the target induces a PTAS for the source. -/
theorem ptas (r : LReduction A B) (h : B.PTAS) : A.PTAS := by
  intro k hk
  let j := r.optimumFactor * (k * r.errorFactor)
  have hj : 0 < j := Nat.mul_pos r.optimumFactor_pos (Nat.mul_pos hk r.errorFactor_pos)
  obtain ⟨solve, hsolve, hgood⟩ := h j hj
  exact ⟨fun a => r.recover (a, solve (r.mapInstance a)), r.computableInPolyTime_recover.comp
    (ComputableInPolyTime.id'.prod (hsolve.comp r.computableInPolyTime_mapInstance)),
    fun a => r.isApproximate_recover (hgood (r.mapInstance a))⟩

end LReduction

end Cslib.Complexity
