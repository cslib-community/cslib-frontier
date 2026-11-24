/-
Copyright (c) 2026 Christian Reitwiessner, Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Matthew Doty
-/

module

import CslibFrontier.Foundations.Computability.RecursiveInClockedJoin

/-! # Handlers of clocked oracle programs compute, diverge and split joins as expected -/

set_option linter.privateModule false

namespace CslibFrontierTests.ClockedHandlers

open Cslib
open scoped Partrec

/-- The doubling oracle. -/
def double : ℕ →. ℕ := fun i => Part.some (2 * i)

/-- Answer a query `q` by searching for the least `i` with `double i = q`: a handler that needs
unbounded search and diverges on odd queries. -/
def half (q : ℕ) : ClockedComp natOracleSpec ℕ :=
  ClockedComp.rfind fun i => (fun r => decide (r = q)) <$> ClockedComp.query i

theorem stable_half (q : ℕ) : ClockedComp.Stable double (half q) :=
  .rfind fun i => (ClockedComp.Stable.query i).map _

theorem eval_half (q : ℕ) :
    ClockedComp.eval double (half q) = Nat.rfind fun i => Part.some (decide (2 * i = q)) := by
  refine (ClockedComp.eval_rfind double fun i => (ClockedComp.Stable.query i).map _).trans ?_
  congr 1
  funext i
  exact (ClockedComp.eval_map double (.query i) _).trans
    (congrArg _ (ClockedComp.eval_query double i))

/-- The search handler answers `6` with `3` against the doubling oracle. -/
theorem eval_half_six : ClockedComp.eval double (half 6) = Part.some 3 := by
  rw [eval_half]
  refine Part.eq_some_iff.2 (Nat.mem_rfind.2 ⟨by simp, fun {m} hm => ?_⟩)
  interval_cases m <;> simp

/-- The search handler diverges on `7`. -/
theorem eval_half_seven : ClockedComp.eval double (half 7) = Part.none := by
  rw [eval_half]
  refine Part.eq_none_iff.2 fun n hn => ?_
  have := Nat.rfind_spec hn
  simp only [Part.mem_some_iff] at this
  have := of_decide_eq_true this.symm
  omega

/-- Substituting the search handler into a program querying `6` returns `3`. -/
example : ClockedComp.eval double
    ((ClockedComp.query (spec := natOracleSpec) 6).subst half) = Part.some 3 := by
  exact ((ClockedComp.eval_subst stable_half (.query 6)).trans
    (ClockedComp.eval_query _ 6)).trans eval_half_six

/-- Substitution propagates the divergence of the handler. -/
example : ClockedComp.eval double
    ((ClockedComp.query (spec := natOracleSpec) 7).subst half) = Part.none := by
  exact ((ClockedComp.eval_subst stable_half (.query 7)).trans
    (ClockedComp.eval_query _ 7)).trans eval_half_seven

/-- A program over two oracles: the sum of their values at `0`. -/
def sumAtZero : ClockedComp (natOracleSpec ⊕ₒ natOracleSpec) ℕ := do
  let a ← ClockedComp.query (spec := natOracleSpec ⊕ₒ natOracleSpec) (Sum.inl 0)
  let b ← ClockedComp.query (spec := natOracleSpec ⊕ₒ natOracleSpec) (Sum.inr 0)
  pure (a + b)

theorem eval_sumAtZero (p x : ℕ →. ℕ) :
    ClockedComp.Stable (OracleComp.sumHandler p x) sumAtZero ∧
      ClockedComp.eval (OracleComp.sumHandler p x) sumAtZero =
        (p 0).bind fun a => (x 0).map (a + ·) := by
  refine ⟨(ClockedComp.Stable.query _).bind fun _ => (ClockedComp.Stable.query _).bind
    fun _ => .pure _, ?_⟩
  rw [sumAtZero, ClockedComp.eval_bind _ (.query _) fun _ =>
    (ClockedComp.Stable.query _).bind fun _ => .pure _]
  simp only [ClockedComp.eval_bind _ (.query _) fun _ => .pure _, ClockedComp.eval_pure]
  rw [ClockedComp.eval_query (OracleComp.sumHandler (m := Part) p x)]
  refine congrArg _ (funext fun a => ?_)
  rw [ClockedComp.eval_query (OracleComp.sumHandler (m := Part) p x), Part.bind_some_eq_map]

/-- Run through `joinHandler` against the join of the constant oracles `1` and `2`, the
two-oracle program returns `3`. -/
example : ClockedComp.eval ((fun _ => Part.some 1 : ℕ →. ℕ) ⊕ (fun _ => Part.some 2))
    (sumAtZero.subst Nat.RecursiveIn.Code.joinHandler) = Part.some 3 := by
  refine (Nat.RecursiveIn.Code.eval_subst_joinHandler _ _ (eval_sumAtZero _ _).1).trans
    (((eval_sumAtZero _ _).2).trans ?_)
  simp

/-- Run through `splitHandler` against the oracles `p` and `x`, a query `1` to the join reads
`x 0` and codes it as odd. -/
example (p x : ℕ →. ℕ) : ClockedComp.eval (OracleComp.sumHandler p x)
    ((ClockedComp.query (spec := natOracleSpec) 1).subst Nat.RecursiveIn.Code.splitHandler) =
      (x 0).map fun y => 2 * y + 1 := by
  refine (Nat.RecursiveIn.Code.eval_subst_splitHandler _ _ (.query 1)).trans
    ((ClockedComp.eval_query (p ⊕ x) 1).trans ?_)
  simp [Partrec.join]

end CslibFrontierTests.ClockedHandlers
