/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Basic
public import CslibFrontier.Probability.IID
public import Mathlib.Data.List.Forall2

/-!
# Probabilistic list traversal

The support of ordinary `List.mapM` consists exactly of the lists whose entries are supported
by the corresponding calls. The relation also records the exact output length. These are
semantic laws; computational efficiency is provided separately in `Computability.Probabilistic`.

## Main results

* `Cslib.ProbComp.mem_support_mapM_iff`: pointwise support characterizes list traversal.
* `Cslib.ProbComp.eval_mapM_splice`: sample a designated coordinate before its surrounding
  traversal without changing the joint distribution.
* `Cslib.ProbComp.eval_mapM_range`: traversing `List.range k` equals pushing `PMF.piFin` through
  `List.ofFn`.
-/

public section

namespace Cslib.ProbComp

/-- The support of list traversal is exactly the pointwise support of the individual calls. -/
theorem mem_support_mapM_iff {α β : Type} (program : α → ProbComp β)
    (inputs : List α) (outputs : List β) :
    outputs ∈ (eval (inputs.mapM program)).support ↔
      List.Forall₂ (fun a b => b ∈ (eval (program a)).support) inputs outputs := by
  induction inputs generalizing outputs with
  | nil => cases outputs <;> simp
  | cons a inputs ih =>
    cases outputs with
    | nil => simp [List.mapM_cons]
    | cons b outputs =>
      simp only [PMF.mem_support_iff] at ih
      simp [List.mapM_cons, ih, and_comm]

/-- Sampling a designated coordinate before its prefix and suffix preserves the full traversal
law. The three computations use independent randomness, and the returned order is unchanged. -/
theorem eval_mapM_splice {α β : Type} (program : α → ProbComp β)
    (before : List α) (middle : α) (after : List α) :
    eval (do
      let challenge ← program middle
      let front ← before.mapM program
      let back ← after.mapM program
      pure (front ++ challenge :: back)) =
        eval ((before ++ middle :: after).mapM program) := by
  simp only [List.mapM_append, List.mapM_cons, eval_bind, eval_pure,
    PMF.bind_bind, PMF.pure_bind]
  exact PMF.bind_comm _ _ _

/-- Traversing `List.range k` with an indexed probabilistic computation has the law of drawing
independent coordinates via `PMF.piFin` and converting to a list via `List.ofFn`. -/
theorem eval_mapM_range {β : Type} :
    ∀ (k : ℕ) (f : ℕ → ProbComp β),
      eval ((List.range k).mapM f) =
        (Cslib.Probability.PMF.piFin fun i : Fin k => eval (f i.val)).map List.ofFn
  | 0, _ => by simp [Cslib.Probability.PMF.piFin]
  | k + 1, f => by
    rw [List.range_succ_eq_map, List.mapM_cons, List.mapM_map]
    simp only [eval_bind, eval_pure, Cslib.Probability.PMF.piFin, PMF.map_bind, PMF.map_comp,
      Function.comp_def]
    refine congrArg _ (funext fun first => ?_)
    change ((eval ((List.range k).mapM fun n => f (n + 1))).map (first :: ·)) = _
    rw [eval_mapM_range k (fun n => f (n + 1)), PMF.map_comp]
    exact congrArg (PMF.map · _) (funext fun _ => by simp [List.ofFn_succ])

end Cslib.ProbComp
