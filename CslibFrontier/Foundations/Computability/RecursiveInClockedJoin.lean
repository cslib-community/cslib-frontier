/-
Copyright (c) 2026 Christian Reitwiessner, Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Clocked.Subst
public import CslibFrontier.Foundations.Computability.RecursiveInClocked
public import CslibFrontier.Foundations.Computability.RecursiveInJoin

/-!
# Handlers, code substitution and the Turing join

This file connects the handlers of `Cslib.ClockedComp.subst` with the code-level reductions of
`RecursiveInJoin` through the compiler `Nat.RecursiveIn.Code.toClocked`.

* *Code substitution.* The compiled program of a code `d` implements the function `d` computes,
  against every partial oracle (`Code.implements_toClocked`). Substituting it into the compiled
  program of `c` computes the substituted code `c.subst d` (`Code.eval_subst_toClocked`).
  Through codes, computability by clocked programs with computable dialogue is transitive
  (`Code.exists_clockedComp_trans`): the composite is the compiled program of a substituted code.
* *Two oracles and their join.* A program over the sum interface
  `natOracleSpec ⊕ₒ natOracleSpec`, run with the oracles `p` and `x`, computes the same as its
  substitution by `Code.joinHandler` run with the single oracle `p ⊕ x`
  (`Code.eval_subst_joinHandler`). The handler answers the two kinds of query by the compiled
  programs of `Code.joinLeft` and `Code.joinRight`. Conversely, a program over `natOracleSpec`
  run with `p ⊕ x` computes the same as its substitution by `Code.splitHandler`, which reads
  the join from the two oracles, run with `p` and `x` (`Code.eval_subst_splitHandler`).
  Composing `splitHandler` with the compiled programs of codes `a` and `b` implements the join
  code `Code.join a b` (`Code.implements_subst_splitHandler`).

## Main definitions

* `Nat.RecursiveIn.Code.joinHandler`: answer the two oracles of the sum interface from their join.
* `Nat.RecursiveIn.Code.splitHandler`: answer the join from the two oracles of the sum interface.

## Main results

* `Nat.RecursiveIn.Code.implements_toClocked`, `Nat.RecursiveIn.Code.eval_subst_toClocked`.
* `Nat.RecursiveIn.Code.exists_clockedComp_trans`: computability by clocked programs with
  computable dialogue is transitive.
* `Nat.RecursiveIn.Code.implements_joinHandler`, `Nat.RecursiveIn.Code.eval_subst_joinHandler`.
* `Nat.RecursiveIn.Code.implements_splitHandler`, `Nat.RecursiveIn.Code.eval_subst_splitHandler`.
* `Nat.RecursiveIn.Code.implements_subst_splitHandler`: the clocked form of `Code.eval_join`.
-/

@[expose] public section

open Cslib
open scoped Partrec

namespace Nat.RecursiveIn.Code

/-- The compiled program of a code implements, against every partial oracle `g`, the function the
code computes relative to `g`. -/
theorem implements_toClocked (g : ℕ →. ℕ) (d : Code) :
    ClockedComp.Implements d.toClocked g (d.eval g) :=
  fun n => ⟨stable_toClocked g d n, eval_toClocked g d n⟩

/-- Substituting compiled programs computes the substituted code: the clocked form of
`Code.eval_subst`. -/
theorem eval_subst_toClocked (g : ℕ →. ℕ) (c d : Code) (n : ℕ) :
    ClockedComp.eval g ((c.toClocked n).subst d.toClocked) = (c.subst d).eval g n := by
  rw [(implements_toClocked g d).eval_subst (stable_toClocked _ c n), eval_toClocked, eval_subst]

/-- **Transitivity of clocked reducibility.** If `F` is computed against `g`, and `g` against
`h`, by families of clocked programs with computable dialogue, then so is `F` against `h`. The
family is the compiled program of a substituted code, so its dialogue is computable even when the
given families are not stable. -/
theorem exists_clockedComp_trans {F g h : ℕ →. ℕ}
    (hF : ∃ P : ℕ → ClockedComp natOracleSpec ℕ, Computable (ClockedComp.dialogue P) ∧
      ∀ n, ClockedComp.eval g (P n) = F n)
    (hg : ∃ Q : ℕ → ClockedComp natOracleSpec ℕ, Computable (ClockedComp.dialogue Q) ∧
      ∀ n, ClockedComp.eval h (Q n) = g n) :
    ∃ R : ℕ → ClockedComp natOracleSpec ℕ, Computable (ClockedComp.dialogue R) ∧
      ∀ n, ClockedComp.eval h (R n) = F n := by
  obtain ⟨P, hP, hPF⟩ := hF
  obtain ⟨Q, hQ, hQg⟩ := hg
  obtain ⟨cP, hcP⟩ := ClockedComp.exists_code_eval hP
  obtain ⟨cQ, hcQ⟩ := ClockedComp.exists_code_eval hQ
  have eg : cQ.eval h = g := funext fun n => (congrFun (hcQ h) n).trans (hQg n)
  refine ⟨(cP.subst cQ).toClocked, computable_dialogue_toClocked _, fun n => ?_⟩
  rw [eval_toClocked, eval_subst, eg, hcP g]
  exact hPF n

/-! ### Two oracles and their join -/

/-- Answer a query of the left oracle by the compiled program of `joinLeft` and a query of the
right oracle by that of `joinRight`, both querying the join. -/
noncomputable def joinHandler :
    (q : ℕ ⊕ ℕ) → ClockedComp natOracleSpec ((natOracleSpec ⊕ₒ natOracleSpec) q) :=
  OracleComp.sumHandler joinLeft.toClocked joinRight.toClocked

/-- Answer a query of the join from the two oracles: an even query `2 * n` asks the left oracle at
`n`, an odd query `2 * n + 1` asks the right oracle at `n`. -/
def splitHandler (q : ℕ) : ClockedComp (natOracleSpec ⊕ₒ natOracleSpec) ℕ :=
  cond q.bodd
    ((fun y => 2 * y + 1) <$> ClockedComp.query (spec := natOracleSpec ⊕ₒ natOracleSpec)
      (Sum.inr q.div2))
    ((fun y => 2 * y) <$> ClockedComp.query (spec := natOracleSpec ⊕ₒ natOracleSpec)
      (Sum.inl q.div2))

/-- Against `p ⊕ x`, `joinHandler` implements the oracles `p` and `x` of the sum interface. -/
theorem implements_joinHandler (p x : ℕ →. ℕ) :
    ClockedComp.Implements joinHandler (p ⊕ x) (OracleComp.sumHandler p x) := by
  simpa only [joinHandler, eval_joinLeft, eval_joinRight] using
    (implements_toClocked (p ⊕ x) joinLeft).sumHandler (implements_toClocked (p ⊕ x) joinRight)

/-- Against the oracles `p` and `x`, `splitHandler` implements their join `p ⊕ x`. -/
theorem implements_splitHandler (p x : ℕ →. ℕ) :
    ClockedComp.Implements splitHandler (OracleComp.sumHandler p x) (p ⊕ x) := by
  intro q
  cases h : q.bodd <;> simp only [splitHandler, h, Bool.cond_false, Bool.cond_true] <;>
    refine ⟨(ClockedComp.Stable.query _).map _,
      (ClockedComp.eval_map _ (.query _) _).trans ?_⟩ <;>
    simp [ClockedComp.eval_query (OracleComp.sumHandler (m := Part) p x), Partrec.join, h]

/-- A program over two oracles `p` and `x`, with each query answered through the join, computes
the same relative to `p ⊕ x`. -/
theorem eval_subst_joinHandler (p x : ℕ →. ℕ) {α : Type}
    {P : ClockedComp (natOracleSpec ⊕ₒ natOracleSpec) α}
    (hP : ClockedComp.Stable (OracleComp.sumHandler p x) P) :
    ClockedComp.eval (p ⊕ x) (P.subst joinHandler) =
      ClockedComp.eval (OracleComp.sumHandler p x) P :=
  (implements_joinHandler p x).eval_subst hP

/-- A program relative to `p ⊕ x`, with each query of the join answered from `p` and `x`,
computes the same relative to the two oracles. -/
theorem eval_subst_splitHandler (p x : ℕ →. ℕ) {α : Type} {P : ClockedComp natOracleSpec α}
    (hP : ClockedComp.Stable (p ⊕ x) P) :
    ClockedComp.eval (OracleComp.sumHandler p x) (P.subst splitHandler) =
      ClockedComp.eval (p ⊕ x) P :=
  (implements_splitHandler p x).eval_subst hP

/-- Answering the two oracles of `splitHandler` by the compiled programs of codes `a` and `b`
implements the join code `Code.join a b`, against every partial oracle: the clocked form of
`Code.eval_join`. -/
theorem implements_subst_splitHandler (h : ℕ →. ℕ) (a b : Code) :
    ClockedComp.Implements
      (fun q => (splitHandler q).subst (OracleComp.sumHandler a.toClocked b.toClocked)) h
      ((join a b).eval h) := by
  rw [eval_join]
  exact (implements_splitHandler _ _).trans
    ((implements_toClocked h a).sumHandler (implements_toClocked h b))

end Nat.RecursiveIn.Code
