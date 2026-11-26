/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.Chosen
public import CslibFrontier.Logics.Propositional.PseudoBoolean.Reification
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Bounds.Defs
import Mathlib.Algebra.BigOperators.Fin

/-!
# Certified dynamic programs: encodings, certificates and the proof log

[Demirović, McCreesh, McIlree, Nordström, Oertel and
Sidorov][DemirovicMcCreeshMcIlreeNordstromOertelSidorov2024] certify a dynamic program for a
maximization problem by a VeriPB proof, written as the program runs, about its states and
transitions. Only the encoding of the *problem* as a pseudo-Boolean formula with an objective needs
a correctness theorem; the program and its proof are checked by
`Cslib.Logic.PL.VeriPB.checkRed` on each run. This file holds what the certified dynamic programs
of the library share.

* **Encodings.** `Cslib.Logic.PL.VeriPB.Encodes F f feas val` says that the formula `F` and the
  objective `f`, to be minimized, encode the maximization of `val` over `feas`: every feasible
  point is a solution of `F` of objective `-val`, and every solution of `F` is a feasible point of
  value `-f`. Then a proof that the checker accepts with the conclusion `BOUNDS lb : q ub` puts
  the optimum in `[-ub, -lb]` (`Cslib.Logic.PL.VeriPB.Encodes.bounds_of_checkRed`), equal to
  `-lb` when `lb = ub` (`Cslib.Logic.PL.VeriPB.Encodes.isGreatest_of_checkRed`), and one with the
  conclusion `BOUNDS INF : q ub` shows that nothing is feasible
  (`Cslib.Logic.PL.VeriPB.Encodes.eq_empty_of_checkRed`). These statements hold for every proof,
  whoever wrote it.
* **Selections.** For a problem that selects elements of `Fin n`, element `i` is the variable `i`
  (`Cslib.Logic.PL.VeriPB.chosen`), and the profit `∑ i ∈ S, p i` is the objective
  `∑ -pᵢ xᵢ` (`Cslib.Logic.PL.VeriPB.negProfit`). A formula whose solutions choose exactly the
  feasible sets then encodes the problem (`Cslib.Logic.PL.VeriPB.encodes_negProfit`).
* **Certificates.** `Cslib.Logic.PL.VeriPB.Certificate` is the plain record of a claimed optimum
  and a candidate proof that a certified dynamic program returns. Its type relates neither.
* **The proof log.** `Cslib.Logic.PL.VeriPB.ProofLog` is a kernel proof being written, with the
  steps that the dynamic programs emit: the reification `z ⇔ C` of a constraint by a fresh
  variable (`Cslib.Logic.PL.VeriPB.reify`), cutting-planes `pol` steps, hinted `rup` steps and
  deletions. It numbers the constraints and the fresh variables as the checker does.

## Main definitions

* `Cslib.Logic.PL.VeriPB.Encodes`: a formula and objective encode a maximization problem.
* `Cslib.Logic.PL.VeriPB.negProfit`: the objective `∑ -pᵢ xᵢ`.
* `Cslib.Logic.PL.VeriPB.Certificate`: a claimed optimum with a candidate proof.
* `Cslib.Logic.PL.VeriPB.ProofLog`: a kernel proof being written.

## Main results

* `Cslib.Logic.PL.VeriPB.Encodes.bounds_of_checkRed`,
  `Cslib.Logic.PL.VeriPB.Encodes.isGreatest_of_checkRed`,
  `Cslib.Logic.PL.VeriPB.Encodes.eq_empty_of_checkRed`: an accepted proof bounds the optimum, or
  shows infeasibility.
* `Cslib.Logic.PL.VeriPB.encodes_negProfit`: the encoding of a selection problem.

## References

* [E. Demirović, C. McCreesh, M. J. McIlree, J. Nordström, A. Oertel, K. Sidorov, *Pseudo-Boolean
  Reasoning About States and Transitions to Certify Dynamic Programming and Decision Diagram
  Algorithms*][DemirovicMcCreeshMcIlreeNordstromOertelSidorov2024]
-/

public section

namespace Cslib.Logic.PL.VeriPB

open Std.Sat (Literal)
open PBConstr

/-! ### Encodings of maximization problems -/

/-- **The formula `F` and the objective `f`, to be minimized, encode the maximization of `val`
over `feas`**: every feasible point is a solution of `F` with objective `-val`, and every solution
of `F` is a feasible point of value `-f`. -/
structure Encodes {α : Type*} (F : List PBConstr) (f : Objective) (feas : Set α) (val : α → ℤ) :
    Prop where
  /-- Every feasible point is a solution of objective `-val`. -/
  exists_eval : ∀ a ∈ feas, ∃ σ, (∀ c ∈ F, c.Holds σ) ∧ f.eval σ = -val a
  /-- Every solution is a feasible point of value `-f`. -/
  exists_val : ∀ σ, (∀ c ∈ F, c.Holds σ) → ∃ a ∈ feas, val a = -f.eval σ

namespace Encodes

variable {α : Type*} {F : List PBConstr} {f : Objective} {feas : Set α} {val : α → ℤ}
  {P : RedProof} {q : ℕ} {asg : Option (List (Literal ℕ))} {pres : Option (List ℕ)}

/-- **An accepted proof bounds the optimum**: if the checker accepts a proof with the conclusion
`BOUNDS lb : q ub` for an encoding of a maximization problem, then every feasible point has value
at most `-lb`, and some feasible point has value at least `-ub`. -/
theorem bounds_of_checkRed (hE : Encodes F f feas val) {lb ub : ℤ}
    (h : checkRed F (some f) P pres = true)
    (hc : P.conclusion = .bounds (some lb) q (some ub) asg) :
    (∀ a ∈ feas, val a ≤ -lb) ∧ ∃ a ∈ feas, -ub ≤ val a := by
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨σ, hσ, he⟩ := hE.exists_eval a ha
    have := le_eval_of_checkRed h hc σ hσ
    omega
  · obtain ⟨σ, hσ, hle⟩ := exists_eval_le_of_checkRed h hc
    obtain ⟨a, ha, hv⟩ := hE.exists_val σ hσ
    exact ⟨a, ha, by omega⟩

/-- **An accepted proof of `BOUNDS lb : q lb` certifies the optimum `-lb`** of an encoded
maximization problem. -/
theorem isGreatest_of_checkRed (hE : Encodes F f feas val) {lb : ℤ}
    (h : checkRed F (some f) P pres = true)
    (hc : P.conclusion = .bounds (some lb) q (some lb) asg) :
    IsGreatest (val '' feas) (-lb) := by
  obtain ⟨hle, a, ha, hge⟩ := hE.bounds_of_checkRed h hc
  exact ⟨⟨a, ha, le_antisymm (hle a ha) hge⟩, by rintro _ ⟨b, hb, rfl⟩; exact hle b hb⟩

/-- **An accepted proof of `BOUNDS -k : q -k` certifies the natural optimum `k`** of an encoded
maximization problem with natural values. -/
theorem isGreatest_natCast_of_checkRed (hE : Encodes F f feas val) {g : α → ℕ}
    (hg : ∀ a, val a = g a) {k : ℕ} (h : checkRed F (some f) P pres = true)
    (hc : P.conclusion = .bounds (some (-k)) q (some (-k)) asg) :
    IsGreatest (g '' feas) k := by
  obtain ⟨⟨a, ha, hv⟩, hub⟩ := hE.isGreatest_of_checkRed h hc
  refine ⟨⟨a, ha, by rw [hg] at hv; simpa using hv⟩, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  have := hub ⟨b, hb, rfl⟩
  rw [hg, neg_neg] at this
  exact_mod_cast this

/-- **An accepted proof of `BOUNDS INF : q ub` shows that nothing is feasible.** -/
theorem eq_empty_of_checkRed (hE : Encodes F f feas val) {ub : Option ℤ}
    (h : checkRed F (some f) P pres = true) (hc : P.conclusion = .bounds none q ub asg) :
    feas = ∅ :=
  Set.eq_empty_of_forall_notMem fun a ha => by
    obtain ⟨σ, hσ, -⟩ := hE.exists_eval a ha
    exact not_satisfiable_of_checkRed_bounds h hc σ hσ

end Encodes

/-! ### Selection problems -/

variable {n : ℕ}

/-- **The negated profit** `∑ -pᵢ xᵢ` of the elements chosen, an objective to be minimized. -/
@[expose]
def negProfit (p : Fin n → ℕ) : Objective :=
  ⟨(List.finRange n).map fun i => (i.val, -(p i : ℤ)), 0⟩

/-- **The objective value is the negated profit of the elements chosen.** -/
theorem eval_negProfit (p : Fin n → ℕ) (σ : ℕ → Bool) :
    (negProfit p).eval σ = -∑ i ∈ chosen n σ, (p i : ℤ) := by
  rw [Objective.eval, negProfit, linVal, List.map_map, ← Fin.sum_univ_def, add_zero,
    ← Finset.sum_neg_distrib, chosen, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases h : σ i.val <;> simp [h]

/-- **The encoding of a selection problem**: a formula whose solutions choose exactly the feasible
sets of elements, with the negated profit as objective, encodes the maximization of the profit
over the feasible sets. -/
theorem encodes_negProfit {F : List PBConstr} {feas : Set (Finset (Fin n))} (p : Fin n → ℕ)
    (hF : ∀ σ, (∀ c ∈ F, c.Holds σ) ↔ chosen n σ ∈ feas) :
    Encodes F (negProfit p) feas fun S => ∑ i ∈ S, (p i : ℤ) where
  exists_eval S hS := by
    obtain ⟨σ, rfl⟩ := exists_chosen_eq S
    exact ⟨σ, (hF σ).2 hS, eval_negProfit p σ⟩
  exists_val σ hσ := ⟨chosen n σ, (hF σ).1 hσ, by rw [eval_negProfit, neg_neg]⟩

/-! ### Certificates -/

/-- **A claimed optimum with a candidate proof**: a plain record. Its type imposes no relation
between them, nor any constraint on the proof's conclusion; only the checker's acceptance makes
the optimum certified. -/
structure Certificate (α : Type) where
  /-- The claimed optimum. -/
  optimum : α
  /-- The candidate proof. -/
  proof : RedProof

/-! ### The proof log -/

/-- **A kernel proof being written**: its steps, latest first, the number of the next constraint
and the next fresh variable. -/
structure ProofLog where
  /-- The steps written, latest first. -/
  steps : List TopStep
  /-- The number of the next constraint. -/
  next : ℕ
  /-- The next fresh variable. -/
  var : ℕ

namespace ProofLog

-- The bodies are exposed, so that the conclusion of a proof written through them unfolds.

/-- Reify the constraint `c` by the next fresh variable `z`, `z ⇔ c`
(`Cslib.Logic.PL.VeriPB.reify`): returns `z` and the numbers of `z ⇒ c` and of `c ⇒ z`. Each
`red` step with its empty subproof takes two numbers. -/
@[expose]
def reify (e : ProofLog) (c : PBConstr) : ProofLog × ℕ × ℕ × ℕ :=
  (⟨reifyBwd e.var c :: reifyFwd e.var c :: e.steps, e.next + 4, e.var + 1⟩,
    e.var, e.next + 1, e.next + 3)

/-- A `pol` step: returns the number of its constraint. -/
@[expose]
def pol (e : ProofLog) (ops : List PolOp) : ProofLog × ℕ :=
  (⟨.step (.pol ops) :: e.steps, e.next + 1, e.var⟩, e.next)

/-- A `rup` step with hints: returns the number of its constraint. -/
@[expose]
def rup (e : ProofLog) (c : PBConstr) (hs : List Hint) : ProofLog × ℕ :=
  (⟨.step (.rup c hs) :: e.steps, e.next + 1, e.var⟩, e.next)

/-- A `deld` step, which takes no number. -/
@[expose]
def deld (e : ProofLog) (ids : List ℕ) : ProofLog :=
  ⟨.deld ids :: e.steps, e.next, e.var⟩

/-- The proof of the steps `pre` followed by the steps written, with the conclusion `c`. -/
@[expose]
def proof (e : ProofLog) (pre : List TopStep) (c : Conclusion) : RedProof :=
  ⟨pre ++ e.steps.reverse, c⟩

end ProofLog

end Cslib.Logic.PL.VeriPB

end
