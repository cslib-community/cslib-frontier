/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.Chosen
public import CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Bounds.Defs
public import CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackDP
import CslibFrontier.Algorithms.Lean.Knapsack.ProfitDP
import CslibFrontier.Logics.Propositional.PseudoBoolean.Reification
import Mathlib.Algebra.BigOperators.Fin

/-!
# Certified knapsack: a dynamic program that writes a VeriPB proof

The 0–1 knapsack problem takes `n` items with weights `w i` and profits `p i`, and a capacity
`B`, and asks for the largest profit `∑ i ∈ S, p i` of a set `S : Finset (Fin n)` of items of
weight `∑ i ∈ S, w i ≤ B`. This file writes it as a pseudo-Boolean problem, and gives a dynamic
program that writes, with its answer, a proof in the kernel format of VeriPB that the answer is
optimal, following §3.1 of [Demirović, McCreesh, McIlree, Nordström, Oertel and
Sidorov][DemirovicMcCreeshMcIlreeNordstromOertelSidorov2024]. The proof is checked by
`Cslib.Logic.PL.VeriPB.checkRed`; that the checker accepts it on every instance is proved in
`CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackCertify`.

**The encoding** (equations (1)–(3) of the paper). Item `i` is the variable `i`, true when the
item is taken; an assignment `σ` takes the items `Cslib.Logic.PL.VeriPB.chosen n σ`.
The formula is the single capacity constraint `∑ wᵢ ¬xᵢ ≥ ∑ wᵢ - B`, the normal form of
`∑ wᵢ xᵢ ≤ B` (`Cslib.Logic.PL.VeriPB.Knapsack.capacity`), and the objective, to be minimized, is
the negated profit `∑ -pᵢ xᵢ` (`Cslib.Logic.PL.VeriPB.Knapsack.objective`). An assignment
satisfies the formula exactly when the items it takes fit
(`Cslib.Logic.PL.VeriPB.Knapsack.holds_capacity_iff`), its objective value is the negated profit
of those items (`Cslib.Logic.PL.VeriPB.Knapsack.eval_objective`), and every set of items is taken
by some assignment (`Cslib.Logic.PL.VeriPB.exists_chosen_eq`). So a proof that the checker
accepts with the conclusion `BOUNDS lb : q ub` shows that the optimum lies in `[-ub, -lb]`
(`Cslib.Logic.PL.VeriPB.Knapsack.bounds_of_checkRed`), and is `-lb` when `lb = ub`
(`Cslib.Logic.PL.VeriPB.Knapsack.isGreatest_of_checkRed`). These statements hold for every proof,
whoever wrote it.

**The dynamic program** (`Cslib.Logic.PL.VeriPB.Knapsack.certify`). Layer `i` holds states
`(w, p)`: the weight and profit of a selection among the first `i` items, of weight at most `B`.
Layer `i + 1` takes the states of layer `i` and those with item `i` added, if they fit, and keeps
only the states that no other state *dominates*, by weighing no more and earning no less. The
layers and their proof are written by the state-graph emitter of
`CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackDP`, shared with the knapsack propagator,
with dominance merging and pruning on (`Cslib.Logic.PL.VeriPB.Knapsack.optMode`). The answer is the
profit of the selection of `Cslib.Algorithms.Lean.Knapsack.profitDP`. The proof follows §3.1 of
the paper:
* it logs that selection with `soli`, which adds the objective-improving constraint
  `∑ pᵢ xᵢ ≥ k + 1` for the answer `k`;
* for each state of layer `i` it reifies, by `Cslib.Logic.PL.VeriPB.reify`, the extension
  variables `W ⇔ ∑_{j<i} wⱼ xⱼ ≥ w`, `P ⇔ ∑_{j<i} pⱼ xⱼ ≤ p` and `S ⇔ W + P ≥ 2` (equations
  (8)–(10));
* for each state `S` of layer `i` and its successor `S'` of layer `i + 1` without item `i`, it
  derives `W ∧ ¬xᵢ ⇒ W'` and `P ∧ ¬xᵢ ⇒ P'` by adding the forward half of `W` to the backward half
  of `W'`, and of `P` to that of `P'`, and then `S ∧ ¬xᵢ ⇒ S'` by RUP (equations (11)–(13)); and
  likewise with item `i` (equations (17)–(19));
* if item `i` does not fit, it adds the forward half of `W` to the capacity constraint instead,
  and derives `S ⇒ ¬xᵢ` by RUP (equations (14)–(15));
* it derives `S ⇒ S'₀ ∨ S'₁` for the successors of `S` by RUP (equations (16) and (20)), and from
  these and the at-least-one constraint of layer `i`, that of layer `i + 1` (equations
  (22)–(23)); the layers are not deleted;
* each state of the last layer has profit at most `k`, so the forward half of its `P` plus the
  improving constraint gives `¬P`, and the at-least-one constraint of the last layer is refuted
  by RUP.

The paper derives an implication `S ⇒ S'` for a dominated state `S` of a layer and its dominating
state `S'` (equation (21)). Here a dominated state is never created: the transition that would
reach it goes to the dominating state, and its implications (11)–(13) or (17)–(19) are derived by
the same addition and RUP, as the paper allows ("we could instead derive the appropriate
implication whenever the maximum rule is used"). The conclusion is `BOUNDS -k : q -k`.

The proof has three extension variables for each state and a constant number of steps for each
state and transition. The theorem `Cslib.Logic.PL.VeriPB.Knapsack.isGreatest_of_checkRed_certify`
turns acceptance into optimality; acceptance itself holds on every instance
(`Cslib.Logic.PL.VeriPB.Knapsack.checkRed_certify`, in
`CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackCertify`).

## Main definitions

* `Cslib.Logic.PL.VeriPB.Knapsack.capacity`, `Cslib.Logic.PL.VeriPB.Knapsack.formula`,
  `Cslib.Logic.PL.VeriPB.Knapsack.objective`: the encoding; an assignment takes the items
  `Cslib.Logic.PL.VeriPB.chosen n σ`, shared with the clique encoding.
* `Cslib.Logic.PL.VeriPB.Knapsack.Certificate`, `Cslib.Logic.PL.VeriPB.Knapsack.certify`: the
  record of a claimed optimum and a candidate proof, and the proof-logging dynamic program that
  writes one, on the shared emitter (`Cslib.Logic.PL.VeriPB.Knapsack.optMode`,
  `Cslib.Logic.PL.VeriPB.Knapsack.optInst`, `Cslib.Logic.PL.VeriPB.Knapsack.optSteps`).

## Main results

* `Cslib.Logic.PL.VeriPB.Knapsack.holds_capacity_iff`,
  `Cslib.Logic.PL.VeriPB.Knapsack.eval_objective`: the encoding is correct.
* `Cslib.Logic.PL.VeriPB.Knapsack.bounds_of_checkRed`,
  `Cslib.Logic.PL.VeriPB.Knapsack.isGreatest_of_checkRed`: an accepted proof bounds the optimum.
* `Cslib.Logic.PL.VeriPB.Knapsack.isGreatest_of_checkRed_certify`: if the checker accepts the
  proof of the dynamic program, its answer is the optimum.

## References

* [E. Demirović, C. McCreesh, M. J. McIlree, J. Nordström, A. Oertel, K. Sidorov, *Pseudo-Boolean
  Reasoning About States and Transitions to Certify Dynamic Programming and Decision Diagram
  Algorithms*][DemirovicMcCreeshMcIlreeNordstromOertelSidorov2024]
-/

public section

namespace Cslib.Logic.PL.VeriPB.Knapsack

open PBConstr

variable {n : ℕ}

/-! ### The encoding -/

/-- **The capacity constraint** `∑ wᵢ ¬xᵢ ≥ ∑ wᵢ - B`, the normal form of `∑ wᵢ xᵢ ≤ B`
(equation (3) of the paper), with item `i` the variable `i`. -/
@[expose]
def capacity (w : Fin n → ℕ) (B : ℕ) : PBConstr :=
  ⟨(List.finRange n).map fun i => (w i, (i.val, false)), ((List.finRange n).map w).sum - B⟩

/-- **The knapsack formula**: the capacity constraint alone. -/
@[expose]
def formula (w : Fin n → ℕ) (B : ℕ) : List PBConstr := [capacity w B]

/-- **The knapsack objective**, the negated profit `∑ -pᵢ xᵢ`, to be minimized (equation (2) of the
paper). -/
@[expose]
def objective (p : Fin n → ℕ) : Objective :=
  ⟨(List.finRange n).map fun i => (i.val, -(p i : ℤ)), 0⟩

private theorem lhs_capacity (w : Fin n → ℕ) (B : ℕ) (σ : ℕ → Bool) :
    lhs σ (capacity w B).terms = ∑ i ∈ (chosen n σ)ᶜ, w i := by
  rw [capacity, lhs, List.map_map, ← Fin.sum_univ_def,
    show (chosen n σ)ᶜ = Finset.univ.filter fun i : Fin n => σ i.val = false by ext; simp,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases h : σ i.val <;> simp [termVal, Literal.eval, h]

/-- **The capacity constraint holds exactly when the items taken fit.** -/
theorem holds_capacity_iff (w : Fin n → ℕ) (B : ℕ) (σ : ℕ → Bool) :
    (capacity w B).Holds σ ↔ ∑ i ∈ chosen n σ, w i ≤ B := by
  have htot : ((List.finRange n).map w).sum = ∑ i ∈ chosen n σ, w i + ∑ i ∈ (chosen n σ)ᶜ, w i :=
    by rw [Finset.sum_add_sum_compl, Fin.sum_univ_def]
  rw [Holds, lhs_capacity]
  change ((List.finRange n).map w).sum - B ≤ _ ↔ _
  omega

/-- **The objective value is the negated profit of the items taken.** -/
theorem eval_objective (p : Fin n → ℕ) (σ : ℕ → Bool) :
    (objective p).eval σ = -∑ i ∈ chosen n σ, (p i : ℤ) := by
  rw [Objective.eval, objective, linVal, List.map_map, ← Fin.sum_univ_def, add_zero,
    ← Finset.sum_neg_distrib, chosen, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases h : σ i.val <;> simp [h]

/-! ### Accepted proofs bound the optimum -/

/-- **An accepted proof bounds the optimum**: if the checker accepts a proof with the conclusion
`BOUNDS lb : q ub` for the knapsack formula and objective, then every set of items that fits has
profit at most `-lb`, and some set that fits has profit at least `-ub`. -/
theorem bounds_of_checkRed {w p : Fin n → ℕ} {B : ℕ} {P : RedProof} {lb ub : ℤ} {q : ℕ}
    {asg : Option (List (Literal ℕ))} {pres : Option (List ℕ)}
    (h : checkRed (formula w B) (some (objective p)) P pres = true)
    (hc : P.conclusion = .bounds (some lb) q (some ub) asg) :
    (∀ S : Finset (Fin n), ∑ i ∈ S, w i ≤ B → ∑ i ∈ S, (p i : ℤ) ≤ -lb) ∧
      ∃ S : Finset (Fin n), ∑ i ∈ S, w i ≤ B ∧ -ub ≤ ∑ i ∈ S, (p i : ℤ) := by
  refine ⟨fun S hS => ?_, ?_⟩
  · obtain ⟨σ, rfl⟩ := exists_chosen_eq S
    have := le_eval_of_checkRed h hc σ (by simpa [formula, holds_capacity_iff] using hS)
    rw [eval_objective] at this
    omega
  · obtain ⟨σ, hσ, hle⟩ := exists_eval_le_of_checkRed h hc
    refine ⟨chosen n σ, (holds_capacity_iff w B σ).1 (hσ _ (by simp [formula])), ?_⟩
    rw [eval_objective] at hle
    omega

/-- **An accepted proof of `BOUNDS lb : q lb` certifies the optimum `-lb`**: it is the largest
profit of a set of items that fits. -/
theorem isGreatest_of_checkRed {w p : Fin n → ℕ} {B : ℕ} {P : RedProof} {lb : ℤ} {q : ℕ}
    {asg : Option (List (Literal ℕ))} {pres : Option (List ℕ)}
    (h : checkRed (formula w B) (some (objective p)) P pres = true)
    (hc : P.conclusion = .bounds (some lb) q (some lb) asg) :
    IsGreatest ((fun S : Finset (Fin n) => ∑ i ∈ S, (p i : ℤ)) '' {S | ∑ i ∈ S, w i ≤ B})
      (-lb) := by
  obtain ⟨hle, S, hS, hge⟩ := bounds_of_checkRed h hc
  exact ⟨⟨S, hS, le_antisymm (hle S hS) hge⟩, by rintro _ ⟨T, hT, rfl⟩; exact hle T hT⟩

/-! ### The proof-logging dynamic program -/

/-- The options of the optimization: merge the dominated states and drop the transitions that
overflow the capacity. -/
def optMode : Mode := ⟨true, true⟩

/-- The ℕ-indexed instance of the optimization: all items free, no profit bound. -/
def optInst (w p : Fin n → ℕ) (B : ℕ) : Inst := Inst.ofFin w p B 0 fun _ => none

/-- The steps of the dynamic program after the solution: the layers, then for each state of the
last layer the forward half of `P` plus the improving constraint `2`, then the contradiction by
RUP. Returns the proof and the number of the contradiction. -/
def optSteps (I : Inst) : Acc × ℕ :=
  let f := I.forward optMode
  let rn := f.2.headD ⟨0, [], [], 0⟩
  let e₂ := f.1.push (rn.nodes.map fun u => .step (.pol [.id u.pf, .id 2, .add]))
    rn.nodes.length 0
  let ks := (List.range rn.nodes.length).map (f.1.next + ·)
  (e₂.push [.step (.rup ⟨[], 1⟩ (ks.map .id ++ rn.nodes.map (.id ·.sf) ++ [.id rn.alo]))] 1 0,
    e₂.next)

/-- **A claimed knapsack optimum with a candidate proof**: a plain record of a natural number and a
kernel proof. Its type imposes no relation between them, nor any constraint on the proof's
conclusion; `Cslib.Logic.PL.VeriPB.Knapsack.certify` writes one whose conclusion is
`BOUNDS -optimum : q -optimum`, and only the checker's acceptance makes the optimum certified. -/
structure Certificate where
  /-- The claimed optimum. -/
  optimum : ℕ
  /-- The candidate proof. -/
  proof : RedProof

/-- **The proof-logging dynamic program** for the items of weights `w` and profits `p` and the
capacity `B`. It returns a claimed optimum, the profit of the selection of
`Cslib.Algorithms.Lean.Knapsack.profitDP`, and a VeriPB proof with the conclusion
`BOUNDS -optimum : q -optimum` for the knapsack formula and objective. When
`Cslib.Logic.PL.VeriPB.checkRed` accepts the proof, the claimed optimum is the optimum
(`Cslib.Logic.PL.VeriPB.Knapsack.isGreatest_of_checkRed_certify`), and it always accepts it
(`Cslib.Logic.PL.VeriPB.Knapsack.checkRed_certify`). -/
def certify (w p : Fin n → ℕ) (B : ℕ) : Certificate :=
  -- The solution is logged first, so its improving constraint is `2`; the rest starts at `3`.
  let sel := Cslib.Algorithms.Lean.Knapsack.profitDP w p B (List.finRange n)
  let k := (sel.map p).sum
  let r := optSteps (optInst w p B)
  ⟨k, ⟨.soli ((List.finRange n).map fun i => (i.val, decide (i ∈ sel))) :: r.1.steps.reverse,
    .bounds (some (-k)) r.2 (some (-k)) none⟩⟩

/-- **If the checker accepts the proof of the dynamic program, its answer is the optimum**: the
largest profit of a set of items that fits. -/
theorem isGreatest_of_checkRed_certify {w p : Fin n → ℕ} {B : ℕ}
    (h : checkRed (formula w B) (some (objective p)) (certify w p B).proof = true) :
    IsGreatest ((fun S : Finset (Fin n) => ∑ i ∈ S, p i) '' {S | ∑ i ∈ S, w i ≤ B})
      (certify w p B).optimum := by
  obtain ⟨q, hc⟩ : ∃ q, (certify w p B).proof.conclusion =
      .bounds (some (-(certify w p B).optimum)) q (some (-(certify w p B).optimum)) none :=
    ⟨_, rfl⟩
  obtain ⟨⟨S, hS, hSv⟩, hub⟩ := isGreatest_of_checkRed h hc
  refine ⟨⟨S, hS, ?_⟩, ?_⟩
  · simp only [neg_neg] at hSv
    exact_mod_cast hSv
  rintro _ ⟨T, hT, rfl⟩
  have := hub ⟨T, hT, rfl⟩
  simp only [neg_neg] at this
  exact_mod_cast this

end Cslib.Logic.PL.VeriPB.Knapsack

end
