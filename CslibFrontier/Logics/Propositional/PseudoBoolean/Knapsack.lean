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
`Cslib.Logic.PL.VeriPB.checkRed`; nothing about the dynamic program is proved.

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
answer is the largest profit in the last layer. The proof follows §3.1 of the paper:
* it logs an optimal selection with `soli`, which adds the objective-improving constraint
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
  (22)–(23)), and then deletes the constraints of layer `i`;
* each state of the last layer has profit at most `k`, so the forward half of its `P` plus the
  improving constraint gives `¬P`, and the at-least-one constraint of the last layer is refuted
  by RUP.

The paper derives an implication `S ⇒ S'` for a dominated state `S` of a layer and its dominating
state `S'` (equation (21)). Here a dominated state is never created: the transition that would
reach it goes to the dominating state, and its implications (11)–(13) or (17)–(19) are derived by
the same addition and RUP, as the paper allows ("we could instead derive the appropriate
implication whenever the maximum rule is used"). The conclusion is `BOUNDS -k : q -k`.

The proof has three extension variables for each state and a constant number of steps for each
state and transition. That the checker accepts it is not proved, nor that the claimed optimum is
right: both are checked when the proof is run, and the theorem
`Cslib.Logic.PL.VeriPB.Knapsack.isGreatest_of_checkRed_certify` turns acceptance into
optimality.

## Main definitions

* `Cslib.Logic.PL.VeriPB.Knapsack.capacity`, `Cslib.Logic.PL.VeriPB.Knapsack.formula`,
  `Cslib.Logic.PL.VeriPB.Knapsack.objective`: the encoding; an assignment takes the items
  `Cslib.Logic.PL.VeriPB.chosen n σ`, shared with the clique encoding.
* `Cslib.Logic.PL.VeriPB.Knapsack.Certificate`, `Cslib.Logic.PL.VeriPB.Knapsack.certify`: the
  record of a claimed optimum and a candidate proof, and the proof-logging dynamic program that
  writes one.

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

/-- A state of the dynamic program on a layer: the weight and the profit of a selection of the
items so far, and the selection, latest item first. -/
private structure St where
  w : ℕ
  p : ℕ
  sel : List ℕ

/-- Add the state `s` to a list of states none of which dominates another: drop `s` if a state
weighs no more and earns no less, and otherwise drop the states that `s` dominates. -/
private def insertSt (K : List St) (s : St) : List St :=
  if K.any fun t => decide (t.w ≤ s.w) && decide (s.p ≤ t.p) then K
  else s :: K.filter fun t => !(decide (s.w ≤ t.w) && decide (t.p ≤ s.p))

/-- A state together with its extension variable `S` and the numbers of the forward and backward
halves of the reifications of `W`, `P` and `S`. -/
private structure Node where
  st : St
  S : ℕ
  wf : ℕ
  wb : ℕ
  pf : ℕ
  pb : ℕ
  sf : ℕ
  sb : ℕ

/-- A placeholder node, never reached on the dynamic program's own layers. -/
private def noNode : Node := ⟨⟨0, 0, []⟩, 0, 0, 0, 0, 0, 0, 0⟩

/-- The numbers of the constraints of a node. -/
private def Node.ids (u : Node) : List ℕ := [u.wf, u.wb, u.pf, u.pb, u.sf, u.sb]

/-- The proof being written: its steps, latest first, the next constraint number and the next
free variable. -/
private structure Acc where
  steps : List TopStep
  next : ℕ
  var : ℕ

/-- Reify a fresh variable `z ⇔ c`: returns `z` and the numbers of `z ⇒ c` and `c ⇒ z`. -/
private def Acc.reify (e : Acc) (c : PBConstr) : Acc × ℕ × ℕ × ℕ :=
  (⟨reifyBwd e.var c :: reifyFwd e.var c :: e.steps, e.next + 4, e.var + 1⟩,
    e.var, e.next + 1, e.next + 3)

/-- A `pol` step: returns the number of its constraint. -/
private def Acc.pol (e : Acc) (ops : List PolOp) : Acc × ℕ :=
  (⟨.step (.pol ops) :: e.steps, e.next + 1, e.var⟩, e.next)

/-- A `rup` step: returns the number of its constraint. -/
private def Acc.rup (e : Acc) (c : PBConstr) (hs : List Hint) : Acc × ℕ :=
  (⟨.step (.rup c hs) :: e.steps, e.next + 1, e.var⟩, e.next)

/-- The clause of a list of literals. -/
private def clause (ls : List (Literal ℕ)) : PBConstr := ⟨ls.map ((1, ·)), 1⟩

/-- The prefix sums of layer `i`: the terms `wⱼ xⱼ` and `pⱼ ¬xⱼ` of the items `j < i`, without
zero coefficients, and the total profit. -/
private structure Pre where
  wTerms : List (ℕ × Literal ℕ)
  pTerms : List (ℕ × Literal ℕ)
  pTot : ℕ

/-- Create the node of a state: reify `W ⇔ ∑ wⱼ xⱼ ≥ w`, `P ⇔ ∑ pⱼ ¬xⱼ ≥ ∑ pⱼ - p` and
`S ⇔ W + P ≥ 2`. -/
private def mkNode (pre : Pre) (e : Acc) (s : St) : Acc × Node :=
  let (e, a, wf, wb) := e.reify ⟨pre.wTerms, s.w⟩
  let (e, c, pf, pb) := e.reify ⟨pre.pTerms, pre.pTot - s.p⟩
  let (e, S, sf, sb) := e.reify ⟨[(1, (a, true)), (1, (c, true))], 2⟩
  (e, ⟨s, S, wf, wb, pf, pb, sf, sb⟩)

/-- Create the nodes of a layer. -/
private def mkLayer (pre : Pre) (e : Acc) (ss : List St) : Acc × List Node :=
  ss.foldl (fun (e, L) s => let (e, u) := mkNode pre e s; (e, u :: L)) (e, [])

/-- The node of the layer `L` that dominates the state `(w, p)`. -/
private def domNode (L : List Node) (w p : ℕ) : Node :=
  (L.find? fun t => decide (t.st.w ≤ w) && decide (p ≤ t.st.p)).getD noNode

/-- The transition implication `S_u ∧ x ⇒ S_t` (equations (11)–(13) and (17)–(19)), with the
numbers of the constraints it adds, the implication last. -/
private def transition (e : Acc) (u t : Node) (x : Literal ℕ) : Acc × List ℕ :=
  let (e, A) := e.pol [.id u.wf, .id t.wb, .add]
  let (e, P) := e.pol [.id u.pf, .id t.pb, .add]
  let (e, τ) := e.rup (clause [(u.S, false), (x.1, !x.2), (t.S, true)])
    [.neg, .id u.sf, .id A, .id P, .id t.sb]
  (e, [A, P, τ])

/-- The transitions out of the node `u` for the item `j` of weight `wj` and profit `pj`, into the
layer `L`: returns the number of `S_u ⇒ ⋁ S_t` over the successors `t`, and the numbers of all the
constraints added. -/
private def successors (B j wj pj : ℕ) (L : List Node) (e : Acc) (u : Node) :
    Acc × ℕ × List ℕ :=
  let t₀ := domNode L u.st.w u.st.p
  let (e, ids₀) := transition e u t₀ (j, false)
  let τ₀ := ids₀.getLastD 0
  if u.st.w + wj ≤ B then
    let t₁ := domNode L (u.st.w + wj) (u.st.p + pj)
    let (e, ids₁) := transition e u t₁ (j, true)
    let τ₁ := ids₁.getLastD 0
    let ts := if t₀.S = t₁.S then [(t₀.S, true)] else [(t₁.S, true), (t₀.S, true)]
    let (e, c) := e.rup (clause ((u.S, false) :: ts)) [.neg, .id τ₁, .id τ₀]
    (e, c, ids₀ ++ ids₁ ++ [c])
  else
    let (e, A) := e.pol [.id u.wf, .id 1, .add]
    let (e, τ₁) := e.rup (clause [(u.S, false), (j, false)]) [.neg, .id u.sf, .id A]
    let (e, c) := e.rup (clause [(u.S, false), (t₀.S, true)]) [.neg, .id τ₁, .id τ₀]
    (e, c, ids₀ ++ [A, τ₁, c])

/-- The states of the next layer: those of `L`, and those with the item `j` added if they fit,
without dominated states. -/
private def nextStates (B j wj pj : ℕ) (L : List Node) : List St :=
  L.foldl (fun K u =>
    let K := insertSt K u.st
    if u.st.w + wj ≤ B then insertSt K ⟨u.st.w + wj, u.st.p + pj, j :: u.st.sel⟩ else K) []

/-- The state of the dynamic program between layers: the nodes of the current layer, the number
of its at-least-one constraint, its prefix sums and the proof so far. -/
private structure Layer where
  nodes : List Node
  alo : ℕ
  pre : Pre
  acc : Acc

/-- One layer of the dynamic program, for the item `j` of weight `wj` and profit `pj`: create the
next layer, derive its transitions and its at-least-one constraint, and delete the current
layer. -/
private def step (B : ℕ) (X : Layer) (item : ℕ × ℕ × ℕ) : Layer :=
  let (j, wj, pj) := item
  let pre : Pre :=
    ⟨if wj = 0 then X.pre.wTerms else X.pre.wTerms ++ [(wj, (j, true))],
      if pj = 0 then X.pre.pTerms else X.pre.pTerms ++ [(pj, (j, false))], X.pre.pTot + pj⟩
  let (e, L) := mkLayer pre X.acc (nextStates B j wj pj X.nodes)
  let (e, cs, dead) := X.nodes.foldl (fun (e, cs, dead) u =>
    let (e, c, ids) := successors B j wj pj L e u
    (e, c :: cs, ids ++ dead)) (e, [], [])
  let (e, alo) := e.rup (clause (L.map fun t => (t.S, true)))
    (.neg :: cs.map .id ++ [.id X.alo])
  let dead := X.alo :: X.nodes.flatMap Node.ids ++ dead
  ⟨L, alo, pre, ⟨.deld dead :: e.steps, e.next, e.var⟩⟩

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
capacity `B`. It returns a claimed optimum, the largest profit in the last layer of the dynamic
program, and a candidate VeriPB proof with the conclusion `BOUNDS -optimum : q -optimum` for the
knapsack formula and objective. No theorem says that the checker accepts the proof or that the
claimed optimum is right; when `Cslib.Logic.PL.VeriPB.checkRed` accepts the proof on an
instance, the claimed optimum is the optimum there
(`Cslib.Logic.PL.VeriPB.Knapsack.isGreatest_of_checkRed_certify`). -/
def certify (w p : Fin n → ℕ) (B : ℕ) : Certificate :=
  -- The solution is logged first, so its improving constraint is `2`; the rest starts at `3`.
  let (e, L₀) := mkLayer ⟨[], [], 0⟩ ⟨[], 3, n⟩ [⟨0, 0, []⟩]
  let u₀ := L₀.headD noNode
  let (e, alo₀) := e.rup (clause [(u₀.S, true)]) [.neg, .id u₀.wb, .id u₀.pb, .id u₀.sb]
  let X := ((List.finRange n).map fun i => (i.val, w i, p i)).foldl (step B)
    ⟨L₀, alo₀, ⟨[], [], 0⟩, e⟩
  let best := X.nodes.foldl (fun b u => if b.p < u.st.p then u.st else b) ⟨0, 0, []⟩
  let (e, ks) := X.nodes.foldl (fun (e, ks) u =>
    let (e, k) := e.pol [.id u.pf, .id 2, .add]; (e, k :: ks)) (X.acc, [])
  let (e, q) := e.rup ⟨[], 1⟩ (ks.map .id ++ X.nodes.map (.id ·.sf) ++ [.id X.alo])
  ⟨best.p, ⟨.soli ((List.finRange n).map fun i => (i.val, decide (i.val ∈ best.sel))) ::
      e.steps.reverse, .bounds (some (-best.p)) q (some (-best.p)) none⟩⟩

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
