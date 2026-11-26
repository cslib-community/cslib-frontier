/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.DynamicProgramming
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
the negated profit `∑ -pᵢ xᵢ` (`Cslib.Logic.PL.VeriPB.negProfit`). An assignment
satisfies the formula exactly when the items it takes fit
(`Cslib.Logic.PL.VeriPB.Knapsack.holds_capacity_iff`), its objective value is the negated profit
of those items (`Cslib.Logic.PL.VeriPB.eval_negProfit`), and every set of items is taken
by some assignment (`Cslib.Logic.PL.VeriPB.exists_chosen_eq`): the formula and objective encode
the problem (`Cslib.Logic.PL.VeriPB.Knapsack.encodes`). So a proof that the checker accepts with
the conclusion `BOUNDS lb : q ub` shows that the optimum lies in `[-ub, -lb]`
(`Cslib.Logic.PL.VeriPB.Encodes.bounds_of_checkRed`), and is `-lb` when `lb = ub`
(`Cslib.Logic.PL.VeriPB.Encodes.isGreatest_of_checkRed`). These statements hold for every proof,
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

* `Cslib.Logic.PL.VeriPB.Knapsack.capacity`, `Cslib.Logic.PL.VeriPB.Knapsack.formula`: the
  encoding, with the objective `Cslib.Logic.PL.VeriPB.negProfit`; an assignment takes the items
  `Cslib.Logic.PL.VeriPB.chosen n σ`, shared with the clique encoding.
* `Cslib.Logic.PL.VeriPB.Knapsack.certify`: the proof-logging dynamic program, which returns a
  `Cslib.Logic.PL.VeriPB.Certificate`: a claimed optimum and a candidate proof.

## Main results

* `Cslib.Logic.PL.VeriPB.Knapsack.holds_capacity_iff`, `Cslib.Logic.PL.VeriPB.Knapsack.encodes`:
  the encoding is correct, so an accepted proof bounds the optimum.
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

/-- **The knapsack encoding is correct**: the knapsack formula and the negated profit encode the
maximization of the profit over the sets of items that fit. With
`Cslib.Logic.PL.VeriPB.Encodes.isGreatest_of_checkRed`, a proof that the checker accepts with the
conclusion `BOUNDS lb : q lb` certifies the optimum `-lb`. -/
theorem encodes (w p : Fin n → ℕ) (B : ℕ) :
    Encodes (formula w B) (negProfit p) {S | ∑ i ∈ S, w i ≤ B} fun S => ∑ i ∈ S, (p i : ℤ) :=
  encodes_negProfit p fun σ => by simp [formula, holds_capacity_iff]

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

/-- The prefix sums of layer `i`: the terms `wⱼ xⱼ` and `pⱼ ¬xⱼ` of the items `j < i`, without
zero coefficients, and the total profit. -/
private structure Pre where
  wTerms : List (ℕ × Literal ℕ)
  pTerms : List (ℕ × Literal ℕ)
  pTot : ℕ

/-- Create the node of a state: reify `W ⇔ ∑ wⱼ xⱼ ≥ w`, `P ⇔ ∑ pⱼ ¬xⱼ ≥ ∑ pⱼ - p` and
`S ⇔ W + P ≥ 2`. -/
private def mkNode (pre : Pre) (e : ProofLog) (s : St) : ProofLog × Node :=
  let (e, a, wf, wb) := e.reify ⟨pre.wTerms, s.w⟩
  let (e, c, pf, pb) := e.reify ⟨pre.pTerms, pre.pTot - s.p⟩
  let (e, S, sf, sb) := e.reify ⟨[(1, (a, true)), (1, (c, true))], 2⟩
  (e, ⟨s, S, wf, wb, pf, pb, sf, sb⟩)

/-- Create the nodes of a layer. -/
private def mkLayer (pre : Pre) (e : ProofLog) (ss : List St) : ProofLog × List Node :=
  ss.foldl (fun (e, L) s => let (e, u) := mkNode pre e s; (e, u :: L)) (e, [])

/-- The node of the layer `L` that dominates the state `(w, p)`. -/
private def domNode (L : List Node) (w p : ℕ) : Node :=
  (L.find? fun t => decide (t.st.w ≤ w) && decide (p ≤ t.st.p)).getD noNode

/-- The transition implication `S_u ∧ x ⇒ S_t` (equations (11)–(13) and (17)–(19)), with the
numbers of the constraints it adds, the implication last. -/
private def transition (e : ProofLog) (u t : Node) (x : Literal ℕ) : ProofLog × List ℕ :=
  let (e, A) := e.pol [.id u.wf, .id t.wb, .add]
  let (e, P) := e.pol [.id u.pf, .id t.pb, .add]
  let (e, τ) := e.rup (Clause.toPB [(u.S, false), (x.1, !x.2), (t.S, true)])
    [.neg, .id u.sf, .id A, .id P, .id t.sb]
  (e, [A, P, τ])

/-- The transitions out of the node `u` for the item `j` of weight `wj` and profit `pj`, into the
layer `L`: returns the number of `S_u ⇒ ⋁ S_t` over the successors `t`, and the numbers of all the
constraints added. -/
private def successors (B j wj pj : ℕ) (L : List Node) (e : ProofLog) (u : Node) :
    ProofLog × ℕ × List ℕ :=
  let t₀ := domNode L u.st.w u.st.p
  let (e, ids₀) := transition e u t₀ (j, false)
  let τ₀ := ids₀.getLastD 0
  if u.st.w + wj ≤ B then
    let t₁ := domNode L (u.st.w + wj) (u.st.p + pj)
    let (e, ids₁) := transition e u t₁ (j, true)
    let τ₁ := ids₁.getLastD 0
    let ts := if t₀.S = t₁.S then [(t₀.S, true)] else [(t₁.S, true), (t₀.S, true)]
    let (e, c) := e.rup (Clause.toPB ((u.S, false) :: ts)) [.neg, .id τ₁, .id τ₀]
    (e, c, ids₀ ++ ids₁ ++ [c])
  else
    let (e, A) := e.pol [.id u.wf, .id 1, .add]
    let (e, τ₁) := e.rup (Clause.toPB [(u.S, false), (j, false)]) [.neg, .id u.sf, .id A]
    let (e, c) := e.rup (Clause.toPB [(u.S, false), (t₀.S, true)]) [.neg, .id τ₁, .id τ₀]
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
  acc : ProofLog

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
  let (e, alo) := e.rup (Clause.toPB (L.map fun t => (t.S, true)))
    (.neg :: cs.map .id ++ [.id X.alo])
  let dead := X.alo :: X.nodes.flatMap Node.ids ++ dead
  ⟨L, alo, pre, e.deld dead⟩

/-- **The proof-logging dynamic program** for the items of weights `w` and profits `p` and the
capacity `B`. It returns a claimed optimum, the largest profit in the last layer of the dynamic
program, and a candidate VeriPB proof with the conclusion `BOUNDS -optimum : q -optimum` for the
knapsack formula and objective. No theorem says that the checker accepts the proof or that the
claimed optimum is right; when `Cslib.Logic.PL.VeriPB.checkRed` accepts the proof on an
instance, the claimed optimum is the optimum there
(`Cslib.Logic.PL.VeriPB.Knapsack.isGreatest_of_checkRed_certify`). -/
def certify (w p : Fin n → ℕ) (B : ℕ) : Certificate ℕ :=
  -- The solution is logged first, so its improving constraint is `2`; the rest starts at `3`.
  let (e, L₀) := mkLayer ⟨[], [], 0⟩ ⟨[], 3, n⟩ [⟨0, 0, []⟩]
  let u₀ := L₀.headD noNode
  let (e, alo₀) := e.rup (Clause.toPB [(u₀.S, true)]) [.neg, .id u₀.wb, .id u₀.pb, .id u₀.sb]
  let X := ((List.finRange n).map fun i => (i.val, w i, p i)).foldl (step B)
    ⟨L₀, alo₀, ⟨[], [], 0⟩, e⟩
  let best := X.nodes.foldl (fun b u => if b.p < u.st.p then u.st else b) ⟨0, 0, []⟩
  let (e, ks) := X.nodes.foldl (fun (e, ks) u =>
    let (e, k) := e.pol [.id u.pf, .id 2, .add]; (e, k :: ks)) (X.acc, [])
  let (e, q) := e.rup ⟨[], 1⟩ (ks.map .id ++ X.nodes.map (.id ·.sf) ++ [.id X.alo])
  ⟨best.p, e.proof [.soli ((List.finRange n).map fun i => (i.val, decide (i.val ∈ best.sel)))]
      (.bounds (some (-best.p)) q (some (-best.p)) none)⟩

/-- **If the checker accepts the proof of the dynamic program, its answer is the optimum**: the
largest profit of a set of items that fits. -/
theorem isGreatest_of_checkRed_certify {w p : Fin n → ℕ} {B : ℕ}
    (h : checkRed (formula w B) (some (negProfit p)) (certify w p B).proof = true) :
    IsGreatest ((fun S : Finset (Fin n) => ∑ i ∈ S, p i) '' {S | ∑ i ∈ S, w i ≤ B})
      (certify w p B).optimum :=
  (encodes w p B).isGreatest_natCast_of_checkRed (fun _ => by push_cast; rfl) h rfl

end Cslib.Logic.PL.VeriPB.Knapsack

end
