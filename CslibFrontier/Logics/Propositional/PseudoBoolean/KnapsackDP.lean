/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.DynamicProgramming
public import CslibFrontier.Logics.Propositional.PseudoBoolean.RupComplete
-- `import all`: the acceptance proofs unfold `stepTop`, `runTop` and the reification steps.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Reification
import CslibFrontier.Logics.Propositional.PseudoBoolean.Fast
import Mathlib.Algebra.BigOperators.Fin

/-!
# The knapsack dynamic program and its proof log

The state-graph emitter shared by the certified knapsack
(`CslibFrontier.Logics.Propositional.PseudoBoolean.Knapsack`) and the knapsack propagator
(`CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackPropagator`), after §3 of
[Demirović, McCreesh, McIlree, Nordström, Oertel and
Sidorov][DemirovicMcCreeshMcIlreeNordstromOertelSidorov2024].
For `n` items of weights `w` and profits `p`, a capacity `C` and the domains of the items
(`Cslib.Logic.PL.VeriPB.Knapsack.Inst`), layer `i` holds states `(w, q)`: the weight taken and the
profit left out by the first `i` items. Two options (`Cslib.Logic.PL.VeriPB.Knapsack.Mode`) choose
the layers: merging the dominated states, those that weigh no less and leave out no less than
another, and pruning the transitions that overflow the capacity. The optimization uses both; the
propagator neither, its states being exact.

**The proof** (`Cslib.Logic.PL.VeriPB.Knapsack.Inst.forward`). Each node of layer `i` gets three
extension variables, by `Cslib.Logic.PL.VeriPB.reify`: `W ⇔ ∑_{j<i} wⱼ xⱼ ≥ w`,
`P ⇔ ∑_{j<i} pⱼ ¬xⱼ ≥ q` and `S ⇔ W + P ≥ 2` (equations (8)–(10) of the paper). For each node and
value `b` of its item, a kept transition goes to the node of the successor, or, with merging, to
one dominating it; it adds the forward halves of `W` and `P` to the backward halves of those of the
target and closes `S ∧ (xᵢ = b) ⇒ S'` by RUP (equations (11)–(13) and (17)–(19)). A pruned one adds
the forward half of `W` to the capacity constraint and derives `S ⇒ xᵢ ≠ b` (equations
(14)–(15)). Then `S ∧ D ⇒ ⋁ S'` follows by RUP (equations (16) and (20)), and the at-least-one
constraint `D ⇒ ⋁ S` of each layer from that of the layer before (equations (22)–(23)), `D` being
the literals that the domains fix.

**Acceptance is proved.** From a start state that numbers the capacity constraint `1` and some
constraint `2` (`Cslib.Logic.PL.VeriPB.Knapsack.Ctx`), the checker accepts the proof of the
forward pass on every instance, in both modes (`Cslib.Logic.PL.VeriPB.Knapsack.Inst.forward_spec`),
with the facts about every node, transition and layer that its clients use: each `rup` step is
accepted by the completeness of unit propagation on normalized constraints
(`CslibFrontier.Logics.Propositional.PseudoBoolean.RupComplete`), and each addition by the slacks of
the reification halves (`Cslib.Logic.PL.VeriPB.Knapsack.Inst.trans_dim`,
`Cslib.Logic.PL.VeriPB.Knapsack.Inst.prune_dim`).

## Main definitions

* `Cslib.Logic.PL.VeriPB.Knapsack.Inst`, `Cslib.Logic.PL.VeriPB.Knapsack.Mode`: the instance and
  the options.
* `Cslib.Logic.PL.VeriPB.Knapsack.Inst.layM`: the layers.
* `Cslib.Logic.PL.VeriPB.Knapsack.Inst.forward`: the forward pass and its proof.

## Main results

* `Cslib.Logic.PL.VeriPB.Knapsack.Inst.forward_spec`: the forward pass runs, with the facts about
  its layers.

## References

* [E. Demirović, C. McCreesh, M. J. McIlree, J. Nordström, A. Oertel, K. Sidorov, *Pseudo-Boolean
  Reasoning About States and Transitions to Certify Dynamic Programming and Decision Diagram
  Algorithms*][DemirovicMcCreeshMcIlreeNordstromOertelSidorov2024]
-/

public section

namespace Cslib.Logic.PL.VeriPB.Knapsack

open PBConstr

/-! ### The instance, ℕ-indexed -/

/-- A knapsack constraint with current domains, indexed by `ℕ`: `n` items of weights `w` and
profits `p`, the capacity `C`, the profit bound `P`, and the domain of each item, `none` when
free and `some b` when fixed to `b`. It is the instance on which the propagator
`Cslib.Logic.PL.VeriPB.Knapsack.propagate` runs. -/
structure Inst where
  /-- The number of items. -/
  n : ℕ
  /-- The weights. -/
  w : ℕ → ℕ
  /-- The profits. -/
  p : ℕ → ℕ
  /-- The capacity. -/
  C : ℕ
  /-- The profit bound. -/
  P : ℕ
  /-- The domains. -/
  dom : ℕ → Option Bool

/-- **The options of the dynamic program**: merge the dominated states (`dom`), and drop the
transitions that overflow the capacity (`prune`). The optimization of
`Cslib.Logic.PL.VeriPB.Knapsack.certify` uses both; the propagator
`Cslib.Logic.PL.VeriPB.Knapsack.propagate` uses neither, its states being exact. -/
structure Mode where
  /-- Merge the dominated states. -/
  dom : Bool
  /-- Drop the transitions that overflow the capacity. -/
  prune : Bool

/-- **Where the dynamic program starts**: the formula and objective of the run, the state reached
before the dynamic program's first step, and the constraint numbered `2` (the profit constraint of
the propagator, the objective-improving constraint of the optimization). -/
structure Ctx where
  /-- The formula. -/
  F : List PBConstr
  /-- The objective. -/
  obj : Option Objective
  /-- The start state. -/
  s₀ : State
  /-- The constraint numbered `2`. -/
  c₂ : PBConstr

/-- The ℕ-indexed instance of a knapsack constraint on `Fin n`, items outside `Fin n` absent. -/
def Inst.ofFin {n : ℕ} (w p : Fin n → ℕ) (C P : ℕ) (dom : Fin n → Option Bool) : Inst :=
  ⟨n, fun j => if h : j < n then w ⟨j, h⟩ else 0, fun j => if h : j < n then p ⟨j, h⟩ else 0, C,
    P, fun j => if h : j < n then dom ⟨j, h⟩ else none⟩

namespace Inst

variable (I : Inst)

/-- The values of a domain. -/
def vals : Option Bool → List Bool
  | none => [false, true]
  | some b => [b]

/-- `a` if `b = pol`, and `0` otherwise. -/
def bit (b pol : Bool) (a : ℕ) : ℕ := if b = pol then a else 0

/-- `∑_{j<i} aⱼ`. -/
def tot (a : ℕ → ℕ) (i : ℕ) : ℕ := ((List.range i).map a).sum

/-- `∑_{j<i} aⱼ [σ j = pol]`. -/
def part (σ : ℕ → Bool) (a : ℕ → ℕ) (pol : Bool) (i : ℕ) : ℕ :=
  ((List.range i).map fun j => bit (σ j) pol (a j)).sum

/-- The terms `aⱼ ℓⱼ` for `j < i` with `aⱼ > 0`, `ℓⱼ` the literal `(j, pol)`. -/
def sumTerms (a : ℕ → ℕ) (pol : Bool) (i : ℕ) : List (ℕ × Literal ℕ) :=
  (List.range i).filterMap fun j => if a j = 0 then none else some (a j, (j, pol))

/-- The partial sum constraint `∑_{j<i} aⱼ ℓⱼ ≥ d`. -/
def dimC (a : ℕ → ℕ) (pol : Bool) (i d : ℕ) : PBConstr := ⟨sumTerms a pol i, d⟩

/-- The capacity constraint `∑ wⱼ ¬xⱼ ≥ ∑ wⱼ - C`. -/
def capC : PBConstr :=
  ⟨(List.range I.n).map fun j => (I.w j, (j, false)), tot I.w I.n - I.C⟩

/-- A state: the weight taken so far and the profit left out so far. -/
abbrev St := ℕ × ℕ

/-- The successor of a state by the value `b` of item `i`. -/
def succSt (i : ℕ) (st : St) (b : Bool) : St :=
  (st.1 + bit b true (I.w i), st.2 + bit b false (I.p i))

/-- `t` dominates `s`: it weighs no more and leaves out no more profit. -/
def dominates (t s : St) : Bool := decide (t.1 ≤ s.1) && decide (t.2 ≤ s.2)

/-- Add the state `s` to a list of states none of which dominates another: drop `s` if a state
dominates it, and otherwise drop the states that `s` dominates. -/
private def insertSt (K : List St) (s : St) : List St :=
  if K.any (dominates · s) then K else s :: K.filter fun t => !dominates s t

/-- The transition by the value `b` out of the state `st` of layer `i` is kept: always without
pruning, and otherwise when it fits the capacity. -/
def keep (m : Mode) (i : ℕ) (st : St) (b : Bool) : Bool :=
  !m.prune || decide (st.1 + bit b true (I.w i) ≤ I.C)

/-- The successors kept out of the states `L` of layer `i`. -/
def cands (m : Mode) (i : ℕ) (L : List St) : List St :=
  L.flatMap fun st => ((vals (I.dom i)).filter (I.keep m i st)).map (I.succSt i st)

/-- The states of the next layer: the kept successors, without the dominated ones when `m.dom`,
and without repetitions otherwise. -/
def nextL (m : Mode) (i : ℕ) (L : List St) : List St :=
  if m.dom then (I.cands m i L).foldl insertSt [] else (I.cands m i L).dedup

/-- The states of layer `i`. -/
def layM (m : Mode) : ℕ → List St
  | 0 => [(0, 0)]
  | i + 1 => I.nextL m i (layM m i)

/-- The literals fixed by the domains. -/
def fixedLits : List (Literal ℕ) :=
  (List.range I.n).filterMap fun j => (I.dom j).map fun b => (j, b)

/-- Their negations, the antecedent of every derived implication. -/
def negD : List (Literal ℕ) := I.fixedLits.map Std.Sat.Literal.negate

end Inst

/-- The clause of a list of literals. -/
private def clause (ls : List (Literal ℕ)) : PBConstr := ⟨ls.map ((1, ·)), 1⟩

/-! ### The proof being written -/

/-- A node of the decision diagram: its state, its extension variables `W`, `P`, `S`, and the
numbers of the two halves of their reifications. -/
structure Node where
  /-- The state. -/
  st : ℕ × ℕ
  /-- The weight variable. -/
  W : ℕ
  /-- The profit variable. -/
  P : ℕ
  /-- The state variable. -/
  S : ℕ
  /-- The number of `W ⇒ …`. -/
  wf : ℕ
  /-- The number of `… ⇒ W`. -/
  wb : ℕ
  /-- The number of `P ⇒ …`. -/
  pf : ℕ
  /-- The number of `… ⇒ P`. -/
  pb : ℕ
  /-- The number of `S ⇒ W ∧ P`. -/
  sf : ℕ
  /-- The number of `W ∧ P ⇒ S`. -/
  sb : ℕ

/-- A placeholder node, never reached on the layers of the dynamic program. -/
private def noNode : Node := ⟨(0, 0), 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- A kept transition out of a node: the value of its item, the target node and the number of the
implication `S ∧ (x = b) ⇒ S'`. -/
structure Tr where
  /-- The value of the item. -/
  val : Bool
  /-- The target node. -/
  tgt : Node
  /-- The number of the implication. -/
  id : ℕ

/-- The transitions out of a node: for each kept value `b` of its item, the target node and the
number of the implication `S ∧ (x = b) ⇒ S'`; for every value, in order, the number of that
implication or, for a pruned value, of `S ⇒ x ≠ b`; and the number of `S ⇒ ⋁ S'`. -/
structure Out where
  /-- The node. -/
  u : Node
  /-- The kept transitions: value, target and implication. -/
  tr : List Tr
  /-- The implications for all values, in order. -/
  cls : List ℕ
  /-- The number of `S ⇒ ⋁ S'`. -/
  succ : ℕ

/-- A layer of the diagram: its index, nodes, transitions out (none for the last layer) and the
number of its at-least-one constraint. -/
structure LayerRec where
  /-- The index. -/
  i : ℕ
  /-- The nodes. -/
  nodes : List Node
  /-- The transitions out. -/
  outs : List Out
  /-- The number of the at-least-one constraint. -/
  alo : ℕ

/-- What the transitions out of a node leave: the proof, the kept transitions, and the numbers of
the implications for all values. -/
private structure T1 where
  /-- The proof. -/
  acc : ProofLog
  /-- The kept transitions. -/
  tr : List Tr
  /-- The numbers of the implications for all values. -/
  cls : List ℕ

/-- The entry for `S` of a list of pairs. -/
def dlook (dl : List (ℕ × ℕ)) (S : ℕ) : ℕ := ((dl.find? (·.1 == S)).map (·.2)).getD 0

/-- The node of a layer that a transition to the state `st` goes to: one with the state `st`, or,
when `m.dom`, one dominating it. -/
def tgt (m : Mode) (L : List Node) (st : ℕ × ℕ) : Node :=
  (L.find? fun t => if m.dom then Inst.dominates t.st st else t.st == st).getD noNode

/-- The target and the implication of a transition by the value `b`. -/
def Out.tgt (o : Out) (b : Bool) : Node := ((o.tr.find? (·.val == b)).map (·.tgt)).getD noNode

/-- The number of the implication of the transition by the value `b`. -/
def Out.tau (o : Out) (b : Bool) : ℕ := ((o.tr.find? (·.val == b)).map (·.id)).getD 0

namespace Inst

variable (I : Inst)

/-- The reified weight constraint `W ⇔ ∑_{j<i} wⱼ xⱼ ≥ w`. -/
def cW (i : ℕ) (st : St) : PBConstr := dimC I.w true i st.1

/-- The reified profit constraint `P ⇔ ∑_{j<i} pⱼ ¬xⱼ ≥ q`: the profit left out is at least `q`. -/
def cP (i : ℕ) (st : St) : PBConstr := dimC I.p false i st.2

/-- The state constraint `S ⇔ W + P ≥ 2`. -/
def cS (W P : ℕ) : PBConstr := ⟨[(1, (W, true)), (1, (P, true))], 2⟩

/-- The node of the state `st` created at `e`: variables from `e.var`, constraints from
`e.next`. -/
private def mkNode (e : ProofLog) (st : St) : Node :=
  ⟨st, e.var, e.var + 1, e.var + 2, e.next + 1, e.next + 3, e.next + 5, e.next + 7, e.next + 9,
    e.next + 11⟩

/-- The reifications of a node. -/
private def nodeSteps (i : ℕ) (u : Node) : List TopStep :=
  reify u.W (I.cW i u.st) ++ reify u.P (I.cP i u.st) ++ reify u.S (cS u.W u.P)

/-- Create the nodes of a layer. -/
private def mkLayer (i : ℕ) : ProofLog → List St → ProofLog × List Node
  | e, [] => (e, [])
  | e, st :: sts =>
    let u := mkNode e st
    let r := mkLayer i (e.push (I.nodeSteps i u) 12 3) sts
    (r.1, u :: r.2)

/-- The implication `S_u ∧ (xᵢ = b) ⇒ S_t`. -/
def trClause (i : ℕ) (u : Node) (b : Bool) (t : Node) : PBConstr :=
  clause [(u.S, false), (i, !b), (t.S, true)]

/-- The transition steps (equations (11)–(13) and (17)–(19) of the paper): add the forward
halves of `W_u` and `P_u` to the backward halves of `W_t` and `P_t`, then RUP. -/
private def trSteps (i : ℕ) (u : Node) (b : Bool) (t : Node) (e : ProofLog) : List TopStep :=
  [.step (.pol [.id u.wf, .id t.wb, .add]), .step (.pol [.id u.pf, .id t.pb, .add]),
    .step (.rup (trClause i u b t) [.neg, .id u.sf, .id e.next, .id (e.next + 1), .id t.sb])]

/-- The pruning steps (equations (14)–(15) of the paper): add the forward half of `W_u` to the
capacity constraint, then derive `S_u ⇒ xᵢ ≠ b` by RUP. -/
private def prSteps (i : ℕ) (u : Node) (b : Bool) (e : ProofLog) : List TopStep :=
  [.step (.pol [.id u.wf, .id 1, .add]),
    .step (.rup (clause [(u.S, false), (i, !b)]) [.neg, .id u.sf, .id e.next])]

/-- The transitions out of `u` into the layer `L'`, for the values `bs`: the kept transitions
with their targets, and the numbers of the implications for all values. -/
private def trans1 (m : Mode) (i : ℕ) (L' : List Node) (u : Node) : ProofLog → List Bool → T1
  | e, [] => ⟨e, [], []⟩
  | e, b :: bs =>
    if I.keep m i u.st b then
      let t := tgt m L' (I.succSt i u.st b)
      let r := trans1 m i L' u (e.push (trSteps i u b t e) 3 0) bs
      ⟨r.acc, ⟨b, t, e.next + 2⟩ :: r.tr, (e.next + 2) :: r.cls⟩
    else
      let r := trans1 m i L' u (e.push (prSteps i u b e) 2 0) bs
      ⟨r.acc, r.tr, (e.next + 1) :: r.cls⟩

/-- The negation of the domain literal of item `i`, if it is fixed. -/
private def fixNeg (i : ℕ) : List (Literal ℕ) := ((I.dom i).map fun b => (i, !b)).toList

/-- `S_u ∧ D ⇒ ⋁ S_t` over the targets of the transitions `tr`. -/
def succClause (i : ℕ) (u : Node) (tr : List Tr) : PBConstr :=
  clause ((u.S, false) :: I.fixNeg i ++ tr.map fun x => (x.tgt.S, true))

/-- The transitions out of `u`, then `S_u ⇒ ⋁ S_t` by RUP (equations (16) and (20)). -/
private def transOut (m : Mode) (i : ℕ) (L' : List Node) (e : ProofLog) (u : Node) :
    ProofLog × Out :=
  let r := I.trans1 m i L' u e (vals (I.dom i))
  (r.acc.push [.step (.rup (I.succClause i u r.tr) (.neg :: r.cls.map .id))] 1 0,
    ⟨u, r.tr, r.cls, r.acc.next⟩)

/-- The transitions out of a layer. -/
def trans (m : Mode) (i : ℕ) (L' : List Node) : ProofLog → List Node → ProofLog × List Out
  | e, [] => (e, [])
  | e, u :: us =>
    let r := I.transOut m i L' e u
    let q := trans m i L' r.1 us
    (q.1, r.2 :: q.2)

/-- The at-least-one constraint of a layer, under the domains: `D ⇒ ⋁ S_u`. -/
def aloClause (L : List Node) : PBConstr := clause (I.negD ++ L.map fun u => (u.S, true))

/-- The forward pass: from layer `i`, create `k` more layers with their transitions and
at-least-one constraints. The records are returned latest first. -/
def fwd (m : Mode) : ℕ → ℕ → ProofLog → List Node → ℕ → List LayerRec → ProofLog × List LayerRec
  | 0, i, e, L, alo, recs => (e, ⟨i, L, [], alo⟩ :: recs)
  | k + 1, i, e, L, alo, recs =>
    let r₁ := I.mkLayer (i + 1) e (I.nextL m i (L.map (·.st)))
    let r₂ := I.trans m i r₁.2 r₁.1 L
    let e' := r₂.1.push [.step (.rup (I.aloClause r₁.2)
      (.neg :: r₂.2.map (fun o => .id o.succ) ++ [.id alo]))] 1 0
    fwd m k (i + 1) e' r₁.2 r₂.1.next (⟨i, L, r₂.2, alo⟩ :: recs)

/-- **The forward pass from the start**: from the constraint number `3` and the variable `n`,
the node of layer `0`, its at-least-one constraint `D ⇒ S₀` by RUP, and the layers `1, …, n`.
The records are returned latest first. -/
def forward (m : Mode) : ProofLog × List LayerRec :=
  let r₀ := I.mkLayer 0 ⟨[], 3, I.n⟩ (I.layM m 0)
  let u₀ := r₀.2.headD noNode
  let e₁ := r₀.1.push [.step (.rup (I.aloClause r₀.2) [.neg, .id u₀.wb, .id u₀.pb, .id u₀.sb])]
    1 0
  I.fwd m I.n 0 e₁ r₀.2 r₀.1.next []

end Inst

/-! ### Semantics of the constraints -/

namespace Inst

variable (I : Inst)

theorem part_succ (σ : ℕ → Bool) (a : ℕ → ℕ) (pol : Bool) (i : ℕ) :
    part σ a pol (i + 1) = part σ a pol i + bit (σ i) pol (a i) := by
  simp [part, List.range_succ]

private theorem tot_succ (a : ℕ → ℕ) (i : ℕ) : tot a (i + 1) = tot a i + a i := by
  simp [tot, List.range_succ]

theorem part_add_part (σ : ℕ → Bool) (a : ℕ → ℕ) (pol : Bool) (i : ℕ) :
    part σ a pol i + part σ a (!pol) i = tot a i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [part_succ, part_succ, tot_succ, ← ih]
    cases h : σ i <;> cases pol <;> simp [bit] <;> omega

private theorem part_const (a : ℕ → ℕ) (pol : Bool) (i : ℕ) :
    part (fun _ => pol) a pol i = tot a i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [part_succ, tot_succ, ih]; simp [bit]

theorem lhs_sumTerms (σ : ℕ → Bool) (a : ℕ → ℕ) (pol : Bool) (i : ℕ) :
    lhs σ (sumTerms a pol i) = part σ a pol i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [part_succ, ← ih]
    simp only [sumTerms, List.range_succ, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil, lhs_append]
    split_ifs with h
    · simp [bit, h]
    · simp only [lhs_cons, lhs_nil, termVal, Literal.eval_mk, bit]
      cases σ i <;> cases pol <;> simp

theorem vars_sumTerms {a : ℕ → ℕ} {pol : Bool} {i x : ℕ}
    (h : x ∈ (sumTerms a pol i).map termVar) : x < i := by
  simp only [sumTerms, List.mem_map, List.mem_filterMap, List.mem_range] at h
  obtain ⟨t, ⟨j, hj, ht⟩, rfl⟩ := h
  split_ifs at ht
  cases ht
  simpa using hj

theorem nodup_sumTerms (a : ℕ → ℕ) (pol : Bool) (i : ℕ) :
    ((sumTerms a pol i).map termVar).Nodup := by
  induction i with
  | zero => simp [sumTerms]
  | succ i ih =>
    have : (sumTerms a pol (i + 1)) = sumTerms a pol i ++
        (if a i = 0 then [] else [(a i, (i, pol))]) := by
      simp only [sumTerms, List.range_succ, List.filterMap_append, List.filterMap_cons,
        List.filterMap_nil]
      split_ifs <;> rfl
    rw [this, List.map_append, List.nodup_append]
    refine ⟨ih, by split_ifs <;> simp, ?_⟩
    intro x hx y hy
    split_ifs at hy
    · simp at hy
    · simp only [List.map_cons, List.map_nil, List.mem_singleton, termVar_mk] at hy
      have := vars_sumTerms hx
      omega

theorem holds_dimC (σ : ℕ → Bool) (a : ℕ → ℕ) (pol : Bool) (i d : ℕ) :
    (dimC a pol i d).Holds σ ↔ d ≤ part σ a pol i := by
  simp [Holds, dimC, lhs_sumTerms]

private theorem holds_clause (σ : ℕ → Bool) (ls : List (Literal ℕ)) :
    (clause ls).Holds σ ↔ ∃ l ∈ ls, Literal.eval σ l = true := by
  simp only [clause, Holds, lhs, List.map_map]
  induction ls with
  | nil => simp
  | cons l ls ih =>
    simp only [List.map_cons, Function.comp_apply, List.sum_cons, List.mem_cons,
      exists_eq_or_imp]
    rw [← ih]
    cases h : Literal.eval σ l <;> simp [termVal, h]

theorem holds_cS (σ : ℕ → Bool) (W P : ℕ) :
    (cS W P).Holds σ ↔ σ W = true ∧ σ P = true := by
  simp only [cS, Holds, lhs_cons, lhs_nil, termVal, Literal.eval_mk]
  cases σ W <;> cases σ P <;> simp

/-- The negation of a clause holds when its literals are all false. -/
private theorem holds_negate_clause (σ : ℕ → Bool) (ls : List (Literal ℕ)) :
    (clause ls).negate.Holds σ → Consistent σ (ls.map Std.Sat.Literal.negate) := by
  rw [holds_negate, holds_clause]
  intro h l hl
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hl
  simp only [Literal.eval_negate, Bool.not_eq_true']
  by_contra h'
  exact h ⟨m, hm, by simpa using h'⟩

theorem consistent_append {σ : ℕ → Bool} {A B : List (Literal ℕ)} :
    Consistent σ (A ++ B) ↔ Consistent σ A ∧ Consistent σ B := by
  simp only [Consistent, List.mem_append]
  exact ⟨fun h => ⟨fun l hl => h l (.inl hl), fun l hl => h l (.inr hl)⟩,
    fun h l hl => hl.elim (h.1 l) (h.2 l)⟩

theorem mem_fixedLits {j : ℕ} {b : Bool} :
    (j, b) ∈ I.fixedLits ↔ j < I.n ∧ I.dom j = some b := by
  simp only [fixedLits, List.mem_filterMap, List.mem_range, Option.map_eq_some_iff,
    Prod.mk.injEq]
  constructor
  · rintro ⟨k, hk, b', hb', rfl, rfl⟩; exact ⟨hk, hb'⟩
  · rintro ⟨hj, hb⟩; exact ⟨j, hj, b, hb, rfl, rfl⟩

/-- Under the fixed literals, the negated domain literals are all false. -/
theorem eval_negD {σ : ℕ → Bool} (h : Consistent σ I.fixedLits) :
    ∀ l ∈ I.negD, Literal.eval σ l = false := by
  intro l hl
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hl
  simp [Literal.eval_negate, h m hm]

theorem negate_negD : I.negD.map Std.Sat.Literal.negate = I.fixedLits := by
  simp [negD, List.map_map, Function.comp_def, negate_negate]

private theorem vars_fixedLits {l : Literal ℕ} (h : l ∈ I.fixedLits) : l.1 < I.n := by
  obtain ⟨j, b⟩ := l
  exact ((I.mem_fixedLits).1 h).1

/-! ### The slacks of the reification halves -/

private theorem lhs_map_negate (σ : ℕ → Bool) (ts : List (ℕ × Literal ℕ)) :
    lhs σ (ts.map fun t => (t.1, Std.Sat.Literal.negate t.2)) + lhs σ ts = coeffSum ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨a, l⟩ := t
    rw [List.map_cons, lhs_cons, lhs_cons, coeffSum_cons]
    dsimp only
    have := termVal_add_negate σ a l
    omega

private theorem nodup_impl_single {l : Literal ℕ} {c : PBConstr} (hz : l.1 ∉ c.vars)
    (hd : (c.terms.map termVar).Nodup) : ((impl [l] c).terms.map termVar).Nodup := by
  simp only [impl, List.map_cons, List.map_nil, List.singleton_append, List.nodup_cons]
  refine ⟨?_, hd⟩
  obtain ⟨v, b⟩ := l
  simpa [Std.Sat.Literal.negate, PBConstr.vars] using hz

/-- The slack of `z ⇒ C`, as `reifyFwd` stores it. -/
theorem slack_fwd {z : ℕ} {c : PBConstr} (hz : z ∉ c.vars)
    (hd : (c.terms.map termVar).Nodup) (σ : ℕ → Bool) :
    (lhs σ (impl [(z, true)] c).normalize.terms : ℤ) - (impl [(z, true)] c).normalize.degree =
      (if σ z = true then 0 else (c.degree : ℤ)) + lhs σ c.terms - c.degree := by
  rw [slack_normalize (nodup_impl_single hz hd)]
  simp only [impl, List.map_cons, List.map_nil, List.singleton_append, lhs_cons, termVal,
    Std.Sat.Literal.negate, Literal.eval_mk]
  cases σ z <;> simp

/-- The slack of `C ⇒ z`, as `reifyBwd` stores it, for a satisfiable `C`. -/
private theorem slack_bwd {z : ℕ} {c : PBConstr} (hz : z ∉ c.vars)
    (hd : (c.terms.map termVar).Nodup) (hsat : ∃ τ, c.Holds τ) (σ : ℕ → Bool) :
    (lhs σ (impl [(z, false)] c.negate).normalize.terms : ℤ) -
        (impl [(z, false)] c.negate).normalize.degree =
      (if σ z = true then (c.negate.degree : ℤ) else 0) - ((lhs σ c.terms : ℤ) - c.degree) - 1 := by
  have hz' : z ∉ c.negate.vars := not_mem_vars_negate hz
  rw [slack_normalize (nodup_impl_single hz' (nodup_vars_negate c))]
  obtain ⟨τ, hτ⟩ := hsat
  have hle : c.normalize.degree ≤ coeffSum c.normalize.terms :=
    le_trans ((holds_normalize τ c).2 hτ) (lhs_le_coeffSum τ _)
  have hneg := lhs_map_negate σ c.normalize.terms
  have hsl := slack_normalize hd σ
  simp only [impl, List.map_cons, List.map_nil, List.singleton_append, lhs_cons, termVal,
    Std.Sat.Literal.negate, Literal.eval_mk]
  simp only [negate] at hneg ⊢
  cases σ z <;> simp <;> omega

/-- **The transition by addition** (equations (11)–(12) of the paper): the forward half of
`Z ⇔ ∑_{j<i} aⱼ ℓⱼ ≥ d` plus the backward half of `Z' ⇔ ∑_{j≤i} aⱼ ℓⱼ ≥ d'`, for the successor
`d'` of `d` by the value `b` of item `i`, gives `Z ∧ (xᵢ = b) ⇒ Z'`. -/
private theorem trans_dim {a : ℕ → ℕ} {pol b : Bool} {i d dt zu zt : ℕ} (hzu : i ≤ zu)
    (hzt : i + 1 ≤ zt) (hdt : dt ≤ d + bit b pol (a i)) (hd' : dt ≤ tot a (i + 1))
    {σ : ℕ → Bool}
    (hA : ((impl [(zu, true)] (dimC a pol i d)).normalize.add
      (impl [(zt, false)] (dimC a pol (i + 1) dt).negate).normalize).Holds σ)
    (hu : σ zu = true) (hx : σ i = b) : σ zt = true := by
  have h1 := slack_fwd (c := dimC a pol i d) (z := zu)
    (fun h => by have := vars_sumTerms h; omega) (nodup_sumTerms a pol i) σ
  have h2 := slack_bwd (c := dimC a pol (i + 1) dt) (z := zt)
    (fun h => by have := vars_sumTerms h; omega) (nodup_sumTerms a pol (i + 1))
    ⟨fun _ => pol, by rw [holds_dimC, part_const]; exact hd'⟩ σ
  rw [holds_add_iff] at hA
  simp only [dimC, lhs_sumTerms, part_succ, hx, hu, ite_true] at h1 h2 hA
  cases hz : σ zt
  · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h2
    omega
  · rfl

/-- **The refutation of a last-layer state by addition**, as in equations (14)–(15) of the
paper: the forward half of `Z ⇔ ∑_{j<n} aⱼ ℓⱼ ≥ d` plus a constraint `∑ aⱼ ¬ℓⱼ ≥ B` of the
formula gives `Z ⇒ d + B ≤ ∑ aⱼ`. -/
theorem final_dim {a : ℕ → ℕ} {pol : Bool} {m d z : ℕ} (hz : m ≤ z) {G : PBConstr}
    (hG : (G.terms.map termVar).Nodup) (hGl : ∀ σ, lhs σ G.terms = part σ a (!pol) m)
    {σ : ℕ → Bool} (hA : ((impl [(z, true)] (dimC a pol m d)).normalize.add G.normalize).Holds σ)
    (hu : σ z = true) : d + G.degree ≤ tot a m := by
  have h1 := slack_fwd (c := dimC a pol m d) (z := z)
    (fun h => by have := vars_sumTerms h; omega) (nodup_sumTerms a pol m) σ
  have h2 := slack_normalize hG σ
  have h3 := part_add_part σ a pol m
  rw [holds_add_iff] at hA
  simp only [dimC, lhs_sumTerms, hu, ite_true, hGl] at h1 h2 hA
  omega

end Inst

namespace Inst

variable (I : Inst) {X : Ctx}

/-! ### Running the proof -/

/-- The checker state with the database `db` and the next number `m`, all else as in the state
`X.s₀` where the dynamic program starts. -/
def state (X : Ctx) (db : List (ℕ × PBConstr)) (m : ℕ) : State :=
  { X.s₀ with db := db, next := m }

/-- The start state suits the dynamic program: no strengthening-to-core mode and no loaded order,
the core set over item variables, and every non-item variable free in the objective and the
preserved set. -/
structure CtxOk (X : Ctx) : Prop where
  /-- No strengthening-to-core mode. -/
  tcb : X.s₀.tcb = false
  /-- No loaded order. -/
  order : X.s₀.order = none
  /-- The core set is over item variables. -/
  core : ∀ x ∈ X.s₀.core, ∀ v ∈ x.2.vars, v < I.n
  /-- Every other variable is free in the objective, the preserved set and the order. -/
  avoid : ∀ v, I.n ≤ v → X.s₀.avoidsVar v = true

/-- **The proof so far runs** from the start state to the database `db`: the numbers of `db` are
below the next one, its variables below the next free one, which is not an item variable, the
capacity constraint is `1` and the constraint `X.c₂` is `2`. -/
def Run (X : Ctx) (e : ProofLog) (db : List (ℕ × PBConstr)) : Prop :=
  runTop X.F X.obj X.s₀ e.steps.reverse = some (state X db e.next) ∧
    (∀ x ∈ db, x.1 < e.next) ∧ (∀ x ∈ db, ∀ v ∈ x.2.vars, v < e.var) ∧ I.n ≤ e.var ∧
    lookup db 1 = some I.capC.normalize ∧ lookup db 2 = some X.c₂.normalize

/-- `db'` extends `db`. -/
def Sub (db db' : List (ℕ × PBConstr)) : Prop :=
  ∀ k c, lookup db k = some c → lookup db' k = some c

theorem Sub.refl (db : List (ℕ × PBConstr)) : Sub db db := fun _ _ h => h

theorem Sub.trans {a b c : List (ℕ × PBConstr)} (h₁ : Sub a b) (h₂ : Sub b c) : Sub a c :=
  fun k x h => h₂ k x (h₁ k x h)

private theorem runTop_append (F : List PBConstr) (obj : Option Objective) :
    ∀ (s : State) (a b : List TopStep),
      runTop F obj s (a ++ b) = (runTop F obj s a).bind fun s' => runTop F obj s' b
  | s, [], b => by simp [runTop_nil]
  | s, t :: a, b => by
    rw [List.cons_append, runTop_cons, runTop_cons]
    cases stepTop F obj s t with
    | none => rfl
    | some s' => exact runTop_append F obj s' a b

private theorem push_steps (e : ProofLog) (ss : List TopStep) (dn dv : ℕ) :
    (e.push ss dn dv).steps.reverse = e.steps.reverse ++ ss := by
  simp [ProofLog.push]

private theorem mem_of_lookup {db : List (ℕ × PBConstr)} {k : ℕ} {c : PBConstr}
    (h : lookup db k = some c) : (k, c) ∈ db := by
  simp only [lookup, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  have := List.mem_of_find?_eq_some hx
  have hk : x.1 = k := by simpa using List.find?_some hx
  rw [← hk]
  exact this

private theorem sub_cons {db : List (ℕ × PBConstr)} {m : ℕ} (hm : ∀ x ∈ db, x.1 < m)
    (c : PBConstr) : Sub db ((m, c) :: db) := by
  intro k d h
  have hk : k ≠ m := fun he => by have := hm _ (mem_of_lookup h); simp at this; omega
  simpa [lookup, List.find?_cons, Ne.symm hk, hk] using h

/-- The proof starts at `X.s₀`. -/
theorem run_start {X : Ctx} (h3 : X.s₀.next = 3) (hid : ∀ x ∈ X.s₀.db, x.1 < 3)
    (hv : ∀ x ∈ X.s₀.db, ∀ v ∈ x.2.vars, v < I.n)
    (h1 : lookup X.s₀.db 1 = some I.capC.normalize) (h2 : lookup X.s₀.db 2 = some X.c₂.normalize) :
    I.Run X ⟨[], 3, I.n⟩ X.s₀.db :=
  ⟨by simp only [List.reverse_nil, runTop_nil, state, ← h3], hid, hv, le_rfl, h1, h2⟩

/-- **A step that is not a deletion runs from any start state** `s₀`, adding the constraint `c`
at the next number: the numbers stay below the next one and the variables below the next free
one. -/
theorem runTop_push_step {F : List PBConstr} {obj : Option Objective} {s₀ : State}
    {e : ProofLog} {db : List (ℕ × PBConstr)}
    (hrun : runTop F obj s₀ e.steps.reverse = some { s₀ with db := db, next := e.next })
    (hid : ∀ x ∈ db, x.1 < e.next) (hvar : ∀ x ∈ db, ∀ v ∈ x.2.vars, v < e.var) {st : Step}
    (hst : ∀ ids, st ≠ .del ids) {c : PBConstr}
    (hr : runStep db e.next st = some ((e.next, c) :: db, e.next + 1))
    (hv : ∀ v ∈ c.vars, v < e.var) :
    runTop F obj s₀ (e.push [.step st] 1 0).steps.reverse =
        some { s₀ with db := (e.next, c) :: db, next := (e.push [.step st] 1 0).next } ∧
      (∀ x ∈ (e.next, c) :: db, x.1 < (e.push [.step st] 1 0).next) ∧
      ∀ x ∈ (e.next, c) :: db, ∀ v ∈ x.2.vars, v < (e.push [.step st] 1 0).var := by
  refine ⟨?_, ?_, ?_⟩
  · rw [push_steps, runTop_append, hrun, Option.bind_some, runTop_cons,
      stepTop_step_of_ne_del _ _ _ hst]
    simp [hr, runTop_nil, ProofLog.push]
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp [ProofLog.push]
    · have := hid x hx; simp [ProofLog.push]; omega
  · intro x hx v hv'
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simpa [ProofLog.push] using hv _ hv'
    · simpa [ProofLog.push] using hvar x hx v hv'

/-- **A step that is not a deletion runs** when it adds the constraint `c` at the next number. -/
theorem Run.step {e : ProofLog} {db : List (ℕ × PBConstr)} (h : I.Run X e db) {st : Step}
    (hst : ∀ ids, st ≠ .del ids) {c : PBConstr}
    (hr : runStep db e.next st = some ((e.next, c) :: db, e.next + 1))
    (hv : ∀ v ∈ c.vars, v < e.var) :
    I.Run X (e.push [.step st] 1 0) ((e.next, c) :: db) ∧ Sub db ((e.next, c) :: db) := by
  have hs := sub_cons h.2.1 c
  obtain ⟨h1, h2, h3⟩ := runTop_push_step h.1 h.2.1 h.2.2.1 hst hr hv
  exact ⟨⟨h1, h2, h3, by simpa [ProofLog.push] using h.2.2.2.1, hs _ _ h.2.2.2.2.1,
    hs _ _ h.2.2.2.2.2⟩, hs⟩

/-- **A `pol` step runs.** -/
theorem Run.pol {e : ProofLog} {db : List (ℕ × PBConstr)} (h : I.Run X e db) {ops : List PolOp}
    {c : PBConstr} (hp : polEval db ops [] = some [c]) (hv : ∀ v ∈ c.vars, v < e.var) :
    I.Run X (e.push [.step (.pol ops)] 1 0) ((e.next, c) :: db) ∧ Sub db ((e.next, c) :: db) :=
  Run.step I h (by intro ids h; cases h) (by simp [runStep, hp]) hv

/-- **A `rup` step runs** when the checker accepts it. -/
theorem Run.rup {e : ProofLog} {db : List (ℕ × PBConstr)} (h : I.Run X e db) {c : PBConstr}
    {hs : List Hint} (hr : rup db c hs = true) (hv : ∀ v ∈ c.vars, v < e.var) :
    I.Run X (e.push [.step (.rup c hs)] 1 0) ((e.next, c.normalize) :: db) ∧
      Sub db ((e.next, c.normalize) :: db) :=
  Run.step I h (by intro ids h; cases h) (by simp [runStep, hr])
    fun v hv' => hv _ (mem_vars_of_mem_vars_normalize hv')

private theorem vars_impl {l : Literal ℕ} {c : PBConstr} {x : ℕ} (h : x ∈ (impl [l] c).vars) :
    x = l.1 ∨ x ∈ c.vars := by
  obtain ⟨v, b⟩ := l
  simp only [PBConstr.vars, impl, List.map_cons, List.map_nil, List.singleton_append,
    List.mem_cons] at h
  rcases h with h | h
  · left; simpa [Std.Sat.Literal.negate] using h
  · right; exact h

/-- The database after a reification by the next free variable extends the one before. -/
theorem sub_reify {e : ProofLog} {db : List (ℕ × PBConstr)} (hid : ∀ x ∈ db, x.1 < e.next)
    (c : PBConstr) :
    Sub db ((e.next + 3, (impl [(e.var, false)] c.negate).normalize) ::
      (e.next + 1, (impl [(e.var, true)] c).normalize) :: db) :=
  (sub_cons (m := e.next + 1) (fun x hx => by have := hid x hx; omega) _).trans
    (sub_cons (fun x hx => by
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp
      · have := hid x hx; omega) _)

/-- **A reification by the next free variable runs from any start state** `s₀` without
strengthening-to-core mode, for a satisfiable constraint over older variables and a variable fresh
in the state. -/
theorem runTop_push_reify {F : List PBConstr} {obj : Option Objective} {s₀ : State}
    (htcb : s₀.tcb = false) {e : ProofLog} {db : List (ℕ × PBConstr)}
    (hrun : runTop F obj s₀ e.steps.reverse = some { s₀ with db := db, next := e.next })
    (hid : ∀ x ∈ db, x.1 < e.next) (hvar : ∀ x ∈ db, ∀ v ∈ x.2.vars, v < e.var) {c : PBConstr}
    (hv : ∀ v ∈ c.vars, v < e.var) (hsat : ∃ σ, c.Holds σ)
    (hfresh : ({ s₀ with db := db, next := e.next } : State).fresh e.var = true) :
    runTop F obj s₀ (e.push (reify e.var c) 4 1).steps.reverse =
        some { s₀ with
          db := ((e.next + 3, (impl [(e.var, false)] c.negate).normalize) ::
            (e.next + 1, (impl [(e.var, true)] c).normalize) :: db)
          next := (e.push (reify e.var c) 4 1).next } ∧
      (∀ x ∈ (e.next + 3, (impl [(e.var, false)] c.negate).normalize) ::
          (e.next + 1, (impl [(e.var, true)] c).normalize) :: db,
        x.1 < (e.push (reify e.var c) 4 1).next) ∧
      ∀ x ∈ (e.next + 3, (impl [(e.var, false)] c.negate).normalize) ::
          (e.next + 1, (impl [(e.var, true)] c).normalize) :: db,
        ∀ v ∈ x.2.vars, v < (e.push (reify e.var c) 4 1).var := by
  have hz : e.var ∉ c.vars := fun h' => by have := hv _ h'; omega
  have hnc : ¬ c.normalize.IsContradiction := fun hc => by
    obtain ⟨σ, hσ⟩ := hsat
    exact hc.not_holds σ ((holds_normalize σ c).2 hσ)
  refine ⟨?_, ?_, ?_⟩
  · rw [push_steps, runTop_append, hrun, Option.bind_some, runTop_reify hfresh hz hnc]
    simp [State.addStrengthened, htcb, ProofLog.push]
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · simp [ProofLog.push]
    · simp [ProofLog.push]
    · have := hid x hx; simp [ProofLog.push]; omega
  · intro x hx v hv'
    simp only [List.mem_cons] at hx
    simp only [ProofLog.push]
    rcases hx with rfl | rfl | hx
    · rcases vars_impl (mem_vars_of_mem_vars_normalize hv') with h' | h'
      · simp at h'; omega
      · have := hv _ (by_contra fun hx => not_mem_vars_negate hx h'); omega
    · rcases vars_impl (mem_vars_of_mem_vars_normalize hv') with h' | h'
      · simp at h'; omega
      · have := hv _ h'; omega
    · have := hvar x hx v hv'; omega

/-- **A reification by the next free variable runs**, for a satisfiable constraint over older
variables. -/
theorem Run.reify {e : ProofLog} {db : List (ℕ × PBConstr)} (hX : I.CtxOk X)
    (h : I.Run X e db) {c : PBConstr} (hv : ∀ v ∈ c.vars, v < e.var) (hsat : ∃ σ, c.Holds σ) :
    I.Run X (e.push (reify e.var c) 4 1)
        ((e.next + 3, (impl [(e.var, false)] c.negate).normalize) ::
          (e.next + 1, (impl [(e.var, true)] c).normalize) :: db) ∧
      Sub db ((e.next + 3, (impl [(e.var, false)] c.negate).normalize) ::
          (e.next + 1, (impl [(e.var, true)] c).normalize) :: db) := by
  obtain ⟨hrun, hid, hvar, hn, h1, h2⟩ := h
  have hsub := sub_reify hid c
  have hfresh : (state X db e.next).fresh e.var = true := by
    have hav := hX.avoid e.var hn
    simp only [State.fresh, Bool.and_eq_true, List.all_eq_true, List.mem_append]
    refine ⟨fun x hx => ?_, by simpa [State.avoidsVar, state] using hav⟩
    have : e.var ∉ x.2.vars := fun hm => by
      rcases hx with hx | hx
      · have := hvar x hx _ hm; omega
      · have := hX.core x hx _ hm; omega
    simpa using this
  obtain ⟨r1, r2, r3⟩ := runTop_push_reify hX.tcb hrun hid hvar hv hsat hfresh
  exact ⟨⟨r1, r2, r3, by simp [ProofLog.push]; omega, hsub _ _ h1, hsub _ _ h2⟩, hsub⟩

/-- **A derived constraint over preserved variables holds at every solution** of the formula: the
checker runs from `F` with the preserved set `pres` to a state with the same preserved set and no
logged solution, whose database holds `c`; the witnesses of `red` change only variables outside
`pres`. -/
theorem holds_of_runTop {F : List PBConstr} {pres : List ℕ} {steps : List TopStep} {s : State}
    (h : runTop F none (State.init F none (some pres)) steps = some s)
    (hpres : s.pres = some pres) (hpc : s.presChanged = false) (hlog : s.logged = []) {k : ℕ}
    {c : PBConstr}
    (hk : lookup s.db k = some c) (hv : ∀ x ∈ c.vars, x ∈ pres) {σ : ℕ → Bool}
    (hσ : ∀ c ∈ F, c.Holds σ) : c.Holds σ := by
  obtain ⟨-, he⟩ := invariants_of_runTop h
  obtain ⟨g, -, hmaps, hid⟩ := he.fwd 0 (.inr rfl)
  have hmem : proj pres σ ∈ proj ((some pres).getD []) '' solsLE F none 0 :=
    ⟨σ, ⟨hσ, by simp [objValue]⟩, rfl⟩
  rcases hmaps hmem with ⟨_, ⟨τ, ⟨hτ, -⟩, rfl⟩, hτσ⟩ | ⟨m, ⟨hm, -⟩, -⟩
  · have heq := hid hpc _ hmem _ hτσ.symm
    simp only [hpres, Option.getD_some] at heq
    refine (holds_congr fun t ht => ?_).2 (hτ.lookup hk)
    have hx : termVar t ∈ pres := hv _ (List.mem_map_of_mem ht)
    have := congrArg (fun l => l[(pres.idxOf (termVar t))]?) heq
    simp only [proj, List.getElem?_map, List.getElem?_idxOf hx, Option.map_some,
      Option.some.injEq] at this
    exact this.symm
  · simp [hlog] at hm

theorem push_push (e : ProofLog) (a b : List TopStep) (m k m' k' : ℕ) :
    (e.push a m k).push b m' k' = e.push (a ++ b) (m + m') (k + k') := by
  simp [ProofLog.push, Nat.add_assoc]

/-! ### Nodes -/

/-- The states of layer `i` weigh at most `∑_{j<i} wⱼ` and leave out at most `∑_{j<i} pⱼ`. -/
private theorem mem_insertSt {K : List St} {s t : St} (h : t ∈ insertSt K s) : t ∈ K ∨ t = s := by
  unfold insertSt at h
  split_ifs at h
  · exact .inl h
  · rcases List.mem_cons.1 h with rfl | h
    · exact .inr rfl
    · exact .inl (List.mem_filter.1 h).1

private theorem mem_foldl_insertSt :
    ∀ {L K : List St} {t : St}, t ∈ L.foldl insertSt K → t ∈ K ∨ t ∈ L
  | [], _, _, h => .inl h
  | s :: L, K, t, h => by
    rcases mem_foldl_insertSt (L := L) h with h | h
    · rcases mem_insertSt h with h | rfl
      · exact .inl h
      · exact .inr List.mem_cons_self
    · exact .inr (List.mem_cons_of_mem _ h)

/-- A state of the next layer is a kept successor of a state of the layer. -/
theorem mem_nextL {m : Mode} {i : ℕ} {L : List St} {t : St} (h : t ∈ I.nextL m i L) :
    ∃ st ∈ L, ∃ b ∈ vals (I.dom i), I.keep m i st b = true ∧ t = I.succSt i st b := by
  have hc : t ∈ I.cands m i L := by
    unfold nextL at h
    split_ifs at h
    · simpa using mem_foldl_insertSt h
    · exact List.mem_dedup.1 h
  simp only [cands, List.mem_flatMap, List.mem_map, List.mem_filter] at hc
  obtain ⟨st, hst, b, ⟨hb, hk⟩, rfl⟩ := hc
  exact ⟨st, hst, b, hb, hk, rfl⟩

/-- The states of layer `i` weigh at most `∑_{j<i} wⱼ` and leave out at most `∑_{j<i} pⱼ`. -/
private theorem le_tot_of_mem_layM {m : Mode} : ∀ {i : ℕ} {st : St}, st ∈ I.layM m i →
    st.1 ≤ tot I.w i ∧ st.2 ≤ tot I.p i
  | 0, st, h => by
    simp only [layM, List.mem_singleton] at h
    subst h; simp [tot]
  | i + 1, st, h => by
    obtain ⟨st₀, h₀, b, -, -, rfl⟩ := I.mem_nextL h
    have := le_tot_of_mem_layM h₀
    simp only [succSt, tot_succ, bit]
    split_ifs <;> simp_all <;> omega

/-- **The facts about a node** of layer `i` in the database `db`, its variables below `V`. -/
structure NodeOk (i : ℕ) (db : List (ℕ × PBConstr)) (V : ℕ) (u : Node) : Prop where
  /-- The state is within the totals. -/
  bnd : u.st.1 ≤ tot I.w i ∧ u.st.2 ≤ tot I.p i
  /-- `W` is not an item variable. -/
  nW : I.n ≤ u.W
  /-- `P` is not an item variable. -/
  nP : I.n ≤ u.P
  /-- `W` is below `V`. -/
  W : u.W < V
  /-- `P` is below `V`. -/
  P : u.P < V
  /-- `S` is below `V`. -/
  S : u.S < V
  /-- `W ⇒ …`. -/
  wf : lookup db u.wf = some (impl [(u.W, true)] (I.cW i u.st)).normalize
  /-- `… ⇒ W`. -/
  wb : lookup db u.wb = some (impl [(u.W, false)] (I.cW i u.st).negate).normalize
  /-- `P ⇒ …`. -/
  pf : lookup db u.pf = some (impl [(u.P, true)] (I.cP i u.st)).normalize
  /-- `… ⇒ P`. -/
  pb : lookup db u.pb = some (impl [(u.P, false)] (I.cP i u.st).negate).normalize
  /-- `S ⇒ W ∧ P`. -/
  sf : lookup db u.sf = some (impl [(u.S, true)] (cS u.W u.P)).normalize
  /-- `W ∧ P ⇒ S`. -/
  sb : lookup db u.sb = some (impl [(u.S, false)] (cS u.W u.P).negate).normalize

theorem NodeOk.mono {i : ℕ} {db db' : List (ℕ × PBConstr)} {V V' : ℕ} {u : Node}
    (h : I.NodeOk i db V u) (hs : Sub db db') (hV : V ≤ V') : I.NodeOk i db' V' u :=
  ⟨h.bnd, h.nW, h.nP, by have := h.W; omega, by have := h.P; omega, by have := h.S; omega,
    hs _ _ h.wf, hs _ _ h.wb, hs _ _ h.pf, hs _ _ h.pb, hs _ _ h.sf, hs _ _ h.sb⟩

private theorem vars_dimC {a : ℕ → ℕ} {pol : Bool} {i d x : ℕ} (h : x ∈ (dimC a pol i d).vars) :
    x < i := vars_sumTerms h

/-- **Creating a layer runs**, and gives nodes with their facts. -/
private theorem mkLayer_spec {i : ℕ} (hi : i ≤ I.n) : ∀ (sts : List St) (e : ProofLog)
    (db : List (ℕ × PBConstr)), I.CtxOk X → I.Run X e db →
    (∀ st ∈ sts, st.1 ≤ tot I.w i ∧ st.2 ≤ tot I.p i) →
    ∃ db', I.Run X (I.mkLayer i e sts).1 db' ∧ Sub db db' ∧
      (I.mkLayer i e sts).2.map (·.st) = sts ∧
      (∀ u ∈ (I.mkLayer i e sts).2, I.NodeOk i db' (I.mkLayer i e sts).1.var u) ∧
      e.var ≤ (I.mkLayer i e sts).1.var
  | [], e, db, _, h, _ => ⟨db, h, Sub.refl _, rfl, by simp [mkLayer], by simp [mkLayer]⟩
  | st :: sts, e, db, hX, h, hst => by
    have hb := hst st List.mem_cons_self
    have hn := h.2.2.2.1
    -- The three reifications.
    obtain ⟨h₁, s₁⟩ := Run.reify I hX h (c := I.cW i st)
      (fun v hv => by have := vars_dimC hv; omega)
      ⟨fun _ => true, by rw [cW, holds_dimC, part_const]; exact hb.1⟩
    obtain ⟨h₂, s₂⟩ := Run.reify I hX h₁ (c := I.cP i st)
      (fun v hv => by have := vars_dimC hv; simp [ProofLog.push]; omega)
      ⟨fun _ => false, by rw [cP, holds_dimC, part_const]; exact hb.2⟩
    obtain ⟨h₃, s₃⟩ := Run.reify I hX h₂ (c := cS e.var (e.var + 1))
      (fun v hv => by
        simp only [cS, PBConstr.vars, List.map_cons, List.map_nil, termVar_mk,
          List.mem_cons, List.not_mem_nil, or_false] at hv
        simp only [ProofLog.push]; omega)
      ⟨fun _ => true, by simp [cS, Holds, termVal]⟩
    have he : ((e.push (reify e.var (I.cW i st)) 4 1).push (reify (e.var + 1) (I.cP i st)) 4
        1).push (reify (e.var + 2) (cS e.var (e.var + 1))) 4 1 =
        e.push (I.nodeSteps i (mkNode e st)) 12 3 := by
      simp [push_push, nodeSteps, mkNode]
    have hv1 : (e.push (reify e.var (I.cW i st)) 4 1).var = e.var + 1 := rfl
    have hv2 : ((e.push (reify e.var (I.cW i st)) 4 1).push (reify (e.var + 1) (I.cP i st)) 4
        1).var = e.var + 2 := rfl
    rw [hv1] at h₃ s₃ h₂ s₂
    rw [hv2] at h₃ s₃
    have h₃' := h₃
    rw [he] at h₃'
    obtain ⟨db', hr, hs, hmap, hok, hv⟩ := mkLayer_spec hi sts _ _ hX h₃'
      (fun s hs => hst s (List.mem_cons_of_mem _ hs))
    refine ⟨db', hr, s₁.trans (s₂.trans (s₃.trans hs)), ?_, ?_, ?_⟩
    · simp only [mkLayer, List.map_cons, hmap]; rfl
    · simp only [mkLayer, List.mem_cons]
      rintro u (rfl | hu)
      · have hv' := le_trans
          (by simp [ProofLog.push] : e.var + 3 ≤ (e.push (I.nodeSteps i (mkNode e st)) 12 3).var) hv
        simp only [mkNode] at hv' ⊢
        refine ⟨hb, hn, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
          by dsimp only; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        · refine hs _ _ ?_
          simp (disch := omega) only [ProofLog.push, lookup_cons, ite_eq_right, ↓reduceIte]
      · exact hok u hu
    · simp only [mkLayer]; exact le_trans (by simp [ProofLog.push]) hv

/-! ### Reverse unit propagation on clauses and on the database -/

/-- A `rup` step for a clause starts from the negations of its literals. -/
private theorem rup_clause {db : List (ℕ × PBConstr)} {ls : List (Literal ℕ)} {hs : List Hint}
    (h : RupOk db (clause ls).negate hs (ls.map Std.Sat.Literal.negate ++ [])) :
    rup db (clause ls) (.neg :: hs) = true :=
  rup_of_rupOk (RupOk.imp rfl (nodup_vars_negate _)
    (fun σ _ hc => holds_negate_clause σ ls hc) h)

private theorem RupOk.id_imp {db : List (ℕ × PBConstr)} {neg c : PBConstr} {k : ℕ}
    {hs : List Hint} {K L : List (Literal ℕ)} (hk : lookup db k = some c)
    (hd : (c.terms.map termVar).Nodup) (hi : ∀ σ, Consistent σ K → c.Holds σ → Consistent σ L)
    (hrest : RupOk db neg hs (L ++ K)) : RupOk db neg (.id k :: hs) K :=
  RupOk.imp hk hd hi hrest

private theorem RupOk.id_conflict {db : List (ℕ × PBConstr)} {neg c : PBConstr} {k : ℕ}
    {hs : List Hint} {K : List (Literal ℕ)} (hk : lookup db k = some c)
    (hd : (c.terms.map termVar).Nodup) (hi : ∀ σ, Consistent σ K → ¬ c.Holds σ) :
    RupOk db neg (.id k :: hs) K :=
  RupOk.conflict hk hd hi

theorem lit_of {σ : ℕ → Bool} {K : List (Literal ℕ)} (h : Consistent σ K) {v : ℕ}
    {b : Bool} (hl : (v, b) ∈ K) : σ v = b := by
  simpa using h _ hl

theorem vars_of_lookup {e : ProofLog} {db : List (ℕ × PBConstr)} (h : I.Run X e db) {k : ℕ}
    {c : PBConstr} (hk : lookup db k = some c) : ∀ v ∈ c.vars, v < e.var :=
  fun v hv => h.2.2.1 _ (mem_of_lookup hk) v hv

theorem vars_add {c d : PBConstr} {x : ℕ} (h : x ∈ (c.add d).vars) :
    x ∈ c.vars ∨ x ∈ d.vars := by
  have := mem_vars_of_mem_vars_normalize h
  simpa [PBConstr.vars] using this

theorem polEval_add {db : List (ℕ × PBConstr)} {a b : ℕ} {c d : PBConstr}
    (ha : lookup db a = some c) (hb : lookup db b = some d) :
    polEval db [.id a, .id b, .add] [] = some [c.add d] := by
  simp [polEval, ha, hb]

/-- A `pol` step adding two constraints of the database runs. -/
theorem Run.add {e : ProofLog} {db : List (ℕ × PBConstr)} (h : I.Run X e db) {a b : ℕ}
    {c d : PBConstr} (ha : lookup db a = some c) (hb : lookup db b = some d) :
    I.Run X (e.push [.step (.pol [.id a, .id b, .add])] 1 0) ((e.next, c.add d) :: db) ∧
      Sub db ((e.next, c.add d) :: db) :=
  Run.pol I h (polEval_add ha hb) fun v hv => (vars_add hv).elim
    (I.vars_of_lookup h ha v) (I.vars_of_lookup h hb v)

private theorem vars_clause {ls : List (Literal ℕ)} {x : ℕ} (h : x ∈ (clause ls).vars) :
    ∃ l ∈ ls, l.1 = x := by
  simpa [clause, PBConstr.vars, List.map_map] using h

theorem vars_negD {l : Literal ℕ} (h : l ∈ I.negD) : l.1 < I.n := by
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h
  obtain ⟨v, b⟩ := m
  simpa [Std.Sat.Literal.negate] using I.vars_fixedLits hm

/-! ### Transitions -/

/-- **A transition runs** (equations (11)–(13) and (17)–(19) of the paper): from a node `u` of
layer `i` by the value `b` to its successor `t`, the two additions and the RUP step derive
`S_u ∧ (xᵢ = b) ⇒ S_t`. -/
private theorem trSteps_spec {i : ℕ} (hi : i < I.n) {e : ProofLog} {db : List (ℕ × PBConstr)}
    (h : I.Run X e db) {u t : Node} {b : Bool} (hu : I.NodeOk i db e.var u)
    (ht : I.NodeOk (i + 1) db e.var t) (hst₁ : t.st.1 ≤ (I.succSt i u.st b).1)
    (hst₂ : t.st.2 ≤ (I.succSt i u.st b).2) :
    ∃ db', I.Run X (e.push (trSteps i u b t e) 3 0) db' ∧ Sub db db' ∧
      lookup db' (e.next + 2) = some (trClause i u b t).normalize := by
  obtain ⟨h₁, s₁⟩ := Run.add I h hu.wf ht.wb
  obtain ⟨h₂, s₂⟩ := Run.add I h₁ (s₁ _ _ hu.pf) (s₁ _ _ ht.pb)
  have hb := ht.bnd
  set cA := (impl [(u.W, true)] (I.cW i u.st)).normalize.add
    (impl [(t.W, false)] (I.cW (i + 1) t.st).negate).normalize with hcA
  set cP' := (impl [(u.P, true)] (I.cP i u.st)).normalize.add
    (impl [(t.P, false)] (I.cP (i + 1) t.st).negate).normalize with hcP
  have hlookA : lookup ((e.next + 1, cP') :: (e.next, cA) :: db) e.next = some cA := by
    simp (disch := omega) only [lookup_cons, ite_eq_right, ↓reduceIte]
  have hlookP : lookup ((e.next + 1, cP') :: (e.next, cA) :: db) (e.next + 1) = some cP' :=
    ((lookup_cons _ _ _ _).trans (ite_eq_left rfl))
  have hr : rup ((e.next + 1, cP') :: (e.next, cA) :: db)
      (trClause i u b t) [.neg, .id u.sf, .id e.next, .id (e.next + 1), .id t.sb] = true := by
    refine rup_clause ?_
    simp only [List.map_cons, List.map_nil, Std.Sat.Literal.negate, Bool.not_not,
      Bool.not_false, Bool.not_true, List.append_nil]
    refine RupOk.id_imp (L := [(u.W, true), (u.P, true)]) (s₂ _ _ (s₁ _ _ hu.sf))
      (nodup_termVar_normalize _) ?_ ?_
    · intro σ hσ hc
      rw [holds_normalize, holds_impl] at hc
      have := (holds_cS σ _ _).1 (hc (by simp [lit_of hσ (v := u.S) (b := true) (by simp)]))
      simp [Consistent, this]
    refine RupOk.id_imp (L := [(t.W, true)]) hlookA (nodup_termVar_normalize _) ?_ ?_
    · intro σ hσ hc
      have := trans_dim (a := I.w) (pol := true) (b := b) (i := i) (d := u.st.1) (zu := u.W)
        (zt := t.W) (by have := hu.nW; omega) (by have := ht.nW; omega) hst₁ hb.1
        (by rw [hcA] at hc; simp only [cW] at hc; exact hc)
        (lit_of hσ (by simp)) (lit_of hσ (by simp))
      simp [Consistent, this]
    refine RupOk.id_imp (L := [(t.P, true)]) hlookP (nodup_termVar_normalize _) ?_ ?_
    · intro σ hσ hc
      have := trans_dim (a := I.p) (pol := false) (b := b) (i := i) (d := u.st.2) (zu := u.P)
        (zt := t.P) (by have := hu.nP; omega) (by have := ht.nP; omega) hst₂ hb.2
        (by rw [hcP] at hc; simp only [cP] at hc; exact hc)
        (lit_of hσ (by simp)) (lit_of hσ (by simp))
      simp [Consistent, this]
    refine RupOk.id_conflict (s₂ _ _ (s₁ _ _ ht.sb)) (nodup_termVar_normalize _) ?_
    intro σ hσ hc
    rw [holds_normalize, holds_impl_neg_negate] at hc
    have h1 := hc ((holds_cS σ _ _).2 ⟨lit_of hσ (by simp), lit_of hσ (by simp)⟩)
    have h2 := lit_of hσ (v := t.S) (b := false) (by simp)
    simp [h1] at h2
  obtain ⟨h₃, s₃⟩ := Run.rup I h₂ hr (fun v hv => by
    obtain ⟨l, hl, rfl⟩ := vars_clause hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    simp only [ProofLog.push]
    rcases hl with rfl | rfl | rfl
    · exact hu.S
    · simp; have := h.2.2.2.1; omega
    · exact ht.S)
  refine ⟨_, ?_, s₁.trans (s₂.trans s₃), ?_⟩
  · rw [push_push, push_push] at h₃; simpa [trSteps] using h₃
  · simp [ProofLog.push, lookup_cons]

/-- The layer `L` has a node that a transition to `st` may go to: one with the state `st`, or,
when `m.dom`, one dominating it. -/
def Cover (m : Mode) (L : List Node) (st : St) : Prop :=
  ∃ t ∈ L, (if m.dom then dominates t.st st else t.st == st) = true

private theorem tgt_spec {m : Mode} {L : List Node} {st : St} (h : Cover m L st) :
    tgt m L st ∈ L ∧ (tgt m L st).st.1 ≤ st.1 ∧ (tgt m L st).st.2 ≤ st.2 ∧
      (m.dom = false → (tgt m L st).st = st) := by
  obtain ⟨t, ht, hp⟩ := h
  rcases hf : L.find? (fun t => if m.dom then dominates t.st st else t.st == st) with _ | t'
  · exact absurd (List.find?_eq_none.1 hf t ht) (by simp [hp])
  · have hp' := List.find?_some hf
    have hmem := List.mem_of_find?_eq_some hf
    have ht' : tgt m L st = t' := by simp only [tgt]; rw [hf]; rfl
    rw [ht']
    refine ⟨hmem, ?_⟩
    cases hm : m.dom
    · simp only [hm, Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at hp'
      simp [hp']
    · simp only [hm, ↓reduceIte, dominates, Bool.and_eq_true, decide_eq_true_eq] at hp'
      simp [hp']

/-- The capacity constraint holds at `σ` exactly as computed. -/
theorem lhs_range (σ : ℕ → Bool) (a : ℕ → ℕ) (pol : Bool) (m : ℕ) :
    lhs σ ((List.range m).map fun j => (a j, (j, pol))) = part σ a pol m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [part_succ, ← ih]
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, lhs_append,
      lhs_cons, lhs_nil, termVal, Literal.eval_mk, bit]
    cases σ m <;> cases pol <;> simp

theorem nodup_range (a : ℕ → ℕ) (pol : Bool) (m : ℕ) :
    (((List.range m).map fun j => (a j, (j, pol))).map termVar).Nodup := by
  simpa [List.map_map, Function.comp_def] using List.nodup_range

private theorem part_mono (σ : ℕ → Bool) (a : ℕ → ℕ) (pol : Bool) {i m : ℕ} (h : i ≤ m) :
    part σ a pol i ≤ part σ a pol m := by
  induction m with
  | zero => rw [Nat.le_zero.1 h]
  | succ m ih =>
    rcases Nat.lt_or_ge i (m + 1) with h' | h'
    · have := ih (by omega); rw [part_succ]; omega
    · rw [show i = m + 1 by omega]

/-- **A pruned transition by addition** (equations (14)–(15) of the paper): the forward half of
`W ⇔ ∑_{j<i} wⱼ xⱼ ≥ d` plus the capacity constraint gives `W ∧ (xᵢ = b) ⇒ d + wᵢ [b] ≤ C`. -/
private theorem prune_dim {i d z : ℕ} (hi : i < I.n) (hz : I.n ≤ z) (hd : d ≤ tot I.w i)
    {σ : ℕ → Bool} {b : Bool}
    (hA : ((impl [(z, true)] (dimC I.w true i d)).normalize.add I.capC.normalize).Holds σ)
    (hu : σ z = true) (hx : σ i = b) : d + bit b true (I.w i) ≤ I.C := by
  have h1 := slack_fwd (c := dimC I.w true i d) (z := z)
    (fun h => by have := vars_sumTerms h; omega) (nodup_sumTerms I.w true i) σ
  have h2 := slack_normalize (c := I.capC) (nodup_range I.w false I.n) σ
  have h3 := part_add_part σ I.w true I.n
  have h4 := part_mono σ I.w true (show i + 1 ≤ I.n by omega)
  have h5 : tot I.w (i + 1) ≤ tot I.w I.n := by
    have := part_mono (fun _ => true) I.w true (show i + 1 ≤ I.n by omega)
    rwa [part_const, part_const] at this
  rw [part_succ, hx] at h4
  rw [holds_add_iff] at hA
  simp only [dimC, lhs_sumTerms, hu, ite_true, capC, lhs_range] at h1 h2 hA
  simp only [Bool.not_true] at h3
  rw [tot_succ] at h5
  cases b <;> simp only [bit, Bool.false_eq_true, ↓reduceIte] at h4 ⊢ <;> omega

/-- **A pruned transition runs**: the addition and the RUP step derive `S_u ⇒ xᵢ ≠ b`. -/
private theorem prSteps_spec {m : Mode} {i : ℕ} (hi : i < I.n) {e : ProofLog}
    {db : List (ℕ × PBConstr)}
    (h : I.Run X e db) {u : Node} {b : Bool} (hu : I.NodeOk i db e.var u)
    (hk : I.keep m i u.st b = false) :
    ∃ db', I.Run X (e.push (prSteps i u b e) 2 0) db' ∧ Sub db db' ∧
      lookup db' (e.next + 1) = some (clause [(u.S, false), (i, !b)]).normalize := by
  have hC : I.C < u.st.1 + bit b true (I.w i) := by
    simp only [keep, Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_false_iff_not] at hk
    omega
  obtain ⟨h₁, s₁⟩ := Run.add I h hu.wf h.2.2.2.2.1
  have hr : rup ((e.next, (impl [(u.W, true)] (I.cW i u.st)).normalize.add I.capC.normalize) :: db)
      (clause [(u.S, false), (i, !b)]) [.neg, .id u.sf, .id e.next] = true := by
    refine rup_clause ?_
    simp only [List.map_cons, List.map_nil, Std.Sat.Literal.negate, Bool.not_not,
      Bool.not_false, List.append_nil]
    refine RupOk.id_imp (L := [(u.W, true), (u.P, true)]) (s₁ _ _ hu.sf)
      (nodup_termVar_normalize _) ?_ ?_
    · intro σ hσ hc
      rw [holds_normalize, holds_impl] at hc
      have := (holds_cS σ _ _).1 (hc (by simp [lit_of hσ (v := u.S) (b := true) (by simp)]))
      simp [Consistent, this]
    refine RupOk.id_conflict ((lookup_cons _ _ _ _).trans (ite_eq_left rfl))
      (nodup_termVar_normalize _) fun σ hσ hc => ?_
    have := I.prune_dim (b := b) hi hu.nW hu.bnd.1 hc (lit_of hσ (by simp)) (lit_of hσ (by simp))
    omega
  obtain ⟨h₂, s₂⟩ := Run.rup I h₁ hr (fun v hv => by
    obtain ⟨l, hl, rfl⟩ := vars_clause hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    simp only [ProofLog.push]
    rcases hl with rfl | rfl
    · exact hu.S
    · simp; have := h.2.2.2.1; omega)
  refine ⟨_, ?_, s₁.trans s₂, ?_⟩
  · rw [push_push] at h₂; simpa [prSteps] using h₂
  · simp [ProofLog.push, lookup_cons]

theorem holds_trClause {σ : ℕ → Bool} {i : ℕ} {u t : Node} {b : Bool} :
    (trClause i u b t).normalize.Holds σ ↔
      (σ u.S = true → σ i = b → σ t.S = true) := by
  rw [holds_normalize, trClause, holds_clause]
  cases hu : σ u.S <;> cases hi : σ i <;> cases ht : σ t.S <;> cases b <;> simp [hu, hi, ht]

/-- The facts about the implication number `k` for the value `b` out of `u`: it makes some
target of the kept transitions `tr` true when `S_u` and `xᵢ = b` are. -/
def ClsOk (i : ℕ) (db : List (ℕ × PBConstr)) (u : Node) (tr : List Tr) (b : Bool)
    (k : ℕ) : Prop :=
  ∃ c, lookup db k = some c ∧ (c.terms.map termVar).Nodup ∧
    ∀ σ, c.Holds σ → σ u.S = true → σ i = b → ∃ x ∈ tr, σ x.tgt.S = true

/-- The facts about a kept transition out of `u` into `L'`. -/
def TrOk (m : Mode) (i : ℕ) (db : List (ℕ × PBConstr)) (L' : List Node) (u : Node)
    (x : Tr) : Prop :=
  x.tgt ∈ L' ∧ x.tgt.st.1 ≤ (I.succSt i u.st x.val).1 ∧ x.tgt.st.2 ≤ (I.succSt i u.st x.val).2 ∧
    (m.dom = false → x.tgt.st = I.succSt i u.st x.val) ∧
    lookup db x.id = some (trClause i u x.val x.tgt).normalize

private theorem trans1_spec {m : Mode} {i : ℕ} (hi : i < I.n) {L' : List Node} {u : Node} :
    ∀ (bs : List Bool) (e : ProofLog) (db : List (ℕ × PBConstr)), I.Run X e db →
      I.NodeOk i db e.var u → (∀ t ∈ L', I.NodeOk (i + 1) db e.var t) →
      (∀ b ∈ bs, I.keep m i u.st b = true → Cover m L' (I.succSt i u.st b)) →
      ∃ db', I.Run X (I.trans1 m i L' u e bs).acc db' ∧ Sub db db' ∧
        (I.trans1 m i L' u e bs).tr.map (·.val) = bs.filter (I.keep m i u.st) ∧
        (∀ x ∈ (I.trans1 m i L' u e bs).tr, I.TrOk m i db' L' u x) ∧
        (I.trans1 m i L' u e bs).cls.length = bs.length ∧
        (∀ p ∈ bs.zip (I.trans1 m i L' u e bs).cls,
          ClsOk i db' u (I.trans1 m i L' u e bs).tr p.1 p.2) ∧
        (I.trans1 m i L' u e bs).acc.var = e.var
  | [], e, db, h, _, _, _ => ⟨db, h, Sub.refl _, rfl, by simp [trans1], rfl, by simp [trans1],
      rfl⟩
  | b :: bs, e, db, h, hu, hL', hbs => by
    by_cases hk : I.keep m i u.st b = true
    · obtain ⟨htm, hts₁, hts₂, hex⟩ := tgt_spec (hbs b List.mem_cons_self hk)
      obtain ⟨db₁, h₁, s₁, hl₁⟩ := I.trSteps_spec hi h hu (hL' _ htm) hts₁ hts₂
      obtain ⟨db', h', s', hmap, hall, hlen, hcls, hv⟩ := trans1_spec hi bs _ db₁ h₁
        (hu.mono I s₁ (by simp [ProofLog.push]))
        (fun t ht => (hL' t ht).mono I s₁ (by simp [ProofLog.push]))
        (fun b hb => hbs b (List.mem_cons_of_mem _ hb))
      simp only [trans1, hk, ↓reduceIte]
      refine ⟨db', h', s₁.trans s', by simp [hmap, hk], ?_, by simp [hlen], ?_,
        by rw [hv]; rfl⟩
      · simp only [List.mem_cons]
        rintro x (rfl | hx)
        · exact ⟨htm, hts₁, hts₂, hex, s' _ _ hl₁⟩
        · exact hall x hx
      · simp only [List.zip_cons_cons, List.mem_cons]
        rintro p (rfl | hp)
        · refine ⟨_, s' _ _ hl₁, nodup_termVar_normalize _, fun σ hc hS hx => ?_⟩
          exact ⟨_, List.mem_cons_self, holds_trClause.1 hc hS hx⟩
        · obtain ⟨c, hc, hnd, hsem⟩ := hcls p hp
          exact ⟨c, hc, hnd, fun σ hσ hS hx => by
            obtain ⟨x, hx, hx'⟩ := hsem σ hσ hS hx
            exact ⟨x, List.mem_cons_of_mem _ hx, hx'⟩⟩
    · have hk' : I.keep m i u.st b = false := by simpa using hk
      obtain ⟨db₁, h₁, s₁, hl₁⟩ := I.prSteps_spec hi h hu hk'
      obtain ⟨db', h', s', hmap, hall, hlen, hcls, hv⟩ := trans1_spec hi bs _ db₁ h₁
        (hu.mono I s₁ (by simp [ProofLog.push]))
        (fun t ht => (hL' t ht).mono I s₁ (by simp [ProofLog.push]))
        (fun b hb => hbs b (List.mem_cons_of_mem _ hb))
      simp only [trans1, hk', Bool.false_eq_true, ↓reduceIte]
      refine ⟨db', h', s₁.trans s', by simp [hmap, hk'], hall, by simp [hlen], ?_,
        by rw [hv]; rfl⟩
      simp only [List.zip_cons_cons, List.mem_cons]
      rintro p (rfl | hp)
      · refine ⟨_, s' _ _ hl₁, nodup_termVar_normalize _, fun σ hc hS hx => ?_⟩
        rw [holds_normalize, holds_clause] at hc
        simp [hS, hx] at hc
      · exact hcls p hp

/-- **The facts about the transitions out of a node** of layer `i` into the layer `L'`. -/
structure OutOk (m : Mode) (i : ℕ) (db : List (ℕ × PBConstr)) (V : ℕ) (L' : List Node)
    (o : Out) : Prop where
  /-- The node's facts. -/
  u : I.NodeOk i db V o.u
  /-- The kept values. -/
  vals : o.tr.map (·.val) = (vals (I.dom i)).filter (I.keep m i o.u.st)
  /-- The kept transitions' facts. -/
  tr : ∀ x ∈ o.tr, I.TrOk m i db L' o.u x
  /-- `S ⇒ ⋁ S'`. -/
  succ : lookup db o.succ = some (I.succClause i o.u o.tr).normalize

theorem OutOk.mono {m : Mode} {i : ℕ} {db db' : List (ℕ × PBConstr)} {V V' : ℕ}
    {L' : List Node} {o : Out} (h : I.OutOk m i db V L' o) (hs : Sub db db') (hV : V ≤ V') :
    I.OutOk m i db' V' L' o :=
  ⟨h.u.mono I hs hV, h.vals, fun x hx => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := h.tr x hx
    exact ⟨h1, h2, h3, h4, hs _ _ h5⟩, hs _ _ h.succ⟩

/-- **A node's transitions run**, then `S_u ∧ D ⇒ ⋁ S_t` by RUP (equations (16) and (20)). -/
private theorem transOut_spec {m : Mode} {i : ℕ} (hi : i < I.n) {L' : List Node} {e : ProofLog}
    {db : List (ℕ × PBConstr)} (h : I.Run X e db) {u : Node} (hu : I.NodeOk i db e.var u)
    (hL' : ∀ t ∈ L', I.NodeOk (i + 1) db e.var t)
    (hbs : ∀ b ∈ vals (I.dom i), I.keep m i u.st b = true → Cover m L' (I.succSt i u.st b)) :
    ∃ db', I.Run X (I.transOut m i L' e u).1 db' ∧ Sub db db' ∧
      (I.transOut m i L' e u).2.u = u ∧
      I.OutOk m i db' (I.transOut m i L' e u).1.var L' (I.transOut m i L' e u).2 ∧
      (I.transOut m i L' e u).1.var = e.var := by
  obtain ⟨db₁, h₁, s₁, hmap, hall, hlen, hcls, hv⟩ :=
    I.trans1_spec hi (vals (I.dom i)) e db h hu hL' hbs
  have hvo : (I.transOut m i L' e u).1.var = e.var := by
    simp only [transOut, ProofLog.push, Nat.add_zero]; exact hv
  set r := I.trans1 m i L' u e (vals (I.dom i)) with hr
  -- Under `S_u`, the domain literal and the falsity of the targets, each implication for `b`
  -- forces `xᵢ ≠ b`.
  have key : ∀ (K : List (Literal ℕ)), (u.S, true) ∈ K → (∀ x ∈ r.tr, (x.tgt.S, false) ∈ K) →
      ∀ p ∈ (vals (I.dom i)).zip r.cls, ∃ c, lookup db₁ p.2 = some c ∧
        (c.terms.map termVar).Nodup ∧ ∀ σ, Consistent σ K → c.Holds σ → σ i = !p.1 := by
    intro K hS hT p hp
    obtain ⟨c, hc, hnd, hsem⟩ := hcls p hp
    refine ⟨c, hc, hnd, fun σ hσ hcσ => ?_⟩
    by_contra hne
    have hx : σ i = p.1 := by
      revert hne; cases σ i <;> cases p.1 <;> simp
    obtain ⟨x, hx', hxS⟩ := hsem σ hcσ (lit_of hσ hS) hx
    have := lit_of hσ (hT x hx')
    simp [hxS] at this
  have hrup : rup db₁ (I.succClause i u r.tr) (.neg :: r.cls.map .id) = true := by
    refine rup_clause ?_
    have hK : ∀ x ∈ r.tr, (x.tgt.S, false) ∈ ((u.S, false) :: I.fixNeg i ++
        r.tr.map fun x => (x.tgt.S, true)).map Std.Sat.Literal.negate ++ [] := fun x hx => by
      have h1 : (x.tgt.S, true) ∈ (u.S, false) :: I.fixNeg i ++
          r.tr.map fun x => (x.tgt.S, true) :=
        List.mem_append_right _ (List.mem_map_of_mem (f := fun x => (x.tgt.S, true)) hx)
      simpa [Std.Sat.Literal.negate] using
        List.mem_append_left [] (List.mem_map_of_mem (f := Std.Sat.Literal.negate) h1)
    have hSK : (u.S, true) ∈ ((u.S, false) :: I.fixNeg i ++
        r.tr.map fun x => (x.tgt.S, true)).map Std.Sat.Literal.negate ++ [] := by
      simp [Std.Sat.Literal.negate]
    have hkey := key _ hSK hK
    cases hd : I.dom i with
    | none =>
      rw [hd] at hlen hkey
      obtain ⟨k₀, k₁, hr2⟩ : ∃ k₀ k₁, r.cls = [k₀, k₁] :=
        List.length_eq_two.1 (by simpa [vals] using hlen)
      rw [hr2] at hkey ⊢
      obtain ⟨c₀, hc₀, hn₀, hs₀⟩ := hkey (false, k₀) (by simp [vals])
      obtain ⟨c₁, hc₁, hn₁, hs₁⟩ := hkey (true, k₁) (by simp [vals])
      simp only [List.map_cons, List.map_nil]
      refine RupOk.id_imp (L := [(i, true)]) hc₀ hn₀ (fun σ hσ hc => ?_) ?_
      · simp [Consistent, hs₀ σ hσ hc]
      refine RupOk.id_conflict hc₁ hn₁ fun σ hσ hc => ?_
      have h1 := hs₁ σ (fun l hl => hσ l (List.mem_append_right _ hl)) hc
      have h2 := lit_of hσ (v := i) (b := true) (by simp)
      simp [h1] at h2
    | some b =>
      rw [hd] at hlen hkey
      obtain ⟨k, hr2⟩ : ∃ k, r.cls = [k] :=
        List.length_eq_one_iff.1 (by simpa [vals] using hlen)
      rw [hr2] at hkey ⊢
      obtain ⟨c, hc, hn, hs⟩ := hkey (b, k) (by simp [vals])
      simp only [List.map_cons, List.map_nil]
      refine RupOk.id_conflict hc hn fun σ hσ hcσ => ?_
      have h1 := hs σ hσ hcσ
      have h2 := lit_of hσ (v := i) (b := b) (by simp [fixNeg, hd, Std.Sat.Literal.negate])
      cases b <;> simp_all
  obtain ⟨h₂, s₂⟩ := Run.rup I h₁ hrup (fun v hv' => by
    obtain ⟨l, hl, rfl⟩ := vars_clause hv'
    simp only [fixNeg, List.mem_cons, List.mem_append, List.mem_map] at hl
    rw [hv]
    rcases hl with (rfl | hl) | ⟨x, hx, rfl⟩
    · exact hu.S
    · cases hd : I.dom i with
      | none => simp [hd] at hl
      | some c =>
        simp only [hd, Option.map_some, Option.toList_some, List.mem_singleton] at hl
        subst hl; simp; have := h.2.2.2.1; omega
    · exact (hL' _ (hall x hx).1).S)
  refine ⟨_, h₂, s₁.trans s₂, rfl, ⟨hu.mono I (s₁.trans s₂) hvo.ge, hmap, fun x hx => ?_, ?_⟩,
    hvo⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hall x hx
    exact ⟨h1, h2, h3, h4, s₂ _ _ h5⟩
  · exact (lookup_cons _ _ _ _).trans (ite_eq_left rfl)

private theorem trans_spec {m : Mode} {i : ℕ} (hi : i < I.n) {L' : List Node} :
    ∀ (L : List Node) (e : ProofLog) (db : List (ℕ × PBConstr)), I.Run X e db →
      (∀ u ∈ L, I.NodeOk i db e.var u) → (∀ t ∈ L', I.NodeOk (i + 1) db e.var t) →
      (∀ u ∈ L, ∀ b ∈ vals (I.dom i), I.keep m i u.st b = true →
        Cover m L' (I.succSt i u.st b)) →
      ∃ db', I.Run X (I.trans m i L' e L).1 db' ∧ Sub db db' ∧
        (I.trans m i L' e L).2.map (·.u) = L ∧
        (∀ o ∈ (I.trans m i L' e L).2, I.OutOk m i db' (I.trans m i L' e L).1.var L' o) ∧
        (I.trans m i L' e L).1.var = e.var
  | [], e, db, h, _, _, _ => ⟨db, h, Sub.refl _, rfl, by simp [trans], rfl⟩
  | u :: L, e, db, h, hL, hL', hs => by
    obtain ⟨db₁, h₁, s₁, hu₁, hok₁, hv₁⟩ := I.transOut_spec hi h (hL u List.mem_cons_self) hL'
      (hs u List.mem_cons_self)
    obtain ⟨db', h', s', hmap, hall, hv⟩ := trans_spec hi L _ db₁ h₁
      (fun v hv => by rw [hv₁]; exact (hL v (List.mem_cons_of_mem _ hv)).mono I s₁ le_rfl)
      (fun t ht => by rw [hv₁]; exact (hL' t ht).mono I s₁ le_rfl)
      (fun v hv => hs v (List.mem_cons_of_mem _ hv))
    refine ⟨db', h', s₁.trans s', by simp [trans, hmap, hu₁], ?_, by simp [trans, hv, hv₁]⟩
    simp only [trans, List.mem_cons]
    rintro o (rfl | ho)
    · exact hok₁.mono I s' (by rw [hv, hv₁])
    · exact hall o ho

/-! ### At-least-one constraints and the forward pass -/

private theorem negate_aloClause (L : List Node) :
    (I.negD ++ L.map fun u => (u.S, true)).map Std.Sat.Literal.negate ++ [] =
      I.fixedLits ++ L.map fun u => (u.S, false) := by
  simp [List.map_append, negate_negD, List.map_map, Function.comp_def, Std.Sat.Literal.negate]

/-- **The at-least-one constraint of a layer conflicts** with the fixed literals and the falsity
of every node of the layer. -/
theorem rupOk_alo {db : List (ℕ × PBConstr)} {neg : PBConstr} {k : ℕ} {hs : List Hint}
    {L : List Node} {K : List (Literal ℕ)} (halo : lookup db k = some (I.aloClause L).normalize)
    (hD : ∀ l ∈ I.fixedLits, l ∈ K) (hL : ∀ u ∈ L, (u.S, false) ∈ K) :
    RupOk db neg (.id k :: hs) K :=
  RupOk.id_conflict halo (nodup_termVar_normalize _) fun σ hσ hc => by
    rw [holds_normalize, aloClause, holds_clause] at hc
    obtain ⟨l, hl, hev⟩ := hc
    rcases List.mem_append.1 hl with hl | hl
    · have := I.eval_negD (fun m hm => hσ m (hD m hm)) l hl
      simp [this] at hev
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hl
      simp [lit_of hσ (hL u hu)] at hev

/-- Under the fixed literals and the falsity of every node of `L'`, the clause `S_u ∧ D ⇒ ⋁ S_t`
of a node whose targets are in `L'` makes `S_u` false. -/
theorem succ_false {i : ℕ} (hi : i < I.n) {o : Out} {σ : ℕ → Bool}
    {K : List (Literal ℕ)} (hD : ∀ l ∈ I.fixedLits, l ∈ K)
    (hL' : ∀ x ∈ o.tr, (x.tgt.S, false) ∈ K) (hσ : Consistent σ K)
    (hc : (I.succClause i o.u o.tr).normalize.Holds σ) : σ o.u.S = false := by
  rw [holds_normalize, succClause, holds_clause] at hc
  obtain ⟨l, hl, hev⟩ := hc
  simp only [List.mem_cons, List.mem_append, List.mem_map] at hl
  rcases hl with (rfl | hl) | ⟨x, hx, rfl⟩
  · simpa using hev
  · cases hd : I.dom i with
    | none => simp [fixNeg, hd] at hl
    | some b =>
      simp only [fixNeg, hd, Option.map_some, Option.toList_some, List.mem_singleton] at hl
      subst hl
      have := lit_of hσ (hD _ ((I.mem_fixedLits).2 ⟨hi, hd⟩))
      simp [this] at hev
  · have := lit_of hσ (hL' x hx)
    simp [this] at hev

/-- **The at-least-one constraint of the next layer runs** (equations (22)–(23)). -/
private theorem rup_alo {m : Mode} {i : ℕ} (hi : i < I.n) {db : List (ℕ × PBConstr)} {V : ℕ}
    {L L' : List Node} {outs : List Out} {alo : ℕ} (hmap : outs.map (·.u) = L)
    (houts : ∀ o ∈ outs, I.OutOk m i db V L' o)
    (halo : lookup db alo = some (I.aloClause L).normalize) :
    rup db (I.aloClause L') (.neg :: outs.map (fun o => .id o.succ) ++ [.id alo]) = true := by
  refine rup_clause ?_
  rw [negate_aloClause]
  have := RupOk.imps (db := db) (neg := (I.aloClause L').negate)
    (K₀ := I.fixedLits ++ L'.map fun u => (u.S, false)) (rest := [.id alo])
    (outs.map fun o => (Hint.id o.succ, (o.u.S, false))) _ (fun l hl => hl) ?_ ?_
  · rw [List.map_map] at this; exact this
  · intro x hx
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hx
    refine ⟨_, (houts o ho).succ, nodup_termVar_normalize _, fun σ hσ hc => ?_⟩
    have := I.succ_false hi (fun l hl => List.mem_append_left _ hl)
      (fun x hx => List.mem_append_right _ (List.mem_map.2 ⟨_, ((houts o ho).tr x hx).1, rfl⟩))
      hσ hc
    simp [this]
  · refine I.rupOk_alo halo (fun m hm => by simp [hm]) fun u hu => ?_
    rw [← hmap] at hu
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hu
    simp only [List.map_map, List.mem_append, List.mem_map]
    exact .inl ⟨o, ho, rfl⟩

/-- **The facts about a layer** `i` of the forward pass. -/
structure LayOk (m : Mode) (i : ℕ) (db : List (ℕ × PBConstr)) (V : ℕ) (r : LayerRec) : Prop where
  /-- The index. -/
  idx : r.i = i
  /-- The states are those of the layer. -/
  lay : r.nodes.map (·.st) = I.layM m i
  /-- The nodes' facts. -/
  nodes : ∀ u ∈ r.nodes, I.NodeOk i db V u
  /-- The at-least-one constraint. -/
  alo : lookup db r.alo = some (I.aloClause r.nodes).normalize

theorem LayOk.mono {m : Mode} {i : ℕ} {db db' : List (ℕ × PBConstr)} {V V' : ℕ}
    {r : LayerRec} (h : I.LayOk m i db V r) (hs : Sub db db') (hV : V ≤ V') :
    I.LayOk m i db' V' r :=
  ⟨h.idx, h.lay, fun u hu => (h.nodes u hu).mono I hs hV, hs _ _ h.alo⟩

/-- **The layers before layer `j`**, latest first, the nodes of layer `j` being `L'`: each with
its facts and its transitions into the layer after it. -/
def Chain (m : Mode) (db : List (ℕ × PBConstr)) (V : ℕ) : ℕ → List Node → List LayerRec → Prop
  | _, _, [] => True
  | j, L', r :: rs => r.i + 1 = j ∧ I.LayOk m r.i db V r ∧ r.outs.map (·.u) = r.nodes ∧
      (∀ o ∈ r.outs, I.OutOk m r.i db V L' o) ∧ Chain m db V r.i r.nodes rs

theorem Chain.mono {m : Mode} {db db' : List (ℕ × PBConstr)} {V V' : ℕ} (hs : Sub db db')
    (hV : V ≤ V') : ∀ {j : ℕ} {L' : List Node} {rs : List LayerRec}, I.Chain m db V j L' rs →
      I.Chain m db' V' j L' rs
  | _, _, [], _ => trivial
  | _, _, _ :: _, ⟨h1, h2, h3, h4, h5⟩ =>
    ⟨h1, h2.mono I hs hV, h3, fun o ho => (h4 o ho).mono I hs hV, Chain.mono hs hV h5⟩

private theorem dominates_refl (s : St) : dominates s s = true := by simp [dominates]

private theorem dominates_trans {a b c : St} (h₁ : dominates a b = true)
    (h₂ : dominates b c = true) :
    dominates a c = true := by
  simp only [dominates, Bool.and_eq_true, decide_eq_true_eq] at *
  omega

private theorem dominated_insertSt {C K : List St} (h : ∀ c ∈ C, ∃ t ∈ K, dominates t c = true)
    (s : St) : ∀ c ∈ s :: C, ∃ t ∈ insertSt K s, dominates t c = true := by
  unfold insertSt
  split_ifs with hd
  · obtain ⟨t, ht, hts⟩ := List.any_eq_true.1 hd
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨t, ht, hts⟩
    · exact h c hc
  · intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨c, List.mem_cons_self, dominates_refl c⟩
    · obtain ⟨t, ht, htc⟩ := h c hc
      by_cases hst : dominates s t = true
      · exact ⟨s, List.mem_cons_self, dominates_trans hst htc⟩
      · exact ⟨t, List.mem_cons_of_mem _ (List.mem_filter.2 ⟨ht, by simpa using hst⟩), htc⟩

private theorem dominated_foldl : ∀ (L : List St) {C K : List St},
    (∀ c ∈ C, ∃ t ∈ K, dominates t c = true) →
    ∀ c ∈ C ++ L, ∃ t ∈ L.foldl insertSt K, dominates t c = true
  | [], C, K, h => by simpa using h
  | s :: L, C, K, h => by
    have := dominated_foldl L (C := s :: C) (K := insertSt K s) (dominated_insertSt h s)
    intro c hc
    refine this c ?_
    simp only [List.mem_append, List.mem_cons] at hc ⊢
    tauto

/-- **Every kept successor is covered** by a state of the next layer: equal to it, or, with
`m.dom`, dominating it. -/
private theorem cover_nextL {m : Mode} {i : ℕ} {L : List St} {st : St} (hst : st ∈ L) {b : Bool}
    (hb : b ∈ vals (I.dom i)) (hk : I.keep m i st b = true) :
    ∃ t ∈ I.nextL m i L, (if m.dom then dominates t (I.succSt i st b)
      else t == I.succSt i st b) = true := by
  have hc : I.succSt i st b ∈ I.cands m i L := by
    simp only [cands, List.mem_flatMap, List.mem_map, List.mem_filter]
    exact ⟨st, hst, b, ⟨hb, hk⟩, rfl⟩
  cases hm : m.dom
  · refine ⟨I.succSt i st b, ?_, by simp⟩
    simp only [nextL, hm, Bool.false_eq_true, ↓reduceIte]
    exact List.mem_dedup.2 hc
  · obtain ⟨t, ht, hdom⟩ := dominated_foldl (I.cands m i L) (C := []) (K := [])
      (by simp) _ (by simpa using hc)
    exact ⟨t, by simpa [nextL, hm] using ht, by simpa using hdom⟩

private theorem cover_of_map {m : Mode} {L' : List Node} {S : List St} (hS : L'.map (·.st) = S)
    {st : St} (h : ∃ t ∈ S, (if m.dom then dominates t st else t == st) = true) :
    Cover m L' st := by
  obtain ⟨t, ht, hp⟩ := h
  rw [← hS] at ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ht
  exact ⟨u, hu, hp⟩

/-- **The forward pass runs**: from layer `i`, the layers `i + 1, …, n` with their transitions and
at-least-one constraints. -/
private theorem fwd_spec (m : Mode) (hX : I.CtxOk X) :
    ∀ (k i : ℕ) (e : ProofLog) (L : List Node) (alo : ℕ)
    (recs : List LayerRec) (db : List (ℕ × PBConstr)), i + k = I.n → I.Run X e db →
    I.LayOk m i db e.var ⟨i, L, [], alo⟩ → I.Chain m db e.var i L recs →
    recs.map (·.i) = (List.range i).reverse →
    ∃ db', I.Run X (I.fwd m k i e L alo recs).1 db' ∧ Sub db db' ∧
      ∃ rn rs, (I.fwd m k i e L alo recs).2 = rn :: rs ∧
        I.LayOk m I.n db' (I.fwd m k i e L alo recs).1.var rn ∧
        I.Chain m db' (I.fwd m k i e L alo recs).1.var I.n rn.nodes rs ∧
        rs.map (·.i) = (List.range I.n).reverse
  | 0, i, e, L, alo, recs, db, hk, h, hL, hc, hidx => by
    simp only [Nat.add_zero] at hk
    subst hk
    exact ⟨db, h, Sub.refl _, _, recs, rfl, hL, hc, hidx⟩
  | k + 1, i, e, L, alo, recs, db, hk, h, hL, hc, hidx => by
    have hi : i < I.n := by omega
    have hLl : L.map (·.st) = I.layM m i := hL.lay
    obtain ⟨db₁, h₁, s₁, hmap₁, hok₁, hv₁⟩ := I.mkLayer_spec (i := i + 1) (by omega)
      (I.nextL m i (L.map (·.st))) e db hX h (fun st hst => by
        rw [hLl] at hst; exact I.le_tot_of_mem_layM (m := m) (i := i + 1) hst)
    set r₁ := I.mkLayer (i + 1) e (I.nextL m i (L.map (·.st))) with hr₁
    have hlay₁ : r₁.2.map (·.st) = I.layM m (i + 1) := by rw [hmap₁, hLl]; rfl
    obtain ⟨db₂, h₂, s₂, hmap₂, hok₂, hv₂⟩ := I.trans_spec (m := m) hi L r₁.1 db₁ h₁
      (fun u hu => (hL.nodes u hu).mono I s₁ hv₁)
      hok₁ (fun u hu b hb hk' => cover_of_map hmap₁
        (I.cover_nextL (List.mem_map_of_mem hu) hb hk'))
    set r₂ := I.trans m i r₁.2 r₁.1 L with hr₂
    have hrup := I.rup_alo hi hmap₂ hok₂ (s₂ _ _ (s₁ _ _ hL.alo))
    obtain ⟨h₃, s₃⟩ := Run.rup I h₂ hrup (fun v hv => by
      obtain ⟨l, hl, rfl⟩ := vars_clause hv
      rcases List.mem_append.1 hl with hl | hl
      · have := I.vars_negD hl; have := h₂.2.2.2.1; omega
      · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hl
        rw [hv₂]; exact (hok₁ t ht).S)
    have hV : r₁.1.var ≤ (r₂.1.push [.step (.rup (I.aloClause r₁.2)
        (.neg :: r₂.2.map (fun o => .id o.succ) ++ [.id alo]))] 1 0).var := by
      simp [ProofLog.push, hv₂]
    have hs := s₁.trans (s₂.trans s₃)
    obtain ⟨db', h', s', rest⟩ := fwd_spec m hX k (i + 1) _ r₁.2 r₂.1.next
      (⟨i, L, r₂.2, alo⟩ :: recs) _ (by omega) h₃
      ⟨rfl, hlay₁, fun u hu => (hok₁ u hu).mono I (s₂.trans s₃) hV,
        ((lookup_cons _ _ _ _).trans (ite_eq_left rfl))⟩
      ⟨rfl, ⟨rfl, hLl, fun u hu => (hL.nodes u hu).mono I hs (le_trans hv₁ hV), hs _ _ hL.alo⟩,
        hmap₂, fun o ho => (hok₂ o ho).mono I s₃ (by rw [hv₂]; exact hV),
        hc.mono I hs (le_trans hv₁ hV)⟩
      (by simp [List.range_succ, hidx])
    exact ⟨db', h', s₁.trans (s₂.trans (s₃.trans s')), rest⟩

/-- **The forward pass from the start runs**, for a start state numbering its constraints below
`3` over item variables. -/
theorem forward_spec (m : Mode) (hX : I.CtxOk X) {db₀ : List (ℕ × PBConstr)}
    (h₀' : I.Run X ⟨[], 3, I.n⟩ db₀) :
    ∃ db, I.Run X (I.forward m).1 db ∧ Sub db₀ db ∧ ∃ rn rs, (I.forward m).2 = rn :: rs ∧
      I.LayOk m I.n db (I.forward m).1.var rn ∧
      I.Chain m db (I.forward m).1.var I.n rn.nodes rs ∧
      rs.map (·.i) = (List.range I.n).reverse := by
  obtain ⟨db₁, h₀, s₀, hmap₀, hok₀, hv₀⟩ := I.mkLayer_spec (i := 0) (Nat.zero_le _)
    (I.layM m 0) ⟨[], 3, I.n⟩ _ hX h₀' (fun st hst => I.le_tot_of_mem_layM hst)
  set r₀ := I.mkLayer 0 ⟨[], 3, I.n⟩ (I.layM m 0) with hr₀
  obtain ⟨u₀, hu₀⟩ : ∃ u₀, r₀.2 = [u₀] := by
    rcases h : r₀.2 with _ | ⟨u, _ | _⟩ <;> rw [h] at hmap₀ <;> simp [layM] at hmap₀ ⊢
  have hst₀ : u₀.st = (0, 0) := by rw [hu₀] at hmap₀; simpa [layM] using hmap₀
  have hn₀ := hok₀ u₀ (by rw [hu₀]; simp)
  have hrup : rup db₁ (I.aloClause r₀.2) [.neg, .id (r₀.2.headD noNode).wb,
      .id (r₀.2.headD noNode).pb, .id (r₀.2.headD noNode).sb] = true := by
    rw [hu₀]
    refine rup_clause ?_
    rw [negate_aloClause]
    simp only [List.headD_cons, List.map_cons, List.map_nil]
    refine RupOk.id_imp (L := [(u₀.W, true)]) hn₀.wb (nodup_termVar_normalize _) ?_ ?_
    · intro σ _ hc
      rw [holds_normalize, holds_impl_neg_negate] at hc
      simp [Consistent, hc (by rw [cW, holds_dimC, hst₀]; exact Nat.zero_le _)]
    refine RupOk.id_imp (L := [(u₀.P, true)]) hn₀.pb (nodup_termVar_normalize _) ?_ ?_
    · intro σ _ hc
      rw [holds_normalize, holds_impl_neg_negate] at hc
      have : (I.cP 0 u₀.st).Holds σ := by
        rw [cP, holds_dimC, hst₀]; exact Nat.zero_le _
      simp [Consistent, hc this]
    refine RupOk.id_conflict hn₀.sb (nodup_termVar_normalize _) fun σ hσ hc => ?_
    rw [holds_normalize, holds_impl_neg_negate] at hc
    have h1 := hc ((holds_cS σ _ _).2 ⟨lit_of hσ (by simp), lit_of hσ (by simp)⟩)
    have h2 := lit_of hσ (v := u₀.S) (b := false) (by simp)
    simp [h1] at h2
  obtain ⟨h₁, s₁⟩ := Run.rup I h₀ hrup (fun v hv => by
    obtain ⟨l, hl, rfl⟩ := vars_clause hv
    rcases List.mem_append.1 hl with hl | hl
    · have := I.vars_negD hl; have := h₀.2.2.2.1; omega
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hl; exact (hok₀ t ht).S)
  obtain ⟨db₂, h₂, s₂, rest⟩ := I.fwd_spec m hX I.n 0 _ r₀.2 r₀.1.next [] _ (by omega) h₁
    ⟨rfl, hmap₀, fun u hu => (hok₀ u hu).mono I s₁ (by simp [ProofLog.push]),
      ((lookup_cons _ _ _ _).trans (ite_eq_left rfl))⟩ trivial rfl
  exact ⟨db₂, h₂, s₀.trans (s₁.trans s₂), rest⟩

/-! ### Reachable states -/

/-- The state of the assignment `σ` after the first `i` items. -/
def stOf (σ : ℕ → Bool) (i : ℕ) : St := (part σ I.w true i, part σ I.p false i)

theorem part_congr {σ τ : ℕ → Bool} {i : ℕ} (h : ∀ j < i, σ j = τ j) (a : ℕ → ℕ)
    (pol : Bool) : part σ a pol i = part τ a pol i := by
  simp only [part]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  rw [h j (List.mem_range.1 hj)]

theorem stOf_succ (σ : ℕ → Bool) (i : ℕ) :
    I.stOf σ (i + 1) = I.succSt i (I.stOf σ i) (σ i) := by
  simp [stOf, succSt, part_succ]

/-- Changing an assignment at item `i` keeps its state after the first `i` items. -/
theorem stOf_update (σ : ℕ → Bool) (i : ℕ) (b : Bool) :
    I.stOf (Function.update σ i b) i = I.stOf σ i := by
  have h : ∀ j < i, Function.update σ i b j = σ j :=
    fun j hj => Function.update_of_ne (Nat.ne_of_lt hj) _ _
  simp only [stOf]
  rw [part_congr h, part_congr h]

end Inst

/-! ### Instances on `Fin n` -/

section

variable {n : ℕ}

theorem map_finRange {α : Type*} (g : ℕ → α) :
    (List.finRange n).map (fun i => g i.val) = (List.range n).map g := by
  rw [← List.map_coe_finRange_eq_range, List.map_map]; rfl

/-- The capacity constraint of the instance on `Fin n`. -/
theorem Inst.capC_ofFin (w p : Fin n → ℕ) (C P : ℕ) (dom : Fin n → Option Bool) :
    (Inst.ofFin w p C P dom).capC =
      ⟨(List.finRange n).map fun i => (w i, (i.val, false)),
        ((List.finRange n).map w).sum - C⟩ := by
  have h1 : (List.finRange n).map (fun i => (w i, (i.val, false))) =
      (List.range n).map fun j => ((Inst.ofFin w p C P dom).w j, (j, false)) := by
    rw [← map_finRange]; exact List.map_congr_left fun i _ => by simp [Inst.ofFin]
  have h3 : (List.finRange n).map w = (List.range n).map (Inst.ofFin w p C P dom).w := by
    rw [← map_finRange]; exact List.map_congr_left fun i _ => by simp [Inst.ofFin]
  simp only [Inst.capC, Inst.tot, h1, h3]
  rfl

/-- The weight of the items an assignment takes, as the dynamic program counts it. -/
theorem Inst.part_ofFin (σ : ℕ → Bool) (a : Fin n → ℕ) :
    Inst.part σ (fun j => if h : j < n then a ⟨j, h⟩ else 0) true n = ∑ i ∈ chosen n σ, a i := by
  rw [chosen, Finset.sum_filter, Inst.part, ← map_finRange
    (fun j => Inst.bit (σ j) true (if h : j < n then a ⟨j, h⟩ else 0)), ← Fin.sum_univ_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases σ i.val <;> simp [Inst.bit]

/-- The total weight, as the dynamic program counts it. -/
theorem Inst.tot_ofFin (a : Fin n → ℕ) :
    Inst.tot (fun j => if h : j < n then a ⟨j, h⟩ else 0) n = ∑ i, a i := by
  rw [Inst.tot, ← map_finRange (fun j => if h : j < n then a ⟨j, h⟩ else 0), ← Fin.sum_univ_def]
  exact Finset.sum_congr rfl fun i _ => by simp [i.isLt]

end

end Cslib.Logic.PL.VeriPB.Knapsack

end
