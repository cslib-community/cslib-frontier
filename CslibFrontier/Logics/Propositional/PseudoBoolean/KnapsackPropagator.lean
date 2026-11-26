/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.Knapsack
public import CslibFrontier.Logics.Propositional.PseudoBoolean.Reification
public import CslibFrontier.Logics.Propositional.PseudoBoolean.RupComplete
-- `import all`: the acceptance proof unfolds `stepTop`, `runTop` and the reification steps.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Reification
import Mathlib.Algebra.BigOperators.Fin

/-!
# Proof logging for a knapsack propagator

A *knapsack constraint* over `n` items, of weights `w i` and profits `p i`, with a capacity `C`
and a profit bound `P`, asks for a set of items of weight at most `C` and profit at least `P`. As
a propagator in a constraint solver, it receives the current *domains* of the items (each free,
or fixed to `0` or `1`) and removes every value of a domain that no solution of the constraint
agreeing with the domains supports (`Cslib.Logic.PL.VeriPB.Knapsack.Supported`). This file gives
such a propagator, by a dynamic program, that writes a kernel-format VeriPB proof justifying each
removal, after §3.3 of [Demirović, McCreesh, McIlree, Nordström, Oertel and
Sidorov][DemirovicMcCreeshMcIlreeNordstromOertelSidorov2024], in the proof-logging framework for
constraint programming of [Gocht, McCreesh and Nordström][GochtMcCreeshNordstrom2022]: a
propagator justifies the implication `D ⇒ xᵢ ≠ b` from its antecedent `D`, the literals that the
domains fix.

**The encoding** (`Cslib.Logic.PL.VeriPB.Knapsack.propFormula`): item `i` is the variable `i`;
the formula is the capacity constraint `∑ wᵢ ¬xᵢ ≥ ∑ wᵢ - C` of the certified knapsack
(`Cslib.Logic.PL.VeriPB.Knapsack.capacity`, `Cslib.Logic.PL.VeriPB.Knapsack.holds_capacity_iff`)
and the profit constraint `∑ pᵢ xᵢ ≥ P` (`Cslib.Logic.PL.VeriPB.Knapsack.profitBound`,
`Cslib.Logic.PL.VeriPB.Knapsack.holds_profitBound_iff`).

**The dynamic program.** Layer `i` holds the states `(w, q)` reachable on the first `i` items
under the domains: the weight taken and the profit left out. States are merged only when they are
equal, as the paper requires of a propagator (§3.3, difference 4). A forward pass builds the
layers; a backward pass finds the states with a feasible completion; the value `b` of item `j` is
removed when no state of layer `j` has a successor by `b` with a feasible completion.

**The proof.** As in the certified knapsack (equations (8)–(23) of the paper), each node `u` of
layer `i` gets extension variables, defined by `Cslib.Logic.PL.VeriPB.reify`:
`W ⇔ ∑_{j<i} wⱼ xⱼ ≥ w`, `P ⇔ ∑_{j<i} pⱼ ¬xⱼ ≥ q` and `S ⇔ W + P ≥ 2`. Then:
* each transition `S_u ∧ (xᵢ = b) ⇒ S_t` is derived by adding halves of the reifications of `W`
  and of `P` and closing by RUP, and `S_u ∧ D ⇒ ⋁ S_t` by RUP from the transitions;
* the at-least-one constraint `D ⇒ ⋁_{u} S_u` of each layer follows by RUP from that of the layer
  before;
* the backward pass refutes each state without a feasible completion, `D ⇒ ¬S_t`: in the last
  layer by adding the forward half of `W` to the capacity constraint, or that of `P` to the profit
  constraint, then RUP; earlier, by RUP from the refutations of its targets;
* each removal `D ⇒ xⱼ ≠ b` follows by RUP from the refutations of the targets by `b`, the
  transitions and the at-least-one constraint of layer `j`.

The proof has no conclusion; it runs with the item variables as the preserved set, so that each
derived constraint over the items holds at every solution of the formula.

**Soundness and completeness.** The checker accepts the proof on every instance
(`Cslib.Logic.PL.VeriPB.Knapsack.checkRed_propagate`). This is proved, not checked when the proof
runs: each `rup` step is shown accepted by the completeness of unit propagation on constraints over
distinct variables (`CslibFrontier.Logics.Propositional.PseudoBoolean.RupComplete`), from the
meaning of the constraints its hints name, and each addition by the slacks of the reification
halves. The propagator removes exactly the unsupported values
(`Cslib.Logic.PL.VeriPB.Knapsack.mem_removed_iff`): a removed value is unsupported because the
checker's soundness makes its derived clause `D ⇒ xⱼ ≠ b` hold at every solution, and an
unsupported value is removed because the dynamic program is exact.

**Departures from the paper.** §3.3 treats Trick's constraint, linear equalities whose sums are
integer variables, with states `S^i_{w,p}` reifying exact sums by four variables (equations
(24)–(26)) and direct variables for non-Boolean domains. Here the items are `0`–`1` variables
with domains of fixed literals, the sums are bounded by constants, and each state reifies
one-sided sums by two variables, as in §3.1: a weight of at least `w` and a profit left out of at
least `q`. Every condition under which a state is refuted is monotone in both, so the one-sided
states suffice, and the states are still exact. The bounds of sum variables are not propagated.
The proof deletes nothing.

## Main definitions

* `Cslib.Logic.PL.VeriPB.Knapsack.profitBound`, `Cslib.Logic.PL.VeriPB.Knapsack.propFormula`: the
  encoding.
* `Cslib.Logic.PL.VeriPB.Knapsack.Supported`: a value supported under the domains.
* `Cslib.Logic.PL.VeriPB.Knapsack.Propagation`, `Cslib.Logic.PL.VeriPB.Knapsack.propagate`: the
  propagator and its output.

## Main results

* `Cslib.Logic.PL.VeriPB.Knapsack.holds_profitBound_iff`: the profit constraint is correct.
* `Cslib.Logic.PL.VeriPB.Knapsack.checkRed_propagate`: the checker accepts every proof of the
  propagator.
* `Cslib.Logic.PL.VeriPB.Knapsack.mem_removed_iff`: the propagator removes exactly the unsupported
  values of the domains.

## References

* [E. Demirović, C. McCreesh, M. J. McIlree, J. Nordström, A. Oertel, K. Sidorov, *Pseudo-Boolean
  Reasoning About States and Transitions to Certify Dynamic Programming and Decision Diagram
  Algorithms*][DemirovicMcCreeshMcIlreeNordstromOertelSidorov2024]
* [S. Gocht, C. McCreesh, J. Nordström, *An Auditable Constraint Programming
  Solver*][GochtMcCreeshNordstrom2022]
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

namespace Inst

variable (I : Inst)

/-- The values of a domain. -/
private def vals : Option Bool → List Bool
  | none => [false, true]
  | some b => [b]

/-- `a` if `b = pol`, and `0` otherwise. -/
private def bit (b pol : Bool) (a : ℕ) : ℕ := if b = pol then a else 0

/-- `∑_{j<i} aⱼ`. -/
private def tot (a : ℕ → ℕ) (i : ℕ) : ℕ := ((List.range i).map a).sum

/-- `∑_{j<i} aⱼ [σ j = pol]`. -/
private def part (σ : ℕ → Bool) (a : ℕ → ℕ) (pol : Bool) (i : ℕ) : ℕ :=
  ((List.range i).map fun j => bit (σ j) pol (a j)).sum

/-- The terms `aⱼ ℓⱼ` for `j < i` with `aⱼ > 0`, `ℓⱼ` the literal `(j, pol)`. -/
private def sumTerms (a : ℕ → ℕ) (pol : Bool) (i : ℕ) : List (ℕ × Literal ℕ) :=
  (List.range i).filterMap fun j => if a j = 0 then none else some (a j, (j, pol))

/-- The partial sum constraint `∑_{j<i} aⱼ ℓⱼ ≥ d`. -/
private def dimC (a : ℕ → ℕ) (pol : Bool) (i d : ℕ) : PBConstr := ⟨sumTerms a pol i, d⟩

/-- The capacity constraint `∑ wⱼ ¬xⱼ ≥ ∑ wⱼ - C`. -/
private def capC : PBConstr :=
  ⟨(List.range I.n).map fun j => (I.w j, (j, false)), tot I.w I.n - I.C⟩

/-- The profit constraint `∑ pⱼ xⱼ ≥ P`. -/
private def profC : PBConstr := ⟨(List.range I.n).map fun j => (I.p j, (j, true)), I.P⟩

/-- The formula: the capacity and the profit constraints, numbered `1` and `2`. -/
private def F : List PBConstr := [I.capC, I.profC]

/-- The preserved set: the item variables. -/
private def pres : List ℕ := List.range I.n

/-- A state: the weight taken so far and the profit left out so far. -/
private abbrev St := ℕ × ℕ

/-- The successor of a state by the value `b` of item `i`. -/
private def succSt (i : ℕ) (st : St) (b : Bool) : St :=
  (st.1 + bit b true (I.w i), st.2 + bit b false (I.p i))

/-- The states of the next layer. -/
private def nextLay (i : ℕ) (L : List St) : List St :=
  (L.flatMap fun st => (vals (I.dom i)).map (I.succSt i st)).dedup

/-- The reachable states of layer `i`. -/
private def lay : ℕ → List St
  | 0 => [(0, 0)]
  | i + 1 => I.nextLay i (lay i)

/-- A state of the last layer is feasible: weight at most `C` and profit at least `P`. -/
private def finalOk (st : St) : Bool := decide (st.1 ≤ I.C) && decide (st.2 + I.P ≤ tot I.p I.n)

/-- The states of layer `i` with a feasible completion, by `k = n - i` backward layers. -/
private def aliveAt : ℕ → ℕ → List St
  | 0, i => (I.lay i).filter I.finalOk
  | k + 1, i =>
    let A := aliveAt k (i + 1)
    (I.lay i).filter fun st => (vals (I.dom i)).any fun b => I.succSt i st b ∈ A

/-- The states of layer `i` with a feasible completion. -/
private def alive (i : ℕ) : List St := I.aliveAt (I.n - i) i

/-- The literals fixed by the domains. -/
private def fixedLits : List (Literal ℕ) :=
  (List.range I.n).filterMap fun j => (I.dom j).map fun b => (j, b)

/-- Their negations, the antecedent of every derived implication. -/
private def negD : List (Literal ℕ) := I.fixedLits.map Std.Sat.Literal.negate

end Inst

/-- The clause of a list of literals. -/
private def clause (ls : List (Literal ℕ)) : PBConstr := ⟨ls.map ((1, ·)), 1⟩

/-! ### The proof being written -/

/-- A node of the decision diagram: its state, its extension variables `W`, `P`, `S`, and the
numbers of the two halves of their reifications. -/
private structure Node where
  st : ℕ × ℕ
  W : ℕ
  P : ℕ
  S : ℕ
  wf : ℕ
  wb : ℕ
  pf : ℕ
  pb : ℕ
  sf : ℕ
  sb : ℕ

/-- The proof being written: its steps, latest first, the next constraint number and the next
free variable. -/
private structure Acc where
  steps : List TopStep
  next : ℕ
  var : ℕ

/-- Append steps, advancing the next number by `dn` and the next variable by `dv`. -/
private def Acc.push (e : Acc) (ss : List TopStep) (dn dv : ℕ) : Acc :=
  ⟨ss.reverse ++ e.steps, e.next + dn, e.var + dv⟩

/-- A placeholder node, never reached on the layers of the dynamic program. -/
private def noNode : Node := ⟨(0, 0), 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The transitions out of a node: for each value `b` of its item, the target node and the number
of the implication `S ∧ (x = b) ⇒ S'`; and the number of `S ⇒ ⋁ S'`. -/
private structure Out where
  u : Node
  tr : List (Bool × Node × ℕ)
  succ : ℕ

/-- A layer of the diagram: its index, nodes, transitions out (none for the last layer) and the
number of its at-least-one constraint. -/
private structure LayerRec where
  i : ℕ
  nodes : List Node
  outs : List Out
  alo : ℕ

/-- The entry for `S` of a list of pairs. -/
private def dlook (dl : List (ℕ × ℕ)) (S : ℕ) : ℕ := ((dl.find? (·.1 == S)).map (·.2)).getD 0

/-- The node of a layer with the state `st`. -/
private def findNode (L : List Node) (st : ℕ × ℕ) : Node := (L.find? (·.st == st)).getD noNode

/-- The target and the implication of a transition by the value `b`. -/
private def Out.tgt (o : Out) (b : Bool) : Node := ((o.tr.find? (·.1 == b)).map (·.2.1)).getD noNode

/-- The number of the implication of the transition by the value `b`. -/
private def Out.tau (o : Out) (b : Bool) : ℕ := ((o.tr.find? (·.1 == b)).map (·.2.2)).getD 0

namespace Inst

variable (I : Inst)

/-- The reified weight constraint `W ⇔ ∑_{j<i} wⱼ xⱼ ≥ w`. -/
private def cW (i : ℕ) (st : St) : PBConstr := dimC I.w true i st.1

/-- The reified profit constraint `P ⇔ ∑_{j<i} pⱼ ¬xⱼ ≥ q`: the profit left out is at least `q`. -/
private def cP (i : ℕ) (st : St) : PBConstr := dimC I.p false i st.2

/-- The state constraint `S ⇔ W + P ≥ 2`. -/
private def cS (W P : ℕ) : PBConstr := ⟨[(1, (W, true)), (1, (P, true))], 2⟩

/-- The node of the state `st` created at `e`: variables from `e.var`, constraints from
`e.next`. -/
private def mkNode (e : Acc) (st : St) : Node :=
  ⟨st, e.var, e.var + 1, e.var + 2, e.next + 1, e.next + 3, e.next + 5, e.next + 7, e.next + 9,
    e.next + 11⟩

/-- The reifications of a node. -/
private def nodeSteps (i : ℕ) (u : Node) : List TopStep :=
  reify u.W (I.cW i u.st) ++ reify u.P (I.cP i u.st) ++ reify u.S (cS u.W u.P)

/-- Create the nodes of a layer. -/
private def mkLayer (i : ℕ) : Acc → List St → Acc × List Node
  | e, [] => (e, [])
  | e, st :: sts =>
    let u := mkNode e st
    let r := mkLayer i (e.push (I.nodeSteps i u) 12 3) sts
    (r.1, u :: r.2)

/-- The implication `S_u ∧ (xᵢ = b) ⇒ S_t`. -/
private def trClause (i : ℕ) (u : Node) (b : Bool) (t : Node) : PBConstr :=
  clause [(u.S, false), (i, !b), (t.S, true)]

/-- The transition steps (equations (11)–(13) and (17)–(19) of the paper): add the forward
halves of `W_u` and `P_u` to the backward halves of `W_t` and `P_t`, then RUP. -/
private def trSteps (i : ℕ) (u : Node) (b : Bool) (t : Node) (e : Acc) : List TopStep :=
  [.step (.pol [.id u.wf, .id t.wb, .add]), .step (.pol [.id u.pf, .id t.pb, .add]),
    .step (.rup (trClause i u b t) [.neg, .id u.sf, .id e.next, .id (e.next + 1), .id t.sb])]

/-- The transitions out of `u` into the layer `L'`, for the values `bs`. -/
private def trans1 (i : ℕ) (L' : List Node) (u : Node) :
    Acc → List Bool → Acc × List (Bool × Node × ℕ)
  | e, [] => (e, [])
  | e, b :: bs =>
    let t := findNode L' (I.succSt i u.st b)
    let r := trans1 i L' u (e.push (trSteps i u b t e) 3 0) bs
    (r.1, (b, t, e.next + 2) :: r.2)

/-- The negation of the domain literal of item `i`, if it is fixed. -/
private def fixNeg (i : ℕ) : List (Literal ℕ) := ((I.dom i).map fun b => (i, !b)).toList

/-- `S_u ∧ D ⇒ ⋁ S_t` over the targets of the transitions `tr`. -/
private def succClause (i : ℕ) (u : Node) (tr : List (Bool × Node × ℕ)) : PBConstr :=
  clause ((u.S, false) :: I.fixNeg i ++ tr.map fun x => (x.2.1.S, true))

/-- The transitions out of `u`, then `S_u ⇒ ⋁ S_t` by RUP (equations (16) and (20)). -/
private def transOut (i : ℕ) (L' : List Node) (e : Acc) (u : Node) : Acc × Out :=
  let r := I.trans1 i L' u e (vals (I.dom i))
  (r.1.push [.step (.rup (I.succClause i u r.2) (.neg :: r.2.map fun x => .id x.2.2))] 1 0,
    ⟨u, r.2, r.1.next⟩)

/-- The transitions out of a layer. -/
private def trans (i : ℕ) (L' : List Node) : Acc → List Node → Acc × List Out
  | e, [] => (e, [])
  | e, u :: us =>
    let r := I.transOut i L' e u
    let q := trans i L' r.1 us
    (q.1, r.2 :: q.2)

/-- The at-least-one constraint of a layer, under the domains: `D ⇒ ⋁ S_u`. -/
private def aloClause (L : List Node) : PBConstr := clause (I.negD ++ L.map fun u => (u.S, true))

/-- The forward pass: from layer `i`, create `k` more layers with their transitions and
at-least-one constraints. The records are returned latest first. -/
private def fwd : ℕ → ℕ → Acc → List Node → ℕ → List LayerRec → Acc × List LayerRec
  | 0, i, e, L, alo, recs => (e, ⟨i, L, [], alo⟩ :: recs)
  | k + 1, i, e, L, alo, recs =>
    let r₁ := I.mkLayer (i + 1) e (I.nextLay i (L.map (·.st)))
    let r₂ := I.trans i r₁.2 r₁.1 L
    let e' := r₂.1.push [.step (.rup (I.aloClause r₁.2)
      (.neg :: r₂.2.map (fun o => .id o.succ) ++ [.id alo]))] 1 0
    fwd k (i + 1) e' r₁.2 r₂.1.next (⟨i, L, r₂.2, alo⟩ :: recs)

/-- The refutation of a state under the domains: `D ⇒ ¬S`. -/
private def deadClause (S : ℕ) : PBConstr := clause (I.negD ++ [(S, false)])

/-- The infeasible states of the last layer: add the forward half of `W` to the capacity
constraint, or that of `P` to the profit constraint, then RUP. -/
private def deadFinal : Acc → List Node → Acc × List (ℕ × ℕ)
  | e, [] => (e, [])
  | e, t :: ts =>
    if I.finalOk t.st then deadFinal e ts
    else
      let ops := if t.st.1 ≤ I.C then [PolOp.id t.pf, .id 2, .add] else [.id t.wf, .id 1, .add]
      let r := deadFinal (e.push [.step (.pol ops),
        .step (.rup (I.deadClause t.S) [.neg, .id t.sf, .id e.next])] 2 0) ts
      (r.1, (t.S, e.next + 1) :: r.2)

/-- The states of layer `i` without a feasible completion, from the alive states `A` and the
refutations `dl` of layer `i + 1`: refute `S` by RUP from the refutations of its targets and
`S ⇒ ⋁ S_t`. -/
private def deadLayer (i : ℕ) (A : List St) (dl : List (ℕ × ℕ)) :
    Acc → List Out → Acc × List (ℕ × ℕ)
  | e, [] => (e, [])
  | e, o :: os =>
    if (vals (I.dom i)).any fun b => I.succSt i o.u.st b ∈ A then deadLayer i A dl e os
    else
      let r := deadLayer i A dl (e.push [.step (.rup (I.deadClause o.u.S)
        (.neg :: o.tr.map (fun x => .id (dlook dl x.2.1.S)) ++ [.id o.succ]))] 1 0) os
      (r.1, (o.u.S, e.next) :: r.2)

/-- The backward pass over the layers `rs`, latest first, from the alive states `A` and the
refutations `dl` of the layer after them. Returns each layer with the alive states and the
refutations of the layer after it. -/
private def backAll : Acc → List St → List (ℕ × ℕ) → List LayerRec →
    Acc × List (LayerRec × List St × List (ℕ × ℕ))
  | e, _, _, [] => (e, [])
  | e, A, dl, r :: rs =>
    let d := I.deadLayer r.i A dl e r.outs
    let A' := (r.nodes.map (·.st)).filter fun st =>
      (vals (I.dom r.i)).any fun b => I.succSt r.i st b ∈ A
    let q := backAll d.1 A' d.2 rs
    (q.1, (r, A, dl) :: q.2)

/-- The removal of the value `b` of item `i`: `D ⇒ xᵢ ≠ b`. -/
private def remClause (i : ℕ) (b : Bool) : PBConstr := clause (I.negD ++ [(i, !b)])

/-- The removals of a layer: the values `b` all of whose transitions lead to refuted states,
derived by RUP from those refutations, the transitions and the at-least-one constraint. -/
private def remLayer (r : LayerRec) (A : List St) (dl : List (ℕ × ℕ)) :
    Acc → List Bool → Acc × List (ℕ × Bool × ℕ)
  | e, [] => (e, [])
  | e, b :: bs =>
    if r.outs.all fun o => I.succSt r.i o.u.st b ∉ A then
      let hs := .neg :: r.outs.map (fun o => .id (dlook dl (o.tgt b).S)) ++
        r.outs.map (fun o => .id (o.tau b)) ++ [.id r.alo]
      let q := remLayer r A dl (e.push [.step (.rup (I.remClause r.i b) hs)] 1 0) bs
      (q.1, (r.i, b, e.next) :: q.2)
    else remLayer r A dl e bs

/-- The removals of all layers. -/
private def remAll : Acc → List (LayerRec × List St × List (ℕ × ℕ)) → Acc × List (ℕ × Bool × ℕ)
  | e, [] => (e, [])
  | e, x :: xs =>
    let q := I.remLayer x.1 x.2.1 x.2.2 e (vals (I.dom x.1.i))
    let q' := remAll q.1 xs
    (q'.1, q.2 ++ q'.2)

/-- The whole proof, before its conclusion, and the removals with their numbers. -/
private def emit : Acc × List (ℕ × Bool × ℕ) :=
  let r₀ := I.mkLayer 0 ⟨[], 3, I.n⟩ (I.lay 0)
  let u₀ := r₀.2.headD noNode
  let e₁ := r₀.1.push [.step (.rup (I.aloClause r₀.2) [.neg, .id u₀.wb, .id u₀.pb, .id u₀.sb])]
    1 0
  let f := I.fwd I.n 0 e₁ r₀.2 r₀.1.next []
  let rn := f.2.headD ⟨0, [], [], 0⟩
  let d := I.deadFinal f.1 rn.nodes
  let b := I.backAll d.1 ((rn.nodes.map (·.st)).filter I.finalOk) d.2 f.2.tail
  I.remAll b.1 b.2

end Inst

/-- **The output of the propagator**: the removed values `(i, b)`, item `i` no longer taking the
value `b`, and a kernel proof, with no conclusion, deriving `D ⇒ xᵢ ≠ b` for each. -/
structure Propagation where
  /-- The removed values. -/
  removed : List (ℕ × Bool)
  /-- The proof. -/
  proof : RedProof

/-- The propagator on an ℕ-indexed instance. -/
private def Inst.run (I : Inst) : Propagation :=
  ⟨I.emit.2.map fun x => (x.1, x.2.1), ⟨I.emit.1.steps.reverse, .noClaim⟩⟩

/-! ### Semantics of the constraints -/

namespace Inst

variable (I : Inst)

private theorem part_succ (σ : ℕ → Bool) (a : ℕ → ℕ) (pol : Bool) (i : ℕ) :
    part σ a pol (i + 1) = part σ a pol i + bit (σ i) pol (a i) := by
  simp [part, List.range_succ]

private theorem tot_succ (a : ℕ → ℕ) (i : ℕ) : tot a (i + 1) = tot a i + a i := by
  simp [tot, List.range_succ]

private theorem part_add_part (σ : ℕ → Bool) (a : ℕ → ℕ) (pol : Bool) (i : ℕ) :
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

private theorem lhs_sumTerms (σ : ℕ → Bool) (a : ℕ → ℕ) (pol : Bool) (i : ℕ) :
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

private theorem vars_sumTerms {a : ℕ → ℕ} {pol : Bool} {i x : ℕ}
    (h : x ∈ (sumTerms a pol i).map termVar) : x < i := by
  simp only [sumTerms, List.mem_map, List.mem_filterMap, List.mem_range] at h
  obtain ⟨t, ⟨j, hj, ht⟩, rfl⟩ := h
  split_ifs at ht
  cases ht
  simpa using hj

private theorem nodup_sumTerms (a : ℕ → ℕ) (pol : Bool) (i : ℕ) :
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

private theorem holds_dimC (σ : ℕ → Bool) (a : ℕ → ℕ) (pol : Bool) (i d : ℕ) :
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

private theorem holds_cS (σ : ℕ → Bool) (W P : ℕ) :
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

private theorem consistent_append {σ : ℕ → Bool} {A B : List (Literal ℕ)} :
    Consistent σ (A ++ B) ↔ Consistent σ A ∧ Consistent σ B := by
  simp only [Consistent, List.mem_append]
  exact ⟨fun h => ⟨fun l hl => h l (.inl hl), fun l hl => h l (.inr hl)⟩,
    fun h l hl => hl.elim (h.1 l) (h.2 l)⟩

private theorem mem_fixedLits {j : ℕ} {b : Bool} :
    (j, b) ∈ I.fixedLits ↔ j < I.n ∧ I.dom j = some b := by
  simp only [fixedLits, List.mem_filterMap, List.mem_range, Option.map_eq_some_iff,
    Prod.mk.injEq]
  constructor
  · rintro ⟨k, hk, b', hb', rfl, rfl⟩; exact ⟨hk, hb'⟩
  · rintro ⟨hj, hb⟩; exact ⟨j, hj, b, hb, rfl, rfl⟩

/-- Under the fixed literals, the negated domain literals are all false. -/
private theorem eval_negD {σ : ℕ → Bool} (h : Consistent σ I.fixedLits) :
    ∀ l ∈ I.negD, Literal.eval σ l = false := by
  intro l hl
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hl
  simp [Literal.eval_negate, h m hm]

private theorem negate_negD : I.negD.map Std.Sat.Literal.negate = I.fixedLits := by
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

private theorem vars_negate_sub {c : PBConstr} {x : ℕ} (h : x ∈ c.negate.vars) : x ∈ c.vars := by
  refine mem_vars_of_mem_vars_normalize ?_
  simp only [PBConstr.vars, negate, List.map_map, List.mem_map] at h ⊢
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨t, ht, by obtain ⟨a, v, b⟩ := t; rfl⟩

private theorem nodup_impl_single {l : Literal ℕ} {c : PBConstr} (hz : l.1 ∉ c.vars)
    (hd : (c.terms.map termVar).Nodup) : ((impl [l] c).terms.map termVar).Nodup := by
  simp only [impl, List.map_cons, List.map_nil, List.singleton_append, List.nodup_cons]
  refine ⟨?_, hd⟩
  obtain ⟨v, b⟩ := l
  simpa [Std.Sat.Literal.negate, PBConstr.vars] using hz

/-- The slack of `z ⇒ C`, as `reifyFwd` stores it. -/
private theorem slack_fwd {z : ℕ} {c : PBConstr} (hz : z ∉ c.vars)
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
  have hz' : z ∉ c.negate.vars := fun h => hz (vars_negate_sub h)
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
private theorem trans_dim {a : ℕ → ℕ} {pol b : Bool} {i d zu zt : ℕ} (hzu : i ≤ zu)
    (hzt : i + 1 ≤ zt) (hd' : d + bit b pol (a i) ≤ tot a (i + 1)) {σ : ℕ → Bool}
    (hA : ((impl [(zu, true)] (dimC a pol i d)).normalize.add
      (impl [(zt, false)] (dimC a pol (i + 1) (d + bit b pol (a i))).negate).normalize).Holds σ)
    (hu : σ zu = true) (hx : σ i = b) : σ zt = true := by
  have h1 := slack_fwd (c := dimC a pol i d) (z := zu)
    (fun h => by have := vars_sumTerms h; omega) (nodup_sumTerms a pol i) σ
  have h2 := slack_bwd (c := dimC a pol (i + 1) (d + bit b pol (a i))) (z := zt)
    (fun h => by have := vars_sumTerms h; omega) (nodup_sumTerms a pol (i + 1))
    ⟨fun _ => pol, by rw [holds_dimC, part_const]; exact hd'⟩ σ
  rw [holds_add_iff] at hA
  simp only [dimC, lhs_sumTerms, part_succ, hx, hu, ite_true] at h1 h2 hA
  cases hz : σ zt
  · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h2
    omega
  · rfl

/-- **The refutation of a last-layer state by addition** (equations (14)–(15) of the paper): the
forward half of `Z ⇔ ∑_{j<n} aⱼ ℓⱼ ≥ d` plus a constraint `∑ aⱼ ¬ℓⱼ ≥ B` of the formula gives
`Z ⇒ d + B ≤ ∑ aⱼ`. -/
private theorem final_dim {a : ℕ → ℕ} {pol : Bool} {m d z : ℕ} (hz : m ≤ z) {G : PBConstr}
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

variable (I : Inst)

/-! ### Running the proof -/

/-- The checker state with the database `db` and the next number `m`, all else as at the start. -/
private def state (db : List (ℕ × PBConstr)) (m : ℕ) : State :=
  { State.init I.F none (some I.pres) with db := db, next := m }

/-- **The proof so far runs** to the database `db`: the numbers of `db` are below the next one,
its variables below the next free one, which is not an item variable, and the formula's two
constraints are `1` and `2`. -/
private def Run (e : Acc) (db : List (ℕ × PBConstr)) : Prop :=
  runTop I.F none (State.init I.F none (some I.pres)) e.steps.reverse = some (I.state db e.next) ∧
    (∀ x ∈ db, x.1 < e.next) ∧ (∀ x ∈ db, ∀ v ∈ x.2.vars, v < e.var) ∧ I.n ≤ e.var ∧
    lookup db 1 = some I.capC.normalize ∧ lookup db 2 = some I.profC.normalize

/-- `db'` extends `db`. -/
private def Sub (db db' : List (ℕ × PBConstr)) : Prop :=
  ∀ k c, lookup db k = some c → lookup db' k = some c

private theorem Sub.refl (db : List (ℕ × PBConstr)) : Sub db db := fun _ _ h => h

private theorem Sub.trans {a b c : List (ℕ × PBConstr)} (h₁ : Sub a b) (h₂ : Sub b c) : Sub a c :=
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

private theorem push_steps (e : Acc) (ss : List TopStep) (dn dv : ℕ) :
    (e.push ss dn dv).steps.reverse = e.steps.reverse ++ ss := by
  simp [Acc.push]

private theorem lookup_cons_self (db : List (ℕ × PBConstr)) (m : ℕ) (c : PBConstr) :
    lookup ((m, c) :: db) m = some c := by
  simp [lookup]

private theorem lookup_cons_ne {db : List (ℕ × PBConstr)} {m k : ℕ} {c : PBConstr} (h : m ≠ k) :
    lookup ((m, c) :: db) k = lookup db k := by
  simp [lookup, h]

private theorem lookup_cons_eq {db : List (ℕ × PBConstr)} {m k : ℕ} {c : PBConstr} (h : m = k) :
    lookup ((m, c) :: db) k = some c := by
  subst h; simp [lookup]

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

private theorem vars_initDb : ∀ x ∈ initDb I.F, ∀ v ∈ x.2.vars, v < I.n := by
  intro x hx v hv
  simp only [initDb, F, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hx
  have key : ∀ c ∈ [I.capC, I.profC], ∀ v ∈ c.vars, v < I.n := by
    intro c hc v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
      simpa [capC, profC, PBConstr.vars] using hv
  rcases hx with rfl | rfl
  · exact key _ (by simp) v (mem_vars_of_mem_vars_normalize hv)
  · exact key _ (by simp) v (mem_vars_of_mem_vars_normalize hv)

/-- The proof starts at the formula. -/
private theorem run_init : I.Run ⟨[], 3, I.n⟩ (initDb I.F) := by
  refine ⟨by simp [runTop_nil, state, State.init, F], ?_, fun x hx v hv => I.vars_initDb x hx v hv,
    le_rfl, by simp [lookup, initDb, F], by simp [lookup, initDb, F]⟩
  intro x hx
  simp only [initDb, F, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> simp

/-- **A `pol` step runs.** -/
private theorem Run.pol {e : Acc} {db : List (ℕ × PBConstr)} (h : I.Run e db) {ops : List PolOp}
    {c : PBConstr} (hp : polEval db ops [] = some [c]) (hv : ∀ v ∈ c.vars, v < e.var) :
    I.Run (e.push [.step (.pol ops)] 1 0) ((e.next, c) :: db) ∧ Sub db ((e.next, c) :: db) := by
  have hs := sub_cons h.2.1 c
  refine ⟨⟨?_, ?_, ?_, by simpa [Acc.push] using h.2.2.2.1, hs _ _ h.2.2.2.2.1,
    hs _ _ h.2.2.2.2.2⟩, hs⟩
  · rw [push_steps, runTop_append, h.1, Option.bind_some, runTop_cons,
      stepTop_step_of_ne_del _ _ _ (by intro ids h; cases h)]
    simp [state, runStep, hp, runTop_nil, Acc.push]
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp [Acc.push]
    · have := h.2.1 x hx; simp [Acc.push]; omega
  · intro x hx v hv'
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simpa [Acc.push] using hv _ hv'
    · simpa [Acc.push] using h.2.2.1 x hx v hv'

/-- **A `rup` step runs** when the checker accepts it. -/
private theorem Run.rup {e : Acc} {db : List (ℕ × PBConstr)} (h : I.Run e db) {c : PBConstr}
    {hs : List Hint} (hr : rup db c hs = true) (hv : ∀ v ∈ c.vars, v < e.var) :
    I.Run (e.push [.step (.rup c hs)] 1 0) ((e.next, c.normalize) :: db) ∧
      Sub db ((e.next, c.normalize) :: db) := by
  have hsub := sub_cons h.2.1 c.normalize
  refine ⟨⟨?_, ?_, ?_, by simpa [Acc.push] using h.2.2.2.1, hsub _ _ h.2.2.2.2.1,
    hsub _ _ h.2.2.2.2.2⟩, hsub⟩
  · rw [push_steps, runTop_append, h.1, Option.bind_some, runTop_cons,
      stepTop_step_of_ne_del _ _ _ (by intro ids h; cases h)]
    simp [state, runStep, hr, runTop_nil, Acc.push]
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp [Acc.push]
    · have := h.2.1 x hx; simp [Acc.push]; omega
  · intro x hx v hv'
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simpa [Acc.push] using hv _ (mem_vars_of_mem_vars_normalize hv')
    · simpa [Acc.push] using h.2.2.1 x hx v hv'

private theorem vars_impl {l : Literal ℕ} {c : PBConstr} {x : ℕ} (h : x ∈ (impl [l] c).vars) :
    x = l.1 ∨ x ∈ c.vars := by
  obtain ⟨v, b⟩ := l
  simp only [PBConstr.vars, impl, List.map_cons, List.map_nil, List.singleton_append,
    List.mem_cons] at h
  rcases h with h | h
  · left; simpa [Std.Sat.Literal.negate] using h
  · right; exact h

/-- **A reification by the next free variable runs**, for a satisfiable constraint over older
variables. -/
private theorem Run.reify {e : Acc} {db : List (ℕ × PBConstr)} (h : I.Run e db) {c : PBConstr}
    (hv : ∀ v ∈ c.vars, v < e.var) (hsat : ∃ σ, c.Holds σ) :
    I.Run (e.push (reify e.var c) 4 1)
        ((e.next + 3, (impl [(e.var, false)] c.negate).normalize) ::
          (e.next + 1, (impl [(e.var, true)] c).normalize) :: db) ∧
      Sub db ((e.next + 3, (impl [(e.var, false)] c.negate).normalize) ::
          (e.next + 1, (impl [(e.var, true)] c).normalize) :: db) := by
  obtain ⟨hrun, hid, hvar, hn, h1, h2⟩ := h
  have hsub : Sub db ((e.next + 3, (impl [(e.var, false)] c.negate).normalize) ::
      (e.next + 1, (impl [(e.var, true)] c).normalize) :: db) :=
    (sub_cons (m := e.next + 1) (fun x hx => by have := hid x hx; omega) _).trans
      (sub_cons (fun x hx => by
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · simp
        · have := hid x hx; omega) _)
  have hz : e.var ∉ c.vars := fun h' => by have := hv _ h'; omega
  have hnc : ¬ c.normalize.IsContradiction := fun hc => by
    obtain ⟨σ, hσ⟩ := hsat
    exact hc.not_holds σ ((holds_normalize σ c).2 hσ)
  have hfresh : (I.state db e.next).fresh e.var = true := by
    simp only [State.fresh, State.avoidsVar, state, State.init, Bool.and_eq_true,
      List.all_eq_true, Option.all_none, Option.all_some, List.mem_append]
    refine ⟨fun x hx => ?_, ?_⟩
    · have : e.var ∉ x.2.vars := fun hm => by
        rcases hx with hx | hx
        · have := hvar x hx _ hm; omega
        · have := I.vars_initDb x hx _ hm; omega
      simpa using this
    · simp [pres]; omega
  refine ⟨⟨?_, ?_, ?_, by simp [Acc.push]; omega, hsub _ _ h1, hsub _ _ h2⟩, hsub⟩
  · rw [push_steps, runTop_append, hrun, Option.bind_some, runTop_reify hfresh hz hnc]
    rfl
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · simp [Acc.push]
    · simp [Acc.push]
    · have := hid x hx; simp [Acc.push]; omega
  · intro x hx v hv'
    simp only [List.mem_cons] at hx
    simp only [Acc.push]
    rcases hx with rfl | rfl | hx
    · rcases vars_impl (mem_vars_of_mem_vars_normalize hv') with h' | h'
      · simp at h'; omega
      · have := hv _ (vars_negate_sub h'); omega
    · rcases vars_impl (mem_vars_of_mem_vars_normalize hv') with h' | h'
      · simp at h'; omega
      · have := hv _ h'; omega
    · have := hvar x hx v hv'; omega

private theorem push_push (e : Acc) (a b : List TopStep) (m k m' k' : ℕ) :
    (e.push a m k).push b m' k' = e.push (a ++ b) (m + m') (k + k') := by
  simp [Acc.push, Nat.add_assoc]

/-! ### Nodes -/

/-- The states of layer `i` weigh at most `∑_{j<i} wⱼ` and leave out at most `∑_{j<i} pⱼ`. -/
private theorem le_tot_of_mem_lay : ∀ {i : ℕ} {st : St}, st ∈ I.lay i →
    st.1 ≤ tot I.w i ∧ st.2 ≤ tot I.p i
  | 0, st, h => by
    simp only [lay, List.mem_singleton] at h
    subst h; simp [tot]
  | i + 1, st, h => by
    simp only [lay, nextLay, List.mem_dedup, List.mem_flatMap, List.mem_map] at h
    obtain ⟨st₀, h₀, b, -, rfl⟩ := h
    have := le_tot_of_mem_lay h₀
    simp only [succSt, tot_succ, bit]
    split_ifs <;> simp_all <;> omega

/-- **The facts about a node** of layer `i` in the database `db`, its variables below `V`. -/
private structure NodeOk (i : ℕ) (db : List (ℕ × PBConstr)) (V : ℕ) (u : Node) : Prop where
  lay : u.st ∈ I.lay i
  nW : I.n ≤ u.W
  nP : I.n ≤ u.P
  W : u.W < V
  P : u.P < V
  S : u.S < V
  wf : lookup db u.wf = some (impl [(u.W, true)] (I.cW i u.st)).normalize
  wb : lookup db u.wb = some (impl [(u.W, false)] (I.cW i u.st).negate).normalize
  pf : lookup db u.pf = some (impl [(u.P, true)] (I.cP i u.st)).normalize
  pb : lookup db u.pb = some (impl [(u.P, false)] (I.cP i u.st).negate).normalize
  sf : lookup db u.sf = some (impl [(u.S, true)] (cS u.W u.P)).normalize
  sb : lookup db u.sb = some (impl [(u.S, false)] (cS u.W u.P).negate).normalize

private theorem NodeOk.mono {i : ℕ} {db db' : List (ℕ × PBConstr)} {V V' : ℕ} {u : Node}
    (h : I.NodeOk i db V u) (hs : Sub db db') (hV : V ≤ V') : I.NodeOk i db' V' u :=
  ⟨h.lay, h.nW, h.nP, by have := h.W; omega, by have := h.P; omega, by have := h.S; omega,
    hs _ _ h.wf, hs _ _ h.wb, hs _ _ h.pf, hs _ _ h.pb, hs _ _ h.sf, hs _ _ h.sb⟩

private theorem vars_dimC {a : ℕ → ℕ} {pol : Bool} {i d x : ℕ} (h : x ∈ (dimC a pol i d).vars) :
    x < i := vars_sumTerms h

/-- **Creating a layer runs**, and gives nodes with their facts. -/
private theorem mkLayer_spec {i : ℕ} (hi : i ≤ I.n) : ∀ (sts : List St) (e : Acc)
    (db : List (ℕ × PBConstr)), I.Run e db → (∀ st ∈ sts, st ∈ I.lay i) →
    ∃ db', I.Run (I.mkLayer i e sts).1 db' ∧ Sub db db' ∧
      (I.mkLayer i e sts).2.map (·.st) = sts ∧
      (∀ u ∈ (I.mkLayer i e sts).2, I.NodeOk i db' (I.mkLayer i e sts).1.var u) ∧
      e.var ≤ (I.mkLayer i e sts).1.var
  | [], e, db, h, _ => ⟨db, h, Sub.refl _, rfl, by simp [mkLayer], by simp [mkLayer]⟩
  | st :: sts, e, db, h, hst => by
    have hl := hst st List.mem_cons_self
    have hb := I.le_tot_of_mem_lay hl
    have hn := h.2.2.2.1
    -- The three reifications.
    obtain ⟨h₁, s₁⟩ := Run.reify I h (c := I.cW i st)
      (fun v hv => by have := vars_dimC hv; omega)
      ⟨fun _ => true, by rw [cW, holds_dimC, part_const]; exact hb.1⟩
    obtain ⟨h₂, s₂⟩ := Run.reify I h₁ (c := I.cP i st)
      (fun v hv => by have := vars_dimC hv; simp [Acc.push]; omega)
      ⟨fun _ => false, by rw [cP, holds_dimC, part_const]; exact hb.2⟩
    obtain ⟨h₃, s₃⟩ := Run.reify I h₂ (c := cS e.var (e.var + 1))
      (fun v hv => by
        simp only [cS, PBConstr.vars, List.map_cons, List.map_nil, termVar_mk,
          List.mem_cons, List.not_mem_nil, or_false] at hv
        simp only [Acc.push]; omega)
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
    obtain ⟨db', hr, hs, hmap, hok, hv⟩ := mkLayer_spec hi sts _ _ h₃'
      (fun s hs => hst s (List.mem_cons_of_mem _ hs))
    refine ⟨db', hr, s₁.trans (s₂.trans (s₃.trans hs)), ?_, ?_, ?_⟩
    · simp only [mkLayer, List.map_cons, hmap]; rfl
    · simp only [mkLayer, List.mem_cons]
      rintro u (rfl | hu)
      · have hv' := le_trans
          (by simp [Acc.push] : e.var + 3 ≤ (e.push (I.nodeSteps i (mkNode e st)) 12 3).var) hv
        simp only [mkNode] at hv' ⊢
        refine ⟨hl, hn, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
          by dsimp only; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        · refine hs _ _ ?_
          simp (disch := omega) only [Acc.push, lookup_cons_ne, lookup_cons_eq]
      · exact hok u hu
    · simp only [mkLayer]; exact le_trans (by simp [Acc.push]) hv

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

private theorem RupOk.mono {db : List (ℕ × PBConstr)} {neg : PBConstr} {hs : List Hint}
    {K K' : List (Literal ℕ)} (h : RupOk db neg hs K) (hK : ∀ l ∈ K, l ∈ K') :
    RupOk db neg hs K' :=
  fun ρ hρ hK' => h ρ hρ fun l hl => hK' l (hK l hl)

/-- A run of hints each of which implies one literal from `K`. -/
private theorem RupOk.imps {db : List (ℕ × PBConstr)} {neg : PBConstr} {K₀ : List (Literal ℕ)}
    {rest : List Hint} :
    ∀ (xs : List (Hint × Literal ℕ)) (K : List (Literal ℕ)), (∀ l ∈ K₀, l ∈ K) →
      (∀ x ∈ xs, ∃ c, resolve db neg x.1 = some c ∧ (c.terms.map termVar).Nodup ∧
        ∀ σ, Consistent σ K₀ → c.Holds σ → Literal.eval σ x.2 = true) →
      RupOk db neg rest (xs.map (·.2) ++ K) → RupOk db neg (xs.map (·.1) ++ rest) K
  | [], K, _, _, h => by simpa using h
  | x :: xs, K, hK, hx, h => by
    obtain ⟨c, hc, hd, hi⟩ := hx x List.mem_cons_self
    refine RupOk.imp (L := [x.2]) hc hd
      (fun σ hσ hcσ => by
        have := hi σ (fun l hl => hσ l (hK l hl)) hcσ
        intro l hl; simp only [List.mem_singleton] at hl; subst hl; exact this) ?_
    refine RupOk.imps xs ([x.2] ++ K) (fun l hl => List.mem_append_right _ (hK l hl))
      (fun y hy => hx y (List.mem_cons_of_mem _ hy)) (RupOk.mono h ?_)
    intro l hl
    simp only [List.map_cons, List.mem_append, List.mem_cons] at hl ⊢
    tauto

private theorem lit_of {σ : ℕ → Bool} {K : List (Literal ℕ)} (h : Consistent σ K) {v : ℕ}
    {b : Bool} (hl : (v, b) ∈ K) : σ v = b := by
  simpa using h _ hl

private theorem vars_of_lookup {e : Acc} {db : List (ℕ × PBConstr)} (h : I.Run e db) {k : ℕ}
    {c : PBConstr} (hk : lookup db k = some c) : ∀ v ∈ c.vars, v < e.var :=
  fun v hv => h.2.2.1 _ (mem_of_lookup hk) v hv

private theorem vars_add {c d : PBConstr} {x : ℕ} (h : x ∈ (c.add d).vars) :
    x ∈ c.vars ∨ x ∈ d.vars := by
  have := mem_vars_of_mem_vars_normalize h
  simpa [PBConstr.vars] using this

private theorem polEval_add {db : List (ℕ × PBConstr)} {a b : ℕ} {c d : PBConstr}
    (ha : lookup db a = some c) (hb : lookup db b = some d) :
    polEval db [.id a, .id b, .add] [] = some [c.add d] := by
  simp [polEval, ha, hb]

/-- A `pol` step adding two constraints of the database runs. -/
private theorem Run.add {e : Acc} {db : List (ℕ × PBConstr)} (h : I.Run e db) {a b : ℕ}
    {c d : PBConstr} (ha : lookup db a = some c) (hb : lookup db b = some d) :
    I.Run (e.push [.step (.pol [.id a, .id b, .add])] 1 0) ((e.next, c.add d) :: db) ∧
      Sub db ((e.next, c.add d) :: db) :=
  Run.pol I h (polEval_add ha hb) fun v hv => (vars_add hv).elim
    (I.vars_of_lookup h ha v) (I.vars_of_lookup h hb v)

private theorem vars_clause {ls : List (Literal ℕ)} {x : ℕ} (h : x ∈ (clause ls).vars) :
    ∃ l ∈ ls, l.1 = x := by
  simpa [clause, PBConstr.vars, List.map_map] using h

private theorem vars_negD {l : Literal ℕ} (h : l ∈ I.negD) : l.1 < I.n := by
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h
  obtain ⟨v, b⟩ := m
  simpa [Std.Sat.Literal.negate] using I.vars_fixedLits hm

/-! ### Transitions -/

/-- **A transition runs** (equations (11)–(13) and (17)–(19) of the paper): from a node `u` of
layer `i` by the value `b` to its successor `t`, the two additions and the RUP step derive
`S_u ∧ (xᵢ = b) ⇒ S_t`. -/
private theorem trSteps_spec {i : ℕ} (hi : i < I.n) {e : Acc} {db : List (ℕ × PBConstr)}
    (h : I.Run e db) {u t : Node} {b : Bool} (hu : I.NodeOk i db e.var u)
    (ht : I.NodeOk (i + 1) db e.var t) (hst : t.st = I.succSt i u.st b) :
    ∃ db', I.Run (e.push (trSteps i u b t e) 3 0) db' ∧ Sub db db' ∧
      lookup db' (e.next + 2) = some (trClause i u b t).normalize := by
  obtain ⟨h₁, s₁⟩ := Run.add I h hu.wf ht.wb
  obtain ⟨h₂, s₂⟩ := Run.add I h₁ (s₁ _ _ hu.pf) (s₁ _ _ ht.pb)
  have hb := I.le_tot_of_mem_lay ht.lay
  set cA := (impl [(u.W, true)] (I.cW i u.st)).normalize.add
    (impl [(t.W, false)] (I.cW (i + 1) t.st).negate).normalize with hcA
  set cP' := (impl [(u.P, true)] (I.cP i u.st)).normalize.add
    (impl [(t.P, false)] (I.cP (i + 1) t.st).negate).normalize with hcP
  have hlookA : lookup ((e.next + 1, cP') :: (e.next, cA) :: db) e.next = some cA := by
    simp (disch := omega) only [lookup_cons_ne, lookup_cons_eq]
  have hlookP : lookup ((e.next + 1, cP') :: (e.next, cA) :: db) (e.next + 1) = some cP' :=
    lookup_cons_self _ _ _
  have hr : rup ((e.next + 1, cP') :: (e.next, cA) :: db)
      (trClause i u b t) [.neg, .id u.sf, .id e.next, .id (e.next + 1), .id t.sb] = true := by
    refine rup_clause ?_
    simp only [List.map_cons, List.map_nil, Std.Sat.Literal.negate, Bool.not_not,
      Bool.not_false, Bool.not_true, List.append_nil]
    refine RupOk.id_imp (L := [(u.W, true), (u.P, true)]) (s₂ _ _ (s₁ _ _ hu.sf))
      (nodup_vars_normalize _) ?_ ?_
    · intro σ hσ hc
      rw [holds_normalize, holds_impl] at hc
      have := (holds_cS σ _ _).1 (hc (by simp [lit_of hσ (v := u.S) (b := true) (by simp)]))
      simp [Consistent, this]
    refine RupOk.id_imp (L := [(t.W, true)]) hlookA (nodup_vars_normalize _) ?_ ?_
    · intro σ hσ hc
      have := trans_dim (a := I.w) (pol := true) (b := b) (i := i) (d := u.st.1) (zu := u.W)
        (zt := t.W) (by have := hu.nW; omega) (by have := ht.nW; omega)
        (by rw [hst] at hb; exact hb.1)
        (by rw [hcA] at hc; simp only [cW, hst, succSt] at hc; exact hc)
        (lit_of hσ (by simp)) (lit_of hσ (by simp))
      simp [Consistent, this]
    refine RupOk.id_imp (L := [(t.P, true)]) hlookP (nodup_vars_normalize _) ?_ ?_
    · intro σ hσ hc
      have := trans_dim (a := I.p) (pol := false) (b := b) (i := i) (d := u.st.2) (zu := u.P)
        (zt := t.P) (by have := hu.nP; omega) (by have := ht.nP; omega)
        (by rw [hst] at hb; exact hb.2)
        (by rw [hcP] at hc; simp only [cP, hst, succSt] at hc; exact hc)
        (lit_of hσ (by simp)) (lit_of hσ (by simp))
      simp [Consistent, this]
    refine RupOk.id_conflict (s₂ _ _ (s₁ _ _ ht.sb)) (nodup_vars_normalize _) ?_
    intro σ hσ hc
    rw [holds_normalize, holds_impl_neg_negate] at hc
    have h1 := hc ((holds_cS σ _ _).2 ⟨lit_of hσ (by simp), lit_of hσ (by simp)⟩)
    have h2 := lit_of hσ (v := t.S) (b := false) (by simp)
    simp [h1] at h2
  obtain ⟨h₃, s₃⟩ := Run.rup I h₂ hr (fun v hv => by
    obtain ⟨l, hl, rfl⟩ := vars_clause hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    simp only [Acc.push]
    rcases hl with rfl | rfl | rfl
    · exact hu.S
    · simp; have := h.2.2.2.1; omega
    · exact ht.S)
  refine ⟨_, ?_, s₁.trans (s₂.trans s₃), ?_⟩
  · rw [push_push, push_push] at h₃; simpa [trSteps] using h₃
  · simpa [Acc.push] using lookup_cons_self _ _ _

private theorem findNode_spec {L : List Node} {st : St} (h : st ∈ L.map (·.st)) :
    findNode L st ∈ L ∧ (findNode L st).st = st := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
  rcases hf : L.find? (·.st == t.st) with _ | t'
  · exact absurd (List.find?_eq_none.1 hf t ht) (by simp)
  · have := List.find?_some hf
    simp only [beq_iff_eq] at this
    simp only [findNode, hf, Option.getD_some]
    exact ⟨List.mem_of_find?_eq_some hf, this⟩

private theorem trans1_spec {i : ℕ} (hi : i < I.n) {L' : List Node} {u : Node} :
    ∀ (bs : List Bool) (e : Acc) (db : List (ℕ × PBConstr)), I.Run e db →
      I.NodeOk i db e.var u → (∀ t ∈ L', I.NodeOk (i + 1) db e.var t) →
      (∀ b ∈ bs, I.succSt i u.st b ∈ L'.map (·.st)) →
      ∃ db', I.Run (I.trans1 i L' u e bs).1 db' ∧ Sub db db' ∧
        (I.trans1 i L' u e bs).2.map (·.1) = bs ∧
        (∀ x ∈ (I.trans1 i L' u e bs).2, x.2.1 ∈ L' ∧ x.2.1.st = I.succSt i u.st x.1 ∧
          lookup db' x.2.2 = some (trClause i u x.1 x.2.1).normalize) ∧
        (I.trans1 i L' u e bs).1.var = e.var
  | [], e, db, h, _, _, _ => ⟨db, h, Sub.refl _, rfl, by simp [trans1], rfl⟩
  | b :: bs, e, db, h, hu, hL', hbs => by
    obtain ⟨htm, hts⟩ := findNode_spec (hbs b List.mem_cons_self)
    obtain ⟨db₁, h₁, s₁, hl₁⟩ := I.trSteps_spec hi h hu (hL' _ htm) hts
    obtain ⟨db', h', s', hmap, hall, hv⟩ := trans1_spec hi bs _ db₁ h₁
      (hu.mono I s₁ (by simp [Acc.push])) (fun t ht => (hL' t ht).mono I s₁ (by simp [Acc.push]))
      (fun b hb => hbs b (List.mem_cons_of_mem _ hb))
    refine ⟨db', h', s₁.trans s', by simp [trans1, hmap], ?_, by simp only [trans1]; rw [hv]; rfl⟩
    simp only [trans1, List.mem_cons]
    rintro x (rfl | hx)
    · exact ⟨htm, hts, s' _ _ hl₁⟩
    · exact hall x hx

/-- **The facts about the transitions out of a node** of layer `i` into the layer `L'`. -/
private structure OutOk (i : ℕ) (db : List (ℕ × PBConstr)) (V : ℕ) (L' : List Node) (o : Out) :
    Prop where
  u : I.NodeOk i db V o.u
  vals : o.tr.map (·.1) = vals (I.dom i)
  tr : ∀ x ∈ o.tr, x.2.1 ∈ L' ∧ x.2.1.st = I.succSt i o.u.st x.1 ∧
    lookup db x.2.2 = some (trClause i o.u x.1 x.2.1).normalize
  succ : lookup db o.succ = some (I.succClause i o.u o.tr).normalize

private theorem OutOk.mono {i : ℕ} {db db' : List (ℕ × PBConstr)} {V V' : ℕ} {L' : List Node}
    {o : Out} (h : I.OutOk i db V L' o) (hs : Sub db db') (hV : V ≤ V') : I.OutOk i db' V' L' o :=
  ⟨h.u.mono I hs hV, h.vals, fun x hx => ⟨(h.tr x hx).1, (h.tr x hx).2.1, hs _ _ (h.tr x hx).2.2⟩,
    hs _ _ h.succ⟩

private theorem holds_trClause {σ : ℕ → Bool} {i : ℕ} {u t : Node} {b : Bool} :
    (trClause i u b t).normalize.Holds σ ↔
      (σ u.S = true → σ i = b → σ t.S = true) := by
  rw [holds_normalize, trClause, holds_clause]
  cases hu : σ u.S <;> cases hi : σ i <;> cases ht : σ t.S <;> cases b <;> simp [hu, hi, ht]

/-- **A node's transitions run**, then `S_u ∧ D ⇒ ⋁ S_t` by RUP (equations (16) and (20)). -/
private theorem transOut_spec {i : ℕ} (hi : i < I.n) {L' : List Node} {e : Acc}
    {db : List (ℕ × PBConstr)} (h : I.Run e db) {u : Node} (hu : I.NodeOk i db e.var u)
    (hL' : ∀ t ∈ L', I.NodeOk (i + 1) db e.var t)
    (hbs : ∀ b ∈ vals (I.dom i), I.succSt i u.st b ∈ L'.map (·.st)) :
    ∃ db', I.Run (I.transOut i L' e u).1 db' ∧ Sub db db' ∧ (I.transOut i L' e u).2.u = u ∧
      I.OutOk i db' (I.transOut i L' e u).1.var L' (I.transOut i L' e u).2 ∧
      (I.transOut i L' e u).1.var = e.var := by
  obtain ⟨db₁, h₁, s₁, hmap, hall, hv⟩ := I.trans1_spec hi (vals (I.dom i)) e db h hu hL' hbs
  have hvo : (I.transOut i L' e u).1.var = e.var := by
    simp only [transOut, Acc.push, Nat.add_zero]; exact hv
  set r := I.trans1 i L' u e (vals (I.dom i)) with hr
  have hrup : rup db₁ (I.succClause i u r.2) (.neg :: r.2.map fun x => .id x.2.2) = true := by
    refine rup_clause ?_
    cases hd : I.dom i with
    | none =>
      rw [hd] at hmap
      obtain ⟨x₀, x₁, hr2⟩ : ∃ x₀ x₁, r.2 = [x₀, x₁] := by
        rcases h2 : r.2 with _ | ⟨x₀, _ | ⟨x₁, _ | _⟩⟩ <;> simp_all [vals]
      rw [hr2] at hmap ⊢
      simp only [vals, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
      have h₀ := hall x₀ (by rw [hr2]; simp)
      have h₁' := hall x₁ (by rw [hr2]; simp)
      rw [hmap.1] at h₀; rw [hmap.2] at h₁'
      simp only [fixNeg, hd, Option.map_none, Option.toList_none, List.nil_append,
        List.cons_append, List.map_cons, List.map_nil, Std.Sat.Literal.negate, Bool.not_false,
        Bool.not_true, List.append_nil]
      refine RupOk.id_imp (L := [(i, true)]) h₀.2.2 (nodup_vars_normalize _) ?_ ?_
      · intro σ hσ hc
        have := holds_trClause.1 hc (lit_of hσ (by simp))
        have h2 := lit_of hσ (v := x₀.2.1.S) (b := false) (by simp)
        cases hx : σ i
        · simp [this hx] at h2
        · simp [Consistent, hx]
      refine RupOk.id_conflict h₁'.2.2 (nodup_vars_normalize _) ?_
      intro σ hσ hc
      have := holds_trClause.1 hc (lit_of hσ (by simp))
        (lit_of hσ (by simp))
      have h2 := lit_of hσ (v := x₁.2.1.S) (b := false) (by simp)
      simp [this] at h2
    | some b =>
      rw [hd] at hmap
      obtain ⟨x, hr2⟩ : ∃ x, r.2 = [x] := by
        rcases h2 : r.2 with _ | ⟨x, _ | _⟩ <;> simp_all [vals]
      rw [hr2] at hmap ⊢
      simp only [vals, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
      have h₀ := hall x (by rw [hr2]; simp)
      rw [hmap] at h₀
      simp only [fixNeg, hd, Option.map_some, Option.toList_some, List.cons_append,
        List.map_cons, List.map_nil, Std.Sat.Literal.negate, Bool.not_not,
        Bool.not_false, List.append_nil]
      refine RupOk.id_conflict h₀.2.2 (nodup_vars_normalize _) ?_
      intro σ hσ hc
      have := holds_trClause.1 hc (lit_of hσ (by simp))
        (lit_of hσ (by simp))
      have h2 := lit_of hσ (v := x.2.1.S) (b := false) (by simp [Std.Sat.Literal.negate])
      simp [this] at h2
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
  · obtain ⟨h1, h2, h3⟩ := hall x hx
    exact ⟨h1, h2, s₂ _ _ h3⟩
  · exact lookup_cons_self _ _ _

private theorem trans_spec {i : ℕ} (hi : i < I.n) {L' : List Node} :
    ∀ (L : List Node) (e : Acc) (db : List (ℕ × PBConstr)), I.Run e db →
      (∀ u ∈ L, I.NodeOk i db e.var u) → (∀ t ∈ L', I.NodeOk (i + 1) db e.var t) →
      (∀ u ∈ L, ∀ b ∈ vals (I.dom i), I.succSt i u.st b ∈ L'.map (·.st)) →
      ∃ db', I.Run (I.trans i L' e L).1 db' ∧ Sub db db' ∧ (I.trans i L' e L).2.map (·.u) = L ∧
        (∀ o ∈ (I.trans i L' e L).2, I.OutOk i db' (I.trans i L' e L).1.var L' o) ∧
        (I.trans i L' e L).1.var = e.var
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

/-- Under the fixed literals and the falsity of every node of `L'`, the clause `S_u ∧ D ⇒ ⋁ S_t`
of a node whose targets are in `L'` makes `S_u` false. -/
private theorem succ_false {i : ℕ} (hi : i < I.n) {o : Out} {σ : ℕ → Bool}
    {K : List (Literal ℕ)} (hD : ∀ l ∈ I.fixedLits, l ∈ K)
    (hL' : ∀ x ∈ o.tr, (x.2.1.S, false) ∈ K) (hσ : Consistent σ K)
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
private theorem rup_alo {i : ℕ} (hi : i < I.n) {db : List (ℕ × PBConstr)} {V : ℕ}
    {L L' : List Node} {outs : List Out} {alo : ℕ} (hmap : outs.map (·.u) = L)
    (houts : ∀ o ∈ outs, I.OutOk i db V L' o)
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
    refine ⟨_, (houts o ho).succ, nodup_vars_normalize _, fun σ hσ hc => ?_⟩
    have := I.succ_false hi (fun l hl => List.mem_append_left _ hl)
      (fun x hx => List.mem_append_right _ (List.mem_map.2 ⟨_, ((houts o ho).tr x hx).1, rfl⟩))
      hσ hc
    simp [this]
  · refine RupOk.id_conflict halo (nodup_vars_normalize _) fun σ hσ hc => ?_
    rw [holds_normalize, aloClause, holds_clause] at hc
    obtain ⟨l, hl, hev⟩ := hc
    rcases List.mem_append.1 hl with hl | hl
    · have := I.eval_negD (fun m hm => hσ m (by simp [hm])) l hl
      simp [this] at hev
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hl
      rw [← hmap] at hu
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hu
      have := lit_of hσ (v := o.u.S) (b := false)
        (by simp only [List.map_map, List.mem_append, List.mem_map]; exact .inl ⟨o, ho, rfl⟩)
      simp [this] at hev

/-- **The facts about a layer** `i` of the forward pass. -/
private structure LayOk (i : ℕ) (db : List (ℕ × PBConstr)) (V : ℕ) (r : LayerRec) : Prop where
  idx : r.i = i
  lay : r.nodes.map (·.st) = I.lay i
  nodes : ∀ u ∈ r.nodes, I.NodeOk i db V u
  alo : lookup db r.alo = some (I.aloClause r.nodes).normalize

private theorem LayOk.mono {i : ℕ} {db db' : List (ℕ × PBConstr)} {V V' : ℕ} {r : LayerRec}
    (h : I.LayOk i db V r) (hs : Sub db db') (hV : V ≤ V') : I.LayOk i db' V' r :=
  ⟨h.idx, h.lay, fun u hu => (h.nodes u hu).mono I hs hV, hs _ _ h.alo⟩

/-- **The layers before layer `j`**, latest first, the nodes of layer `j` being `L'`: each with
its facts and its transitions into the layer after it. -/
private def Chain (db : List (ℕ × PBConstr)) (V : ℕ) : ℕ → List Node → List LayerRec → Prop
  | _, _, [] => True
  | j, L', r :: rs => r.i + 1 = j ∧ I.LayOk r.i db V r ∧ r.outs.map (·.u) = r.nodes ∧
      (∀ o ∈ r.outs, I.OutOk r.i db V L' o) ∧ Chain db V r.i r.nodes rs

private theorem Chain.mono {db db' : List (ℕ × PBConstr)} {V V' : ℕ} (hs : Sub db db')
    (hV : V ≤ V') : ∀ {j : ℕ} {L' : List Node} {rs : List LayerRec}, I.Chain db V j L' rs →
      I.Chain db' V' j L' rs
  | _, _, [], _ => trivial
  | _, _, _ :: _, ⟨h1, h2, h3, h4, h5⟩ =>
    ⟨h1, h2.mono I hs hV, h3, fun o ho => (h4 o ho).mono I hs hV, Chain.mono hs hV h5⟩

private theorem mem_nextLay {i : ℕ} {st : St} (hst : st ∈ I.lay i) {b : Bool}
    (hb : b ∈ vals (I.dom i)) : I.succSt i st b ∈ I.lay (i + 1) := by
  simp only [lay, nextLay, List.mem_dedup, List.mem_flatMap, List.mem_map]
  exact ⟨st, hst, b, hb, rfl⟩

/-- **The forward pass runs**: from layer `i`, the layers `i + 1, …, n` with their transitions and
at-least-one constraints. -/
private theorem fwd_spec : ∀ (k i : ℕ) (e : Acc) (L : List Node) (alo : ℕ) (recs : List LayerRec)
    (db : List (ℕ × PBConstr)), i + k = I.n → I.Run e db →
    I.LayOk i db e.var ⟨i, L, [], alo⟩ → I.Chain db e.var i L recs →
    recs.map (·.i) = (List.range i).reverse →
    ∃ db', I.Run (I.fwd k i e L alo recs).1 db' ∧ Sub db db' ∧
      ∃ rn rs, (I.fwd k i e L alo recs).2 = rn :: rs ∧
        I.LayOk I.n db' (I.fwd k i e L alo recs).1.var rn ∧
        I.Chain db' (I.fwd k i e L alo recs).1.var I.n rn.nodes rs ∧
        rs.map (·.i) = (List.range I.n).reverse
  | 0, i, e, L, alo, recs, db, hk, h, hL, hc, hidx => by
    simp only [Nat.add_zero] at hk
    subst hk
    exact ⟨db, h, Sub.refl _, _, recs, rfl, hL, hc, hidx⟩
  | k + 1, i, e, L, alo, recs, db, hk, h, hL, hc, hidx => by
    have hi : i < I.n := by omega
    have hLl : L.map (·.st) = I.lay i := hL.lay
    obtain ⟨db₁, h₁, s₁, hmap₁, hok₁, hv₁⟩ := I.mkLayer_spec (i := i + 1) (by omega)
      (I.nextLay i (L.map (·.st))) e db h (fun st hst => by
        rw [hLl] at hst; exact hst)
    set r₁ := I.mkLayer (i + 1) e (I.nextLay i (L.map (·.st))) with hr₁
    have hlay₁ : r₁.2.map (·.st) = I.lay (i + 1) := by rw [hmap₁, hLl]; rfl
    obtain ⟨db₂, h₂, s₂, hmap₂, hok₂, hv₂⟩ := I.trans_spec hi L r₁.1 db₁ h₁
      (fun u hu => (hL.nodes u hu).mono I s₁ hv₁)
      hok₁ (fun u hu b hb => by
        rw [hlay₁]
        exact I.mem_nextLay (hLl ▸ List.mem_map_of_mem hu) hb)
    set r₂ := I.trans i r₁.2 r₁.1 L with hr₂
    have hrup := I.rup_alo hi hmap₂ hok₂ (s₂ _ _ (s₁ _ _ hL.alo))
    obtain ⟨h₃, s₃⟩ := Run.rup I h₂ hrup (fun v hv => by
      obtain ⟨l, hl, rfl⟩ := vars_clause hv
      rcases List.mem_append.1 hl with hl | hl
      · have := I.vars_negD hl; have := h₂.2.2.2.1; omega
      · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hl
        rw [hv₂]; exact (hok₁ t ht).S)
    have hV : r₁.1.var ≤ (r₂.1.push [.step (.rup (I.aloClause r₁.2)
        (.neg :: r₂.2.map (fun o => .id o.succ) ++ [.id alo]))] 1 0).var := by
      simp [Acc.push, hv₂]
    have hs := s₁.trans (s₂.trans s₃)
    obtain ⟨db', h', s', rest⟩ := fwd_spec k (i + 1) _ r₁.2 r₂.1.next (⟨i, L, r₂.2, alo⟩ :: recs)
      _ (by omega) h₃
      ⟨rfl, hlay₁, fun u hu => (hok₁ u hu).mono I (s₂.trans s₃) hV,
        lookup_cons_self _ _ _⟩
      ⟨rfl, ⟨rfl, hLl, fun u hu => (hL.nodes u hu).mono I hs (le_trans hv₁ hV), hs _ _ hL.alo⟩,
        hmap₂, fun o ho => (hok₂ o ho).mono I s₃ (by rw [hv₂]; exact hV),
        hc.mono I hs (le_trans hv₁ hV)⟩
      (by simp [List.range_succ, hidx])
    exact ⟨db', h', s₁.trans (s₂.trans (s₃.trans s')), rest⟩

/-! ### The backward pass -/

/-- The refutations `dl` are in the database. -/
private def DeadOk (db : List (ℕ × PBConstr)) (dl : List (ℕ × ℕ)) : Prop :=
  ∀ x ∈ dl, lookup db x.2 = some (I.deadClause x.1).normalize

private theorem DeadOk.mono {db db' : List (ℕ × PBConstr)} {dl : List (ℕ × ℕ)}
    (h : I.DeadOk db dl) (hs : Sub db db') : I.DeadOk db' dl := fun x hx => hs _ _ (h x hx)

private theorem dlook_mem {dl : List (ℕ × ℕ)} {S : ℕ} (h : ∃ k, (S, k) ∈ dl) :
    (S, dlook dl S) ∈ dl := by
  obtain ⟨k, hk⟩ := h
  rcases hf : dl.find? (·.1 == S) with _ | x
  · exact absurd (List.find?_eq_none.1 hf _ hk) (by simp)
  · have := List.find?_some hf
    simp only [beq_iff_eq] at this
    simp only [dlook, hf, Option.map_some, Option.getD_some]
    rw [← this]
    exact List.mem_of_find?_eq_some hf

private theorem negate_deadClause (S : ℕ) :
    (I.negD ++ [(S, false)]).map Std.Sat.Literal.negate ++ [] = I.fixedLits ++ [(S, true)] := by
  simp [List.map_append, negate_negD, Std.Sat.Literal.negate]

private theorem holds_deadClause {σ : ℕ → Bool} (hD : Consistent σ I.fixedLits) {S : ℕ}
    (h : (I.deadClause S).normalize.Holds σ) : σ S = false := by
  rw [holds_normalize, deadClause, holds_clause] at h
  obtain ⟨l, hl, hev⟩ := h
  rcases List.mem_append.1 hl with hl | hl
  · simp [I.eval_negD hD l hl] at hev
  · simp only [List.mem_singleton] at hl; subst hl; simpa using hev

private theorem lhs_range (σ : ℕ → Bool) (a : ℕ → ℕ) (pol : Bool) (m : ℕ) :
    lhs σ ((List.range m).map fun j => (a j, (j, pol))) = part σ a pol m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [part_succ, ← ih]
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, lhs_append,
      lhs_cons, lhs_nil, termVal, Literal.eval_mk, bit]
    cases σ m <;> cases pol <;> simp

private theorem nodup_range (a : ℕ → ℕ) (pol : Bool) (m : ℕ) :
    (((List.range m).map fun j => (a j, (j, pol))).map termVar).Nodup := by
  simpa [List.map_map, Function.comp_def] using List.nodup_range

private theorem consistent_fixed {σ : ℕ → Bool} {K : List (Literal ℕ)}
    (h : Consistent σ (I.fixedLits ++ K)) :
    Consistent σ I.fixedLits := (consistent_append.1 h).1

/-- **The refutations of the last layer run** (equations (14)–(15) of the paper, against the
capacity or the profit constraint). -/
private theorem deadFinal_spec : ∀ (ts : List Node) (e : Acc) (db : List (ℕ × PBConstr)),
    I.Run e db → (∀ t ∈ ts, I.NodeOk I.n db e.var t) →
    ∃ db', I.Run (I.deadFinal e ts).1 db' ∧ Sub db db' ∧ I.DeadOk db' (I.deadFinal e ts).2 ∧
      (∀ t ∈ ts, I.finalOk t.st = false → ∃ k, (t.S, k) ∈ (I.deadFinal e ts).2) ∧
      (I.deadFinal e ts).1.var = e.var
  | [], e, db, h, _ => ⟨db, h, Sub.refl _, by simp [deadFinal, DeadOk], by simp, rfl⟩
  | t :: ts, e, db, h, hts => by
    have ht := hts t List.mem_cons_self
    by_cases hf : I.finalOk t.st = true
    · obtain ⟨db', h', s', hd', hall, hv⟩ := deadFinal_spec ts e db h
        (fun u hu => hts u (List.mem_cons_of_mem _ hu))
      refine ⟨db', by simpa [deadFinal, hf] using h', s', by simpa [deadFinal, hf] using hd', ?_,
        by simpa [deadFinal, hf] using hv⟩
      simp only [deadFinal, hf, ↓reduceIte, List.mem_cons]
      rintro u (rfl | hu) hu'
      · simp [hf] at hu'
      · exact hall u hu hu'
    · have hb := I.le_tot_of_mem_lay ht.lay
      have hf' : ¬ (t.st.1 ≤ I.C ∧ t.st.2 + I.P ≤ tot I.p I.n) := by simpa [finalOk] using hf
      -- The addition, then the RUP step.
      have key : ∃ c, polEval db (if t.st.1 ≤ I.C then [PolOp.id t.pf, .id 2, .add]
            else [.id t.wf, .id 1, .add]) [] = some [c] ∧ (∀ v ∈ c.vars, v < e.var) ∧
          (c.terms.map termVar).Nodup ∧ ∀ σ, σ t.W = true → σ t.P = true → ¬ c.Holds σ := by
        split_ifs with hC
        · refine ⟨_, polEval_add ht.pf h.2.2.2.2.2, fun v hv => (vars_add hv).elim
            (I.vars_of_lookup h ht.pf v) (I.vars_of_lookup h h.2.2.2.2.2 v),
            nodup_vars_normalize _, fun σ _ hP hA => ?_⟩
          have := final_dim (a := I.p) (pol := false) (m := I.n) (d := t.st.2) (z := t.P)
            ht.nP (G := I.profC) (nodup_range _ _ _) (fun σ => lhs_range σ _ _ _) hA hP
          exact hf' ⟨hC, by simpa [profC] using this⟩
        · refine ⟨_, polEval_add ht.wf h.2.2.2.2.1, fun v hv => (vars_add hv).elim
            (I.vars_of_lookup h ht.wf v) (I.vars_of_lookup h h.2.2.2.2.1 v),
            nodup_vars_normalize _, fun σ hW _ hA => ?_⟩
          have := final_dim (a := I.w) (pol := true) (m := I.n) (d := t.st.1) (z := t.W)
            ht.nW (G := I.capC) (nodup_range _ _ _) (fun σ => lhs_range σ _ _ _) hA hW
          simp only [capC] at this
          omega
      obtain ⟨c, hp, hvc, hnd, hsem⟩ := key
      obtain ⟨h₁, s₁⟩ := Run.pol I h hp hvc
      have hr : rup ((e.next, c) :: db) (I.deadClause t.S) [.neg, .id t.sf, .id e.next] = true := by
        refine rup_clause ?_
        rw [negate_deadClause]
        refine RupOk.id_imp (L := [(t.W, true), (t.P, true)]) (s₁ _ _ ht.sf)
          (nodup_vars_normalize _) (fun σ hσ hc => ?_) ?_
        · rw [holds_normalize, holds_impl] at hc
          have := (holds_cS σ _ _).1 (hc (by simp [lit_of hσ (v := t.S) (b := true) (by simp)]))
          simp [Consistent, this]
        exact RupOk.id_conflict (lookup_cons_self _ _ _) hnd fun σ hσ hc =>
          hsem σ (lit_of hσ (by simp)) (lit_of hσ (by simp)) hc
      obtain ⟨h₂, s₂⟩ := Run.rup I h₁ hr (fun v hv => by
        obtain ⟨l, hl, rfl⟩ := vars_clause hv
        simp only [Acc.push]
        rcases List.mem_append.1 hl with hl | hl
        · have := I.vars_negD hl; have := h.2.2.2.1; omega
        · simp only [List.mem_singleton] at hl; subst hl; exact ht.S)
      rw [push_push] at h₂
      obtain ⟨db', h', s', hd', hall, hv⟩ := deadFinal_spec ts _ _ h₂
        (fun u hu => (hts u (List.mem_cons_of_mem _ hu)).mono I (s₁.trans s₂) (by simp [Acc.push]))
      have hfF : I.finalOk t.st = false := by simpa using hf
      refine ⟨db', by simpa [deadFinal, hfF] using h', s₁.trans (s₂.trans s'), ?_, ?_, ?_⟩
      · simp only [deadFinal, hfF, Bool.false_eq_true, ↓reduceIte, DeadOk, List.mem_cons,
          forall_eq_or_imp]
        refine ⟨s' _ _ ?_, hd'⟩
        simpa [Acc.push] using lookup_cons_self _ _ _
      · intro u hu hu'
        simp only [deadFinal, hfF, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
        rcases List.mem_cons.1 hu with rfl | hu
        · exact ⟨_, .inl rfl⟩
        · obtain ⟨k, hk⟩ := hall u hu hu'
          exact ⟨k, .inr hk⟩
      · simp only [deadFinal, hfF, Bool.false_eq_true, ↓reduceIte]
        simpa [Acc.push] using hv

/-- **The refutations of an earlier layer run**: a state all of whose targets are refuted is
refuted by RUP. -/
private theorem deadLayer_spec {i : ℕ} (hi : i < I.n) {A : List St} {dl : List (ℕ × ℕ)}
    {L' : List Node} : ∀ (os : List Out) (e : Acc) (db : List (ℕ × PBConstr)), I.Run e db →
    (∀ o ∈ os, I.OutOk i db e.var L' o) → I.DeadOk db dl →
    (∀ t ∈ L', t.st ∉ A → ∃ k, (t.S, k) ∈ dl) →
    ∃ db', I.Run (I.deadLayer i A dl e os).1 db' ∧ Sub db db' ∧
      I.DeadOk db' (I.deadLayer i A dl e os).2 ∧
      (∀ o ∈ os, ((vals (I.dom i)).any fun b => I.succSt i o.u.st b ∈ A) = false →
        ∃ k, (o.u.S, k) ∈ (I.deadLayer i A dl e os).2) ∧
      (I.deadLayer i A dl e os).1.var = e.var
  | [], e, db, h, _, _, _ => ⟨db, h, Sub.refl _, by simp [deadLayer, DeadOk], by simp, rfl⟩
  | o :: os, e, db, h, hos, hdl, hL' => by
    have ho := hos o List.mem_cons_self
    by_cases hany : ((vals (I.dom i)).any fun b => I.succSt i o.u.st b ∈ A) = true
    · obtain ⟨db', h', s', hd', hall, hv⟩ := deadLayer_spec hi os e db h
        (fun u hu => hos u (List.mem_cons_of_mem _ hu)) hdl hL'
      refine ⟨db', by simpa [deadLayer, hany] using h', s', by simpa [deadLayer, hany] using hd',
        ?_, by simpa [deadLayer, hany] using hv⟩
      simp only [deadLayer, hany, ↓reduceIte, List.mem_cons]
      rintro u (rfl | hu) hu'
      · simp [hany] at hu'
      · exact hall u hu hu'
    · have hany' : ((vals (I.dom i)).any fun b => I.succSt i o.u.st b ∈ A) = false := by
        simpa using hany
      -- Every target is refuted.
      have hdead : ∀ x ∈ o.tr, (x.2.1.S, dlook dl x.2.1.S) ∈ dl := by
        intro x hx
        obtain ⟨htm, hts, -⟩ := ho.tr x hx
        refine dlook_mem (hL' _ htm fun hA => ?_)
        have hb : x.1 ∈ vals (I.dom i) := ho.vals ▸ List.mem_map_of_mem hx
        simp only [List.any_eq_false, decide_eq_true_eq] at hany'
        exact hany' _ hb (hts ▸ hA)
      have hr : rup db (I.deadClause o.u.S)
          (.neg :: o.tr.map (fun x => .id (dlook dl x.2.1.S)) ++ [.id o.succ]) = true := by
        refine rup_clause ?_
        rw [negate_deadClause]
        have := RupOk.imps (db := db) (neg := (I.deadClause o.u.S).negate)
          (K₀ := I.fixedLits ++ [(o.u.S, true)]) (rest := [.id o.succ])
          (o.tr.map fun x => (Hint.id (dlook dl x.2.1.S), (x.2.1.S, false))) _ (fun l hl => hl)
          ?_ ?_
        · rw [List.map_map] at this; exact this
        · intro y hy
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
          refine ⟨_, hdl _ (hdead x hx), nodup_vars_normalize _, fun σ hσ hc => ?_⟩
          have := I.holds_deadClause (I.consistent_fixed hσ) hc
          simp [this]
        · refine RupOk.id_conflict ho.succ (nodup_vars_normalize _) fun σ hσ hc => ?_
          have := I.succ_false hi (o := o)
            (K := (o.tr.map fun x => (Hint.id (dlook dl x.2.1.S), (x.2.1.S, false))).map (·.2) ++
              (I.fixedLits ++ [(o.u.S, true)])) (fun l hl => by simp [hl])
            (fun x hx => by
              simp only [List.mem_append, List.mem_map]; left; exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩) hσ hc
          have h2 := lit_of hσ (v := o.u.S) (b := true) (by simp)
          simp [this] at h2
      obtain ⟨h₁, s₁⟩ := Run.rup I h hr (fun v hv => by
        obtain ⟨l, hl, rfl⟩ := vars_clause hv
        rcases List.mem_append.1 hl with hl | hl
        · have := I.vars_negD hl; have := h.2.2.2.1; omega
        · simp only [List.mem_singleton] at hl; subst hl; exact ho.u.S)
      obtain ⟨db', h', s', hd', hall, hv⟩ := deadLayer_spec hi os _ _ h₁
        (fun u hu => (hos u (List.mem_cons_of_mem _ hu)).mono I s₁ (by simp [Acc.push]))
        (hdl.mono I s₁) hL'
      refine ⟨db', by simpa [deadLayer, hany'] using h', s₁.trans s', ?_, ?_, ?_⟩
      · simp only [deadLayer, hany', Bool.false_eq_true, ↓reduceIte, DeadOk, List.mem_cons,
          forall_eq_or_imp]
        exact ⟨s' _ _ (lookup_cons_self _ _ _), hd'⟩
      · intro u hu hu'
        simp only [deadLayer, hany', Bool.false_eq_true, ↓reduceIte, List.mem_cons]
        rcases List.mem_cons.1 hu with rfl | hu
        · exact ⟨_, .inl rfl⟩
        · obtain ⟨k, hk⟩ := hall u hu hu'
          exact ⟨k, .inr hk⟩
      · simp only [deadLayer, hany', Bool.false_eq_true, ↓reduceIte]
        simpa [Acc.push] using hv

private theorem alive_lt {i : ℕ} (hi : i < I.n) :
    I.alive i = (I.lay i).filter fun st =>
      (vals (I.dom i)).any fun b => I.succSt i st b ∈ I.alive (i + 1) := by
  simp only [alive]
  rw [show I.n - i = (I.n - (i + 1)) + 1 by omega]
  rfl

private theorem alive_n : I.alive I.n = (I.lay I.n).filter I.finalOk := by
  simp [alive, aliveAt]

/-- What the backward pass returns for a layer `r` before the last: its facts, the alive states
and the refutations of the layer `next` after it. -/
private structure BackAt (db : List (ℕ × PBConstr)) (V : ℕ) (next : List Node)
    (x : LayerRec × List St × List (ℕ × ℕ)) : Prop where
  lt : x.1.i < I.n
  lay : I.LayOk x.1.i db V x.1
  outs : x.1.outs.map (·.u) = x.1.nodes
  out : ∀ o ∈ x.1.outs, I.OutOk x.1.i db V next o
  alive : x.2.1 = I.alive (x.1.i + 1)
  dead : I.DeadOk db x.2.2
  cover : ∀ t ∈ next, t.st ∉ x.2.1 → ∃ k, (t.S, k) ∈ x.2.2

/-- **The backward pass runs.** -/
private theorem backAll_spec : ∀ (rs : List LayerRec) (e : Acc) (A : List St)
    (dl : List (ℕ × ℕ)) (j : ℕ) (L' : List Node) (db : List (ℕ × PBConstr)), I.Run e db →
    I.Chain db e.var j L' rs → j ≤ I.n → A = I.alive j → I.DeadOk db dl →
    (∀ t ∈ L', t.st ∉ A → ∃ k, (t.S, k) ∈ dl) →
    ∃ db', I.Run (I.backAll e A dl rs).1 db' ∧ Sub db db' ∧
      (∀ x ∈ (I.backAll e A dl rs).2, ∃ next, I.BackAt db' e.var next x) ∧
      (I.backAll e A dl rs).2.map (·.1) = rs ∧ (I.backAll e A dl rs).1.var = e.var
  | [], e, A, dl, j, L', db, h, _, _, _, _, _ =>
    ⟨db, h, Sub.refl _, by simp [backAll], rfl, rfl⟩
  | r :: rs, e, A, dl, j, L', db, h, ⟨hij, hlay, houts, hout, hc⟩, hj, hA, hdl, hcov => by
    have hi : r.i < I.n := by omega
    obtain ⟨db₁, h₁, s₁, hd₁, hall₁, hv₁⟩ := I.deadLayer_spec hi r.outs e db h hout hdl hcov
    set d := I.deadLayer r.i A dl e r.outs with hd
    have hA' : ((r.nodes.map (·.st)).filter fun st =>
        (vals (I.dom r.i)).any fun b => I.succSt r.i st b ∈ A) = I.alive r.i := by
      rw [I.alive_lt hi, hlay.lay, hA, hij]
    obtain ⟨db', h', s', hall, hmap, hv⟩ := backAll_spec rs d.1
      ((r.nodes.map (·.st)).filter fun st =>
        (vals (I.dom r.i)).any fun b => I.succSt r.i st b ∈ A) d.2 r.i r.nodes db₁ h₁
      (by rw [hv₁]; exact hc.mono I s₁ le_rfl) (by omega) hA' hd₁ (fun t ht hn => by
        rw [← houts] at ht
        obtain ⟨o, ho, rfl⟩ := List.mem_map.1 ht
        refine hall₁ o ho ?_
        have hst : o.u.st ∈ r.nodes.map (·.st) := by
          rw [← houts]; exact List.mem_map.2 ⟨o.u, List.mem_map.2 ⟨o, ho, rfl⟩, rfl⟩
        simpa [List.mem_filter, hst] using hn)
    refine ⟨db', h', s₁.trans s', ?_,
      by simp only [backAll, List.map_cons, List.cons.injEq, true_and]; exact hmap,
      by simp only [backAll]; exact hv.trans hv₁⟩
    simp only [backAll, List.mem_cons]
    rintro x (rfl | hx)
    · exact ⟨L', hi, hlay.mono I (s₁.trans s') le_rfl, houts,
        fun o ho => (hout o ho).mono I (s₁.trans s') le_rfl, by rw [hA, hij],
        hdl.mono I (s₁.trans s'), hcov⟩
    · obtain ⟨nx, hnx⟩ := hall x hx
      rw [hv₁] at hnx
      exact ⟨nx, hnx⟩

/-! ### The removals -/

private theorem tgt_tau {o : Out} {b : Bool} (hb : b ∈ o.tr.map (·.1)) :
    ∃ x ∈ o.tr, x.1 = b ∧ o.tgt b = x.2.1 ∧ o.tau b = x.2.2 := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
  rcases hf : o.tr.find? (·.1 == x.1) with _ | y
  · exact absurd (List.find?_eq_none.1 hf x hx) (by simp)
  · have := List.find?_some hf
    simp only [beq_iff_eq] at this
    exact ⟨y, List.mem_of_find?_eq_some hf, this, by simp [Out.tgt, hf],
      by simp [Out.tau, hf]⟩

private theorem negate_remClause (i : ℕ) (b : Bool) :
    (I.negD ++ [(i, !b)]).map Std.Sat.Literal.negate ++ [] = I.fixedLits ++ [(i, b)] := by
  simp [List.map_append, negate_negD, Std.Sat.Literal.negate]

/-- **A removal runs**: if every transition by `b` out of layer `r` leads to a refuted state, the
refutations, the transitions and the at-least-one constraint of the layer give `D ⇒ xᵢ ≠ b` by
RUP. -/
private theorem rup_rem {db : List (ℕ × PBConstr)} {V : ℕ} {next : List Node} {r : LayerRec}
    {A : List St} {dl : List (ℕ × ℕ)} (hx : I.BackAt db V next (r, A, dl)) {b : Bool}
    (hb : b ∈ vals (I.dom r.i)) (hall : ∀ o ∈ r.outs, I.succSt r.i o.u.st b ∉ A) :
    rup db (I.remClause r.i b) (.neg :: r.outs.map (fun o => .id (dlook dl (o.tgt b).S)) ++
      r.outs.map (fun o => .id (o.tau b)) ++ [.id r.alo]) = true := by
  -- The transition by `b` out of each node.
  have htr : ∀ o ∈ r.outs, ∃ y ∈ o.tr, y.1 = b ∧ o.tgt b = y.2.1 ∧ o.tau b = y.2.2 :=
    fun o ho => tgt_tau (((hx.out o ho).vals).symm ▸ hb)
  have hdead : ∀ o ∈ r.outs, lookup db (dlook dl (o.tgt b).S) =
      some (I.deadClause (o.tgt b).S).normalize := by
    intro o ho
    obtain ⟨y, hy, rfl, ht, -⟩ := htr o ho
    obtain ⟨hym, hys, -⟩ := (hx.out o ho).tr y hy
    rw [ht]
    exact hx.dead _ (dlook_mem (hx.cover _ hym (by rw [hys]; exact hall o ho)))
  rw [show ∀ a b c : List Hint, (Hint.neg :: a) ++ b ++ c = .neg :: (a ++ (b ++ c)) from
    fun a b c => by simp]
  refine rup_clause ?_
  rw [negate_remClause]
  have h1 := RupOk.imps (db := db) (neg := (I.remClause r.i b).negate)
    (K₀ := I.fixedLits ++ [(r.i, b)]) (rest := r.outs.map (fun o => .id (o.tau b)) ++ [.id r.alo])
    (r.outs.map fun o => (Hint.id (dlook dl (o.tgt b).S), ((o.tgt b).S, false))) _
    (fun l hl => hl) ?_ ?_
  · rw [List.map_map] at h1; exact h1
  · intro y hy
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hy
    refine ⟨_, hdead o ho, nodup_vars_normalize _, fun σ hσ hc => ?_⟩
    have := I.holds_deadClause (I.consistent_fixed hσ) hc
    simp [this]
  have h2 := RupOk.imps (db := db) (neg := (I.remClause r.i b).negate)
    (K₀ := (r.outs.map fun o => (Hint.id (dlook dl (o.tgt b).S), ((o.tgt b).S, false))).map
      (·.2) ++ (I.fixedLits ++ [(r.i, b)])) (rest := [.id r.alo])
    (r.outs.map fun o => (Hint.id (o.tau b), (o.u.S, false))) _ (fun l hl => hl) ?_ ?_
  · rw [List.map_map] at h2; exact h2
  · intro y hy
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hy
    obtain ⟨z, hz, hzb, ht, hτ⟩ := htr o ho
    obtain ⟨-, -, hzl⟩ := (hx.out o ho).tr z hz
    refine ⟨_, by rw [hτ]; exact hzl, nodup_vars_normalize _, fun σ hσ hc => ?_⟩
    rw [hzb] at hc
    have h3 := lit_of hσ (v := (o.tgt b).S) (b := false)
      (by simp only [List.mem_append, List.mem_map]; left; exact ⟨_, ⟨o, ho, rfl⟩, rfl⟩)
    rw [ht] at h3
    have h4 := lit_of hσ (v := r.i) (b := b) (by simp)
    cases hu : σ o.u.S
    · simp [hu]
    · simp [holds_trClause.1 hc hu h4] at h3
  · refine RupOk.id_conflict hx.lay.alo (nodup_vars_normalize _) fun σ hσ hc => ?_
    rw [holds_normalize, aloClause, holds_clause] at hc
    obtain ⟨l, hl, hev⟩ := hc
    rcases List.mem_append.1 hl with hl | hl
    · have := I.eval_negD (fun m hm => hσ m (by simp [hm])) l hl
      simp [this] at hev
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hl
      rw [← hx.outs] at hu
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hu
      have := lit_of hσ (v := o.u.S) (b := false)
        (by simp only [List.mem_append, List.mem_map]; left; exact ⟨_, ⟨o, ho, rfl⟩, rfl⟩)
      simp [this] at hev

private theorem remLayer_spec {next : List Node} {r : LayerRec} {A : List St}
    {dl : List (ℕ × ℕ)} : ∀ (bs : List Bool) (e : Acc) (db : List (ℕ × PBConstr)),
    I.Run e db → I.BackAt db e.var next (r, A, dl) → (∀ b ∈ bs, b ∈ vals (I.dom r.i)) →
    ∃ db', I.Run (I.remLayer r A dl e bs).1 db' ∧ Sub db db' ∧
      (∀ y ∈ (I.remLayer r A dl e bs).2, y.1 = r.i ∧ y.2.1 ∈ bs ∧
        lookup db' y.2.2 = some (I.remClause r.i y.2.1).normalize) ∧
      (∀ b ∈ bs, (r.outs.all fun o => I.succSt r.i o.u.st b ∉ A) = true →
        ∃ k, (r.i, b, k) ∈ (I.remLayer r A dl e bs).2) ∧
      (I.remLayer r A dl e bs).1.var = e.var
  | [], e, db, h, _, _ => ⟨db, h, Sub.refl _, by simp [remLayer], by simp, rfl⟩
  | b :: bs, e, db, h, hx, hbs => by
    have hlt : r.i < I.n := hx.lt
    by_cases hall : (r.outs.all fun o => I.succSt r.i o.u.st b ∉ A) = true
    · have hr := I.rup_rem hx (hbs b List.mem_cons_self) (by simpa using hall)
      obtain ⟨h₁, s₁⟩ := Run.rup I h hr (fun v hv => by
        obtain ⟨l, hl, rfl⟩ := vars_clause hv
        rcases List.mem_append.1 hl with hl | hl
        · have := I.vars_negD hl; have := h.2.2.2.1; omega
        · simp only [List.mem_singleton] at hl; subst hl
          have := h.2.2.2.1; simp; omega)
      obtain ⟨db', h', s', hys, hcov, hv⟩ := remLayer_spec bs _ _ h₁
        ⟨hx.lt, hx.lay.mono I s₁ (by simp [Acc.push]), hx.outs,
          fun o ho => (hx.out o ho).mono I s₁ (by simp [Acc.push]), hx.alive, hx.dead.mono I s₁,
          hx.cover⟩ (fun b hb => hbs b (List.mem_cons_of_mem _ hb))
      simp only [remLayer, hall, ↓reduceIte]
      refine ⟨db', h', s₁.trans s', ?_, ?_, by simpa [Acc.push] using hv⟩
      · simp only [List.mem_cons, forall_eq_or_imp]
        refine ⟨⟨by simp, by simp, s' _ _ (lookup_cons_self _ _ _)⟩, fun y hy => ?_⟩
        obtain ⟨h1, h2, h3⟩ := hys y hy
        exact ⟨h1, .inr h2, h3⟩
      · simp only [List.mem_cons]
        rintro b' (rfl | hb') hb''
        · exact ⟨_, .inl rfl⟩
        · obtain ⟨k, hk⟩ := hcov b' hb' hb''
          exact ⟨k, .inr hk⟩
    · obtain ⟨db', h', s', hys, hcov, hv⟩ := remLayer_spec bs e db h hx
        (fun b hb => hbs b (List.mem_cons_of_mem _ hb))
      simp only [remLayer, hall, Bool.false_eq_true, ↓reduceIte]
      refine ⟨db', h', s', ?_, ?_, hv⟩
      · intro y hy
        obtain ⟨h1, h2, h3⟩ := hys y hy
        exact ⟨h1, List.mem_cons_of_mem _ h2, h3⟩
      · simp only [List.mem_cons]
        rintro b' (rfl | hb') hb''
        · exact absurd hb'' hall
        · exact hcov b' hb' hb''

private theorem remAll_spec : ∀ (xs : List (LayerRec × List St × List (ℕ × ℕ))) (e : Acc)
    (db : List (ℕ × PBConstr)), I.Run e db → (∀ x ∈ xs, ∃ next, I.BackAt db e.var next x) →
    ∃ db', I.Run (I.remAll e xs).1 db' ∧ Sub db db' ∧
      (∀ y ∈ (I.remAll e xs).2, y.2.1 ∈ vals (I.dom y.1) ∧ y.1 < I.n ∧
        lookup db' y.2.2 = some (I.remClause y.1 y.2.1).normalize) ∧
      (∀ x ∈ xs, ∀ b ∈ vals (I.dom x.1.i),
        (x.1.outs.all fun o => I.succSt x.1.i o.u.st b ∉ x.2.1) = true →
        ∃ k, (x.1.i, b, k) ∈ (I.remAll e xs).2)
  | [], e, db, h, _ => ⟨db, h, Sub.refl _, by simp [remAll], by simp⟩
  | x :: xs, e, db, h, hxs => by
    obtain ⟨nx, hx⟩ := hxs x List.mem_cons_self
    obtain ⟨db₁, h₁, s₁, hys₁, hcov₁, hv₁⟩ := I.remLayer_spec (r := x.1) (A := x.2.1)
      (dl := x.2.2) (vals (I.dom x.1.i)) e db h hx (fun b hb => hb)
    obtain ⟨db', h', s', hys, hcov⟩ := remAll_spec xs _ db₁ h₁ (fun y hy => by
      obtain ⟨n', hn'⟩ := hxs y (List.mem_cons_of_mem _ hy)
      rw [hv₁]
      exact ⟨n', ⟨hn'.lt, hn'.lay.mono I s₁ le_rfl, hn'.outs,
        fun o ho => (hn'.out o ho).mono I s₁ le_rfl, hn'.alive, hn'.dead.mono I s₁,
        hn'.cover⟩⟩)
    refine ⟨db', h', s₁.trans s', ?_, ?_⟩
    · simp only [remAll, List.mem_append]
      rintro y (hy | hy)
      · obtain ⟨h1, h2, h3⟩ := hys₁ y hy
        exact ⟨h1 ▸ h2, h1 ▸ hx.lt, h1 ▸ s' _ _ h3⟩
      · exact hys y hy
    · simp only [remAll, List.mem_cons, List.mem_append]
      rintro y (rfl | hy) b hb hall
      · obtain ⟨k, hk⟩ := hcov₁ b hb hall
        exact ⟨k, .inl hk⟩
      · obtain ⟨k, hk⟩ := hcov y hy b hb hall
        exact ⟨k, .inr hk⟩

/-! ### The whole proof -/

/-- **The whole proof runs**, and derives the removal clause of every removed value; every value
of a free domain all of whose transitions out of layer `j` lead to states without a feasible
completion is removed. -/
private theorem emit_spec : ∃ db, I.Run I.emit.1 db ∧
    (∀ y ∈ I.emit.2, y.2.1 ∈ vals (I.dom y.1) ∧ y.1 < I.n ∧
      lookup db y.2.2 = some (I.remClause y.1 y.2.1).normalize) ∧
    (∀ j < I.n, ∀ b ∈ vals (I.dom j), (∀ st ∈ I.lay j, I.succSt j st b ∉ I.alive (j + 1)) →
      ∃ k, (j, b, k) ∈ I.emit.2) := by
  -- Layer `0` and its at-least-one constraint.
  obtain ⟨db₀, h₀, s₀, hmap₀, hok₀, hv₀⟩ := I.mkLayer_spec (i := 0) (Nat.zero_le _) (I.lay 0)
    ⟨[], 3, I.n⟩ _ I.run_init (fun st hst => hst)
  set r₀ := I.mkLayer 0 ⟨[], 3, I.n⟩ (I.lay 0) with hr₀
  obtain ⟨u₀, hu₀⟩ : ∃ u₀, r₀.2 = [u₀] := by
    rcases h : r₀.2 with _ | ⟨u, _ | _⟩ <;> rw [h] at hmap₀ <;> simp [lay] at hmap₀ ⊢
  have hst₀ : u₀.st = (0, 0) := by rw [hu₀] at hmap₀; simpa [lay] using hmap₀
  have hn₀ := hok₀ u₀ (by rw [hu₀]; simp)
  have hrup : rup db₀ (I.aloClause r₀.2) [.neg, .id (r₀.2.headD noNode).wb,
      .id (r₀.2.headD noNode).pb, .id (r₀.2.headD noNode).sb] = true := by
    rw [hu₀]
    refine rup_clause ?_
    rw [negate_aloClause]
    simp only [List.headD_cons, List.map_cons, List.map_nil]
    refine RupOk.id_imp (L := [(u₀.W, true)]) hn₀.wb (nodup_vars_normalize _) ?_ ?_
    · intro σ _ hc
      rw [holds_normalize, holds_impl_neg_negate] at hc
      simp [Consistent, hc (by rw [cW, holds_dimC, hst₀]; exact Nat.zero_le _)]
    refine RupOk.id_imp (L := [(u₀.P, true)]) hn₀.pb (nodup_vars_normalize _) ?_ ?_
    · intro σ _ hc
      rw [holds_normalize, holds_impl_neg_negate] at hc
      have : (I.cP 0 u₀.st).Holds σ := by
        rw [cP, holds_dimC, hst₀]; exact Nat.zero_le _
      simp [Consistent, hc this]
    refine RupOk.id_conflict hn₀.sb (nodup_vars_normalize _) fun σ hσ hc => ?_
    rw [holds_normalize, holds_impl_neg_negate] at hc
    have h1 := hc ((holds_cS σ _ _).2 ⟨lit_of hσ (by simp), lit_of hσ (by simp)⟩)
    have h2 := lit_of hσ (v := u₀.S) (b := false) (by simp)
    simp [h1] at h2
  obtain ⟨h₁, s₁⟩ := Run.rup I h₀ hrup (fun v hv => by
    obtain ⟨l, hl, rfl⟩ := vars_clause hv
    rcases List.mem_append.1 hl with hl | hl
    · have := I.vars_negD hl; have := h₀.2.2.2.1; omega
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hl; exact (hok₀ t ht).S)
  -- The forward pass.
  obtain ⟨db₂, h₂, s₂, rn, rs, hf, hrn, hc, hidx⟩ := I.fwd_spec I.n 0 _ r₀.2 r₀.1.next [] _
    (by omega) h₁ ⟨rfl, hmap₀, fun u hu => (hok₀ u hu).mono I s₁ (by simp [Acc.push]),
      lookup_cons_self _ _ _⟩ trivial rfl
  set f := I.fwd I.n 0 (r₀.1.push [.step (.rup (I.aloClause r₀.2) [.neg,
    .id (r₀.2.headD noNode).wb, .id (r₀.2.headD noNode).pb, .id (r₀.2.headD noNode).sb])] 1 0)
    r₀.2 r₀.1.next [] with hfdef
  -- The backward pass.
  obtain ⟨db₃, h₃, s₃, hd₃, hall₃, hv₃⟩ := I.deadFinal_spec rn.nodes f.1 db₂ h₂ hrn.nodes
  have hA : (rn.nodes.map (·.st)).filter I.finalOk = I.alive I.n := by rw [alive_n, hrn.lay]
  obtain ⟨db₄, h₄, s₄, hall₄, hmap₄, hv₄⟩ := I.backAll_spec rs (I.deadFinal f.1 rn.nodes).1
    ((rn.nodes.map (·.st)).filter I.finalOk) (I.deadFinal f.1 rn.nodes).2 I.n rn.nodes db₃ h₃
    (by rw [hv₃]; exact hc.mono I s₃ le_rfl) le_rfl hA hd₃ (fun t ht hn => hall₃ t ht (by
      have : t.st ∈ rn.nodes.map (·.st) := List.mem_map_of_mem ht
      simpa [List.mem_filter, this] using hn))
  -- The removals.
  obtain ⟨db₅, h₅, -, hys, hcov⟩ := I.remAll_spec _ _ db₄ h₄ (fun x hx => by
    rw [hv₄]; exact hall₄ x hx)
  have he : I.emit = I.remAll (I.backAll (I.deadFinal f.1 rn.nodes).1
      ((rn.nodes.map (·.st)).filter I.finalOk) (I.deadFinal f.1 rn.nodes).2 rs).1
      (I.backAll (I.deadFinal f.1 rn.nodes).1
      ((rn.nodes.map (·.st)).filter I.finalOk) (I.deadFinal f.1 rn.nodes).2 rs).2 := by
    simp only [emit]
    rw [← hr₀, ← hfdef, hf]
    rfl
  rw [he]
  refine ⟨db₅, h₅, hys, fun j hj b hb hall => ?_⟩
  have hjr : j ∈ rs.map (·.i) := by rw [hidx]; simpa using hj
  rw [← hmap₄, List.map_map] at hjr
  obtain ⟨x, hx, hxj⟩ := List.mem_map.1 hjr
  simp only [Function.comp_apply] at hxj
  obtain ⟨nx, hnx⟩ := hall₄ x hx
  obtain ⟨k, hk⟩ := hcov x hx b (hxj ▸ hb) (by
    simp only [List.all_eq_true, decide_eq_true_eq]
    intro o ho
    have hu : o.u ∈ x.1.nodes := by rw [← hnx.outs]; exact List.mem_map_of_mem ho
    have hst : o.u.st ∈ I.lay x.1.i := by
      rw [← hnx.lay.lay]; exact List.mem_map_of_mem hu
    rw [hnx.alive, hxj]
    exact hall _ (hxj ▸ hst))
  exact ⟨k, hxj ▸ hk⟩

/-- **The checker accepts the propagator's proof**, on every instance. -/
private theorem checkRed_run : checkRed I.F none I.run.proof (some I.pres) = true := by
  obtain ⟨db, h, -⟩ := I.emit_spec
  simp [checkRed, run, h.1, checkConclusion]

/-- A constraint of the database over item variables holds at every solution of the formula: the
witnesses of `red` change only extension variables, which the preserved set excludes. -/
private theorem holds_of_run {e : Acc} {db : List (ℕ × PBConstr)} (h : I.Run e db) {k : ℕ}
    {c : PBConstr} (hk : lookup db k = some c) (hv : ∀ x ∈ c.vars, x < I.n) {σ : ℕ → Bool}
    (hσ : ∀ c ∈ I.F, c.Holds σ) : c.Holds σ := by
  obtain ⟨-, he⟩ := invariants_of_runTop h.1
  obtain ⟨g, -, hmaps, hid⟩ := he.fwd 0 (.inr rfl)
  have hmem : proj I.pres σ ∈ proj ((some I.pres).getD []) '' solsLE I.F none 0 :=
    ⟨σ, ⟨hσ, by simp [objValue]⟩, rfl⟩
  rcases hmaps hmem with ⟨_, ⟨τ, ⟨hτ, -⟩, rfl⟩, hτσ⟩ | ⟨m, ⟨hm, -⟩, -⟩
  · have heq := hid rfl _ hmem _ hτσ.symm
    simp only [state, State.init, Option.getD_some] at heq
    refine (holds_congr fun t ht => ?_).2 (hτ.lookup hk)
    have hx : termVar t ∈ I.pres := by
      simpa [pres] using hv _ (List.mem_map_of_mem ht)
    have := congrArg (fun l => l[(I.pres.idxOf (termVar t))]?) heq
    simp only [proj, List.getElem?_map, List.getElem?_idxOf hx, Option.map_some,
      Option.some.injEq] at this
    exact this.symm
  · simp [state, State.init] at hm

/-! ### The dynamic program is exact -/

/-- The state of the assignment `σ` after the first `i` items. -/
private def stOf (σ : ℕ → Bool) (i : ℕ) : St := (part σ I.w true i, part σ I.p false i)

/-- `∑_{i ≤ j < m} aⱼ [σ j = pol]`. -/
private def sfx (σ : ℕ → Bool) (a : ℕ → ℕ) (pol : Bool) (i m : ℕ) : ℕ :=
  ((List.range' i (m - i)).map fun j => bit (σ j) pol (a j)).sum

/-- The last state reached from the state `st` of layer `i` along `σ`. -/
private def finOf (σ : ℕ → Bool) (i : ℕ) (st : St) : St :=
  (st.1 + sfx σ I.w true i I.n, st.2 + sfx σ I.p false i I.n)

/-- `σ` takes values in the domains of the items `i ≤ j < m`. -/
private def Allowed (σ : ℕ → Bool) (i m : ℕ) : Prop := ∀ j, i ≤ j → j < m → σ j ∈ vals (I.dom j)

private theorem part_congr {σ τ : ℕ → Bool} {i : ℕ} (h : ∀ j < i, σ j = τ j) (a : ℕ → ℕ)
    (pol : Bool) : part σ a pol i = part τ a pol i := by
  simp only [part]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  rw [h j (List.mem_range.1 hj)]

private theorem sfx_congr {σ τ : ℕ → Bool} {i m : ℕ} (h : ∀ j, i ≤ j → j < m → σ j = τ j)
    (a : ℕ → ℕ) (pol : Bool) : sfx σ a pol i m = sfx τ a pol i m := by
  simp only [sfx]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  rw [List.mem_range'_1] at hj
  rw [h j hj.1 (by omega)]

private theorem sfx_cons {σ : ℕ → Bool} {a : ℕ → ℕ} {pol : Bool} {i m : ℕ} (h : i < m) :
    sfx σ a pol i m = bit (σ i) pol (a i) + sfx σ a pol (i + 1) m := by
  simp only [sfx]
  rw [show m - i = (m - (i + 1)) + 1 by omega, List.range'_succ]
  simp

private theorem sfx_snoc (σ : ℕ → Bool) (a : ℕ → ℕ) (pol : Bool) {i m : ℕ} (h : i ≤ m) :
    sfx σ a pol i (m + 1) = sfx σ a pol i m + bit (σ m) pol (a m) := by
  simp only [sfx]
  rw [show m + 1 - i = (m - i) + 1 by omega, List.range'_concat]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero, Nat.one_mul]
  rw [show i + (m - i) = m by omega]

private theorem part_eq_add_sfx (σ : ℕ → Bool) (a : ℕ → ℕ) (pol : Bool) {i m : ℕ} (h : i ≤ m) :
    part σ a pol m = part σ a pol i + sfx σ a pol i m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => simp [sfx]
  | succ k ih =>
    rw [← Nat.add_assoc, part_succ, ih (by omega), sfx_snoc σ a pol (by omega)]
    omega

private theorem stOf_succ (σ : ℕ → Bool) (i : ℕ) :
    I.stOf σ (i + 1) = I.succSt i (I.stOf σ i) (σ i) := by
  simp [stOf, succSt, part_succ]

private theorem stOf_eq_finOf (σ : ℕ → Bool) {i : ℕ} (h : i ≤ I.n) :
    I.stOf σ I.n = I.finOf σ i (I.stOf σ i) := by
  simp [stOf, finOf, part_eq_add_sfx σ _ _ h]

private theorem finOf_succ (σ : ℕ → Bool) {i : ℕ} (h : i < I.n) (st : St) :
    I.finOf σ i st = I.finOf σ (i + 1) (I.succSt i st (σ i)) := by
  simp only [finOf, succSt, sfx_cons h]
  ext <;> simp <;> omega

/-- **The layers are the reachable states**: the states of the assignments allowed by the
domains on the first `i` items. -/
private theorem mem_lay_iff : ∀ {i : ℕ} {st : St},
    st ∈ I.lay i ↔ ∃ σ, I.Allowed σ 0 i ∧ I.stOf σ i = st
  | 0, st => by
    simp only [lay, List.mem_singleton]
    exact ⟨fun h => ⟨fun _ => false, fun j _ hj => absurd hj (Nat.not_lt_zero _),
      by simp [h, stOf, part]⟩, fun ⟨σ, _, h⟩ => by rw [← h]; simp [stOf, part]⟩
  | i + 1, st => by
    simp only [lay, nextLay, List.mem_dedup, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨st₀, h₀, b, hb, rfl⟩
      obtain ⟨σ, hσ, rfl⟩ := (mem_lay_iff (i := i)).1 h₀
      refine ⟨Function.update σ i b, fun j _ hj => ?_, ?_⟩
      · by_cases hji : j = i
        · subst hji; simpa using hb
        · rw [Function.update_of_ne hji]; exact hσ j (Nat.zero_le _) (by omega)
      · rw [stOf_succ, Function.update_self]
        congr 1
        simp only [stOf]
        rw [part_congr (σ := Function.update σ i b) (τ := σ) (fun (j : ℕ) (hj : j < i) =>
            Function.update_of_ne (Nat.ne_of_lt hj) _ _),
          part_congr (σ := Function.update σ i b) (τ := σ) (fun (j : ℕ) (hj : j < i) =>
            Function.update_of_ne (Nat.ne_of_lt hj) _ _)]
    · rintro ⟨σ, hσ, rfl⟩
      exact ⟨I.stOf σ i, (mem_lay_iff (i := i)).2 ⟨σ, fun (j : ℕ) h0 (hj : j < i) =>
        hσ j h0 (Nat.lt_succ_of_lt hj), rfl⟩,
        σ i, hσ i (Nat.zero_le _) (Nat.lt_succ_self i), (stOf_succ I σ i).symm⟩

/-- **The alive states are those with a feasible completion.** -/
private theorem mem_alive_iff : ∀ (k : ℕ) {i : ℕ} (_ : i + k = I.n) {st : St},
    st ∈ I.alive i ↔ st ∈ I.lay i ∧ ∃ σ, I.Allowed σ i I.n ∧ I.finalOk (I.finOf σ i st) = true
  | 0, i, hk, st => by
    simp only [Nat.add_zero] at hk
    subst hk
    rw [alive_n, List.mem_filter]
    have hf : ∀ σ : ℕ → Bool, I.finOf σ I.n st = st := fun σ => by simp [finOf, sfx]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun _ => false, fun (j : ℕ) (h1 : I.n ≤ j) (h2 : j < I.n) =>
        absurd h2 (Nat.not_lt.2 h1), by rw [hf]; exact h2⟩
    · rintro ⟨h1, σ, -, h2⟩
      exact ⟨h1, by rw [hf] at h2; exact h2⟩
  | k + 1, i, hk, st => by
    have hi : i < I.n := by omega
    rw [I.alive_lt hi, List.mem_filter]
    simp only [List.any_eq_true, decide_eq_true_eq]
    refine and_congr_right fun hst => ⟨?_, ?_⟩
    · rintro ⟨b, hb, hA⟩
      obtain ⟨-, σ, hσ, hfin⟩ := (mem_alive_iff k (i := i + 1) (by omega)).1 hA
      refine ⟨Function.update σ i b, fun j hij hj => ?_, ?_⟩
      · by_cases hji : j = i
        · subst hji; simpa using hb
        · rw [Function.update_of_ne hji]; exact hσ j (by omega) hj
      · rw [finOf_succ I _ hi, Function.update_self]
        rw [← hfin]
        simp only [finOf]
        rw [sfx_congr (σ := Function.update σ i b) (τ := σ) (fun (j : ℕ) (hj : i + 1 ≤ j) _ =>
            Function.update_of_ne (Nat.ne_of_gt hj) _ _),
          sfx_congr (σ := Function.update σ i b) (τ := σ) (fun (j : ℕ) (hj : i + 1 ≤ j) _ =>
            Function.update_of_ne (Nat.ne_of_gt hj) _ _)]
    · rintro ⟨σ, hσ, hfin⟩
      refine ⟨σ i, hσ i le_rfl hi, (mem_alive_iff k (i := i + 1) (by omega)).2
        ⟨I.mem_nextLay hst (hσ i le_rfl hi), σ, fun j hj h' => hσ j (by omega) h', ?_⟩⟩
      rw [← finOf_succ I _ hi]; exact hfin

/-- The value `b` of item `j` is **supported**: some assignment allowed by the domains, with
`xⱼ = b`, satisfies the knapsack constraint. -/
private def SupportedN (j : ℕ) (b : Bool) : Prop :=
  ∃ σ, I.Allowed σ 0 I.n ∧ σ j = b ∧ I.finalOk (I.stOf σ I.n) = true

/-- **Completeness of the dynamic program**: if no transition by `b` out of layer `j` reaches an
alive state, the value is unsupported, and conversely. -/
private theorem forall_not_alive_iff {j : ℕ} (hj : j < I.n) {b : Bool}
    (hb : b ∈ vals (I.dom j)) :
    (∀ st ∈ I.lay j, I.succSt j st b ∉ I.alive (j + 1)) ↔ ¬ I.SupportedN j b := by
  constructor
  · rintro hall ⟨σ, hσ, hσj, hfin⟩
    refine hall (I.stOf σ j) ((I.mem_lay_iff).2 ⟨σ, fun x h0 hx => hσ x h0 (by omega), rfl⟩) ?_
    rw [I.mem_alive_iff (I.n - (j + 1)) (by omega)]
    refine ⟨I.mem_nextLay ((I.mem_lay_iff).2 ⟨σ, fun x h0 hx => hσ x h0 (by omega), rfl⟩) hb,
      σ, fun x h1 h2 => hσ x (Nat.zero_le _) h2, ?_⟩
    rw [← hσj, ← finOf_succ I _ hj, ← stOf_eq_finOf I σ hj.le]
    exact hfin
  · rintro hns st hst hA
    obtain ⟨σ₁, hσ₁, rfl⟩ := (I.mem_lay_iff).1 hst
    obtain ⟨-, σ₂, hσ₂, hfin⟩ := (I.mem_alive_iff (I.n - (j + 1)) (by omega)).1 hA
    let σ : ℕ → Bool := fun x => if x < j then σ₁ x else if x = j then b else σ₂ x
    have h1 : ∀ x < j, σ x = σ₁ x := fun x hx => by simp [σ, hx]
    have h2 : ∀ x, j + 1 ≤ x → x < I.n → σ x = σ₂ x := fun x hx _ => by
      simp [σ, show ¬ x < j by omega, show x ≠ j by omega]
    have hσj : σ j = b := by simp [σ]
    refine hns ⟨σ, fun x _ hx => ?_, hσj, ?_⟩
    · by_cases h : x < j
      · rw [h1 x h]; exact hσ₁ x (Nat.zero_le _) h
      · by_cases h' : x = j
        · subst h'; rw [hσj]; exact hb
        · rw [h2 x (by omega) hx]; exact hσ₂ x (by omega) hx
    · rw [stOf_eq_finOf I σ hj.le, finOf_succ I _ hj, hσj]
      have hst : I.stOf σ j = I.stOf σ₁ j := by
        simp only [stOf]; rw [part_congr h1, part_congr h1]
      rw [hst, ← hfin]
      simp only [finOf]
      rw [sfx_congr h2, sfx_congr h2]

/-! ### The removals are exactly the unsupported values -/

private theorem consistent_fixedLits_of_allowed {σ : ℕ → Bool} (h : I.Allowed σ 0 I.n) :
    Consistent σ I.fixedLits := by
  rintro ⟨j, b⟩ hl
  obtain ⟨hj, hd⟩ := (I.mem_fixedLits).1 hl
  have := h j (Nat.zero_le _) hj
  simp only [hd, vals, List.mem_singleton] at this
  simp [this]

private theorem holds_F_of_finalOk {σ : ℕ → Bool} (h : I.finalOk (I.stOf σ I.n) = true) :
    ∀ c ∈ I.F, c.Holds σ := by
  simp only [finalOk, stOf, Bool.and_eq_true] at h
  obtain ⟨ha, hb⟩ := h
  have ha := of_decide_eq_true ha
  have hb := of_decide_eq_true hb
  have h1 := part_add_part σ I.w true I.n
  have h2 := part_add_part σ I.p false I.n
  simp only [Bool.not_true, Bool.not_false] at h1 h2
  simp only [F, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨?_, ?_⟩
  · simp only [capC, Holds, lhs_range]; omega
  · simp only [profC, Holds, lhs_range]; omega

/-- **The removed values are exactly the unsupported values of the domains.** The direction
"removed ⇒ unsupported" holds because the checker accepts the proof, which derives
`D ⇒ xⱼ ≠ b`; the converse is the exactness of the dynamic program. -/
private theorem mem_run_removed_iff {j : ℕ} {b : Bool} :
    (j, b) ∈ I.run.removed ↔ j < I.n ∧ b ∈ vals (I.dom j) ∧ ¬ I.SupportedN j b := by
  obtain ⟨db, h, hys, hcov⟩ := I.emit_spec
  constructor
  · intro hm
    simp only [run, List.mem_map, Prod.mk.injEq] at hm
    obtain ⟨y, hy, rfl, rfl⟩ := hm
    obtain ⟨hb, hj, hl⟩ := hys y hy
    refine ⟨hj, hb, fun ⟨σ, hσ, hσj, hfin⟩ => ?_⟩
    have hc := I.holds_of_run h hl (fun x hx => by
      obtain ⟨l, hl, rfl⟩ := vars_clause (mem_vars_of_mem_vars_normalize hx)
      rcases List.mem_append.1 hl with hl | hl
      · exact I.vars_negD hl
      · simp only [List.mem_singleton] at hl; subst hl; exact hj) (I.holds_F_of_finalOk hfin)
    rw [holds_normalize, remClause, holds_clause] at hc
    obtain ⟨l, hl, hev⟩ := hc
    rcases List.mem_append.1 hl with hl | hl
    · simp [I.eval_negD (I.consistent_fixedLits_of_allowed hσ) l hl] at hev
    · simp only [List.mem_singleton] at hl; subst hl; simp [hσj] at hev
  · rintro ⟨hj, hb, hns⟩
    obtain ⟨k, hk⟩ := hcov j hj b hb ((I.forall_not_alive_iff hj hb).2 hns)
    exact List.mem_map.2 ⟨_, hk, rfl⟩

end Inst

/-! ### The propagator on `Fin n` -/

variable {n : ℕ}

/-- **The profit constraint** `∑ pᵢ xᵢ ≥ P`, with item `i` the variable `i`. -/
def profitBound (p : Fin n → ℕ) (P : ℕ) : PBConstr :=
  ⟨(List.finRange n).map fun i => (p i, (i.val, true)), P⟩

/-- **The knapsack constraint** `∑ wᵢ xᵢ ≤ C ∧ ∑ pᵢ xᵢ ≥ P`: the capacity constraint of the
certified knapsack and the profit constraint. -/
def propFormula (w p : Fin n → ℕ) (C P : ℕ) : List PBConstr :=
  [capacity w C, profitBound p P]

/-- The ℕ-indexed instance of a knapsack constraint with domains, items outside `Fin n` absent. -/
private def Inst.ofFin (w p : Fin n → ℕ) (C P : ℕ) (dom : Fin n → Option Bool) : Inst :=
  ⟨n, fun j => if h : j < n then w ⟨j, h⟩ else 0, fun j => if h : j < n then p ⟨j, h⟩ else 0, C,
    P, fun j => if h : j < n then dom ⟨j, h⟩ else none⟩

/-- **The knapsack propagator**: for the items of weights `w` and profits `p`, the capacity `C`,
the profit bound `P` and the domains `dom` (`none` for a free item, `some b` for an item fixed to
`b`), the values removed and a kernel proof deriving `D ⇒ xᵢ ≠ b` for each removed value `b` of
item `i`, `D` the domain literals. -/
def propagate (w p : Fin n → ℕ) (C P : ℕ) (dom : Fin n → Option Bool) : Propagation :=
  (Inst.ofFin w p C P dom).run

/-- The value `b` of item `j` is **supported** by the knapsack constraint under the domains:
some set of items that agrees with the domains, contains `j` exactly when `b`, weighs at most `C`
and earns at least `P`. -/
def Supported (w p : Fin n → ℕ) (C P : ℕ) (dom : Fin n → Option Bool) (j : Fin n) (b : Bool) :
    Prop :=
  ∃ S : Finset (Fin n), (∀ i c, dom i = some c → (i ∈ S ↔ c = true)) ∧ (j ∈ S ↔ b = true) ∧
    ∑ i ∈ S, w i ≤ C ∧ P ≤ ∑ i ∈ S, p i

/-- **The profit constraint holds exactly when the items taken earn at least `P`.** -/
theorem holds_profitBound_iff (p : Fin n → ℕ) (P : ℕ) (σ : ℕ → Bool) :
    (profitBound p P).Holds σ ↔ P ≤ ∑ i ∈ chosen n σ, p i := by
  rw [Holds, profitBound, lhs, List.map_map, ← Fin.sum_univ_def, chosen, Finset.sum_filter]
  refine iff_of_eq (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
  cases h : σ i.val <;> simp [termVal, h]

private theorem map_finRange {α : Type*} (g : ℕ → α) :
    (List.finRange n).map (fun i => g i.val) = (List.range n).map g := by
  rw [← List.map_coe_finRange_eq_range, List.map_map]; rfl

private theorem F_ofFin (w p : Fin n → ℕ) (C P : ℕ) (dom : Fin n → Option Bool) :
    (Inst.ofFin w p C P dom).F = propFormula w p C P := by
  have h1 : (List.finRange n).map (fun i => (w i, (i.val, false))) =
      (List.range n).map fun j => ((Inst.ofFin w p C P dom).w j, (j, false)) := by
    rw [← map_finRange]; exact List.map_congr_left fun i _ => by simp [Inst.ofFin]
  have h2 : (List.finRange n).map (fun i => (p i, (i.val, true))) =
      (List.range n).map fun j => ((Inst.ofFin w p C P dom).p j, (j, true)) := by
    rw [← map_finRange]; exact List.map_congr_left fun i _ => by simp [Inst.ofFin]
  have h3 : (List.finRange n).map w = (List.range n).map (Inst.ofFin w p C P dom).w := by
    rw [← map_finRange]; exact List.map_congr_left fun i _ => by simp [Inst.ofFin]
  simp only [Inst.F, propFormula, Inst.capC, Inst.profC, capacity, profitBound, Inst.tot, h1, h2,
    h3]
  rfl

/-- **The checker accepts the propagator's proof**, for every knapsack constraint and every
domains, the item variables preserved. -/
theorem checkRed_propagate (w p : Fin n → ℕ) (C P : ℕ) (dom : Fin n → Option Bool) :
    checkRed (propFormula w p C P) none (propagate w p C P dom).proof (some (List.range n)) =
      true := by
  have := (Inst.ofFin w p C P dom).checkRed_run
  rwa [F_ofFin] at this

private theorem part_eq_sum (σ : ℕ → Bool) (a : Fin n → ℕ) :
    Inst.part σ (fun j => if h : j < n then a ⟨j, h⟩ else 0) true n = ∑ i ∈ chosen n σ, a i := by
  rw [chosen, Finset.sum_filter, Inst.part, ← map_finRange
    (fun j => Inst.bit (σ j) true (if h : j < n then a ⟨j, h⟩ else 0)), ← Fin.sum_univ_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases σ i.val <;> simp [Inst.bit]

private theorem tot_eq_sum (a : Fin n → ℕ) :
    Inst.tot (fun j => if h : j < n then a ⟨j, h⟩ else 0) n = ∑ i, a i := by
  rw [Inst.tot, ← map_finRange (fun j => if h : j < n then a ⟨j, h⟩ else 0), ← Fin.sum_univ_def]
  exact Finset.sum_congr rfl fun i _ => by simp [i.isLt]

private theorem supportedN_iff (w p : Fin n → ℕ) (C P : ℕ) (dom : Fin n → Option Bool)
    (j : Fin n) (b : Bool) :
    (Inst.ofFin w p C P dom).SupportedN j.val b ↔ Supported w p C P dom j b := by
  have key : ∀ σ : ℕ → Bool, (Inst.ofFin w p C P dom).finalOk
      ((Inst.ofFin w p C P dom).stOf σ (Inst.ofFin w p C P dom).n) = true ↔
      ∑ i ∈ chosen n σ, w i ≤ C ∧ P ≤ ∑ i ∈ chosen n σ, p i := by
    intro σ
    have hw' := part_eq_sum σ w
    have hp' := part_eq_sum σ p
    have ht := tot_eq_sum p
    have h2 := Inst.part_add_part σ (Inst.ofFin w p C P dom).p true n
    simp only [Inst.ofFin, Bool.not_true] at h2
    simp only [Inst.finalOk, Inst.stOf, Inst.ofFin, Bool.and_eq_true]
    constructor
    · rintro ⟨ha, hb⟩
      have := of_decide_eq_true ha
      have := of_decide_eq_true hb
      omega
    · rintro ⟨ha, hb⟩
      exact ⟨decide_eq_true (by omega), decide_eq_true (by omega)⟩
  have hallow : ∀ σ : ℕ → Bool, (Inst.ofFin w p C P dom).Allowed σ 0 n ↔
      ∀ i c, dom i = some c → (i ∈ chosen n σ ↔ c = true) := by
    intro σ
    constructor
    · intro h i c hc
      have := h i.val (Nat.zero_le _) i.isLt
      simp only [Inst.ofFin, i.isLt, ↓reduceDIte, Fin.eta, hc, Inst.vals,
        List.mem_singleton] at this
      simp [this]
    · intro h k _ hk
      cases hc : dom ⟨k, hk⟩ with
      | none => simp [Inst.ofFin, hk, hc, Inst.vals]
      | some c =>
        have := h _ c hc
        simp only [mem_chosen] at this
        simp only [Inst.ofFin, hk, ↓reduceDIte, hc, Inst.vals, List.mem_singleton]
        cases c <;> simp_all
  constructor
  · rintro ⟨σ, hσ, hσj, hfin⟩
    refine ⟨chosen n σ, (hallow σ).1 hσ, by simp [hσj], (key σ).1 hfin⟩
  · rintro ⟨S, hS, hj, hfin⟩
    obtain ⟨σ, rfl⟩ := exists_chosen_eq S
    refine ⟨σ, (hallow σ).2 hS, ?_, (key σ).2 hfin⟩
    simp only [mem_chosen] at hj
    cases b <;> cases h : σ j.val <;> simp_all

/-- **The propagator removes exactly the unsupported values**: the value `b` of item `j` is
removed exactly when it is in the domain of `j` and no set of items agreeing with the domains,
with `j` taken exactly when `b`, satisfies the knapsack constraint. -/
theorem mem_removed_iff (w p : Fin n → ℕ) (C P : ℕ) (dom : Fin n → Option Bool) (j : Fin n)
    (b : Bool) :
    (j.val, b) ∈ (propagate w p C P dom).removed ↔
      (dom j = none ∨ dom j = some b) ∧ ¬ Supported w p C P dom j b := by
  rw [propagate, Inst.mem_run_removed_iff, supportedN_iff]
  have hv : b ∈ Inst.vals ((Inst.ofFin w p C P dom).dom j.val) ↔ dom j = none ∨ dom j = some b := by
    simp only [Inst.ofFin, j.isLt, ↓reduceDIte]
    cases dom j <;> cases b <;> simp [Inst.vals]
  rw [hv]
  simp [Inst.ofFin, j.isLt]

/-- Every removed value is of an item. -/
theorem lt_of_mem_removed {w p : Fin n → ℕ} {C P : ℕ} {dom : Fin n → Option Bool} {i : ℕ}
    {b : Bool} (h : (i, b) ∈ (propagate w p C P dom).removed) : i < n :=
  ((Inst.ofFin w p C P dom).mem_run_removed_iff.1 h).1

end Cslib.Logic.PL.VeriPB.Knapsack

end
