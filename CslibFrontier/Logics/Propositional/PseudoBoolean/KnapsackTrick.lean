/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.DynamicProgramming
-- `import all`: the emitter reuses the Boolean emitter's private `clause` and its partial sums.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackDP

/-!
# A two-equality knapsack propagator with proof logging

The *knapsack constraint with two equalities* over `n` items with integer domains asks for values
`xⱼ` of the items, `W` of the weight and `P` of the profit, each in its domain, with
`∑ wⱼ xⱼ = W` and `∑ pⱼ xⱼ = P`. §3.3 (p. 9:11) of [Demirović, McCreesh, McIlree, Nordström,
Oertel and Sidorov][DemirovicMcCreeshMcIlreeNordstromOertelSidorov2024] attributes this form to
Fahle and Sellmann, Sellmann, Katriel et al., Malitsky et al. and MiniZinc, and cites Trick for a
propagator of a single `0`–`1` inequality whose sum is a variable. This file gives a propagator
for the two-equality form in Trick's style, a decision diagram over exact states pruned backwards
from its last layer, that writes a kernel-format VeriPB proof justifying each value it removes,
after §3.3 and the framework of [Gocht, McCreesh and Nordström][GochtMcCreeshNordstrom2022]. The
names `Knapsack.Trick` refer to that propagation method. Its acceptance by the checker and its
exactness are proved in
`CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackTrickProof`.

**The encoding** (`Cslib.Logic.PL.VeriPB.Knapsack.Trick.Inst.formula`). Every variable has an
initial domain, a list of values, each with a flag telling whether it is still in the current
domain (`Cslib.Logic.PL.VeriPB.Knapsack.Trick.Dom`). Each value has its *direct* literal
`[x = v]`, a Boolean variable: those of the items first, item after item, then those of `W`, then
those of `P`. The formula says that each variable takes exactly one value of its initial domain (an
at-least-one and an at-most-one constraint), and states each linear equality as two inequalities
between the direct literals, `∑ⱼ ∑_v wⱼ v [xⱼ = v] ≥ ∑_u u [W = u]` and its converse, and
likewise for the profit. The current domains enter only through the *antecedent* `D`: the
negations `[x ≠ v]` of the values no longer in them, from which, as in Gocht, McCreesh and
Nordström's framework, the propagator derives each removal `D ⇒ [x ≠ v]`.

**The dynamic program.** Layer `i` holds the states `(w, p)` that the first `i` items reach with
values of their current domains: the weight and the profit so far. States are merged only when
equal (§3.3, difference 4). A state of the last layer is *feasible* when `w` and `p` are in the
current domains of `W` and `P`; a backward pass finds the states with a feasible completion. A
value of an item is removed when no transition by it leads to such a state, and a value of `W`
or `P` when no feasible state of the last layer has it.

**The proof** follows the paper's equations (24)–(26). Each node of layer `i`, of state `(w, p)`,
gets five extension variables, defined by `Cslib.Logic.PL.VeriPB.reify`: the four partial states
`W↑ ⇔ ∑_{j<i} wⱼ xⱼ ≥ w`, `W↓ ⇔ ∑_{j<i} wⱼ xⱼ ≤ w`, `P↑ ⇔ ∑_{j<i} pⱼ xⱼ ≥ p` and
`P↓ ⇔ ∑_{j<i} pⱼ xⱼ ≤ p`, each a constraint over direct literals, and `S ⇔ W↑ + W↓ + P↑ + P↓ ≥ 4`.
Then:
* for each node `u` and each value `v` of its item in the current domain, with successor `t`, the
  forward half of each partial state of `u` plus the backward half of that of `t` gives
  `S_u ∧ [xᵢ = v] ⇒ S_t` by RUP, the item's at-most-one constraint making its other values false
  (difference 3); then `S_u ∧ D ⇒ ⋁ S_t` by RUP from these and the item's at-least-one constraint;
* the at-least-one constraint `D ⇒ ⋁_u S_u` of each layer follows by RUP from that of the layer
  before;
* for each node `t` of the last layer and each value `u ≠ w` of `W` in its current domain,
  `S_t ⇒ [W ≠ u]`, by adding a partial state of `t` to one of the two inequalities of the weight
  and RUP; likewise for `P`;
* each infeasible state of the last layer is refuted, `D ⇒ ¬S_t`, by RUP from these and the
  at-least-one constraint of `W` or of `P`, and the backward pass refutes each earlier state
  without a feasible completion by RUP from the refutations of its targets;
* each removal of an item value follows by RUP from the refutations of its targets, the
  transitions and the at-least-one constraint of its layer, and each removal of a value of `W`
  or `P` from the clauses `S_t ⇒ [W ≠ u]`, the refutations of the last layer and its at-least-one
  constraint.

The proof has no conclusion; it runs with the direct literals as the preserved set. It deletes
nothing (difference 5 allows deleting the intermediate constraints at the end).

## Main definitions

* `Cslib.Logic.PL.VeriPB.Knapsack.Trick.Inst`: an instance, with its domains.
* `Cslib.Logic.PL.VeriPB.Knapsack.Trick.Inst.formula`,
  `Inst.antecedent`: the encoding and the antecedent `D`.
* `Inst.lay`: the layers.
* `Cslib.Logic.PL.VeriPB.Knapsack.Trick.Propagation`,
  `Cslib.Logic.PL.VeriPB.Knapsack.Trick.Inst.propagate`: the propagator and its output.

## References

* [E. Demirović, C. McCreesh, M. J. McIlree, J. Nordström, A. Oertel, K. Sidorov, *Pseudo-Boolean
  Reasoning About States and Transitions to Certify Dynamic Programming and Decision Diagram
  Algorithms*][DemirovicMcCreeshMcIlreeNordstromOertelSidorov2024]
* [S. Gocht, C. McCreesh, J. Nordström, *An Auditable Constraint Programming
  Solver*][GochtMcCreeshNordstrom2022]
-/

public section

namespace Cslib.Logic.PL.VeriPB.Knapsack.Trick

open PBConstr

/-- **A domain**: the values of an initial domain, in order, each with a flag that is `true` while
the value is in the current domain. -/
abbrev Dom := List (ℕ × Bool)

/-- **An instance of the two-equality knapsack constraint**: `n` items of weights `w` and profits
`p`, the domains of the items, and those of the weight `W` and of the profit `P`. -/
structure Inst where
  /-- The number of items. -/
  n : ℕ
  /-- The weights. -/
  w : ℕ → ℕ
  /-- The profits. -/
  p : ℕ → ℕ
  /-- The domains of the items. -/
  dom : ℕ → Dom
  /-- The domain of the weight. -/
  wDom : Dom
  /-- The domain of the profit. -/
  pDom : Dom

/-- The value at position `k` of a domain. -/
def dval (D : Dom) (k : ℕ) : ℕ := (D.getD k (0, false)).1

/-- The value at position `k` of a domain is in the current domain. -/
def dlive (D : Dom) (k : ℕ) : Bool := (D.getD k (0, false)).2

/-- The positions of a domain whose values are in the current domain. -/
def livePos (D : Dom) : List ℕ := (List.range D.length).filter (dlive D)

/-- The terms `D[k] ℓₖ` over the positions `k` of a domain with a nonzero value, `ℓₖ` the literal
of the variable `base + k` with the polarity `pol`. -/
def sTerms (D : Dom) (base : ℕ) (pol : Bool) : List (ℕ × Literal ℕ) :=
  (List.range D.length).filterMap fun k =>
    if dval D k = 0 then none else some (dval D k, (base + k, pol))

/-- The sum of the values of a domain. -/
def sTot (D : Dom) : ℕ := ((List.range D.length).map (dval D)).sum

/-- At least one of the variables `base, …, base + m - 1` is true. -/
def alo (base m : ℕ) : PBConstr := ⟨(List.range m).map fun k => (1, (base + k, true)), 1⟩

/-- At most one of the variables `base, …, base + m - 1` is true. -/
def amo (base m : ℕ) : PBConstr := ⟨(List.range m).map fun k => (1, (base + k, false)), m - 1⟩

/-- A state: the weight and the profit so far. -/
abbrev St := ℕ × ℕ

namespace Inst

variable (I : Inst)

/-- The length of the domain of item `j`. -/
def len (j : ℕ) : ℕ := (I.dom j).length

/-- The first variable of item `j`. -/
def off (j : ℕ) : ℕ := ((List.range j).map I.len).sum

/-- The direct literal of position `k` of item `j`. -/
def var (j k : ℕ) : ℕ := I.off j + k

/-- The first variable of the weight. -/
def wBase : ℕ := I.off I.n

/-- The first variable of the profit. -/
def pBase : ℕ := I.wBase + I.wDom.length

/-- The variables of the formula are below `M`; the extension variables start there. -/
def M : ℕ := I.pBase + I.pDom.length

/-- The weight `wⱼ v` of the value at position `k` of item `j`. -/
def cw (j k : ℕ) : ℕ := I.w j * dval (I.dom j) k

/-- The profit `pⱼ v` of the value at position `k` of item `j`. -/
def cp (j k : ℕ) : ℕ := I.p j * dval (I.dom j) k

/-- The coefficients `a j k` of all positions, item after item. -/
def coefs (a : ℕ → ℕ → ℕ) : List ℕ :=
  (List.range I.n).flatMap fun j => (List.range (I.len j)).map (a j)

/-- The coefficient of the variable `x`: `a j k` for `x = off j + k`. -/
def flat (a : ℕ → ℕ → ℕ) (x : ℕ) : ℕ := (I.coefs a).getD x 0

/-- The terms `a j k ℓ` over the positions of the items `j < i` with `a j k ≠ 0`, `ℓ` the direct
literal with the polarity `pol`. -/
def terms (a : ℕ → ℕ → ℕ) (pol : Bool) (i : ℕ) : List (ℕ × Literal ℕ) :=
  Knapsack.Inst.sumTerms (I.flat a) pol (I.off i)

/-- `∑_{j<i} ∑ₖ a j k`. -/
def tot (a : ℕ → ℕ → ℕ) (i : ℕ) : ℕ := Knapsack.Inst.tot (I.flat a) (I.off i)

/-- The constraint `∑_{j<i} ∑ₖ a j k ℓ ≥ d`. -/
def dimC (a : ℕ → ℕ → ℕ) (pol : Bool) (i d : ℕ) : PBConstr :=
  Knapsack.Inst.dimC (I.flat a) pol (I.off i) d

/-! ### The encoding -/

/-- The weight is at least its sum over the items: `∑ wⱼ v [xⱼ = v] + ∑ u [W ≠ u] ≥ ∑ u`. -/
def linkW₁ : PBConstr := ⟨I.terms I.cw true I.n ++ sTerms I.wDom I.wBase false, sTot I.wDom⟩

/-- The weight is at most its sum over the items: `∑ wⱼ v [xⱼ ≠ v] + ∑ u [W = u] ≥ ∑ wⱼ v`. -/
def linkW₂ : PBConstr := ⟨I.terms I.cw false I.n ++ sTerms I.wDom I.wBase true, I.tot I.cw I.n⟩

/-- The profit is at least its sum over the items. -/
def linkP₁ : PBConstr := ⟨I.terms I.cp true I.n ++ sTerms I.pDom I.pBase false, sTot I.pDom⟩

/-- The profit is at most its sum over the items. -/
def linkP₂ : PBConstr := ⟨I.terms I.cp false I.n ++ sTerms I.pDom I.pBase true, I.tot I.cp I.n⟩

/-- **The formula**: the four inequalities of the two equalities, numbered `1`–`4`; the
exactly-one constraints of `W`, numbered `5` and `6`, and of `P`, `7` and `8`; then those of each
item `j`, numbered `9 + 2j` and `10 + 2j`. -/
def formula : List PBConstr :=
  [I.linkW₁, I.linkW₂, I.linkP₁, I.linkP₂, alo I.wBase I.wDom.length, amo I.wBase I.wDom.length,
    alo I.pBase I.pDom.length, amo I.pBase I.pDom.length] ++
  (List.range I.n).flatMap fun j => [alo (I.off j) (I.len j), amo (I.off j) (I.len j)]

/-- The number of the at-least-one constraint of item `j`. -/
private def aloId (j : ℕ) : ℕ := 9 + 2 * j

/-- The number of the at-most-one constraint of item `j`. -/
private def amoId (j : ℕ) : ℕ := 10 + 2 * j

/-- The first number after the formula. -/
private def start : ℕ := 9 + 2 * I.n

/-- The variables preserved: the direct literals. -/
def pres : List ℕ := List.range I.M

/-- **The antecedent `D`**: the negations `[x ≠ v]` of the values not in the current domains. -/
private def antecedent : List (Literal ℕ) :=
  ((List.range I.n).flatMap fun j =>
    (List.range (I.len j)).filterMap fun k =>
      if dlive (I.dom j) k then none else some (I.var j k, false)) ++
  ((List.range I.wDom.length).filterMap fun k =>
    if dlive I.wDom k then none else some (I.wBase + k, false)) ++
  ((List.range I.pDom.length).filterMap fun k =>
    if dlive I.pDom k then none else some (I.pBase + k, false))

/-- The negation of the antecedent, the first literals of every derived clause. -/
private def negD : List (Literal ℕ) := I.antecedent.map Std.Sat.Literal.negate

/-- The direct literals of the values of item `i` not in its current domain. -/
private def negItem (i : ℕ) : List (Literal ℕ) :=
  (List.range (I.len i)).filterMap fun k =>
    if dlive (I.dom i) k then none else some (I.var i k, true)

/-! ### The layers -/

/-- The successor of the state `st` by the value at position `k` of item `i`. -/
private def succ (i : ℕ) (st : St) (k : ℕ) : St := (st.1 + I.cw i k, st.2 + I.cp i k)

/-- The states of the next layer. -/
private def nextL (i : ℕ) (L : List St) : List St :=
  (L.flatMap fun st => (livePos (I.dom i)).map (I.succ i st)).dedup

/-- **The states of layer `i`**, those reached by the first `i` items. -/
private def lay : ℕ → List St
  | 0 => [(0, 0)]
  | i + 1 => I.nextL i (lay i)

/-- A state of the last layer is feasible: its weight and profit are in the current domains. -/
private def feasible (st : St) : Bool :=
  (livePos I.wDom).any (fun k => dval I.wDom k == st.1) &&
    (livePos I.pDom).any (fun k => dval I.pDom k == st.2)

/-- The states of layer `i` with a feasible completion, by `k = n - i` backward layers. -/
private def aliveAt : ℕ → ℕ → List St
  | 0, i => (I.lay i).filter I.feasible
  | k + 1, i =>
    let A := aliveAt k (i + 1)
    (I.lay i).filter fun st => (livePos (I.dom i)).any fun k => I.succ i st k ∈ A

/-- The states of layer `i` with a feasible completion. -/
private def alive (i : ℕ) : List St := I.aliveAt (I.n - i) i

end Inst

/-! ### The proof being written -/

/-- A node of the decision diagram: its state, the first of its five extension variables (the
partial states `W↑`, `W↓`, `P↑`, `P↓`, then `S`) and the number before its constraints; the halves
of the reification of its `d`-th variable are numbered `c + 4d + 1` and `c + 4d + 3`. -/
structure Node where
  /-- The state. -/
  st : St
  /-- The first extension variable. -/
  v : ℕ
  /-- The number before the constraints. -/
  c : ℕ

/-- The `d`-th extension variable of a node. -/
private def Node.z (u : Node) (d : ℕ) : ℕ := u.v + d

/-- The number of `z_d ⇒ …`. -/
private def Node.fwd (u : Node) (d : ℕ) : ℕ := u.c + 4 * d + 1

/-- The number of `… ⇒ z_d`. -/
private def Node.bwd (u : Node) (d : ℕ) : ℕ := u.c + 4 * d + 3

/-- The state variable `S`. -/
private def Node.S (u : Node) : ℕ := u.v + 4

/-- A placeholder node, never reached on the layers. -/
private def noNode : Node := ⟨(0, 0), 0, 0⟩

/-- A transition out of a node: the position of the value of its item, the target and the number
of `S ∧ [x = v] ⇒ S'`. -/
structure Tr where
  /-- The position of the value. -/
  pos : ℕ
  /-- The target. -/
  tgt : Node
  /-- The number of the implication. -/
  id : ℕ

/-- The transitions out of a node and the number of `S ∧ D ⇒ ⋁ S'`. -/
structure Out where
  /-- The node. -/
  u : Node
  /-- The transitions. -/
  tr : List Tr
  /-- The number of `S ∧ D ⇒ ⋁ S'`. -/
  succ : ℕ

/-- A layer of the diagram: its index, nodes, transitions out (none for the last) and the number
of its at-least-one constraint. -/
structure Layer where
  /-- The index. -/
  i : ℕ
  /-- The nodes. -/
  nodes : List Node
  /-- The transitions out. -/
  outs : List Out
  /-- The number of the at-least-one constraint. -/
  alo : ℕ

/-- The node of a layer with the state `st`. -/
private def tgt (L : List Node) (st : St) : Node := (L.find? (·.st == st)).getD noNode

/-- The target of the transitions by the position `k`. -/
private def Out.tgtOf (o : Out) (k : ℕ) : Node :=
  ((o.tr.find? (·.pos == k)).map (·.tgt)).getD noNode

/-- The number of the implication of the transition by the position `k`. -/
private def Out.tau (o : Out) (k : ℕ) : ℕ := ((o.tr.find? (·.pos == k)).map (·.id)).getD 0

/-- The state constraint `W↑ + W↓ + P↑ + P↓ ≥ 4` over the variables `v, …, v + 3`. -/
private def cS (v : ℕ) : PBConstr := ⟨(List.range 4).map fun d => (1, (v + d, true)), 4⟩

namespace Inst

variable (I : Inst)

/-- The coefficients of the partial state `d`: the weights for `W↑`, `W↓`, the profits for `P↑`,
`P↓`. -/
private def dimA (d : ℕ) : ℕ → ℕ → ℕ := if d < 2 then I.cw else I.cp

/-- The polarity of the partial state `d`: `true` for `W↑`, `P↑`, and `false` for `W↓`, `P↓`,
which bound the sum over the negated literals from below. -/
private def dimPol (d : ℕ) : Bool := d % 2 == 0

/-- The coordinate of the state that the partial state `d` bounds. -/
private def dimS (st : St) (d : ℕ) : ℕ := if d < 2 then st.1 else st.2

/-- The partial state `d` of a state of layer `i`: `∑ a ℓ ≥ s` for `↑`, and `∑ a ¬ℓ ≥ ∑ a - s`, that
is `∑ a ℓ ≤ s`, for `↓`. -/
private def cD (i : ℕ) (st : St) (d : ℕ) : PBConstr :=
  I.dimC (I.dimA d) (dimPol d) i (if dimPol d then dimS st d else I.tot (I.dimA d) i - dimS st d)

/-- The node of the state `st` created at `e`. -/
private def mkNode (e : ProofLog) (st : St) : Node := ⟨st, e.var, e.next⟩

/-- The reifications of a node of layer `i`. -/
private def nodeSteps (i : ℕ) (u : Node) : List TopStep :=
  reify (u.z 0) (I.cD i u.st 0) ++ reify (u.z 1) (I.cD i u.st 1) ++ reify (u.z 2) (I.cD i u.st 2) ++
    reify (u.z 3) (I.cD i u.st 3) ++ reify u.S (cS u.v)

/-- Create the nodes of layer `i`. -/
private def mkLayer (i : ℕ) : ProofLog → List St → ProofLog × List Node
  | e, [] => (e, [])
  | e, st :: sts =>
    let u := mkNode e st
    let r := mkLayer i (e.push (I.nodeSteps i u) 20 5) sts
    (r.1, u :: r.2)

/-- The implication `S_u ∧ [xᵢ = v] ⇒ S_t` for the value at position `k`. -/
private def trClause (i k : ℕ) (u t : Node) : PBConstr :=
  clause [(u.S, false), (I.var i k, false), (t.S, true)]

/-- The transition steps: add the forward half of each partial state of `u` to the backward half
of that of `t`, then RUP, the at-most-one constraint of item `i` first. -/
private def trSteps (i k : ℕ) (u t : Node) (e : ProofLog) : List TopStep :=
  [.step (.pol [.id (u.fwd 0), .id (t.bwd 0), .add]),
    .step (.pol [.id (u.fwd 1), .id (t.bwd 1), .add]),
    .step (.pol [.id (u.fwd 2), .id (t.bwd 2), .add]),
    .step (.pol [.id (u.fwd 3), .id (t.bwd 3), .add]),
    .step (.rup (I.trClause i k u t) [.neg, .id (amoId i), .id (u.fwd 4), .id e.next,
      .id (e.next + 1), .id (e.next + 2), .id (e.next + 3), .id (t.bwd 4)])]

/-- The transitions out of `u` into the layer `L'`, for the positions `ks`. -/
private def trans1 (i : ℕ) (L' : List Node) (u : Node) : ProofLog → List ℕ → ProofLog × List Tr
  | e, [] => (e, [])
  | e, k :: ks =>
    let t := tgt L' (I.succ i u.st k)
    let r := trans1 i L' u (e.push (I.trSteps i k u t e) 5 0) ks
    (r.1, ⟨k, t, e.next + 4⟩ :: r.2)

/-- `S_u ∧ D ⇒ ⋁ S_t` over the targets of the transitions `tr`. -/
private def succClause (i : ℕ) (u : Node) (tr : List Tr) : PBConstr :=
  clause ((u.S, false) :: I.negItem i ++ tr.map fun x => (x.tgt.S, true))

/-- The transitions out of `u`, then `S_u ∧ D ⇒ ⋁ S_t` by RUP. -/
private def transOut (i : ℕ) (L' : List Node) (e : ProofLog) (u : Node) : ProofLog × Out :=
  let r := I.trans1 i L' u e (livePos (I.dom i))
  (r.1.push [.step (.rup (I.succClause i u r.2) (.neg :: r.2.map (fun x => .id x.id) ++
    [.id (aloId i)]))] 1 0, ⟨u, r.2, r.1.next⟩)

/-- The transitions out of a layer. -/
private def trans (i : ℕ) (L' : List Node) : ProofLog → List Node → ProofLog × List Out
  | e, [] => (e, [])
  | e, u :: us =>
    let r := I.transOut i L' e u
    let q := trans i L' r.1 us
    (q.1, r.2 :: q.2)

/-- The at-least-one constraint of a layer, under the domains: `D ⇒ ⋁ S_u`. -/
private def aloClause (L : List Node) : PBConstr := clause (I.negD ++ L.map fun u => (u.S, true))

/-- The forward pass: from layer `i`, `k` more layers with their transitions and at-least-one
constraints. The records are returned latest first. -/
private def fwd : ℕ → ℕ → ProofLog → List Node → ℕ → List Layer → ProofLog × List Layer
  | 0, i, e, L, a, recs => (e, ⟨i, L, [], a⟩ :: recs)
  | k + 1, i, e, L, a, recs =>
    let r₁ := I.mkLayer (i + 1) e (I.nextL i (L.map (·.st)))
    let r₂ := I.trans i r₁.2 r₁.1 L
    let e' := r₂.1.push [.step (.rup (I.aloClause r₁.2)
      (.neg :: r₂.2.map (fun o => .id o.succ) ++ [.id a]))] 1 0
    fwd k (i + 1) e' r₁.2 r₂.1.next (⟨i, L, r₂.2, a⟩ :: recs)

/-- **The forward pass from the start**: the node of layer `0`, its at-least-one constraint by
RUP, and the layers `1, …, n`. The records are returned latest first. -/
private def forward : ProofLog × List Layer :=
  let r₀ := I.mkLayer 0 ⟨[], I.start, I.M⟩ (I.lay 0)
  let u₀ := r₀.2.headD noNode
  let e₁ := r₀.1.push [.step (.rup (I.aloClause r₀.2) [.neg, .id (u₀.bwd 0), .id (u₀.bwd 1),
    .id (u₀.bwd 2), .id (u₀.bwd 3), .id (u₀.bwd 4)])] 1 0
  I.fwd I.n 0 e₁ r₀.2 r₀.1.next []

/-! ### The last layer and the sums -/

/-- The domain of the sum `s`: `W` for `false`, `P` for `true`. -/
private def sDom (s : Bool) : Dom := if s then I.pDom else I.wDom

/-- The first variable of the sum `s`. -/
private def sBase (s : Bool) : ℕ := if s then I.pBase else I.wBase

/-- The coordinate of the state that the sum `s` is. -/
private def sCoord (s : Bool) (st : St) : ℕ := if s then st.2 else st.1

/-- The partial state `↑` of the sum `s`. -/
private def sUp (s : Bool) : ℕ := if s then 2 else 0

/-- The number of the at-least-one constraint of the sum `s`. -/
private def sAlo (s : Bool) : ℕ := if s then 7 else 5

/-- The number of the at-most-one constraint of the sum `s`. -/
private def sAmo (s : Bool) : ℕ := if s then 8 else 6

/-- The clause `S_t ⇒ [s ≠ u]` for the value at position `k` of the sum `s`. -/
private def sClause (s : Bool) (t : Node) (k : ℕ) : PBConstr :=
  clause [(t.S, false), (I.sBase s + k, false)]

/-- The steps of `S_t ⇒ [s ≠ u]`: for `u` above the coordinate of `t`, add the forward half of its
`↓` to the first inequality of the sum, and otherwise that of its `↑` to the second; then RUP, the
at-most-one constraint of the sum first. -/
private def sSteps (s : Bool) (t : Node) (k : ℕ) (e : ProofLog) : List TopStep :=
  let ops := if sCoord s t.st < dval (I.sDom s) k then
      [PolOp.id (t.fwd (sUp s + 1)), .id (if s then 3 else 1), .add]
    else [PolOp.id (t.fwd (sUp s)), .id (if s then 4 else 2), .add]
  [.step (.pol ops), .step (.rup (I.sClause s t k) [.neg, .id (sAmo s), .id (t.fwd 4), .id e.next])]

/-- The positions of the current domain of the sum `s` other than the coordinate of `t`. -/
private def others (s : Bool) (t : Node) : List ℕ :=
  (livePos (I.sDom s)).filter fun k => dval (I.sDom s) k != sCoord s t.st

/-- The clauses `S_t ⇒ [s ≠ u]` of the node `t`, for both sums, with their numbers: entries
`((S_t, s, k), number)`. -/
private def sAll (t : Node) : ProofLog → List (Bool × ℕ) → ProofLog × List ((ℕ × Bool × ℕ) × ℕ)
  | e, [] => (e, [])
  | e, (s, k) :: xs =>
    let r := sAll t (e.push (I.sSteps s t k e) 2 0) xs
    (r.1, ((t.S, s, k), e.next + 1) :: r.2)

/-- The clauses of all nodes of the last layer. -/
private def sLayer : ProofLog → List Node → ProofLog × List ((ℕ × Bool × ℕ) × ℕ)
  | e, [] => (e, [])
  | e, t :: ts =>
    let r := I.sAll t e ((I.others false t).map (false, ·) ++ (I.others true t).map (true, ·))
    let q := sLayer r.1 ts
    (q.1, r.2 ++ q.2)

/-- The entry for `x` of a list of pairs. -/
private def slook (sl : List ((ℕ × Bool × ℕ) × ℕ)) (x : ℕ × Bool × ℕ) : ℕ :=
  ((sl.find? (·.1 == x)).map (·.2)).getD 0

/-- The refutation of a state under the domains: `D ⇒ ¬S`. -/
private def deadClause (S : ℕ) : PBConstr := clause (I.negD ++ [(S, false)])

/-- The sum that refutes an infeasible state of the last layer: `W` if its weight is not in the
current domain, and `P` otherwise. -/
private def deadSum (st : St) : Bool := (livePos I.wDom).any (fun k => dval I.wDom k == st.1)

/-- The infeasible states of the last layer: refute `S_t` by RUP from its clauses `S_t ⇒ [s ≠ u]`
and the at-least-one constraint of the sum. -/
private def deadFinal (sl : List ((ℕ × Bool × ℕ) × ℕ)) :
    ProofLog → List Node → ProofLog × List (ℕ × ℕ)
  | e, [] => (e, [])
  | e, t :: ts =>
    if I.feasible t.st then deadFinal sl e ts
    else
      let s := I.deadSum t.st
      let r := deadFinal sl (e.push [.step (.rup (I.deadClause t.S)
        (.neg :: (I.others s t).map (fun k => .id (slook sl (t.S, s, k))) ++
          [.id (sAlo s)]))] 1 0) ts
      (r.1, (t.S, e.next) :: r.2)

/-- The states of layer `i` without a feasible completion, refuted by RUP from the refutations of
their targets and `S ∧ D ⇒ ⋁ S'`. -/
private def deadLayer (i : ℕ) (A : List St) (dl : List (ℕ × ℕ)) :
    ProofLog → List Out → ProofLog × List (ℕ × ℕ)
  | e, [] => (e, [])
  | e, o :: os =>
    if (livePos (I.dom i)).any fun k => I.succ i o.u.st k ∈ A then deadLayer i A dl e os
    else
      let r := deadLayer i A dl (e.push [.step (.rup (I.deadClause o.u.S)
        (.neg :: o.tr.map (fun x => .id (dlook dl x.tgt.S)) ++ [.id o.succ]))] 1 0) os
      (r.1, (o.u.S, e.next) :: r.2)

/-- What the backward pass records for a layer: the layer, the alive states of the layer after
it and their refutations. -/
structure Back where
  /-- The layer. -/
  layer : Layer
  /-- The alive states of the next layer. -/
  alive : List St
  /-- The refutations of the next layer. -/
  dead : List (ℕ × ℕ)

/-- The backward pass over the layers `rs`, latest first, from the alive states `A` and the
refutations `dl` of the layer after them. Returns each layer with the alive states and the
refutations of the layer after it. -/
private def backAll : ProofLog → List St → List (ℕ × ℕ) → List Layer → ProofLog × List Back
  | e, _, _, [] => (e, [])
  | e, A, dl, r :: rs =>
    let d := I.deadLayer r.i A dl e r.outs
    let A' := (r.nodes.map (·.st)).filter fun st =>
      (livePos (I.dom r.i)).any fun k => I.succ r.i st k ∈ A
    let q := backAll d.1 A' d.2 rs
    (q.1, ⟨r, A, dl⟩ :: q.2)

/-! ### The removals -/

/-- The removal of the value at position `k` of item `i`: `D ⇒ [xᵢ ≠ v]`. -/
private def remClause (i k : ℕ) : PBConstr := clause (I.negD ++ [(I.var i k, false)])

/-- The removals of a layer: the values all of whose transitions lead to refuted states, by RUP
from those refutations, the transitions and the at-least-one constraint. -/
private def remLayer (r : Layer) (A : List St) (dl : List (ℕ × ℕ)) :
    ProofLog → List ℕ → ProofLog × List ((ℕ × ℕ) × ℕ)
  | e, [] => (e, [])
  | e, k :: ks =>
    if r.outs.all fun o => I.succ r.i o.u.st k ∉ A then
      let hs := .neg :: r.outs.map (fun o => .id (dlook dl (o.tgtOf k).S)) ++
        r.outs.map (fun o => .id (o.tau k)) ++ [.id r.alo]
      let q := remLayer r A dl (e.push [.step (.rup (I.remClause r.i k) hs)] 1 0) ks
      (q.1, ((r.i, k), e.next) :: q.2)
    else remLayer r A dl e ks

/-- The removals of all layers. -/
private def remAll : ProofLog → List Back → ProofLog × List ((ℕ × ℕ) × ℕ)
  | e, [] => (e, [])
  | e, x :: xs =>
    let q := I.remLayer x.layer x.alive x.dead e (livePos (I.dom x.layer.i))
    let q' := remAll q.1 xs
    (q'.1, q.2 ++ q'.2)

/-- The removal of the value at position `k` of the sum `s`: `D ⇒ [s ≠ u]`. -/
private def remSClause (s : Bool) (k : ℕ) : PBConstr := clause (I.negD ++ [(I.sBase s + k, false)])

/-- The removals of the sum `s`: the values of its current domain that no feasible state of the
last layer `L` has, by RUP from the clauses `S_t ⇒ [s ≠ u]` of the feasible states, the
refutations `dl` of the others, and the at-least-one constraint `a` of the last layer. -/
private def remSum (s : Bool) (L : List Node) (sl : List ((ℕ × Bool × ℕ) × ℕ)) (dl : List (ℕ × ℕ))
    (a : ℕ) : ProofLog → List ℕ → ProofLog × List (ℕ × ℕ)
  | e, [] => (e, [])
  | e, k :: ks =>
    if L.all fun t => !(I.feasible t.st && sCoord s t.st == dval (I.sDom s) k) then
      let hs := .neg :: L.map (fun t => .id (if I.feasible t.st then slook sl (t.S, s, k)
        else dlook dl t.S)) ++ [.id a]
      let q := remSum s L sl dl a (e.push [.step (.rup (I.remSClause s k) hs)] 1 0) ks
      (q.1, (k, e.next) :: q.2)
    else remSum s L sl dl a e ks

/-- What the propagator writes: the proof and the removals with their numbers, of the item
values, then of the values of `W` and of `P`. -/
structure Emitted where
  /-- The proof. -/
  acc : ProofLog
  /-- The removed item values `(j, k)`, with their numbers. -/
  items : List ((ℕ × ℕ) × ℕ)
  /-- The removed values of `W`, with their numbers. -/
  ws : List (ℕ × ℕ)
  /-- The removed values of `P`, with their numbers. -/
  ps : List (ℕ × ℕ)

/-- **The whole proof** and the removals with their numbers: the item values, then the values of
`W` and of `P`. -/
private def emit : Emitted :=
  let f := I.forward
  let rn := f.2.headD ⟨0, [], [], 0⟩
  let s := I.sLayer f.1 rn.nodes
  let d := I.deadFinal s.2 s.1 rn.nodes
  let b := I.backAll d.1 ((rn.nodes.map (·.st)).filter I.feasible) d.2 f.2.tail
  let r := I.remAll b.1 b.2
  let rw := I.remSum false rn.nodes s.2 d.2 rn.alo r.1 (livePos I.wDom)
  let rp := I.remSum true rn.nodes s.2 d.2 rn.alo rw.1 (livePos I.pDom)
  ⟨rp.1, r.2, rw.2, rp.2⟩

end Inst

/-- **The output of the propagator**: the removed values, as positions `(j, k)` of the items and
positions of the domains of `W` and `P`, and a kernel proof, with no conclusion, deriving
`D ⇒ [x ≠ v]` for each. -/
structure Propagation where
  /-- The removed values of the items. -/
  removed : List (ℕ × ℕ)
  /-- The removed values of the weight. -/
  removedW : List ℕ
  /-- The removed values of the profit. -/
  removedP : List ℕ
  /-- The proof. -/
  proof : RedProof

/-- **The propagator.** -/
def Inst.propagate (I : Inst) : Propagation :=
  ⟨I.emit.items.map (·.1), I.emit.ws.map (·.1), I.emit.ps.map (·.1),
    ⟨I.emit.acc.steps.reverse, .noClaim⟩⟩

end Cslib.Logic.PL.VeriPB.Knapsack.Trick

end
