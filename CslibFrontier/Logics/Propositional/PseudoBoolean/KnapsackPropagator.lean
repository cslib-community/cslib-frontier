/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.Knapsack
-- `import all`: the acceptance proof unfolds `stepTop`, `runTop`, the reification steps, and the
-- emitter's definitions and private lemmas.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Reification
import all CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackDP
import CslibFrontier.Logics.Propositional.PseudoBoolean.Fast
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

**The proof.** The forward pass is the state-graph emitter of
`CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackDP`, shared with the certified knapsack,
run without merging or pruning (`Cslib.Logic.PL.VeriPB.Knapsack.Mode`): as in the paper's
equations (8)–(23), each node `u` of layer `i` gets extension variables, defined by
`Cslib.Logic.PL.VeriPB.reify`:
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
(`Cslib.Logic.PL.VeriPB.Knapsack.checkRed_propagate`), and the database it reaches holds the
removal clause `D ⇒ xⱼ ≠ b` (`Cslib.Logic.PL.VeriPB.Knapsack.remClause`,
`Cslib.Logic.PL.VeriPB.Knapsack.holds_remClause_iff`) of every removed value
(`Cslib.Logic.PL.VeriPB.Knapsack.runTop_propagate`). This is proved, not checked when the proof
runs, for the forward pass by `Cslib.Logic.PL.VeriPB.Knapsack.Inst.forward_spec`: each `rup` step
is shown accepted by the completeness of unit propagation on constraints over
distinct variables (`CslibFrontier.Logics.Propositional.PseudoBoolean.RupComplete`), from the
meaning of the constraints its hints name, and each addition by the slacks of the reification
halves. The propagator removes exactly the unsupported values
(`Cslib.Logic.PL.VeriPB.Knapsack.mem_removed_iff`): a removed value is unsupported because the
checker's soundness makes its derived clause `D ⇒ xⱼ ≠ b` hold at every solution, and an
unsupported value is removed because the dynamic program is exact.

**Departures from the paper.** §3.3 (p. 9:11) cites Trick's propagator for a single `0`–`1`
linear inequality whose sum is an integer variable, and the work of Fahle and Sellmann, Sellmann,
Katriel et al. and Malitsky et al., and MiniZinc's definition, for two linear equalities summing to
two integer variables over items that need not be `0`–`1`. Its proof has states `S^i_{w,p}`
reifying exact sums by four variables (equations (24)–(26)), direct variables for non-Boolean
domains, and propagation on the sum variables. Here the items are `0`–`1` variables with domains
of fixed literals, the sums are bounded by constants, and each state reifies one-sided sums by two
variables, as in §3.1: a weight of at least `w` and a profit left out of at least `q`. Every
condition under which a state is refuted is monotone in both, so the one-sided states suffice,
and the states are still exact. The proof deletes nothing. The integer-domain constraint with sum
variables and the exact states of equations (24)–(26) is tracked in #7222 and formalized in
#8789.

## Main definitions

* `Cslib.Logic.PL.VeriPB.Knapsack.profitBound`, `Cslib.Logic.PL.VeriPB.Knapsack.propFormula`: the
  encoding.
* `Cslib.Logic.PL.VeriPB.Knapsack.Supported`: a value supported under the domains.
* `Cslib.Logic.PL.VeriPB.Knapsack.Propagation`, `Cslib.Logic.PL.VeriPB.Knapsack.propagate`: the
  propagator and its output.
* `Cslib.Logic.PL.VeriPB.Knapsack.remClause`: the removal clause `D ⇒ xⱼ ≠ b`.

## Main results

* `Cslib.Logic.PL.VeriPB.Knapsack.holds_profitBound_iff`: the profit constraint is correct.
* `Cslib.Logic.PL.VeriPB.Knapsack.runTop_propagate`: the propagator's proof runs and derives the
  removal clause of every removed value, whose meaning is
  `Cslib.Logic.PL.VeriPB.Knapsack.holds_remClause_iff`.
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


namespace Cslib.Logic.PL.VeriPB.Knapsack

open PBConstr

namespace Inst

variable (I : Inst)

/-- The profit constraint `∑ pⱼ xⱼ ≥ P`. -/
private def profC : PBConstr := ⟨(List.range I.n).map fun j => (I.p j, (j, true)), I.P⟩

/-- The formula: the capacity and the profit constraints, numbered `1` and `2`. -/
private def F : List PBConstr := [I.capC, I.profC]

/-- The preserved set: the item variables. -/
private def pres : List ℕ := List.range I.n

/-- The options of the propagator: exact states, no pruning. -/
private def exact : Mode := ⟨false, false⟩

/-- The reachable states of layer `i`. -/
private def lay (i : ℕ) : List St := I.layM exact i

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

/-- Where the propagator's dynamic program starts: the formula, no objective, the item variables
preserved, and the profit constraint numbered `2`. -/
private def X₀ : Ctx := ⟨I.F, none, State.init I.F none (some I.pres), I.profC⟩

/-- The refutation of a state under the domains: `D ⇒ ¬S`. -/
private def deadClause (S : ℕ) : PBConstr := clause (I.negD ++ [(S, false)])

/-- The infeasible states of the last layer: add the forward half of `W` to the capacity
constraint, or that of `P` to the profit constraint, then RUP. -/
private def deadFinal : ProofLog → List Node → ProofLog × List (ℕ × ℕ)
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
    ProofLog → List Out → ProofLog × List (ℕ × ℕ)
  | e, [] => (e, [])
  | e, o :: os =>
    if (vals (I.dom i)).any fun b => I.succSt i o.u.st b ∈ A then deadLayer i A dl e os
    else
      let r := deadLayer i A dl (e.push [.step (.rup (I.deadClause o.u.S)
        (.neg :: o.tr.map (fun x => .id (dlook dl x.tgt.S)) ++ [.id o.succ]))] 1 0) os
      (r.1, (o.u.S, e.next) :: r.2)

/-- The backward pass over the layers `rs`, latest first, from the alive states `A` and the
refutations `dl` of the layer after them. Returns each layer with the alive states and the
refutations of the layer after it. -/
private def backAll : ProofLog → List St → List (ℕ × ℕ) → List LayerRec →
    ProofLog × List (LayerRec × List St × List (ℕ × ℕ))
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
    ProofLog → List Bool → ProofLog × List (ℕ × Bool × ℕ)
  | e, [] => (e, [])
  | e, b :: bs =>
    if r.outs.all fun o => I.succSt r.i o.u.st b ∉ A then
      let hs := .neg :: r.outs.map (fun o => .id (dlook dl (o.tgt b).S)) ++
        r.outs.map (fun o => .id (o.tau b)) ++ [.id r.alo]
      let q := remLayer r A dl (e.push [.step (.rup (I.remClause r.i b) hs)] 1 0) bs
      (q.1, (r.i, b, e.next) :: q.2)
    else remLayer r A dl e bs

/-- The removals of all layers. -/
private def remAll :
    ProofLog → List (LayerRec × List St × List (ℕ × ℕ)) → ProofLog × List (ℕ × Bool × ℕ)
  | e, [] => (e, [])
  | e, x :: xs =>
    let q := I.remLayer x.1 x.2.1 x.2.2 e (vals (I.dom x.1.i))
    let q' := remAll q.1 xs
    (q'.1, q.2 ++ q'.2)

/-- The whole proof, before its conclusion, and the removals with their numbers. -/
private def emit : ProofLog × List (ℕ × Bool × ℕ) :=
  let f := I.forward exact
  let rn := f.2.headD ⟨0, [], [], 0⟩
  let d := I.deadFinal f.1 rn.nodes
  let b := I.backAll d.1 ((rn.nodes.map (·.st)).filter I.finalOk) d.2 f.2.tail
  I.remAll b.1 b.2

end Inst

/-- **The output of the propagator**: the removed values `(i, b)`, item `i` no longer taking the
value `b`, and a kernel proof, with no conclusion, deriving `D ⇒ xᵢ ≠ b` for each. -/
public structure Propagation where
  /-- The removed values. -/
  removed : List (ℕ × Bool)
  /-- The proof. -/
  proof : RedProof

/-- The propagator on an ℕ-indexed instance. -/
private def Inst.run (I : Inst) : Propagation :=
  ⟨I.emit.2.map fun x => (x.1, x.2.1), ⟨I.emit.1.steps.reverse, .noClaim⟩⟩


namespace Inst

variable (I : Inst)

/-! ### The propagator's start and its exact layers -/

private theorem keep_exact (i : ℕ) (st : St) (b : Bool) : I.keep exact i st b = true := by
  simp [keep, exact]

private theorem nextL_exact (i : ℕ) (L : List St) :
    I.nextL exact i L = (L.flatMap fun st => (vals (I.dom i)).map (I.succSt i st)).dedup := by
  have h : ∀ st, (vals (I.dom i)).filter (I.keep exact i st) = vals (I.dom i) := fun st =>
    List.filter_eq_self.2 fun b _ => I.keep_exact i st b
  simp only [nextL, cands, h]
  rfl

private theorem mem_nextLay {i : ℕ} {st : St} (hst : st ∈ I.lay i) {b : Bool}
    (hb : b ∈ vals (I.dom i)) : I.succSt i st b ∈ I.lay (i + 1) := by
  simp only [lay, layM, nextL_exact, List.mem_dedup, List.mem_flatMap, List.mem_map]
  exact ⟨st, hst, b, hb, rfl⟩

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

private theorem ctxOk : I.CtxOk I.X₀ where
  tcb := rfl
  order := rfl
  core := fun x hx v hv => I.vars_initDb x hx v hv
  avoid := fun v hv => by simp [State.avoidsVar, X₀, State.init, pres]; omega

/-- The proof starts at the formula. -/
private theorem run_init : I.Run I.X₀ ⟨[], 3, I.n⟩ (initDb I.F) :=
  I.run_start (X := I.X₀) (by simp [X₀, State.init, F])
    (fun x hx => by
      simp only [X₀, State.init, initDb, F, List.zipIdx_cons, List.zipIdx_nil, List.map_cons,
        List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp)
    (fun x hx v hv => I.vars_initDb x hx v hv)
    (by simp [lookup, X₀, State.init, initDb, F]) (by simp [lookup, X₀, State.init, initDb, F])


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

private theorem consistent_fixed {σ : ℕ → Bool} {K : List (Literal ℕ)}
    (h : Consistent σ (I.fixedLits ++ K)) :
    Consistent σ I.fixedLits := (consistent_append.1 h).1

/-- **The refutations of the last layer run** (equations (14)–(15) of the paper, against the
capacity or the profit constraint). -/
private theorem deadFinal_spec : ∀ (ts : List Node) (e : ProofLog) (db : List (ℕ × PBConstr)),
    I.Run I.X₀ e db → (∀ t ∈ ts, I.NodeOk I.n db e.var t) →
    ∃ db', I.Run I.X₀ (I.deadFinal e ts).1 db' ∧ Sub db db' ∧ I.DeadOk db' (I.deadFinal e ts).2 ∧
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
    · have hb := ht.bnd
      have hf' : ¬ (t.st.1 ≤ I.C ∧ t.st.2 + I.P ≤ tot I.p I.n) := by simpa [finalOk] using hf
      -- The addition, then the RUP step.
      have key : ∃ c, polEval db (if t.st.1 ≤ I.C then [PolOp.id t.pf, .id 2, .add]
            else [.id t.wf, .id 1, .add]) [] = some [c] ∧ (∀ v ∈ c.vars, v < e.var) ∧
          (c.terms.map termVar).Nodup ∧ ∀ σ, σ t.W = true → σ t.P = true → ¬ c.Holds σ := by
        split_ifs with hC
        · refine ⟨_, polEval_add ht.pf h.2.2.2.2.2, fun v hv => (vars_add hv).elim
            (I.vars_of_lookup h ht.pf v) (I.vars_of_lookup h h.2.2.2.2.2 v),
            nodup_termVar_normalize _, fun σ _ hP hA => ?_⟩
          have := final_dim (a := I.p) (pol := false) (m := I.n) (d := t.st.2) (z := t.P)
            ht.nP (G := I.profC) (nodup_range _ _ _) (fun σ => lhs_range σ _ _ _) hA hP
          exact hf' ⟨hC, by simpa [profC] using this⟩
        · refine ⟨_, polEval_add ht.wf h.2.2.2.2.1, fun v hv => (vars_add hv).elim
            (I.vars_of_lookup h ht.wf v) (I.vars_of_lookup h h.2.2.2.2.1 v),
            nodup_termVar_normalize _, fun σ hW _ hA => ?_⟩
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
          (nodup_termVar_normalize _) (fun σ hσ hc => ?_) ?_
        · rw [holds_normalize, holds_impl] at hc
          have := (holds_cS σ _ _).1 (hc (by simp [lit_of hσ (v := t.S) (b := true) (by simp)]))
          simp [Consistent, this]
        exact RupOk.id_conflict ((lookup_cons _ _ _ _).trans (ite_eq_left rfl)) hnd fun σ hσ hc =>
          hsem σ (lit_of hσ (by simp)) (lit_of hσ (by simp)) hc
      obtain ⟨h₂, s₂⟩ := Run.rup I h₁ hr (fun v hv => by
        obtain ⟨l, hl, rfl⟩ := vars_clause hv
        simp only [ProofLog.push]
        rcases List.mem_append.1 hl with hl | hl
        · have := I.vars_negD hl; have := h.2.2.2.1; omega
        · simp only [List.mem_singleton] at hl; subst hl; exact ht.S)
      rw [push_push] at h₂
      obtain ⟨db', h', s', hd', hall, hv⟩ := deadFinal_spec ts _ _ h₂
        (fun u hu => (hts u (List.mem_cons_of_mem _ hu)).mono I (s₁.trans s₂)
          (by simp [ProofLog.push]))
      have hfF : I.finalOk t.st = false := by simpa using hf
      refine ⟨db', by simpa [deadFinal, hfF] using h', s₁.trans (s₂.trans s'), ?_, ?_, ?_⟩
      · simp only [deadFinal, hfF, Bool.false_eq_true, ↓reduceIte, DeadOk, List.mem_cons,
          forall_eq_or_imp]
        refine ⟨s' _ _ ?_, hd'⟩
        simp [ProofLog.push, lookup_cons]
      · intro u hu hu'
        simp only [deadFinal, hfF, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
        rcases List.mem_cons.1 hu with rfl | hu
        · exact ⟨_, .inl rfl⟩
        · obtain ⟨k, hk⟩ := hall u hu hu'
          exact ⟨k, .inr hk⟩
      · simp only [deadFinal, hfF, Bool.false_eq_true, ↓reduceIte]
        simpa [ProofLog.push] using hv

/-- **The refutations of an earlier layer run**: a state all of whose targets are refuted is
refuted by RUP. -/
private theorem deadLayer_spec {i : ℕ} (hi : i < I.n) {A : List St} {dl : List (ℕ × ℕ)}
    {L' : List Node} :
    ∀ (os : List Out) (e : ProofLog) (db : List (ℕ × PBConstr)), I.Run I.X₀ e db →
    (∀ o ∈ os, I.OutOk exact i db e.var L' o) → I.DeadOk db dl →
    (∀ t ∈ L', t.st ∉ A → ∃ k, (t.S, k) ∈ dl) →
    ∃ db', I.Run I.X₀ (I.deadLayer i A dl e os).1 db' ∧ Sub db db' ∧
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
      have hdead : ∀ x ∈ o.tr, (x.tgt.S, dlook dl x.tgt.S) ∈ dl := by
        intro x hx
        obtain ⟨htm, -, -, hex, -⟩ := ho.tr x hx
        have hts := hex rfl
        refine dlook_mem (hL' _ htm fun hA => ?_)
        have hb : x.val ∈ vals (I.dom i) :=
          (List.mem_filter.1 (ho.vals ▸ List.mem_map_of_mem hx)).1
        simp only [List.any_eq_false, decide_eq_true_eq] at hany'
        exact hany' _ hb (hts ▸ hA)
      have hr : rup db (I.deadClause o.u.S)
          (.neg :: o.tr.map (fun x => .id (dlook dl x.tgt.S)) ++ [.id o.succ]) = true := by
        refine rup_clause ?_
        rw [negate_deadClause]
        have := RupOk.imps (db := db) (neg := (I.deadClause o.u.S).negate)
          (K₀ := I.fixedLits ++ [(o.u.S, true)]) (rest := [.id o.succ])
          (o.tr.map fun x => (Hint.id (dlook dl x.tgt.S), (x.tgt.S, false))) _ (fun l hl => hl)
          ?_ ?_
        · rw [List.map_map] at this; exact this
        · intro y hy
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
          refine ⟨_, hdl _ (hdead x hx), nodup_termVar_normalize _, fun σ hσ hc => ?_⟩
          have := I.holds_deadClause (I.consistent_fixed hσ) hc
          simp [this]
        · refine RupOk.id_conflict ho.succ (nodup_termVar_normalize _) fun σ hσ hc => ?_
          have := I.succ_false hi (o := o)
            (K := (o.tr.map fun x => (Hint.id (dlook dl x.tgt.S), (x.tgt.S, false))).map (·.2) ++
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
        (fun u hu => (hos u (List.mem_cons_of_mem _ hu)).mono I s₁ (by simp [ProofLog.push]))
        (hdl.mono I s₁) hL'
      refine ⟨db', by simpa [deadLayer, hany'] using h', s₁.trans s', ?_, ?_, ?_⟩
      · simp only [deadLayer, hany', Bool.false_eq_true, ↓reduceIte, DeadOk, List.mem_cons,
          forall_eq_or_imp]
        exact ⟨s' _ _ ((lookup_cons _ _ _ _).trans (ite_eq_left rfl)), hd'⟩
      · intro u hu hu'
        simp only [deadLayer, hany', Bool.false_eq_true, ↓reduceIte, List.mem_cons]
        rcases List.mem_cons.1 hu with rfl | hu
        · exact ⟨_, .inl rfl⟩
        · obtain ⟨k, hk⟩ := hall u hu hu'
          exact ⟨k, .inr hk⟩
      · simp only [deadLayer, hany', Bool.false_eq_true, ↓reduceIte]
        simpa [ProofLog.push] using hv

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
  lay : I.LayOk exact x.1.i db V x.1
  outs : x.1.outs.map (·.u) = x.1.nodes
  out : ∀ o ∈ x.1.outs, I.OutOk exact x.1.i db V next o
  alive : x.2.1 = I.alive (x.1.i + 1)
  dead : I.DeadOk db x.2.2
  cover : ∀ t ∈ next, t.st ∉ x.2.1 → ∃ k, (t.S, k) ∈ x.2.2

/-- **The backward pass runs.** -/
private theorem backAll_spec : ∀ (rs : List LayerRec) (e : ProofLog) (A : List St)
    (dl : List (ℕ × ℕ)) (j : ℕ) (L' : List Node) (db : List (ℕ × PBConstr)), I.Run I.X₀ e db →
    I.Chain exact db e.var j L' rs → j ≤ I.n → A = I.alive j → I.DeadOk db dl →
    (∀ t ∈ L', t.st ∉ A → ∃ k, (t.S, k) ∈ dl) →
    ∃ db', I.Run I.X₀ (I.backAll e A dl rs).1 db' ∧ Sub db db' ∧
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
      rw [I.alive_lt hi, hlay.lay, hA, hij]; rfl
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

private theorem tgt_tau {o : Out} {b : Bool} (hb : b ∈ o.tr.map (·.val)) :
    ∃ x ∈ o.tr, x.val = b ∧ o.tgt b = x.tgt ∧ o.tau b = x.id := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
  rcases hf : o.tr.find? (·.val == x.val) with _ | y
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
  have htr : ∀ o ∈ r.outs, ∃ y ∈ o.tr, y.val = b ∧ o.tgt b = y.tgt ∧ o.tau b = y.id :=
    fun o ho => tgt_tau (by
      rw [(hx.out o ho).vals]; exact List.mem_filter.2 ⟨hb, I.keep_exact _ _ _⟩)
  have hdead : ∀ o ∈ r.outs, lookup db (dlook dl (o.tgt b).S) =
      some (I.deadClause (o.tgt b).S).normalize := by
    intro o ho
    obtain ⟨y, hy, rfl, ht, -⟩ := htr o ho
    obtain ⟨hym, -, -, hyx, -⟩ := (hx.out o ho).tr y hy
    have hys := hyx rfl
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
    refine ⟨_, hdead o ho, nodup_termVar_normalize _, fun σ hσ hc => ?_⟩
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
    obtain ⟨-, -, -, -, hzl⟩ := (hx.out o ho).tr z hz
    refine ⟨_, by rw [hτ]; exact hzl, nodup_termVar_normalize _, fun σ hσ hc => ?_⟩
    rw [hzb] at hc
    have h3 := lit_of hσ (v := (o.tgt b).S) (b := false)
      (by simp only [List.mem_append, List.mem_map]; left; exact ⟨_, ⟨o, ho, rfl⟩, rfl⟩)
    rw [ht] at h3
    have h4 := lit_of hσ (v := r.i) (b := b) (by simp)
    cases hu : σ o.u.S
    · simp [hu]
    · simp [holds_trClause.1 hc hu h4] at h3
  · refine I.rupOk_alo hx.lay.alo (fun m hm => by simp [hm]) fun u hu => ?_
    rw [← hx.outs] at hu
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hu
    simp only [List.mem_append, List.mem_map]
    left
    exact ⟨_, ⟨o, ho, rfl⟩, rfl⟩

private theorem remLayer_spec {next : List Node} {r : LayerRec} {A : List St}
    {dl : List (ℕ × ℕ)} : ∀ (bs : List Bool) (e : ProofLog) (db : List (ℕ × PBConstr)),
    I.Run I.X₀ e db → I.BackAt db e.var next (r, A, dl) → (∀ b ∈ bs, b ∈ vals (I.dom r.i)) →
    ∃ db', I.Run I.X₀ (I.remLayer r A dl e bs).1 db' ∧ Sub db db' ∧
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
        ⟨hx.lt, hx.lay.mono I s₁ (by simp [ProofLog.push]), hx.outs,
          fun o ho => (hx.out o ho).mono I s₁ (by simp [ProofLog.push]), hx.alive,
          hx.dead.mono I s₁,
          hx.cover⟩ (fun b hb => hbs b (List.mem_cons_of_mem _ hb))
      simp only [remLayer, hall, ↓reduceIte]
      refine ⟨db', h', s₁.trans s', ?_, ?_, by simpa [ProofLog.push] using hv⟩
      · simp only [List.mem_cons, forall_eq_or_imp]
        refine ⟨⟨by simp, by simp, s' _ _ ((lookup_cons _ _ _ _).trans (ite_eq_left rfl))⟩,
          fun y hy => ?_⟩
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

private theorem remAll_spec : ∀ (xs : List (LayerRec × List St × List (ℕ × ℕ))) (e : ProofLog)
    (db : List (ℕ × PBConstr)), I.Run I.X₀ e db → (∀ x ∈ xs, ∃ next, I.BackAt db e.var next x) →
    ∃ db', I.Run I.X₀ (I.remAll e xs).1 db' ∧ Sub db db' ∧
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
private theorem emit_spec : ∃ db, I.Run I.X₀ I.emit.1 db ∧
    (∀ y ∈ I.emit.2, y.2.1 ∈ vals (I.dom y.1) ∧ y.1 < I.n ∧
      lookup db y.2.2 = some (I.remClause y.1 y.2.1).normalize) ∧
    (∀ j < I.n, ∀ b ∈ vals (I.dom j), (∀ st ∈ I.lay j, I.succSt j st b ∉ I.alive (j + 1)) →
      ∃ k, (j, b, k) ∈ I.emit.2) := by
  obtain ⟨db₂, h₂, -, rn, rs, hf, hrn, hc, hidx⟩ := I.forward_spec exact I.ctxOk I.run_init
  set f := I.forward exact with hfdef
  -- The backward pass.
  obtain ⟨db₃, h₃, s₃, hd₃, hall₃, hv₃⟩ := I.deadFinal_spec rn.nodes f.1 db₂ h₂ hrn.nodes
  have hA : (rn.nodes.map (·.st)).filter I.finalOk = I.alive I.n := by rw [alive_n, hrn.lay]; rfl
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
    rw [← hfdef, hf]
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
      change o.u.st ∈ I.layM exact x.1.i
      rw [← hnx.lay.lay]; exact List.mem_map_of_mem hu
    rw [hnx.alive, hxj]
    exact hall _ (hxj ▸ hst))
  exact ⟨k, hxj ▸ hk⟩

/-- **The propagator's proof runs and derives every removal clause.** -/
private theorem runTop_run : ∃ s, runTop I.F none (State.init I.F none (some I.pres))
    I.run.proof.steps = some s ∧
      ∀ j b, (j, b) ∈ I.run.removed → ∃ k, lookup s.db k = some (I.remClause j b).normalize := by
  obtain ⟨db, h, hys, -⟩ := I.emit_spec
  have h1 := h.1
  simp only [X₀] at h1
  refine ⟨state I.X₀ db I.emit.1.next, h1, fun j b hm => ?_⟩
  simp only [run, List.mem_map, Prod.mk.injEq] at hm
  obtain ⟨y, hy, rfl, rfl⟩ := hm
  exact ⟨y.2.2, (hys y hy).2.2⟩

/-- A constraint of the database over item variables holds at every solution of the formula. -/
private theorem holds_of_run {e : ProofLog} {db : List (ℕ × PBConstr)} (h : I.Run I.X₀ e db)
    {k : ℕ} {c : PBConstr} (hk : lookup db k = some c) (hv : ∀ x ∈ c.vars, x < I.n)
    {σ : ℕ → Bool} (hσ : ∀ c ∈ I.F, c.Holds σ) : c.Holds σ :=
  holds_of_runTop (s := state I.X₀ db e.next) h.1 rfl rfl rfl hk
    (fun x hx => by simpa [pres] using hv x hx) hσ

/-! ### The dynamic program is exact -/

/-- `∑_{i ≤ j < m} aⱼ [σ j = pol]`. -/
private def sfx (σ : ℕ → Bool) (a : ℕ → ℕ) (pol : Bool) (i m : ℕ) : ℕ :=
  ((List.range' i (m - i)).map fun j => bit (σ j) pol (a j)).sum

/-- The last state reached from the state `st` of layer `i` along `σ`. -/
private def finOf (σ : ℕ → Bool) (i : ℕ) (st : St) : St :=
  (st.1 + sfx σ I.w true i I.n, st.2 + sfx σ I.p false i I.n)

/-- `σ` takes values in the domains of the items `i ≤ j < m`. -/
private def Allowed (σ : ℕ → Bool) (i m : ℕ) : Prop := ∀ j, i ≤ j → j < m → σ j ∈ vals (I.dom j)

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
    simp only [lay, layM, List.mem_singleton]
    exact ⟨fun h => ⟨fun _ => false, fun j _ hj => absurd hj (Nat.not_lt_zero _),
      by simp [h, stOf, part]⟩, fun ⟨σ, _, h⟩ => by rw [← h]; simp [stOf, part]⟩
  | i + 1, st => by
    simp only [lay, layM, nextL_exact, List.mem_dedup, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨st₀, h₀, b, hb, rfl⟩
      obtain ⟨σ, hσ, rfl⟩ := (mem_lay_iff (i := i)).1 h₀
      refine ⟨Function.update σ i b, fun j _ hj => ?_, ?_⟩
      · by_cases hji : j = i
        · subst hji; simpa using hb
        · rw [Function.update_of_ne hji]; exact hσ j (Nat.zero_le _) (by omega)
      · rw [stOf_succ, Function.update_self]
        congr 1
        exact I.stOf_update σ i b
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
@[expose] public def profitBound (p : Fin n → ℕ) (P : ℕ) : PBConstr :=
  ⟨(List.finRange n).map fun i => (p i, (i.val, true)), P⟩

/-- **The knapsack constraint** `∑ wᵢ xᵢ ≤ C ∧ ∑ pᵢ xᵢ ≥ P`: the capacity constraint of the
certified knapsack and the profit constraint. -/
@[expose] public def propFormula (w p : Fin n → ℕ) (C P : ℕ) : List PBConstr :=
  [capacity w C, profitBound p P]

/-- **The knapsack propagator**: for the items of weights `w` and profits `p`, the capacity `C`,
the profit bound `P` and the domains `dom` (`none` for a free item, `some b` for an item fixed to
`b`), the values removed and a kernel proof deriving `D ⇒ xᵢ ≠ b` for each removed value `b` of
item `i`, `D` the domain literals. -/
public def propagate (w p : Fin n → ℕ) (C P : ℕ) (dom : Fin n → Option Bool) : Propagation :=
  (Inst.ofFin w p C P dom).run

/-- The value `b` of item `j` is **supported** by the knapsack constraint under the domains:
some set of items that agrees with the domains, contains `j` exactly when `b`, weighs at most `C`
and earns at least `P`. -/
@[expose] public def Supported (w p : Fin n → ℕ) (C P : ℕ) (dom : Fin n → Option Bool)
    (j : Fin n) (b : Bool) : Prop :=
  ∃ S : Finset (Fin n), (∀ i c, dom i = some c → (i ∈ S ↔ c = true)) ∧ (j ∈ S ↔ b = true) ∧
    ∑ i ∈ S, w i ≤ C ∧ P ≤ ∑ i ∈ S, p i

/-- **The profit constraint holds exactly when the items taken earn at least `P`.** -/
public theorem holds_profitBound_iff (p : Fin n → ℕ) (P : ℕ) (σ : ℕ → Bool) :
    (profitBound p P).Holds σ ↔ P ≤ ∑ i ∈ chosen n σ, p i := by
  rw [Holds, profitBound, lhs, List.map_map, ← Fin.sum_univ_def, chosen, Finset.sum_filter]
  refine iff_of_eq (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
  cases h : σ i.val <;> simp [termVal, h]

private theorem F_ofFin (w p : Fin n → ℕ) (C P : ℕ) (dom : Fin n → Option Bool) :
    (Inst.ofFin w p C P dom).F = propFormula w p C P := by
  have h2 : (List.finRange n).map (fun i => (p i, (i.val, true))) =
      (List.range n).map fun j => ((Inst.ofFin w p C P dom).p j, (j, true)) := by
    rw [← map_finRange]; exact List.map_congr_left fun i _ => by simp [Inst.ofFin]
  simp only [Inst.F, propFormula, Inst.capC_ofFin, Inst.profC, capacity, profitBound, h2]
  rfl

/-- **The removal clause** `D ⇒ xⱼ ≠ b` of the value `b` of item `j`, `D` the literals that the
domains `dom` fix: the clause `⋁_{dom i = some c} xᵢ ≠ c ∨ xⱼ ≠ b`. -/
@[expose] public def remClause (dom : Fin n → Option Bool) (j : Fin n) (b : Bool) : PBConstr :=
  ⟨(((List.finRange n).filterMap fun i => (dom i).map fun c => (i.val, !c)) ++
    [(j.val, !b)]).map ((1, ·)), 1⟩

/-- **The removal clause holds exactly when** an assignment agreeing with the domains does not
give item `j` the value `b`. -/
public theorem holds_remClause_iff (dom : Fin n → Option Bool) (j : Fin n) (b : Bool)
    (σ : ℕ → Bool) :
    (remClause dom j b).Holds σ ↔ ((∀ i c, dom i = some c → σ i = c) → σ j ≠ b) := by
  rw [show remClause dom j b = clause _ from rfl, Inst.holds_clause]
  simp only [List.mem_append, List.mem_filterMap, List.mem_finRange, true_and,
    Option.map_eq_some_iff, List.mem_singleton, Literal.eval_eq_true_iff]
  constructor
  · rintro ⟨l, hl | rfl, hev⟩ hd hj
    · obtain ⟨i, c, hc, rfl⟩ := hl
      simp [hd i c hc] at hev
    · simp [hj] at hev
  · intro h
    by_contra hne
    push Not at hne
    refine h (fun i c hc => ?_) ?_
    · have := hne (i.val, !c) (.inl ⟨i, c, hc, rfl⟩)
      simpa using this
    · simpa using hne (j.val, !b) (.inr rfl)

private theorem remClause_ofFin (w p : Fin n → ℕ) (C P : ℕ) (dom : Fin n → Option Bool)
    (j : Fin n) (b : Bool) : (Inst.ofFin w p C P dom).remClause j.val b = remClause dom j b := by
  have key : ((List.range n).filterMap fun k =>
      (if h : k < n then dom ⟨k, h⟩ else none).map fun c => (k, c)).map Std.Sat.Literal.negate =
      (List.finRange n).filterMap fun i => (dom i).map fun c => (i.val, !c) := by
    rw [← List.map_coe_finRange_eq_range, List.filterMap_map, List.map_filterMap]
    refine List.filterMap_congr fun i _ => ?_
    rcases h : dom i with _ | c <;> simp [i.isLt, h, Std.Sat.Literal.negate]
  simp only [Inst.remClause, Inst.negD, Inst.fixedLits, Inst.ofFin, remClause, clause, key]

/-- **The propagator's proof runs, and derives the removal clause** `D ⇒ xⱼ ≠ b` of every removed
value `b` of item `j`: the checker, run on the knapsack constraint with the item variables
preserved, reaches a database holding the normalized removal clause. -/
public theorem runTop_propagate (w p : Fin n → ℕ) (C P : ℕ) (dom : Fin n → Option Bool) :
    ∃ s, runTop (propFormula w p C P) none
        (State.init (propFormula w p C P) none (some (List.range n)))
        (propagate w p C P dom).proof.steps = some s ∧
      ∀ j b, (j.val, b) ∈ (propagate w p C P dom).removed →
        ∃ k, lookup s.db k = some (remClause dom j b).normalize := by
  obtain ⟨s, hs, hrem⟩ := (Inst.ofFin w p C P dom).runTop_run
  rw [F_ofFin] at hs
  refine ⟨s, hs, fun j b hm => ?_⟩
  rw [← remClause_ofFin w p C P]
  exact hrem j.val b hm

/-- **The checker accepts the propagator's proof**, for every knapsack constraint and every
domains, the item variables preserved. -/
public theorem checkRed_propagate (w p : Fin n → ℕ) (C P : ℕ) (dom : Fin n → Option Bool) :
    checkRed (propFormula w p C P) none (propagate w p C P dom).proof (some (List.range n)) =
      true := by
  obtain ⟨s, hs, -⟩ := runTop_propagate w p C P dom
  rw [checkRed, hs]
  rfl


private theorem supportedN_iff (w p : Fin n → ℕ) (C P : ℕ) (dom : Fin n → Option Bool)
    (j : Fin n) (b : Bool) :
    (Inst.ofFin w p C P dom).SupportedN j.val b ↔ Supported w p C P dom j b := by
  have key : ∀ σ : ℕ → Bool, (Inst.ofFin w p C P dom).finalOk
      ((Inst.ofFin w p C P dom).stOf σ (Inst.ofFin w p C P dom).n) = true ↔
      ∑ i ∈ chosen n σ, w i ≤ C ∧ P ≤ ∑ i ∈ chosen n σ, p i := by
    intro σ
    have hw' := Inst.part_ofFin σ w
    have hp' := Inst.part_ofFin σ p
    have ht := Inst.tot_ofFin p
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
public theorem mem_removed_iff (w p : Fin n → ℕ) (C P : ℕ) (dom : Fin n → Option Bool) (j : Fin n)
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
public theorem lt_of_mem_removed {w p : Fin n → ℕ} {C P : ℕ} {dom : Fin n → Option Bool} {i : ℕ}
    {b : Bool} (h : (i, b) ∈ (propagate w p C P dom).removed) : i < n :=
  ((Inst.ofFin w p C P dom).mem_run_removed_iff.1 h).1

end Cslib.Logic.PL.VeriPB.Knapsack
