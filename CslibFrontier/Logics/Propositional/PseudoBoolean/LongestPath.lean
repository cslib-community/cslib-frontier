/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.DynamicProgramming
public import Cslib.Foundations.Relation.Defs
import CslibFrontier.Algorithms.Lean.DFS.TopologicalSort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Certified longest paths in a DAG: a dynamic program that writes a VeriPB proof

A directed multigraph has vertices `Fin m` and edges `Fin n`, edge `e` going from `src e` to
`dst e` with length `c e`. A *walk* from `s` to `t` is a list of edges, each starting where the
last one ended (`Cslib.Logic.PL.VeriPB.LongestPath.IsWalk`), and its length is the sum of the
lengths of its edges. In an acyclic graph every walk is a path, and the longest-path problem asks
for the largest length of a walk from `s` to `t`. This file writes it as a pseudo-Boolean problem,
and gives a dynamic program that writes, with its answer, a proof in the kernel format of VeriPB
that the answer is optimal, or that there is no walk, after §3.2 of [Demirović, McCreesh,
McIlree, Nordström, Oertel and Sidorov][DemirovicMcCreeshMcIlreeNordstromOertelSidorov2024] and the
DAG solver of its supplement. The proof is checked by `Cslib.Logic.PL.VeriPB.checkRed`; nothing
about the dynamic program is proved.

**The encoding.** Edge `e` is the variable `e`. The formula is flow conservation
(`Cslib.Logic.PL.VeriPB.LongestPath.formula`): at each vertex `v`, the edges chosen out of `v`
minus those into `v` number `1` at `s`, `-1` at `t` and `0` elsewhere (all `0` if `s = t`), as
two inequalities. The objective, to be minimized, is the negated length
`Cslib.Logic.PL.VeriPB.negProfit c`. In an acyclic graph the solutions of the formula choose
exactly the edge sets of the walks from `s` to `t`: a walk repeats no edge, and a set of edges that
conserves flow is followed from `s` until `t`, after which the remaining edges conserve flow
everywhere and so, without a cycle, are none. So the formula and objective encode the problem
(`Cslib.Logic.PL.VeriPB.LongestPath.encodes`). Acyclicity is a hypothesis of that theorem, about
the graph; it is not checked by the proof.

**The dynamic program** (`Cslib.Logic.PL.VeriPB.LongestPath.certify`). It orders the vertices by
`Cslib.Algorithms.Lean.DFS.topologicalSort`, and computes in that order the length `D v` of a
longest walk from `s` to each vertex `v` that has one, taking the best of the incoming edges. The
proof does not trust the order. With `L_k` the first `k` vertices of the order, it adds up the
conservation constraints of the vertices of `L_k`, one at a time, into the *cut constraint*
`K_k`: the edges from `L_k` to the other vertices number at most `[s ∈ L_k] - [t ∈ L_k]` more than
those back into `L_k`. In a topological order there are no edges back, so `K_k` says that at most
one edge leaves `L_k` while `s` is in it and `t` is not, and none once both are. A vertex is
*live* if it has a walk from `s` and comes no later than `t`. For a live vertex `v` the proof
reifies, by `Cslib.Logic.PL.VeriPB.reify`, the state `Q_v ⇔ ∑ c e x_e ≤ D v` over the edges `e`
into `L_{k+1}`, for `v` the `k`-th vertex, and derives:
* `Q_s` as a unit, the edges into the vertices before `s` being unused;
* for each edge `e` from a live `u` into `v`, the transition `x_e ⇒ Q_v`: the forward half of
  `Q_u` plus the backward half of `Q_v` is closed by RUP from `x_e ⇒ Q_u` and the cut constraints
  between `u` and `v`, which rule out every other edge into the vertices between them;
* for each edge `f` out of `v` to a live vertex, `x_f ⇒ Q_v`, by RUP from the transitions into `v`
  and the conservation constraint at `v`: one option per incoming edge;
* `Q_t` as a unit, likewise.
Each edge out of a vertex that is not live is refuted, `¬x_f`, by RUP from the refutations of the
edges into it and its conservation constraint, or, out of a live vertex past `t`, by the cut
constraint after `t`. The proof logs a longest walk with `soli`, which adds the improving
constraint `∑ c e x_e ≥ D t + 1`; the forward half of `Q_t` plus that constraint is refuted by
`Q_t` and the refutations of the edges past `t`, and the conclusion is `BOUNDS -D t : q -D t`. If
`t` has no walk from `s`, the edges into it are refuted and its conservation constraint is
contradicted, and the conclusion is `BOUNDS INF : q INF`.

If the order were not topological, or the graph had a cycle, the cut constraints would keep the
edges back and the derivations would fail: the proof process checks the order, as the paper
notes. That the checker accepts the proof is not proved, nor that the claimed optimum is right;
`Cslib.Logic.PL.VeriPB.LongestPath.isGreatest_of_checkRed_certify` turns acceptance into
optimality, or into the absence of a walk.

## Main definitions

* `Cslib.Logic.PL.VeriPB.LongestPath.IsWalk`: a walk, as a list of edges.
* `Cslib.Logic.PL.VeriPB.LongestPath.formula`: the flow-conservation encoding.
* `Cslib.Logic.PL.VeriPB.LongestPath.certify`: the proof-logging dynamic program.

## Main results

* `Cslib.Logic.PL.VeriPB.LongestPath.forall_holds_formula_iff`: the solutions of the formula are
  the flows of value `1` from `s` to `t`.
* `Cslib.Logic.PL.VeriPB.LongestPath.encodes`: in an acyclic graph, the encoding is correct.
* `Cslib.Logic.PL.VeriPB.LongestPath.isGreatest_of_checkRed_certify`: if the checker accepts the
  proof of the dynamic program, its answer is the longest length of a walk, or there is none.

## References

* [E. Demirović, C. McCreesh, M. J. McIlree, J. Nordström, A. Oertel, K. Sidorov, *Pseudo-Boolean
  Reasoning About States and Transitions to Certify Dynamic Programming and Decision Diagram
  Algorithms*][DemirovicMcCreeshMcIlreeNordstromOertelSidorov2024]
-/

public section

namespace Cslib.Logic.PL.VeriPB.LongestPath

open Relation PBConstr

variable {m n : ℕ} {src dst : Fin n → Fin m}

/-! ### Walks and the encoding -/

/-- **A walk from `u` to `v`**: a list of edges, the first starting at `u`, each starting where the
previous one ends, and the last ending at `v`; the empty walk from `u` to `u`. -/
@[expose]
def IsWalk (src dst : Fin n → Fin m) : Fin m → List (Fin n) → Fin m → Prop
  | u, [], v => u = v
  | u, e :: l, v => src e = u ∧ IsWalk src dst (dst e) l v

/-- **The flow out of `v` of one unit sent from `s` to `t`**: `1` at `s`, `-1` at `t`, and `0`
elsewhere or if `s = t`. The edge `e` carries one unit from `src e` to `dst e`, so its coefficient
in the flow out of `v` is `unitFlow (src e) (dst e) v`. -/
@[expose]
def unitFlow (s t v : Fin m) : ℤ := (if s = v then 1 else 0) - (if t = v then 1 else 0)

/-- The flow out of the vertex `v`, as a linear form over the edge variables. -/
@[expose]
def flow (src dst : Fin n → Fin m) (v : Fin m) : List (ℕ × ℤ) :=
  (List.finRange n).map fun e => (e.val, unitFlow (src e) (dst e) v)

/-- **The longest-path formula**: flow conservation from `s` to `t`. For each vertex `v`, in
order, the flow out of `v` is at least `unitFlow s t v`, and at most it. -/
@[expose]
def formula (src dst : Fin n → Fin m) (s t : Fin m) : List PBConstr :=
  (List.finRange m).flatMap fun v =>
    [fromLinear (flow src dst v) (unitFlow s t v),
      fromLinear ((flow src dst v).map fun a => (a.1, -a.2)) (-unitFlow s t v)]

private theorem unitFlow_add (a b c w : Fin m) :
    unitFlow a b w + unitFlow b c w = unitFlow a c w := by
  simp only [unitFlow]; ring

private theorem unitFlow_self (a w : Fin m) : unitFlow a a w = 0 := by simp [unitFlow]

/-- An edge of positive coefficient in the flow out of `u` leaves `u`. -/
private theorem eq_of_unitFlow_pos {a b u : Fin m} (h : 0 < unitFlow a b u) : a = u := by
  unfold unitFlow at h
  by_contra hne
  simp only [hne, ↓reduceIte] at h
  split_ifs at h <;> omega

private theorem linVal_flow (σ : ℕ → Bool) (v : Fin m) :
    linVal σ (flow src dst v) = ∑ e ∈ chosen n σ, unitFlow (src e) (dst e) v := by
  rw [linVal, flow, List.map_map, ← Fin.sum_univ_def, chosen, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  cases h : σ e.val <;> simp [h]

/-- **The solutions of the formula are the flows of one unit from `s` to `t`**: an assignment
satisfies it exactly when, at every vertex `v`, the edges it chooses carry the flow
`unitFlow s t v` out of `v`. -/
theorem forall_holds_formula_iff (s t : Fin m) (σ : ℕ → Bool) :
    (∀ c ∈ formula src dst s t, c.Holds σ) ↔
      ∀ v, ∑ e ∈ chosen n σ, unitFlow (src e) (dst e) v = unitFlow s t v := by
  simp only [formula, List.forall_mem_flatMap, List.mem_finRange, forall_const,
    List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
    holds_fromLinear_iff, linVal_map_neg, linVal_flow]
  exact forall_congr' fun _ => by omega

/-! ### Walks and flows in an acyclic graph -/

private theorem reflTransGen_of_mem {u v : Fin m} {l : List (Fin n)} (hl : IsWalk src dst u l v)
    {f : Fin n} (hf : f ∈ l) : ReflTransGen (fun u v => ∃ e, src e = u ∧ dst e = v) u (src f) := by
  induction l generalizing u with
  | nil => simp at hf
  | cons e l ih =>
    obtain ⟨rfl, hl⟩ := hl
    rcases List.mem_cons.1 hf with rfl | hf
    · exact .refl
    · exact ReflTransGen.head ⟨e, rfl, rfl⟩ (ih hl hf)

/-- A walk in an acyclic graph repeats no edge. -/
private theorem nodup_of_isWalk (hG : Acyclic fun u v => ∃ e, src e = u ∧ dst e = v)
    {u v : Fin m} {l : List (Fin n)} (hl : IsWalk src dst u l v) : l.Nodup := by
  induction l generalizing u with
  | nil => exact List.nodup_nil
  | cons e l ih =>
    obtain ⟨rfl, hl⟩ := hl
    refine List.nodup_cons.2 ⟨fun he => hG.irrefl (src e) ?_, ih hl⟩
    exact TransGen.head' ⟨e, rfl, rfl⟩ (reflTransGen_of_mem hl he)

/-- A walk without repeated edges carries one unit from its start to its end. -/
private theorem sum_unitFlow_of_isWalk {u v : Fin m} {l : List (Fin n)}
    (hl : IsWalk src dst u l v) (hnd : l.Nodup) (w : Fin m) :
    ∑ e ∈ l.toFinset, unitFlow (src e) (dst e) w = unitFlow u v w := by
  induction l generalizing u with
  | nil => cases hl; simp [unitFlow_self]
  | cons e l ih =>
    obtain ⟨rfl, hl⟩ := hl
    rw [List.toFinset_cons, Finset.sum_insert (by simpa using (List.nodup_cons.1 hnd).1),
      ih hl (List.nodup_cons.1 hnd).2, unitFlow_add]

/-- In an acyclic graph, a set of edges that conserves flow at every vertex is empty. -/
private theorem eq_empty_of_circulation (hG : Acyclic fun u v => ∃ e, src e = u ∧ dst e = v)
    {S : Finset (Fin n)} (hS : ∀ w, ∑ e ∈ S, unitFlow (src e) (dst e) w = 0) : S = ∅ := by
  by_contra hne
  let r : Fin m → Fin m → Prop := fun a b => TransGen (fun u v => ∃ e, src e = u ∧ dst e = v) b a
  have : IsTrans (Fin m) r := ⟨fun _ _ _ hab hbc => hbc.trans hab⟩
  have : Std.Irrefl r := ⟨fun a h => hG.irrefl a h⟩
  obtain ⟨a, ha, hmin⟩ := (Finite.wellFounded_of_trans_of_irrefl r).has_min
    (S.image dst : Set (Fin m)) (by simpa [Finset.nonempty_iff_ne_empty] using hne)
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 ha
  have hloop : src e ≠ dst e := fun h => hG.irrefl (dst e) (.single ⟨e, h, rfl⟩)
  have hfe : unitFlow (src e) (dst e) (dst e) = -1 := by simp [unitFlow, hloop]
  obtain ⟨f, hf, hpos⟩ : ∃ f ∈ S.erase e, 0 < unitFlow (src f) (dst f) (dst e) := by
    by_contra! hneg
    have h₁ := Finset.sum_nonpos hneg
    have h₂ := hS (dst e)
    rw [← Finset.sum_erase_add _ _ he, hfe] at h₂
    omega
  exact hmin (dst f) (Finset.mem_image_of_mem _ (Finset.mem_of_mem_erase hf))
    (.single ⟨f, eq_of_unitFlow_pos hpos, rfl⟩)

/-- In an acyclic graph, a set of edges that carries one unit from `u` to `t` is the set of edges
of a walk from `u` to `t`. -/
private theorem exists_isWalk (hG : Acyclic fun u v => ∃ e, src e = u ∧ dst e = v)
    {t : Fin m} (u : Fin m) (S : Finset (Fin n))
    (hS : ∀ w, ∑ e ∈ S, unitFlow (src e) (dst e) w = unitFlow u t w) :
    ∃ l, IsWalk src dst u l t ∧ l.toFinset = S := by
  by_cases hut : u = t
  · subst hut
    exact ⟨[], rfl, (eq_empty_of_circulation hG fun w => by rw [hS w, unitFlow_self]).symm⟩
  obtain ⟨f, hf, hpos⟩ : ∃ f ∈ S, 0 < unitFlow (src f) (dst f) u := by
    by_contra! hneg
    have h₁ := Finset.sum_nonpos hneg
    have h₂ := hS u
    have h₃ : unitFlow u t u = 1 := by simp [unitFlow, Ne.symm hut]
    omega
  have hsrc := eq_of_unitFlow_pos hpos
  obtain ⟨l, hl, hlS⟩ := exists_isWalk hG (dst f) (S.erase f) fun w => by
    have h₁ := hS w
    rw [← Finset.sum_erase_add _ _ hf, hsrc, ← unitFlow_add u (dst f) t w] at h₁
    linarith
  exact ⟨f :: l, ⟨hsrc, hl⟩, by rw [List.toFinset_cons, hlS, Finset.insert_erase hf]⟩
termination_by S.card
decreasing_by exact Finset.card_erase_lt_of_mem hf

/-- **The longest-path encoding is correct in an acyclic graph**: flow conservation from `s` to `t`
and the negated length encode the maximization of the length over the walks from `s` to `t`. -/
theorem encodes (hG : Acyclic fun u v => ∃ e, src e = u ∧ dst e = v) (c : Fin n → ℕ)
    (s t : Fin m) :
    Encodes (formula src dst s t) (negProfit c) {l | IsWalk src dst s l t}
      fun l => ((l.map c).sum : ℤ) where
  exists_eval l hl := by
    have hnd := nodup_of_isWalk hG hl
    obtain ⟨σ, hσ⟩ := exists_chosen_eq l.toFinset
    refine ⟨σ, (forall_holds_formula_iff s t σ).2 fun w => ?_, ?_⟩
    · rw [hσ]; exact sum_unitFlow_of_isWalk hl hnd w
    · rw [eval_negProfit, hσ, List.sum_toFinset _ hnd, Nat.cast_list_sum, List.map_map]; rfl
  exists_val σ hσ := by
    obtain ⟨l, hl, hlS⟩ := exists_isWalk hG s (chosen n σ) ((forall_holds_formula_iff s t σ).1 hσ)
    refine ⟨l, hl, ?_⟩
    rw [eval_negProfit, neg_neg, ← hlS, List.sum_toFinset _ (nodup_of_isWalk hG hl),
      Nat.cast_list_sum, List.map_map]
    rfl

/-! ### The proof-logging dynamic program -/

/-- The fixed data of a run: the instance, the position of each vertex in the order and the
position of `t`, and the longest walk found to each vertex, as its length and its
edges. -/
private structure Ctx (m n : ℕ) where
  src : Fin n → Fin m
  dst : Fin n → Fin m
  c : Fin n → ℕ
  s : Fin m
  t : Fin m
  pos : List ℕ
  posT : ℕ
  dist : List (Option (ℕ × List ℕ))

/-- The position of a vertex in the order. -/
private def Ctx.at (C : Ctx m n) (v : Fin m) : ℕ := C.pos.getD v.val 0

/-- The edges into `v`, loops excepted. -/
private def Ctx.ins (C : Ctx m n) (v : Fin m) : List (Fin n) :=
  (List.finRange n).filter fun e => C.dst e = v && C.src e != v

/-- The edges out of `v`, loops excepted. -/
private def Ctx.outs (C : Ctx m n) (v : Fin m) : List (Fin n) :=
  (List.finRange n).filter fun e => C.src e = v && C.dst e != v

/-- `v` has a walk from `s` and comes no later than `t`. -/
private def Ctx.live (C : Ctx m n) (v : Fin m) : Bool :=
  (C.dist.getD v.val none).isSome && decide (C.at v ≤ C.posT)

/-- The number of the constraint "the flow into `v` is at least `-unitFlow s t v`". -/
private def inId (v : Fin m) : ℕ := 2 * v.val + 2

/-- The unit clause `¬x_e`. -/
private def offClause (e : Fin n) : PBConstr := Clause.toPB [(e.val, false)]

/-- The proof being written and what it has derived: the numbers of the cut constraints `K_1, …`,
for each edge the number of a constraint refuting it (`¬x_e`, or `x_e ⇒ Q_{dst e}`), for each
edge the number of `x_e ⇒ Q_{src e}`, for each vertex its state variable `Q` and the numbers of
its two halves, and the number of the last unit `Q`. -/
private structure Run where
  log : ProofLog
  cuts : List ℕ
  kill : List ℕ
  vis : List ℕ
  q : List (ℕ × ℕ × ℕ)
  unit : ℕ

/-- Process a live vertex `v` at position `k`: reify `Q_v`, derive the transitions into it, the
implications `x_f ⇒ Q_v` for the edges `f` out of it, and the unit `Q_v` for `v = s` or `v = t`. -/
private def live (C : Ctx m n) (X : Run) (k : ℕ) (v : Fin m) (d : ℕ) : Run :=
  let pre := (List.finRange n).filter fun e => decide (C.at (C.dst e) ≤ k) && C.c e != 0
  let (e, z, fw, bw) := X.log.reify
    ⟨pre.map fun f => (C.c f, (f.val, false)), (pre.map C.c).sum - d⟩
  let X := { X with log := e, q := X.q.set v.val (z, fw, bw) }
  let killed := fun (X : Run) => (C.ins v).map fun f => Hint.id (X.kill.getD f.val 0)
  if v = C.s then
    let (e, u) := X.log.rup (Clause.toPB [(z, true)])
      (.neg :: pre.map (fun f => .id (X.kill.getD f.val 0)) ++ [.id bw])
    { X with log := e, vis := (C.outs v).foldl (fun V f => V.set f.val u) X.vis, unit := u }
  else
    -- The transitions `x_e ⇒ Q_v` for the edges `e` from a live vertex.
    let X := (C.ins v).foldl (fun X ee =>
      if C.live (C.src ee) then
        let ku := C.at (C.src ee)
        let (_, fu, _) := X.q.getD (C.src ee).val (0, 0, 0)
        let (e, A) := X.log.pol [.id fu, .id bw, .add]
        let (e, τ) := e.rup (Clause.toPB [(ee.val, false), (z, true)])
          (.neg :: .id (X.vis.getD ee.val 0) ::
            ((List.range (k - ku)).map fun j => .id (X.cuts.getD (ku + j) 0)) ++ [.id A])
        { X with log := e.deld [A], kill := X.kill.set ee.val τ }
      else X) X
    -- The implications `x_f ⇒ Q_v` for the edges `f` to a live vertex.
    let X := (C.outs v).foldl (fun X f =>
      if C.at (C.dst f) ≤ C.posT then
        let (e, τ) := X.log.rup (Clause.toPB [(f.val, false), (z, true)])
          (.neg :: killed X ++ [.id (inId v)])
        { X with log := e, vis := X.vis.set f.val τ }
      else X) X
    if v = C.t then
      let (e, u) := X.log.rup (Clause.toPB [(z, true)]) (.neg :: killed X ++ [.id (inId v)])
      { X with log := e, unit := u }
    else X

/-- Process a vertex `v` that is not live: refute the edges into it from a live vertex by the cut
constraint after `t`, if `cut`, and the edges out of it by its conservation constraint. -/
private def dead (C : Ctx m n) (cut : Bool) (X : Run) (v : Fin m) : Run :=
  let X := if cut then (C.ins v).foldl (fun X ee =>
    if X.kill.getD ee.val 0 = 0 then
      let (e, u) := X.log.rup (offClause ee) [.neg, .id (X.cuts.getD C.posT 0)]
      { X with log := e, kill := X.kill.set ee.val u }
    else X) X else X
  (C.outs v).foldl (fun X f =>
    let (e, u) := X.log.rup (offClause f)
      (.neg :: (C.ins v).map (fun g => .id (X.kill.getD g.val 0)) ++ [.id (inId v)])
    { X with log := e, kill := X.kill.set f.val u }) X

/-- Process the next vertex `v` of the order when `t` has a walk from `s`: extend the cut
constraint by `v`, then process `v`. -/
private def visit (C : Ctx m n) (X : Run) (v : Fin m) : Run :=
  let k := X.cuts.length
  let (e, K) := if k = 0 then (X.log, inId v)
    else X.log.pol [.id (X.cuts.getD (k - 1) 0), .id (inId v), .add]
  let X := { X with log := e, cuts := X.cuts ++ [K] }
  match C.dist.getD v.val none with
  | some (d, _) => if k ≤ C.posT then live C X k v d else dead C true X v
  | none => dead C true X v

/-- The longest walks from `s` to each vertex, computed in the order `ord`: for each vertex, its
length and its edges, or none. -/
private def longest (src dst : Fin n → Fin m) (c : Fin n → ℕ) (s : Fin m) (ord : List (Fin m)) :
    List (Option (ℕ × List ℕ)) :=
  ord.foldl (fun D v =>
    if v = s then D.set v.val (some (0, [])) else
      D.set v.val (((List.finRange n).filter fun e => dst e = v && src e != v).foldl
        (fun b e => match D.getD (src e).val none, b with
          | some (d, p), some (d', _) =>
            if d' < d + c e then some (d + c e, e.val :: p) else b
          | some (d, p), none => some (d + c e, e.val :: p)
          | none, _ => b) none)) (List.replicate m none)

/-- The conclusion `BOUNDS -k : q -k` for the optimum `k`, and `BOUNDS INF : q INF` for none. -/
private def boundsOf : Option ℕ → ℕ → Conclusion
  | some k, q => .bounds (some (-k)) q (some (-k)) none
  | none, q => .bounds none q none none

/-- The tail of a run: the proof, the number of its final contradiction, the claimed optimum and
the steps before the proof. -/
private structure Tail where
  log : ProofLog
  q : ℕ
  opt : Option ℕ
  pre : List TopStep

/-- **The proof-logging dynamic program** for the graph of edges `e` from `src e` to `dst e` of
lengths `c e` and the vertices `s` and `t`. It returns a claimed optimum, the length of a longest
walk from `s` to `t` or none, and a candidate VeriPB proof for the flow-conservation formula and
the negated length, with the conclusion `BOUNDS -optimum : q -optimum`, or `BOUNDS INF : q INF`
for none. No theorem says that the checker accepts the proof or that the claimed optimum is right;
when `Cslib.Logic.PL.VeriPB.checkRed` accepts the proof on an acyclic instance, the claimed optimum
is the optimum there, or there is no walk
(`Cslib.Logic.PL.VeriPB.LongestPath.isGreatest_of_checkRed_certify`). -/
def certify (src dst : Fin n → Fin m) (c : Fin n → ℕ) (s t : Fin m) : Certificate (Option ℕ) :=
  let ord := Algorithms.Lean.DFS.topologicalSort
    (fun u => ((List.finRange n).filter fun e => src e = u).map dst) (List.finRange m)
  let pos := (List.finRange m).map ord.idxOf
  let dist := longest src dst c s ord
  let C : Ctx m n := ⟨src, dst, c, s, t, pos, pos.getD t.val 0, dist⟩
  let T : Tail := match dist.getD t.val none with
    | some (k, path) =>
      -- The solution is logged first, so its improving constraint is `2 m + 1`.
      let X := ord.foldl (visit C)
        ⟨⟨[], 2 * m + 2, n⟩, [], List.replicate n 0, List.replicate n 0,
          List.replicate m (0, 0, 0), 0⟩
      let (_, fw, _) := X.q.getD t.val (0, 0, 0)
      let (e, r) := X.log.pol [.id fw, .id (2 * m + 1), .add]
      let late := (List.finRange n).filter fun e => decide (C.posT < C.at (dst e)) && c e != 0
      let (e, q) := e.rup ⟨[], 1⟩
        (.id X.unit :: late.map (fun f => .id (X.kill.getD f.val 0)) ++ [.id r])
      ⟨e, q, some k,
        [.soli ((List.finRange n).map fun e => (e.val, decide (e.val ∈ path)))]⟩
    | none =>
      let X := ord.foldl (fun X v => if (dist.getD v.val none).isSome then X else dead C false X v)
        ⟨⟨[], 2 * m + 1, n⟩, [], List.replicate n 0, [], [], 0⟩
      let (e, q) := X.log.rup ⟨[], 1⟩
        ((C.ins t).map (fun f => .id (X.kill.getD f.val 0)) ++ [.id (inId t)])
      ⟨e, q, none, []⟩
  ⟨T.opt, T.log.proof T.pre (boundsOf T.opt T.q)⟩

/-- **If the checker accepts the proof of the dynamic program on an acyclic graph, its answer is
right**: a claimed optimum `k` is the largest length of a walk from `s` to `t`, and a claimed none
means that there is no such walk. -/
theorem isGreatest_of_checkRed_certify {c : Fin n → ℕ} {s t : Fin m}
    (hG : Acyclic fun u v => ∃ e, src e = u ∧ dst e = v)
    (h : checkRed (formula src dst s t) (some (negProfit c)) (certify src dst c s t).proof =
      true) :
    (∀ k, (certify src dst c s t).optimum = some k →
      IsGreatest ((fun l => (l.map c).sum) '' {l | IsWalk src dst s l t}) k) ∧
    ((certify src dst c s t).optimum = none → ∀ l, ¬ IsWalk src dst s l t) := by
  obtain ⟨q, hc⟩ : ∃ q, (certify src dst c s t).proof.conclusion =
      boundsOf (certify src dst c s t).optimum q := ⟨_, rfl⟩
  refine ⟨fun k hk => ?_, fun hk l hl => ?_⟩
  · rw [hk] at hc
    exact (encodes hG c s t).isGreatest_natCast_of_checkRed (fun _ => rfl) h hc
  · rw [hk] at hc
    exact Set.eq_empty_iff_forall_notMem.1 ((encodes hG c s t).eq_empty_of_checkRed h hc) l hl

end Cslib.Logic.PL.VeriPB.LongestPath

end
