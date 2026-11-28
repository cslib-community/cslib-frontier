/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Search.Frontier
public import CslibFrontier.Algorithms.Lean.Search.Query
public import Cslib.Foundations.Control.Monad.IsMonadHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Cslib.Foundations.Control.Monad.IsMonadHom.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Data.Multiset.Basic

/-!
# Best-first tree search

Generic best-first search ([RussellNorvig2020], §3.3.1, Figure 3.7) over an abstract frontier
(`Cslib.Algorithms.Lean.Search.Frontier`) and a node priority. The search keeps a frontier of
nodes, initially holding the root; at each step it pops a node of minimum priority, returns it if
its state is a goal state (the goal test is applied on removal from the frontier, as in the
textbook's algorithm), and otherwise expands it, inserting each child with its priority.

This is the *tree-like* variant ([RussellNorvig2020], §3.3.3): it keeps no table of reached
states, so it does not detect repeated states or redundant paths; graph search with a reached
table is a later milestone of the roadmap issue. The search runs for at most `fuel` iterations
and returns `none` when the fuel runs out or the frontier becomes empty, so it is a total
function on any state space, finite or not.

The algorithm is written once, monad-polymorphically, as `bestFirstTreeSearchM` against an
interpretation `q : {ι : Type} → SearchQuery S A ι → m ι` of the search queries and a monadic
priority, as CSLib's `List.mergeSortM` is written against a monadic comparison:

* `bestFirstTreeSearch` is the `Id` instance with the queries answered by a problem, and carries
  correctness;
* `bestFirstTreeSearchQ` is the `FreeM (SearchQuery S A)` instance, interpreting the queries by
  `FreeM.lift`, and carries query counts;
* `Cslib.IsMonadHom.map_bestFirstTreeSearchM` says that a monad morphism `f` commutes with the
  algorithm, sending the interpretation `q` to `fun op => f (q op)`, and
  `eval_bestFirstTreeSearchQ` instantiates it at evaluation: the query program, evaluated against
  the oracle of a problem, is the pure algorithm on that problem.

Priorities are computed in the monad, so an informed priority can ask for the heuristic: in the
query instance, A*'s priority `g + h` is
`fun x => (x.cost + ·) <$> FreeM.lift (.heuristic x.state)`.

The textbook's search nodes store the parent and the last action; here a node stores the whole
action sequence from the root, which is what the parent chain encodes.

## Main definitions

* `Node`: a search-tree node.
* `Problem.childNode`, `Problem.keyedChildren`: the children of a node, and their keyed
  versions.
* `Node.IsSound`: a node whose path leads from the initial state to its state at its cost.
* `bestFirstTreeSearchM`: best-first tree search in an arbitrary monad.
* `bestFirstTreeSearch`: the pure algorithm.
* `bestFirstTreeSearchQ`: the query program.

## Main results

* `Cslib.IsMonadHom.map_bestFirstTreeSearchM`, `eval_bestFirstTreeSearchQ`: transfer along monad
  morphisms, and evaluation of the query program.
* `contents_expandM`: expanding a node adds its keyed children (`Problem.keyedChildren`) to the
  frontier.
* `bestFirstLoopM_inv`, `isSome_bestFirstLoopM`: an invariant principle and a termination
  principle (by a potential) for the pure search loop.
* `bestFirstTreeSearch_sound`: whatever the search returns is a path from the initial state to a
  goal state, reaching the returned state at the returned cost, for every lawful frontier,
  priority and fuel.
* `cost_expansionWeight_bestFirstTreeSearchQ_le`: the search expands at most `fuel` nodes.
* `cost_generationWeight_bestFirstTreeSearchQ_le`: with branching factor at most `b`, it
  generates at most `fuel * b` nodes.
* `cost_bestFirstLoopM_le_potential`: a potential paying for each expansion bounds the weighted
  query cost of the search, whatever the fuel.

## References

* [RussellNorvig2020]
-/

public section

namespace Cslib.Algorithms.Lean.Search

/-- A node of the search tree ([RussellNorvig2020], §3.3.2): a state, the sequence of actions
leading to it from the root, and its path cost `g`. -/
structure Node (S A : Type) where
  /-- The state of the node. -/
  state : S
  /-- The actions from the root to the node, in order. -/
  path : List A
  /-- The path cost reported for the node. -/
  cost : ℕ
deriving DecidableEq

variable {m : Type → Type*} [Monad m] {S A κ Q : Type}

/-! ## The algorithm -/

section Programs

variable (q : {ι : Type} → SearchQuery S A ι → m ι)

/-- Generate the child of `node` reached by action `a`, compute its priority and insert it into
the frontier `fr`. -/
@[expose] def pushChildM (F : Frontier Q κ (Node S A)) (prio : Node S A → m κ) (node : Node S A)
    (fr : Q) (a : A) : m Q := do
  let s' ← q (.result node.state a)
  let c ← q (.stepCost node.state a)
  let child : Node S A := ⟨s', node.path ++ [a], node.cost + c⟩
  let k ← prio child
  return F.insert k child fr

/-- Expand `node`: ask for the actions of its state and insert every child into the frontier
`fr`. -/
@[expose] def expandM (F : Frontier Q κ (Node S A)) (prio : Node S A → m κ) (node : Node S A)
    (fr : Q) : m Q := do
  let acts ← q (.actions node.state)
  acts.foldlM (pushChildM q F prio node) fr

/-- The loop of best-first tree search, for at most `fuel` iterations from the frontier `fr`. -/
@[expose] def bestFirstLoopM (F : Frontier Q κ (Node S A)) (prio : Node S A → m κ) :
    ℕ → Q → m (Option (Node S A))
  | 0, _ => pure none
  | fuel + 1, fr =>
    match F.popMin? fr with
    | none => pure none
    | some (node, fr') => do
      if ← q (.isGoal node.state) then
        return some node
      else
        bestFirstLoopM F prio fuel (← expandM q F prio node fr')

/-- Best-first tree search from `init` against the interpretation `q` of the search queries, with
frontier `F`, node priority `prio` and at most `fuel` iterations. -/
@[expose] def bestFirstTreeSearchM (F : Frontier Q κ (Node S A)) (prio : Node S A → m κ)
    (fuel : ℕ) (init : S) : m (Option (Node S A)) := do
  let root : Node S A := ⟨init, [], 0⟩
  let k ← prio root
  bestFirstLoopM q F prio fuel (F.insert k root F.empty)

end Programs

/-- Best-first tree search on the problem `P` with frontier `F`, node priority `prio` and at
most `fuel` iterations: the `Id` instance of `bestFirstTreeSearchM`, with the queries answered by
`P`. The search asks no heuristic queries (its priority is pure), so the heuristic of the oracle
`P.oracle 0` is never consulted; `eval_bestFirstTreeSearchQ` holds for every heuristic. -/
@[expose] def bestFirstTreeSearch (P : Problem S A) (F : Frontier Q κ (Node S A))
    (prio : Node S A → κ) (fuel : ℕ) : Option (Node S A) :=
  Id.run (bestFirstTreeSearchM (fun op => pure (P.oracle 0 op)) F (fun x => pure (prio x)) fuel
    P.initial)

/-- Best-first tree search from `init` as a query program on the search interface: the
`FreeM (SearchQuery S A)` instance of `bestFirstTreeSearchM`. -/
abbrev bestFirstTreeSearchQ (F : Frontier Q κ (Node S A))
    (prio : Node S A → FreeM (SearchQuery S A) κ) (fuel : ℕ) (init : S) :
    FreeM (SearchQuery S A) (Option (Node S A)) :=
  bestFirstTreeSearchM FreeM.lift F prio fuel init

/-! ## Transfer along monad morphisms -/

section Transfer

variable {n : Type → Type*} [Monad n] {f : {α : Type} → m α → n α}

private theorem _root_.Cslib.IsMonadHom.map_pushChildM (hf : IsMonadHom m n f)
    (q : {ι : Type} → SearchQuery S A ι → m ι) (F : Frontier Q κ (Node S A))
    (prio : Node S A → m κ) (node : Node S A) (fr : Q) (a : A) :
    f (pushChildM q F prio node fr a) =
      pushChildM (fun op => f (q op)) F (fun x => f (prio x)) node fr a := by
  simp only [pushChildM, hf.map_bind, hf.map_pure]

private theorem _root_.Cslib.IsMonadHom.map_expandM (hf : IsMonadHom m n f)
    (q : {ι : Type} → SearchQuery S A ι → m ι) (F : Frontier Q κ (Node S A))
    (prio : Node S A → m κ) (node : Node S A) (fr : Q) :
    f (expandM q F prio node fr) =
      expandM (fun op => f (q op)) F (fun x => f (prio x)) node fr := by
  simp only [expandM, hf.map_bind, hf.map_listFoldlM, hf.map_pushChildM]

private theorem _root_.Cslib.IsMonadHom.map_bestFirstLoopM (hf : IsMonadHom m n f)
    (q : {ι : Type} → SearchQuery S A ι → m ι) (F : Frontier Q κ (Node S A))
    (prio : Node S A → m κ) (fuel : ℕ) (fr : Q) :
    f (bestFirstLoopM q F prio fuel fr) =
      bestFirstLoopM (fun op => f (q op)) F (fun x => f (prio x)) fuel fr := by
  induction fuel generalizing fr with
  | zero => exact hf.map_pure _
  | succ fuel ih =>
    simp only [bestFirstLoopM]
    split
    · exact hf.map_pure _
    · simp only [hf.map_bind, apply_ite f, hf.map_pure, hf.map_expandM, ih]

/-- A monad morphism commutes with best-first tree search: applying it to the search is the
search against the image of the query interpretation and of the priority. -/
theorem _root_.Cslib.IsMonadHom.map_bestFirstTreeSearchM (hf : IsMonadHom m n f)
    (q : {ι : Type} → SearchQuery S A ι → m ι) (F : Frontier Q κ (Node S A))
    (prio : Node S A → m κ) (fuel : ℕ) (init : S) :
    f (bestFirstTreeSearchM q F prio fuel init) =
      bestFirstTreeSearchM (fun op => f (q op)) F (fun x => f (prio x)) fuel init := by
  simp only [bestFirstTreeSearchM, hf.map_bind, hf.map_bestFirstLoopM]

end Transfer

/-! ## Evaluation -/

section Congr

variable {q₁ q₂ : {ι : Type} → SearchQuery S A ι → m ι}
  (hactions : ∀ s, q₁ (.actions s) = q₂ (.actions s))
  (hresult : ∀ s a, q₁ (.result s a) = q₂ (.result s a))
  (hisGoal : ∀ s, q₁ (.isGoal s) = q₂ (.isGoal s))
  (hstepCost : ∀ s a, q₁ (.stepCost s a) = q₂ (.stepCost s a))
include hactions hresult hisGoal hstepCost

private theorem bestFirstLoopM_congr (F : Frontier Q κ (Node S A)) (prio : Node S A → m κ)
    (fuel : ℕ) (fr : Q) :
    bestFirstLoopM q₁ F prio fuel fr = bestFirstLoopM q₂ F prio fuel fr := by
  have hpush : ∀ node, pushChildM q₁ F prio node = pushChildM q₂ F prio node := fun node => by
    funext fr a
    simp only [pushChildM, hresult, hstepCost]
  induction fuel generalizing fr with
  | zero => rfl
  | succ fuel ih => simp only [bestFirstLoopM, expandM, hactions, hisGoal, hpush, ih]

/-- The search itself asks only `actions`, `result`, `isGoal` and `stepCost` queries: two
interpretations agreeing on these give the same search. -/
private theorem bestFirstTreeSearchM_congr (F : Frontier Q κ (Node S A)) (prio : Node S A → m κ)
    (fuel : ℕ) (init : S) :
    bestFirstTreeSearchM q₁ F prio fuel init = bestFirstTreeSearchM q₂ F prio fuel init := by
  simp only [bestFirstTreeSearchM, bestFirstLoopM_congr hactions hresult hisGoal hstepCost]

end Congr

/-- Evaluating the query program against the oracle of a problem `P` (with any heuristic `h`)
is the pure algorithm on `P`, with the evaluated priority. -/
@[simp] theorem eval_bestFirstTreeSearchQ (P : Problem S A) (h : S → ℕ)
    (F : Frontier Q κ (Node S A)) (prio : Node S A → FreeM (SearchQuery S A) κ) (fuel : ℕ) :
    (bestFirstTreeSearchQ F prio fuel P.initial).eval (P.oracle h) =
      bestFirstTreeSearch P F (fun x => (prio x).eval (P.oracle h)) fuel := by
  refine Id.pure_injective ?_
  rw [(FreeM.isMonadHom_pure_eval (P.oracle h)).map_bestFirstTreeSearchM]
  exact bestFirstTreeSearchM_congr (q₂ := fun op => pure (P.oracle 0 op)) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) F _ fuel P.initial

/-! ## Children and sound nodes -/

/-- The child of the node `x` reached by the action `a` in the problem `P` ([RussellNorvig2020],
§3.3.1): its state is the result of `a`, its path extends `x`'s by `a`, and its cost adds the
action cost. -/
abbrev Problem.childNode (P : Problem S A) (x : Node S A) (a : A) : Node S A :=
  ⟨P.result x.state a, x.path ++ [a], x.cost + P.stepCost x.state a⟩

/-- The children of the node `x` in the problem `P`, one per action applicable in its state, keyed
by the priority `prio`: what expanding `x` adds to the frontier (`contents_expandM`). -/
@[expose] def Problem.keyedChildren (P : Problem S A) (prio : Node S A → κ) (x : Node S A) :
    Multiset (κ × Node S A) :=
  ((P.actions x.state).map fun a => (prio (P.childNode x a), P.childNode x a) : List _)

/-- The keyed children of `x` are its children by the applicable actions, each with its
priority. -/
theorem Problem.mem_keyedChildren_iff {P : Problem S A} {prio : Node S A → κ} {x : Node S A}
    {p : κ × Node S A} :
    p ∈ P.keyedChildren prio x ↔
      ∃ a ∈ P.actions x.state, (prio (P.childNode x a), P.childNode x a) = p := by
  simp [Problem.keyedChildren]

/-- A node is sound for `P` when its path leads from the initial state to its state and its
reported cost is the path's cost. -/
@[expose] def Node.IsSound (P : Problem S A) (x : Node S A) : Prop :=
  P.toLTS.MTr P.initial x.path x.state ∧ P.pathCost P.initial x.path = x.cost

/-- The child of a sound node by an applicable action is sound. -/
theorem Node.IsSound.childNode {P : Problem S A} {x : Node S A} (hx : x.IsSound P) {a : A}
    (ha : a ∈ P.actions x.state) : (P.childNode x a).IsSound P :=
  ⟨LTS.MTr.stepR _ hx.1 ⟨ha, rfl⟩, by simp [P.pathCost_append_of_mTr hx.1, hx.2]⟩

/-! ## Invariants of the pure algorithm -/

section Invariants

variable [LE κ] {F : Frontier Q κ (Node S A)} {P : Problem S A} {prio : Node S A → κ}

/-- Expanding the node `x` in the pure algorithm (with the queries answered by `P` and any
heuristic) adds its keyed children to the frontier. -/
theorem contents_expandM (hF : F.Lawful) (h : S → ℕ) (x : Node S A) (fr : Q) :
    F.contents (expandM (m := Id) (fun op => pure (P.oracle h op)) F (fun y => pure (prio y)) x
      fr) = P.keyedChildren prio x + F.contents fr := by
  simp only [expandM, Problem.keyedChildren, Problem.oracle_actions]
  change F.contents (Id.run ((P.actions x.state).foldlM _ fr)) = _
  generalize P.actions x.state = acts
  induction acts generalizing fr with
  | nil => simp
  | cons a acts ih =>
    rw [List.foldlM_cons]
    change F.contents (Id.run (acts.foldlM _ (F.insert _ _ fr))) = _
    rw [ih, hF.contents_insert, List.map_cons, ← Multiset.cons_coe, Multiset.cons_add,
      Multiset.add_cons]
    rfl

/-- **Invariant principle for best-first tree search.** A property of the frontier's contents
preserved by expanding every non-goal node of minimum key holds of the frontier from which the
search's answer is popped, with the answer of minimum key and a goal state. -/
theorem bestFirstLoopM_inv (hF : F.Lawful) (Inv : Multiset (κ × Node S A) → Prop)
    (hstep : ∀ M k y, Inv ((k, y) ::ₘ M) → (∀ p ∈ M, k ≤ p.1) → P.isGoal y.state = false →
      Inv (P.keyedChildren prio y + M)) :
    ∀ (fuel : ℕ) (fr : Q) {x : Node S A}, Inv (F.contents fr) →
      Id.run (bestFirstLoopM (fun op => pure (P.oracle 0 op)) F (fun y => pure (prio y)) fuel
        fr) = some x →
      ∃ k M, Inv ((k, x) ::ₘ M) ∧ (∀ p ∈ M, k ≤ p.1) ∧ P.isGoal x.state = true
  | 0, _, _, _, h => by simp [bestFirstLoopM] at h
  | fuel + 1, fr, x, hinv, h => by
    simp only [bestFirstLoopM] at h
    split at h
    · simp at h
    · rename_i y fr' hpop
      obtain ⟨k, hcont, hmin⟩ := hF.exists_of_popMin?_eq_some hpop
      rw [hcont] at hinv
      cases hg : P.isGoal y.state
      · simp only [Problem.oracle_isGoal, hg] at h
        refine bestFirstLoopM_inv hF Inv hstep fuel _ ?_ h
        rw [contents_expandM hF]
        exact hstep _ k y hinv hmin hg
      · simp only [Problem.oracle_isGoal, hg] at h
        cases h
        exact ⟨k, _, hinv, hmin, hg⟩

/-- **Termination principle for best-first tree search.** A potential `Φ` on nodes, positive on
every frontier satisfying an invariant and strictly decreased by every expansion of a non-goal
node of minimum key preserving it, bounds the iterations the search needs to return an
answer. -/
theorem isSome_bestFirstLoopM (hF : F.Lawful) (Inv : Multiset (κ × Node S A) → Prop)
    (Φ : Node S A → ℕ) (hpos : ∀ M, Inv M → 0 < (M.map fun p => Φ p.2).sum)
    (hstep : ∀ M k y, Inv ((k, y) ::ₘ M) → (∀ p ∈ M, k ≤ p.1) → P.isGoal y.state = false →
      Inv (P.keyedChildren prio y + M) ∧ ((P.keyedChildren prio y).map fun p => Φ p.2).sum < Φ y) :
    ∀ (fuel : ℕ) (fr : Q), Inv (F.contents fr) → ((F.contents fr).map fun p => Φ p.2).sum ≤ fuel →
      (Id.run (bestFirstLoopM (fun op => pure (P.oracle 0 op)) F (fun y => pure (prio y)) fuel
        fr)).isSome
  | 0, fr, hinv, hfuel => by have := hpos _ hinv; omega
  | fuel + 1, fr, hinv, hfuel => by
    simp only [bestFirstLoopM]
    split
    · rename_i hpop
      have := hpos _ hinv
      rw [(hF.popMin?_eq_none_iff fr).1 hpop] at this
      simp at this
    · rename_i y fr' hpop
      obtain ⟨k, hcont, hmin⟩ := hF.exists_of_popMin?_eq_some hpop
      rw [hcont] at hinv hfuel
      cases hg : P.isGoal y.state
      · simp only [Problem.oracle_isGoal, hg]
        obtain ⟨hinv', hlt⟩ := hstep _ k y hinv hmin hg
        refine isSome_bestFirstLoopM hF Inv Φ hpos hstep fuel _ ?_ ?_
        · rwa [contents_expandM hF]
        · rw [contents_expandM hF, Multiset.map_add, Multiset.sum_add]
          simp only [Multiset.map_cons, Multiset.sum_cons] at hfuel
          omega
      · simp [hg]

end Invariants

/-! ## Soundness -/

/-- **Soundness of best-first tree search.** A node returned by best-first search
([RussellNorvig2020], §3.3.1, Figure 3.7, here without the reached table) carries a solution: for
every lawful frontier, every node priority and every amount of fuel, the node's action sequence
is a path from the initial state to the node's state, that state is a goal state, and the node's
reported cost is the path's cost. In particular the action sequence is a solution
(`Problem.IsSolution`). -/
theorem bestFirstTreeSearch_sound [LE κ] {F : Frontier Q κ (Node S A)} (hF : F.Lawful)
    (P : Problem S A) (prio : Node S A → κ) (fuel : ℕ) {x : Node S A}
    (h : bestFirstTreeSearch P F prio fuel = some x) :
    P.toLTS.MTr P.initial x.path x.state ∧ P.isGoal x.state = true ∧
      P.pathCost P.initial x.path = x.cost := by
  obtain ⟨k, M, hinv, -, hg⟩ := bestFirstLoopM_inv hF (fun M => ∀ p ∈ M, p.2.IsSound P)
    (fun M k y hinv _ _ p hp => by
      rcases Multiset.mem_add.1 hp with hp | hp
      · obtain ⟨a, ha, rfl⟩ := Problem.mem_keyedChildren_iff.1 hp
        exact (hinv (k, y) (Multiset.mem_cons_self _ _)).childNode ha
      · exact hinv p (Multiset.mem_cons_of_mem hp))
    fuel _ (fun p hp => by
      rw [hF.contents_insert, hF.contents_empty, Multiset.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨.refl, rfl⟩
      · simp at hp) h
  obtain ⟨hpath, hcost⟩ := hinv (k, x) (Multiset.mem_cons_self _ _)
  exact ⟨hpath, hg, hcost⟩

/-! ## Expansions and generations -/

section Cost

variable {F : Frontier Q κ (Node S A)} (oracle : {ι : Type} → SearchQuery S A ι → ι)

/-- In the query model, expanding a node evaluates to the pure expansion against the oracle, with
the evaluated priority. -/
theorem eval_expandM (prio : Node S A → FreeM (SearchQuery S A) κ) (x : Node S A) (fr : Q) :
    (expandM FreeM.lift F prio x fr).eval oracle =
      expandM (m := Id) (fun op => pure (oracle op)) F (fun y => pure ((prio y).eval oracle)) x
        fr :=
  congrArg Id.run ((FreeM.isMonadHom_pure_eval oracle).map_expandM FreeM.lift F prio x fr)

private theorem cost_bestFirstLoopM_le (w : {ι : Type} → SearchQuery S A ι → ℕ)
    (prio : Node S A → FreeM (SearchQuery S A) κ) (c : ℕ) (hgoal : ∀ s, w (.isGoal s) = 0)
    (hexpand : ∀ x fr, (expandM FreeM.lift F prio x fr).cost oracle w ≤ c) :
    ∀ (fuel : ℕ) (fr : Q), (bestFirstLoopM FreeM.lift F prio fuel fr).cost oracle w ≤ fuel * c
  | 0, _ => by simp [bestFirstLoopM]
  | fuel + 1, fr => by
    simp only [bestFirstLoopM]
    split
    · simp
    · rename_i y fr' _
      simp only [FreeM.cost_bind, FreeM.cost_lift, hgoal, zero_add]
      split
      · simp
      · rw [FreeM.cost_bind, Nat.succ_mul, Nat.add_comm (fuel * c)]
        exact Nat.add_le_add (hexpand y fr')
          (cost_bestFirstLoopM_le w prio c hgoal hexpand fuel _)

/-- The cost of expanding a node under weight `w` when each child's priority costs nothing: one
`actions` query and, per action, one `result` and one `stepCost` query. -/
theorem cost_expandM (w : {ι : Type} → SearchQuery S A ι → ℕ)
    (prio : Node S A → FreeM (SearchQuery S A) κ) (hprio : ∀ x, (prio x).cost oracle w = 0)
    (x : Node S A) (fr : Q) :
    (expandM FreeM.lift F prio x fr).cost oracle w =
      w (.actions x.state) + ((oracle (.actions x.state)).map fun a =>
        w (.result x.state a) + w (.stepCost x.state a)).sum := by
  simp only [expandM, FreeM.cost_bind, FreeM.cost_lift, FreeM.eval_lift]
  congr 1
  generalize oracle (.actions x.state) = acts
  induction acts generalizing fr with
  | nil => simp
  | cons a acts ih =>
    simp only [List.foldlM_cons, FreeM.cost_bind, ih, List.map_cons, List.sum_cons]
    simp [pushChildM, hprio, Nat.add_assoc]

/-- **Expansion bound**: in the query model, best-first tree search with `fuel` iterations expands
at most `fuel` nodes, for every oracle, frontier and priority whose computation expands nothing
(for instance any pure priority, or a priority asking only for the heuristic). An expansion is an
`actions` query, counted by `SearchQuery.expansionWeight`. -/
theorem cost_expansionWeight_bestFirstTreeSearchQ_le
    (prio : Node S A → FreeM (SearchQuery S A) κ)
    (hprio : ∀ x, (prio x).cost oracle SearchQuery.expansionWeight = 0) (fuel : ℕ) (init : S) :
    (bestFirstTreeSearchQ F prio fuel init).cost oracle SearchQuery.expansionWeight ≤ fuel := by
  simp only [bestFirstTreeSearchQ, bestFirstTreeSearchM, FreeM.cost_bind, hprio, zero_add]
  simpa using cost_bestFirstLoopM_le oracle SearchQuery.expansionWeight prio 1 (fun _ => rfl)
    (fun x fr => by simp [cost_expandM oracle _ prio hprio, SearchQuery.expansionWeight]) fuel _

/-- **Generation bound**: in the query model, if every state has at most `b` actions, then
best-first tree search with `fuel` iterations generates at most `fuel * b` nodes, for every
frontier and every priority whose computation generates nothing. A generation is a `result`
query, counted by `SearchQuery.generationWeight`. -/
theorem cost_generationWeight_bestFirstTreeSearchQ_le
    (prio : Node S A → FreeM (SearchQuery S A) κ)
    (hprio : ∀ x, (prio x).cost oracle SearchQuery.generationWeight = 0) {b : ℕ}
    (hb : ∀ s, (oracle (.actions s)).length ≤ b) (fuel : ℕ) (init : S) :
    (bestFirstTreeSearchQ F prio fuel init).cost oracle SearchQuery.generationWeight ≤
      fuel * b := by
  simp only [bestFirstTreeSearchQ, bestFirstTreeSearchM, FreeM.cost_bind, hprio, zero_add]
  refine cost_bestFirstLoopM_le oracle SearchQuery.generationWeight prio b (fun _ => rfl)
    (fun x fr => ?_) fuel _
  simpa [cost_expandM oracle _ prio hprio, SearchQuery.generationWeight] using hb x.state

/-- **Potential bound on the weighted cost.** A potential `E` on nodes that pays for the
expansion of every node under the weight `w`, its children's potentials included, bounds the
weighted query cost of the search loop with a pure priority by the total potential of the
frontier, whatever the fuel. -/
theorem cost_bestFirstLoopM_le_potential [LE κ] (hF : F.Lawful) (P : Problem S A) (h : S → ℕ)
    (prio : Node S A → κ) (w : {ι : Type} → SearchQuery S A ι → ℕ)
    (hgoal : ∀ s, w (.isGoal s) = 0) (E : Node S A → ℕ)
    (hE : ∀ y, w (.actions y.state) + ((P.actions y.state).map fun a =>
      w (.result y.state a) + w (.stepCost y.state a) + E (P.childNode y a)).sum ≤ E y) :
    ∀ (fuel : ℕ) (fr : Q), (bestFirstLoopM FreeM.lift F (fun x => pure (prio x)) fuel fr).cost
      (P.oracle h) w ≤ ((F.contents fr).map fun p => E p.2).sum
  | 0, _ => by simp [bestFirstLoopM]
  | fuel + 1, fr => by
    simp only [bestFirstLoopM]
    split
    · simp
    · rename_i y fr' hpop
      obtain ⟨k, hcont, -⟩ := hF.exists_of_popMin?_eq_some hpop
      rw [hcont, Multiset.map_cons, Multiset.sum_cons]
      simp only [FreeM.cost_bind, FreeM.cost_lift, hgoal, zero_add]
      split
      · simp
      · have ih := cost_bestFirstLoopM_le_potential hF P h prio w hgoal E hE fuel
          ((expandM FreeM.lift F (fun x => pure (prio x)) y fr').eval (P.oracle h))
        have hc : F.contents ((expandM FreeM.lift F (fun x => pure (prio x)) y fr').eval
            (P.oracle h)) = P.keyedChildren prio y + F.contents fr' := by
          rw [eval_expandM]
          exact contents_expandM hF h y fr'
        rw [hc, Multiset.map_add, Multiset.sum_add] at ih
        simp only [Problem.keyedChildren, Multiset.map_coe, Multiset.sum_coe, List.map_map,
          Function.comp_def] at ih
        rw [FreeM.cost_bind, cost_expandM _ w _ (fun _ => FreeM.cost_pure _ _ _)]
        have := hE y
        rw [List.sum_map_add] at this
        simp only [Problem.oracle_actions]
        omega

end Cost

end Cslib.Algorithms.Lean.Search
