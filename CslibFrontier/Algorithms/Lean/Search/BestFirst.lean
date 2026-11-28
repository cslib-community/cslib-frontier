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
import Cslib.Foundations.Control.Monad.IsMonadHom.List
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
* `bestFirstTreeSearchM`: best-first tree search in an arbitrary monad.
* `bestFirstTreeSearch`: the pure algorithm.
* `bestFirstTreeSearchQ`: the query program.

## Main results

* `Cslib.IsMonadHom.map_bestFirstTreeSearchM`, `eval_bestFirstTreeSearchQ`: transfer along monad
  morphisms, and evaluation of the query program.
* `bestFirstTreeSearch_sound`: whatever the search returns is a path from the initial state to a
  goal state, reaching the returned state at the returned cost, for every lawful frontier,
  priority and fuel.
* `cost_expansionWeight_bestFirstTreeSearchQ_le`: the search expands at most `fuel` nodes.
* `cost_generationWeight_bestFirstTreeSearchQ_le`: with branching factor at most `b`, it
  generates at most `fuel * b` nodes.

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

/-! ## Soundness -/

section Soundness

variable [LE κ] {P : Problem S A} {F : Frontier Q κ (Node S A)} {prio : Node S A → κ}

/-- A node is sound for `P` when its path leads from the initial state to its state and costs
its cost. -/
private def Sound (P : Problem S A) (x : Node S A) : Prop :=
  P.toLTS.MTr P.initial x.path x.state ∧ P.pathCost P.initial x.path = x.cost

private theorem sound_child {x : Node S A} (hx : Sound P x) {a : A}
    (ha : a ∈ P.actions x.state) :
    Sound P ⟨P.result x.state a, x.path ++ [a], x.cost + P.stepCost x.state a⟩ :=
  ⟨LTS.MTr.stepR _ hx.1 ⟨ha, rfl⟩, by simp [P.pathCost_append_of_mTr hx.1, hx.2]⟩

private theorem sound_foldlM (hF : F.Lawful) {x : Node S A} (hx : Sound P x) :
    ∀ (acts : List A), (∀ a ∈ acts, a ∈ P.actions x.state) →
      ∀ fr : Q, (∀ p ∈ F.contents fr, Sound P p.2) →
        ∀ p ∈ F.contents (Id.run (acts.foldlM
          (pushChildM (fun op => pure (P.oracle 0 op)) F (fun y => pure (prio y)) x) fr)),
          Sound P p.2
  | [], _, _, hfr => hfr
  | a :: acts, hacts, fr, hfr => by
    refine sound_foldlM hF hx acts (fun b hb => hacts b (List.mem_cons_of_mem _ hb)) _ ?_
    intro p hp
    change p ∈ F.contents (F.insert _ _ fr) at hp
    rw [hF.contents_insert, Multiset.mem_cons] at hp
    rcases hp with rfl | hp
    · exact sound_child hx (hacts a List.mem_cons_self)
    · exact hfr p hp

private theorem sound_bestFirstLoopM (hF : F.Lawful) :
    ∀ (fuel : ℕ) (fr : Q), (∀ p ∈ F.contents fr, Sound P p.2) → ∀ {x : Node S A},
      Id.run (bestFirstLoopM (fun op => pure (P.oracle 0 op)) F (fun y => pure (prio y)) fuel
        fr) = some x →
        Sound P x ∧ P.isGoal x.state = true
  | 0, _, _, _, h => by simp [bestFirstLoopM] at h
  | fuel + 1, fr, hfr, x, h => by
    simp only [bestFirstLoopM] at h
    split at h
    · simp at h
    · rename_i y fr' hpop
      obtain ⟨k, hcont, -⟩ := hF.exists_of_popMin?_eq_some hpop
      have hy : Sound P y := hfr (k, y) (by rw [hcont]; exact Multiset.mem_cons_self _ _)
      have hfr' : ∀ p ∈ F.contents fr', Sound P p.2 :=
        fun p hp => hfr p (by rw [hcont]; exact Multiset.mem_cons_of_mem hp)
      by_cases hg : P.isGoal y.state = true
      · simp only [Problem.oracle_isGoal, hg] at h
        cases h
        exact ⟨hy, hg⟩
      · simp only [Problem.oracle_isGoal, hg] at h
        exact sound_bestFirstLoopM hF fuel _
          (sound_foldlM hF hy _ (fun _ ha => ha) fr' hfr') h

/-- **Soundness of best-first tree search.** A node returned by best-first search
([RussellNorvig2020], §3.3.1, Figure 3.7, here without the reached table) carries a solution: for
every lawful frontier, every node priority and every amount of fuel, the node's action sequence
is a path from the initial state to the node's state, that state is a goal state, and the node's
reported cost is the path's cost. In particular the action sequence is a solution
(`Problem.IsSolution`). -/
theorem bestFirstTreeSearch_sound (hF : F.Lawful) (P : Problem S A) (prio : Node S A → κ)
    (fuel : ℕ) {x : Node S A} (h : bestFirstTreeSearch P F prio fuel = some x) :
    P.toLTS.MTr P.initial x.path x.state ∧ P.isGoal x.state = true ∧
      P.pathCost P.initial x.path = x.cost := by
  have hroot : ∀ p ∈ F.contents (F.insert (prio ⟨P.initial, [], 0⟩) ⟨P.initial, [], 0⟩ F.empty),
      Sound P p.2 := by
    intro p hp
    rw [hF.contents_insert, hF.contents_empty, Multiset.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨.refl, rfl⟩
    · simp at hp
  obtain ⟨⟨hpath, hcost⟩, hgoal⟩ := sound_bestFirstLoopM hF fuel _ hroot h
  exact ⟨hpath, hgoal, hcost⟩

end Soundness

/-! ## Expansions and generations -/

section Cost

variable {F : Frontier Q κ (Node S A)} (oracle : {ι : Type} → SearchQuery S A ι → ι)

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
private theorem cost_expandM (w : {ι : Type} → SearchQuery S A ι → ℕ)
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

end Cost

end Cslib.Algorithms.Lean.Search
