/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Search.AStar
public import Mathlib.Data.Finset.Card
import Cslib.Foundations.Control.Monad.IsMonadHom.List
import Mathlib.Data.Multiset.Basic

/-!
# Best-first graph search and A* graph search

Best-first *graph* search ([RussellNorvig2020], §3.3.3) is best-first search that remembers the
states it has expanded, its *explored set*, so that it expands no state twice. Each iteration
pops a node of minimum priority from the frontier; a node whose state is already explored is
discarded; otherwise the search returns the node if its state is a goal state, and else adds the
state to the explored set and expands the node, inserting each child whose state is not
explored. As in `Cslib.Algorithms.Lean.Search.BestFirst`, the search runs for at most `fuel`
iterations, is written once monad-polymorphically as `bestFirstGraphSearchM` against an
interpretation of the search queries, and has a pure instance `bestFirstGraphSearch` carrying
correctness and a query instance `bestFirstGraphSearchQ` carrying counts, related by
`eval_bestFirstGraphSearchQ`.

The explored set is the closed list of the classical formulation of graph search. The fourth
edition's `BEST-FIRST-SEARCH` ([RussellNorvig2020], §3.3.1, Figure 3.7) instead keeps a table
`reached` of the cheapest node found for each generated state, and adds a child to the frontier
when its state is new or reached more cheaply. The abstract frontier has no decrease-key
operation, so here the frontier may hold several nodes for one state, and those popped after the
state is explored are discarded ("lazy deletion"). This makes "every state is expanded at most
once" a structural property of the algorithm, holding for every oracle.

*A\* graph search* `aStarGraphSearch` is the instance with priority `f = g + h`. With a
consistent heuristic it is cost-optimal ([RussellNorvig2020], §3.5.2): by the argument of
[HartNilssonRaphael1968], consistency makes the first node popped for a state carry a cheapest
path to that state, so discarding later nodes for the same state loses nothing. With a heuristic
that is admissible but not consistent this variant can return a suboptimal solution, because it
never reopens an explored state; the tests exhibit such a run. Reopening is not implemented here.

## Main definitions

* `bestFirstGraphSearchM`: best-first graph search in an arbitrary monad.
* `bestFirstGraphSearch`: the pure algorithm.
* `bestFirstGraphSearchQ`: the query program.
* `aStarGraphSearch`: A* graph search.

## Main results

* `Cslib.IsMonadHom.map_bestFirstGraphSearchM`, `eval_bestFirstGraphSearchQ`: transfer along monad
  morphisms, and evaluation of the query program.
* `bestFirstGraphSearch_sound`: whatever the search returns is a path from the initial state to a
  goal state at the reported cost, for every lawful frontier, priority and fuel.
* `bestFirstGraphSearch_complete`: on a finite state space with bounded branching, a problem with
  a solution, and enough fuel (explicitly bounded), the search returns a solution, for every lawful
  frontier and priority.
* `aStarGraphSearch_isOptimalSolution`: with a consistent heuristic, the solution A* graph search
  returns is optimal.
* `aStarGraphSearch_complete`: with a consistent heuristic, on a finite state space with enough
  fuel, A* graph search returns an optimal solution whenever the problem has one.
* `uniformCostGraphSearch_isOptimalSolution`: the same for uniform-cost graph search, the case
  `h = 0`.
* `cost_expansionWeightAt_bestFirstGraphSearchQ_le_one`: in the query model, the search expands
  every state at most once, for every oracle, frontier, priority and fuel.
* `cost_expansionWeight_bestFirstGraphSearchQ_le_card`: the search expands at most as many nodes
  as there are states in any finite set containing the initial state and closed under successors.

## References

* [HartNilssonRaphael1968]
* [RussellNorvig2020]
-/

public section

namespace Cslib.Algorithms.Lean.Search

variable {m : Type → Type*} [Monad m] {S A κ Q : Type} [DecidableEq S]

/-! ## The algorithm -/

section Programs

variable (q : {ι : Type} → SearchQuery S A ι → m ι)

/-- Generate the child of `node` reached by action `a` and, unless its state is in the explored
set `explored`, compute its priority and insert it into the frontier `fr`. -/
@[expose] def pushGraphChildM (F : Frontier Q κ (Node S A)) (prio : Node S A → m κ)
    (explored : Finset S) (node : Node S A) (fr : Q) (a : A) : m Q := do
  let s' ← q (.result node.state a)
  if s' ∈ explored then
    return fr
  else
    let c ← q (.stepCost node.state a)
    let child : Node S A := ⟨s', node.path ++ [a], node.cost + c⟩
    let k ← prio child
    return F.insert k child fr

/-- Expand `node` against the explored set `explored`: ask for the actions of its state and insert
every child whose state is not explored into the frontier `fr`. -/
@[expose] def expandGraphM (F : Frontier Q κ (Node S A)) (prio : Node S A → m κ)
    (explored : Finset S) (node : Node S A) (fr : Q) : m Q := do
  let acts ← q (.actions node.state)
  acts.foldlM (pushGraphChildM q F prio explored node) fr

/-- The loop of best-first graph search, for at most `fuel` iterations from the frontier `fr` and
the explored set `explored`. -/
@[expose] def bestFirstGraphLoopM (F : Frontier Q κ (Node S A)) (prio : Node S A → m κ) :
    ℕ → Q → Finset S → m (Option (Node S A))
  | 0, _, _ => pure none
  | fuel + 1, fr, explored =>
    match F.popMin? fr with
    | none => pure none
    | some (node, fr') =>
      if node.state ∈ explored then
        bestFirstGraphLoopM F prio fuel fr' explored
      else do
        if ← q (.isGoal node.state) then
          return some node
        else
          let explored' := insert node.state explored
          bestFirstGraphLoopM F prio fuel (← expandGraphM q F prio explored' node fr') explored'

/-- Best-first graph search from `init` against the interpretation `q` of the search queries,
with frontier `F`, node priority `prio` and at most `fuel` iterations. -/
@[expose] def bestFirstGraphSearchM (F : Frontier Q κ (Node S A)) (prio : Node S A → m κ)
    (fuel : ℕ) (init : S) : m (Option (Node S A)) := do
  let root : Node S A := ⟨init, [], 0⟩
  let k ← prio root
  bestFirstGraphLoopM q F prio fuel (F.insert k root F.empty) ∅

end Programs

/-- Best-first graph search on the problem `P` with frontier `F`, node priority `prio` and at most
`fuel` iterations: the `Id` instance of `bestFirstGraphSearchM`, with the queries answered by `P`.
The search asks no heuristic queries (its priority is pure), so the heuristic of the oracle
`P.oracle 0` is never consulted; `eval_bestFirstGraphSearchQ` holds for every heuristic. -/
@[expose] def bestFirstGraphSearch (P : Problem S A) (F : Frontier Q κ (Node S A))
    (prio : Node S A → κ) (fuel : ℕ) : Option (Node S A) :=
  Id.run (bestFirstGraphSearchM (fun op => pure (P.oracle 0 op)) F (fun x => pure (prio x)) fuel
    P.initial)

/-- Best-first graph search from `init` as a query program on the search interface: the
`FreeM (SearchQuery S A)` instance of `bestFirstGraphSearchM`. -/
abbrev bestFirstGraphSearchQ (F : Frontier Q κ (Node S A))
    (prio : Node S A → FreeM (SearchQuery S A) κ) (fuel : ℕ) (init : S) :
    FreeM (SearchQuery S A) (Option (Node S A)) :=
  bestFirstGraphSearchM FreeM.lift F prio fuel init

/-- A\* graph search ([RussellNorvig2020], §3.5.2) on the problem `P` with heuristic `h`:
best-first graph search with the evaluation function `f = g + h`, with frontier `F` and at most
`fuel` iterations. In the query model it is `bestFirstGraphSearchQ` with the priority
`fun x => (x.cost + ·) <$> FreeM.lift (.heuristic x.state)`. -/
abbrev aStarGraphSearch (P : Problem S A) (h : S → ℕ) (F : Frontier Q ℕ (Node S A)) (fuel : ℕ) :
    Option (Node S A) :=
  bestFirstGraphSearch P F (fun x => x.cost + h x.state) fuel

/-! ## Transfer along monad morphisms -/

section Transfer

variable {n : Type → Type*} [Monad n] {f : {α : Type} → m α → n α}

private theorem _root_.Cslib.IsMonadHom.map_pushGraphChildM (hf : IsMonadHom m n f)
    (q : {ι : Type} → SearchQuery S A ι → m ι) (F : Frontier Q κ (Node S A))
    (prio : Node S A → m κ) (E : Finset S) (node : Node S A) (fr : Q) (a : A) :
    f (pushGraphChildM q F prio E node fr a) =
      pushGraphChildM (fun op => f (q op)) F (fun x => f (prio x)) E node fr a := by
  simp only [pushGraphChildM, hf.map_bind, hf.map_pure, apply_ite f]

private theorem _root_.Cslib.IsMonadHom.map_expandGraphM (hf : IsMonadHom m n f)
    (q : {ι : Type} → SearchQuery S A ι → m ι) (F : Frontier Q κ (Node S A))
    (prio : Node S A → m κ) (E : Finset S) (node : Node S A) (fr : Q) :
    f (expandGraphM q F prio E node fr) =
      expandGraphM (fun op => f (q op)) F (fun x => f (prio x)) E node fr := by
  simp only [expandGraphM, hf.map_bind, hf.map_listFoldlM, hf.map_pushGraphChildM]

private theorem _root_.Cslib.IsMonadHom.map_bestFirstGraphLoopM (hf : IsMonadHom m n f)
    (q : {ι : Type} → SearchQuery S A ι → m ι) (F : Frontier Q κ (Node S A))
    (prio : Node S A → m κ) (fuel : ℕ) (fr : Q) (E : Finset S) :
    f (bestFirstGraphLoopM q F prio fuel fr E) =
      bestFirstGraphLoopM (fun op => f (q op)) F (fun x => f (prio x)) fuel fr E := by
  induction fuel generalizing fr E with
  | zero => exact hf.map_pure _
  | succ fuel ih =>
    simp only [bestFirstGraphLoopM]
    split
    · exact hf.map_pure _
    · split
      · exact ih _ _
      · simp only [hf.map_bind, apply_ite f, hf.map_pure, hf.map_expandGraphM, ih]

/-- A monad morphism commutes with best-first graph search: applying it to the search is the
search against the image of the query interpretation and of the priority. -/
theorem _root_.Cslib.IsMonadHom.map_bestFirstGraphSearchM (hf : IsMonadHom m n f)
    (q : {ι : Type} → SearchQuery S A ι → m ι) (F : Frontier Q κ (Node S A))
    (prio : Node S A → m κ) (fuel : ℕ) (init : S) :
    f (bestFirstGraphSearchM q F prio fuel init) =
      bestFirstGraphSearchM (fun op => f (q op)) F (fun x => f (prio x)) fuel init := by
  simp only [bestFirstGraphSearchM, hf.map_bind, hf.map_bestFirstGraphLoopM]

end Transfer

/-! ## Evaluation -/

section Congr

variable {q₁ q₂ : {ι : Type} → SearchQuery S A ι → m ι}
  (hactions : ∀ s, q₁ (.actions s) = q₂ (.actions s))
  (hresult : ∀ s a, q₁ (.result s a) = q₂ (.result s a))
  (hisGoal : ∀ s, q₁ (.isGoal s) = q₂ (.isGoal s))
  (hstepCost : ∀ s a, q₁ (.stepCost s a) = q₂ (.stepCost s a))
include hactions hresult hisGoal hstepCost

private theorem bestFirstGraphLoopM_congr (F : Frontier Q κ (Node S A)) (prio : Node S A → m κ)
    (fuel : ℕ) (fr : Q) (E : Finset S) :
    bestFirstGraphLoopM q₁ F prio fuel fr E = bestFirstGraphLoopM q₂ F prio fuel fr E := by
  have hpush : ∀ E node, pushGraphChildM q₁ F prio E node = pushGraphChildM q₂ F prio E node :=
    fun E node => by
      funext fr a
      simp only [pushGraphChildM, hresult, hstepCost]
  induction fuel generalizing fr E with
  | zero => rfl
  | succ fuel ih => simp only [bestFirstGraphLoopM, expandGraphM, hactions, hisGoal, hpush, ih]

/-- The search itself asks only `actions`, `result`, `isGoal` and `stepCost` queries: two
interpretations agreeing on these give the same search. -/
private theorem bestFirstGraphSearchM_congr (F : Frontier Q κ (Node S A))
    (prio : Node S A → m κ) (fuel : ℕ) (init : S) :
    bestFirstGraphSearchM q₁ F prio fuel init = bestFirstGraphSearchM q₂ F prio fuel init := by
  simp only [bestFirstGraphSearchM,
    bestFirstGraphLoopM_congr hactions hresult hisGoal hstepCost]

end Congr

/-- Evaluating the query program against the oracle of a problem `P` (with any heuristic `h`)
is the pure algorithm on `P`, with the evaluated priority. -/
@[simp] theorem eval_bestFirstGraphSearchQ (P : Problem S A) (h : S → ℕ)
    (F : Frontier Q κ (Node S A)) (prio : Node S A → FreeM (SearchQuery S A) κ) (fuel : ℕ) :
    (bestFirstGraphSearchQ F prio fuel P.initial).eval (P.oracle h) =
      bestFirstGraphSearch P F (fun x => (prio x).eval (P.oracle h)) fuel := by
  refine Id.pure_injective ?_
  rw [(FreeM.isMonadHom_pure_eval (P.oracle h)).map_bestFirstGraphSearchM]
  exact bestFirstGraphSearchM_congr (q₂ := fun op => pure (P.oracle 0 op)) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) F _ fuel P.initial

/-! ## Frontier contents along the search -/

section Contents

variable [LE κ] {F : Frontier Q κ (Node S A)}

/-- The child of `x` reached by the action `a`, with the answers of the oracle `o`. -/
private abbrev graphChild (o : {ι : Type} → SearchQuery S A ι → ι) (x : Node S A) (a : A) :
    Node S A :=
  ⟨o (.result x.state a), x.path ++ [a], x.cost + o (.stepCost x.state a)⟩

omit [LE κ] in
private theorem pushGraphChildM_of_mem {o : {ι : Type} → SearchQuery S A ι → ι}
    {prio : Node S A → κ} {E : Finset S} {x : Node S A} {fr : Q} {a : A}
    (ha : o (.result x.state a) ∈ E) :
    pushGraphChildM (m := Id) (fun op => pure (o op)) F (fun y => pure (prio y)) E x fr a =
      pure fr := by
  simp [pushGraphChildM, ha]

omit [LE κ] in
private theorem pushGraphChildM_of_notMem {o : {ι : Type} → SearchQuery S A ι → ι}
    {prio : Node S A → κ} {E : Finset S} {x : Node S A} {fr : Q} {a : A}
    (ha : o (.result x.state a) ∉ E) :
    pushGraphChildM (m := Id) (fun op => pure (o op)) F (fun y => pure (prio y)) E x fr a =
      pure (F.insert (prio (graphChild o x a)) (graphChild o x a) fr) := by
  simp [pushGraphChildM, ha]

/-- The keyed elements held after expanding `x` over the actions `acts` against the explored set
`E`: those held before, and each child whose state is not explored, with its priority. -/
private theorem mem_contents_foldlM_pushGraphChildM (hF : F.Lawful)
    (o : {ι : Type} → SearchQuery S A ι → ι) (prio : Node S A → κ) (E : Finset S)
    (x : Node S A) (p : κ × Node S A) :
    ∀ (acts : List A) (fr : Q),
      p ∈ F.contents (Id.run (acts.foldlM
        (pushGraphChildM (fun op => pure (o op)) F (fun y => pure (prio y)) E x) fr)) ↔
      p ∈ F.contents fr ∨
        ∃ a ∈ acts, o (.result x.state a) ∉ E ∧ p = (prio (graphChild o x a), graphChild o x a)
  | [], fr => by simp
  | a :: acts, fr => by
    rw [List.foldlM_cons]
    by_cases ha : o (.result x.state a) ∈ E
    · rw [pushGraphChildM_of_mem ha, pure_bind,
        mem_contents_foldlM_pushGraphChildM hF o prio E x p acts fr]
      simp only [List.mem_cons, exists_eq_or_imp, ha, not_true_eq_false, false_and, false_or]
    · rw [pushGraphChildM_of_notMem ha, pure_bind,
        mem_contents_foldlM_pushGraphChildM hF o prio E x p acts, hF.contents_insert,
        Multiset.mem_cons]
      simp only [List.mem_cons, exists_eq_or_imp, ha, not_false_eq_true, true_and]
      tauto

/-- Expanding `x` over the actions `acts` adds at most `acts.length` keyed elements. -/
private theorem card_contents_foldlM_pushGraphChildM_le (hF : F.Lawful)
    (o : {ι : Type} → SearchQuery S A ι → ι) (prio : Node S A → κ) (E : Finset S)
    (x : Node S A) :
    ∀ (acts : List A) (fr : Q),
      Multiset.card (F.contents (Id.run (acts.foldlM
        (pushGraphChildM (fun op => pure (o op)) F (fun y => pure (prio y)) E x) fr))) ≤
      Multiset.card (F.contents fr) + acts.length
  | [], fr => by simp
  | a :: acts, fr => by
    rw [List.foldlM_cons, List.length_cons]
    by_cases ha : o (.result x.state a) ∈ E
    · rw [pushGraphChildM_of_mem ha, pure_bind]
      have := card_contents_foldlM_pushGraphChildM_le hF o prio E x acts fr
      omega
    · rw [pushGraphChildM_of_notMem ha, pure_bind]
      have := card_contents_foldlM_pushGraphChildM_le hF o prio E x acts
        (F.insert (prio (graphChild o x a)) (graphChild o x a) fr)
      rw [hF.contents_insert, Multiset.card_cons] at this
      omega

/-- The keyed elements held after expanding `x` in the pure algorithm on `P`. -/
private theorem mem_contents_expandGraphM (hF : F.Lawful) {P : Problem S A}
    (prio : Node S A → κ) (E : Finset S) (x : Node S A) (fr : Q) (p : κ × Node S A) :
    p ∈ F.contents (Id.run (expandGraphM (fun op => pure (P.oracle 0 op)) F
      (fun y => pure (prio y)) E x fr)) ↔
      p ∈ F.contents fr ∨ ∃ a ∈ P.actions x.state, P.result x.state a ∉ E ∧
        p = (prio (P.childNode x a), P.childNode x a) :=
  mem_contents_foldlM_pushGraphChildM hF (P.oracle 0) prio E x p (P.actions x.state) fr

end Contents

/-! ## Soundness -/

section Soundness

variable {P : Problem S A} {F : Frontier Q κ (Node S A)}

/-- Induction along a run of the pure algorithm: if a property of the frontier and explored set
holds initially and survives discarding a popped node whose state is explored and expanding a
popped node whose state is not, then a returned node was popped from a frontier with the property,
with its state unexplored and a goal state. -/
private theorem exists_of_bestFirstGraphLoopM_eq_some (prio : Node S A → κ)
    (I : Q → Finset S → Prop)
    (hskip : ∀ {fr E y fr'}, I fr E → F.popMin? fr = some (y, fr') → y.state ∈ E → I fr' E)
    (hexpand : ∀ {fr E y fr'}, I fr E → F.popMin? fr = some (y, fr') → y.state ∉ E →
      P.isGoal y.state = false →
      I (Id.run (expandGraphM (fun op => pure (P.oracle 0 op)) F (fun z => pure (prio z))
        (insert y.state E) y fr')) (insert y.state E)) :
    ∀ (fuel : ℕ) (fr : Q) (E : Finset S), I fr E → ∀ {x : Node S A},
      Id.run (bestFirstGraphLoopM (fun op => pure (P.oracle 0 op)) F (fun z => pure (prio z))
        fuel fr E) = some x →
      ∃ fr E fr', I fr E ∧ F.popMin? fr = some (x, fr') ∧ x.state ∉ E ∧ P.isGoal x.state = true
  | 0, _, _, _, _, hx => by simp [bestFirstGraphLoopM] at hx
  | fuel + 1, fr, E, hI, x, hx => by
    simp only [bestFirstGraphLoopM] at hx
    split at hx
    · simp at hx
    · rename_i y fr' hpop
      split at hx
      · rename_i hyE
        exact exists_of_bestFirstGraphLoopM_eq_some prio I hskip hexpand fuel fr' E
          (hskip hI hpop hyE) hx
      · rename_i hyE
        by_cases hg : P.isGoal y.state = true
        · simp only [Problem.oracle_isGoal, hg] at hx
          cases hx
          exact ⟨fr, E, fr', hI, hpop, hyE, hg⟩
        · simp only [Problem.oracle_isGoal, hg] at hx
          exact exists_of_bestFirstGraphLoopM_eq_some prio I hskip hexpand fuel _ _
            (hexpand hI hpop hyE (by simpa using hg)) hx

/-- **Soundness of best-first graph search.** A node returned by best-first graph search carries a
solution: for every lawful frontier, every node priority and every amount of fuel, the node's
action sequence is a path from the initial state to the node's state, that state is a goal state,
and the node's reported cost is the path's cost. -/
theorem bestFirstGraphSearch_sound [LE κ] (hF : F.Lawful) (P : Problem S A) (prio : Node S A → κ)
    (fuel : ℕ) {x : Node S A} (hx : bestFirstGraphSearch P F prio fuel = some x) :
    P.toLTS.MTr P.initial x.path x.state ∧ P.isGoal x.state = true ∧
      P.pathCost P.initial x.path = x.cost := by
  obtain ⟨fr, E, fr', hI, hpop, -, hg⟩ := exists_of_bestFirstGraphLoopM_eq_some (P := P) prio
    (fun fr _ => ∀ p ∈ F.contents fr, p.2.IsSound P)
    (fun hI hpop _ p hp => hI p (hF.mem_of_mem_popMin? hpop hp))
    (fun {_ _ y fr'} hI hpop _ _ p hp => by
      rcases (mem_contents_expandGraphM hF prio _ y fr' p).1 hp with hp | ⟨a, ha, -, rfl⟩
      · exact hI p (hF.mem_of_mem_popMin? hpop hp)
      · obtain ⟨k, hk⟩ := hF.exists_mem_of_popMin? hpop
        exact (hI (k, y) hk).childNode ha)
    fuel _ ∅ (fun p hp => by
      rw [hF.contents_insert, hF.contents_empty, Multiset.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨.refl, rfl⟩
      · simp at hp) hx
  obtain ⟨k, hk⟩ := hF.exists_mem_of_popMin? hpop
  obtain ⟨hpath, hcost⟩ := hI (k, x) hk
  exact ⟨hpath, hg, hcost⟩

end Soundness

/-! ## Completeness under finiteness -/

section Completeness

variable [LE κ] {P : Problem S A} {F : Frontier Q κ (Node S A)}

/-- The loop invariant for completeness, relative to a set of states `R`: frontier states lie in
`R`; no explored state is a goal state; the root is on the frontier while the initial state is
unexplored; and every unexplored successor of an explored state has a node on the frontier. -/
private structure ReachInv (P : Problem S A) (F : Frontier Q κ (Node S A)) (R : Finset S)
    (fr : Q) (E : Finset S) : Prop where
  mem : ∀ p ∈ F.contents fr, p.2.state ∈ R
  goal : ∀ s ∈ E, P.isGoal s = false
  root : P.initial ∉ E → ∃ p ∈ F.contents fr, p.2.state = P.initial
  succ : ∀ s ∈ E, ∀ a ∈ P.actions s, P.result s a ∉ E →
    ∃ p ∈ F.contents fr, p.2.state = P.result s a

omit [DecidableEq S] [LE κ] in
/-- Under the invariant, the frontier is not empty while the problem has a solution: the solution
leaves the explored set, which holds no goal state, and the frontier holds a node for the first
unexplored state on it. -/
private theorem ReachInv.contents_ne_zero {R : Finset S} {fr : Q} {E : Finset S}
    (hI : ReachInv P F R fr E) {σ : List A} (hσ : P.IsSolution σ) : F.contents fr ≠ 0 := by
  obtain ⟨t, hσ, ht⟩ := hσ
  have htE : t ∉ E := fun h => by simp [hI.goal t h] at ht
  suffices h : ∀ π u, P.toLTS.MTr u π t → (u ∉ E → ∃ p ∈ F.contents fr, p.2.state = u) →
      F.contents fr ≠ 0 from h σ P.initial hσ hI.root
  intro π
  induction π with
  | nil =>
    intro u hu h
    rw [LTS.MTr.nil_iff] at hu
    subst hu
    obtain ⟨p, hp, -⟩ := h htE
    exact fun h0 => by simp [h0] at hp
  | cons a π ih =>
    intro u hu h
    by_cases huE : u ∈ E
    · rw [Problem.toLTS_mTr_cons_iff] at hu
      exact ih _ hu.2 (hI.succ u huE a hu.1)
    · obtain ⟨p, hp, -⟩ := h huE
      exact fun h0 => by simp [h0] at hp

omit [DecidableEq S] in
private theorem ReachInv.skip (hF : F.Lawful) {R : Finset S} {fr fr' : Q} {E : Finset S}
    (hI : ReachInv P F R fr E) {y : Node S A} (hpop : F.popMin? fr = some (y, fr'))
    (hy : y.state ∈ E) : ReachInv P F R fr' E where
  mem p hp := hI.mem p (hF.mem_of_mem_popMin? hpop hp)
  goal := hI.goal
  root hi := by
    obtain ⟨p, hp, hps⟩ := hI.root hi
    refine ⟨p, hF.mem_popMin?_of_ne hpop hp <| ne_of_apply_ne Node.state <| fun hne => hi ?_, hps⟩
    rwa [← hps, hne]
  succ s hs a ha hv := by
    obtain ⟨p, hp, hps⟩ := hI.succ s hs a ha hv
    refine ⟨p, hF.mem_popMin?_of_ne hpop hp <| ne_of_apply_ne Node.state <| fun hne => hv ?_, hps⟩
    rwa [← hps, hne]

private theorem ReachInv.expand (hF : F.Lawful) (prio : Node S A → κ) {R : Finset S}
    (hR : ∀ s ∈ R, ∀ a ∈ P.actions s, P.result s a ∈ R) {fr fr' : Q} {E : Finset S}
    (hI : ReachInv P F R fr E) {y : Node S A} (hpop : F.popMin? fr = some (y, fr'))
    (hg : P.isGoal y.state = false) :
    ReachInv P F R (Id.run (expandGraphM (fun op => pure (P.oracle 0 op)) F
      (fun z => pure (prio z)) (insert y.state E) y fr')) (insert y.state E) where
  mem p hp := by
    rcases (mem_contents_expandGraphM hF _ _ y fr' p).1 hp with hp | ⟨a, ha, -, rfl⟩
    · exact hI.mem p (hF.mem_of_mem_popMin? hpop hp)
    · obtain ⟨k, hk⟩ := hF.exists_mem_of_popMin? hpop
      exact hR _ (hI.mem _ hk) a ha
  goal s hs := by
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact hg
    · exact hI.goal s hs
  root hi := by
    rw [Finset.mem_insert, not_or] at hi
    obtain ⟨p, hp, hps⟩ := hI.root hi.2
    exact ⟨p, (mem_contents_expandGraphM hF _ _ y fr' p).2
      (Or.inl (hF.mem_popMin?_of_ne hpop hp <| ne_of_apply_ne Node.state <| (hps ▸ hi.1))), hps⟩
  succ s hs a ha hv := by
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact ⟨_, (mem_contents_expandGraphM hF _ _ _ fr' _).2 (Or.inr ⟨a, ha, hv, rfl⟩), rfl⟩
    · rw [Finset.mem_insert, not_or] at hv
      obtain ⟨p, hp, hps⟩ := hI.succ s hs a ha hv.2
      exact ⟨p, (mem_contents_expandGraphM hF _ _ y fr' p).2
        (Or.inl (hF.mem_popMin?_of_ne hpop hp <| ne_of_apply_ne Node.state <| (hps ▸ hv.1))), hps⟩

/-- Under the invariant, with a solution and branching at most `b` on `R`, the loop returns a node
when its fuel is at least the number of frontier elements plus `b` per unexplored state of `R`:
each iteration lowers this measure. -/
private theorem isSome_bestFirstGraphLoopM (hF : F.Lawful) (prio : Node S A → κ) {R : Finset S}
    (hR : ∀ s ∈ R, ∀ a ∈ P.actions s, P.result s a ∈ R) {b : ℕ}
    (hb : ∀ s ∈ R, (P.actions s).length ≤ b) {σ : List A} (hσ : P.IsSolution σ) :
    ∀ (fuel : ℕ) (fr : Q) (E : Finset S), ReachInv P F R fr E →
      Multiset.card (F.contents fr) + b * (R \ E).card ≤ fuel →
      (Id.run (bestFirstGraphLoopM (fun op => pure (P.oracle 0 op)) F (fun z => pure (prio z))
        fuel fr E)).isSome
  | 0, fr, E, hI, hfuel => by
    have := Multiset.card_pos.2 (hI.contents_ne_zero hσ)
    omega
  | fuel + 1, fr, E, hI, hfuel => by
    simp only [bestFirstGraphLoopM]
    split
    · rename_i hpop
      exact absurd ((hF.popMin?_eq_none_iff fr).1 hpop) (hI.contents_ne_zero hσ)
    · rename_i y fr' hpop
      obtain ⟨k, hcont, -⟩ := hF.exists_of_popMin?_eq_some hpop
      rw [hcont, Multiset.card_cons] at hfuel
      split
      · rename_i hyE
        exact isSome_bestFirstGraphLoopM hF prio hR hb hσ fuel fr' E (hI.skip hF hpop hyE)
          (by omega)
      · rename_i hyE
        by_cases hg : P.isGoal y.state = true
        · simp [hg]
        · simp only [Problem.oracle_isGoal, hg]
          refine isSome_bestFirstGraphLoopM hF prio hR hb hσ fuel _ _
            (hI.expand hF prio hR hpop (by simpa using hg)) ?_
          have hyR : y.state ∈ R := hI.mem (k, y) (by rw [hcont]; exact Multiset.mem_cons_self _ _)
          have h₁ := card_contents_foldlM_pushGraphChildM_le hF (P.oracle 0) prio
            (insert y.state E) y (P.actions y.state) fr'
          have h₂ := hb _ hyR
          have h₃ := Finset.card_erase_add_one (Finset.mem_sdiff.2 ⟨hyR, hyE⟩)
          rw [← h₃, Nat.mul_succ] at hfuel
          rw [Finset.sdiff_insert]
          exact le_trans (Nat.add_le_add_right h₁ _) (by omega)

/-- **Completeness of best-first graph search on a finite state space.** If the problem has a
solution, `R` is a finite set of states containing the initial state and closed under
successors, every state of `R` has at most `b` applicable actions, and the fuel is at least
`b * R.card + 1`, then best-first graph search returns a node whose action sequence is a solution,
for every lawful frontier and every node priority. -/
theorem bestFirstGraphSearch_complete (hF : F.Lawful) (prio : Node S A → κ) {R : Finset S}
    (hinit : P.initial ∈ R) (hR : ∀ s ∈ R, ∀ a ∈ P.actions s, P.result s a ∈ R) {b : ℕ}
    (hb : ∀ s ∈ R, (P.actions s).length ≤ b) {σ : List A} (hσ : P.IsSolution σ) {fuel : ℕ}
    (hfuel : b * R.card + 1 ≤ fuel) :
    ∃ x, bestFirstGraphSearch P F prio fuel = some x ∧ P.IsSolution x.path := by
  have hsome : (bestFirstGraphSearch P F prio fuel).isSome := by
    refine isSome_bestFirstGraphLoopM hF prio hR hb hσ fuel _ ∅
      { mem := fun p hp => ?_
        goal := fun _ hs => absurd hs (Finset.notMem_empty _)
        root := fun _ => ⟨_, by rw [hF.contents_insert]; exact Multiset.mem_cons_self _ _, rfl⟩
        succ := fun _ hs => absurd hs (Finset.notMem_empty _) } ?_
    · rw [hF.contents_insert, hF.contents_empty, Multiset.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hinit
      · simp at hp
    · rw [hF.contents_insert, hF.contents_empty, Finset.sdiff_empty]
      simpa [Nat.add_comm] using hfuel
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨hpath, hgoal, -⟩ := bestFirstGraphSearch_sound hF P prio fuel hx
  exact ⟨x, hx, _, hpath, hgoal⟩

end Completeness

/-! ## Optimality of A* graph search under a consistent heuristic -/

section Optimality

variable {P : Problem S A} {h : S → ℕ} {F : Frontier Q ℕ (Node S A)}

section Invariant

omit [DecidableEq S]

/-- The loop invariant of A* graph search: every frontier element is keyed by `g + h`; no explored
state is a goal state; the root is on the frontier while the initial state is unexplored; and for
every explored state `s`, every path `π` to it and every action `a` applicable in `s` leading to an
unexplored state, the frontier holds a node for that state costing at most `c(π) + c(s, a)`. -/
private structure OptInv (P : Problem S A) (h : S → ℕ) (F : Frontier Q ℕ (Node S A)) (fr : Q)
    (E : Finset S) : Prop where
  key : ∀ p ∈ F.contents fr, p.1 = p.2.cost + h p.2.state
  goal : ∀ s ∈ E, P.isGoal s = false
  root : P.initial ∉ E → ∃ p ∈ F.contents fr, p.2.state = P.initial ∧ p.2.cost = 0
  succ : ∀ s ∈ E, ∀ π, P.toLTS.MTr P.initial π s → ∀ a ∈ P.actions s, P.result s a ∉ E →
    ∃ p ∈ F.contents fr, p.2.state = P.result s a ∧
      p.2.cost ≤ P.pathCost P.initial π + P.stepCost s a

private theorem OptInv.exists_le_aux (hc : P.Consistent h) {fr : Q} {E : Finset S}
    (hI : OptInv P h F fr E) {t : S} (ht : t ∉ E) :
    ∀ (π₂ π₁ : List A) (u : S), P.toLTS.MTr P.initial π₁ u → P.toLTS.MTr u π₂ t →
      (u ∉ E → ∃ p ∈ F.contents fr, p.2.state = u ∧ p.2.cost ≤ P.pathCost P.initial π₁) →
      ∃ p ∈ F.contents fr, p.1 ≤ P.pathCost P.initial π₁ + P.pathCost u π₂ + h t
  | [], π₁, u, _, h₂, hu => by
    rw [LTS.MTr.nil_iff] at h₂
    subst h₂
    obtain ⟨p, hp, hps, hpc⟩ := hu ht
    refine ⟨p, hp, ?_⟩
    rw [hI.key p hp, hps]
    simp only [Problem.pathCost_nil]
    omega
  | a :: π₂, π₁, u, h₁, h₂, hu => by
    by_cases huE : u ∈ E
    · rw [Problem.toLTS_mTr_cons_iff] at h₂
      obtain ⟨p, hp, hle⟩ := hI.exists_le_aux hc ht π₂ (π₁ ++ [a]) (P.result u a)
        (LTS.MTr.stepR _ h₁ ⟨h₂.1, rfl⟩) h₂.2 fun hv => by
          obtain ⟨p, hp, hps, hpc⟩ := hI.succ u huE π₁ h₁ a h₂.1 hv
          exact ⟨p, hp, hps, by simpa [P.pathCost_append_of_mTr h₁] using hpc⟩
      refine ⟨p, hp, ?_⟩
      simp only [P.pathCost_append_of_mTr h₁, Problem.pathCost_cons, Problem.pathCost_nil] at hle ⊢
      omega
    · obtain ⟨p, hp, hps, hpc⟩ := hu huE
      refine ⟨p, hp, ?_⟩
      have := hc.le_pathCost_add h₂
      rw [hI.key p hp, hps]
      omega

/-- Under the invariant and a consistent heuristic, every path `π` to an unexplored state `t` has
a frontier element keyed at most `c(π) + h t`. -/
private theorem OptInv.exists_le (hc : P.Consistent h) {fr : Q} {E : Finset S}
    (hI : OptInv P h F fr E) {π : List A} {t : S} (hπ : P.toLTS.MTr P.initial π t)
    (ht : t ∉ E) : ∃ p ∈ F.contents fr, p.1 ≤ P.pathCost P.initial π + h t := by
  obtain ⟨p, hp, hle⟩ := hI.exists_le_aux hc ht π [] P.initial .refl hπ fun hi => by
    obtain ⟨p, hp, hps, hpc⟩ := hI.root hi
    exact ⟨p, hp, hps, by simp [hpc]⟩
  exact ⟨p, hp, by simpa using hle⟩

/-- The popped node has the least key on the frontier. -/
private theorem OptInv.key_le (hF : F.Lawful) {fr fr' : Q} {E : Finset S}
    (hI : OptInv P h F fr E) {y : Node S A} (hpop : F.popMin? fr = some (y, fr'))
    {p : ℕ × Node S A} (hp : p ∈ F.contents fr) : y.cost + h y.state ≤ p.1 := by
  obtain ⟨k, hcont, hmin⟩ := hF.exists_of_popMin?_eq_some hpop
  rw [← hI.key (k, y) (by rw [hcont]; exact Multiset.mem_cons_self _ _)]
  rw [hcont, Multiset.mem_cons] at hp
  rcases hp with rfl | hp
  · exact le_rfl
  · exact hmin p hp

/-- With a consistent heuristic, a popped node whose state is unexplored costs at most every path
to its state. -/
private theorem OptInv.cost_le (hF : F.Lawful) (hc : P.Consistent h) {fr fr' : Q}
    {E : Finset S} (hI : OptInv P h F fr E) {y : Node S A} (hpop : F.popMin? fr = some (y, fr'))
    (hy : y.state ∉ E) {π : List A} (hπ : P.toLTS.MTr P.initial π y.state) :
    y.cost ≤ P.pathCost P.initial π := by
  obtain ⟨p, hp, hle⟩ := hI.exists_le hc hπ hy
  have := hI.key_le hF hpop hp
  omega

private theorem OptInv.skip (hF : F.Lawful) {fr fr' : Q} {E : Finset S}
    (hI : OptInv P h F fr E) {y : Node S A} (hpop : F.popMin? fr = some (y, fr'))
    (hy : y.state ∈ E) : OptInv P h F fr' E where
  key p hp := hI.key p (hF.mem_of_mem_popMin? hpop hp)
  goal := hI.goal
  root hi := by
    obtain ⟨p, hp, hps, hpc⟩ := hI.root hi
    refine ⟨p, hF.mem_popMin?_of_ne hpop hp <| ne_of_apply_ne Node.state <| fun hne => hi ?_,
      hps, hpc⟩
    rwa [← hps, hne]
  succ s hs π hπ a ha hv := by
    obtain ⟨p, hp, hps, hpc⟩ := hI.succ s hs π hπ a ha hv
    refine ⟨p, hF.mem_popMin?_of_ne hpop hp <| ne_of_apply_ne Node.state <| fun hne => hv ?_,
      hps, hpc⟩
    rwa [← hps, hne]

end Invariant

private theorem OptInv.expand (hF : F.Lawful) (hc : P.Consistent h) {fr fr' : Q}
    {E : Finset S} (hI : OptInv P h F fr E) {y : Node S A} (hpop : F.popMin? fr = some (y, fr'))
    (hy : y.state ∉ E) (hg : P.isGoal y.state = false) :
    OptInv P h F (Id.run (expandGraphM (fun op => pure (P.oracle 0 op)) F
      (fun z => pure (z.cost + h z.state)) (insert y.state E) y fr')) (insert y.state E) where
  key p hp := by
    rcases (mem_contents_expandGraphM hF _ _ y fr' p).1 hp with hp | ⟨a, -, -, rfl⟩
    · exact hI.key p (hF.mem_of_mem_popMin? hpop hp)
    · rfl
  goal s hs := by
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact hg
    · exact hI.goal s hs
  root hi := by
    rw [Finset.mem_insert, not_or] at hi
    obtain ⟨p, hp, hps, hpc⟩ := hI.root hi.2
    exact ⟨p, (mem_contents_expandGraphM hF _ _ y fr' p).2
      (Or.inl (hF.mem_popMin?_of_ne hpop hp <| ne_of_apply_ne Node.state <| (hps ▸ hi.1))),
        hps, hpc⟩
  succ s hs π hπ a ha hv := by
    rcases Finset.mem_insert.1 hs with rfl | hs
    · refine ⟨_, (mem_contents_expandGraphM hF _ _ _ fr' _).2 (Or.inr ⟨a, ha, hv, rfl⟩), rfl, ?_⟩
      have := hI.cost_le hF hc hpop hy hπ
      simp only
      omega
    · rw [Finset.mem_insert, not_or] at hv
      obtain ⟨p, hp, hps, hpc⟩ := hI.succ s hs π hπ a ha hv.2
      exact ⟨p, (mem_contents_expandGraphM hF _ _ y fr' p).2
        (Or.inl (hF.mem_popMin?_of_ne hpop hp <| ne_of_apply_ne Node.state <| (hps ▸ hv.1))),
        hps, hpc⟩

/-- **Cost-optimality of A\* graph search** ([RussellNorvig2020], §3.5.2;
[HartNilssonRaphael1968]). With a consistent heuristic, for every lawful frontier and every
amount of fuel, the action sequence of a node returned by A\* graph search is an optimal
solution: a solution whose path cost is at most that of every solution. -/
theorem aStarGraphSearch_isOptimalSolution (hF : F.Lawful) (hc : P.Consistent h) (fuel : ℕ)
    {x : Node S A} (hx : aStarGraphSearch P h F fuel = some x) : P.IsOptimalSolution x.path := by
  obtain ⟨hpath, hgoal, hcost⟩ := bestFirstGraphSearch_sound hF P _ fuel hx
  obtain ⟨fr, E, fr', hI, hpop, hxE, -⟩ := exists_of_bestFirstGraphLoopM_eq_some (P := P)
    (fun z => z.cost + h z.state) (OptInv P h F)
    (fun hI hpop hy => hI.skip hF hpop hy) (fun hI hpop hy hg => hI.expand hF hc hpop hy hg)
    fuel _ ∅
    { key := fun p hp => by
        rw [hF.contents_insert, hF.contents_empty, Multiset.mem_cons] at hp
        rcases hp with rfl | hp
        · rfl
        · simp at hp
      goal := fun _ hs => absurd hs (Finset.notMem_empty _)
      root := fun _ => ⟨_, by rw [hF.contents_insert]; exact Multiset.mem_cons_self _ _, rfl, rfl⟩
      succ := fun _ hs => absurd hs (Finset.notMem_empty _) } hx
  refine ⟨⟨_, hpath, hgoal⟩, fun σ ⟨t, hσ, ht⟩ => ?_⟩
  have htE : t ∉ E := fun htE => by simp [hI.goal t htE] at ht
  obtain ⟨p, hp, hle⟩ := hI.exists_le hc hσ htE
  have := hI.key_le hF hpop hp
  rw [hc.eq_zero_of_isGoal t ht] at hle
  omega

/-- **A\* graph search is complete and cost-optimal on a finite state space**
([RussellNorvig2020], §3.5.2). With a consistent heuristic, if the problem has a solution, `R` is
a finite set of states containing the initial state and closed under successors, every state of
`R` has at most `b` applicable actions, and the fuel is at least `b * R.card + 1`, then A\* graph
search returns a node whose action sequence is an optimal solution. -/
theorem aStarGraphSearch_complete (hF : F.Lawful) (hc : P.Consistent h) {R : Finset S}
    (hinit : P.initial ∈ R) (hR : ∀ s ∈ R, ∀ a ∈ P.actions s, P.result s a ∈ R) {b : ℕ}
    (hb : ∀ s ∈ R, (P.actions s).length ≤ b) {σ : List A} (hσ : P.IsSolution σ) {fuel : ℕ}
    (hfuel : b * R.card + 1 ≤ fuel) :
    ∃ x, aStarGraphSearch P h F fuel = some x ∧ P.IsOptimalSolution x.path := by
  obtain ⟨x, hx, -⟩ := bestFirstGraphSearch_complete hF _ hinit hR hb hσ hfuel
  exact ⟨x, hx, aStarGraphSearch_isOptimalSolution hF hc fuel hx⟩

/-- **Cost-optimality of uniform-cost graph search** ([RussellNorvig2020], §3.4.2). For every
lawful frontier and every amount of fuel, the action sequence of a node returned by best-first
graph search with the path cost `g` as priority is an optimal solution. This is A\* graph search
with the consistent heuristic `0`. -/
theorem uniformCostGraphSearch_isOptimalSolution (hF : F.Lawful) (fuel : ℕ) {x : Node S A}
    (hx : bestFirstGraphSearch P F (·.cost) fuel = some x) : P.IsOptimalSolution x.path :=
  aStarGraphSearch_isOptimalSolution (h := fun _ => 0) hF
    ⟨fun _ _ _ => Nat.zero_le _, fun _ _ => rfl⟩ fuel hx

end Optimality

/-! ## Expansions -/

section Cost

variable {F : Frontier Q κ (Node S A)} (oracle : {ι : Type} → SearchQuery S A ι → ι)

/-- Under a weight charging no `result` or `stepCost` query, and a priority costing nothing,
expanding a node costs exactly the weight of its `actions` query. -/
private theorem cost_expandGraphM (w : {ι : Type} → SearchQuery S A ι → ℕ)
    (hresult : ∀ s a, w (.result s a) = 0) (hstepCost : ∀ s a, w (.stepCost s a) = 0)
    (prio : Node S A → FreeM (SearchQuery S A) κ) (hprio : ∀ x, (prio x).cost oracle w = 0)
    (E : Finset S) (x : Node S A) (fr : Q) :
    (expandGraphM FreeM.lift F prio E x fr).cost oracle w = w (.actions x.state) := by
  simp only [expandGraphM, FreeM.cost_bind, FreeM.cost_lift, FreeM.eval_lift]
  suffices h : ∀ (acts : List A) (fr : Q),
      (acts.foldlM (pushGraphChildM FreeM.lift F prio E x) fr).cost oracle w = 0 by
    rw [h, add_zero]
  intro acts
  induction acts with
  | nil => intro fr; rfl
  | cons a acts ih =>
    intro fr
    simp only [List.foldlM_cons, FreeM.cost_bind, ih, add_zero, pushGraphChildM, FreeM.cost_lift,
      hresult, zero_add, FreeM.eval_lift]
    by_cases hmem : oracle (.result x.state a) ∈ E <;> simp [hmem, hstepCost, hprio]

/-- The expansion cost of the loop under a potential: if every expansion of a state satisfying
`R` and not yet explored costs at most the drop of the potential `Φ` of the explored set, and
popped states satisfy `R` (tracked by the frontier invariant `J`), the loop costs at most the
potential of the initial explored set. -/
private theorem cost_bestFirstGraphLoopM_le (w : {ι : Type} → SearchQuery S A ι → ℕ)
    (hresult : ∀ s a, w (.result s a) = 0) (hstepCost : ∀ s a, w (.stepCost s a) = 0)
    (hisGoal : ∀ s, w (.isGoal s) = 0)
    (prio : Node S A → FreeM (SearchQuery S A) κ) (hprio : ∀ x, (prio x).cost oracle w = 0)
    (R : S → Prop) (J : Q → Prop)
    (hpop : ∀ {fr y fr'}, J fr → F.popMin? fr = some (y, fr') → R y.state ∧ J fr')
    (hexpand : ∀ {y fr'} (E : Finset S), R y.state → J fr' →
      J ((expandGraphM FreeM.lift F prio E y fr').eval oracle))
    (Φ : Finset S → ℕ) (hΦ : ∀ E s, R s → s ∉ E → w (.actions s) + Φ (insert s E) ≤ Φ E) :
    ∀ (fuel : ℕ) (fr : Q) (E : Finset S), J fr →
      (bestFirstGraphLoopM FreeM.lift F prio fuel fr E).cost oracle w ≤ Φ E
  | 0, _, _, _ => by simp [bestFirstGraphLoopM]
  | fuel + 1, fr, E, hJ => by
    simp only [bestFirstGraphLoopM]
    split
    · simp
    · rename_i y fr' hp
      obtain ⟨hR, hJ'⟩ := hpop hJ hp
      split
      · exact cost_bestFirstGraphLoopM_le w hresult hstepCost hisGoal prio hprio R J hpop hexpand
          Φ hΦ fuel fr' E hJ'
      · rename_i hyE
        simp only [FreeM.cost_bind, FreeM.cost_lift, hisGoal, zero_add]
        split
        · simp
        · rw [FreeM.cost_bind, cost_expandGraphM oracle w hresult hstepCost prio hprio]
          exact (Nat.add_le_add_left (cost_bestFirstGraphLoopM_le w hresult hstepCost hisGoal
            prio hprio R J hpop hexpand Φ hΦ fuel _ _ (hexpand _ hR hJ')) _).trans
            (hΦ E y.state hR hyE)

/-- **Every state is expanded at most once.** In the query model, for every oracle, every state
`s₀`, every frontier, every priority whose computation does not expand `s₀` (for instance any pure
priority, or A\*'s priority asking for the heuristic) and every amount of fuel, best-first graph
search asks for the actions of `s₀` at most once: its cost under the weight
`SearchQuery.expansionWeightAt s₀` is at most `1`. The count needs no hypothesis on the
heuristic, since the explored set rules out a second expansion; consistency is what makes A\*
graph search, which never reopens a state, optimal (`aStarGraphSearch_isOptimalSolution`). -/
theorem cost_expansionWeightAt_bestFirstGraphSearchQ_le_one (s₀ : S)
    (prio : Node S A → FreeM (SearchQuery S A) κ)
    (hprio : ∀ x, (prio x).cost oracle (SearchQuery.expansionWeightAt s₀) = 0) (fuel : ℕ)
    (init : S) :
    (bestFirstGraphSearchQ F prio fuel init).cost oracle (SearchQuery.expansionWeightAt s₀) ≤
      1 := by
  simp only [bestFirstGraphSearchQ, bestFirstGraphSearchM, FreeM.cost_bind, hprio, zero_add]
  refine (cost_bestFirstGraphLoopM_le oracle (SearchQuery.expansionWeightAt s₀) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) prio hprio (fun _ => True) (fun _ => True)
    (fun _ _ => ⟨trivial, trivial⟩) (fun _ _ _ => trivial) (fun E => if s₀ ∈ E then 0 else 1)
    (fun E s _ hs => ?_) fuel _ ∅ trivial).trans (by simp)
  by_cases h : s = s₀
  · subst h
    simp [SearchQuery.expansionWeightAt, hs]
  · simp [SearchQuery.expansionWeightAt, h, Finset.mem_insert, Ne.symm h]

/-- **Expansion bound for graph search.** In the query model, for every oracle, every lawful
frontier, every priority whose computation expands nothing and every amount of fuel, best-first
graph search from `init` expands at most `R.card` nodes, for every finite set of states `R`
containing `init` and closed under the oracle's successors. For a `Fintype` state space `R` can be
`Finset.univ`; in general it can be the set of states reachable from `init` when that is finite. -/
theorem cost_expansionWeight_bestFirstGraphSearchQ_le_card [LE κ] (hF : F.Lawful)
    (prio : Node S A → FreeM (SearchQuery S A) κ)
    (hprio : ∀ x, (prio x).cost oracle SearchQuery.expansionWeight = 0) (R : Finset S)
    {init : S} (hinit : init ∈ R)
    (hR : ∀ s ∈ R, ∀ a ∈ oracle (.actions s), oracle (.result s a) ∈ R) (fuel : ℕ) :
    (bestFirstGraphSearchQ F prio fuel init).cost oracle SearchQuery.expansionWeight ≤
      R.card := by
  simp only [bestFirstGraphSearchQ, bestFirstGraphSearchM, FreeM.cost_bind, hprio, zero_add]
  refine (cost_bestFirstGraphLoopM_le oracle SearchQuery.expansionWeight (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) prio hprio (· ∈ R)
    (fun fr => ∀ p ∈ F.contents fr, p.2.state ∈ R) (fun {fr y fr'} hJ hpop => ?_)
    (fun {y fr'} E hy hJ => ?_) (fun E => (R \ E).card) (fun E s hs hsE => ?_) fuel _ ∅
    ?_).trans (by simp)
  · obtain ⟨k, hk⟩ := hF.exists_mem_of_popMin? hpop
    exact ⟨hJ (k, y) hk, fun p hp => hJ p (hF.mem_of_mem_popMin? hpop hp)⟩
  · intro p hp
    have heval : (expandGraphM FreeM.lift F prio E y fr').eval oracle =
        Id.run (expandGraphM (fun op => pure (oracle op)) F
          (fun x => pure ((prio x).eval oracle)) E y fr') :=
      congrArg Id.run ((FreeM.isMonadHom_pure_eval oracle).map_expandGraphM FreeM.lift F prio E
        y fr')
    rw [heval] at hp
    rcases (mem_contents_foldlM_pushGraphChildM hF oracle _ E y p _ fr').1 hp with
      hp | ⟨a, ha, -, rfl⟩
    · exact hJ p hp
    · exact hR _ hy a ha
  · have := Finset.card_erase_add_one (Finset.mem_sdiff.2 ⟨hs, hsE⟩)
    simp only [SearchQuery.expansionWeight, Finset.sdiff_insert]
    omega
  · intro p hp
    rw [hF.contents_insert, hF.contents_empty, Multiset.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hinit
    · simp at hp

end Cost

end Cslib.Algorithms.Lean.Search
