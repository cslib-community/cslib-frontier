/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Search.BestFirst
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.OrderDual
import Cslib.Foundations.Control.Monad.IsMonadHom.List
import CslibFrontier.Algorithms.Lean.Query.FreeM.LiftM
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Multiset.Basic

/-!
# Uninformed search

Breadth-first, depth-limited and iterative deepening search ([RussellNorvig2020], §3.4) as
instances of best-first tree search (`Cslib.Algorithms.Lean.Search.bestFirstTreeSearch`), with
their completeness and optimality in the number of actions, and their expansion counts in the
query model.

* **Breadth-first search** is best-first search whose priority is the depth of a node, the number
  of actions on its path, as the textbook observes (§3.4.1). It is an abbreviation, so the
  soundness, evaluation and cost theorems of best-first search apply to it verbatim.
* **Depth-limited search** with limit `ℓ` (§3.4.4) is best-first search on the depth-limited
  problem `Problem.depthLimited P ℓ`, whose states carry their depth and have no actions at depth
  `ℓ`, with the depth-first priority (the negative depth, as a key in `ℕᵒᵈ`, §3.4.3). Its query
  program asks `P`'s queries through `SearchQuery.depthLimit`, which answers an `actions` query at
  the depth limit by `[]` without asking, so a node at the limit is not expanded.
* **Iterative deepening search** (§3.4.4) runs depth-limited search with the limits
  `0, 1, …, maxDepth` and returns the first answer.

These are tree-like searches: they do not detect repeated states, and depth-limited search does
not check for cycles along a path. Each search takes a frontier and is correct for every lawful
one; the theorems do not depend on how a frontier breaks ties between equal keys.

Completeness is proved by a potential argument. If `sol` is a solution, the frontier always holds
a node whose path is a prefix of `sol`; a node of depth at most `D` carries the potential
`∑ i < D + 1 - depth, b ^ i`, the number of nodes of depth at most `D` below it in a `b`-ary tree,
and each expansion of such a node strictly decreases the total potential of the frontier. For
breadth-first search, with `D = sol.length`, every popped node has depth at most `D` because the
frontier holds a node no deeper than that; for depth-limited search, with `D = ℓ`, every node has
depth at most `ℓ`.

## Main definitions

* `Problem.depthLimited`: the problem with depth-annotated states and no actions at depth `ℓ`.
* `breadthFirstTreeSearch`, `breadthFirstTreeSearchQ`: breadth-first tree search.
* `SearchQuery.depthLimit`: the depth-limited problem's queries answered through `P`'s.
* `depthLimitedSearchM`, `depthLimitedSearch`, `depthLimitedSearchQ`: depth-limited search.
* `iterativeDeepeningSearchM`, `iterativeDeepeningSearch`, `iterativeDeepeningSearchQ`:
  iterative deepening search.

## Main results

* `breadthFirstTreeSearch_length_le`: breadth-first search returns a solution with the fewest
  actions, for any fuel.
* `breadthFirstTreeSearch_complete`: with branching factor at most `b` and a solution of `d`
  actions, breadth-first search with fuel `∑ i ≤ d, b ^ i` returns a shortest solution.
* `depthLimitedSearch_sound`, `depthLimitedSearch_complete`: depth-limited search with limit `ℓ`
  returns only solutions of at most `ℓ` actions, and returns one with fuel `∑ i ≤ ℓ, b ^ i` when
  one exists.
* `iterativeDeepeningSearch_sound`, `iterativeDeepeningSearch_complete`: iterative deepening search
  returns only solutions, and returns a shortest one when a solution of `d ≤ maxDepth` actions
  exists and the fuel is at least `∑ i ≤ d, b ^ i`.
* `eval_depthLimitedSearchQ`, `eval_iterativeDeepeningSearchQ`: the query programs evaluate to the
  pure algorithms.
* `cost_expansionWeight_depthLimitedSearchQ_le`: depth-limited search expands at most
  `∑ i < ℓ, b ^ i` nodes, whatever the fuel.
* `cost_expansionWeight_iterativeDeepeningSearchQ_le`: iterative deepening search expands at most
  `∑ ℓ ≤ maxDepth, ∑ i < ℓ, b ^ i` nodes.

## References

* [RussellNorvig2020]
-/

public section

namespace Cslib.Algorithms.Lean.Search

variable {m : Type → Type*} [Monad m] {S A Q : Type}

/-! ## The depth-limited problem -/

/-- The depth-limited version of a problem: states carry their depth, the number of actions taken
from the initial state, and states at depth `ℓ` or more have no actions, as depth-limited search
treats nodes at the depth limit as having no successors ([RussellNorvig2020], §3.4.4). -/
@[expose] def Problem.depthLimited (P : Problem S A) (ℓ : ℕ) : Problem (S × ℕ) A where
  initial := (P.initial, 0)
  actions p := if p.2 < ℓ then P.actions p.1 else []
  result p a := (P.result p.1 a, p.2 + 1)
  isGoal p := P.isGoal p.1
  stepCost p a := P.stepCost p.1 a

namespace Problem

variable (P : Problem S A) (ℓ : ℕ)

@[simp] theorem depthLimited_initial : (P.depthLimited ℓ).initial = (P.initial, 0) := rfl

@[simp] theorem depthLimited_actions (p : S × ℕ) :
    (P.depthLimited ℓ).actions p = if p.2 < ℓ then P.actions p.1 else [] := rfl

@[simp] theorem depthLimited_result (p : S × ℕ) (a : A) :
    (P.depthLimited ℓ).result p a = (P.result p.1 a, p.2 + 1) := rfl

@[simp] theorem depthLimited_isGoal (p : S × ℕ) : (P.depthLimited ℓ).isGoal p = P.isGoal p.1 :=
  rfl

@[simp] theorem depthLimited_stepCost (p : S × ℕ) (a : A) :
    (P.depthLimited ℓ).stepCost p a = P.stepCost p.1 a := rfl

/-- A path of the depth-limited problem from depth `d ≤ ℓ` is a path of the problem that ends at
depth `d + as.length ≤ ℓ`. -/
theorem depthLimited_mTr_iff {s : S} {d : ℕ} {as : List A} {t : S × ℕ} (hd : d ≤ ℓ) :
    (P.depthLimited ℓ).toLTS.MTr (s, d) as t ↔
      P.toLTS.MTr s as t.1 ∧ t.2 = d + as.length ∧ d + as.length ≤ ℓ := by
  induction as generalizing s d with
  | nil =>
    simp only [LTS.MTr.nil_iff, List.length_nil, Nat.add_zero, hd, and_true]
    exact ⟨fun h => by subst h; simp, fun ⟨h1, h2⟩ => Prod.ext h1 h2.symm⟩
  | cons a as ih =>
    rw [toLTS_mTr_cons_iff, toLTS_mTr_cons_iff, depthLimited_actions, depthLimited_result]
    by_cases h : d < ℓ
    · simp only [h, ite_true, ih (Nat.succ_le_of_lt h), List.length_cons]
      constructor
      · rintro ⟨ha, hm, he, hl⟩
        exact ⟨⟨ha, hm⟩, by omega, by omega⟩
      · rintro ⟨⟨ha, hm⟩, he, hl⟩
        exact ⟨ha, hm, by omega, by omega⟩
    · simp only [h, ite_false, List.not_mem_nil, false_and, List.length_cons, false_iff, not_and]
      omega

/-- The solutions of the depth-limited problem are the solutions of at most `ℓ` actions. -/
theorem depthLimited_isSolution_iff {as : List A} :
    (P.depthLimited ℓ).IsSolution as ↔ P.IsSolution as ∧ as.length ≤ ℓ := by
  simp only [IsSolution]
  constructor
  · rintro ⟨t, ht, hg⟩
    rw [depthLimited_initial, depthLimited_mTr_iff P ℓ (Nat.zero_le _)] at ht
    exact ⟨⟨t.1, ht.1, hg⟩, by simpa using ht.2.2⟩
  · rintro ⟨⟨t, ht, hg⟩, hl⟩
    refine ⟨(t, as.length), ?_, hg⟩
    rw [depthLimited_initial, depthLimited_mTr_iff P ℓ (Nat.zero_le _)]
    simpa using ⟨ht, hl⟩

/-- Path costs in the depth-limited problem are those of the problem. -/
@[simp] theorem depthLimited_pathCost (p : S × ℕ) (as : List A) :
    (P.depthLimited ℓ).pathCost p as = P.pathCost p.1 as := by
  induction as generalizing p with
  | nil => rfl
  | cons a as ih => simp [ih]

end Problem

/-! ## Frontier invariants of best-first search -/

section Invariants

variable {κ : Type} {F : Frontier Q κ (Node S A)} {P : Problem S A}
  {prio : Node S A → κ}

/-- If `y` is reached and its path is a proper prefix of a solution, the solution continues with
an action applicable at `y`. -/
private theorem exists_child_prefix {y : Node S A} (hy : P.toLTS.MTr P.initial y.path y.state)
    {sol : List A} (hsol : P.IsSolution sol) (hpre : y.path <+: sol)
    (hg : P.isGoal y.state = false) : ∃ a ∈ P.actions y.state, y.path ++ [a] <+: sol := by
  obtain ⟨t, ht, htg⟩ := hsol
  obtain ⟨rest, rfl⟩ := hpre
  rcases rest with _ | ⟨a, rest⟩
  · rw [List.append_nil] at ht
    rw [LTS.Deterministic.eq_of_mTr hy ht, htg] at hg
    exact absurd hg (by simp)
  · obtain ⟨u, hu, hut⟩ := LTS.MTr.split ht
    rw [← LTS.Deterministic.eq_of_mTr hy hu, Problem.toLTS_mTr_cons_iff] at hut
    exact ⟨a, hut.1, rest, by simp⟩

/-- The potential `∑ i < D + 1 - depth, b ^ i` (the number of nodes of depth at most `D` in a
`b`-ary tree below a node) strictly decreases when a node of depth at most `D` is replaced by its
children, if every state has at most `b` actions. -/
private theorem sum_children_lt {b D : ℕ} (hb : ∀ s, (P.actions s).length ≤ b) (y : Node S A)
    (hy : y.path.length ≤ D) :
    ((P.keyedChildren prio y).map fun p =>
        ∑ i ∈ Finset.range (D + 1 - p.2.path.length), b ^ i).sum <
      ∑ i ∈ Finset.range (D + 1 - y.path.length), b ^ i := by
  have hD : D + 1 - y.path.length = (D - y.path.length) + 1 := by omega
  simp only [Problem.keyedChildren, Multiset.map_coe, Multiset.sum_coe, List.map_map,
    Function.comp_def, List.length_append, List.length_singleton, hD, geom_sum_succ]
  have : D + 1 - (y.path.length + 1) = D - y.path.length := by omega
  simp only [this, List.map_const', List.sum_replicate, smul_eq_mul]
  have := hb y.state
  have := Nat.mul_le_mul_right (∑ i ∈ Finset.range (D - y.path.length), b ^ i) this
  omega

/-- The geometric sum `∑ i < n, b ^ i` is positive when `n` is. -/
private theorem geom_sum_pos {b n : ℕ} (hn : 0 < n) : 0 < ∑ i ∈ Finset.range n, b ^ i := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [geom_sum_succ]
  omega

/-- The invariant of a search towards the solution `sol`: every node on the frontier is reached
by its path, and the path of some node on the frontier is a prefix of `sol`. -/
private def PrefixInv (P : Problem S A) (sol : List A) (M : Multiset (κ × Node S A)) : Prop :=
  (∀ p ∈ M, P.toLTS.MTr P.initial p.2.path p.2.state) ∧ ∃ p ∈ M, p.2.path <+: sol

/-- The frontier holding only the root satisfies `PrefixInv`. -/
private theorem PrefixInv.root [LE κ] (hF : F.Lawful) (sol : List A) (k : κ) :
    PrefixInv P sol (F.contents (F.insert k ⟨P.initial, [], 0⟩ F.empty)) := by
  rw [hF.contents_insert, hF.contents_empty]
  refine ⟨fun p hp => ?_, ⟨_, Multiset.mem_cons_self _ _, List.nil_prefix⟩⟩
  simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hp
  subst hp
  exact .refl

/-- Expanding a non-goal node preserves `PrefixInv`. -/
private theorem PrefixInv.step {sol : List A} (hsol : P.IsSolution sol)
    {M : Multiset (κ × Node S A)} {k : κ} {y : Node S A} (h : PrefixInv P sol ((k, y) ::ₘ M))
    (hg : P.isGoal y.state = false) :
    PrefixInv P sol (P.keyedChildren prio y + M) := by
  obtain ⟨hall, p, hp, hpre⟩ := h
  have hy := hall _ (Multiset.mem_cons_self _ _)
  refine ⟨fun q hq => ?_, ?_⟩
  · rcases Multiset.mem_add.1 hq with hq | hq
    · obtain ⟨a, ha, rfl⟩ := Problem.mem_keyedChildren_iff.1 hq
      exact LTS.MTr.stepR _ hy ⟨ha, rfl⟩
    · exact hall q (Multiset.mem_cons_of_mem hq)
  · rcases Multiset.mem_cons.1 hp with rfl | hp
    · obtain ⟨a, ha, hpre'⟩ := exists_child_prefix hy hsol hpre hg
      exact ⟨_, Multiset.mem_add.2 (Or.inl (Problem.mem_keyedChildren_iff.2 ⟨a, ha, rfl⟩)),
        hpre'⟩
    · exact ⟨p, Multiset.mem_add.2 (Or.inr hp), hpre⟩

/-- Under `PrefixInv`, the potential of `sum_children_lt` with `D ≥ sol.length` is positive. -/
private theorem PrefixInv.pos {sol : List A} {M : Multiset (κ × Node S A)}
    (h : PrefixInv P sol M) {b D : ℕ} (hD : sol.length ≤ D) :
    0 < (M.map fun p => ∑ i ∈ Finset.range (D + 1 - p.2.path.length), b ^ i).sum := by
  obtain ⟨-, p, hp, hpre⟩ := h
  have hpos : 0 < ∑ i ∈ Finset.range (D + 1 - p.2.path.length), b ^ i :=
    geom_sum_pos (by have := hpre.length_le; omega)
  exact lt_of_lt_of_le hpos (Multiset.le_sum_of_mem (Multiset.mem_map_of_mem
    (fun p : κ × Node S A => ∑ i ∈ Finset.range (D + 1 - p.2.path.length), b ^ i) hp))

end Invariants

/-! ## Breadth-first search -/

/-- Breadth-first tree search ([RussellNorvig2020], §3.4.1): best-first tree search whose
priority is the depth of a node, the number of actions on its path, so that a node of least depth
is popped first. The textbook observes that breadth-first search is best-first search with this
evaluation function; its own breadth-first search applies the goal test on generation and keeps a
reached table, whereas this tree-like version tests on removal, like `bestFirstTreeSearch`. The
order among nodes of equal depth is the frontier's: the sorted-list frontier pops the most
recently inserted first, so within one depth level the order is not that of a FIFO queue, but no
result here depends on it. -/
abbrev breadthFirstTreeSearch (P : Problem S A) (F : Frontier Q ℕ (Node S A)) (fuel : ℕ) :
    Option (Node S A) :=
  bestFirstTreeSearch P F (·.path.length) fuel

/-- Breadth-first tree search from `init` as a query program on the search interface. Its
evaluation against a problem's oracle is `breadthFirstTreeSearch` (`eval_bestFirstTreeSearchQ`),
and its expansion and generation counts are bounded by
`cost_expansionWeight_bestFirstTreeSearchQ_le` and
`cost_generationWeight_bestFirstTreeSearchQ_le`. -/
abbrev breadthFirstTreeSearchQ (F : Frontier Q ℕ (Node S A)) (fuel : ℕ) (init : S) :
    FreeM (SearchQuery S A) (Option (Node S A)) :=
  bestFirstTreeSearchQ F (fun x => pure x.path.length) fuel init

section BreadthFirst

variable {F : Frontier Q ℕ (Node S A)}

/-- The invariant of breadth-first search towards `sol`: `PrefixInv`, and every node on the
frontier is keyed by its depth. -/
private def BFSInv (P : Problem S A) (sol : List A) (M : Multiset (ℕ × Node S A)) : Prop :=
  PrefixInv P sol M ∧ ∀ p ∈ M, p.1 = p.2.path.length

/-- A node of minimum key on a frontier satisfying `BFSInv` is no deeper than `sol`. -/
private theorem BFSInv.depth_le {P : Problem S A} {sol : List A} {M : Multiset (ℕ × Node S A)}
    {k : ℕ} {y : Node S A} (h : BFSInv P sol ((k, y) ::ₘ M)) (hmin : ∀ p ∈ M, k ≤ p.1) :
    y.path.length ≤ sol.length := by
  obtain ⟨⟨-, p, hp, hpre⟩, hkey⟩ := h
  have hk := hkey _ (Multiset.mem_cons_self _ _)
  have := hpre.length_le
  rcases Multiset.mem_cons.1 hp with rfl | hp
  · exact this
  · have := hmin p hp
    have := hkey p (Multiset.mem_cons_of_mem hp)
    simp only at hk
    omega

private theorem BFSInv.step {P : Problem S A} {sol : List A} (hsol : P.IsSolution sol)
    {M : Multiset (ℕ × Node S A)} {k : ℕ} {y : Node S A} (h : BFSInv P sol ((k, y) ::ₘ M))
    (hg : P.isGoal y.state = false) : BFSInv P sol (P.keyedChildren (·.path.length) y + M) := by
  refine ⟨h.1.step hsol hg, fun p hp => ?_⟩
  rcases Multiset.mem_add.1 hp with hp | hp
  · obtain ⟨a, -, rfl⟩ := Problem.mem_keyedChildren_iff.1 hp
    rfl
  · exact h.2 p (Multiset.mem_cons_of_mem hp)

private theorem BFSInv.root (hF : F.Lawful) (P : Problem S A) (sol : List A) :
    BFSInv P sol (F.contents (F.insert ([] : List A).length ⟨P.initial, [], 0⟩ F.empty)) := by
  refine ⟨PrefixInv.root hF sol _, fun p hp => ?_⟩
  simp only [hF.contents_insert, hF.contents_empty, Multiset.mem_cons, Multiset.notMem_zero,
    or_false] at hp
  subst hp
  rfl

/-- **Breadth-first search returns a shortest solution.** Whatever breadth-first tree search
returns has no more actions than any solution, for every lawful frontier and every amount of
fuel, with no finiteness assumption; together with `bestFirstTreeSearch_sound`, its answer is a
solution with the fewest actions ([RussellNorvig2020], §3.4.1, where breadth-first search is
cost-optimal for problems whose actions all have the same cost). -/
theorem breadthFirstTreeSearch_length_le (hF : F.Lawful) (P : Problem S A) (fuel : ℕ)
    {x : Node S A} (h : breadthFirstTreeSearch P F fuel = some x) {sol : List A}
    (hsol : P.IsSolution sol) : x.path.length ≤ sol.length := by
  obtain ⟨k, M, hinv, hmin, -⟩ := bestFirstLoopM_inv hF (BFSInv P sol)
    (fun _ _ _ hinv _ hg => hinv.step hsol hg) fuel _ (BFSInv.root hF P sol) h
  exact hinv.depth_le hmin

/-- **Completeness of breadth-first search.** If the problem has a solution `sol` and every
state has at most `b` actions, then breadth-first tree search with fuel at least
`∑ i ≤ sol.length, b ^ i` (the number of nodes of depth at most `sol.length` in a `b`-ary tree)
returns a solution with the fewest actions, for every lawful frontier ([RussellNorvig2020],
§3.4.1: breadth-first search is complete when the branching factor is finite, and it generates
`O(b ^ d)` nodes for a shallowest solution at depth `d`). -/
theorem breadthFirstTreeSearch_complete (hF : F.Lawful) {P : Problem S A} {b : ℕ}
    (hb : ∀ s, (P.actions s).length ≤ b) {sol : List A} (hsol : P.IsSolution sol) {fuel : ℕ}
    (hfuel : ∑ i ∈ Finset.range (sol.length + 1), b ^ i ≤ fuel) :
    ∃ x, breadthFirstTreeSearch P F fuel = some x ∧ P.IsSolution x.path ∧
      ∀ sol', P.IsSolution sol' → x.path.length ≤ sol'.length := by
  have hsome : (breadthFirstTreeSearch P F fuel).isSome :=
    isSome_bestFirstLoopM hF (BFSInv P sol)
      (fun y => ∑ i ∈ Finset.range (sol.length + 1 - y.path.length), b ^ i)
      (fun _ h => h.1.pos le_rfl)
      (fun _ _ y hinv hmin hg => ⟨hinv.step hsol hg, sum_children_lt hb y (hinv.depth_le hmin)⟩)
      fuel _ (BFSInv.root hF P sol)
      (by rw [hF.contents_insert, hF.contents_empty]; simpa using hfuel)
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨hm, hg, -⟩ := bestFirstTreeSearch_sound hF P _ fuel hx
  exact ⟨x, hx, ⟨x.state, hm, hg⟩, fun _ => breadthFirstTreeSearch_length_le hF P fuel hx⟩

end BreadthFirst

/-! ## Depth-limited search -/

/-- Apply a function to the state of a node, keeping its path and cost. -/
@[expose] def Node.mapState {T : Type} (f : S → T) (x : Node S A) : Node T A :=
  ⟨f x.state, x.path, x.cost⟩

/-- The interpretation of the queries of the depth-limited problem `P.depthLimited ℓ` induced by
an interpretation `q` of the queries of `P`: an `actions` query at depth `ℓ` or more is answered
by `[]` without consulting `q`, so a node at the depth limit costs no expansion; every other query
is passed to `q` on the state component, and `result` increments the depth. -/
@[expose] def SearchQuery.depthLimit (ℓ : ℕ) (q : {ι : Type} → SearchQuery S A ι → m ι) :
    {ι : Type} → SearchQuery (S × ℕ) A ι → m ι
  | _, .actions p => if p.2 < ℓ then q (.actions p.1) else pure []
  | _, .result p a => (·, p.2 + 1) <$> q (.result p.1 a)
  | _, .isGoal p => q (.isGoal p.1)
  | _, .stepCost p a => q (.stepCost p.1 a)
  | _, .heuristic p => q (.heuristic p.1)

/-- Depth-limited search with limit `ℓ` from `init` against the interpretation `q` of the search
queries: best-first tree search on the depth-limited problem with the depth-first priority
(deepest node first, a key in `ℕᵒᵈ`), at most `fuel` iterations and frontier `F`, returning the
answer with the depth forgotten. -/
@[expose] def depthLimitedSearchM (q : {ι : Type} → SearchQuery S A ι → m ι)
    (F : Frontier Q ℕᵒᵈ (Node (S × ℕ) A)) (ℓ fuel : ℕ) (init : S) : m (Option (Node S A)) :=
  Option.map (Node.mapState Prod.fst) <$>
    bestFirstTreeSearchM (SearchQuery.depthLimit ℓ q) F
      (fun x => pure (OrderDual.toDual x.path.length)) fuel (init, 0)

/-- Depth-limited search ([RussellNorvig2020], §3.4.4) on the problem `P` with depth limit `ℓ`:
depth-first search that treats nodes at depth `ℓ` as having no successors, here best-first tree
search on `P.depthLimited ℓ` with the depth-first priority (the textbook's depth-first search is
best-first search with the negative depth as evaluation function, §3.4.3), frontier `F` and at
most `fuel` iterations. Unlike the textbook's algorithm it does not check for cycles along a path,
and it returns `none` both when the fuel runs out and when the depth-limited tree is exhausted,
without distinguishing a cutoff from a failure. -/
@[expose] def depthLimitedSearch (P : Problem S A) (F : Frontier Q ℕᵒᵈ (Node (S × ℕ) A))
    (ℓ fuel : ℕ) : Option (Node S A) :=
  (bestFirstTreeSearch (P.depthLimited ℓ) F (fun x => OrderDual.toDual x.path.length) fuel).map
    (Node.mapState Prod.fst)

/-- Depth-limited search from `init` as a query program on the search interface. -/
abbrev depthLimitedSearchQ (F : Frontier Q ℕᵒᵈ (Node (S × ℕ) A)) (ℓ fuel : ℕ) (init : S) :
    FreeM (SearchQuery S A) (Option (Node S A)) :=
  depthLimitedSearchM FreeM.lift F ℓ fuel init

/-- The depth-limited query program is the best-first query program of the depth-limited problem
with each query replaced by its interpretation under `SearchQuery.depthLimit ℓ FreeM.lift`. -/
private theorem depthLimitedSearchQ_eq_liftM (F : Frontier Q ℕᵒᵈ (Node (S × ℕ) A)) (ℓ fuel : ℕ)
    (init : S) :
    depthLimitedSearchQ F ℓ fuel init = Option.map (Node.mapState Prod.fst) <$>
      (bestFirstTreeSearchQ F (fun x => pure (OrderDual.toDual x.path.length)) fuel
        (init, 0)).liftM (SearchQuery.depthLimit ℓ FreeM.lift) := by
  rw [(FreeM.isMonadHom_liftM _).map_bestFirstTreeSearchM]
  simp only [FreeM.liftM_lift, FreeM.liftM_pure]
  rfl

/-- Answering the depth-limited problem's queries through `SearchQuery.depthLimit` and the
oracle of `P` is the oracle of the depth-limited problem. -/
private theorem eval_depthLimit (P : Problem S A) (h : S → ℕ) (ℓ : ℕ) :
    (fun {ι} (op : SearchQuery (S × ℕ) A ι) =>
      (SearchQuery.depthLimit ℓ FreeM.lift op).eval (P.oracle h)) =
      fun {ι} (op : SearchQuery (S × ℕ) A ι) => (P.depthLimited ℓ).oracle (fun p => h p.1) op := by
  funext ι op
  cases op with
  | actions p =>
    simp only [SearchQuery.depthLimit, Problem.oracle_actions, Problem.depthLimited_actions]
    split <;> simp
  | _ => simp [SearchQuery.depthLimit]

/-- Evaluating the depth-limited query program against the oracle of `P` (with any heuristic) is
depth-limited search on `P`. -/
@[simp] theorem eval_depthLimitedSearchQ (P : Problem S A) (h : S → ℕ)
    (F : Frontier Q ℕᵒᵈ (Node (S × ℕ) A)) (ℓ fuel : ℕ) :
    (depthLimitedSearchQ F ℓ fuel P.initial).eval (P.oracle h) = depthLimitedSearch P F ℓ fuel := by
  rw [depthLimitedSearchQ_eq_liftM, FreeM.eval_map, FreeM.eval_liftM, eval_depthLimit,
    ← Problem.depthLimited_initial, eval_bestFirstTreeSearchQ]
  rfl

section DepthLimited

variable {F : Frontier Q ℕᵒᵈ (Node (S × ℕ) A)}

/-- A reached node of the depth-limited problem is at depth at most `ℓ`. -/
private theorem length_le_of_depthLimited_mTr {P : Problem S A} {ℓ : ℕ} {y : Node (S × ℕ) A}
    (hy : (P.depthLimited ℓ).toLTS.MTr (P.depthLimited ℓ).initial y.path y.state) :
    y.path.length ≤ ℓ := by
  rw [Problem.depthLimited_initial, Problem.depthLimited_mTr_iff P ℓ (Nat.zero_le _)] at hy
  simpa using hy.2.2

/-- **Soundness of depth-limited search.** Whatever depth-limited search returns carries a
solution of at most `ℓ` actions: its path leads from the initial state to its state, which is a
goal state, at its reported cost. -/
theorem depthLimitedSearch_sound (hF : F.Lawful) (P : Problem S A) (ℓ fuel : ℕ) {x : Node S A}
    (h : depthLimitedSearch P F ℓ fuel = some x) :
    P.toLTS.MTr P.initial x.path x.state ∧ P.isGoal x.state = true ∧
      P.pathCost P.initial x.path = x.cost ∧ x.path.length ≤ ℓ := by
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨hm, hg, hc⟩ := bestFirstTreeSearch_sound hF _ _ fuel hy
  have hl := length_le_of_depthLimited_mTr hm
  rw [Problem.depthLimited_initial, Problem.depthLimited_mTr_iff P ℓ (Nat.zero_le _)] at hm
  rw [Problem.depthLimited_initial, Problem.depthLimited_pathCost] at hc
  exact ⟨hm.1, hg, hc, hl⟩

/-- **Completeness of depth-limited search.** If the problem has a solution of at most `ℓ`
actions and every state has at most `b` actions, then depth-limited search with limit `ℓ` and
fuel at least `∑ i ≤ ℓ, b ^ i` (the number of nodes of a `b`-ary tree of depth `ℓ`) returns a
solution of at most `ℓ` actions, for every lawful frontier ([RussellNorvig2020], §3.4.4). -/
theorem depthLimitedSearch_complete (hF : F.Lawful) {P : Problem S A} {b : ℕ}
    (hb : ∀ s, (P.actions s).length ≤ b) {sol : List A} (hsol : P.IsSolution sol) {ℓ : ℕ}
    (hℓ : sol.length ≤ ℓ) {fuel : ℕ} (hfuel : ∑ i ∈ Finset.range (ℓ + 1), b ^ i ≤ fuel) :
    ∃ x, depthLimitedSearch P F ℓ fuel = some x ∧ P.IsSolution x.path ∧ x.path.length ≤ ℓ := by
  have hsol' : (P.depthLimited ℓ).IsSolution sol :=
    (Problem.depthLimited_isSolution_iff P ℓ).2 ⟨hsol, hℓ⟩
  have hb' : ∀ p, ((P.depthLimited ℓ).actions p).length ≤ b := fun p => by
    rw [Problem.depthLimited_actions]
    split
    · exact hb _
    · exact Nat.zero_le _
  have hsome : (bestFirstTreeSearch (P.depthLimited ℓ) F
      (fun x => OrderDual.toDual x.path.length) fuel).isSome :=
    isSome_bestFirstLoopM hF (PrefixInv (P.depthLimited ℓ) sol)
      (fun y => ∑ i ∈ Finset.range (ℓ + 1 - y.path.length), b ^ i)
      (fun _ h => h.pos hℓ)
      (fun _ _ y hinv _ hg => ⟨hinv.step hsol' hg, sum_children_lt hb' y
        (length_le_of_depthLimited_mTr (hinv.1 _ (Multiset.mem_cons_self _ _)))⟩)
      fuel _ (PrefixInv.root hF sol _)
      (by rw [hF.contents_insert, hF.contents_empty]; simpa using hfuel)
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hsome
  have hx : depthLimitedSearch P F ℓ fuel = some (y.mapState Prod.fst) := by
    simp [depthLimitedSearch, hy]
  obtain ⟨hm, hg, -, hl⟩ := depthLimitedSearch_sound hF P ℓ fuel hx
  exact ⟨_, hx, ⟨_, hm, hg⟩, hl⟩

end DepthLimited

/-! ## Iterative deepening search -/

/-- Iterative deepening search in an arbitrary monad: depth-limited search with the limits
`0, 1, …, maxDepth` in turn, each with at most `fuel` iterations, returning the first answer. -/
@[expose] def iterativeDeepeningSearchM (q : {ι : Type} → SearchQuery S A ι → m ι)
    (F : Frontier Q ℕᵒᵈ (Node (S × ℕ) A)) (maxDepth fuel : ℕ) (init : S) :
    m (Option (Node S A)) :=
  (List.range (maxDepth + 1)).findSomeM? fun ℓ => depthLimitedSearchM q F ℓ fuel init

/-- Iterative deepening search ([RussellNorvig2020], §3.4.4) on the problem `P`:
depth-limited search with the limits `0, 1, …, maxDepth` in turn, each with frontier `F` and at
most `fuel` iterations, returning the first answer. The textbook's loop runs until depth-limited
search returns something other than a cutoff; here the bound `maxDepth` makes the definition
total, and a limit whose search fails is followed by the next limit. -/
@[expose] def iterativeDeepeningSearch (P : Problem S A) (F : Frontier Q ℕᵒᵈ (Node (S × ℕ) A))
    (maxDepth fuel : ℕ) : Option (Node S A) :=
  (List.range (maxDepth + 1)).findSome? fun ℓ => depthLimitedSearch P F ℓ fuel

/-- Iterative deepening search from `init` as a query program on the search interface. -/
abbrev iterativeDeepeningSearchQ (F : Frontier Q ℕᵒᵈ (Node (S × ℕ) A)) (maxDepth fuel : ℕ)
    (init : S) : FreeM (SearchQuery S A) (Option (Node S A)) :=
  iterativeDeepeningSearchM FreeM.lift F maxDepth fuel init

/-- Evaluating the iterative deepening query program against the oracle of `P` (with any
heuristic) is iterative deepening search on `P`. -/
@[simp] theorem eval_iterativeDeepeningSearchQ (P : Problem S A) (h : S → ℕ)
    (F : Frontier Q ℕᵒᵈ (Node (S × ℕ) A)) (maxDepth fuel : ℕ) :
    (iterativeDeepeningSearchQ F maxDepth fuel P.initial).eval (P.oracle h) =
      iterativeDeepeningSearch P F maxDepth fuel := by
  refine Id.pure_injective ?_
  rw [iterativeDeepeningSearchQ, iterativeDeepeningSearchM,
    (FreeM.isMonadHom_pure_eval _).map_listFindSomeM?]
  have (ℓ : ℕ) : (depthLimitedSearchM FreeM.lift F ℓ fuel P.initial).eval (P.oracle h) =
      depthLimitedSearch P F ℓ fuel := eval_depthLimitedSearchQ P h F ℓ fuel
  simp only [Function.comp_def, this]
  exact List.findSomeM?_pure

section IterativeDeepening

variable {F : Frontier Q ℕᵒᵈ (Node (S × ℕ) A)}

/-- The first `ℓ < n` at which `f` returns something is where `findSome?` over `range n` finds its
answer. -/
private theorem exists_of_findSome?_range_eq_some {α : Type} {f : ℕ → Option α} {n : ℕ} {x : α}
    (h : (List.range n).findSome? f = some x) :
    ∃ ℓ < n, f ℓ = some x ∧ ∀ ℓ' < ℓ, f ℓ' = none := by
  induction n with
  | zero => simp at h
  | succ n ih =>
    rw [List.range_succ, List.findSome?_append] at h
    cases h' : (List.range n).findSome? f with
    | some y =>
      rw [h', Option.some_or, Option.some_inj] at h
      subst h
      obtain ⟨ℓ, hℓ, hf, hmin⟩ := ih h'
      exact ⟨ℓ, by omega, hf, hmin⟩
    | none =>
      rw [h', Option.none_or, List.findSome?_singleton] at h
      refine ⟨n, by omega, h, fun ℓ' hℓ' => ?_⟩
      exact List.findSome?_eq_none_iff.1 h' ℓ' (List.mem_range.2 hℓ')

/-- **Soundness of iterative deepening search.** Whatever iterative deepening search returns
carries a solution of at most `maxDepth` actions, at its reported cost. -/
theorem iterativeDeepeningSearch_sound (hF : F.Lawful) (P : Problem S A) (maxDepth fuel : ℕ)
    {x : Node S A} (h : iterativeDeepeningSearch P F maxDepth fuel = some x) :
    P.toLTS.MTr P.initial x.path x.state ∧ P.isGoal x.state = true ∧
      P.pathCost P.initial x.path = x.cost ∧ x.path.length ≤ maxDepth := by
  obtain ⟨ℓ, hℓ, hx, -⟩ := exists_of_findSome?_range_eq_some h
  obtain ⟨hm, hg, hc, hl⟩ := depthLimitedSearch_sound hF P ℓ fuel hx
  exact ⟨hm, hg, hc, by omega⟩

/-- **Completeness and optimality of iterative deepening search.** If the problem has a solution
`sol` of at most `maxDepth` actions and every state has at most `b` actions, then iterative
deepening search with fuel at least `∑ i ≤ sol.length, b ^ i` per depth-limited search returns a
solution with the fewest actions, for every lawful frontier ([RussellNorvig2020], §3.4.4:
iterative deepening search is complete when the branching factor is finite, and optimal for
problems whose actions all have the same cost). -/
theorem iterativeDeepeningSearch_complete (hF : F.Lawful) {P : Problem S A} {b : ℕ}
    (hb : ∀ s, (P.actions s).length ≤ b) {sol : List A} (hsol : P.IsSolution sol)
    {maxDepth : ℕ} (hmax : sol.length ≤ maxDepth) {fuel : ℕ}
    (hfuel : ∑ i ∈ Finset.range (sol.length + 1), b ^ i ≤ fuel) :
    ∃ x, iterativeDeepeningSearch P F maxDepth fuel = some x ∧ P.IsSolution x.path ∧
      ∀ sol', P.IsSolution sol' → x.path.length ≤ sol'.length := by
  -- Depth-limited search succeeds at every limit from the length of a solution up to its own.
  have hdls : ∀ sol', P.IsSolution sol' → sol'.length ≤ sol.length →
      ∃ y, depthLimitedSearch P F sol'.length fuel = some y := fun sol' h' hl =>
    have hfuel' : ∑ i ∈ Finset.range (sol'.length + 1), b ^ i ≤ fuel :=
      le_trans (Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))) hfuel
    (depthLimitedSearch_complete hF hb h' le_rfl hfuel').imp fun _ h => h.1
  obtain ⟨y, hy⟩ := hdls sol hsol le_rfl
  obtain ⟨x, hx⟩ : ∃ x, iterativeDeepeningSearch P F maxDepth fuel = some x := by
    rw [← Option.isSome_iff_exists, iterativeDeepeningSearch, List.findSome?_isSome_iff]
    exact ⟨sol.length, List.mem_range.2 (by omega), by simp [hy]⟩
  obtain ⟨ℓ, -, hxℓ, hmin⟩ := exists_of_findSome?_range_eq_some hx
  obtain ⟨hm, hg, -, hl⟩ := depthLimitedSearch_sound hF P ℓ fuel hxℓ
  have hℓ : ℓ ≤ sol.length := by
    by_contra hlt
    rw [hmin _ (by omega)] at hy
    cases hy
  refine ⟨x, hx, ⟨_, hm, hg⟩, fun sol' h' => ?_⟩
  by_contra hlt
  obtain ⟨z, hz⟩ := hdls sol' h' (by omega)
  rw [hmin _ (by omega)] at hz
  cases hz

end IterativeDeepening

/-! ## Expansions of depth-limited and iterative deepening search -/

section Cost

/-- The weight of the depth-limited problem's queries induced through `SearchQuery.depthLimit`
by the expansion weight: an `actions` query costs one expansion below the depth limit and nothing
at it. -/
private theorem cost_depthLimit (P : Problem S A) (h : S → ℕ) (ℓ : ℕ) :
    (∀ p : S × ℕ, (SearchQuery.depthLimit ℓ FreeM.lift (.actions p)).cost (P.oracle h)
      SearchQuery.expansionWeight = if p.2 < ℓ then 1 else 0) ∧
    (∀ (p : S × ℕ) (a : A), (SearchQuery.depthLimit ℓ FreeM.lift (.result p a)).cost (P.oracle h)
      SearchQuery.expansionWeight = 0) ∧
    (∀ (p : S × ℕ) (a : A), (SearchQuery.depthLimit ℓ FreeM.lift (.stepCost p a)).cost
      (P.oracle h) SearchQuery.expansionWeight = 0) ∧
    (∀ p : S × ℕ, (SearchQuery.depthLimit ℓ FreeM.lift (.isGoal p)).cost (P.oracle h)
      SearchQuery.expansionWeight = 0) := by
  refine ⟨fun p => ?_, fun p a => ?_, fun p a => ?_, fun p => ?_⟩
  · simp only [SearchQuery.depthLimit]
    split <;> simp [SearchQuery.expansionWeight]
  all_goals simp [SearchQuery.depthLimit, SearchQuery.expansionWeight]

/-- **Expansion bound for depth-limited search.** In the query model, if every state has at most
`b` actions, depth-limited search with limit `ℓ` expands at most `∑ i < ℓ, b ^ i` nodes (the
number of nodes of depth less than `ℓ` in a `b`-ary tree), for every lawful frontier and every
amount of fuel; nodes at the depth limit are not expanded ([RussellNorvig2020], §3.4.4, where the
time complexity of depth-limited search is `O(b ^ ℓ)`). An expansion is an `actions` query,
counted by `SearchQuery.expansionWeight`. -/
theorem cost_expansionWeight_depthLimitedSearchQ_le {F : Frontier Q ℕᵒᵈ (Node (S × ℕ) A)}
    (hF : F.Lawful) (P : Problem S A) (h : S → ℕ) {b : ℕ} (hb : ∀ s, (P.actions s).length ≤ b)
    (ℓ fuel : ℕ) :
    (depthLimitedSearchQ F ℓ fuel P.initial).cost (P.oracle h) SearchQuery.expansionWeight ≤
      ∑ i ∈ Finset.range ℓ, b ^ i := by
  obtain ⟨hact, hres, hsc, hgoal⟩ := cost_depthLimit P h ℓ
  rw [depthLimitedSearchQ_eq_liftM, FreeM.cost_map, FreeM.cost_liftM, eval_depthLimit]
  simp only [bestFirstTreeSearchQ, bestFirstTreeSearchM, FreeM.cost_bind, FreeM.cost_pure,
    FreeM.eval_pure, zero_add]
  refine (cost_bestFirstLoopM_le_potential hF (P.depthLimited ℓ) _ _ _ hgoal
    (fun y => ∑ i ∈ Finset.range (ℓ - y.state.2), b ^ i) (fun y => ?_) fuel _).trans ?_
  · simp only [hact, hres, hsc, Problem.depthLimited_actions, Problem.depthLimited_result,
      zero_add]
    split
    · rename_i hlt
      have hℓ : ℓ - y.state.2 = (ℓ - (y.state.2 + 1)) + 1 := by omega
      rw [hℓ, geom_sum_succ, List.map_const', List.sum_replicate, smul_eq_mul]
      have := Nat.mul_le_mul_right (∑ i ∈ Finset.range (ℓ - (y.state.2 + 1)), b ^ i)
        (hb y.state.1)
      omega
    · simp
  · simp [hF.contents_insert, hF.contents_empty]

/-- The weighted cost of `findSomeM?` is at most the sum of the costs of the calls it may make. -/
private theorem cost_findSomeM?_le {α β : Type} (oracle : {ι : Type} → SearchQuery S A ι → ι)
    (w : {ι : Type} → SearchQuery S A ι → ℕ) (f : α → FreeM (SearchQuery S A) (Option β)) :
    ∀ l : List α, (l.findSomeM? f).cost oracle w ≤ (l.map fun a => (f a).cost oracle w).sum
  | [] => by simp [List.findSomeM?_nil]
  | a :: l => by
    rw [List.findSomeM?_cons, FreeM.cost_bind, List.map_cons, List.sum_cons]
    split
    · simp
    · exact Nat.add_le_add_left (cost_findSomeM?_le oracle w f l) _

/-- **Expansion bound for iterative deepening search.** In the query model, if every state has at
most `b` actions, iterative deepening search up to depth `maxDepth` expands at most
`∑ ℓ ≤ maxDepth, ∑ i < ℓ, b ^ i` nodes, for every lawful frontier and every amount of fuel: the
nodes of depth `i` are expanded once by each depth-limited search with limit above `i`
([RussellNorvig2020], §3.4.4). -/
theorem cost_expansionWeight_iterativeDeepeningSearchQ_le {F : Frontier Q ℕᵒᵈ (Node (S × ℕ) A)}
    (hF : F.Lawful) (P : Problem S A) (h : S → ℕ) {b : ℕ} (hb : ∀ s, (P.actions s).length ≤ b)
    (maxDepth fuel : ℕ) :
    (iterativeDeepeningSearchQ F maxDepth fuel P.initial).cost (P.oracle h)
      SearchQuery.expansionWeight ≤
      ∑ ℓ ∈ Finset.range (maxDepth + 1), ∑ i ∈ Finset.range ℓ, b ^ i := by
  refine (cost_findSomeM?_le _ _ _ _).trans ?_
  generalize maxDepth + 1 = n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.sum_range_succ, Finset.sum_range_succ]
    exact Nat.add_le_add ih (cost_expansionWeight_depthLimitedSearchQ_le hF P h hb n fuel)

end Cost

end Cslib.Algorithms.Lean.Search
