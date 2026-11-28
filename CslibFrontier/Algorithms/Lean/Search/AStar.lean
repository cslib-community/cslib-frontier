/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Search.BestFirst
public import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Multiset.Basic

/-!
# Heuristics and A* tree search

A heuristic for a search problem estimates, for each state, the cost of a cheapest path from it to
a goal state ([RussellNorvig2020], §3.5). This module defines the *optimal cost-to-go*
`Problem.costToGo` (the textbook's `h*`), as an infimum in `ℕ∞` over the paths from a state to a
goal state, so that it is `⊤` exactly on the states from which no goal is reachable; a heuristic
is *admissible* when it never overestimates it, and *consistent* when it satisfies the triangle
inequality `h s ≤ c(s, a) + h (result s a)` along every applicable action and vanishes on goal
states ([RussellNorvig2020], §3.5.2). Every consistent heuristic is admissible.

*A\* tree search* `aStarTreeSearch` is best-first tree search (`bestFirstTreeSearch`) with the
evaluation function `f = g + h`, the path cost of a node plus the heuristic estimate of its state.
In the query model it is the query program `bestFirstTreeSearchQ` with the priority
`fun x => (x.cost + ·) <$> FreeM.lift (.heuristic x.state)`, whose evaluation against the oracle
`P.oracle h` is `aStarTreeSearch P h` (`eval_bestFirstTreeSearchQ`), and whose expansion and
generation counts are bounded by `cost_expansionWeight_bestFirstTreeSearchQ_le` and
`cost_generationWeight_bestFirstTreeSearchQ_le`.

The optimality theorem is the cost-optimality of A* with an admissible heuristic
([RussellNorvig2020], §3.5.2), following the argument of [HartNilssonRaphael1968]: when
the search pops a goal node, every solution still has a node on the frontier whose priority is
at most that solution's cost, and the popped node has the least priority. Cost-optimality in the
sense of [RussellNorvig2020], §3.3.4 is a property of the solution a search returns; it holds here
for every amount of fuel, since a search that runs out of fuel returns nothing. Completeness of
A\* tree search (that, with action costs bounded below by a positive constant, enough fuel finds a
solution when one exists) is a separate property, not proved here and left as a target of
issue #3669; completeness of A\* graph search on finite state spaces is
`aStarGraphSearch_complete`.

## Main definitions

* `Problem.costToGo`: the optimal cost-to-go `h*`.
* `Problem.Admissible`, `Problem.Consistent`: admissible and consistent heuristics.
* `aStarTreeSearch`: A* tree search.

## Main results

* `Problem.Consistent.le_pathCost_add`: a consistent heuristic satisfies the triangle inequality
  along every path.
* `Problem.Consistent.admissible`: every consistent heuristic is admissible.
* `aStarTreeSearch_isOptimalSolution`: with an admissible heuristic, the solution A* tree search
  returns is optimal.
* `uniformCostTreeSearch_isOptimalSolution`: the same for uniform-cost tree search, the case
  `h = 0`.

## References

* [HartNilssonRaphael1968]
* [RussellNorvig2020]
-/

public section

namespace Cslib.Algorithms.Lean.Search

variable {S A : Type}

namespace Problem

variable (P : Problem S A)

/-- The optimal cost-to-go `h*(s)` ([RussellNorvig2020], §3.5): the infimum, over the paths from
`s` to a goal state, of their costs. It is `⊤` when no goal state is reachable from `s`. -/
@[expose] noncomputable def costToGo (s : S) : ℕ∞ :=
  ⨅ (as : List A) (t : S) (_ : P.toLTS.MTr s as t ∧ P.isGoal t = true), (P.pathCost s as : ℕ∞)

/-- A heuristic is admissible ([RussellNorvig2020], §3.5.2) when it never overestimates the cost
to reach a goal: `h s ≤ h*(s)` for every state `s`. -/
@[expose] def Admissible (h : S → ℕ) : Prop :=
  ∀ s, (h s : ℕ∞) ≤ P.costToGo s

/-- A heuristic is consistent ([RussellNorvig2020], §3.5.2) when it satisfies the triangle
inequality `h s ≤ c(s, a) + h (result s a)` for every action `a` applicable in `s`, and is `0` on
goal states. -/
structure Consistent (h : S → ℕ) : Prop where
  /-- The triangle inequality along an applicable action. -/
  le_stepCost_add (s : S) (a : A) : a ∈ P.actions s → h s ≤ P.stepCost s a + h (P.result s a)
  /-- The heuristic vanishes on goal states. -/
  eq_zero_of_isGoal (s : S) : P.isGoal s = true → h s = 0

variable {P} {h : S → ℕ}

/-- A heuristic is admissible iff it is at most the cost of every path from a state to a goal
state. -/
theorem admissible_iff :
    P.Admissible h ↔
      ∀ s as t, P.toLTS.MTr s as t → P.isGoal t = true → h s ≤ P.pathCost s as := by
  simp only [Admissible, costToGo, le_iInf_iff, Nat.cast_le, and_imp]

/-- A consistent heuristic satisfies the triangle inequality along every path: if `as` leads from
`s` to `t`, then `h s ≤ c(as) + h t`. -/
theorem Consistent.le_pathCost_add (hc : P.Consistent h) {s t : S} {as : List A}
    (hst : P.toLTS.MTr s as t) : h s ≤ P.pathCost s as + h t := by
  induction hst with
  | refl => simp
  | stepL htr _ ih =>
    obtain ⟨ha, rfl⟩ := htr
    have := hc.le_stepCost_add _ _ ha
    simp only [pathCost_cons]
    omega

/-- Every consistent heuristic is admissible ([RussellNorvig2020], §3.5.2). -/
theorem Consistent.admissible (hc : P.Consistent h) : P.Admissible h :=
  admissible_iff.2 fun _ _ _ hst hg => by
    simpa [hc.eq_zero_of_isGoal _ hg] using hc.le_pathCost_add hst

end Problem

/-- A\* tree search ([RussellNorvig2020], §3.5.2) on the problem `P` with heuristic `h`: best-first
tree search with the evaluation function `f = g + h`, the path cost of a node plus the heuristic
estimate of its state, with frontier `F` and at most `fuel` iterations. -/
abbrev aStarTreeSearch {Q : Type} (P : Problem S A) (h : S → ℕ) (F : Frontier Q ℕ (Node S A))
    (fuel : ℕ) : Option (Node S A) :=
  bestFirstTreeSearch P F (fun x => x.cost + h x.state) fuel

/-! ## Cost-optimality of A* tree search -/

section Optimality

variable {Q : Type} {F : Frontier Q ℕ (Node S A)} {P : Problem S A} {h : S → ℕ}

/-- The loop invariant of A* tree search towards a solution reaching the goal state `t` at cost at
most `C`: every frontier element is keyed by `g + h`, and some frontier node lies on the solution,
so that its path cost plus the cost of the rest of the solution is at most `C`. -/
private def AStarInv (P : Problem S A) (h : S → ℕ) (t : S) (C : ℕ)
    (M : Multiset (ℕ × Node S A)) : Prop :=
  (∀ p ∈ M, p.1 = p.2.cost + h p.2.state) ∧
    ∃ p ∈ M, ∃ rest, P.toLTS.MTr p.2.state rest t ∧ p.2.cost + P.pathCost p.2.state rest ≤ C

/-- Expanding a non-goal node preserves the invariant: if the node on the solution is the expanded
one, its child along the solution takes its place. -/
private theorem AStarInv.step {t : S} (ht : P.isGoal t = true) {C : ℕ}
    {M : Multiset (ℕ × Node S A)} {k : ℕ} {y : Node S A} (hI : AStarInv P h t C ((k, y) ::ₘ M))
    (hg : P.isGoal y.state = false) :
    AStarInv P h t C (P.keyedChildren (fun z => z.cost + h z.state) y + M) := by
  obtain ⟨hkey, p, hp, rest, hrest, hC⟩ := hI
  refine ⟨fun q hq => ?_, ?_⟩
  · rcases Multiset.mem_add.1 hq with hq | hq
    · obtain ⟨a, -, rfl⟩ := Problem.mem_keyedChildren_iff.1 hq
      rfl
    · exact hkey q (Multiset.mem_cons_of_mem hq)
  · rcases Multiset.mem_cons.1 hp with rfl | hp
    · rcases rest with _ | ⟨a, rest⟩
      · rw [LTS.MTr.nil_iff] at hrest
        rw [hrest, ht] at hg
        exact absurd hg (by simp)
      · rw [Problem.toLTS_mTr_cons_iff] at hrest
        refine ⟨_, Multiset.mem_add.2 (Or.inl (Problem.mem_keyedChildren_iff.2 ⟨a, hrest.1, rfl⟩)),
          rest, hrest.2, ?_⟩
        simp only [Problem.pathCost_cons] at hC
        simp only
        omega
    · exact ⟨p, Multiset.mem_add.2 (Or.inr hp), rest, hrest, hC⟩

/-- **Cost-optimality of A\* tree search** ([RussellNorvig2020], §3.5.2;
[HartNilssonRaphael1968]). With an admissible heuristic, for every lawful frontier and every
amount of fuel, the action sequence of a node returned by A\* tree search is an optimal solution:
a solution whose path cost is at most that of every solution. -/
theorem aStarTreeSearch_isOptimalSolution (hF : F.Lawful) (hadm : P.Admissible h) (fuel : ℕ)
    {x : Node S A} (hx : aStarTreeSearch P h F fuel = some x) :
    P.IsOptimalSolution x.path := by
  obtain ⟨hpath, hgoal, hcost⟩ := bestFirstTreeSearch_sound hF P _ fuel hx
  refine ⟨⟨_, hpath, hgoal⟩, fun σ ⟨t, hσ, ht⟩ => ?_⟩
  rw [hcost]
  have hroot : AStarInv P h t (P.pathCost P.initial σ)
      (F.contents (F.insert (0 + h P.initial) ⟨P.initial, [], 0⟩ F.empty)) := by
    rw [hF.contents_insert, hF.contents_empty]
    refine ⟨fun p hp => ?_, _, Multiset.mem_cons_self _ _, σ, hσ, by simp⟩
    rw [Multiset.mem_cons] at hp
    rcases hp with rfl | hp
    · rfl
    · simp at hp
  -- When the goal node is popped, its key is at most that of the node on `σ`, which is at most
  -- the cost of `σ` by admissibility.
  obtain ⟨k, M, ⟨hkey, p, hp, rest, hrest, hC⟩, hmin, -⟩ := bestFirstLoopM_inv hF
    (AStarInv P h t (P.pathCost P.initial σ)) (fun _ _ _ hI _ hg => hI.step ht hg) fuel _ hroot hx
  have hkx := hkey (k, x) (Multiset.mem_cons_self _ _)
  have hkp : k ≤ p.1 := by
    rcases Multiset.mem_cons.1 hp with rfl | hp
    · exact le_rfl
    · exact hmin p hp
  have := Problem.admissible_iff.1 hadm _ _ _ hrest ht
  have := hkey p hp
  simp only at hkx
  omega

/-- **Cost-optimality of uniform-cost tree search** ([RussellNorvig2020], §3.4.2). For every
lawful frontier and every amount of fuel, the action sequence of a node returned by best-first tree
search with the path cost `g` as priority is an optimal solution. This is A\* tree search with the
admissible heuristic `0`. -/
theorem uniformCostTreeSearch_isOptimalSolution (hF : F.Lawful) (fuel : ℕ) {x : Node S A}
    (hx : bestFirstTreeSearch P F (·.cost) fuel = some x) : P.IsOptimalSolution x.path :=
  aStarTreeSearch_isOptimalSolution (h := fun _ => 0) hF
    (Problem.admissible_iff.2 fun _ _ _ _ _ => Nat.zero_le _) fuel hx

end Optimality

end Cslib.Algorithms.Lean.Search
