/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

import CslibFrontier.Foundations.Combinatorics.CoveringTower.Defs
import CslibFrontier.Foundations.Combinatorics.CoveringTower.Path
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-! Tests of the covering-tower interface: a one-level tower with two chambers joined by one
typed edge, and its routes. -/

namespace CslibFrontierTests.CoveringTower

open Cslib.CoveringTower

/-- One level (`J = 0`), one type (`h = 1`), two chambers `0, 1` joined by one edge `()`, `b = 2`
places at the single vertex, no near pairs, degree `r = 1`, and `D = 1`. -/
abbrev twoChambers : Tower 1 2 1 0 1 where
  X _ := Fin 2
  Ed _ := Unit
  V _ _ := Unit
  Fl := Fin 2
  Nr := Empty
  e0 _ := 0
  e1 _ := 1
  e_ne _ := by decide
  ty _ := 0
  card_ed _ _ i := by fin_cases i; decide
  deg _ _ c i := by fin_cases i; fin_cases c <;> decide
  vx _ _ := ()
  co _ c := c
  vx_co _ _ := ⟨fun c c' h => (Prod.ext_iff.1 h).2, fun ⟨(), c⟩ => ⟨c, rfl⟩⟩
  card_fl := rfl
  cN := Empty.elim
  dN := Empty.elim
  n_ne := fun ν => ν.elim
  nr _ i := {
    toFun := fun e => absurd (Subsingleton.elim (α := Fin 1) _ i) e.2
    invFun := fun p => p.2.elim
    left_inv := fun e => absurd (Subsingleton.elim (α := Fin 1) _ i) e.2
    right_inv := fun p => p.2.elim }
  nr_vx0 _ i e := absurd (Subsingleton.elim (α := Fin 1) _ i) e.2
  nr_vx1 _ i e := absurd (Subsingleton.elim (α := Fin 1) _ i) e.2
  nr_co _ i e := absurd (Subsingleton.elim (α := Fin 1) _ i) e.2
  π c := c
  πE e := e
  πV v := v
  π_ends h := absurd h (Nat.not_lt_zero _)
  π_ty h := absurd h (Nat.not_lt_zero _)
  card_X _ h := absurd h (Nat.not_lt_zero _)
  fibre h := absurd h (Nat.not_lt_zero _)
  π_vx h := absurd h (Nat.not_lt_zero _)
  π_co h := absurd h (Nat.not_lt_zero _)
  host _ _ := 0
  host_inj h := absurd h (Nat.not_lt_zero _)
  host_vx h := absurd h (Nat.not_lt_zero _)

/-- Routes of length at most `1`: the edge for distinct chambers, nothing otherwise. The edge is
used once from `0` to `1` and once from `1` to `0`. -/
def twoChambersRoutes : Routes twoChambers 1 2 where
  rt c c' := if c = c' then [] else [()]
  walk c c' := by
    fin_cases c <;> fin_cases c' <;>
      simp [Tower.Walk, Tower.step, twoChambers]
  len c c' := by split_ifs <;> simp
  use e := by cases e; decide

/-- A route between distinct chambers has positive length. -/
example : 0 < (twoChambersRoutes.rt (0 : Fin 2) 1).length := by decide

/-- `use` counts both directions: no routes use the edge at most once. -/
example : IsEmpty (Routes twoChambers 1 1) := by
  refine ⟨fun R => ?_⟩
  have hne : ∀ c c' : Fin 2, c ≠ c' → R.rt c c' ≠ [] := fun c c' h e => by
    have := R.walk c c'
    rw [e] at this
    exact h this
  have h01 := hne 0 1 (by decide)
  have h10 := hne 1 0 (by decide)
  have hcount : ∀ l : List Unit, l ≠ [] → 1 ≤ l.count () := fun l hl => by
    obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hl
    simp
  have := R.use ()
  simp only [Fin.sum_univ_two] at this
  have := hcount _ h01
  have := hcount _ h10
  omega

/-! ### The route API of `CoveringTower.Path` -/

/-- Reversing a route gives a walk back. -/
example : twoChambers.Walk (1 : Fin 2) (twoChambersRoutes.rt 0 1).reverse 0 :=
  Tower.walk_reverse (twoChambersRoutes.walk 0 1)

/-- The path from `0` back to `0` by way of `1` is a walk of length at most `2 m = 2`. -/
example : twoChambers.Walk (0 : Fin 2) (twoChambersRoutes.path 0 0 1) 0 ∧
    (twoChambersRoutes.path 0 0 1).length ≤ 2 :=
  ⟨twoChambersRoutes.path_walk 0 0 1, twoChambersRoutes.length_path 0 0 1⟩

/-- The path from `0` to `1` by way of `0` reaches `1` at its first visit `pl`, and every step
before is the edge between successive chambers. -/
example : twoChambersRoutes.pn 0 1 0 (twoChambersRoutes.pl 0 1 0) = 1 ∧
    ∀ s < twoChambersRoutes.pl 0 1 0, ∃ e, (twoChambersRoutes.path 0 1 0)[s]? = some e ∧
      s(twoChambers.e0 e, twoChambers.e1 e) =
        s(twoChambersRoutes.pn 0 1 0 s, twoChambersRoutes.pn 0 1 0 (s + 1)) := by
  refine ⟨twoChambersRoutes.pn_pl 0 1 0, fun s hs => ?_⟩
  obtain ⟨e, h1, h2, -⟩ := twoChambersRoutes.exists_edge 0 1 0 hs
  exact ⟨e, h1, h2⟩

end CslibFrontierTests.CoveringTower
