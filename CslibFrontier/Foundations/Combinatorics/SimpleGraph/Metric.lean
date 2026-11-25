/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Metric.lean`)

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Spheres and balls in graphs of bounded degree

The extended distance `SimpleGraph.edist` changes by at most one along an edge
(`SimpleGraph.Adj.edist_le_edist_add_one`), and a vertex at distance `k + 1` from `u` has a
neighbour at distance `k`, the penultimate vertex of a shortest walk
(`SimpleGraph.exists_adj_edist_eq_of_edist_eq_add_one`).

In a finite graph of maximum degree `D`, a vertex at positive distance `d + 1` from `u` therefore
has at most `D - 1` neighbours at distance `d + 2`, so the sphere of radius `d + 1` around `u` has
at most `D (D - 1) ^ d` vertices (`SimpleGraph.card_edist_eq_add_one_le`), and the closed ball of
radius `r` at most `(D + 1) ^ r` (`SimpleGraph.card_edist_le_le`). The closed ball
`{v | G.edist u v ≤ r}` is the open ball `G.ball u (r + 1)` of Mathlib.

## Main results

* `SimpleGraph.Adj.edist_le_edist_add_one`: distances change by at most one along an edge.
* `SimpleGraph.exists_adj_edist_eq_of_edist_eq_add_one`: a vertex at distance `k + 1` has a
  neighbour at distance `k`.
* `SimpleGraph.exists_edist_le_of_edist_le_add`: a shortest walk of length at most `a + b` passes
  through a vertex at distance at most `a` from its start and `b` from its end.
* `SimpleGraph.card_edist_eq_add_one_le`: the sphere bound `D (D - 1) ^ d`.
* `SimpleGraph.card_edist_le_le`: the ball bound `(D + 1) ^ r`.
-/

public section

open Finset

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {u v w : V}

/-- Adjacent vertices have extended distances to any vertex differing by at most one. -/
theorem Adj.edist_le_edist_add_one (h : G.Adj u v) (w : V) : G.edist u w ≤ G.edist v w + 1 :=
  G.edist_triangle.trans_eq (by rw [edist_eq_one_iff_adj.2 h, add_comm])

/-- A vertex at extended distance `k + 1` from `u` has a neighbour at distance `k` from `u`: the
penultimate vertex of a shortest walk. -/
theorem exists_adj_edist_eq_of_edist_eq_add_one {k : ℕ} (h : G.edist u w = k + 1) :
    ∃ v, G.Adj v w ∧ G.edist u v = k := by
  have h' : G.edist w u = ((k + 1 : ℕ) : ℕ∞) := by rw [edist_comm, h, Nat.cast_add, Nat.cast_one]
  obtain ⟨p, hp⟩ := exists_walk_of_edist_eq_coe h'
  cases p with
  | nil => simp at hp
  | @cons _ v _ hadj p =>
    simp only [Walk.length_cons, Nat.add_right_cancel_iff] at hp
    have hle : G.edist u v ≤ k := edist_comm.trans_le (hp ▸ edist_le p)
    refine ⟨v, hadj.symm, le_antisymm hle ?_⟩
    obtain ⟨n, hn, -⟩ := ENat.le_natCast_iff.mp hle
    have htri : G.edist u w ≤ G.edist u v + 1 := by
      simpa only [edist_comm (u := u)] using hadj.edist_le_edist_add_one u
    rw [h, hn] at htri
    rw [hn]; exact_mod_cast Nat.le_of_succ_le_succ (by exact_mod_cast htri)

/-- If `u` and `v` are at extended distance at most `a + b`, some vertex is at distance at most `a`
from `u` and at most `b` from `v`: the vertex at position `a` of a shortest walk. -/
theorem exists_edist_le_of_edist_le_add {a b : ℕ} (h : G.edist u v ≤ (a + b : ℕ)) :
    ∃ w, G.edist u w ≤ a ∧ G.edist w v ≤ b := by
  obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top (ne_top_of_le_ne_top (ENat.natCast_ne_top _) h)
  rw [← hp, Nat.cast_le] at h
  exact ⟨p.getVert a,
    (edist_le (p.take a)).trans (by rw [Walk.take_length]; exact_mod_cast min_le_left _ _),
    (edist_le (p.drop a)).trans (by rw [Walk.drop_length]; exact_mod_cast (by omega : _ ≤ b))⟩

variable [Fintype V] [DecidableRel G.Adj] {D : ℕ}

/-- A vertex at positive distance `d + 1` from `u` has a neighbour at distance `d`, which leaves at
most `D - 1` neighbours at distance `d + 2`. -/
private theorem card_filter_neighborFinset_le (hD : ∀ v, G.degree v ≤ D) {d : ℕ}
    (hw : G.edist u w = d + 1) :
    #{v ∈ G.neighborFinset w | G.edist u v = d + 1 + 1} ≤ D - 1 := by
  classical
  obtain ⟨p, hpw, hp⟩ := exists_adj_edist_eq_of_edist_eq_add_one hw
  refine (card_le_card (t := (G.neighborFinset w).erase p) fun v hv => ?_).trans ?_
  · rw [mem_filter] at hv; refine mem_erase.mpr ⟨?_, hv.1⟩
    rintro rfl
    have : ((d + 1 + 1 : ℕ) : ℕ∞) = d := by rw [← hp, hv.2]; push_cast; rfl
    exact absurd (Nat.cast_injective this) (by omega)
  · rw [card_erase_of_mem ((G.mem_neighborFinset w p).mpr hpw.symm),
      G.card_neighborFinset_eq_degree]
    exact Nat.sub_le_sub_right (hD w) 1

/-- Every vertex at distance `d + 1` from `u` is a neighbour of a vertex at distance `d`. -/
private theorem card_edist_eq_add_one_le_sum (u : V) (d : ℕ) :
    #{v | G.edist u v = d + 1} ≤
      ∑ w with G.edist u w = d, #{v ∈ G.neighborFinset w | G.edist u v = d + 1} := by
  classical
  refine (card_le_card fun v hv => ?_).trans card_biUnion_le
  obtain ⟨w, hwv, hw⟩ := exists_adj_edist_eq_of_edist_eq_add_one (mem_filter.mp hv).2
  exact mem_biUnion.mpr ⟨w, mem_filter.mpr ⟨mem_univ w, hw⟩,
    mem_filter.mpr ⟨(G.mem_neighborFinset w v).mpr hwv, (mem_filter.mp hv).2⟩⟩

/-- In a graph of maximum degree `D`, the sphere of radius `d + 1` around a vertex has at most
`D (D - 1) ^ d` vertices. -/
theorem card_edist_eq_add_one_le (hD : ∀ v, G.degree v ≤ D) (u : V) (d : ℕ) :
    #{v | G.edist u v = d + 1} ≤ D * (D - 1) ^ d := by
  induction d with
  | zero =>
    have h0 : ({w | G.edist u w = ((0 : ℕ) : ℕ∞)} : Finset V) = {u} := by
      ext w; simp only [mem_filter, mem_univ, true_and, mem_singleton, Nat.cast_zero,
        edist_eq_zero_iff]; exact eq_comm
    refine (card_edist_eq_add_one_le_sum u 0).trans ?_
    rw [h0, sum_singleton, pow_zero, mul_one]
    exact (card_filter_le _ _).trans ((G.card_neighborFinset_eq_degree u).trans_le (hD u))
  | succ d ih =>
    refine (card_edist_eq_add_one_le_sum u (d + 1)).trans
      ((sum_le_sum (g := fun _ => D - 1) fun w hw => ?_).trans ?_)
    · simpa only [Nat.cast_add, Nat.cast_one] using card_filter_neighborFinset_le hD
        (by rw [(mem_filter.mp hw).2, Nat.cast_add, Nat.cast_one])
    · rw [sum_const, smul_eq_mul, mul_comm, Nat.cast_add, Nat.cast_one]
      exact (Nat.mul_le_mul_left _ ih).trans_eq (by ring)

/-- In a graph of maximum degree `D`, the closed ball of radius `r` around a vertex has at most
`(D + 1) ^ r` vertices. -/
theorem card_edist_le_le (hD : ∀ v, G.degree v ≤ D) (u : V) (r : ℕ) :
    #{v | G.edist u v ≤ r} ≤ (D + 1) ^ r := by
  induction r with
  | zero =>
    have h0 : ({v | G.edist u v ≤ ((0 : ℕ) : ℕ∞)} : Finset V) = {u} := by
      ext v; simp only [mem_filter, mem_univ, true_and, mem_singleton, Nat.cast_zero,
        nonpos_iff_eq_zero, edist_eq_zero_iff]; exact eq_comm
    rw [h0, card_singleton, pow_zero]
  | succ r ih =>
    classical
    have hsub : ({v | G.edist u v ≤ ((r + 1 : ℕ) : ℕ∞)} : Finset V) ⊆
        ({v | G.edist u v ≤ r} : Finset V) ∪ ({v | G.edist u v = r + 1} : Finset V) := by
      intro v hv
      obtain ⟨n, hn, _⟩ := ENat.le_natCast_iff.mp (mem_filter.mp hv).2
      simp only [mem_union, mem_filter, mem_univ, true_and, hn]
      rcases Nat.lt_or_ge n (r + 1) with h | h
      · exact Or.inl (by exact_mod_cast (by omega : n ≤ r))
      · exact Or.inr (by rw [show n = r + 1 by omega]; push_cast; rfl)
    have hp : D * (D - 1) ^ r ≤ D * (D + 1) ^ r := by gcongr <;> omega
    have hs := (card_edist_eq_add_one_le hD u r).trans hp
    exact (card_le_card hsub).trans
      ((card_union_le _ _).trans ((add_le_add ih hs).trans_eq (by ring)))

end SimpleGraph
