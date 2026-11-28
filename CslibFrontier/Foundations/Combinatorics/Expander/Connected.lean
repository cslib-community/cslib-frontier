/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.Cheeger
public import CslibFrontier.Foundations.Combinatorics.Expander.Hom
public import CslibFrontier.Foundations.Combinatorics.Expander.Mixing
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import CslibFrontier.Foundations.Data.Finset.Variance

/-!
# Connectivity and spectral expansion

Two facts connect the spectral expansion `λ(G)` of a regular multigraph with its connectivity,
and they are the two ends of Reingold's algorithm for undirected connectivity
[Reingold][Reingold2008] [Arora and Barak, Section 21.4][AroraBarak09].

**A connected graph has a spectral gap.** If `G` is connected, a set `S` of at most half of the
vertices has an edge leaving it, so the edge expansion of `G` is at least `1 / |V|`, and Cheeger's
inequality bounds the second eigenvalue of the walk operator by `1 - 1 / (2 |V|² |D|²)`. When at
least half of the edges at every vertex are self-loops, the walk operator is positive semidefinite
(`expect_mul_walk_nonneg`), so this also bounds `λ(G)`
(`spectralExpansion_le_of_preconnected`). Reingold uses the sharper bound `1 - 1 / (D N²)` for
connected nonbipartite graphs, due to Alon and Sudakov [Reingold, Lemma 2.5][Reingold2008]; any
inverse polynomial gap suffices for his algorithm. Self-loops are often added for this purpose by
passing to the lazy graph (`Cslib.RotationMap.lazy`), whose spectral expansion edge expansion
bounds in the same way
(`Cslib.RotationMap.spectralExpansion_lazy_le_of_mul_card_le_card_interedges_compl`); the bound
here applies to any graph that already has enough self-loops, without relabelling.

**One self-loop per vertex suffices** for an inverse polynomial gap
[Arora and Barak, draft of 2007-01-08, Lemma 7.28][AroraBarak07]: the draft's direct argument
compares the values of a function at the two ends of each edge, without Cheeger's inequality, and
gives `λ(G)² ≤ 1 - 1 / (|D| |V|³)` (`spectralExpansion_sq_le_one_sub_of_preconnected_of_loop`),
hence the draft's `λ(G) ≤ 1 - 1 / (8 |D| |V|³)`
(`spectralExpansion_le_one_sub_of_preconnected_of_loop`). On the connected component of the start
vertex, this makes a walk of `T ≥ 10 d n³ log n` steps end at each vertex of the component with
probability greater than `1 / (2 n)`
[Arora and Barak, draft of 2007-01-08, Corollary 7.30][AroraBarak07]
(`card_pow_lt_two_mul_card_mul_card_filter_neighbor_pow_eq`).

**In a good expander, short walks reach every vertex.** A random walk of length `t` from `u` ends
at `v` with probability within `λ(G) ^ t (1 - 1 / |V|)` of `1 / |V|` (`abs_walk_pow_ite_eq_sub_le`).
So if `λ(G) ^ t (|V| - 1) < 1`, then for any two vertices `u` and `v` some walk of length exactly
`t` leads from `u` to `v` (`exists_neighbor_pow_eq`): the probability is at least
`(1 - λ(G) ^ t (|V| - 1)) / |V| > 0`. So an expander with `λ(G) ≤ c < 1` has diameter
`O(log |V|)` (`exists_walk_length_le_clog_of_spectralExpansion_lt`); Reingold derives this from
vertex expansion instead [Reingold, Proposition 2.2][Reingold2008].

## Main results

* `Cslib.RotationMap.interedges_compl_nonempty`: in a connected graph, an edge leaves every
  nonempty proper set of vertices.
* `Cslib.RotationMap.expect_mul_walk_nonneg`: if at least half of the edges at every vertex are
  self-loops, the walk operator is positive semidefinite.
* `Cslib.RotationMap.spectralExpansion_le_of_preconnected`: a connected graph with at least half
  self-loops at every vertex has `λ(G) ≤ 1 - 1 / (2 |V|² |D|²)`.
* `Cslib.RotationMap.spectralExpansion_sq_le_one_sub_of_preconnected_of_loop`,
  `Cslib.RotationMap.spectralExpansion_le_one_sub_of_preconnected_of_loop`: a connected graph with a
  self-loop at every vertex has `λ(G)² ≤ 1 - 1 / (|D| |V|³)`, so `λ(G) ≤ 1 - 1 / (8 |D| |V|³)`
  (Arora–Barak draft, Lemma 7.28).
* `Cslib.RotationMap.abs_walk_pow_ite_eq_sub_le`: pointwise mixing, the end of a walk of length `t`
  is at each vertex with probability within `λ(G) ^ t (1 - 1 / |V|)` of uniform.
* `Cslib.RotationMap.exists_neighbor_pow_eq`: if `λ(G) ^ t (|V| - 1) < 1`, every vertex is
  reachable from every other by a walk of length exactly `t`.
* `Cslib.RotationMap.card_pow_lt_two_mul_card_mul_card_filter_neighbor_pow_eq`: with a self-loop at
  every vertex, a walk of `T ≥ 10 d n³ log n` steps from `s` ends at every vertex connected to `s`
  with probability greater than `1 / (2 n)` (Arora–Barak draft, Corollary 7.30).
* `Cslib.RotationMap.exists_walk_length_le_clog_of_spectralExpansion_lt`: if `λ(G) < 1 / 4`, the
  simple graph of `G` has diameter at most `⌈log₄ |V|⌉` [Arora and Barak, Theorem 16.35].

## References

* [O. Reingold, *Undirected connectivity in log-space*][Reingold2008]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft of
  2007-01-08][AroraBarak07]
* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their
  applications*][HooryLinialWigderson2006]
-/

public section

namespace Cslib.RotationMap

open Finset
open scoped BigOperators

variable {V D : Type*} (G : RotationMap V D)

section Gap

variable [Fintype V] [DecidableEq V] [Fintype D]

/-- In a connected graph, some edge leaves every nonempty proper set of vertices. -/
theorem interedges_compl_nonempty (hG : G.toSimpleGraph.Preconnected) {S : Finset V}
    (hS : S.Nonempty) (hS' : S ≠ univ) : (G.interedges S Sᶜ).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  have hcl : ∀ v ∈ (S : Set V), ∀ i, G.neighbor v i ∈ (S : Set V) := by
    intro v hv i
    by_contra hvi
    have : (v, i) ∈ G.interedges S Sᶜ := mem_interedges.2 ⟨hv, mem_compl.2 hvi⟩
    rw [h] at this
    exact notMem_empty _ this
  obtain ⟨x, hx⟩ := hS
  exact hS' (eq_univ_of_forall fun y ↦ G.mem_of_reachable hcl hx (hG x y))

omit [Fintype V] in
/-- If at least half of the edges at `v` are self-loops, the average over `i : D` of `c` on
self-loops and `-c` on non-loop edges is nonnegative for `c ≥ 0`. -/
private theorem expect_ite_neighbor_eq_nonneg {v : V}
    (hv : Fintype.card D ≤ 2 * G.edgeCount v v) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ 𝔼 i, (if G.neighbor v i = v then c else -c) := by
  rw [Fintype.expect_eq_sum_div_card]
  refine div_nonneg ?_ (Nat.cast_nonneg _)
  rw [sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have hcard := card_filter_add_card_filter_not (s := (univ : Finset D))
    (fun i ↦ G.neighbor v i = v)
  rw [card_univ] at hcard
  have hle : (#{i | ¬G.neighbor v i = v} : ℝ) ≤ #{i | G.neighbor v i = v} := by
    rw [edgeCount] at hv
    exact_mod_cast (by omega : #{i | ¬G.neighbor v i = v} ≤ #{i | G.neighbor v i = v})
  nlinarith

/-- If at least half of the edges at every vertex are self-loops, the walk operator is positive
semidefinite: `0 ≤ 𝔼 v, f v * G.walk f v` for every `f`. -/
theorem expect_mul_walk_nonneg (hG : ∀ v, Fintype.card D ≤ 2 * G.edgeCount v v)
    (f : V → ℝ) : 0 ≤ 𝔼 v, f v * G.walk f v := by
  -- a self-loop contributes `f v ^ 2`, any other edge at least `-(f v ^ 2 + f w ^ 2) / 2`
  set g : V → V → ℝ := fun v w ↦ if w = v then f v ^ 2 else -(f v ^ 2 + f w ^ 2) / 2 with hg
  have hfg (v w : V) : g v w ≤ f v * f w := by
    simp only [hg]
    split_ifs with h
    · rw [h, sq]
    · nlinarith [sq_nonneg (f v + f w)]
  -- the far ends of the edges other than self-loops are the near ends of such edges
  have hsymm : 𝔼 v, 𝔼 i, (if G.neighbor v i = v then 0 else -f (G.neighbor v i) ^ 2 / 2) =
      𝔼 v, 𝔼 i, (if G.neighbor v i = v then 0 else -f v ^ 2 / 2 : ℝ) := by
    rw [G.expect_expect_neighbor_comm fun v w ↦ (if w = v then 0 else -f w ^ 2 / 2 : ℝ)]
    simp only [eq_comm]
  have h (v : V) (i : D) : g v (G.neighbor v i) =
      (if G.neighbor v i = v then f v ^ 2 else -f v ^ 2 / 2) +
        if G.neighbor v i = v then 0 else -f (G.neighbor v i) ^ 2 / 2 := by
    simp only [hg]
    split_ifs <;> ring
  have hsplit : 𝔼 v, 𝔼 i, g v (G.neighbor v i) =
      𝔼 v, 𝔼 i, (if G.neighbor v i = v then f v ^ 2 else -f v ^ 2) := by
    simp only [h, expect_add_distrib]
    rw [hsymm, ← expect_add_distrib]
    refine expect_congr rfl fun v _ ↦ ?_
    rw [← expect_add_distrib]
    refine expect_congr rfl fun i _ ↦ ?_
    split_ifs <;> ring
  calc (0 : ℝ) ≤ 𝔼 v, 𝔼 i, (if G.neighbor v i = v then f v ^ 2 else -f v ^ 2) :=
        expect_nonneg fun v _ ↦ G.expect_ite_neighbor_eq_nonneg (hG v) (sq_nonneg _)
    _ = 𝔼 v, 𝔼 i, g v (G.neighbor v i) := hsplit.symm
    _ ≤ 𝔼 v, 𝔼 i, f v * f (G.neighbor v i) :=
        expect_le_expect fun v _ ↦ expect_le_expect fun i _ ↦ hfg v _
    _ = 𝔼 v, f v * G.walk f v := by simp only [walk_apply, mul_expect]

/-- **A connected graph has a spectral gap.** If `G` is connected and at least half of the edges at
every vertex are self-loops, then `λ(G) ≤ 1 - 1 / (2 |V|² |D|²)`: an edge leaves every set of at
most half of the vertices, which bounds the second eigenvalue by Cheeger's inequality
[Hoory, Linial and Wigderson, Theorem 2.4][HooryLinialWigderson2006], and the self-loops make the
walk operator positive semidefinite, so that the second eigenvalue is `λ(G)`. Compare the lazy
graph, whose walk is positive semidefinite by construction
(`spectralExpansion_lazy_le_of_mul_card_le_card_interedges_compl`). -/
theorem spectralExpansion_le_of_preconnected
    (hloop : ∀ v, Fintype.card D ≤ 2 * G.edgeCount v v)
    (hconn : G.toSimpleGraph.Preconnected) :
    G.spectralExpansion ≤ 1 - 1 / (2 * Fintype.card V ^ 2 * Fintype.card D ^ 2) := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · rw [G.spectralExpansion_eq_zero_of_subsingleton, sub_nonneg]
    rcases Nat.eq_zero_or_pos (2 * Fintype.card V ^ 2 * Fintype.card D ^ 2) with h | h
    · rw [← Nat.cast_ofNat, ← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_mul, h,
        Nat.cast_zero, div_zero]
      exact zero_le_one
    · rw [div_le_one (by exact_mod_cast h)]
      exact_mod_cast h
  have hN : (0 : ℝ) < Fintype.card V := Nat.cast_pos.2 Fintype.card_pos
  rw [G.spectralExpansion_eq_secondEigenvalue_of_nonneg (G.expect_mul_walk_nonneg hloop),
    secondEigenvalue_le_iff]
  intro f hf
  have hc : ∀ S : Finset V, 2 * #S ≤ Fintype.card V →
      1 / (Fintype.card V : ℝ) * #S ≤ #(G.interedges S Sᶜ) := by
    intro S hS
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp
    have hlt : #S < Fintype.card V := by have := hne.card_pos; omega
    refine le_trans ?_ (Nat.one_le_cast.2 (G.interedges_compl_nonempty hconn hne
      fun h ↦ by simp [h] at hlt).card_pos)
    rw [div_mul_eq_mul_div, one_mul, div_le_one hN]
    exact_mod_cast hlt.le
  refine (G.expect_mul_walk_le_of_mul_card_le_card_interedges_compl (by positivity) hc hf).trans_eq
    ?_
  ring

end Gap

section OneLoop

variable [Fintype V] [Fintype D]

/-- **The energy identity**: averaged over the edges `(v, i)`, the square of the difference between
the walk average of `f` at `v` and the value of `f` at the far end is the loss
`𝔼 f² - 𝔼 (G.walk f)²` of second moment under one step of the walk. -/
private theorem expect_expect_walk_sub_sq [Nonempty D] (f : V → ℝ) :
    𝔼 v, 𝔼 i, (G.walk f v - f (G.neighbor v i)) ^ 2 = 𝔼 v, f v ^ 2 - 𝔼 v, G.walk f v ^ 2 := by
  have h (v : V) : 𝔼 i, (G.walk f v - f (G.neighbor v i)) ^ 2 =
      𝔼 i, f (G.neighbor v i) ^ 2 - G.walk f v ^ 2 := by
    simp_rw [sub_sq_comm (G.walk f v), walk_apply]
    exact Fintype.expect_sub_expect_sq (fun i ↦ f (G.neighbor v i))
  simp only [h, expect_sub_distrib, G.expect_expect_neighbor fun w ↦ f w ^ 2]

/-- The draft's argument for **Arora–Barak, Lemma 7.28**: if `G` is connected and has a self-loop
at every vertex, one step of the walk loses at least a `1 / (|D| |V|³)` fraction of the second
moment of a function of expectation zero. Let `Q` be the loss. Every edge `(v, i)` carries at most
`|D| |V|` times the average loss, so, with a self-loop at `v`, the values of `f` at the ends of an
edge differ by at most `2 √(|D| |V| Q)`. A path has fewer than `|V|` edges, so the range of `f` is
at most `2 (|V| - 1) √(|D| |V| Q)`, and a function of expectation zero has second moment at most a
quarter of its squared range. -/
private theorem expect_sq_le_mul_sub_expect_walk_sq (hloop : ∀ v, ∃ i, G.neighbor v i = v)
    (hconn : G.toSimpleGraph.Preconnected) {f : V → ℝ} (hf : 𝔼 v, f v = 0) :
    𝔼 v, f v ^ 2 ≤
      Fintype.card D * Fintype.card V ^ 3 * (𝔼 v, f v ^ 2 - 𝔼 v, G.walk f v ^ 2) := by
  rcases isEmpty_or_nonempty V with hV | hV
  · simp
  obtain ⟨v₀⟩ := id hV
  have : Nonempty D := ⟨(hloop v₀).choose⟩
  set n : ℝ := (Fintype.card V : ℝ) with hn
  set d : ℝ := (Fintype.card D : ℝ) with hd
  have hn1 : 1 ≤ n := Nat.one_le_cast.2 Fintype.card_pos
  have hd0 : 0 < d := Nat.cast_pos.2 Fintype.card_pos
  set Q := 𝔼 v, f v ^ 2 - 𝔼 v, G.walk f v ^ 2 with hQ
  have hQe := G.expect_expect_walk_sub_sq f
  rw [← hQ] at hQe
  have hQ0 : 0 ≤ Q := hQe ▸ expect_nonneg fun v _ ↦ expect_nonneg fun i _ ↦ sq_nonneg _
  -- every edge carries at most `d n` times the average loss
  have hterm (v : V) (i : D) : (G.walk f v - f (G.neighbor v i)) ^ 2 ≤ d * n * Q := by
    have h1 : (G.walk f v - f (G.neighbor v i)) ^ 2 ≤
        d * 𝔼 i, (G.walk f v - f (G.neighbor v i)) ^ 2 := by
      rw [Fintype.expect_eq_sum_div_card, ← hd, mul_div_cancel₀ _ hd0.ne']
      exact single_le_sum (fun j _ ↦ sq_nonneg (G.walk f v - f (G.neighbor v j))) (mem_univ i)
    have h2 : 𝔼 i, (G.walk f v - f (G.neighbor v i)) ^ 2 ≤ n * Q := by
      rw [← hQe, Fintype.expect_eq_sum_div_card (fun v ↦ 𝔼 i, _), ← hn,
        mul_div_cancel₀ _ (by positivity)]
      exact single_le_sum (fun w _ ↦ expect_nonneg fun i _ ↦
        sq_nonneg (G.walk f w - f (G.neighbor w i))) (mem_univ v)
    linarith [mul_le_mul_of_nonneg_left h2 hd0.le]
  -- with the self-loops, adjacent values differ by at most `c`
  set c := √(4 * (d * n * Q)) with hc
  have hadj {v w : V} (h : G.toSimpleGraph.Adj v w) : |f v - f w| ≤ c := by
    obtain ⟨-, i, rfl⟩ := h
    obtain ⟨j, hj⟩ := hloop v
    have a := hterm v i
    have b := hterm v j
    rw [hj] at b
    refine Real.abs_le_sqrt ?_
    nlinarith [sq_nonneg (G.walk f v - f (G.neighbor v i) + (G.walk f v - f v))]
  have hwalk {u w : V} (p : G.toSimpleGraph.Walk u w) : |f u - f w| ≤ p.length * c := by
    induction p with
    | nil => simp
    | cons h p ih =>
      rw [SimpleGraph.Walk.length_cons, Nat.cast_succ]
      calc _ ≤ |f _ - f _| + |f _ - f _| := abs_sub_le _ _ _
        _ ≤ c + p.length * c := add_le_add (hadj h) ih
        _ = _ := by ring
  -- so the range of `f` is at most `(n - 1) c`
  obtain ⟨u, hu⟩ := Finite.exists_max f
  obtain ⟨w, hw⟩ := Finite.exists_min f
  have hrange : f u - f w ≤ (n - 1) * c := by
    classical
    obtain ⟨p⟩ := hconn u w
    have hp : (p.bypass.length : ℝ) ≤ n - 1 := by
      rw [hn, le_sub_iff_add_le]; exact_mod_cast p.bypass_isPath.length_lt
    exact (le_abs_self _).trans ((hwalk _).trans (by gcongr))
  -- a function of expectation zero has second moment at most `-(max f) (min f)`
  have hvar : 𝔼 v, f v ^ 2 ≤ -(f u * f w) := by
    have h (v : V) : f v ^ 2 ≤ (f u + f w) * f v - f u * f w := by
      nlinarith [hu v, hw v]
    calc 𝔼 v, f v ^ 2 ≤ 𝔼 v, ((f u + f w) * f v - f u * f w) := expect_le_expect fun v _ ↦ h v
      _ = -(f u * f w) := by rw [expect_sub_distrib, ← mul_expect, hf, Fintype.expect_const]; ring
  have hc2 : c ^ 2 = 4 * (d * n * Q) := Real.sq_sqrt (by positivity)
  have hrange0 : 0 ≤ f u - f w := sub_nonneg.2 (hw u)
  have hsq : (f u - f w) ^ 2 ≤ ((n - 1) * c) ^ 2 := pow_le_pow_left₀ hrange0 hrange 2
  have hn3 : (n - 1) ^ 2 * n ≤ n ^ 3 := by nlinarith
  calc 𝔼 v, f v ^ 2 ≤ (f u - f w) ^ 2 / 4 := by nlinarith [sq_nonneg (f u + f w)]
    _ ≤ ((n - 1) * c) ^ 2 / 4 := by gcongr
    _ = d * ((n - 1) ^ 2 * n) * Q := by rw [mul_pow, hc2]; ring
    _ ≤ d * n ^ 3 * Q := by gcongr

/-- On a connected graph with a self-loop at every vertex, one step of the walk multiplies the
second moment of a function of expectation zero by at most `1 - 1 / (|D| |V|³)`. -/
private theorem expect_walk_sq_le_one_sub_mul (hloop : ∀ v, ∃ i, G.neighbor v i = v)
    (hconn : G.toSimpleGraph.Preconnected) {f : V → ℝ} (hf : 𝔼 v, f v = 0) :
    𝔼 v, G.walk f v ^ 2 ≤
      (1 - 1 / (Fintype.card D * Fintype.card V ^ 3)) * 𝔼 v, f v ^ 2 := by
  have h := G.expect_sq_le_mul_sub_expect_walk_sq hloop hconn hf
  have h0 : 0 ≤ 𝔼 v, f v ^ 2 := expect_nonneg fun v _ ↦ sq_nonneg _
  set N : ℝ := Fintype.card D * Fintype.card V ^ 3
  rcases (show (0 : ℝ) ≤ N by positivity).eq_or_lt with hN | hN
  · rw [← hN, zero_mul] at h
    rw [← hN, div_zero, sub_zero, one_mul]
    have := G.expect_walk_sq_le f
    linarith [expect_nonneg (s := univ) fun v (_ : v ∈ univ) ↦ sq_nonneg (G.walk f v)]
  · rw [sub_mul, one_div_mul_eq_div, le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hN]
    linarith

/-- **A connected graph with self-loops has a spectral gap**, squared form: if `G` is connected and
has a self-loop at every vertex, then `λ(G)² ≤ 1 - 1 / (|D| |V|³)`. This is the bound the proof of
[Arora and Barak, draft of 2007-01-08, Lemma 7.28][AroraBarak07] establishes, with the sharper
constant that the draft's argument gives; Lemma 7.28 itself is
`Cslib.RotationMap.spectralExpansion_le_one_sub_of_preconnected_of_loop`. Unlike
`spectralExpansion_le_of_preconnected`, one self-loop per vertex suffices. -/
theorem spectralExpansion_sq_le_one_sub_of_preconnected_of_loop
    (hloop : ∀ v, ∃ i, G.neighbor v i = v) (hconn : G.toSimpleGraph.Preconnected) :
    G.spectralExpansion ^ 2 ≤ 1 - 1 / (Fintype.card D * Fintype.card V ^ 3) := by
  have h1 : 0 ≤ 1 - 1 / (Fintype.card D * Fintype.card V ^ 3 : ℝ) := by
    rcases isEmpty_or_nonempty V with hV | hV
    · simp
    obtain ⟨v₀⟩ := id hV
    have : Nonempty D := ⟨(hloop v₀).choose⟩
    rw [sub_nonneg]
    exact div_le_one_of_le₀ (one_le_mul_of_one_le_of_one_le (Nat.one_le_cast.2 Fintype.card_pos)
      (one_le_pow₀ (Nat.one_le_cast.2 Fintype.card_pos))) (by positivity)
  have h := G.spectralExpansion_le (Real.sqrt_nonneg _) fun f hf ↦ by
    rw [Real.sq_sqrt h1]
    exact G.expect_walk_sq_le_one_sub_mul hloop hconn hf
  calc G.spectralExpansion ^ 2 ≤ √(1 - 1 / (Fintype.card D * Fintype.card V ^ 3)) ^ 2 :=
        pow_le_pow_left₀ G.spectralExpansion_nonneg h 2
    _ = _ := Real.sq_sqrt h1

/-- **Arora–Barak, Lemma 7.28**
[Arora and Barak, draft of 2007-01-08, Lemma 7.28, p. 137][AroraBarak07]: a `d`-regular connected
graph on `n` vertices with a self-loop at every vertex has `λ(G) ≤ 1 - 1 / (8 d n³)`. Here `G` is a
regular multigraph given by its rotation map, `d = |D|`, `n = |V|`, and `λ(G)` is the absolute
spectral expansion, as in the draft. The squared form
`spectralExpansion_sq_le_one_sub_of_preconnected_of_loop` is stronger. -/
theorem spectralExpansion_le_one_sub_of_preconnected_of_loop
    (hloop : ∀ v, ∃ i, G.neighbor v i = v) (hconn : G.toSimpleGraph.Preconnected) :
    G.spectralExpansion ≤ 1 - 1 / (8 * Fintype.card D * Fintype.card V ^ 3) := by
  rcases isEmpty_or_nonempty V with hV | hV
  · rw [G.spectralExpansion_eq_zero_of_subsingleton]
    simp
  obtain ⟨v₀⟩ := id hV
  have : Nonempty D := ⟨(hloop v₀).choose⟩
  have h := G.spectralExpansion_sq_le_one_sub_of_preconnected_of_loop hloop hconn
  set N : ℝ := Fintype.card D * Fintype.card V ^ 3 with hNdef
  have hN1 : 1 ≤ N := one_le_mul_of_one_le_of_one_le (Nat.one_le_cast.2 Fintype.card_pos)
    (one_le_pow₀ (Nat.one_le_cast.2 Fintype.card_pos))
  have hN : (8 * Fintype.card D * Fintype.card V ^ 3 : ℝ) = 8 * N := by rw [hNdef]; ring
  rw [hN]
  have hb : 0 ≤ 1 - 1 / (8 * N) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    linarith
  refine (pow_le_pow_iff_left₀ G.spectralExpansion_nonneg hb two_ne_zero).1 (h.trans ?_)
  have e : (1 - 1 / (8 * N)) ^ 2 = 1 - 1 / N + (3 / (4 * N) + 1 / (64 * N ^ 2)) := by
    field_simp
    ring
  rw [e]
  linarith [show 0 ≤ 3 / (4 * N) + 1 / (64 * N ^ 2) by positivity]

end OneLoop
/-- A walk along the labels `k` in `G` gives a walk of at most `t` steps in the simple graph of
`G`; self-loops are skipped. -/
private theorem exists_walk_length_le_neighbor_pow (t : ℕ) (u : V) (k : Fin t → D) :
    ∃ w : G.toSimpleGraph.Walk u ((G.pow t).neighbor u k), w.length ≤ t := by
  induction t generalizing u with
  | zero => exact ⟨.nil, le_rfl⟩
  | succ t ih =>
    obtain ⟨w, hw⟩ := ih (G.neighbor u (k 0)) (Fin.tail k)
    rw [neighbor_pow_succ]
    by_cases hu : u = G.neighbor u (k 0)
    · exact ⟨w.copy hu.symm rfl, by rw [SimpleGraph.Walk.length_copy]; omega⟩
    · exact ⟨.cons (G.toSimpleGraph_adj.2 ⟨hu, k 0, rfl⟩) w,
        by rw [SimpleGraph.Walk.length_cons]; omega⟩

section Walks

variable [Fintype V] [Fintype D] [Nonempty D]

/-- **Pointwise mixing**: a uniformly random walk of length `t` from `u` ends at `v` with
probability `(G.walk ^ t) 1_{v} u` within `λ(G) ^ t (1 - 1 / |V|)` of `1 / |V|`. This is the mixing
lemma `sq_expect_mul_walk_pow_sub_le` for the indicator functions of `{u}` and `{v}`. -/
theorem abs_walk_pow_ite_eq_sub_le [DecidableEq V] (t : ℕ) (u v : V) :
    |(G.walk ^ t) (fun w ↦ if w = v then 1 else 0) u - 1 / Fintype.card V| ≤
      G.spectralExpansion ^ t * (1 - 1 / Fintype.card V) := by
  set N : ℝ := (Fintype.card V : ℝ) with hN
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨u⟩)
  set P := (G.walk ^ t) (fun w ↦ if w = v then 1 else 0) u
  have hexp (x : V) : 𝔼 w, (if w = x then 1 else 0 : ℝ) = 1 / N := by
    rw [Fintype.expect_eq_sum_div_card, sum_ite_eq', ite_eq_left (mem_univ _)]
  have hexp2 (x : V) : 𝔼 w, (if w = x then 1 else 0 : ℝ) ^ 2 = 1 / N := by
    rw [← hexp x]
    exact expect_congr rfl fun w _ ↦ by split_ifs <;> norm_num
  have hcorr : 𝔼 w, (if w = u then 1 else 0 : ℝ) *
      (G.walk ^ t) (fun w ↦ if w = v then 1 else 0) w = P / N := by
    rw [Fintype.expect_eq_sum_div_card]
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true, P, hN]
  have hmix := G.sq_expect_mul_walk_pow_sub_le t (fun w ↦ if w = u then 1 else 0)
    (fun w ↦ if w = v then 1 else 0)
  rw [hcorr, hexp u, hexp v, hexp2 u, hexp2 v] at hmix
  have e₁ : (P / N - 1 / N * (1 / N)) ^ 2 = (P - 1 / N) ^ 2 / N ^ 2 := by
    field_simp
  have e₂ : G.spectralExpansion ^ (2 * t) * (1 / N - (1 / N) ^ 2) * (1 / N - (1 / N) ^ 2) =
      (G.spectralExpansion ^ t * (1 - 1 / N)) ^ 2 / N ^ 2 := by
    rw [pow_mul']
    field_simp
  rw [e₁, e₂, div_le_div_iff_of_pos_right (by positivity)] at hmix
  have h0 : 0 ≤ G.spectralExpansion ^ t * (1 - 1 / N) := by
    refine mul_nonneg (pow_nonneg G.spectralExpansion_nonneg t) ?_
    rw [sub_nonneg, div_le_one hN0]
    exact Nat.one_le_cast.2 (Fintype.card_pos_iff.2 ⟨u⟩)
  rw [← abs_of_nonneg h0]
  exact sq_le_sq.1 hmix

/-- **Short walks in an expander reach every vertex.** If `λ(G) ^ t (|V| - 1) < 1`, then from every
vertex `u` some walk of length exactly `t` leads to any given vertex `v`: by pointwise mixing
(`abs_walk_pow_ite_eq_sub_le`), a uniformly random walk of length `t` from `u` ends at `v` with
probability at least `(1 - λ(G) ^ t (|V| - 1)) / |V|`. -/
theorem exists_neighbor_pow_eq {t : ℕ} (h : G.spectralExpansion ^ t * (Fintype.card V - 1) < 1)
    (u v : V) : ∃ k : Fin t → D, (G.pow t).neighbor u k = v := by
  classical
  by_contra hk
  simp only [not_exists] at hk
  set N : ℝ := (Fintype.card V : ℝ) with hN
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨u⟩)
  -- no walk of length `t` from `u` ends at `v`
  have hW : (G.walk ^ t) (fun w ↦ if w = v then 1 else 0) u = 0 := by
    rw [← walk_pow, walk_apply]
    exact Finset.expect_eq_zero fun k _ ↦ ite_eq_right (hk k)
  have hmix := G.abs_walk_pow_ite_eq_sub_le t u v
  rw [hW, zero_sub, abs_neg, abs_of_pos (by positivity), ← hN,
    show G.spectralExpansion ^ t * (1 - 1 / N) = G.spectralExpansion ^ t * (N - 1) / N by
      field_simp,
    div_le_div_iff_of_pos_right hN0] at hmix
  linarith

/-- **Expanders have logarithmic diameter** [Arora and Barak, Theorem 16.35][AroraBarak09]. If
`λ(G) < 1 / 4`, any two vertices are joined by a walk of at most `⌈log₄ |V|⌉` steps in the
simple graph of `G`. The draft states the bound `O(d log n)` for `d`-regular `n`-vertex graphs;
this bound does not depend on the degree `d = |D|`, so it is stronger. -/
theorem exists_walk_length_le_clog_of_spectralExpansion_lt (h : G.spectralExpansion < 1 / 4)
    (u v : V) : ∃ w : G.toSimpleGraph.Walk u v, w.length ≤ Nat.clog 4 (Fintype.card V) := by
  set t := Nat.clog 4 (Fintype.card V)
  have hN : (Fintype.card V : ℝ) ≤ 4 ^ t := by exact_mod_cast Nat.le_pow_clog (by norm_num) _
  have hlam : G.spectralExpansion ^ t ≤ (1 / 4) ^ t := by gcongr
  have hpos : (0 : ℝ) ≤ Fintype.card V - 1 := by
    rw [sub_nonneg]; exact Nat.one_le_cast.2 (Fintype.card_pos_iff.2 ⟨u⟩)
  obtain ⟨k, rfl⟩ := G.exists_neighbor_pow_eq (t := t) (by
    calc G.spectralExpansion ^ t * (Fintype.card V - 1) ≤ (1 / 4) ^ t * (Fintype.card V - 1) :=
          mul_le_mul_of_nonneg_right hlam hpos
      _ < (1 / 4) ^ t * 4 ^ t := by gcongr; linarith
      _ = 1 := by rw [← mul_pow]; norm_num) u v
  exact G.exists_walk_length_le_neighbor_pow t u k

end Walks

section PointwiseMixing

variable [Fintype V] [Fintype D]

/-- **Arora–Barak, Corollary 7.30**
[Arora and Barak, draft of 2007-01-08, Corollary 7.30, p. 138][AroraBarak07]: let `G` be a
`d`-regular graph on `n` vertices with a self-loop at every vertex, and let `T ≥ 10 d n³ log n`.
Then a random walk of `T` steps from `s` ends at any vertex `j` connected to `s` with probability
greater than `1 / (2 n)`.

Here `G` is a regular multigraph given by its rotation map, `d = |D|` and `n = |V|`. The walk
follows a uniformly random sequence `k` of `T` labels, so the probability is
`#{k | (G.pow T).neighbor s k = j} / d ^ T`, and `log` is the natural logarithm. The draft assumes
the strict `T > 10 d n³ log n`; the bound already holds at equality, and since `log n` is at most
the logarithm to any base below `e`, such as base `2`, those readings are covered too.

The proof is the draft's: on the connected component of `s` (`componentGraph`), which has at most
`n` vertices, `λ² ≤ 1 - 1 / (d n³)` (`spectralExpansion_sq_le_one_sub_of_preconnected_of_loop`), so
`λ ^ T ≤ n⁻⁵`, and pointwise mixing (`abs_walk_pow_ite_eq_sub_le`) on the component gives the bound.
The draft instead uses Lemma 7.28's `λ ≤ 1 - 1 / (8 d n³)`, which only gives `λ ^ T < n^(-5/4)`;
with the natural logarithm that is too weak for small `n` (at `n = 3` the resulting lower bound on
the probability is below `1 / (2 n)`). The squared bound, from the same argument, suffices. -/
theorem card_pow_lt_two_mul_card_mul_card_filter_neighbor_pow_eq [DecidableEq V]
    (hloop : ∀ v, ∃ i, G.neighbor v i = v) {s j : V} (hj : G.toSimpleGraph.Reachable s j) {T : ℕ}
    (hT : 10 * Fintype.card D * Fintype.card V ^ 3 * Real.log (Fintype.card V) ≤ T) :
    Fintype.card D ^ T < 2 * Fintype.card V * #{k : Fin T → D | (G.pow T).neighbor s k = j} := by
  classical
  have : Nonempty D := ⟨(hloop s).choose⟩
  set W := {v | G.toSimpleGraph.Reachable s v}
  set C := G.componentGraph s
  set s' : W := ⟨s, SimpleGraph.Reachable.refl s⟩
  set j' : W := ⟨j, hj⟩
  set n : ℝ := (Fintype.card V : ℝ) with hn
  set m : ℝ := (Fintype.card W : ℝ) with hm
  set d : ℝ := (Fintype.card D : ℝ) with hd
  have hn1 : 1 ≤ n := Nat.one_le_cast.2 (Fintype.card_pos_iff.2 ⟨s⟩)
  have hm1 : 1 ≤ m := Nat.one_le_cast.2 (Fintype.card_pos_iff.2 ⟨s'⟩)
  have hmn : m ≤ n := Nat.cast_le.2 (Fintype.card_subtype_le _)
  have hd1 : 1 ≤ d := Nat.one_le_cast.2 Fintype.card_pos
  -- the walks from `s` in `G` are those from `s` in the component
  have hcount : #{k : Fin T → D | (G.pow T).neighbor s k = j} =
      #{k : Fin T → D | (C.pow T).neighbor s' k = j'} := by
    congr 1
    ext k
    simp only [mem_filter, mem_univ, true_and, Subtype.ext_iff]
    exact Iff.of_eq (congrArg (· = j) ((G.componentHom s).neighbor_pow_map T s' k))
  have hP : (C.walk ^ T) (fun w ↦ if w = j' then 1 else 0) s' =
      #{k : Fin T → D | (C.pow T).neighbor s' k = j'} / d ^ T := by
    rw [← walk_pow, walk_apply, Fintype.expect_eq_sum_div_card, sum_boole, Fintype.card_fun,
      Fintype.card_fin, hd, Nat.cast_pow]
  -- the spectral gap of the component gives `λ ^ T ≤ n⁻⁵`
  have hgap := C.spectralExpansion_sq_le_one_sub_of_preconnected_of_loop
    (fun v ↦ ⟨(hloop v).choose, Subtype.ext (hloop v).choose_spec⟩)
    (G.preconnected_componentGraph s)
  rw [← hm, ← hd] at hgap
  set lam := C.spectralExpansion
  set a : ℝ := 1 / (d * m ^ 3) with ha
  have ha0 : 0 ≤ a := by positivity
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
  have haT : 10 * Real.log n ≤ a * T := by
    rw [ha, one_div_mul_eq_div, le_div_iff₀ (by positivity)]
    calc 10 * Real.log n * (d * m ^ 3) = 10 * d * m ^ 3 * Real.log n := by ring
      _ ≤ 10 * d * n ^ 3 * Real.log n := by gcongr
      _ ≤ T := hT
  have hexp : (lam ^ 2) ^ T ≤ (1 / n ^ 5) ^ 2 := by
    calc (lam ^ 2) ^ T ≤ (1 - a) ^ T :=
          pow_le_pow_left₀ (sq_nonneg _) hgap T
      _ ≤ Real.exp (-a) ^ T :=
          pow_le_pow_left₀ ((sq_nonneg lam).trans hgap) (by linarith [Real.add_one_le_exp (-a)]) T
      _ = Real.exp (-(a * T)) := by rw [← Real.exp_natCast_mul]; ring_nf
      _ ≤ Real.exp (-(10 * Real.log n)) := Real.exp_le_exp.2 (neg_le_neg haT)
      _ = (1 / n ^ 5) ^ 2 := by
          rw [Real.exp_neg, show (10 : ℝ) * Real.log n = ((10 : ℕ) : ℝ) * Real.log n by norm_num,
            Real.exp_natCast_mul, Real.exp_log (by linarith)]
          ring
  have hlamT : lam ^ T ≤ 1 / n ^ 5 := by
    rw [← pow_mul, mul_comm, pow_mul] at hexp
    exact (pow_le_pow_iff_left₀ (pow_nonneg C.spectralExpansion_nonneg T) (by positivity)
      two_ne_zero).1 hexp
  -- pointwise mixing on the component
  have hmix := C.abs_walk_pow_ite_eq_sub_le T s' j'
  rw [hP, ← hm] at hmix
  have hlow := (abs_le.1 hmix).1
  set P : ℝ := #{k : Fin T → D | (C.pow T).neighbor s' k = j'} / d ^ T
  have hx1 : 1 / n ^ 5 ≤ 1 := by rw [div_le_one (by positivity)]; exact one_le_pow₀ hn1
  have h1m : 0 ≤ 1 - 1 / m := by rw [sub_nonneg, div_le_one (by positivity)]; exact hm1
  set x : ℝ := 1 / n ^ 5 with hx
  have hx0 : 0 < x := by positivity
  have hxn : x * n ^ 5 = 1 := by rw [hx]; field_simp
  have hn5 : 2 * (n - 1) < n ^ 5 := by
    have : n ^ 2 ≤ n ^ 5 := pow_le_pow_right₀ hn1 (by norm_num)
    nlinarith
  have hkey : 2 * x * (n - 1) < 1 := by nlinarith
  have h6 : 1 / m * (1 + x) - x ≤ P := by linarith [mul_le_mul_of_nonneg_right hlamT h1m]
  have h7 : 1 / n * (1 + x) ≤ 1 / m * (1 + x) :=
    mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le (by positivity) hmn) (by positivity)
  have h8 : 1 / (2 * n) < 1 / n * (1 + x) - x := by
    rw [← sub_pos, show 1 / n * (1 + x) - x - 1 / (2 * n) = (1 - 2 * x * (n - 1)) / (2 * n) by
      field_simp; ring]
    exact div_pos (by linarith) (by positivity)
  have hP' : 1 / (2 * n) < P := by linarith
  rw [div_lt_div_iff₀ (by positivity) (by positivity), one_mul] at hP'
  rw [hcount, ← Nat.cast_lt (α := ℝ)]
  push_cast
  linarith

end PointwiseMixing

end Cslib.RotationMap
