/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.TSP
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Complexity.Problems.Hamiltonian.Undirected
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Data.List.Rotate
import Mathlib.Tactic.IntervalCases

/-!
# The traveling salesperson problem with symmetric distances

[Arora and Barak, Example 2.2][AroraBarak07] (printed p. 40 / PDF p. 56) gives TSP instances as
"a set of `n` nodes, `n choose 2` numbers `d_{i,j}` denoting the distances between all pairs of
nodes, and a number `k`", and Chapter 2, Exercise 17 (printed p. 64 / PDF p. 80) asks to prove
this language NP-complete. `SymTSP` is that language. An instance `x : SymTSPInstance` lists the
lower triangle of the distance matrix by rows: row `i` lists the distances `d_{i,0}, …, d_{i,i-1}`
from city `i` to the cities before it, so the `n` rows of a well-formed instance hold exactly
`n choose 2` binary numbers (`encSymTSP`). The cities are the row indices `0, …, n - 1`. As for
`Cslib.Complexity.TSP`, an entry missing from a short row reads `0`. The distance between two
cities is the same in both directions (`SymTSP.dist`), and the instance belongs to `SymTSP` when
some closed tour visiting every city exactly once has length at most `x.bound`. A tour of a single
city has length `0`.

`SymTSP` is in `NP` because it reduces to the general-matrix `TSP` by writing out the full
symmetric matrix with zero diagonal (`SymTSP.toTSP`). It is `NP`-hard because the reduction
`HamCycle.toTSP` from Hamiltonian cycles already produces symmetric distances: keeping the lower
triangle of its matrix (`SymTSP.ofMatrix`) loses nothing, since on two or more cities a tour never
uses a diagonal entry. Graphs with fewer than three vertices, for which `HamCycle.toTSP` returns a
one-city instance, are mapped to the two-city no-instance `⟨[[], [1]], 0⟩`.

## Main definitions

* `Cslib.Complexity.SymTSPInstance`, `Cslib.Complexity.encSymTSP`: symmetric instances as lower
  triangles of binary distances, with a binary budget.
* `Cslib.Complexity.SymTSP.dist`, `Cslib.Complexity.SymTSP.tourLength`, `Cslib.Complexity.SymTSP`.
* `Cslib.Complexity.SymTSP.toTSP`, `Cslib.Complexity.SymTSP.ofMatrix`,
  `Cslib.Complexity.HamCycle.toSymTSP`.

## Main results

* `Cslib.Complexity.SymTSP.toTSP_mem_iff`, `Cslib.Complexity.SymTSP.mem_NP`: `SymTSP ∈ NP`.
* `Cslib.Complexity.SymTSP.ofMatrix_mem_iff`: on two or more cities, a symmetric matrix instance of
  `TSP` and its lower triangle have the same answer.
* `Cslib.Complexity.HamCycle.toSymTSP_mem_iff`, `Cslib.Complexity.SymTSP_npHard`.
* `Cslib.Complexity.SymTSP_npComplete`: **Arora–Barak, Exercise 2.17 (TSP)**.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak07], Example 2.2
  and Chapter 2, Exercise 17.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

/-- An instance of the traveling salesperson problem with symmetric distances, in the format of
[Arora and Barak, Example 2.2][AroraBarak07]: the lower triangle `dist` of the distance matrix, by
rows, and a closed-tour budget `bound`. Row `i` lists the distances from city `i` to the cities
`0, …, i - 1`. -/
structure SymTSPInstance where
  /-- The lower triangle: entry `j` of row `i`, for `j < i`, is the distance between cities `i` and
  `j`. -/
  dist : List (List ℕ)
  /-- The maximum allowed total tour length. -/
  bound : ℕ
  deriving DecidableEq, Repr

/-- Symmetric instances, encoded as framed lists of the rows of the lower triangle, with binary
distances, followed by the binary budget. -/
enc_structure encSymTSP : SymTSPInstance where
  dist : (encList (encList encNat)), bound : encNat

namespace SymTSP

/-- The distance between cities `i` and `j` in the lower triangle `D`: entry `min i j` of row
`max i j`, and `0` from a city to itself. Entries missing from a short triangle read `0`. -/
@[expose] def dist (D : List (List ℕ)) (i j : ℕ) : ℕ :=
  if i = j then 0 else TSP.dist D (max i j) (min i j)

theorem dist_comm (D : List (List ℕ)) (i j : ℕ) : dist D i j = dist D j i := by
  unfold dist
  split_ifs with h h' h' <;> first | rfl | omega | rw [max_comm, min_comm]

/-- The length of the closed tour visiting the cities of `p` in order. -/
@[expose] def tourLength (D : List (List ℕ)) (p : List ℕ) : ℕ :=
  (List.zipWith (dist D) p (p.rotate 1)).sum

end SymTSP

/-- The traveling salesperson problem with symmetric distances
[Arora and Barak, Example 2.2][AroraBarak07]: the instances `x` such that some closed tour visiting
each city `0, …, x.dist.length - 1` exactly once has length at most `x.bound`. -/
@[expose] def SymTSP : Set SymTSPInstance :=
  {x | ∃ p : List ℕ, p.Perm (List.range x.dist.length) ∧
    SymTSP.tourLength x.dist p ≤ x.bound}

namespace SymTSP

/-! ### Tours only see the distances between their cities -/

private theorem sum_zipWith_rotate_congr {f g : ℕ → ℕ → ℕ} {p : List ℕ}
    (h : ∀ a ∈ p, ∀ b ∈ p, f a b = g a b) :
    (List.zipWith f p (p.rotate 1)).sum = (List.zipWith g p (p.rotate 1)).sum := by
  congr 1
  refine List.ext_getElem (by simp) fun k hk _ => ?_
  simp only [List.getElem_zipWith]
  exact h _ (List.getElem_mem _) _ ((List.mem_rotate).1 (List.getElem_mem _))

/-- On a duplicate-free tour of two or more cities, no step stays at a city, so the tour length only
depends on the distances between distinct cities. -/
private theorem sum_zipWith_rotate_congr_of_ne {f g : ℕ → ℕ → ℕ} {p : List ℕ}
    (hp : p.Nodup) (h2 : p.length ≠ 1) (h : ∀ a ∈ p, ∀ b ∈ p, a ≠ b → f a b = g a b) :
    (List.zipWith f p (p.rotate 1)).sum = (List.zipWith g p (p.rotate 1)).sum := by
  congr 1
  refine List.ext_getElem (by simp) fun k hk _ => ?_
  simp only [List.length_zipWith, List.length_rotate, Nat.min_self] at hk
  simp only [List.getElem_zipWith, List.getElem_rotate]
  refine h _ (List.getElem_mem _) _ (List.getElem_mem _) fun he => ?_
  have hlt : (k + 1) % p.length < p.length := Nat.mod_lt _ (by omega)
  have := (hp.getElem_inj_iff (hi := hk) (hj := hlt)).1 he
  rcases Nat.lt_or_ge (k + 1) p.length with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at this
    omega
  · rw [show k + 1 = p.length by omega, Nat.mod_self] at this
    omega

/-! ### Membership in `NP` -/

/-- The full symmetric distance matrix of a lower triangle, with zero diagonal. -/
@[expose] def toMatrix (D : List (List ℕ)) : List (List ℕ) :=
  (List.range D.length).map fun i => (List.range D.length).map fun j => dist D i j

/-- The reduction from `SymTSP` to `TSP`: write out the full symmetric matrix. -/
@[expose] def toTSP (x : SymTSPInstance) : TSPInstance :=
  ⟨toMatrix x.dist, x.bound⟩

theorem toTSP_mem_iff (x : SymTSPInstance) : toTSP x ∈ TSP ↔ x ∈ SymTSP := by
  have hlen : (toMatrix x.dist).length = x.dist.length := by simp [toMatrix]
  have hdist : ∀ i < x.dist.length, ∀ j < x.dist.length,
      TSP.dist (toMatrix x.dist) i j = dist x.dist i j := fun i hi j hj => by
    simp [TSP.dist, toMatrix, List.getD_eq_getElem?_getD, hi, hj]
  simp only [TSP, SymTSP, toTSP, Set.mem_ofPred_eq, hlen]
  refine exists_congr fun p => and_congr_right fun hp => ?_
  have hlt : ∀ a ∈ p, a < x.dist.length := fun a ha => List.mem_range.1 (hp.subset ha)
  rw [TSP.tourLength, tourLength,
    sum_zipWith_rotate_congr fun a ha b hb => hdist a (hlt a ha) b (hlt b hb)]

/-- Writing out the full symmetric matrix is polynomial-time. -/
theorem computableInPolyTime_toTSP : ComputableInPolyTime toTSP encSymTSP encTSP := by
  have hD : ComputableInPolyTime SymTSPInstance.dist encSymTSP (encList (encList encNat)) := by
    fun_prop
  have hn : ComputableInPolyTime (fun x : SymTSPInstance => x.dist.length) encSymTSP encUnary :=
    (length_list _).comp hD
  have hentry : ComputableInPolyTime
      (fun r : (SymTSPInstance × ℕ) × ℕ => dist r.1.1.dist r.1.2 r.2)
      (encPair (encPair encSymTSP encUnary) encUnary) encNat := by
    unfold dist TSP.dist
    fun_prop
  have hrow : ComputableInPolyTime
      (fun q : SymTSPInstance × ℕ =>
        (List.range q.1.dist.length).map fun j => dist q.1.dist q.2 j)
      (encPair encSymTSP encUnary) (encList encNat) :=
    mapWithInput (range.comp (hn.comp (fst _ _))) hentry
  exact encTSP_mk_polyTime (mapWithInput (range.comp hn) hrow) (by fun_prop)

/-- `SymTSP` reduces to `TSP` in polynomial time. -/
theorem polyTimeReducible_TSP : PolyTimeReducible encSymTSP encTSP SymTSP TSP :=
  ⟨toTSP, computableInPolyTime_toTSP, fun x => (toTSP_mem_iff x).symm⟩

/-- `SymTSP` belongs to `NP`. -/
theorem mem_NP : SymTSP ∈ NP encSymTSP :=
  polyTimeReducible_TSP.mem_NP TSP.mem_NP

/-! ### Lower triangles of symmetric matrices -/

/-- The lower triangle of a distance matrix: row `i` keeps its first `i` entries, missing entries
reading `0`. -/
@[expose] def ofMatrix (x : TSPInstance) : SymTSPInstance :=
  ⟨(List.range x.dist.length).map fun i => (List.range i).map fun j => TSP.dist x.dist i j,
    x.bound⟩

/-- On two or more cities, a `TSP` instance whose distances between distinct cities are symmetric
has the same answer as its lower triangle. -/
theorem ofMatrix_mem_iff (x : TSPInstance) (hn : x.dist.length ≠ 1)
    (hsymm : ∀ i < x.dist.length, ∀ j < x.dist.length, i ≠ j →
      TSP.dist x.dist i j = TSP.dist x.dist j i) :
    ofMatrix x ∈ SymTSP ↔ x ∈ TSP := by
  have hlen : (ofMatrix x).dist.length = x.dist.length := by simp [ofMatrix]
  have hdist : ∀ i < x.dist.length, ∀ j < x.dist.length, i ≠ j →
      dist (ofMatrix x).dist i j = TSP.dist x.dist i j := fun i hi j hj hij => by
    have hmax : max i j < x.dist.length := max_lt hi hj
    have hmin : min i j < max i j := by omega
    have hrow : TSP.dist (ofMatrix x).dist (max i j) (min i j) =
        TSP.dist x.dist (max i j) (min i j) := by
      simp [TSP.dist, ofMatrix, List.getD_eq_getElem?_getD, hmax, hmin]
    simp only [dist, hij, ↓reduceIte, hrow]
    rcases le_total i j with h | h
    · rw [max_eq_right h, min_eq_left h, hsymm j hj i hi (Ne.symm hij)]
    · rw [max_eq_left h, min_eq_right h]
  simp only [TSP, SymTSP, Set.mem_ofPred_eq, hlen]
  refine exists_congr fun p => and_congr_right fun hp => ?_
  have hlt : ∀ a ∈ p, a < x.dist.length := fun a ha => List.mem_range.1 (hp.subset ha)
  rw [tourLength, TSP.tourLength, show (ofMatrix x).bound = x.bound from rfl,
    sum_zipWith_rotate_congr_of_ne (hp.nodup_iff.2 List.nodup_range)
      (by rw [hp.length_eq, List.length_range]; exact hn)
      fun a ha b hb hab => hdist a (hlt a ha) b (hlt b hb) hab]

/-- Taking the lower triangle is polynomial-time. -/
theorem computableInPolyTime_ofMatrix : ComputableInPolyTime ofMatrix encTSP encSymTSP := by
  have hD : ComputableInPolyTime TSPInstance.dist encTSP (encList (encList encNat)) := by
    fun_prop
  have hn : ComputableInPolyTime (fun x : TSPInstance => x.dist.length) encTSP encUnary :=
    (length_list _).comp hD
  have hentry : ComputableInPolyTime
      (fun r : (TSPInstance × ℕ) × ℕ => TSP.dist r.1.1.dist r.1.2 r.2)
      (encPair (encPair encTSP encUnary) encUnary) encNat := by
    unfold TSP.dist
    fun_prop
  have hrow : ComputableInPolyTime
      (fun q : TSPInstance × ℕ => (List.range q.2).map fun j => TSP.dist q.1.dist q.2 j)
      (encPair encTSP encUnary) (encList encNat) :=
    mapWithInput (range.comp (snd _ _)) hentry
  exact encSymTSP_mk_polyTime (mapWithInput (range.comp hn) hrow) (by fun_prop)

end SymTSP

namespace HamCycle

/-! ### The reduction from Hamiltonian cycles -/

/-- The reduction from `HamCycle` to `SymTSP`: the lower triangle of `HamCycle.toTSP G`, whose
distances are `1` between adjacent and `2` between non-adjacent distinct vertices. Graphs with
fewer than three distinct vertices have no Hamiltonian cycle and are mapped to the two-city
no-instance at distance `1` with budget `0`. -/
@[expose] def toSymTSP (G : Graph) : SymTSPInstance :=
  if G.distinctVertices.length < 3 then ⟨[[], [1]], 0⟩ else SymTSP.ofMatrix (toTSP G)

theorem toSymTSP_mem_iff (G : Graph) : toSymTSP G ∈ SymTSP ↔ G ∈ HamCycle := by
  rw [← toTSP_mem_iff]
  unfold toSymTSP
  split_ifs with hn
  · simp only [toTSP, hn, ↓reduceIte, SymTSP, TSP, Set.mem_ofPred_eq, List.length_cons,
      List.length_nil]
    refine iff_of_false (fun ⟨p, hp, hle⟩ => ?_) fun ⟨p, hp, hle⟩ => ?_
    · obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 (by simpa using hp.length_eq)
      have ha : a < 2 := List.mem_range.1 (hp.subset (by simp))
      have hb : b < 2 := List.mem_range.1 (hp.subset (by simp))
      have hab : a ≠ b := by simpa using hp.nodup_iff.2 List.nodup_range
      revert hle
      interval_cases a <;> interval_cases b <;> first | omega | decide
    · rw [show p = [0] from List.perm_singleton.1 (by simpa using hp)] at hle
      revert hle
      decide
  · have hadj : ∀ u v, G.adjBool u v = G.adjBool v u := fun u v => Bool.eq_iff_iff.2 (by
      rw [Graph.adjBool_eq_true_iff, Graph.adjBool_eq_true_iff, SimpleGraph.adj_comm])
    refine SymTSP.ofMatrix_mem_iff _ ?_ fun i hi j hj _ => ?_
    · simp only [toTSP, hn, ↓reduceIte, List.length_map]
      omega
    · simp only [toTSP, hn, ↓reduceIte, List.length_map] at hi hj ⊢
      simp only [TSP.dist, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.map_some,
        Option.getD_some]
      rw [hadj]

/-- The reduction `toSymTSP` is polynomial-time. -/
theorem computableInPolyTime_toSymTSP : ComputableInPolyTime toSymTSP encGraph encSymTSP := by
  have hn : ComputableInPolyTime (fun G : Graph => G.distinctVertices.length) encGraph
      encUnary := (length_list _).comp Graph.computableInPolyTime_distinctVertices
  unfold toSymTSP
  exact (unary_lt' hn (const 3)).ite_decide (const _)
    (SymTSP.computableInPolyTime_ofMatrix.comp computableInPolyTime_toTSP)

end HamCycle

/-- `HamCycle` reduces to `SymTSP` in polynomial time via `HamCycle.toSymTSP`. -/
theorem polyTimeReducible_HamCycle_SymTSP : PolyTimeReducible encGraph encSymTSP HamCycle SymTSP :=
  ⟨HamCycle.toSymTSP, HamCycle.computableInPolyTime_toSymTSP,
    fun G => (HamCycle.toSymTSP_mem_iff G).symm⟩

/-- `SymTSP` is `NP`-hard. -/
theorem SymTSP_npHard : NPHard encSymTSP SymTSP :=
  HamCycle_npHard.trans polyTimeReducible_HamCycle_SymTSP

/-- **The traveling salesperson problem of Arora–Barak, Example 2.2 is NP-complete**
[Arora and Barak, Chapter 2, Exercise 17][AroraBarak07]: instances are `n` cities with the
`n choose 2` symmetric binary distances between them, as a lower triangle (`encSymTSP`), and a
binary budget. -/
theorem SymTSP_npComplete : NPComplete encSymTSP SymTSP :=
  ⟨SymTSP.mem_NP, SymTSP_npHard⟩

end Cslib.Complexity
