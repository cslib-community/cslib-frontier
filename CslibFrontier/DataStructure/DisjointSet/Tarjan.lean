/-
Copyright (c) 2026 Samuel Schlesinger, vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.DisjointSet.UnionFind
public import CslibFrontier.DataStructure.StateTransition.Amortized
public import CslibFrontier.Foundations.Data.Nat.InverseAckermann
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Iterate

/-!
# Inverse-Ackermann amortized step bounds for Union–Find

This module is an abstract step-count step toward `#3558` and `#5441` (not a registered cited
endpoint of [Tarjan1975] or [CLRS2009]): it proves inverse-Ackermann amortized upper bounds on the
abstract `findSteps`/link traces of `Cslib.DataStructure.DisjointSet.UnionFind.impl`
(`Batteries.UnionFind` with union by rank and full path compression) using
`Cslib.DataStructure.Amortized` certificates over `Execution.ofStep`.

The rank-shifted potential `potentialCore` adapts the level/iteration potential from
[CLRS2009] Section 21.4 (pp. 573–581, Lemmas 21.11–21.13 and Theorem 21.14) using the `+ d` rank
shift (`d := max 1 d ≥ 1`). Each node `i < uf.size` receives a potential built from the level
`k = ackLevel (uf.rank i + d) (uf.rank (uf.parent i) + d)` and iteration count
`i₀ = ackIter (uf.rank i + d) (uf.rank (uf.parent i) + d)` in the `(j + 1)`-fold hierarchy
`Nat.ackermann` so that
`ackermann k (uf.rank i + d) ≤ (ackermann k)^[i₀] (uf.rank i + d) ≤ uf.rank (uf.parent i) + d`.
Shifting node ranks by `d ≥ 1` ensures `1 ≤ uf.rank i + d` everywhere, avoiding separate
rank-zero handling during `find`.

A single parameterized potential `potentialCore zeroSingletons q d uf` unifies two regimes:

1. **`zeroSingletons = true, d = 1` (`tarjanAmortized`)**: initial potential at `init n` is `0`,
   giving single-parameter amortized charges `2 * α(n) + 2` for `Op.same`, `5 * α(n) + 2` for
   `Op.union`, and `1` for `Op.numComponents`, hence `total id traces ≤ m * (5 * α(n) + 2)`.
2. **`zeroSingletons = false, d = m / n + 1` (`tarjanAmortizedAt`)**: initial potential at
   `init n` is `n * (q * (m / n + 1))`, while each `link` has amortized charge at most `q`. When
   `n ≤ m`, `n * (m / n + 1) ≤ 2 * m`, yielding the two-parameter step bound
   `total id traces ≤ m * (5 * α(m, n) + 2)` (`tarjan_run_two_param`) for every `m, n`, together
   with the linear `7 * m` corollary once `n * Nat.log 2 n ≤ m` (`tarjan_run_linear_of_dense`).

## Cost model and scope

Like `Cslib.DataStructure.DisjointSet.UnionFind`, `total id traces` counts only the exact abstract
forest steps recorded by `UnionFind.step` (`findSteps` parent-pointer inspections per `find`, `1`
link step per `Op.union`, and `1` counter read per `Op.numComponents`), excluding the `O(n)`
creation of `init n`. These theorems make no Word-RAM or pointer-machine instruction-cost claim
(`#3558`, `#5441`). Moreover, `Nat.inverseAckermannTwo m n` uses shift `d = m / n + 1` in the
[CLRS2009] recurrence rather than [Tarjan1975]'s `4 * ⌈m / n⌉` threshold convention, matching
Tarjan's bound only up to small constant shifts/factors and the omitted `init n` cost.

## Main definitions

* `tarjanPotential`, `tarjanCharge`: single-parameter CLRS/Tarjan potential and operation charges.
* `tarjanPotentialAt`, `tarjanChargeAt`: rank-shifted potential and per-operation charges for the
  two-parameter step analysis.

## Main results

* `tarjanAmortized`, `tarjanUniformAmortized`: `Amortized` certificates for the single-parameter
  `O(α(n))` abstract step bound.
* `tarjan_run_correct`: adaptive client correctness and `m * (5 * α(n) + 2)` abstract step bound
  from `init n`.
* `tarjanAmortizedAt`, `tarjanUniformAmortizedAt`: `Amortized` certificates parameterized by `d`.
* `tarjan_run_two_param`: two-parameter `m * (5 * α(m, n) + 2)` abstract step bound for all
  universe sizes `n` and operation counts `m` (step toward `#3558` and `#5441`).
* `tarjan_run_linear_of_dense`: linear `total id traces ≤ 7 * m` abstract step corollary whenever
  `n * Nat.log 2 n ≤ m`.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein, *Introduction to Algorithms* (3rd
  ed.), MIT Press, 2009, Section 21.4, pp. 573–581 (Lemmas 21.11–21.13, Theorem 21.14)][CLRS2009].
* [R. E. Tarjan, *Efficiency of a Good But Not Linear Set Union Algorithm*, JACM 22(2),
  pp. 215–225, 1975][Tarjan1975].
* [D. C. Kozen, *The Design and Analysis of Algorithms*, Lectures 10–11, pp. 48–57,
  1992][Kozen1992].
-/

public section

namespace Cslib.DataStructure.DisjointSet.UnionFind

open Cslib.DataStructure Cslib.DataStructure.DisjointSet

private theorem rank_compressWithSteps (uf : Batteries.UnionFind) (x : Fin uf.size) (i : ℕ) :
    (compressWithSteps uf x).1.rank i = uf.rank i := by
  rw [compressWithSteps_fst, find_rank]

/-! ### Find-path traversal and path compression characterization -/

private def findPathGo (uf : Batteries.UnionFind) : ℕ → Fin uf.size → List ℕ
  | 0, x => [x.1]
  | fuel + 1, x =>
    let y := uf.arr[x.1].parent
    if y = x.1 then [x.1]
    else x.1 :: findPathGo uf fuel ⟨y, uf.parent'_lt x.1 x.2⟩

private def findPath (uf : Batteries.UnionFind) (x : Fin uf.size) : List ℕ :=
  findPathGo uf (rankBound uf) x

private theorem findPathGo_length_eq (uf : Batteries.UnionFind) :
    ∀ (fuel : ℕ) (x : Fin uf.size),
      (findPathGo uf fuel x).length = (findGo uf fuel x).2
  | 0, _ => rfl
  | fuel + 1, x => by
    rw [findPathGo, findGo]
    dsimp only
    split
    · rfl
    · simp only [List.length_cons,
        findPathGo_length_eq uf fuel ⟨uf.arr[x.1].parent, uf.parent'_lt x.1 x.2⟩]

private theorem findPath_length (uf : Batteries.UnionFind) (x : Fin uf.size) :
    (findPath uf x).length = findSteps uf x :=
  findPathGo_length_eq uf (rankBound uf) x

private theorem findPathGo_mem_lt (uf : Batteries.UnionFind) :
    ∀ (fuel : ℕ) (x : Fin uf.size) {u : ℕ},
      u ∈ findPathGo uf fuel x → u < uf.size
  | 0, x, _, hu => List.mem_singleton.mp hu ▸ x.2
  | fuel + 1, x, _, hu => by
    rw [findPathGo] at hu
    split at hu
    · exact List.mem_singleton.mp hu ▸ x.2
    · rcases List.mem_cons.mp hu with rfl | htail
      · exact x.2
      · exact findPathGo_mem_lt uf fuel ⟨uf.arr[x.1].parent, uf.parent'_lt x.1 x.2⟩ htail

private theorem findPath_mem_lt (uf : Batteries.UnionFind) (x : Fin uf.size) {u : ℕ}
    (hu : u ∈ findPath uf x) : u < uf.size :=
  findPathGo_mem_lt uf (rankBound uf) x hu

private theorem findPathGo_rank_ge (uf : Batteries.UnionFind) :
    ∀ (fuel : ℕ) (x : Fin uf.size) {u : ℕ},
      u ∈ findPathGo uf fuel x → uf.rank x.1 ≤ uf.rank u
  | 0, x, _, hu => List.mem_singleton.mp hu ▸ Nat.le_refl _
  | fuel + 1, x, _, hu => by
    rw [findPathGo] at hu
    split at hu
    · exact List.mem_singleton.mp hu ▸ Nat.le_refl _
    · next h =>
      rcases List.mem_cons.mp hu with rfl | htail
      · exact Nat.le_refl _
      · exact (Nat.le_of_lt (uf.rank'_lt x.1 x.2 h)).trans
          (findPathGo_rank_ge uf fuel ⟨uf.arr[x.1].parent, uf.parent'_lt x.1 x.2⟩ htail)

private theorem findPathGo_pairwise_rank_lt (uf : Batteries.UnionFind) :
    ∀ (fuel : ℕ) (x : Fin uf.size),
      (findPathGo uf fuel x).Pairwise (fun u v => uf.rank u < uf.rank v)
  | 0, x => by simp [findPathGo]
  | fuel + 1, x => by
    rw [findPathGo]
    split
    · simp
    · next h =>
      rw [List.pairwise_cons]
      refine ⟨fun v hv => ?_, findPathGo_pairwise_rank_lt uf fuel _⟩
      exact lt_of_lt_of_le (uf.rank'_lt x.1 x.2 h)
        (findPathGo_rank_ge uf fuel ⟨uf.arr[x.1].parent, uf.parent'_lt x.1 x.2⟩ hv)

private theorem findPath_nodup (uf : Batteries.UnionFind) (x : Fin uf.size) :
    (findPath uf x).Nodup :=
  List.nodup_iff_pairwise_ne.mpr
    ((findPathGo_pairwise_rank_lt uf (rankBound uf) x).imp fun hlt heq =>
      Nat.ne_of_lt hlt (congrArg uf.rank heq))

private theorem findPath_rank_ne_of_ne (uf : Batteries.UnionFind) (x : Fin uf.size) {u v : ℕ}
    (hu : u ∈ findPath uf x) (hv : v ∈ findPath uf x) (hne : u ≠ v) :
    uf.rank u < uf.rank v ∨ uf.rank v < uf.rank u := by
  have hpw : (findPath uf x).Pairwise
      (fun a b => uf.rank a < uf.rank b ∨ uf.rank b < uf.rank a) :=
    (findPathGo_pairwise_rank_lt uf (rankBound uf) x).imp Or.inl
  have : Std.Symm (fun a b => uf.rank a < uf.rank b ∨ uf.rank b < uf.rank a) :=
    ⟨fun _ _ => Or.symm⟩
  exact hpw.forall hu hv hne

private theorem findPathGo_rootD (uf : Batteries.UnionFind) :
    ∀ (fuel : ℕ) (x : Fin uf.size) {u : ℕ},
      u ∈ findPathGo uf fuel x → uf.rootD u = uf.rootD x.1
  | 0, x, _, hu => List.mem_singleton.mp hu ▸ rfl
  | fuel + 1, x, _, hu => by
    rw [findPathGo] at hu
    split at hu
    · exact List.mem_singleton.mp hu ▸ rfl
    · rcases List.mem_cons.mp hu with rfl | htail
      · rfl
      · rw [findPathGo_rootD uf fuel ⟨uf.arr[x.1].parent, uf.parent'_lt x.1 x.2⟩ htail]
        exact (congrArg uf.rootD (Batteries.UnionFind.parentD_eq x.2).symm).trans
          (Batteries.UnionFind.rootD_parent uf x.1)

private theorem findPath_rootD (uf : Batteries.UnionFind) (x : Fin uf.size) {u : ℕ}
    (hu : u ∈ findPath uf x) : uf.rootD u = uf.rootD x.1 :=
  findPathGo_rootD uf (rankBound uf) x hu

private theorem findPathGo_parent_rank_le (uf : Batteries.UnionFind) :
    ∀ (fuel : ℕ) (x : Fin uf.size) {u v : ℕ},
      u ∈ findPathGo uf fuel x → v ∈ findPathGo uf fuel x →
      uf.rank u < uf.rank v → uf.rank (uf.parent u) ≤ uf.rank v
  | 0, x, _, _, hu, hv, hlt => by
    simp only [findPathGo, List.mem_singleton] at hu hv
    subst hu hv
    exact absurd hlt (Nat.lt_irrefl _)
  | fuel + 1, x, u, v, hu, hv, hlt => by
    by_cases h : uf.arr[x.1].parent = x.1
    · simp only [findPathGo, ite_eq_left h, List.mem_singleton] at hu hv
      subst hu hv
      exact absurd hlt (Nat.lt_irrefl _)
    · simp only [findPathGo, ite_eq_right h, List.mem_cons] at hu hv
      let y : Fin uf.size := ⟨uf.arr[x.1].parent, uf.parent'_lt x.1 x.2⟩
      have hxy : uf.rank x.1 < uf.rank y.1 := uf.rank'_lt x.1 x.2 h
      rcases hu with rfl | hu <;> rcases hv with rfl | hv
      · exact absurd hlt (Nat.lt_irrefl _)
      · exact le_of_eq_of_le (congrArg uf.rank (Batteries.UnionFind.parentD_eq x.2))
          (findPathGo_rank_ge uf fuel y hv)
      · exact absurd (hxy.trans_le (findPathGo_rank_ge uf fuel y hu)) (Nat.not_lt.mpr hlt.le)
      · exact findPathGo_parent_rank_le uf fuel y hu hv hlt

private theorem findPath_parent_rank_le (uf : Batteries.UnionFind) (x : Fin uf.size) {u v : ℕ}
    (hu : u ∈ findPath uf x) (hv : v ∈ findPath uf x) (hlt : uf.rank u < uf.rank v) :
    uf.rank (uf.parent u) ≤ uf.rank v :=
  findPathGo_parent_rank_le uf (rankBound uf) x hu hv hlt

private theorem parentD_findAux_eq_findPathGo (uf : Batteries.UnionFind) :
    ∀ (fuel : ℕ) (x : Fin uf.size) (i : ℕ),
      uf.rankMax - uf.rank x.1 ≤ fuel →
      Batteries.UnionFind.parentD (uf.findAux x).s i =
        if i ∈ findPathGo uf fuel x then uf.rootD x.1 else uf.parent i
  | 0, x, _, hle => by
    have hlt := uf.lt_rankMax x.1
    omega
  | fuel + 1, x, i, hle => by
    by_cases h : uf.arr[x.1].parent = x.1
    · rw [Batteries.UnionFind.findAux_s, ite_eq_left h, findPathGo, ite_eq_left h]
      split_ifs with him
      · rw [List.mem_singleton] at him
        subst him
        have hxroot : uf.parent x.1 = x.1 := (Batteries.UnionFind.parentD_eq x.2).trans h
        exact hxroot.trans (Batteries.UnionFind.rootD_eq_self.mpr hxroot).symm
      · rfl
    · have ih := parentD_findAux_eq_findPathGo uf fuel ⟨uf.arr[x.1].parent, uf.parent'_lt x.1 x.2⟩ i
        (by
          dsimp only
          have hxy := uf.rank'_lt x.1 x.2 h
          have hmax := uf.lt_rankMax x.1
          omega)
      have hyroot : uf.rootD uf.arr[x.1].parent = uf.rootD x.1 := by
        rw [← Batteries.UnionFind.parentD_eq x.2, Batteries.UnionFind.rootD_parent]
      rw [Batteries.UnionFind.parentD_findAux, findPathGo, ite_eq_right h]
      by_cases hi : i = x.1
      · subst hi
        rw [ite_eq_left rfl, ite_eq_left List.mem_cons_self]
      · rw [ite_eq_right hi, ih, hyroot]
        simp only [List.mem_cons, hi, false_or]

private theorem parent_compressWithSteps (uf : Batteries.UnionFind) (x : Fin uf.size) (i : ℕ) :
    (compressWithSteps uf x).1.parent i =
      if i ∈ findPath uf x then uf.rootD x.1 else uf.parent i := by
  rw [compressWithSteps_fst, find_parent_eq_parentD_findAux]
  exact parentD_findAux_eq_findPathGo uf (rankBound uf) x i
    (by rw [rankBound_eq_rankMax]; exact Nat.sub_le _ _)

private theorem parent_compressWithSteps_eq_self_iff (uf : Batteries.UnionFind) (x : Fin uf.size)
    (i : ℕ) : (compressWithSteps uf x).1.parent i = i ↔ uf.parent i = i := by
  rw [parent_compressWithSteps]
  split_ifs with hi
  · rw [← findPath_rootD uf x hi, Batteries.UnionFind.rootD_eq_self]
  · rfl

/-! ### Level, iteration index, and non-root potential -/

private theorem exists_lt_ackermann {r : ℕ} (hr : 1 ≤ r) (p : ℕ) :
    ∃ k, p < Nat.ackermann k r :=
  ⟨p, Nat.lt_of_le_of_lt (Nat.le_add_left p r) (Nat.add_lt_ackermann p hr)⟩

private noncomputable def ackLevel (r p : ℕ) : ℕ :=
  if h : 1 ≤ r ∧ r < p then Nat.find (exists_lt_ackermann h.1 p) - 1 else 0

private theorem find_lt_ackermann_pos {r p : ℕ} (hr : 1 ≤ r) (hrp : r < p) :
    1 ≤ Nat.find (exists_lt_ackermann hr p) := by
  by_contra h
  have h0 : Nat.find (exists_lt_ackermann hr p) = 0 := by omega
  have hspec := Nat.find_spec (exists_lt_ackermann hr p)
  rw [h0, Nat.ackermann_zero] at hspec
  omega

private theorem ackermann_ackLevel_le {r p : ℕ} (hr : 1 ≤ r) (hrp : r < p) :
    Nat.ackermann (ackLevel r p) r ≤ p := by
  unfold ackLevel
  rw [dite_eq_left ⟨hr, hrp⟩]
  exact Nat.not_lt.mp (Nat.find_min (exists_lt_ackermann hr p)
    (Nat.sub_lt (find_lt_ackermann_pos hr hrp) Nat.one_pos))

private theorem lt_ackermann_ackLevel_succ {r p : ℕ} (hr : 1 ≤ r) (hrp : r < p) :
    p < Nat.ackermann (ackLevel r p + 1) r := by
  unfold ackLevel
  rw [dite_eq_left ⟨hr, hrp⟩, Nat.sub_add_cancel (find_lt_ackermann_pos hr hrp)]
  exact Nat.find_spec (exists_lt_ackermann hr p)

private theorem le_ackLevel_of_ackermann_le {r p k : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hle : Nat.ackermann k r ≤ p) : k ≤ ackLevel r p := by
  by_contra h
  have hsucc : ackLevel r p + 1 ≤ k := Nat.lt_of_not_ge h
  have hlt := lt_ackermann_ackLevel_succ hr hrp
  have hmono : Nat.ackermann (ackLevel r p + 1) r ≤ Nat.ackermann k r :=
    Nat.ackermann_monotone_left r hsucc
  omega

private theorem ackLevel_lt_of_lt_ackermann {r p q : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hlt : p < Nat.ackermann q r) : ackLevel r p < q := by
  unfold ackLevel
  rw [dite_eq_left ⟨hr, hrp⟩]
  have hpos := find_lt_ackermann_pos hr hrp
  have hmin : Nat.find (exists_lt_ackermann hr p) ≤ q := Nat.find_min' _ hlt
  omega

private theorem ackLevel_mono {r p₁ p₂ : ℕ} (hr : 1 ≤ r) (hrp₁ : r < p₁) (hle : p₁ ≤ p₂) :
    ackLevel r p₁ ≤ ackLevel r p₂ :=
  le_ackLevel_of_ackermann_le hr (lt_of_lt_of_le hrp₁ hle)
    ((ackermann_ackLevel_le hr hrp₁).trans hle)

private theorem exists_lt_iterate_ackermann {r p : ℕ} (hr : 1 ≤ r) (hrp : r < p) :
    ∃ i, p < (Nat.ackermann (ackLevel r p))^[i] r :=
  ⟨r + 1, lt_ackermann_ackLevel_succ hr hrp⟩

private noncomputable def ackIter (r p : ℕ) : ℕ :=
  if h : 1 ≤ r ∧ r < p then Nat.find (exists_lt_iterate_ackermann h.1 h.2) - 1 else 0

private theorem two_le_find_iterate {r p : ℕ} (hr : 1 ≤ r) (hrp : r < p) :
    2 ≤ Nat.find (exists_lt_iterate_ackermann hr hrp) := by
  by_contra h
  have hle : Nat.find (exists_lt_iterate_ackermann hr hrp) ≤ 1 := by omega
  have hspec := Nat.find_spec (exists_lt_iterate_ackermann hr hrp)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
  · rw [h0, Function.iterate_zero_apply] at hspec
    omega
  · rw [h1, Function.iterate_one] at hspec
    have hack := ackermann_ackLevel_le hr hrp
    omega

private theorem one_le_ackIter {r p : ℕ} (hr : 1 ≤ r) (hrp : r < p) : 1 ≤ ackIter r p := by
  unfold ackIter
  rw [dite_eq_left ⟨hr, hrp⟩]
  have h2 := two_le_find_iterate hr hrp
  omega

private theorem ackIter_le {r p : ℕ} (hr : 1 ≤ r) (hrp : r < p) : ackIter r p ≤ r := by
  unfold ackIter
  rw [dite_eq_left ⟨hr, hrp⟩]
  have hmin : Nat.find (exists_lt_iterate_ackermann hr hrp) ≤ r + 1 :=
    Nat.find_min' _ (lt_ackermann_ackLevel_succ hr hrp)
  omega

private theorem iterate_ackermann_ackIter_le {r p : ℕ} (hr : 1 ≤ r) (hrp : r < p) :
    (Nat.ackermann (ackLevel r p))^[ackIter r p] r ≤ p := by
  unfold ackIter
  rw [dite_eq_left ⟨hr, hrp⟩]
  exact Nat.not_lt.mp (Nat.find_min (exists_lt_iterate_ackermann hr hrp)
    (Nat.sub_lt (Nat.zero_lt_of_lt (two_le_find_iterate hr hrp)) Nat.zero_lt_one))

private theorem lt_iterate_ackermann_ackIter_succ {r p : ℕ} (hr : 1 ≤ r) (hrp : r < p) :
    p < (Nat.ackermann (ackLevel r p))^[ackIter r p + 1] r := by
  unfold ackIter
  rw [dite_eq_left ⟨hr, hrp⟩,
    Nat.sub_add_cancel (Nat.le_of_lt (two_le_find_iterate hr hrp))]
  exact Nat.find_spec (exists_lt_iterate_ackermann hr hrp)

private theorem le_ackIter_of_iterate_le {r p i : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hle : (Nat.ackermann (ackLevel r p))^[i] r ≤ p) : i ≤ ackIter r p := by
  by_contra h
  have hsucc : ackIter r p + 1 ≤ i := Nat.lt_of_not_ge h
  have hlt := lt_iterate_ackermann_ackIter_succ hr hrp
  have hmono : (Nat.ackermann (ackLevel r p))^[ackIter r p + 1] r ≤
      (Nat.ackermann (ackLevel r p))^[i] r :=
    Function.monotone_iterate_of_id_le (f := Nat.ackermann (ackLevel r p))
      (fun x => Nat.le_of_lt (Nat.lt_ackermann _ x)) hsucc r
  omega

private noncomputable def nonRootPhi (q r p : ℕ) : ℕ :=
  (q - ackLevel r p) * r - ackIter r p

private theorem ackIter_le_mul {q r p : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hpq : p < Nat.ackermann q r) : ackIter r p ≤ (q - ackLevel r p) * r :=
  (ackIter_le hr hrp).trans
    (Nat.le_mul_of_pos_left r (Nat.sub_pos_of_lt (ackLevel_lt_of_lt_ackermann hr hrp hpq)))

private theorem nonRootPhi_le_mul_sub_one {q r p : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hpq : p < Nat.ackermann q r) : nonRootPhi q r p + 1 ≤ q * r := by
  have h1 : 1 ≤ ackIter r p := one_le_ackIter hr hrp
  have himul : ackIter r p ≤ (q - ackLevel r p) * r := ackIter_le_mul hr hrp hpq
  have hqmul : (q - ackLevel r p) * r ≤ q * r := Nat.mul_le_mul_right r (Nat.sub_le q _)
  unfold nonRootPhi
  omega

private theorem nonRootPhi_lt_of_level_lt {q r p p' : ℕ} (hr : 1 ≤ r) (hrp : r < p) (hp : p ≤ p')
    (hp'q : p' < Nat.ackermann q r) (hklt : ackLevel r p < ackLevel r p') :
    nonRootPhi q r p' + 1 ≤ nonRootPhi q r p := by
  have hrp' : r < p' := lt_of_lt_of_le hrp hp
  have hk' : ackLevel r p' < q := ackLevel_lt_of_lt_ackermann hr hrp' hp'q
  have hi : ackIter r p ≤ r := ackIter_le hr hrp
  have hi'1 : 1 ≤ ackIter r p' := one_le_ackIter hr hrp'
  have hi'mul : ackIter r p' ≤ (q - ackLevel r p') * r := ackIter_le_mul hr hrp' hp'q
  have hq : (q - ackLevel r p') + 1 ≤ q - ackLevel r p := by omega
  have hmul : (q - ackLevel r p') * r + r ≤ (q - ackLevel r p) * r := by
    calc
      (q - ackLevel r p') * r + r = ((q - ackLevel r p') + 1) * r := (Nat.succ_mul _ _).symm
      _ ≤ (q - ackLevel r p) * r := Nat.mul_le_mul_right r hq
  unfold nonRootPhi
  omega

private theorem nonRootPhi_le_of_le {q r p p' : ℕ} (hr : 1 ≤ r) (hrp : r < p) (hp : p ≤ p')
    (hp'q : p' < Nat.ackermann q r) :
    nonRootPhi q r p' ≤ nonRootPhi q r p := by
  rcases Nat.eq_or_lt_of_le (ackLevel_mono hr hrp hp) with heq | hlt
  · unfold nonRootPhi
    rw [heq]
    refine Nat.sub_le_sub_left (le_ackIter_of_iterate_le hr (lt_of_lt_of_le hrp hp) ?_) _
    rw [← heq]
    exact (iterate_ackermann_ackIter_le hr hrp).trans hp
  · exact (Nat.le_succ _).trans (nonRootPhi_lt_of_level_lt hr hrp hp hp'q hlt)

private theorem nonRootPhi_lt_of_step {q r p p' : ℕ} (hr : 1 ≤ r) (hrp : r < p) (hp : p ≤ p')
    (hp'q : p' < Nat.ackermann q r)
    (hstep : (Nat.ackermann (ackLevel r p))^[ackIter r p + 1] r ≤ p') :
    nonRootPhi q r p' + 1 ≤ nonRootPhi q r p := by
  have hrp' : r < p' := lt_of_lt_of_le hrp hp
  rcases Nat.eq_or_lt_of_le (ackLevel_mono hr hrp hp) with heq | hlt
  · have hir : ackIter r p < r := (ackIter_le hr hrp).lt_of_ne fun hir_eq =>
      (le_ackLevel_of_ackermann_le hr hrp' (by rwa [hir_eq] at hstep)).not_gt
        (heq.symm.trans_lt (Nat.lt_succ_self _))
    have hiter : ackIter r p + 1 ≤ ackIter r p' :=
      le_ackIter_of_iterate_le hr hrp' (by rwa [← heq])
    have himul' : ackIter r p' ≤ (q - ackLevel r p') * r := ackIter_le_mul hr hrp' hp'q
    unfold nonRootPhi
    rw [← heq] at himul' ⊢
    omega
  · exact nonRootPhi_lt_of_level_lt hr hrp hp hp'q hlt

/-! ### Unified node potential and find/link step inequalities -/

private noncomputable def nodePotential (zeroSingletons : Bool) (q d : ℕ)
    (uf : Batteries.UnionFind) (i : ℕ) : ℕ :=
  if uf.parent i = i then
    if zeroSingletons && uf.rank i = 0 then 0 else q * (uf.rank i + d)
  else
    nonRootPhi q (uf.rank i + d) (uf.rank (uf.parent i) + d)

private noncomputable def potentialCore (zeroSingletons : Bool) (q d : ℕ)
    (uf : Batteries.UnionFind) : ℕ :=
  ∑ i ∈ Finset.range uf.size, nodePotential zeroSingletons q d uf i

private theorem potentialCore_true_ofSize (q d n : ℕ) :
    potentialCore true q d (ofSize n) = 0 := by
  unfold potentialCore nodePotential
  simp

private theorem potentialCore_false_ofSize (q d n : ℕ) :
    potentialCore false q d (ofSize n) = n * (q * d) := by
  unfold potentialCore nodePotential
  simp only [size_ofSize, parent_ofSize, ↓reduceIte, Bool.false_and, Bool.false_eq_true,
    rank_ofSize, Nat.zero_add]
  rw [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]

private theorem findSteps_add_potentialCore_le {uf : Batteries.UnionFind}
    (hvalid : ValidRank uf) {q d : ℕ} (hd : 1 ≤ d)
    (hbound : Nat.log 2 uf.size + d < Nat.ackermann q d)
    (zs : Bool) (x : Fin uf.size) :
    findSteps uf x + potentialCore zs q d (compressWithSteps uf x).1 ≤
      (q + 1) + potentialCore zs q d uf := by
  set uf' := (compressWithSteps uf x).1
  let S : Finset ℕ := (findPath uf x).toFinset
  have hS_sub : S ⊆ Finset.range uf.size := fun u hu =>
    Finset.mem_range.mpr (findPath_mem_lt uf x (List.mem_toFinset.mp hu))
  have hS_card : S.card = findSteps uf x := by
    rw [List.toFinset_card_of_nodup (findPath_nodup uf x), findPath_length]
  let lvl := fun u => ackLevel (uf.rank u + d) (uf.rank (uf.parent u) + d)
  let S_drop : Finset ℕ := S.filter fun u =>
    uf.parent u ≠ u ∧ ∃ v ∈ S, uf.rank u < uf.rank v ∧ uf.parent v ≠ v ∧ lvl u = lvl v
  let S_keep : Finset ℕ := S \ S_drop
  have hdrop_sub : S_drop ⊆ Finset.range uf.size :=
    (Finset.filter_subset _ _).trans hS_sub
  have hpath_bounds : ∀ u, uf.parent u ≠ u →
      1 ≤ uf.rank u + d ∧
      uf.rank u + d < uf.rank (uf.parent u) + d ∧
      uf.rank (uf.parent u) + d ≤ uf.rank (uf.rootD u) + d ∧
      uf.rank (uf.rootD u) + d < Nat.ackermann q (uf.rank u + d) := by
    intro u hroot
    refine ⟨Nat.le_trans hd (Nat.le_add_left d _),
      Nat.add_lt_add_right (uf.rank_lt hroot) d, ?_, ?_⟩
    · have := Batteries.UnionFind.le_rank_root (self := uf) (x := uf.parent u)
      rw [Batteries.UnionFind.rootD_parent] at this
      omega
    · have hlog := hvalid.rank_le_log (uf.rootD u)
      have hack := Nat.ackermann_monotone_right q (Nat.le_add_left d (uf.rank u))
      omega
  have hpot_le : ∀ u, u < uf.size →
      nodePotential zs q d uf' u ≤ nodePotential zs q d uf u := by
    intro u hu
    by_cases hroot : uf.parent u = u
    · have hroot' : uf'.parent u = u := (parent_compressWithSteps_eq_self_iff uf x u).mpr hroot
      simp only [nodePotential, uf', hroot, hroot', ↓reduceIte, rank_compressWithSteps]
      exact Nat.le_refl _
    · have hroot' : uf'.parent u ≠ u := by
        rwa [ne_eq, parent_compressWithSteps_eq_self_iff]
      simp only [nodePotential, uf', hroot, hroot', ↓reduceIte, rank_compressWithSteps]
      rw [parent_compressWithSteps]
      split_ifs with huS
      · rw [← findPath_rootD uf x huS]
        obtain ⟨hr, hrp, hpp', hp'q⟩ := hpath_bounds u hroot
        exact nonRootPhi_le_of_le hr hrp hpp' hp'q
      · exact Nat.le_refl _
  have hpot_drop : ∀ u ∈ S_drop,
      nodePotential zs q d uf' u + 1 ≤ nodePotential zs q d uf u := by
    intro u hu
    rw [Finset.mem_filter] at hu
    rcases hu with ⟨huS, hroot, v, hvS, hrank_uv, hvroot, hlvl⟩
    have huPath : u ∈ findPath uf x := List.mem_toFinset.mp huS
    have hvPath : v ∈ findPath uf x := List.mem_toFinset.mp hvS
    have hroot' : uf'.parent u ≠ u := by
      rwa [ne_eq, parent_compressWithSteps_eq_self_iff]
    simp only [nodePotential, uf', hroot, hroot', ↓reduceIte, rank_compressWithSteps]
    rw [parent_compressWithSteps, ite_eq_left huPath, ← findPath_rootD uf x huPath]
    obtain ⟨hr, hrp, hpp', hp'q⟩ := hpath_bounds u hroot
    refine nonRootPhi_lt_of_step hr hrp hpp' hp'q ?_
    have hpu_rv : uf.rank (uf.parent u) + d ≤ uf.rank v + d :=
      Nat.add_le_add_right (findPath_parent_rank_le uf x huPath hvPath hrank_uv) d
    have hrv : 1 ≤ uf.rank v + d := Nat.le_trans hd (Nat.le_add_left d _)
    have hrvp : uf.rank v + d < uf.rank (uf.parent v) + d :=
      Nat.add_lt_add_right (uf.rank_lt hvroot) d
    have hack_v : Nat.ackermann (lvl u) (uf.rank v + d) ≤ uf.rank (uf.parent v) + d :=
      hlvl ▸ ackermann_ackLevel_le hrv hrvp
    have hpv_root : uf.rank (uf.parent v) + d ≤ uf.rank (uf.rootD u) + d := by
      have hle := Batteries.UnionFind.le_rank_root (self := uf) (x := uf.parent v)
      rw [Batteries.UnionFind.rootD_parent, findPath_rootD uf x hvPath,
        ← findPath_rootD uf x huPath] at hle
      omega
    rw [Function.iterate_succ_apply']
    exact (Nat.ackermann_monotone_right (lvl u)
      ((iterate_ackermann_ackIter_le hr hrp).trans hpu_rv)).trans (hack_v.trans hpv_root)
  have hsum_drop : potentialCore zs q d uf' + S_drop.card ≤ potentialCore zs q d uf := by
    have hsum_le :
        ∑ u ∈ Finset.range uf.size,
            (nodePotential zs q d uf' u + if u ∈ S_drop then 1 else 0) ≤
          ∑ u ∈ Finset.range uf.size, nodePotential zs q d uf u :=
      Finset.sum_le_sum fun u hu => by
        by_cases hud : u ∈ S_drop <;> simp only [hud, ↓reduceIte, Nat.add_zero]
        exacts [hpot_drop u hud, hpot_le u (Finset.mem_range.mp hu)]
    unfold potentialCore
    rw [compressWithSteps_size uf x]
    rwa [Finset.sum_add_distrib, ← Finset.sum_filter (fun u => u ∈ S_drop) (fun _ => (1 : ℕ)),
      Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hdrop_sub, Finset.sum_const,
      Nat.nsmul_eq_mul, Nat.mul_one] at hsum_le
  have hkeep_card : S_keep.card ≤ q + 1 := by
    let S_keep_roots := S_keep.filter (fun u => uf.parent u = u)
    let S_keep_nonroots := S_keep.filter (fun u => uf.parent u ≠ u)
    have hsplit := Finset.card_filter_add_card_filter_not (s := S_keep)
      (p := fun u => uf.parent u = u)
    have hroots : S_keep_roots.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb => by
      rw [Finset.mem_filter, Finset.mem_sdiff] at ha hb
      exact ((Batteries.UnionFind.rootD_eq_self.mpr ha.2).symm.trans
        (findPath_rootD uf x (List.mem_toFinset.mp ha.1.1))).trans
        ((Batteries.UnionFind.rootD_eq_self.mpr hb.2).symm.trans
          (findPath_rootD uf x (List.mem_toFinset.mp hb.1.1))).symm
    have hnonroots : S_keep_nonroots.card ≤ q := by
      have hmap : Set.MapsTo lvl (S_keep_nonroots : Set ℕ) (Finset.range q : Set ℕ) := by
        intro u hu
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_sdiff] at hu
        have hroot := hu.2
        have hr : 1 ≤ uf.rank u + d := Nat.le_trans hd (Nat.le_add_left d _)
        have hrp : uf.rank u + d < uf.rank (uf.parent u) + d :=
          Nat.add_lt_add_right (uf.rank_lt hroot) d
        have hpq : uf.rank (uf.parent u) + d < Nat.ackermann q (uf.rank u + d) := by
          have hlog := hvalid.rank_le_log (uf.parent u)
          have hack := Nat.ackermann_monotone_right q (Nat.le_add_left d (uf.rank u))
          omega
        exact Finset.mem_coe.mpr (Finset.mem_range.mpr
          (ackLevel_lt_of_lt_ackermann hr hrp hpq))
      have hinj : Set.InjOn lvl (S_keep_nonroots : Set ℕ) := by
        intro u₁ hu₁ u₂ hu₂ heq
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_sdiff] at hu₁ hu₂
        by_contra hne
        have hu₁Path : u₁ ∈ findPath uf x := List.mem_toFinset.mp hu₁.1.1
        have hu₂Path : u₂ ∈ findPath uf x := List.mem_toFinset.mp hu₂.1.1
        rcases findPath_rank_ne_of_ne uf x hu₁Path hu₂Path hne with hlt | hlt
        · exact hu₁.1.2 (Finset.mem_filter.mpr
            ⟨hu₁.1.1, hu₁.2, u₂, hu₂.1.1, hlt, hu₂.2, heq⟩)
        · exact hu₂.1.2 (Finset.mem_filter.mpr
            ⟨hu₂.1.1, hu₂.2, u₁, hu₁.1.1, hlt, hu₁.2, heq.symm⟩)
      simpa only [Finset.card_range] using Finset.card_le_card_of_injOn lvl hmap hinj
    change S_keep_roots.card + S_keep_nonroots.card = S_keep.card at hsplit
    omega
  have hS_split : S_keep.card + S_drop.card = S.card :=
    Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  rw [← hS_card]
  omega

private theorem link_pot_aux {uf uf' : Batteries.UnionFind}
    (hvalid' : ValidRank uf')
    {q d : ℕ} (hd : 1 ≤ d)
    (hbound : Nat.log 2 uf.size + d < Nat.ackermann q d)
    {winner child : Fin uf.size}
    (hwinner : uf.parent winner.1 = winner.1)
    (hne : winner.1 ≠ child.1) (hsize : uf'.size = uf.size)
    (hparent : ∀ i, uf'.parent i = if child.1 = i then winner.1 else uf.parent i)
    (hrank : ∀ i, uf'.rank i =
      if uf.rank child.1 = uf.rank winner.1 ∧ winner.1 = i then uf.rank winner.1 + 1
      else uf.rank i)
    (hcrank : uf'.rank child.1 < uf'.rank winner.1)
    (zs : Bool) :
    1 + potentialCore zs q d uf' +
      (nodePotential zs q d uf winner.1 + nodePotential zs q d uf child.1) ≤
      q + (q * (uf.rank winner.1 + d) + q * (uf.rank child.1 + d)) +
        potentialCore zs q d uf := by
  let rest : Finset ℕ := ((Finset.range uf.size).erase winner.1).erase child.1
  have hmem_w : winner.1 ∈ Finset.range uf.size := Finset.mem_range.mpr winner.2
  have hmem_c : child.1 ∈ (Finset.range uf.size).erase winner.1 :=
    Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_range.mpr child.2⟩
  have hsplit_uf :
      nodePotential zs q d uf winner.1 +
        (nodePotential zs q d uf child.1 + ∑ i ∈ rest, nodePotential zs q d uf i) =
      potentialCore zs q d uf := by
    unfold potentialCore
    rw [Finset.add_sum_erase _ _ hmem_c, Finset.add_sum_erase _ _ hmem_w]
  have hsplit_uf' :
      nodePotential zs q d uf' winner.1 +
        (nodePotential zs q d uf' child.1 + ∑ i ∈ rest, nodePotential zs q d uf' i) =
      potentialCore zs q d uf' := by
    unfold potentialCore
    rw [hsize, Finset.add_sum_erase _ _ hmem_c, Finset.add_sum_erase _ _ hmem_w]
  have hrest : ∀ i ∈ rest, nodePotential zs q d uf' i ≤ nodePotential zs q d uf i := by
    intro i hi
    have hi_ne_c : child.1 ≠ i := (Finset.mem_erase.mp hi).1.symm
    have hi_ne_w : winner.1 ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1.symm
    have hp_i : uf'.parent i = uf.parent i := by rw [hparent i, ite_eq_right hi_ne_c]
    have hr_i : uf'.rank i = uf.rank i := by rw [hrank i]; simp [hi_ne_w]
    by_cases hroot : uf.parent i = i
    · simp [nodePotential, hroot, hp_i.trans hroot, hr_i]
    · have hroot' : uf'.parent i ≠ i := by rwa [hp_i]
      simp only [nodePotential, hroot, hroot', ↓reduceIte, hr_i]
      by_cases hpw : uf.parent i = winner.1
      · have hle_p : uf.rank (uf.parent i) ≤ uf'.rank (uf'.parent i) := by
          rw [hp_i, hpw, hrank winner.1]
          split_ifs <;> omega
        have hr_pos : 1 ≤ uf.rank i + d := Nat.le_trans hd (Nat.le_add_left d _)
        have hrp : uf.rank i + d < uf.rank (uf.parent i) + d :=
          Nat.add_lt_add_right (uf.rank_lt hroot) d
        have hpp' : uf.rank (uf.parent i) + d ≤ uf'.rank (uf'.parent i) + d := by omega
        have hp'q : uf'.rank (uf'.parent i) + d < Nat.ackermann q (uf.rank i + d) := by
          have hlog := hvalid'.rank_le_log (uf'.parent i)
          rw [hsize] at hlog
          have hack := Nat.ackermann_monotone_right q (Nat.le_add_left d (uf.rank i))
          omega
        exact nonRootPhi_le_of_le hr_pos hrp hpp' hp'q
      · rw [hp_i, hrank (uf.parent i)]
        simp [Ne.symm hpw]
  have hsum_rest : ∑ i ∈ rest, nodePotential zs q d uf' i ≤
      ∑ i ∈ rest, nodePotential zs q d uf i := Finset.sum_le_sum hrest
  have hchild_bound : 1 + nodePotential zs q d uf' child.1 ≤ q * (uf.rank child.1 + d) := by
    have hpc : uf'.parent child.1 = winner.1 := by rw [hparent child.1, ite_eq_left rfl]
    have hpc_ne : uf'.parent child.1 ≠ child.1 := by rw [hpc]; exact hne
    have hrc : uf'.rank child.1 = uf.rank child.1 := by rw [hrank child.1]; simp [hne]
    simp only [nodePotential, hpc_ne, ↓reduceIte, hrc]
    rw [hpc]
    have hr_pos : 1 ≤ uf.rank child.1 + d := Nat.le_trans hd (Nat.le_add_left d _)
    have hrp : uf.rank child.1 + d < uf'.rank winner.1 + d := by rw [← hrc]; omega
    have hpq : uf'.rank winner.1 + d < Nat.ackermann q (uf.rank child.1 + d) := by
      have hlog := hvalid'.rank_le_log winner.1
      rw [hsize] at hlog
      have hack := Nat.ackermann_monotone_right q (Nat.le_add_left d (uf.rank child.1))
      omega
    have hmul := nonRootPhi_le_mul_sub_one hr_pos hrp hpq
    omega
  have hwinner_bound : nodePotential zs q d uf' winner.1 ≤ q * (uf.rank winner.1 + d) + q := by
    have hpw' : uf'.parent winner.1 = winner.1 := by
      rw [hparent winner.1, ite_eq_right hne.symm, hwinner]
    have hrw' : uf'.rank winner.1 ≤ uf.rank winner.1 + 1 := by
      rw [hrank winner.1]
      split_ifs <;> omega
    simp only [nodePotential, hpw', ↓reduceIte]
    split_ifs
    · exact Nat.zero_le _
    · calc
        q * (uf'.rank winner.1 + d) ≤ q * ((uf.rank winner.1 + 1) + d) :=
          Nat.mul_le_mul_left q (by omega)
        _ = q * ((uf.rank winner.1 + d) + 1) := by rw [Nat.add_right_comm]
        _ = q * (uf.rank winner.1 + d) + q := by rw [Nat.mul_add, Nat.mul_one]
  omega

private theorem link_pot_core {uf : Batteries.UnionFind}
    (hvalid : ValidRank uf) {q d : ℕ} (hq : 1 ≤ q) (hd : 1 ≤ d)
    (hbound : Nat.log 2 uf.size + d < Nat.ackermann q d)
    {x y : Fin uf.size} (hx : uf.parent x.1 = x.1) (hy : uf.parent y.1 = y.1) (zs : Bool) :
    1 + potentialCore zs q d (uf.link x y hy) ≤
      (if zs then 2 * d * q + q else q) + potentialCore zs q d uf := by
  by_cases hxy : x.1 = y.1
  · rw [link_self uf hy hxy]
    split_ifs <;> omega
  · have hvalid' : ValidRank (uf.link x y hy) := hvalid.link hx hy
    have hsize : (uf.link x y hy).size = uf.size := Batteries.UnionFind.linkAux_size
    have haux_res : 1 + potentialCore zs q d (uf.link x y hy) +
        (if uf.rank y.1 < uf.rank x.1 then
          nodePotential zs q d uf x.1 + nodePotential zs q d uf y.1
        else
          nodePotential zs q d uf y.1 + nodePotential zs q d uf x.1) ≤
        q + (if uf.rank y.1 < uf.rank x.1 then
          q * (uf.rank x.1 + d) + q * (uf.rank y.1 + d)
        else
          q * (uf.rank y.1 + d) + q * (uf.rank x.1 + d)) + potentialCore zs q d uf := by
      by_cases hlt : uf.rank y.1 < uf.rank x.1
      · simp only [hlt, ↓reduceIte]
        have hcr : (uf.link x y hy).rank y.1 < (uf.link x y hy).rank x.1 := by
          rw [rank_link, rank_link]
          simp [Nat.ne_of_gt hlt, hlt]
        exact link_pot_aux hvalid' hd hbound hx hxy hsize
          (fun i => by rw [Batteries.UnionFind.parent_link hy]; simp [hxy, hlt])
          (fun i => by rw [rank_link]; simp [Nat.ne_of_lt hlt, Nat.ne_of_gt hlt])
          hcr zs
      · simp only [hlt, ↓reduceIte]
        have hcr : (uf.link x y hy).rank x.1 < (uf.link x y hy).rank y.1 := by
          rw [rank_link, rank_link]
          have hle : uf.rank x.1 ≤ uf.rank y.1 := Nat.not_lt.mp hlt
          rcases Nat.eq_or_lt_of_le hle with heq | hlt_xy
          · simp [hxy, Ne.symm hxy, heq]
          · simp [hxy, Nat.ne_of_lt hlt_xy, hlt_xy]
        exact link_pot_aux hvalid' hd hbound hy (Ne.symm hxy) hsize
          (fun i => by rw [Batteries.UnionFind.parent_link hy]; simp [hxy, hlt])
          (fun i => by rw [rank_link]; simp [hxy])
          hcr zs
    cases zs
    · simp only [Bool.false_eq_true, ↓reduceIte]
      simp only [nodePotential, hx, hy, ↓reduceIte, Bool.false_and, Bool.false_eq_true] at haux_res
      split_ifs at haux_res <;> omega
    · simp only [↓reduceIte]
      have hnode_le : ∀ u : Fin uf.size, uf.parent u.1 = u.1 →
          q * (uf.rank u.1 + d) ≤ nodePotential true q d uf u.1 + q * d := by
        intro u hu
        simp only [nodePotential, hu, ↓reduceIte, Bool.true_and]
        split_ifs with hr0
        · rw [of_decide_eq_true hr0, Nat.zero_add]
          exact Nat.le_add_left _ _
        · exact Nat.le_add_right _ _
      have hx_le := hnode_le x hx
      have hy_le := hnode_le y hy
      have hmul_comm : 2 * d * q = q * d + q * d := by
        rw [Nat.mul_assoc, Nat.mul_comm d q, Nat.two_mul]
      split_ifs at haux_res <;> omega

private theorem two_finds_core {n : ℕ} (s : State n) (x y : Fin n)
    (hrank : ValidRank s.uf) {q d : ℕ} (hd : 1 ≤ d)
    (hbound : Nat.log 2 n + d < Nat.ackermann q d) (zs : Bool) :
    let x' : Fin s.uf.size := ⟨x.1, by rw [s.size_eq]; exact x.2⟩
    let c₁ := compressWithSteps s.uf x'
    let y' : Fin c₁.1.size :=
      ⟨y.1, by rw [compressWithSteps_size s.uf x', s.size_eq]; exact y.2⟩
    let c₂ := compressWithSteps c₁.1 y'
    ValidRank c₂.1 ∧ c₂.1.size = n ∧
      (c₁.2.2 + c₂.2.2) + potentialCore zs q d c₂.1 ≤
        (2 * q + 2) + potentialCore zs q d s.uf := by
  intro x' c₁ y' c₂
  have hvalid₁ : ValidRank c₁.1 := hrank.compressWithSteps x'
  have hvalid₂ : ValidRank c₂.1 := hvalid₁.compressWithSteps y'
  have hsz₂ : c₂.1.size = n :=
    (compressWithSteps_size c₁.1 y').trans ((compressWithSteps_size s.uf x').trans s.size_eq)
  have hf1 := findSteps_add_potentialCore_le hrank hd (by rwa [s.size_eq]) zs x'
  have hf2 := findSteps_add_potentialCore_le hvalid₁ hd
    (by rwa [(compressWithSteps_size s.uf x').trans s.size_eq]) zs y'
  have hs1 : c₁.2.2 = findSteps s.uf x' :=
    congrArg (fun p => p.2.2) (compressWithSteps_eq s.uf x')
  have hs2 : c₂.2.2 = findSteps c₁.1 y' :=
    congrArg (fun p => p.2.2) (compressWithSteps_eq c₁.1 y')
  refine ⟨hvalid₂, hsz₂, ?_⟩
  dsimp only [c₁, c₂] at hf1 hf2 hs1 hs2 ⊢
  omega

private theorem two_finds_union_step_core {n : ℕ} {s : State n} (x y : Fin n)
    (hrank : ValidRank s.uf) {q d : ℕ} (hq : 1 ≤ q) (hd : 1 ≤ d)
    (hbound : Nat.log 2 n + d < Nat.ackermann q d) (zs : Bool) :
    (step s (.union x y)).trace + potentialCore zs q d (step s (.union x y)).state.uf ≤
      (2 * (q + 1) + (if zs then 2 * d * q + q else q)) + potentialCore zs q d s.uf := by
  obtain ⟨hvalid₂, hsz₂, hfinds⟩ := two_finds_core s x y hrank hd hbound zs
  unfold step
  dsimp only
  let x' : Fin s.uf.size := ⟨x.1, by rw [s.size_eq]; exact x.2⟩
  set c₁ := compressWithSteps s.uf x'
  let y' : Fin c₁.1.size :=
    ⟨y.1, by rw [compressWithSteps_size s.uf x', s.size_eq]; exact y.2⟩
  set c₂ := compressWithSteps c₁.1 y'
  let rx : Fin c₂.1.size := ⟨c₁.2.1.1, by
    rw [compressWithSteps_size c₁.1 y', compressWithSteps_size s.uf x']
    exact c₁.2.1.2⟩
  let ry : Fin c₂.1.size := ⟨c₂.2.1.1, by rw [compressWithSteps_size c₁.1 y']; exact c₂.2.1.2⟩
  have hc_root {uf : Batteries.UnionFind} (z : Fin uf.size) :
      (compressWithSteps uf z).1.rootD (compressWithSteps uf z).2.1.1 =
        (compressWithSteps uf z).2.1.1 := by
    rw [rootD_compressWithSteps, congrArg (fun p => (p.2.1 : ℕ)) (compressWithSteps_eq uf z),
      Batteries.UnionFind.rootD_rootD]
  have hxroot : c₂.1.parent rx.1 = rx.1 :=
    Batteries.UnionFind.rootD_eq_self.mp ((rootD_compressWithSteps c₁.1 y' _).trans (hc_root x'))
  have hyroot : c₂.1.parent ry.1 = ry.1 :=
    Batteries.UnionFind.rootD_eq_self.mp (hc_root y')
  have hlink := link_pot_core hvalid₂ hq hd (by rwa [hsz₂]) hxroot hyroot zs
  change (c₁.2.2 + c₂.2.2 + 1) + potentialCore zs q d (c₂.1.link rx ry _) ≤ _
  dsimp only [c₁, c₂, x', y'] at hfinds hlink ⊢
  omega

private theorem two_finds_same_step_core {n : ℕ} {s : State n} (x y : Fin n)
    (hrank : ValidRank s.uf) {q d : ℕ} (hd : 1 ≤ d)
    (hbound : Nat.log 2 n + d < Nat.ackermann q d) (zs : Bool) :
    (step s (.same x y)).trace + potentialCore zs q d (step s (.same x y)).state.uf ≤
      (2 * q + 2) + potentialCore zs q d s.uf :=
  (two_finds_core s x y hrank hd hbound zs).2.2

private theorem amortized_potentialCore (n : ℕ) (zs : Bool) {q d : ℕ}
    (hq : 1 ≤ q) (hd : 1 ≤ d) (hbound : Nat.log 2 n + d < Nat.ackermann q d)
    {pot : Partition n → State n → ℕ} {chg : Partition n → Op n → ℕ}
    (hpot_eq : ∀ p s, pot p s = potentialCore zs q d s.uf)
    (hchg_eq : ∀ p o, chg p o = match o with
      | .same _ _ => 2 * q + 2
      | .union _ _ => 2 * (q + 1) + (if zs then 2 * d * q + q else q)
      | .numComponents => 1) :
    Amortized (impl n) id pot chg := by
  refine Amortized.ofFn fun hr _ he => ?_
  rw [impl_rep] at hr
  have hstate : (step _ _).state = _ := congrArg StepResult.state he
  have hsteps : (step _ _).trace = _ := congrArg StepResult.trace he
  dsimp only at hstate hsteps
  rw [id, ← hsteps, ← hstate, hpot_eq, hpot_eq, hchg_eq]
  cases ‹Op n› with
  | numComponents => exact Nat.le_refl _
  | same x y => exact two_finds_same_step_core x y hr.validRank hd hbound zs
  | union x y => exact two_finds_union_step_core x y hr.validRank hq hd hbound zs

/-! ### Public potentials, amortized certificates, and client step bounds -/

/-- Potential function on `Fin n` used for the single-parameter `O(α(n))` step analysis.
Singletons carry zero potential, so `tarjanPotential n _ (init n) = 0`. -/
noncomputable def tarjanPotential (n : ℕ) (_ : Partition n) (s : State n) : ℕ :=
  potentialCore true (Nat.inverseAckermann n) 1 s.uf

/-- Per-operation single-parameter amortized charge on `Fin n`: `2 * α(n) + 2` for `Op.same`,
`5 * α(n) + 2` for `Op.union`, and `1` for `Op.numComponents`. -/
@[expose] def tarjanCharge (n : ℕ) (_ : Partition n) : Op n → ℕ
  | .same _ _ => 2 * Nat.inverseAckermann n + 2
  | .union _ _ => 5 * Nat.inverseAckermann n + 2
  | .numComponents => 1

/-- Every disjoint-set operation has single-parameter charge at most `5 * α(n) + 2`. -/
theorem tarjanCharge_le (n : ℕ) (p : Partition n) (o : Op n) :
    tarjanCharge n p o ≤ 5 * Nat.inverseAckermann n + 2 := by
  have h1 := Nat.one_le_inverseAckermann n
  cases o <;> simp only [tarjanCharge] <;> omega

/-- Initial single-parameter potential at `init n` is `0`. -/
@[simp] theorem tarjanPotential_init (n : ℕ) (p : Partition n) :
    tarjanPotential n p (init n) = 0 :=
  potentialCore_true_ofSize _ 1 n

/-- Single-parameter `O(α(n))` amortized abstract step certificate over `impl n`. -/
theorem tarjanAmortized (n : ℕ) :
    Amortized (impl n) id (tarjanPotential n) (tarjanCharge n) :=
  amortized_potentialCore n true (Nat.one_le_inverseAckermann n) (Nat.le_refl 1)
    (Nat.log_add_one_lt_ackermann_inverseAckermann n)
    (fun _ _ => rfl)
    (fun _ o => by cases o <;> simp [tarjanCharge]; omega)

/-- Uniform single-parameter amortized abstract step certificate `5 * α(n) + 2` over `impl n`. -/
theorem tarjanUniformAmortized (n : ℕ) :
    Amortized (impl n) id (tarjanPotential n) (fun _ _ => 5 * Nat.inverseAckermann n + 2) where
  step hr hv he := by
    obtain ⟨s', hstep, hr', hpot⟩ := (tarjanAmortized n).step hr hv he
    exact ⟨s', hstep, hr', hpot.trans (Nat.add_le_add_right (tarjanCharge_le n _ _) _)⟩

/-- Running the concrete union-find interpreter from `init n` agrees with abstract `Partition n`
semantics, preserves `Rep`, and satisfies both the exact per-operation and uniform `5 * α(n) + 2`
abstract step bounds (excluding `init n`). -/
theorem tarjan_run_correct {n : ℕ} {β : Type} (client : (spec n).Client β) :
    let (value, finalState, history) := (spec n).runClient (Partition.discrete n) client
    (run (init n) client).value = value ∧ Rep finalState (run (init n) client).state ∧
      total id (run (init n) client).traces ≤
        (spec n).totalCost (tarjanCharge n) (Partition.discrete n) history ∧
      total id (run (init n) client).traces ≤
        history.length * (5 * Nat.inverseAckermann n + 2) := by
  have hrep0 : (impl n).rep (Partition.discrete n) (init n) := by rw [impl_rep]; exact rep_init n
  have hv := (spec n).validHistory_of_forall_valid (fun _ _ => trivial)
    (Partition.discrete n) ((spec n).clientHistory (Partition.discrete n) client)
  have hexec := Execution.executes_run step client (init n)
  have hc := (impl n).correct_client hrep0 hv hexec
  have hclient := (tarjanAmortized n).client hrep0 hv hexec
  have hconst := (tarjanUniformAmortized n).client_const hrep0 hv hexec
  rw [impl_rep] at hc
  rw [tarjanPotential_init] at hclient hconst
  dsimp only at hclient hconst ⊢
  exact ⟨hc.1, hc.2, le_trans (Nat.le_add_right _ _) hclient,
    le_trans (Nat.le_add_right _ _) hconst⟩

/-- Rank-shifted potential function parameterized by `d` on `Fin n` used for the two-parameter
`O(m α(m, n))` abstract step analysis. Initial potential at `init n` is
`n * (inverseAckermannAt d n * max 1 d)`. -/
noncomputable def tarjanPotentialAt (d n : ℕ) (_ : Partition n) (s : State n) : ℕ :=
  potentialCore false (Nat.inverseAckermannAt d n) (max 1 d) s.uf

/-- Per-operation amortized charge parameterized by `d` on `Fin n`: `2 * α_d(n) + 2` for `Op.same`,
`3 * α_d(n) + 2` for `Op.union`, and `1` for `Op.numComponents`. -/
@[expose] def tarjanChargeAt (d n : ℕ) (_ : Partition n) : Op n → ℕ
  | .same _ _ => 2 * Nat.inverseAckermannAt d n + 2
  | .union _ _ => 3 * Nat.inverseAckermannAt d n + 2
  | .numComponents => 1

/-- Every disjoint-set operation has rank-shifted charge at most `3 * α_d(n) + 2`. -/
theorem tarjanChargeAt_le (d n : ℕ) (p : Partition n) (o : Op n) :
    tarjanChargeAt d n p o ≤ 3 * Nat.inverseAckermannAt d n + 2 := by
  have h1 := Nat.one_le_inverseAckermannAt d n
  cases o <;> simp only [tarjanChargeAt] <;> omega

/-- Initial rank-shifted potential at `init n`. -/
@[simp] theorem tarjanPotentialAt_init (d n : ℕ) (p : Partition n) :
    tarjanPotentialAt d n p (init n) = n * (Nat.inverseAckermannAt d n * max 1 d) :=
  potentialCore_false_ofSize _ _ n

/-- Rank-shifted amortized abstract step certificate over `impl n`. -/
theorem tarjanAmortizedAt (d n : ℕ) :
    Amortized (impl n) id (tarjanPotentialAt d n) (tarjanChargeAt d n) :=
  amortized_potentialCore n false (Nat.one_le_inverseAckermannAt d n) (Nat.le_max_left 1 d)
    (Nat.log_add_lt_ackermann_inverseAckermannAt d n)
    (fun _ _ => rfl)
    (fun _ o => by cases o <;> simp [tarjanChargeAt]; omega)

/-- Uniform rank-shifted amortized step certificate `3 * α_d(n) + 2` over `impl n`. -/
theorem tarjanUniformAmortizedAt (d n : ℕ) :
    Amortized (impl n) id (tarjanPotentialAt d n)
      (fun _ _ => 3 * Nat.inverseAckermannAt d n + 2) where
  step hr hv he := by
    obtain ⟨s', hstep, hr', hpot⟩ := (tarjanAmortizedAt d n).step hr hv he
    exact ⟨s', hstep, hr', hpot.trans (Nat.add_le_add_right (tarjanChargeAt_le d n _ _) _)⟩

/-- Two-parameter inverse-Ackermann abstract step bound (step toward `#3558` and `#5441`): for
every universe size `n` and adaptive client on `Fin n` issuing `m = history.length` operations from
`init n`, the concrete `Batteries.UnionFind` execution agrees with `Partition n` and records at
most `m * (5 * Nat.inverseAckermannTwo m n + 2)` pointer/link steps (excluding `init n`). -/
theorem tarjan_run_two_param {n : ℕ} {β : Type} (client : (spec n).Client β) :
    let (value, finalState, history) := (spec n).runClient (Partition.discrete n) client
    (run (init n) client).value = value ∧ Rep finalState (run (init n) client).state ∧
      total id (run (init n) client).traces ≤
        history.length * (5 * Nat.inverseAckermannTwo history.length n + 2) := by
  dsimp only
  let m := ((spec n).clientHistory (Partition.discrete n) client).length
  have hrun := tarjan_run_correct client
  dsimp only at hrun
  refine ⟨hrun.1, hrun.2.1, ?_⟩
  rcases Nat.lt_or_ge m n with hlt | hle
  · simpa only [m, Nat.inverseAckermannTwo_of_lt hlt] using hrun.2.2.2
  · let d := m / n + 1
    have hrep0 : (impl n).rep (Partition.discrete n) (init n) := by rw [impl_rep]; exact rep_init n
    have hv := (spec n).validHistory_of_forall_valid (fun _ _ => trivial)
      (Partition.discrete n) ((spec n).clientHistory (Partition.discrete n) client)
    have hexec := Execution.executes_run step client (init n)
    have hconst := (tarjanUniformAmortizedAt d n).client_const hrep0 hv hexec
    rw [tarjanPotentialAt_init] at hconst
    dsimp only at hconst
    have hnd : n * max 1 d ≤ 2 * m := by
      have hdiv : n * (m / n) ≤ m := Nat.mul_div_le m n
      rw [max_eq_right (Nat.succ_pos _), Nat.mul_add, Nat.mul_one]
      omega
    have hinit : n * (Nat.inverseAckermannTwo m n * max 1 d) ≤
        m * (2 * Nat.inverseAckermannTwo m n) := by
      calc
        n * (Nat.inverseAckermannTwo m n * max 1 d) =
            (n * max 1 d) * Nat.inverseAckermannTwo m n := by
          rw [Nat.mul_comm (Nat.inverseAckermannTwo m n) (max 1 d), ← Nat.mul_assoc]
        _ ≤ (2 * m) * Nat.inverseAckermannTwo m n := Nat.mul_le_mul_right _ hnd
        _ = m * (2 * Nat.inverseAckermannTwo m n) := by
          rw [Nat.mul_comm 2 m, Nat.mul_assoc]
    calc
      total id (run (init n) client).traces ≤
          m * (3 * Nat.inverseAckermannTwo m n + 2) +
            n * (Nat.inverseAckermannTwo m n * max 1 d) := le_trans (Nat.le_add_right _ _) hconst
      _ ≤ m * (3 * Nat.inverseAckermannTwo m n + 2) +
            m * (2 * Nat.inverseAckermannTwo m n) := Nat.add_le_add_left hinit _
      _ = m * ((3 * Nat.inverseAckermannTwo m n + 2) + 2 * Nat.inverseAckermannTwo m n) :=
        (Nat.mul_add _ _ _).symm
      _ = m * (5 * Nat.inverseAckermannTwo m n + 2) := by
        congr 1
        omega

/-- Linear abstract step-count corollary of `tarjan_run_two_param`: whenever `n * Nat.log 2 n ≤ m`,
every `m`-operation adaptive client on `Fin n` records at most `7 * m` pointer/link steps
(excluding `init n`). -/
theorem tarjan_run_linear_of_dense {n : ℕ} {β : Type} (client : (spec n).Client β)
    (hdense : n * Nat.log 2 n ≤ ((spec n).clientHistory (Partition.discrete n) client).length) :
    total id (run (init n) client).traces ≤
      7 * ((spec n).clientHistory (Partition.discrete n) client).length := by
  have htwo := (tarjan_run_two_param client).2.2
  have hhist : ((spec n).runClient (Partition.discrete n) client).2.2 =
      (spec n).clientHistory (Partition.discrete n) client := rfl
  rw [hhist, Nat.inverseAckermannTwo_eq_one_of_mul_log_le hdense] at htwo
  omega

end Cslib.DataStructure.DisjointSet.UnionFind
