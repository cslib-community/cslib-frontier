/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Card

/-!
# Vectors of maxima under linear orders

Let `S₁, …, S_m` be subsets of a ground set `U` of size at most `n`. Every injective weight
`w : α → W` into a linear order picks out the maximum of each `S_i`, and so a *vector of maxima*
`x` with `x i ∈ S i` and `w y ≤ w (x i)` for every `y ∈ S i`. As the order varies over all linear
orders of the ground set, at most `C(n + m - 1, m)` distinct vectors of maxima arise.

This is a step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026], tracked in #8325: the
paper's Lemma 3.9 (§3.4, p. 19), which it attributes to Fredman, in [GrahamYaoYao1980].
`Cslib.exists_maxima_vectors_card_le_choose` exhibits a single finset of `C(n + m - 1, m)` vectors
that contains every vector of maxima, for weights into every linear order `W` in a given universe at
once. Clients can therefore bound any function of the maxima (such as the paper's preferred actions)
by the image of this finset, whatever weights they use, for instance lexicographic pairs that break
ties between two kinds of ground elements.

The weights need only be injective on `U`, and the sets need not be nonempty (an empty `S i` admits
no vector of maxima). The source's ground set of size exactly `n` is the case `#U = n`.

The proof follows the source. A vector of maxima is determined by how often each element is a
maximum, that is by the multiset of its values, which ranges over the `C(#U + m - 1, m)`
multisets of size `m` in `U`. In fact a vector of maxima is the only *selection* (`y i ∈ S i` for
all `i`) with its multiset of values: if `y ≠ x`, take, among the coordinates where they differ,
one where `x` is heaviest; its value is also `y k` for some such coordinate `k`, but
`w (y k) < w (x k)`. This maximality argument replaces the source's directed-cycle argument.

## Main results

* `Cslib.exists_maxima_vectors_card_le_choose`: few vectors of maxima, a step in the proof of
  Theorem 4.1 of [KhannaPuttermanSong2026] (the paper's Lemma 3.9).

## References

* [S. Khanna, A. Putterman, J. Song, *A Deterministic Linear Time Algorithm for Minimum Spanning
  Tree*][KhannaPuttermanSong2026]
* [R. L. Graham, A. C. Yao, F. F. Yao, *Information bounds are weak in the shortest distance
  problem*][GrahamYaoYao1980]
-/

public section

namespace Cslib

open Finset

universe u

variable {α ι : Type*} [Fintype ι]

/-- A vector of maxima `x` is the only selection with its multiset of values. -/
private theorem eq_of_map_eq_of_isMax {W : Type*} [LinearOrder W] {U : Finset α}
    {S : ι → Finset α} (hS : ∀ i, S i ⊆ U) {w : α → W} (hw : Set.InjOn w U) {x y : ι → α}
    (hx : ∀ i, x i ∈ S i ∧ ∀ z ∈ S i, w z ≤ w (x i)) (hy : ∀ i, y i ∈ S i)
    (hxy : (univ.val.map y : Multiset α) = univ.val.map x) : y = x := by
  classical
  by_contra hne
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hne
  set D := univ.filter fun i => y i ≠ x i with hDdef
  have hD : D.Nonempty := ⟨i₀, by simpa [hDdef] using hi₀⟩
  -- the selections agree off `D`, so their values on `D` form the same multiset
  have hsplit (f : ι → α) : univ.val.map f =
      D.val.map f + (univ.filter fun i => ¬ y i ≠ x i).val.map f := by
    rw [← Multiset.map_add, hDdef, filter_val, filter_val, Multiset.filter_add_not]
  have hoff : (univ.filter fun i => ¬ y i ≠ x i).val.map y =
      (univ.filter fun i => ¬ y i ≠ x i).val.map x :=
    Multiset.map_congr rfl fun i hi => by simpa using (mem_filter.1 (mem_def.2 hi)).2
  have hDeq : D.val.map y = D.val.map x := by
    have := hxy
    rw [hsplit y, hsplit x, hoff] at this
    exact add_right_cancel this
  -- the heaviest value of `x` on `D` is also a value `y k` with `k ∈ D`, lighter than `x k`
  obtain ⟨j, hjD, hjmax⟩ := D.exists_max_image (fun i => w (x i)) hD
  obtain ⟨k, hkD, hk⟩ := Multiset.mem_map.1 (hDeq ▸ Multiset.mem_map_of_mem x hjD :
    x j ∈ D.val.map y)
  have hlt : w (y k) < w (x k) := lt_of_le_of_ne ((hx k).2 _ (hy k)) fun h =>
    (mem_filter.1 hkD).2 (hw (hS k (hy k)) (hS k (hx k).1) h)
  rw [hk] at hlt
  exact (hlt.trans_le (hjmax k hkD)).false

/-- Stars and bars for a finset: `U` has `C(#U + m - 1, m)` multisets of size `m`. -/
private theorem card_sym_finset [DecidableEq α] (U : Finset α) (m : ℕ) :
    #(U.sym m) = (#U + m - 1).choose m := by
  have hU : U = U.attach.map (Function.Embedding.subtype (· ∈ U)) := attach_map_val.symm
  nth_rw 1 [hU]
  rw [sym_map, card_map, attach_eq_univ, sym_univ, card_univ, Sym.card_sym_eq_choose,
    Fintype.card_coe]

/-- **Few vectors of maxima**, a step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (the
paper's Lemma 3.9, §3.4, p. 19, which it attributes to Fredman, in [GrahamYaoYao1980]). Let
`S i ⊆ U` for `i` in a type with `m` elements, where `#U ≤ n`. Then some finset of at most
`C(n + m - 1, m)` vectors contains every vector of maxima: every `x` such that, for an injective
weight `w : α → W` into some linear order, each `x i` is the `w`-maximum of `S i`.

The source ranges over total orders of a ground set of size `n`; here the orders are those induced
by weights into an arbitrary linear order `W : Type u`, injective on `U`, and the finset does not
depend on `W` or `w`. -/
theorem exists_maxima_vectors_card_le_choose (U : Finset α) (S : ι → Finset α)
    (hS : ∀ i, S i ⊆ U) {n : ℕ} (hU : #U ≤ n) :
    ∃ X : Finset (ι → α), #X ≤ (n + Fintype.card ι - 1).choose (Fintype.card ι) ∧
      ∀ {W : Type u} [LinearOrder W] (w : α → W), Set.InjOn w U →
        ∀ x : ι → α, (∀ i, x i ∈ S i ∧ ∀ y ∈ S i, w y ≤ w (x i)) → x ∈ X := by
  classical
  set m := Fintype.card ι
  let sel := Fintype.piFinset S
  -- the selections that are the only selection with their multiset of values
  let X := sel.filter fun x => ∀ y ∈ sel, (univ.val.map y : Multiset α) = univ.val.map x → y = x
  refine ⟨X, ?_, fun w hw x hx => ?_⟩
  · let f : (ι → α) → Sym α m := fun x => ⟨univ.val.map x, by simp [m]⟩
    have hmaps : ∀ x ∈ X, f x ∈ U.sym m := fun x hx => mem_sym_iff.2 fun a ha => by
      obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 ha
      exact hS i (Fintype.mem_piFinset.1 (mem_filter.1 hx).1 i)
    have hinj : Set.InjOn f X := fun x hx y hy hxy =>
      ((mem_filter.1 hx).2 y (mem_filter.1 hy).1 (congrArg Subtype.val hxy).symm).symm
    calc #X ≤ #(U.sym m) := card_le_card_of_injOn f hmaps hinj
      _ = (#U + m - 1).choose m := card_sym_finset U m
      _ ≤ (n + m - 1).choose m := Nat.choose_le_choose _ (by omega)
  · exact mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => (hx i).1, fun y hy hxy =>
      eq_of_map_eq_of_isMax hS hw hx (Fintype.mem_piFinset.1 hy) hxy⟩

end Cslib
