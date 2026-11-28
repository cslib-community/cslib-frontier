/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Kruskal.SimpleGraph
public import CslibFrontier.Algorithms.WordRAM.MergeSort
public import CslibFrontier.Computability.WordRAM.ListOutput

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Kruskal's Minimum Spanning Forest Algorithm on the Word RAM

This module implements Kruskal's greedy minimum spanning forest and minimum spanning tree algorithm
([Kruskal1956]; [CLRS2009], Section 23.2, `MST-KRUSKAL`) as a deterministic program on
`Cslib.WordRAM.Basis.standard`, charging every memory load, store, address calculation, edge-weight
comparison, parent-pointer traversal, union-by-rank update, loop test, and final `halt`.

Given a weighted undirected multigraph `es : List (WeightedEdge n ℕ)` (`m = es.length`) encoded in
standard Word-RAM input layout `State.init (encode es)` (`[n, m, u₀, v₀, w₀, …]`):

1. **Stable edge sort.** The program copies the `m` edge weights into a key array and runs the
   stable key-indexed merge sort `Cslib.Algorithms.WordRAM.MergeSort.mergeSortPerm`, producing an
   index permutation `perm` with `perm.filterMap (es[·]?) = sortEdges es`
   (`Cslib.Algorithms.WordRAM.MergeSort.filterMap_getElem?_eq_mergeSort`). The edge triples are not
   moved: the scan reads edge `perm[s]` at step `s`.
2. **Union-by-rank disjoint-set forest.** The program initializes `parent[0..n)` and `rank[0..n)`
   and scans the edges in sorted order. Each `findRoot` follows at most `⌊log₂ n⌋` parent
   pointers, because ranks strictly increase along parent pointers and `2 ^ rank[r]` is at most the
   size of the class of a root `r` ([CLRS2009], Lemma 21.4 for union by rank). An edge whose
   endpoints have distinct roots is appended to the output and its roots are linked by rank.

Consequently `kruskalProgram` outputs `encodeEdges (kruskalEdges es)` via
`Cslib.WordRAM.ExecutesList` within
`52 * m * ⌈log₂ m⌉ + 16 * m * ⌊log₂ n⌋ + 69 * m + 7 * n + 34` instructions at any word width `w`
satisfying `Fits w (9 * m + 2 * n + 4)` (note that `InputFits w (encode es)` for `Data.Bounded w` /
`Runs.bounded_init` additionally requires `∀ e ∈ es, Fits w e.weight`, as witnessed by
`inputFits_encode`), so the pure spanning-forest, minimum-spanning-tree, and `SimpleGraph`
theorems of `CslibFrontier.Algorithms.Lean.Kruskal.Basic` and
`CslibFrontier.Algorithms.Lean.Kruskal.SimpleGraph` apply to its output.

## Main definitions

* `Cslib.Algorithms.WordRAM.Kruskal.encodeEdges`: flat stride-3 `[u₀, v₀, w₀, …]` encoding of an
  edge list `List (WeightedEdge n ℕ)`.
* `Cslib.Algorithms.WordRAM.Kruskal.encode`: Word-RAM input encoding
  `n :: es.length :: encodeEdges es`.
* `Cslib.Algorithms.WordRAM.Kruskal.Reg.out`: output register of the 26-register program.
* `Cslib.Algorithms.WordRAM.Kruskal.kruskalCode`, `Cslib.Algorithms.WordRAM.Kruskal.kruskalProgram`:
  structured and compiled Word-RAM Kruskal programs.

## Main results

* `Cslib.Algorithms.WordRAM.Kruskal.encodeEdges_injective`: `encodeEdges` is injective for every
  `n`.
* `Cslib.Algorithms.WordRAM.Kruskal.inputFits_encode`: sufficient word-width condition for
  `InputFits w (encode es)`.
* `Cslib.Algorithms.WordRAM.Kruskal.kruskalCode_exec`: structured specification, including
  preservation of the input words.
* `Cslib.Algorithms.WordRAM.Kruskal.kruskalProgram_spec`: Word-RAM `ExecutesList` specification and
  `O(m log m + m log n + n)` instruction bound computing `encodeEdges (kruskalEdges es)`, a
  minimum-weight spanning forest.
* `Cslib.Algorithms.WordRAM.Kruskal.kruskalProgram_graphEdges_spec`: `SimpleGraph (Fin n)`
  specialization computing `encodeEdges (kruskalGraph G wt)` in terms of `|E| = G.edgeFinset.card`.

## References

* [J. B. Kruskal, Jr., *On the Shortest Spanning Subtree of a Graph and the Traveling Salesman
  Problem*][Kruskal1956]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapters 21 and 23][CLRS2009]
-/

public section

namespace Cslib.Algorithms.WordRAM.Kruskal

open Cslib.WordRAM
open Cslib.DataStructure.DisjointSet
open Cslib.Algorithms.Lean.Kruskal

/-! ## Edge-List Encoding and Injectivity -/

/-- Flat stride-3 word encoding `[u₀, v₀, w₀, …]` of a weighted edge list on `Fin n`. -/
@[expose] def encodeEdges {n : ℕ} (es : List (WeightedEdge n ℕ)) : List ℕ :=
  es.flatMap fun e => [e.u.val, e.v.val, e.weight]

/-- Word-RAM input encoding `[n, es.length, u₀, v₀, w₀, …]` of a weighted multigraph on `Fin n`. -/
@[expose] def encode {n : ℕ} (es : List (WeightedEdge n ℕ)) : List ℕ :=
  n :: es.length :: encodeEdges es

@[simp]
theorem encodeEdges_nil {n : ℕ} : encodeEdges ([] : List (WeightedEdge n ℕ)) = [] := rfl

@[simp]
theorem encodeEdges_cons {n : ℕ} (e : WeightedEdge n ℕ) (es : List (WeightedEdge n ℕ)) :
    encodeEdges (e :: es) = e.u.val :: e.v.val :: e.weight :: encodeEdges es := rfl

@[simp]
theorem encodeEdges_append {n : ℕ} (es₁ es₂ : List (WeightedEdge n ℕ)) :
    encodeEdges (es₁ ++ es₂) = encodeEdges es₁ ++ encodeEdges es₂ := by
  simp [encodeEdges, List.flatMap_append]

@[simp]
theorem length_encodeEdges {n : ℕ} (es : List (WeightedEdge n ℕ)) :
    (encodeEdges es).length = 3 * es.length := by
  induction es with
  | nil => rfl
  | cons _ es ih => simp only [encodeEdges_cons, List.length_cons, ih]; omega

@[simp]
theorem length_encode {n : ℕ} (es : List (WeightedEdge n ℕ)) :
    (encode es).length = 3 * es.length + 2 := by
  simp only [encode, List.length_cons, length_encodeEdges]

/-- `encodeEdges` is injective for every vertex count `n`. -/
theorem encodeEdges_injective (n : ℕ) : Function.Injective (encodeEdges (n := n)) := by
  intro es₁ es₂ h
  induction es₁ generalizing es₂ with
  | nil => cases es₂ <;> simp_all
  | cons e₁ tl₁ ih =>
    rcases es₂ with _ | ⟨⟨_, _, _⟩, tl₂⟩
    · simp at h
    · rcases e₁ with ⟨_, _, _⟩
      simp only [encodeEdges_cons, List.cons.injEq, Fin.val_inj] at h
      obtain ⟨rfl, rfl, rfl, htl⟩ := h
      exact congrArg _ (ih htl)

/-- Word-width admissibility for `encode es`: when workspace addresses and edge weights fit in `w`
bits, every word of `encode es` (and its total length) fits in `w` bits. -/
theorem inputFits_encode {w n : ℕ} (es : List (WeightedEdge n ℕ))
    (hmem : Fits w (9 * es.length + 2 * n + 4))
    (hw : ∀ e ∈ es, Fits w e.weight) :
    InputFits w (encode es) := by
  refine ⟨hmem.of_le (by simp only [length_encode]; omega), fun x hx => ?_⟩
  simp only [encode, List.mem_cons] at hx
  rcases hx with rfl | rfl | hx
  · exact hmem.of_le (by omega)
  · exact hmem.of_le (by omega)
  · simp only [encodeEdges, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with ⟨e, he, rfl | rfl | rfl⟩
    · exact hmem.of_le (by have := e.u.isLt; omega)
    · exact hmem.of_le (by have := e.v.isLt; omega)
    · exact hw e he

/-! ## Stride-3 Edge Memory -/

/-- Memory `mem` stores `es` in stride-3 `(u, v, weight)` layout starting at `base`. -/
@[expose] def HoldsEdges {n : ℕ} (base : ℕ) (es : List (WeightedEdge n ℕ)) (mem : ℕ → ℕ) : Prop :=
  ∀ i : ℕ, (hi : i < es.length) →
    mem (base + 3 * i) = es[i].u.val ∧
    mem (base + 3 * i + 1) = es[i].v.val ∧
    mem (base + 3 * i + 2) = es[i].weight

/-- Decode a stride-3 `HoldsEdges` layout from a flat `Block.HoldsList (encodeEdges es)`
layout. -/
theorem holdsEdges_of_holdsList {n : ℕ} {base : ℕ} {es : List (WeightedEdge n ℕ)}
    {mem : ℕ → ℕ} (h : Block.HoldsList base (encodeEdges es) mem) :
    HoldsEdges base es mem := by
  induction es generalizing base with
  | nil => intro i hi; simp at hi
  | cons e tl ih =>
    rw [encodeEdges_cons] at h
    have htl : Block.HoldsList (base + 3) (encodeEdges tl) mem := fun j => by
      have hj := h.get (j.val + 1 + 1 + 1) (by simp only [List.length_cons]; omega)
      change mem (base + 3 + j.val) = (encodeEdges tl)[j.val]
      have hidx : base + 3 + j.val = base + (j.val + 1 + 1 + 1) := by omega
      exact hidx ▸ hj
    intro i hi
    cases i with
    | zero =>
      simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero]
      exact ⟨by simpa using h.get 0 (by simp), by simpa using h.get 1 (by simp),
        by simpa using h.get 2 (by simp)⟩
    | succ k =>
      obtain ⟨hu, hv, hw⟩ := ih htl k (by simp only [List.length_cons] at hi; omega)
      simp only [List.getElem_cons_succ]
      exact ⟨by rwa [show base + 3 * (k + 1) = base + 3 + 3 * k by omega],
        by rwa [show base + 3 * (k + 1) + 1 = base + 3 + 3 * k + 1 by omega],
        by rwa [show base + 3 * (k + 1) + 2 = base + 3 + 3 * k + 2 by omega]⟩

/-- Convert a stride-3 `HoldsEdges` layout into a flat `Block.HoldsList (encodeEdges es)`
layout. -/
theorem holdsList_of_holdsEdges {n : ℕ} {base : ℕ} {es : List (WeightedEdge n ℕ)}
    {mem : ℕ → ℕ} (h : HoldsEdges base es mem) :
    Block.HoldsList base (encodeEdges es) mem := by
  induction es generalizing base with
  | nil => exact Block.holdsList_nil _ _
  | cons e tl ih =>
    obtain ⟨hu, hv, hw⟩ := h 0 (by simp)
    have htl : HoldsEdges (base + 3) tl mem := fun k hk => by
      obtain ⟨u_k, v_k, w_k⟩ := h (k + 1) (by simp only [List.length_cons]; omega)
      exact ⟨by rwa [show base + 3 + 3 * k = base + 3 * (k + 1) by omega],
        by rwa [show base + 3 + 3 * k + 1 = base + 3 * (k + 1) + 1 by omega],
        by rwa [show base + 3 + 3 * k + 2 = base + 3 * (k + 1) + 2 by omega]⟩
    have ih_tl := ih htl
    intro j
    change mem (base + j.val) = (encodeEdges (e :: tl))[j.val]
    rcases j with ⟨_ | _ | _ | k, hj⟩
    · simpa using hu
    · simpa using hv
    · simpa using hw
    · have hk : k < (encodeEdges tl).length := by
        simp only [encodeEdges_cons, List.length_cons] at hj; omega
      have hget := ih_tl.get k hk
      rw [show base + (k + 3) = base + 3 + k by omega]
      simpa [encodeEdges_cons] using hget

/-- Framing lemma for `HoldsEdges` over `[base, base + 3 * es.length)`. -/
theorem holdsEdges_frame {n : ℕ} {base : ℕ} {es : List (WeightedEdge n ℕ)}
    {m₀ m₁ : ℕ → ℕ} (h : HoldsEdges base es m₀)
    (heq : ∀ a, base ≤ a → a < base + 3 * es.length → m₁ a = m₀ a) :
    HoldsEdges base es m₁ := fun i hi => by
  obtain ⟨hu, hv, hw⟩ := h i hi
  exact ⟨(heq _ (by omega) (by omega)).trans hu,
    (heq _ (by omega) (by omega)).trans hv,
    (heq _ (by omega) (by omega)).trans hw⟩

/-- `Data.init (encode es)` stores `es` in stride-3 `HoldsEdges` layout starting at address
`3`. -/
theorem holdsEdges_init {r n : ℕ} (es : List (WeightedEdge n ℕ)) :
    HoldsEdges 3 es (Data.init (r := r) (encode es)).mem := by
  have hall : Block.HoldsList 1 (encode es) (Data.init (r := r) (encode es)).mem :=
    (outputList_eq_iff.mp (outputList_init (encode es))).2
  refine holdsEdges_of_holdsList fun j => ?_
  have hj := hall.get (j.val + 1 + 1) (by
    have := j.isLt
    simp only [length_encode, length_encodeEdges] at this ⊢
    omega)
  change (Data.init (r := r) (encode es)).mem (3 + j.val) = (encodeEdges es)[j.val]
  have hidx : 3 + j.val = 1 + (j.val + 1 + 1) := by omega
  exact hidx ▸ hj

/-! ## Private Union-by-Rank Forest Invariant -/

private structure UFValid {n : ℕ} (p : Partition n)
    (par : Fin n → Fin n) (rnk : Fin n → ℕ) (repOf : Fin n → Fin n) : Prop where
  par_rep : ∀ x, par (repOf x) = repOf x
  rep_of_root : ∀ r, par r = r → repOf r = r
  rep_par : ∀ x, repOf (par x) = repOf x
  rnk_strict : ∀ x, par x ≠ x → rnk x < rnk (par x)
  rnk_le_rep : ∀ x, rnk x ≤ rnk (repOf x)
  two_pow_rnk : ∀ r, par r = r →
    2 ^ rnk r ≤ (Finset.univ.filter fun z : Fin n => repOf z = r).card
  rel_eq : ∀ x y : Fin n, p.rel x y = decide (repOf x = repOf y)

private theorem ufValid_discrete (n : ℕ) :
    UFValid (Partition.discrete n) id (fun _ => 0) id := by
  refine ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun x h => False.elim (h rfl),
    fun _ => le_rfl, fun r _ => ?_, fun x y => ?_⟩
  · have hmem : r ∈ Finset.univ.filter (fun z : Fin n => z = r) := by simp
    exact Finset.card_pos.mpr ⟨r, hmem⟩
  · exact Bool.eq_iff_iff.mpr (by simp [Partition.rel_discrete])

private theorem ufValid_rnk_le_log {n : ℕ} {p : Partition n}
    {par : Fin n → Fin n} {rnk : Fin n → ℕ} {repOf : Fin n → Fin n}
    (h : UFValid p par rnk repOf) (x : Fin n) :
    rnk x ≤ Nat.log 2 n :=
  (h.rnk_le_rep x).trans (Nat.le_log_of_pow_le Nat.one_lt_two
    ((h.two_pow_rnk (repOf x) (h.par_rep x)).trans ((Finset.card_filter_le _ _).trans (by simp))))

/-- Linking the root of `u` below the root of `v` keeps the forest fields of `UFValid`. -/
private theorem ufValid_link_forest {n : ℕ} {p : Partition n}
    {par : Fin n → Fin n} {rnk : Fin n → ℕ} {repOf : Fin n → Fin n}
    (h : UFValid p par rnk repOf) {u v : Fin n} (hneq : repOf u ≠ repOf v) :
    (∀ x, Function.update par (repOf u) (repOf v)
        (if repOf x = repOf u then repOf v else repOf x) =
      if repOf x = repOf u then repOf v else repOf x) ∧
    (∀ r, Function.update par (repOf u) (repOf v) r = r →
      (if repOf r = repOf u then repOf v else repOf r) = r) ∧
    (∀ x, (if repOf (Function.update par (repOf u) (repOf v) x) = repOf u then repOf v
        else repOf (Function.update par (repOf u) (repOf v) x)) =
      if repOf x = repOf u then repOf v else repOf x) ∧
    (∀ a b, (p.merge u v).rel a b =
      decide ((if repOf a = repOf u then repOf v else repOf a) =
        if repOf b = repOf u then repOf v else repOf b)) := by
  have hru_rep : repOf (repOf u) = repOf u := h.rep_of_root _ (h.par_rep u)
  have hrv_rep : repOf (repOf v) = repOf v := h.rep_of_root _ (h.par_rep v)
  refine ⟨fun x => ?_, fun r hr => ?_, fun x => ?_, fun a b => ?_⟩
  · by_cases hx : repOf x = repOf u
    · simp only [hx, ↓reduceIte, Function.update_of_ne hneq.symm, h.par_rep v]
    · simp only [hx, ↓reduceIte, Function.update_of_ne hx, h.par_rep x]
  · by_cases hr_u : r = repOf u
    · subst hr_u; simp only [Function.update_self] at hr; exact absurd hr.symm hneq
    · rw [Function.update_of_ne hr_u] at hr
      simp [h.rep_of_root r hr, hr_u]
  · by_cases hx : x = repOf u
    · subst hx; simp [hru_rep, hrv_rep]
    · simp only [Function.update_of_ne hx, h.rep_par x]
  · rw [Bool.eq_iff_iff, Partition.rel_merge_eq_true]
    simp only [h.rel_eq, decide_eq_true_eq]
    split_ifs <;> grind

private theorem ufValid_link_lt {n : ℕ} {p : Partition n}
    {par : Fin n → Fin n} {rnk : Fin n → ℕ} {repOf : Fin n → Fin n}
    (h : UFValid p par rnk repOf) {u v : Fin n}
    (hneq : repOf u ≠ repOf v) (hrnk : rnk (repOf u) < rnk (repOf v)) :
    UFValid (p.merge u v)
      (Function.update par (repOf u) (repOf v)) rnk
      (fun z => if repOf z = repOf u then repOf v else repOf z) := by
  obtain ⟨h1, h2, h3, h4⟩ := ufValid_link_forest h hneq
  refine ⟨h1, h2, h3, fun x hx => ?_, fun x => ?_, fun r hr => ?_, h4⟩
  · by_cases hxu : x = repOf u
    · subst hxu; simp only [Function.update_self]; exact hrnk
    · rw [Function.update_of_ne hxu] at hx ⊢
      exact h.rnk_strict x hx
  · have hle := h.rnk_le_rep x
    by_cases hx : repOf x = repOf u
    · simp only [hx, ↓reduceIte]; rw [hx] at hle; omega
    · simp only [hx, ↓reduceIte]; exact hle
  · by_cases hr_u : r = repOf u
    · subst hr_u; simp only [Function.update_self] at hr; exact absurd hr.symm hneq
    · rw [Function.update_of_ne hr_u] at hr
      refine (h.two_pow_rnk r hr).trans (Finset.card_le_card fun z hz => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      simp [hz, hr_u]

private theorem ufValid_link_eq {n : ℕ} {p : Partition n}
    {par : Fin n → Fin n} {rnk : Fin n → ℕ} {repOf : Fin n → Fin n}
    (h : UFValid p par rnk repOf) {u v : Fin n}
    (hneq : repOf u ≠ repOf v) (hrnk : rnk (repOf u) = rnk (repOf v)) :
    UFValid (p.merge u v)
      (Function.update par (repOf v) (repOf u))
      (Function.update rnk (repOf u) (rnk (repOf u) + 1))
      (fun z => if repOf z = repOf v then repOf u else repOf z) := by
  have hru_par : par (repOf u) = repOf u := h.par_rep u
  have hrv_par : par (repOf v) = repOf v := h.par_rep v
  have hru_rep : repOf (repOf u) = repOf u := h.rep_of_root _ hru_par
  obtain ⟨h1, h2, h3, h4⟩ := ufValid_link_forest h hneq.symm
  refine ⟨h1, h2, h3, fun x hx => ?_, fun x => ?_, fun r hr => ?_,
    fun a b => by rw [Partition.merge_comm]; exact h4 a b⟩
  · by_cases hx_v : x = repOf v
    · subst hx_v
      simp only [Function.update_self, Function.update_of_ne hneq.symm]
      omega
    · rw [Function.update_of_ne hx_v] at hx ⊢
      have hx_ne_u : x ≠ repOf u := fun hxu => hx (hxu ▸ hru_par)
      rw [Function.update_of_ne hx_ne_u]
      have hst := h.rnk_strict x hx
      by_cases hp_u : par x = repOf u
      · rw [hp_u, Function.update_self]; rw [hp_u] at hst; omega
      · rw [Function.update_of_ne hp_u]; exact hst
  · have hle := h.rnk_le_rep x
    by_cases hx_u : x = repOf u
    · subst hx_u; simp [hru_rep, hneq]
    · rw [Function.update_of_ne hx_u]
      by_cases hrep_v : repOf x = repOf v
      · simp only [hrep_v, ↓reduceIte, Function.update_self]
        rw [hrep_v] at hle; omega
      · by_cases hrep_u : repOf x = repOf u
        · simp only [hrep_u, hneq, ↓reduceIte, Function.update_self]
          rw [hrep_u] at hle; omega
        · simp only [hrep_v, ↓reduceIte, Function.update_of_ne hrep_u]
          exact hle
  · by_cases hr_v : r = repOf v
    · subst hr_v; simp only [Function.update_self] at hr; exact absurd hr hneq
    · rw [Function.update_of_ne hr_v] at hr
      by_cases hr_u : r = repOf u
      · subst hr_u
        rw [Function.update_self, Nat.pow_succ]
        have hcu := h.two_pow_rnk (repOf u) hru_par
        have hcv := h.two_pow_rnk (repOf v) hrv_par
        rw [← hrnk] at hcv
        have hunion :
            (Finset.univ.filter fun z : Fin n =>
                (if repOf z = repOf v then repOf u else repOf z) = repOf u) =
              (Finset.univ.filter fun z : Fin n => repOf z = repOf u) ∪
                (Finset.univ.filter fun z : Fin n => repOf z = repOf v) := by
          ext z
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
          by_cases hzv : repOf z = repOf v <;> simp [hzv, hneq.symm]
        have hdisj : Disjoint
            (Finset.univ.filter fun z : Fin n => repOf z = repOf u)
            (Finset.univ.filter fun z : Fin n => repOf z = repOf v) := by
          refine Finset.disjoint_left.mpr fun z h1 h2 => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
          exact hneq (h1.symm.trans h2)
        rw [hunion, Finset.card_union_of_disjoint hdisj]
        omega
      · rw [Function.update_of_ne hr_u]
        refine (h.two_pow_rnk r hr).trans (Finset.card_le_card fun z hz => ?_)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        simp [hz, hr_v]

/-! ## Register File (`Fin 26`) and Structured Sub-Programs -/

namespace Reg

private abbrev zero : Fin 26 := 0
private abbrev one : Fin 26 := 1
private abbrev three : Fin 26 := 2
private abbrev nVerts : Fin 26 := 3
private abbrev mEdges : Fin 26 := 4
private abbrev edgeBase : Fin 26 := 5
private abbrev keyBase : Fin 26 := 6
private abbrev permBase : Fin 26 := 7
private abbrev bufBase : Fin 26 := 8
private abbrev parBase : Fin 26 := 9
private abbrev rnkBase : Fin 26 := 10
/-- Output register holding the base address of the length-prefixed output edge list. -/
abbrev out : Fin 26 := 11
private abbrev ctr : Fin 26 := 12
private abbrev outWords : Fin 26 := 13
private abbrev uReg : Fin 26 := 14
private abbrev vReg : Fin 26 := 15
private abbrev wtReg : Fin 26 := 16
private abbrev ruReg : Fin 26 := 17
private abbrev rvReg : Fin 26 := 18
private abbrev flag : Fin 26 := 19
private abbrev addr : Fin 26 := 20
private abbrev tmp1 : Fin 26 := 21
private abbrev tmp2 : Fin 26 := 22

end Reg

open Reg

/-- Register bank of `MergeSort.mergeSortPerm`: its four parameter registers are `mEdges`,
`keyBase`, `permBase` and `bufBase`; its scratch registers are `ctr` through `25`. -/
private def sortMap (r : Fin 18) : Fin 26 :=
  if r.val = 0 then mEdges
  else if r.val = 1 then keyBase
  else if r.val = 2 then permBase
  else if r.val = 3 then bufBase
  else ⟨r.val + 8, by omega⟩

private theorem sortMap_injective : Function.Injective sortMap := by decide

private def kruskalSetup : Code .standard 26 := ram[
  zero ← #0;
  one ← #1;
  three ← #3;
  nVerts ← *one;
  tmp1 ← #2;
  mEdges ← *tmp1;
  edgeBase ← #3;
  tmp1 ← mEdges + mEdges;
  tmp1 ← tmp1 + mEdges;
  keyBase ← edgeBase + tmp1;
  permBase ← keyBase + mEdges;
  bufBase ← permBase + mEdges;
  parBase ← bufBase + mEdges;
  rnkBase ← parBase + nVerts;
  out ← rnkBase + nVerts ]

private def keyBody : Code .standard 26 := ram[
  tmp1 ← ctr + ctr;
  tmp1 ← tmp1 + ctr;
  addr ← edgeBase + tmp1;
  addr ← addr + one;
  addr ← addr + one;
  tmp2 ← *addr;
  addr ← keyBase + ctr;
  *addr ← tmp2;
  ctr ← ctr + one ]

private def keysCode : Code .standard 26 := ram[
  ctr ← #0;
  while ctr < mEdges do [ ⟪keyBody⟫ ] ]

private def ufInitBody : Code .standard 26 := ram[
  addr ← parBase + ctr;
  *addr ← ctr;
  addr ← rnkBase + ctr;
  *addr ← zero;
  ctr ← ctr + one ]

private def ufInitCode : Code .standard 26 := ram[
  ctr ← #0;
  while ctr < nVerts do [ ⟪ufInitBody⟫ ] ]

private def findStepBody (dst : Fin 26) : Code .standard 26 := ram[
  dst ← tmp1;
  addr ← parBase + dst;
  tmp1 ← *addr;
  if dst = tmp1 then [ flag ← #0 ] else [ flag ← #1 ] ]

private def findRoot (src dst : Fin 26) : Code .standard 26 := ram[
  dst ← src;
  addr ← parBase + dst;
  tmp1 ← *addr;
  if dst = tmp1 then [ flag ← #0 ] else [ flag ← #1 ];
  while zero < flag do [ ⟪findStepBody dst⟫ ] ]

private def emitAndUnionCode : Code .standard 26 := ram[
  if ruReg = rvReg then [
    flag ← #0
  ] else [
    addr ← out + one;
    addr ← addr + outWords;
    *addr ← uReg;
    addr ← addr + one;
    *addr ← vReg;
    addr ← addr + one;
    *addr ← wtReg;
    outWords ← outWords + three;
    addr ← rnkBase + ruReg;
    tmp1 ← *addr;
    addr ← rnkBase + rvReg;
    tmp2 ← *addr;
    if tmp1 < tmp2 then [
      addr ← parBase + ruReg;
      *addr ← rvReg
    ] else [
      addr ← parBase + rvReg;
      *addr ← ruReg;
      if tmp1 = tmp2 then [
        tmp1 ← tmp1 + one;
        addr ← rnkBase + ruReg;
        *addr ← tmp1
      ] else [
        flag ← #0
      ]
    ]
  ] ]

private def loadScanEdge : Code .standard 26 := ram[
  addr ← permBase + ctr;
  tmp1 ← *addr;
  tmp2 ← tmp1 + tmp1;
  tmp2 ← tmp2 + tmp1;
  addr ← edgeBase + tmp2;
  uReg ← *addr;
  addr ← addr + one;
  vReg ← *addr;
  addr ← addr + one;
  wtReg ← *addr ]

private def kruskalScanBody : Code .standard 26 :=
  .seq loadScanEdge
    (.seq (findRoot uReg ruReg)
      (.seq (findRoot vReg rvReg)
        (.seq emitAndUnionCode (ram[ ctr ← ctr + one ]))))

private def kruskalScanCode : Code .standard 26 := ram[
  outWords ← #0;
  ctr ← #0;
  while ctr < mEdges do [ ⟪kruskalScanBody⟫ ];
  *out ← outWords ]

/-- Structured deterministic Word-RAM Kruskal program over `Basis.standard`: setup, weight-key
extraction, stable index merge sort (`MergeSort.mergeSortPerm`), union-find initialization, and the
Kruskal scan. -/
def kruskalCode : Code .standard 26 :=
  .seq kruskalSetup
    (.seq keysCode
      (.seq (MergeSort.mergeSortPerm.rename sortMap) (.seq ufInitCode kruskalScanCode)))

/-- Compiled Word-RAM Kruskal program returning `encodeEdges (kruskalEdges es)` via
`ExecutesList`. -/
def kruskalProgram : Program .standard 26 := kruskalCode.program Reg.out

/-! ## Setup, Key Extraction, and Stable Index Sort -/

private theorem kruskalSetup_exec {w n : ℕ} (es : List (WeightedEdge n ℕ))
    (hfit : Fits w (9 * es.length + 2 * n + 4)) :
    ∃ x₁ : Data 26, ExecWithin w kruskalSetup (Data.init (encode es)) x₁ 15 ∧
      x₁.mem = (Data.init (encode es) : Data 26).mem ∧
      x₁.regs zero = 0 ∧ x₁.regs one = 1 ∧ x₁.regs three = 3 ∧
      x₁.regs nVerts = n ∧ x₁.regs mEdges = es.length ∧
      x₁.regs edgeBase = 3 ∧ x₁.regs keyBase = 3 + 3 * es.length ∧
      x₁.regs permBase = 3 + 4 * es.length ∧ x₁.regs bufBase = 3 + 5 * es.length ∧
      x₁.regs parBase = 3 + 6 * es.length ∧
      x₁.regs rnkBase = 3 + 6 * es.length + n ∧
      x₁.regs out = 3 + 6 * es.length + 2 * n := by
  have hm1 : (Data.init (encode es) : Data 26).mem 1 = n := by
    simp [encode]
  have hm2 : (Data.init (encode es) : Data 26).mem 2 = es.length := by
    simp [encode]
  refine WP.exists_execWithin ?_
  wram_exec [kruskalSetup, Data.init_regs, hm1, hm2]
  exact ⟨rfl, by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
    by wram_simp, by wram_simp; omega, by wram_simp; omega, by wram_simp; omega,
    by wram_simp; omega, by wram_simp; omega, by wram_simp; omega⟩

private structure KeyInv {n : ℕ} (es : List (WeightedEdge n ℕ)) (kb : ℕ) (x : Data 26)
    (s : ℕ) (y : Data 26) : Prop where
  frame : ∀ r : Fin 26, r ≠ ctr → r ≠ tmp1 → r ≠ tmp2 → r ≠ addr → y.regs r = x.regs r
  mod : Modifies (Block.mk kb es.length).footprint x.mem y.mem
  keys : ∀ j : ℕ, j < s → (hj : j < es.length) → y.mem (kb + j) = es[j].weight

private theorem keys_exec {w n kb : ℕ} (es : List (WeightedEdge n ℕ)) (x : Data 26)
    (ho : x.regs one = 1) (hm : x.regs mEdges = es.length) (heb : x.regs edgeBase = 3)
    (hkb : x.regs keyBase = kb) (hes : HoldsEdges 3 es x.mem)
    (hdisj : 3 + 3 * es.length ≤ kb) (hfit : Fits w (kb + es.length)) :
    ∃ y : Data 26, ExecWithin w keysCode x y (11 * es.length + 3) ∧
      (∀ r : Fin 26, r ≠ ctr → r ≠ tmp1 → r ≠ tmp2 → r ≠ addr → y.regs r = x.regs r) ∧
      Modifies (Block.mk kb es.length).footprint x.mem y.mem ∧
      Block.HoldsList kb (es.map WeightedEdge.weight) y.mem := by
  have hbody (v : Data 26) (hv : KeyInv es kb x (v.regs ctr) v)
      (hlt : v.regs ctr < es.length) :
      ∃ v' : Data 26, ExecWithin w keyBody v v' 9 ∧
        KeyInv es kb x (v.regs ctr + 1) v' ∧ v'.regs ctr = v.regs ctr + 1 := by
    obtain ⟨hfr, hmodK, hkeysK⟩ := hv
    have hvo : v.regs one = 1 := (hfr one (by decide) (by decide) (by decide) (by decide)).trans ho
    have hveb : v.regs edgeBase = 3 :=
      (hfr edgeBase (by decide) (by decide) (by decide) (by decide)).trans heb
    have hvkb : v.regs keyBase = kb :=
      (hfr keyBase (by decide) (by decide) (by decide) (by decide)).trans hkb
    have hv_es : HoldsEdges 3 es v.mem :=
      holdsEdges_frame hes fun a ha1 ha2 => Modifies.block_iff.mp hmodK a (by dsimp only; omega)
    have hread : v.mem (3 + (v.regs ctr + v.regs ctr + v.regs ctr) + 1 + 1) =
        es[v.regs ctr].weight := by
      rw [show 3 + (v.regs ctr + v.regs ctr + v.regs ctr) + 1 + 1 = 3 + 3 * v.regs ctr + 2 by
        omega]
      exact (hv_es _ hlt).2.2
    refine WP.exists_execWithin ?_
    wram_exec [keyBody, hvo, hveb, hvkb, hread]
    refine ⟨⟨fun r h1 h2 h3 h4 => ?_, ?_, ?_⟩, by wram_simp⟩
    · simp only [Data.write_regs, Data.set_regs, Function.update_of_ne h1,
        Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h4]
      exact hfr r h1 h2 h3 h4
    · wram_simp [Data.write_mem]
      simpa only [Finset.union_self] using
        hmodK.trans (Modifies.write_of_owns (base := kb) (n := es.length) ⟨by omega, by omega⟩ _)
    · intro j hj hj'
      wram_simp [Data.write_mem]
      by_cases hjeq : j = v.regs ctr
      · subst hjeq; exact Function.update_self _ _ _
      · rw [Function.update_of_ne (by omega)]; exact hkeysK j (by omega) hj'
  refine WP.exists_execWithin ?_
  wram_exec [keysCode]
  refine WP.of_spec
    (ExecWithin.loop_count (index := ctr) (limit := mEdges) (N := es.length) (T := 9)
      (KeyInv es kb x)
      (fun _ hq => (hq.frame mEdges (by decide) (by decide) (by decide) (by decide)).trans hm)
      hbody (by wram_simp; omega) ?_) ?_
  · refine ⟨fun r h1 _ _ _ => ?_, Modifies.refl _ _, fun _ hj => by wram_simp at hj⟩
    simp only [Data.set_regs, Function.update_of_ne h1]
  · rintro yK ⟨⟨hfrK, hmodK, hkeysK⟩, _⟩
    refine ⟨by wram_simp; omega, hfrK, hmodK, fun j => ?_⟩
    have hj : j.val < es.length := by simpa using j.isLt
    change yK.mem (kb + j.val) = (es.map WeightedEdge.weight)[j.val]
    rw [List.getElem_map]
    exact hkeysK j.val hj hj

private theorem getElem?_filterMap_getElem? {α : Type*} (xs : List α) :
    ∀ {perm : List ℕ} (hb : ∀ i ∈ perm, i < xs.length) {s : ℕ} (hs : s < perm.length),
      (perm.filterMap (xs[·]?))[s]? = some (xs[perm[s]]'(hb _ (List.getElem_mem hs)))
  | [], _, _, hs => absurd hs (by simp)
  | a :: as, hb, s, hs => by
    rw [List.filterMap_cons_some (List.getElem?_eq_getElem (hb a List.mem_cons_self))]
    cases s with
    | zero => rfl
    | succ k =>
      simpa using getElem?_filterMap_getElem? xs (fun i hi => hb i (List.mem_cons_of_mem a hi))
        (s := k) (by simpa using hs)

/-- Setup, key extraction, and the stable index sort: afterwards the permutation at `permBase`
lists the edges in the order of `sortEdges es`. -/
private theorem prepare_exec {w n : ℕ} (es : List (WeightedEdge n ℕ))
    (hfit : Fits w (9 * es.length + 2 * n + 4)) :
    ∃ (x₁ yK yS : Data 26) (perm : List ℕ),
      ExecWithin w kruskalSetup (Data.init (encode es)) x₁ 15 ∧
      ExecWithin w keysCode x₁ yK (11 * es.length + 3) ∧
      ExecWithin w (MergeSort.mergeSortPerm.rename sortMap) yK yS
        (52 * es.length * Nat.clog 2 es.length + 5 * es.length + 7) ∧
      yS.regs zero = 0 ∧ yS.regs one = 1 ∧ yS.regs three = 3 ∧
      yS.regs nVerts = n ∧ yS.regs mEdges = es.length ∧ yS.regs edgeBase = 3 ∧
      yS.regs permBase = 3 + 4 * es.length ∧ yS.regs parBase = 3 + 6 * es.length ∧
      yS.regs rnkBase = 3 + 6 * es.length + n ∧ yS.regs out = 3 + 6 * es.length + 2 * n ∧
      Modifies (Block.mk (3 + 3 * es.length) (3 * es.length)).footprint
        (Data.init (encode es) : Data 26).mem yS.mem ∧
      Block.HoldsList (3 + 4 * es.length) perm yS.mem ∧
      perm.length = es.length ∧ (∀ i ∈ perm, i < es.length) ∧
      perm.filterMap (es[·]?) = sortEdges es := by
  obtain ⟨x₁, hex_s, hmem1, hz1, ho1, h3_1, hn1, hm1, heb1, hkb1, hpb1, hbb1, hparb1, hrb1,
    hop1⟩ := kruskalSetup_exec es hfit
  have hes1 : HoldsEdges 3 es x₁.mem := hmem1 ▸ holdsEdges_init es
  obtain ⟨yK, hex_k, hfrK, hmodK, hkeys⟩ :=
    keys_exec es x₁ ho1 hm1 heb1 hkb1 hes1 (by omega) (hfit.of_le (by omega))
  have hfrK' (r : Fin 26) (hr : r ∉ ({ctr, tmp1, tmp2, addr} : Finset (Fin 26))) :
      yK.regs r = x₁.regs r := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
    exact hfrK r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
  obtain ⟨yS, hex_sort, ⟨perm, hmodS, hperm_hold, hperm_range, hperm_stable, _,
    hySm_c, _, hySpb_c, _⟩, hout_sort⟩ :=
    ExecWithin.rename_post sortMap_injective
      (MergeSort.mergeSortPerm_exec (kb := 3 + 3 * es.length) (pb := 3 + 4 * es.length)
        (bb := 3 + 5 * es.length) (w := w)
        (es.map WeightedEdge.weight) (yK.comap sortMap)
        (by simpa [Data.comap, sortMap, hfrK' mEdges (by decide)] using hm1)
        (by simpa [Data.comap, sortMap, hfrK' keyBase (by decide)] using hkb1)
        (by simpa [Data.comap, sortMap, hfrK' permBase (by decide)] using hpb1)
        (by simpa [Data.comap, sortMap, hfrK' bufBase (by decide)] using hbb1)
        hkeys (by simp only [List.length_map]; omega) (by simp only [List.length_map]; omega)
        (hfit.of_le (by simp only [List.length_map]; omega)))
  dsimp only [Data.comap_mem] at hmodS hperm_hold
  simp only [List.length_map] at hmodS hperm_range hySm_c
  have hregS (r : Fin 26) (hr1 : ∀ j, sortMap j ≠ r)
      (hr2 : r ∉ ({ctr, tmp1, tmp2, addr} : Finset (Fin 26))) : yS.regs r = x₁.regs r :=
    (hout_sort r hr1).trans (hfrK' r hr2)
  have hperm_len : perm.length = es.length := by simpa using hperm_range.length_eq
  refine ⟨x₁, yK, yS, perm, hex_s, hex_k, by simpa using hex_sort,
    (hregS zero (by decide) (by decide)).trans hz1,
    (hregS one (by decide) (by decide)).trans ho1,
    (hregS three (by decide) (by decide)).trans h3_1,
    (hregS nVerts (by decide) (by decide)).trans hn1,
    by simpa [Data.comap, sortMap] using hySm_c,
    (hregS edgeBase (by decide) (by decide)).trans heb1,
    by simpa [Data.comap, sortMap] using hySpb_c,
    (hregS parBase (by decide) (by decide)).trans hparb1,
    (hregS rnkBase (by decide) (by decide)).trans hrb1,
    (hregS out (by decide) (by decide)).trans hop1, ?_, hperm_hold, hperm_len,
    fun i hi => List.mem_range.mp (hperm_range.subset hi),
    MergeSort.filterMap_getElem?_eq_mergeSort es WeightedEdge.weight hperm_range hperm_stable⟩
  rw [Modifies.block_iff] at hmodK hmodS ⊢
  intro a ha
  dsimp only at ha
  rw [hmodS a (by dsimp only; omega), hmodK a (by dsimp only; omega), hmem1]

/-! ## Union-Find Initialization and `findRoot` -/

private structure UFInitInv (pb rb : ℕ) (x : Data 26) (n s : ℕ) (y : Data 26) : Prop where
  frame : ∀ r : Fin 26, r ≠ ctr → r ≠ addr → y.regs r = x.regs r
  mod : Modifies (Block.mk pb (2 * n)).footprint x.mem y.mem
  par_init : ∀ i : ℕ, i < s → y.mem (pb + i) = i
  rnk_init : ∀ i : ℕ, i < s → y.mem (rb + i) = 0

private theorem ufInit_exec {w n pb rb : ℕ} (x : Data 26)
    (hz : x.regs zero = 0) (ho : x.regs one = 1) (hn : x.regs nVerts = n)
    (hpb : x.regs parBase = pb) (hrb : x.regs rnkBase = rb)
    (hrb_eq : rb = pb + n) (hfit : Fits w (pb + 2 * n + 1)) :
    ∃ y : Data 26, ExecWithin w ufInitCode x y (7 * n + 3) ∧ UFInitInv pb rb x n n y := by
  have hbody (v : Data 26) (hv : UFInitInv pb rb x n (v.regs ctr) v)
      (hlt : v.regs ctr < n) :
      ∃ v' : Data 26, ExecWithin w ufInitBody v v' 5 ∧
        UFInitInv pb rb x n (v.regs ctr + 1) v' ∧ v'.regs ctr = v.regs ctr + 1 := by
    obtain ⟨hfr, hmodU, hparU, hrnkU⟩ := hv
    have hvz : v.regs zero = 0 := (hfr zero (by decide) (by decide)).trans hz
    have hvo : v.regs one = 1 := (hfr one (by decide) (by decide)).trans ho
    have hvpb : v.regs parBase = pb := (hfr parBase (by decide) (by decide)).trans hpb
    have hvrb : v.regs rnkBase = rb := (hfr rnkBase (by decide) (by decide)).trans hrb
    refine WP.exists_execWithin ?_
    wram_exec [ufInitBody, hvz, hvo, hvpb, hvrb]
    refine ⟨⟨fun r h1 h2 => ?_, ?_, ?_, ?_⟩, by wram_simp⟩
    · simp only [Data.write_regs, Data.set_regs, Function.update_of_ne h1,
        Function.update_of_ne h2]
      exact hfr r h1 h2
    · wram_simp [Data.write_mem]
      simpa only [Finset.union_self] using
        (hmodU.trans
          (Modifies.write_of_owns (base := pb) (n := 2 * n) ⟨by omega, by omega⟩ _)).trans
          (Modifies.write_of_owns (base := pb) (n := 2 * n) ⟨by omega, by omega⟩ _)
    · intro i hi
      wram_simp [Data.write_mem]
      rw [Function.update_of_ne (by omega)]
      by_cases hieq : i = v.regs ctr
      · subst hieq; exact Function.update_self _ _ _
      · rw [Function.update_of_ne (by omega)]; exact hparU i (by omega)
    · intro i hi
      wram_simp [Data.write_mem]
      by_cases hieq : i = v.regs ctr
      · subst hieq; exact Function.update_self _ _ _
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hrnkU i (by omega)
  refine WP.exists_execWithin ?_
  wram_exec [ufInitCode]
  refine WP.of_spec
    (ExecWithin.loop_count (index := ctr) (limit := nVerts) (N := n) (T := 5)
      (UFInitInv pb rb x n)
      (fun _ hq => (hq.frame nVerts (by decide) (by decide)).trans hn)
      hbody (by wram_simp; omega) ?_) ?_
  · refine ⟨fun r h1 _ => ?_, Modifies.refl _ _, fun _ hi => by wram_simp at hi,
      fun _ hi => by wram_simp at hi⟩
    simp only [Data.set_regs, Function.update_of_ne h1]
  · rintro yU ⟨hPU, _⟩
    exact ⟨by wram_simp; omega, hPU⟩

private structure FindInv {n : ℕ} (dst : Fin 26)
    (par : Fin n → Fin n) (repOf : Fin n → Fin n) (u : Fin n)
    (x : Data 26) (v : Data 26) : Prop where
  mem_eq : v.mem = x.mem
  regs_frame : ∀ r : Fin 26, r ≠ dst → r ≠ addr → r ≠ tmp1 → r ≠ flag → v.regs r = x.regs r
  cur_state :
    ∃ cur : Fin n,
      v.regs dst = cur.val ∧
      v.regs tmp1 = (par cur).val ∧
      repOf cur = repOf u ∧
      v.regs flag = (if cur = par cur then 0 else 1)

private theorem findRoot_exec {w n pb : ℕ} {p : Partition n}
    {par : Fin n → Fin n} {rnk : Fin n → ℕ} {repOf : Fin n → Fin n}
    (huf : UFValid p par rnk repOf)
    (src dst : Fin 26)
    (hd_z : dst ≠ zero) (hd_pb : dst ≠ parBase)
    (hd_addr : dst ≠ addr) (hd_tmp1 : dst ≠ tmp1) (hd_flag : dst ≠ flag)
    (u : Fin n) (x : Data 26)
    (hz : x.regs zero = 0) (hpb : x.regs parBase = pb)
    (hsrc : x.regs src = u.val)
    (hpar_mem : ∀ z : Fin n, x.mem (pb + z.val) = (par z).val)
    (hfit : Fits w (pb + n)) :
    ∃ y : Data 26, ExecWithin w (findRoot src dst) x y (8 * Nat.log 2 n + 8) ∧
      y.mem = x.mem ∧
      (∀ r : Fin 26, r ≠ dst → r ≠ addr → r ≠ tmp1 → r ≠ flag → y.regs r = x.regs r) ∧
      y.regs dst = (repOf u).val := by
  let rnkVal : ℕ → ℕ := fun k => if hk : k < n then rnk ⟨k, hk⟩ else 0
  have hrv (z : Fin n) : rnkVal z.val = rnk z := by simp [rnkVal]
  -- Every hop sets `dst ← c`, `addr ← parBase + c`, `tmp1 ← par c`, and `flag ← [c ≠ par c]`.
  have hdst (v : Data 26) (c : Fin n) (fl : ℕ) :
      ((((v.set dst c.val).set addr (pb + c.val)).set tmp1 (par c).val).set flag fl).regs dst =
        c.val := by
    rw [Data.set_regs_of_ne hd_flag, Data.set_regs_of_ne hd_tmp1, Data.set_regs_of_ne hd_addr,
      Data.set_regs_self]
  have hinv (v : Data 26) (c : Fin n) (fl : ℕ) (hfl : fl = if c = par c then 0 else 1)
      (hmem : v.mem = x.mem)
      (hfr : ∀ r : Fin 26, r ≠ dst → r ≠ addr → r ≠ tmp1 → r ≠ flag → v.regs r = x.regs r)
      (hrep : repOf c = repOf u) :
      FindInv dst par repOf u x
        ((((v.set dst c.val).set addr (pb + c.val)).set tmp1 (par c).val).set flag fl) := by
    refine ⟨hmem, fun r h1 h2 h3 h4 => ?_, c, hdst v c fl, ?_, hrep, ?_⟩
    · rw [Data.set_regs_of_ne h4, Data.set_regs_of_ne h3, Data.set_regs_of_ne h2,
        Data.set_regs_of_ne h1]
      exact hfr r h1 h2 h3 h4
    · rw [Data.set_regs_of_ne (show tmp1 ≠ flag by decide), Data.set_regs_self]
    · rw [Data.set_regs_self, hfl]
  have hbody (v : Data 26) (hv : FindInv dst par repOf u x v)
      (hc : (Cond.lt zero flag).Holds v) :
      ∃ v' : Data 26, ExecWithin w (findStepBody dst) v v' 6 ∧
        FindInv dst par repOf u x v' ∧
        Nat.log 2 n - rnkVal (v'.regs dst) < Nat.log 2 n - rnkVal (v.regs dst) := by
    obtain ⟨hmem_v, hfr_v, cur, hdst_v, htmp1_v, hrep_v, hflag_v⟩ := hv
    have hvz : v.regs zero = 0 :=
      (hfr_v zero hd_z.symm (by decide) (by decide) (by decide)).trans hz
    have hvpb : v.regs parBase = pb :=
      (hfr_v parBase hd_pb.symm (by decide) (by decide) (by decide)).trans hpb
    have hflag_pos : 0 < v.regs flag := by simpa only [Cond.holds_lt, hvz] using hc
    have hcur_ne : cur ≠ par cur := fun heq => by rw [ite_eq_left heq] at hflag_v; omega
    obtain ⟨nxt, hnxt⟩ : ∃ z, z = par cur := ⟨_, rfl⟩
    rw [← hnxt] at htmp1_v
    have hread_nxt : v.mem (pb + nxt.val) = (par nxt).val := by rw [hmem_v]; exact hpar_mem nxt
    have hrnk_lt : rnk cur < rnk nxt := hnxt ▸ huf.rnk_strict cur hcur_ne.symm
    have hrnk_le : rnk nxt ≤ Nat.log 2 n := ufValid_rnk_le_log huf nxt
    have hrep_nxt : repOf nxt = repOf u := hnxt ▸ (huf.rep_par cur).trans hrep_v
    have hdec : Nat.log 2 n - rnk nxt < Nat.log 2 n - rnk cur := by omega
    have := nxt.isLt
    refine WP.exists_execWithin ?_
    unfold findStepBody
    by_cases hroot : nxt = par nxt
    · have hcond : (nxt.val = (par nxt).val) = True := eq_true (congrArg Fin.val hroot)
      wram_exec [hvpb, htmp1_v, hread_nxt, hcond, hd_pb, hd_addr, hd_tmp1, hd_flag]
      exact ⟨hinv v nxt 0 (by rw [ite_eq_left hroot]) hmem_v hfr_v hrep_nxt,
        by rwa [hdst, hdst_v, hrv, hrv]⟩
    · have hcond : (nxt.val = (par nxt).val) = False := eq_false (mt Fin.ext hroot)
      wram_exec [hvpb, htmp1_v, hread_nxt, hcond, hd_pb, hd_addr, hd_tmp1, hd_flag]
      exact ⟨hinv v nxt 1 (by rw [ite_eq_right hroot]) hmem_v hfr_v hrep_nxt,
        by rwa [hdst, hdst_v, hrv, hrv]⟩
  have hloop (fl : ℕ) (hfl : fl = if u = par u then 0 else 1) :
      ∃ y : Data 26, ExecWithin w (.loop (.lt zero flag) (findStepBody dst))
          ((((x.set dst u.val).set addr (pb + u.val)).set tmp1 (par u).val).set flag fl) y
          (8 * Nat.log 2 n + 2) ∧
        y.mem = x.mem ∧
        (∀ r : Fin 26, r ≠ dst → r ≠ addr → r ≠ tmp1 → r ≠ flag → y.regs r = x.regs r) ∧
        y.regs dst = (repOf u).val := by
    obtain ⟨y, hex, ⟨hmem_y, hfr_y, cur, hdst_y, _, hrep_y, hflag_y⟩, hstop⟩ :=
      ExecWithin.loop_invariant (cond := .lt zero flag) (body := findStepBody dst)
        (FindInv dst par repOf u x) (fun v => Nat.log 2 n - rnkVal (v.regs dst)) (T := 6) hbody
        (hinv x u fl hfl rfl (fun _ _ _ _ _ => rfl) rfl)
    have hyz : y.regs zero = 0 :=
      (hfr_y zero hd_z.symm (by decide) (by decide) (by decide)).trans hz
    simp only [Cond.holds_lt, hyz] at hstop
    have hcur_root : cur = par cur :=
      Decidable.byContradiction fun hne => by rw [ite_eq_right hne] at hflag_y; omega
    exact ⟨y, hex.mono (by omega), hmem_y, hfr_y,
      by rw [hdst_y, ← hrep_y, huf.rep_of_root cur hcur_root.symm]⟩
  have hread_u : x.mem (pb + u.val) = (par u).val := hpar_mem u
  have := u.isLt
  refine WP.exists_execWithin ?_
  unfold findRoot
  by_cases hroot : u = par u
  · have hcond : (u.val = (par u).val) = True := eq_true (congrArg Fin.val hroot)
    wram_exec [hpb, hsrc, hread_u, hcond, hd_pb, hd_addr, hd_tmp1, hd_flag]
    obtain ⟨y, hex, hy⟩ := hloop 0 (by rw [ite_eq_left hroot])
    exact WP.of_execWithin hex ⟨by omega, hy⟩
  · have hcond : (u.val = (par u).val) = False := eq_false fun h => hroot (Fin.ext h)
    wram_exec [hpb, hsrc, hread_u, hcond, hd_pb, hd_addr, hd_tmp1, hd_flag]
    obtain ⟨y, hex, hy⟩ := hloop 1 (by rw [ite_eq_right hroot])
    exact WP.of_execWithin hex ⟨by omega, hy⟩

/-! ## Kruskal Scan -/

private structure ScanInv {n : ℕ} (sorted : List (WeightedEdge n ℕ))
    (eb sb pb rb op : ℕ) (x_mem : ℕ → ℕ) (s : ℕ) (y : Data 26) : Prop where
  zero_eq : y.regs zero = 0
  one_eq : y.regs one = 1
  three_eq : y.regs three = 3
  nVerts_eq : y.regs nVerts = n
  mEdges_eq : y.regs mEdges = sorted.length
  edgeBase_eq : y.regs edgeBase = eb
  permBase_eq : y.regs permBase = sb
  parBase_eq : y.regs parBase = pb
  rnkBase_eq : y.regs rnkBase = rb
  out_eq : y.regs out = op
  mod : Modifies (Block.mk pb (2 * n + 1 + 3 * sorted.length)).footprint x_mem y.mem
  state :
    ∃ (p : Partition n) (par : Fin n → Fin n) (rnk : Fin n → ℕ)
      (repOf : Fin n → Fin n) (acc : List (WeightedEdge n ℕ)),
      UFValid p par rnk repOf ∧
      (∀ z : Fin n, y.mem (pb + z.val) = (par z).val) ∧
      (∀ z : Fin n, y.mem (rb + z.val) = rnk z) ∧
      acc.length ≤ s ∧
      y.regs outWords = 3 * acc.length ∧
      HoldsEdges (op + 1) acc y.mem ∧
      acc ++ kruskalScan p (sorted.drop s) = kruskalScan (Partition.discrete n) sorted

private theorem emitAndUnion_exec {w n m eb sb pb rb op s : ℕ}
    {p : Partition n} {par : Fin n → Fin n} {rnk : Fin n → ℕ} {repOf : Fin n → Fin n}
    (huf : UFValid p par rnk repOf)
    (e : WeightedEdge n ℕ) (acc : List (WeightedEdge n ℕ))
    (x_mem : ℕ → ℕ) (y : Data 26)
    (hs_lt : s < m) (hacc_le : acc.length ≤ s)
    (hrb_eq : rb = pb + n) (hop_eq : op = pb + 2 * n)
    (hfit : Fits w (op + 1 + 3 * m))
    (hyz : y.regs zero = 0) (hyo : y.regs one = 1)
    (hy3 : y.regs three = 3)
    (hyn : y.regs nVerts = n) (hym : y.regs mEdges = m)
    (hyeb : y.regs edgeBase = eb) (hysb : y.regs permBase = sb)
    (hypb : y.regs parBase = pb) (hyrb : y.regs rnkBase = rb)
    (hyop : y.regs out = op) (hys : y.regs ctr = s)
    (hyow : y.regs outWords = 3 * acc.length)
    (hyu : y.regs uReg = e.u.val) (hyv : y.regs vReg = e.v.val) (hyw : y.regs wtReg = e.weight)
    (hyru : y.regs ruReg = (repOf e.u).val) (hyrv : y.regs rvReg = (repOf e.v).val)
    (hmod : Modifies (Block.mk pb (2 * n + 1 + 3 * m)).footprint x_mem y.mem)
    (hpar_mem : ∀ z : Fin n, y.mem (pb + z.val) = (par z).val)
    (hrnk_mem : ∀ z : Fin n, y.mem (rb + z.val) = rnk z)
    (hacc_mem : HoldsEdges (op + 1) acc y.mem) :
    ∃ z : Data 26, ExecWithin w emitAndUnionCode y z 24 ∧
      z.regs zero = 0 ∧ z.regs one = 1 ∧ z.regs three = 3 ∧
      z.regs nVerts = n ∧ z.regs mEdges = m ∧
      z.regs edgeBase = eb ∧ z.regs permBase = sb ∧
      z.regs parBase = pb ∧ z.regs rnkBase = rb ∧
      z.regs out = op ∧ z.regs ctr = s ∧
      Modifies (Block.mk pb (2 * n + 1 + 3 * m)).footprint x_mem z.mem ∧
      ∃ (p' : Partition n) (par' : Fin n → Fin n) (rnk' : Fin n → ℕ)
        (repOf' : Fin n → Fin n) (acc' : List (WeightedEdge n ℕ)),
        UFValid p' par' rnk' repOf' ∧
        (∀ x_v : Fin n, z.mem (pb + x_v.val) = (par' x_v).val) ∧
        (∀ x_v : Fin n, z.mem (rb + x_v.val) = rnk' x_v) ∧
        acc'.length ≤ s + 1 ∧
        z.regs outWords = 3 * acc'.length ∧
        HoldsEdges (op + 1) acc' z.mem ∧
        (if !p.rel e.u e.v then
          p' = p.merge e.u e.v ∧ acc' = acc ++ [e]
        else
          p' = p ∧ acc' = acc) := by
  set ru := repOf e.u
  set rv := repOf e.v
  by_cases hsame : ru.val = rv.val
  · have hru_eq : ru = rv := Fin.ext hsame
    have hrel_t : p.rel e.u e.v = true := by rw [huf.rel_eq]; simp [ru, rv, hru_eq]
    refine WP.exists_execWithin ?_
    wram_exec [emitAndUnionCode, hyru, hyrv, hsame]
    refine ⟨by wram_simp [hyz], by wram_simp [hyo], by wram_simp [hy3],
      by wram_simp [hyn], by wram_simp [hym], by wram_simp [hyeb], by wram_simp [hysb],
      by wram_simp [hypb], by wram_simp [hyrb], by wram_simp [hyop], by wram_simp [hys],
      hmod, p, par, rnk, repOf, acc, huf, hpar_mem, hrnk_mem, by omega,
      by wram_simp [hyow], hacc_mem, by simp [hrel_t]⟩
  · have hneq : ru ≠ rv := fun h => hsame (congrArg Fin.val h)
    have hrel_f : p.rel e.u e.v = false := by rw [huf.rel_eq]; simp [ru, rv, hneq]
    have hread_ru : y.mem (rb + ru.val) = rnk ru := hrnk_mem ru
    have hread_rv : y.mem (rb + rv.val) = rnk rv := hrnk_mem rv
    have hrnk_ru_le := ufValid_rnk_le_log huf ru
    have hrnk_rv_le := ufValid_rnk_le_log huf rv
    have hfit_rnk1 : Fits w (rnk ru + 1) := hfit.of_le (by
      have hlog : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
      have := ru.isLt; omega)
    have hacc_snoc (m_after : ℕ → ℕ)
        (hm_eq : ∀ a, op + 1 ≤ a → a < op + 1 + 3 * (acc.length + 1) →
          m_after a =
            Function.update (Function.update (Function.update y.mem
              (op + 1 + 3 * acc.length) e.u.val)
              (op + 1 + 3 * acc.length + 1) e.v.val)
              (op + 1 + 3 * acc.length + 2) e.weight a) :
        HoldsEdges (op + 1) (acc ++ [e]) m_after := fun j hj => by
      simp only [List.length_append, List.length_singleton] at hj
      rw [hm_eq _ (by omega) (by omega), hm_eq _ (by omega) (by omega),
        hm_eq _ (by omega) (by omega)]
      by_cases hjeq : j = acc.length
      · subst hjeq
        simp only [le_rfl, List.getElem_append_right, Nat.sub_self, List.getElem_singleton]
        exact ⟨by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_self],
          by rw [Function.update_of_ne (by omega), Function.update_self],
          by rw [Function.update_self]⟩
      · have hj_lt : j < acc.length := by omega
        obtain ⟨au, av, aw⟩ := hacc_mem j hj_lt
        simp only [List.getElem_append_left hj_lt]
        exact ⟨by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]; exact au,
          by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]; exact av,
          by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]; exact aw⟩
    have hlink (a b : Fin n) (M : ℕ → ℕ) (hM : M = Function.update (Function.update
        (Function.update (Function.update y.mem (op + 1 + 3 * acc.length) e.u.val)
          (op + 1 + 3 * acc.length + 1) e.v.val) (op + 1 + 3 * acc.length + 2) e.weight)
        (pb + a.val) b.val) :
        Modifies (Block.mk pb (2 * n + 1 + 3 * m)).footprint x_mem M ∧
          (∀ z : Fin n, M (pb + z.val) = (Function.update par a b z).val) ∧
          (∀ z : Fin n, M (rb + z.val) = rnk z) ∧
          HoldsEdges (op + 1) (acc ++ [e]) M := by
      subst hM
      have := a.isLt
      refine ⟨?_, fun z => ?_, fun z => ?_, hacc_snoc _ fun c hc1 hc2 => ?_⟩
      · have hown {m₀ : ℕ → ℕ} {c : ℕ} (hc : pb ≤ c ∧ c < pb + (2 * n + 1 + 3 * m)) (v : ℕ) :=
          Modifies.write_of_owns (m := m₀) (base := pb) (n := 2 * n + 1 + 3 * m) (a := c) hc v
        simpa only [Finset.union_self] using
          (((hmod.trans (hown ⟨by omega, by omega⟩ e.u.val)).trans
            (hown ⟨by omega, by omega⟩ e.v.val)).trans
            (hown ⟨by omega, by omega⟩ e.weight)).trans
            (hown ⟨by omega, by omega⟩ b.val)
      · have := z.isLt
        by_cases hza : z = a
        · subst hza; simp
        · have hne : z.val ≠ a.val := fun h => hza (Fin.ext h)
          rw [Function.update_of_ne (by omega), Function.update_of_ne hza,
            Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]
          exact hpar_mem z
      · have := z.isLt
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hrnk_mem z
      · rw [Function.update_of_ne (by omega)]
    refine WP.exists_execWithin ?_
    unfold emitAndUnionCode
    by_cases hr_lt : rnk ru < rnk rv
    · wram_exec [hyo, hy3, hypb, hyrb, hyop, hyow, hyu, hyv, hyw, hyru, hyrv,
        hsame, hread_ru, hread_rv, hr_lt]
      obtain ⟨hL1, hL2, hL3, hL4⟩ := hlink ru rv _ rfl
      refine ⟨by wram_simp [hyz], by wram_simp [hyo], by wram_simp [hy3],
        by wram_simp [hyn], by wram_simp [hym], by wram_simp [hyeb], by wram_simp [hysb],
        by wram_simp [hypb], by wram_simp [hyrb], by wram_simp [hyop], by wram_simp [hys],
        ?_, p.merge e.u e.v, Function.update par ru rv, rnk,
        (fun z => if repOf z = ru then rv else repOf z), acc ++ [e],
        ufValid_link_lt huf hneq hr_lt, ?_, ?_,
        by simp only [List.length_append, List.length_singleton]; omega,
        by wram_simp [hyow]; simp only [List.length_append, List.length_singleton]; omega,
        ?_, by simp [hrel_f]⟩
      all_goals (wram_simp [Data.write_mem]; assumption)
    · by_cases hr_eq : rnk ru = rnk rv
      · wram_exec [hyo, hy3, hypb, hyrb, hyop, hyow, hyu, hyv, hyw, hyru, hyrv,
          hsame, hread_ru, hread_rv, hr_lt, hr_eq, hfit_rnk1]
        obtain ⟨hL1, hL2, hL3, hL4⟩ := hlink rv ru _ rfl
        have := ru.isLt
        refine ⟨by wram_simp [hyz], by wram_simp [hyo], by wram_simp [hy3],
          by wram_simp [hyn], by wram_simp [hym], by wram_simp [hyeb], by wram_simp [hysb],
          by wram_simp [hypb], by wram_simp [hyrb], by wram_simp [hyop], by wram_simp [hys],
          ?_, p.merge e.u e.v, Function.update par rv ru,
          Function.update rnk ru (rnk ru + 1),
          (fun z => if repOf z = rv then ru else repOf z), acc ++ [e],
          ufValid_link_eq huf hneq hr_eq, ?_, ?_,
          by simp only [List.length_append, List.length_singleton]; omega,
          by wram_simp [hyow]; simp only [List.length_append, List.length_singleton]; omega,
          ?_, by simp [hrel_f]⟩
        · wram_simp [Data.write_mem]
          simpa only [Finset.union_self] using
            hL1.trans
              (Modifies.write_of_owns (base := pb) (n := 2 * n + 1 + 3 * m) ⟨by omega, by omega⟩ _)
        · intro x_v
          wram_simp [Data.write_mem]
          have := x_v.isLt
          rw [Function.update_of_ne (by omega)]
          exact hL2 x_v
        · intro x_v
          wram_simp [Data.write_mem]
          by_cases hxv : x_v = ru
          · subst hxv; simp [hr_eq]
          · have hne_val : x_v.val ≠ ru.val := fun h => hxv (Fin.ext h)
            rw [Function.update_of_ne (by omega), Function.update_of_ne hxv]
            exact hL3 x_v
        · wram_simp [Data.write_mem]
          exact holdsEdges_frame hL4 fun c hc1 hc2 => Function.update_of_ne (by omega) _ _
      · have hr_gt : rnk rv < rnk ru := by omega
        have huf' : UFValid (p.merge e.u e.v)
            (Function.update par rv ru) rnk
            (fun z => if repOf z = rv then ru else repOf z) := by
          rw [Partition.merge_comm p e.u e.v]
          exact ufValid_link_lt huf hneq.symm hr_gt
        wram_exec [hyo, hy3, hypb, hyrb, hyop, hyow, hyu, hyv, hyw, hyru, hyrv,
          hsame, hread_ru, hread_rv, hr_lt, hr_eq]
        obtain ⟨hL1, hL2, hL3, hL4⟩ := hlink rv ru _ rfl
        refine ⟨by wram_simp [hyz], by wram_simp [hyo], by wram_simp [hy3],
          by wram_simp [hyn], by wram_simp [hym], by wram_simp [hyeb], by wram_simp [hysb],
          by wram_simp [hypb], by wram_simp [hyrb], by wram_simp [hyop], by wram_simp [hys],
          ?_, p.merge e.u e.v, Function.update par rv ru, rnk,
          (fun z => if repOf z = rv then ru else repOf z), acc ++ [e],
          huf', ?_, ?_,
          by simp only [List.length_append, List.length_singleton]; omega,
          by wram_simp [hyow]; simp only [List.length_append, List.length_singleton]; omega,
          ?_, by simp [hrel_f]⟩
        all_goals (wram_simp [Data.write_mem]; assumption)

private theorem kruskalScanBody_exec {w n eb sb pb rb op : ℕ}
    (es sorted : List (WeightedEdge n ℕ)) (perm : List ℕ) (x_mem : ℕ → ℕ)
    (hperm_len : perm.length = sorted.length)
    (hperm_bound : ∀ i ∈ perm, i < es.length)
    (hsorted_eq : perm.filterMap (es[·]?) = sorted)
    (heb_disj : eb + 3 * es.length ≤ pb) (hsb_disj : sb + sorted.length ≤ pb)
    (hrb_eq : rb = pb + n) (hop_eq : op = pb + 2 * n)
    (hes_mem : HoldsEdges eb es x_mem) (hperm_mem : Block.HoldsList sb perm x_mem)
    (hfit : Fits w (op + 1 + 3 * sorted.length))
    (y : Data 26)
    (hy : ScanInv sorted eb sb pb rb op x_mem (y.regs ctr) y)
    (hlt : y.regs ctr < sorted.length) :
    ∃ z : Data 26, ExecWithin w kruskalScanBody y z (16 * Nat.log 2 n + 51) ∧
      ScanInv sorted eb sb pb rb op x_mem (y.regs ctr + 1) z ∧
      z.regs ctr = y.regs ctr + 1 := by
  obtain ⟨s, hs_def⟩ : ∃ sv, y.regs ctr = sv := ⟨_, rfl⟩
  rw [hs_def] at hy hlt ⊢
  obtain ⟨hyz, hyo, hy3, hyn, hym, hyeb, hysb, hypb, hyrb, hyop, hmodS,
    p, par, rnk, repOf, acc, huf, hpar_mem, hrnk_mem, hacc_le, hyow, hacc_mem, hscan_eq⟩ := hy
  have hs_p : s < perm.length := by omega
  have hi_lt : perm[s] < es.length := hperm_bound _ (List.getElem_mem hs_p)
  have he_eq : sorted[s] = es[perm[s]] := by
    have h := getElem?_filterMap_getElem? es hperm_bound hs_p
    rw [hsorted_eq, List.getElem?_eq_getElem hlt] at h
    exact Option.some.inj h
  have hread_i : y.mem (sb + s) = perm[s] :=
    (Modifies.block_iff.mp hmodS _ (by dsimp only; omega)).trans (hperm_mem.get s hs_p)
  obtain ⟨heu, hev, hew⟩ := holdsEdges_frame hes_mem
    (fun a ha1 ha2 => Modifies.block_iff.mp hmodS a (by dsimp only; omega)) _ hi_lt
  obtain ⟨e, he_def⟩ : ∃ e, sorted[s] = e := ⟨_, rfl⟩
  rw [← he_eq, he_def] at heu hev hew
  have hload : ∃ y1 : Data 26, ExecWithin w loadScanEdge y y1 10 ∧
      y1.mem = y.mem ∧
      (∀ r : Fin 26, r ≠ tmp1 → r ≠ tmp2 → r ≠ addr → r ≠ uReg → r ≠ vReg → r ≠ wtReg →
        y1.regs r = y.regs r) ∧
      y1.regs uReg = e.u.val ∧ y1.regs vReg = e.v.val ∧ y1.regs wtReg = e.weight := by
    have hmul3 : perm[s] + perm[s] + perm[s] = 3 * perm[s] := by omega
    have he0 : y.mem (eb + (perm[s] + perm[s] + perm[s])) = e.u.val := by rwa [hmul3]
    have he1 : y.mem (eb + (perm[s] + perm[s] + perm[s]) + 1) = e.v.val := by rwa [hmul3]
    have he2 : y.mem (eb + (perm[s] + perm[s] + perm[s]) + 1 + 1) = e.weight := by
      rwa [hmul3, Nat.add_assoc]
    refine WP.exists_execWithin ?_
    wram_exec [loadScanEdge, hyo, hysb, hyeb, hs_def, hread_i, he0, he1, he2]
    refine ⟨rfl, fun r h1 h2 h3 h4 h5 h6 => ?_, by wram_simp, by wram_simp, by wram_simp⟩
    simp only [Data.set_regs, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3, Function.update_of_ne h4, Function.update_of_ne h5,
      Function.update_of_ne h6]
  obtain ⟨y1, hex_load, hmem1, hfr1, hy1_u, hy1_v, hy1_w⟩ := hload
  have hfr1' (r : Fin 26)
      (hr : r ∉ ({tmp1, tmp2, addr, uReg, vReg, wtReg} : Finset (Fin 26))) :
      y1.regs r = y.regs r := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
    exact hfr1 r h1 h2 h3 h4 h5 h6
  obtain ⟨y2, hex_fu, hmem2, hfr2, hy2_ru⟩ :=
    findRoot_exec huf uReg ruReg (by decide) (by decide) (by decide) (by decide) (by decide)
      e.u y1 ((hfr1' zero (by decide)).trans hyz) ((hfr1' parBase (by decide)).trans hypb)
      hy1_u (fun z => (congrFun hmem1 _).trans (hpar_mem z)) (hfit.of_le (by omega))
  obtain ⟨y3, hex_fv, hmem3, hfr3, hy3_rv⟩ :=
    findRoot_exec huf vReg rvReg (by decide) (by decide) (by decide) (by decide) (by decide)
      e.v y2
      ((hfr2 zero (by decide) (by decide) (by decide) (by decide)).trans
        ((hfr1' zero (by decide)).trans hyz))
      ((hfr2 parBase (by decide) (by decide) (by decide) (by decide)).trans
        ((hfr1' parBase (by decide)).trans hypb))
      ((hfr2 vReg (by decide) (by decide) (by decide) (by decide)).trans hy1_v)
      (fun z => (congrFun (hmem2.trans hmem1) _).trans (hpar_mem z)) (hfit.of_le (by omega))
  have hmem3_eq : y3.mem = y.mem := hmem3.trans (hmem2.trans hmem1)
  have hfr3' (r : Fin 26)
      (hr : r ∉ ({tmp1, tmp2, addr, uReg, vReg, wtReg, ruReg, rvReg, flag} :
        Finset (Fin 26))) :
      y3.regs r = y.regs r := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hr
    exact (hfr3 r h8 h3 h1 h9).trans ((hfr2 r h7 h3 h1 h9).trans (hfr1 r h1 h2 h3 h4 h5 h6))
  obtain ⟨y4, hex_eu, hy4z, hy4o, hy43, hy4n, hy4m, hy4eb, hy4sb, hy4pb, hy4rb,
    hy4op, hy4s, hmod4, p', par', rnk', repOf', acc', huf', hpar4, hrnk4, hacc4_le,
    hy4ow, hacc4_mem, hbranch⟩ :=
    emitAndUnion_exec huf e acc x_mem y3 hlt hacc_le hrb_eq hop_eq hfit
      ((hfr3' zero (by decide)).trans hyz) ((hfr3' one (by decide)).trans hyo)
      ((hfr3' three (by decide)).trans hy3) ((hfr3' nVerts (by decide)).trans hyn)
      ((hfr3' mEdges (by decide)).trans hym) ((hfr3' edgeBase (by decide)).trans hyeb)
      ((hfr3' permBase (by decide)).trans hysb) ((hfr3' parBase (by decide)).trans hypb)
      ((hfr3' rnkBase (by decide)).trans hyrb) ((hfr3' out (by decide)).trans hyop)
      ((hfr3' ctr (by decide)).trans hs_def) ((hfr3' outWords (by decide)).trans hyow)
      ((hfr3 uReg (by decide) (by decide) (by decide) (by decide)).trans
        ((hfr2 uReg (by decide) (by decide) (by decide) (by decide)).trans hy1_u))
      ((hfr3 vReg (by decide) (by decide) (by decide) (by decide)).trans
        ((hfr2 vReg (by decide) (by decide) (by decide) (by decide)).trans hy1_v))
      ((hfr3 wtReg (by decide) (by decide) (by decide) (by decide)).trans
        ((hfr2 wtReg (by decide) (by decide) (by decide) (by decide)).trans hy1_w))
      ((hfr3 ruReg (by decide) (by decide) (by decide) (by decide)).trans hy2_ru)
      hy3_rv
      (hmem3_eq ▸ hmodS)
      (fun z => (congrFun hmem3_eq _).trans (hpar_mem z))
      (fun z => (congrFun hmem3_eq _).trans (hrnk_mem z))
      (hmem3_eq ▸ hacc_mem)
  obtain ⟨y5, hex_inc, hy5⟩ : ∃ y5 : Data 26,
      ExecWithin w (ram[ ctr ← ctr + one ]) y4 y5 1 ∧ y5 = y4.set ctr (s + 1) := by
    refine WP.exists_execWithin ?_
    wram_exec [hy4s, hy4o]
    rfl
  subst hy5
  have hex_body : ExecWithin w kruskalScanBody y (y4.set ctr (s + 1))
      (16 * Nat.log 2 n + 51) := by
    unfold kruskalScanBody
    exact (hex_load.seq (hex_fu.seq (hex_fv.seq (hex_eu.seq hex_inc)))).mono (by omega)
  refine ⟨y4.set ctr (s + 1), hex_body,
    ⟨by wram_simp [hy4z], by wram_simp [hy4o], by wram_simp [hy43],
      by wram_simp [hy4n], by wram_simp [hy4m], by wram_simp [hy4eb], by wram_simp [hy4sb],
      by wram_simp [hy4pb], by wram_simp [hy4rb], by wram_simp [hy4op],
      hmod4, p', par', rnk', repOf', acc', huf', hpar4, hrnk4, hacc4_le,
      by wram_simp [hy4ow], hacc4_mem, ?_⟩,
    by wram_simp⟩
  rw [List.drop_eq_getElem_cons hlt, he_def, kruskalScan_cons] at hscan_eq
  by_cases hrel : p.rel e.u e.v = true
  · simp only [hrel, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hbranch hscan_eq
    rw [hbranch.1, hbranch.2]; exact hscan_eq
  · have hrel_f : p.rel e.u e.v = false := Bool.eq_false_iff.mpr hrel
    simp only [hrel_f, Bool.not_false, ↓reduceIte] at hbranch hscan_eq
    rw [hbranch.1, hbranch.2, List.append_assoc, List.singleton_append]; exact hscan_eq

private theorem kruskalScan_exec {w n eb sb pb rb op : ℕ}
    (es sorted : List (WeightedEdge n ℕ)) (perm : List ℕ) (yU : Data 26)
    (hperm_len : perm.length = sorted.length)
    (hperm_bound : ∀ i ∈ perm, i < es.length)
    (hsorted_eq : perm.filterMap (es[·]?) = sorted)
    (heb_disj : eb + 3 * es.length ≤ pb) (hsb_disj : sb + sorted.length ≤ pb)
    (hrb_eq : rb = pb + n) (hop_eq : op = pb + 2 * n)
    (hfit : Fits w (op + 1 + 3 * sorted.length))
    (hyUz : yU.regs zero = 0) (hyUo : yU.regs one = 1) (hyU3 : yU.regs three = 3)
    (hyUn : yU.regs nVerts = n) (hyUm : yU.regs mEdges = sorted.length)
    (hyUeb : yU.regs edgeBase = eb) (hyUsb : yU.regs permBase = sb)
    (hyUpb : yU.regs parBase = pb) (hyUrb : yU.regs rnkBase = rb)
    (hyUop : yU.regs out = op)
    (hes_mem : HoldsEdges eb es yU.mem) (hperm_mem : Block.HoldsList sb perm yU.mem)
    (hpar_init : ∀ i : ℕ, i < n → yU.mem (pb + i) = i)
    (hrnk_init : ∀ i : ℕ, i < n → yU.mem (rb + i) = 0) :
    ∃ yF : Data 26,
      ExecWithin w kruskalScanCode yU yF
        (16 * sorted.length * Nat.log 2 n + 53 * sorted.length + 5) ∧
      Modifies (Block.mk pb (2 * n + 1 + 3 * sorted.length)).footprint yU.mem yF.mem ∧
      yF.regs out = op ∧
      outputList yF.mem (yF.regs out) =
        encodeEdges (kruskalScan (Partition.discrete n) sorted) := by
  refine WP.exists_execWithin ?_
  wram_exec [kruskalScanCode]
  refine WP.of_spec
    (ExecWithin.loop_count (index := ctr) (limit := mEdges) (N := sorted.length)
      (T := 16 * Nat.log 2 n + 51)
      (ScanInv sorted eb sb pb rb op yU.mem)
      (fun _ hq => hq.mEdges_eq)
      (kruskalScanBody_exec es sorted perm yU.mem hperm_len hperm_bound hsorted_eq heb_disj
        hsb_disj hrb_eq hop_eq hes_mem hperm_mem hfit)
      (by wram_simp; omega) ?_) ?_
  · refine ⟨by wram_simp [hyUz], by wram_simp [hyUo], by wram_simp [hyU3],
      by wram_simp [hyUn], by wram_simp [hyUm], by wram_simp [hyUeb], by wram_simp [hyUsb],
      by wram_simp [hyUpb], by wram_simp [hyUrb], by wram_simp [hyUop], Modifies.refl _ _,
      Partition.discrete n, id, (fun _ => 0), id, [], ufValid_discrete n,
      fun z => by wram_simp; exact hpar_init z.val z.isLt,
      fun z => by wram_simp; exact hrnk_init z.val z.isLt,
      Nat.zero_le _, by wram_simp; simp,
      fun i hi => absurd hi (Nat.not_lt_zero i), by wram_simp; simp⟩
  · rintro yS ⟨hPS, _⟩
    obtain ⟨_, _, _, _, _, _, _, _, _, hySop, hmodS,
      p, par, rnk, repOf, acc, _, _, _, _, hySow, hacc_mem, hscan_end⟩ := hPS
    rw [List.drop_length, kruskalScan_nil, List.append_nil] at hscan_end
    wram_exec [hySop, hySow]
    refine ⟨?_, ?_, by wram_simp [hySop], ?_⟩
    · wram_simp
      have hmul : sorted.length * (16 * Nat.log 2 n + 51 + 2) =
          16 * sorted.length * Nat.log 2 n + 53 * sorted.length := by ring
      omega
    · wram_simp [Data.write_mem]
      simpa only [Finset.union_self] using
        hmodS.trans
          (Modifies.write_of_owns (base := pb) (n := 2 * n + 1 + 3 * sorted.length)
            ⟨by omega, by omega⟩ _)
    · wram_simp [Data.write_mem, hySop]
      rw [outputList_eq_iff, ← hscan_end, length_encodeEdges]
      refine ⟨Function.update_self _ _ _, ?_⟩
      exact (holdsList_of_holdsEdges hacc_mem).frame fun a ha1 ha2 => by
        rw [Function.update_of_ne (by omega)]

/-! ## End-to-End `kruskalProgram_spec` and `SimpleGraph` Specialization -/

/-- Structured `ExecWithin` specification of `kruskalCode`: halts within
`52 * m * Nat.clog 2 m + 16 * m * Nat.log 2 n + 69 * m + 7 * n + 33` instructions, preserves the
input words `Block.HoldsList 1 (encode es) yF.mem`, and writes `encodeEdges (kruskalEdges es)` as a
length-prefixed list at `yF.regs Reg.out`. -/
theorem kruskalCode_exec {w n : ℕ} (es : List (WeightedEdge n ℕ))
    (hfit : Fits w (9 * es.length + 2 * n + 4)) :
    ∃ yF : Data 26,
      ExecWithin w kruskalCode (Data.init (encode es)) yF
        (52 * es.length * Nat.clog 2 es.length + 16 * es.length * Nat.log 2 n +
          69 * es.length + 7 * n + 33) ∧
      Block.HoldsList 1 (encode es) yF.mem ∧
      yF.regs Reg.out = 3 + 6 * es.length + 2 * n ∧
      outputList yF.mem (yF.regs Reg.out) = encodeEdges (kruskalEdges es) := by
  obtain ⟨x₁, yK, yS, perm, hex_s, hex_k, hex_sort, hySz, hySo, hyS3, hySn, hySm, hySeb, hySsb,
    hySpb, hySrb, hySop, hmodS, hperm_mem, hperm_len, hperm_bound, hsorted_eq⟩ :=
    prepare_exec es hfit
  have hinit : Block.HoldsList 1 (encode es) (Data.init (encode es) : Data 26).mem :=
    (outputList_eq_iff.mp (outputList_init (encode es))).2
  have hlen := length_encode es
  have hyS_in : Block.HoldsList 1 (encode es) yS.mem :=
    hinit.frame fun a ha1 ha2 => Modifies.block_iff.mp hmodS a (by dsimp only; omega)
  have hyS_es : HoldsEdges 3 es yS.mem :=
    holdsEdges_frame (holdsEdges_init es) fun a ha1 ha2 =>
      Modifies.block_iff.mp hmodS a (by dsimp only; omega)
  obtain ⟨yU, hex_uf, hfrU, hmodU, hpar_init, hrnk_init⟩ :=
    ufInit_exec yS hySz hySo hySn hySpb hySrb rfl (hfit.of_le (by omega))
  have hframeU (a : ℕ) (ha : a < 3 + 6 * es.length) : yU.mem a = yS.mem a :=
    Modifies.block_iff.mp hmodU a (by dsimp only; omega)
  obtain ⟨yF, hex_scan, hmodF, hyFop, houtF⟩ :=
    kruskalScan_exec (eb := 3) (sb := 3 + 4 * es.length) (pb := 3 + 6 * es.length)
      (rb := 3 + 6 * es.length + n) (op := 3 + 6 * es.length + 2 * n)
      es (sortEdges es) perm yU (by rw [hperm_len, sortEdges_length]) hperm_bound hsorted_eq
      (by omega) (by rw [sortEdges_length]; omega) rfl (by omega)
      (hfit.of_le (by rw [sortEdges_length]; omega))
      ((hfrU zero (by decide) (by decide)).trans hySz)
      ((hfrU one (by decide) (by decide)).trans hySo)
      ((hfrU three (by decide) (by decide)).trans hyS3)
      ((hfrU nVerts (by decide) (by decide)).trans hySn)
      (by rw [sortEdges_length]; exact (hfrU mEdges (by decide) (by decide)).trans hySm)
      ((hfrU edgeBase (by decide) (by decide)).trans hySeb)
      ((hfrU permBase (by decide) (by decide)).trans hySsb)
      ((hfrU parBase (by decide) (by decide)).trans hySpb)
      ((hfrU rnkBase (by decide) (by decide)).trans hySrb)
      ((hfrU out (by decide) (by decide)).trans hySop)
      (holdsEdges_frame hyS_es fun a ha1 ha2 => hframeU a (by omega))
      (hperm_mem.frame fun a ha1 ha2 => hframeU a (by omega))
      hpar_init hrnk_init
  simp only [sortEdges_length] at hex_scan hmodF
  have hex_all : ExecWithin w kruskalCode (Data.init (encode es)) yF
      (52 * es.length * Nat.clog 2 es.length + 16 * es.length * Nat.log 2 n +
        69 * es.length + 7 * n + 33) := by
    unfold kruskalCode
    exact (hex_s.seq (hex_k.seq (hex_sort.seq (hex_uf.seq hex_scan)))).mono (by omega)
  refine ⟨yF, hex_all, ?_, hyFop, houtF⟩
  exact hyS_in.frame fun a ha1 ha2 =>
    (Modifies.block_iff.mp hmodF a (by dsimp only; omega)).trans (hframeU a (by omega))

/-- **`O(m log m + m log n + n)` Word-RAM Kruskal Minimum Spanning Forest Theorem**
([Kruskal1956]; [CLRS2009], Section 23.2, `MST-KRUSKAL`): on any weighted undirected multigraph
`es : List (WeightedEdge n ℕ)` (`m = es.length`) encoded in `State.init (encode es)` at word width
`w` satisfying `Fits w (9 * m + 2 * n + 4)` (with `∀ e ∈ es, Fits w e.weight` additionally
needed for `InputFits w (encode es)` / `Data.Bounded w` via `inputFits_encode`), `kruskalProgram`
halts within `52 * m * Nat.clog 2 m + 16 * m * Nat.log 2 n + 69 * m + 7 * n + 34` instructions
and outputs `encodeEdges (kruskalEdges es)` via `ExecutesList`, where `kruskalEdges es` is a
minimum-weight spanning forest of `es` (`kruskalEdges_isMinSpanningForest`), a minimum spanning
tree when `(edgePartition es).numComponents = 1` (`kruskalEdges_isMinSpanningTree`), and
`encodeEdges` is injective (`encodeEdges_injective`). -/
theorem kruskalProgram_spec {w n : ℕ} (es : List (WeightedEdge n ℕ))
    (hfit : Fits w (9 * es.length + 2 * n + 4)) :
    ∃ steps : ℕ,
      ExecutesList w kruskalProgram (.init (encode es)) (encodeEdges (kruskalEdges es)) steps ∧
      steps ≤ 52 * es.length * Nat.clog 2 es.length + 16 * es.length * Nat.log 2 n +
        69 * es.length + 7 * n + 34 ∧
      IsMinSpanningForest es (kruskalEdges es) := by
  obtain ⟨yF, ⟨t_exact, ht_le, hex_code⟩, _, hyFop, houtF⟩ := kruskalCode_exec es hfit
  have hlen_le : (kruskalEdges es).length ≤ es.length :=
    (kruskalScan_sublist _ _).length_le.trans (sortEdges_length es).le
  have hfit_out : Fits w (yF.regs Reg.out + (outputList yF.mem (yF.regs Reg.out)).length) := by
    rw [houtF, hyFop, length_encodeEdges]; exact hfit.of_le (by omega)
  have hex_list : ExecutesList w kruskalProgram (.init (encode es))
      (encodeEdges (kruskalEdges es)) (t_exact + 1) := by
    rw [kruskalProgram, ← houtF]
    exact hex_code.executesList Reg.out hfit_out
  exact ⟨t_exact + 1, hex_list, by omega, kruskalEdges_isMinSpanningForest es⟩

/-- **`SimpleGraph (Fin n)` Specialization of Word-RAM Kruskal**: on the pre-encoded canonical
`|E|`-edge list `encode (graphEdges G wt)` (`|E| = G.edgeFinset.card`) of `G : SimpleGraph (Fin n)`
weighted by `wt : Sym2 (Fin n) → ℕ`, at word width `w` satisfying `Fits w (9 * |E| + 2 * n + 4)`
(with `∀ e ∈ graphEdges G wt, Fits w e.weight` additionally needed for `InputFits` /
`Data.Bounded w` via `inputFits_encode`), `kruskalProgram` halts within
`52 * |E| * Nat.clog 2 |E| + 16 * |E| * Nat.log 2 n + 69 * |E| + 7 * n + 34` instructions
outputting `encodeEdges (kruskalGraph G wt)`, whose spanned simple graph is a minimum spanning tree
of `G` when `G.Connected`. -/
theorem kruskalProgram_graphEdges_spec {w n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (wt : Sym2 (Fin n) → ℕ)
    (hfit : Fits w (9 * G.edgeFinset.card + 2 * n + 4)) :
    ∃ steps : ℕ,
      ExecutesList w kruskalProgram (.init (encode (graphEdges G wt)))
        (encodeEdges (kruskalGraph G wt)) steps ∧
      steps ≤ 52 * G.edgeFinset.card * Nat.clog 2 G.edgeFinset.card +
        16 * G.edgeFinset.card * Nat.log 2 n + 69 * G.edgeFinset.card + 7 * n + 34 ∧
      (G.Connected → G.IsMST wt (toSimpleGraph (kruskalGraph G wt))) := by
  obtain ⟨steps, hex, hst, _⟩ := kruskalProgram_spec (graphEdges G wt) (by rwa [length_graphEdges])
  rw [length_graphEdges] at hst
  exact ⟨steps, hex, hst, fun hconn => kruskalGraph_isMST hconn wt⟩

end Cslib.Algorithms.WordRAM.Kruskal
