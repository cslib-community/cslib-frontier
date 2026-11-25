/-
Copyright (c) 2026 Serge Gaspers, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Serge Gaspers, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Median
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith

/-!
# Interval bags, ranks, and cubic pathwidth to cutwidth

This file collects the basic interval-bag and label-rank utilities for the switched Gaussian sweep,
and provides the median edge-index bridge (`exists_width_le_of_intervals`) that turns any finite
interval decomposition of a cubic multigraph `G` with maximum bag size `w` into a vertex layout
of cutwidth at most `w + 1` (i.e., `cw(G) ≤ pw(G) + 2`).

**Proof of the bridge.** Suppose every vertex `v` is assigned a closed interval `[s v, e v]` in
`{0, …, T}` and every edge `a` lies inside some bag `intervalBag s e (t a)`. Assign every edge a
distinct integer score `score a = t a * (|E| + 1) + idx a`, where `idx : E ≃ Fin |E|`. Order the
vertices by their median edge score (`Multigraph.exists_isMedian`). For any threshold `m` splitting
a prefix `P` from `Pᶜ`, write `i = m / (|E| + 1)`:

* edges crossing `P` with `score a < m` inject into `intervalBag s e i \ P` via their outer
  endpoint (each `v ∉ P` has at least two edges scoring at least `m`);
* edges crossing `P` with `m < score a` inject into `intervalBag s e i ∩ P` via their inner
  endpoint (each `u ∈ P` has at least two edges scoring at most `m`);
* at most one edge has `score a = m`, since `score` is injective.

Therefore `|edgeCut P| ≤ |intervalBag s e i| + 1`. This recovers the `cw ≤ pw + 2` bound for
cubic multigraphs (even with parallel edges) in direct elementary fashion.

The rank lemmas are adapted from the MIT-licensed Lean 4 companion of [Gaspers2026]
(`doi:10.5281/zenodo.23883489`, module `CubicPathwidth.C3.Intervals`).

## Main definitions

* `Cslib.Circuits.Frontier.Switched.intervalBag`: the bag `{v | s v ≤ t ∧ t ≤ e v}`.
* `Cslib.Circuits.Frontier.Switched.rank`: the rank `#{u | y u < y v}` of a vertex label.

## Main results

* `Cslib.Circuits.Frontier.Switched.exists_width_le_of_intervals`: turning a vertex interval
  cover of a cubic multigraph into a vertex layout of width at most `maxBag + 1`.

## References

* [S. Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster
  Exponential Algorithms*][Gaspers2026]
* [F. S. Makedon and I. H. Sudborough, *On minimizing width in linear layouts*,
  Discrete Appl. Math. 23 (1989), 243–265]
-/

@[expose] public section

open Set

namespace Cslib.Circuits.Frontier.Switched

/-- The bag of vertices whose interval `[s v, e v]` contains `t`. -/
def intervalBag {V : Type*} [Fintype V] (s e : V → ℕ) (t : ℕ) : Finset V :=
  Finset.univ.filter fun v => s v ≤ t ∧ t ≤ e v

/-- A vertex belongs to `intervalBag s e t` iff `s v ≤ t ≤ e v`. -/
@[simp]
theorem mem_intervalBag {V : Type*} [Fintype V] {s e : V → ℕ} {t : ℕ} {v : V} :
    v ∈ intervalBag s e t ↔ s v ≤ t ∧ t ≤ e v := by
  simp only [intervalBag, Finset.mem_filter, Finset.mem_univ, true_and]

/-! ### Ranks of injective real labelings -/

section Rank

variable {n : ℕ}

/-- The number of vertices with label strictly below `y v`. -/
noncomputable def rank (y : Fin n → ℝ) (v : Fin n) : ℕ :=
  (Finset.univ.filter fun u => y u < y v).card

/-- Strictly smaller label implies strictly smaller rank. -/
theorem rank_lt_rank {y : Fin n → ℝ} {u v : Fin n} (h : y u < y v) :
    rank y u < rank y v := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨u, by simp [h], by simp⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.trans h

/-- For injective `y`, rank order equals label order. -/
theorem rank_lt_iff {y : Fin n → ℝ} (hy : Function.Injective y) {u v : Fin n} :
    rank y u < rank y v ↔ y u < y v := by
  constructor
  · intro h
    rcases lt_trichotomy (y u) (y v) with h' | h' | h'
    · exact h'
    · rw [hy h'] at h
      exact absurd h (lt_irrefl _)
    · exact absurd (rank_lt_rank h') (not_lt.mpr h.le)
  · exact rank_lt_rank

/-- For injective `y`, weak rank order equals weak label order. -/
theorem rank_le_iff {y : Fin n → ℝ} (hy : Function.Injective y) {u v : Fin n} :
    rank y u ≤ rank y v ↔ y u ≤ y v := by
  rw [← not_lt, ← not_lt, rank_lt_iff hy]

/-- For injective `y`, `rank y` is injective. -/
theorem rank_injective {y : Fin n → ℝ} (hy : Function.Injective y) :
    Function.Injective (rank y) := fun _ _ h =>
  hy (le_antisymm ((rank_le_iff hy).mp h.le) ((rank_le_iff hy).mp h.ge))

/-- Every rank is strictly below `n`. -/
theorem rank_lt_n (y : Fin n → ℝ) (v : Fin n) : rank y v < n := by
  classical
  have h : (Finset.univ.filter fun u => y u < y v) ⊂ Finset.univ := by
    rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
    exact ⟨v, Finset.mem_univ v, by simp⟩
  simpa only [rank, Finset.card_univ, Fintype.card_fin] using Finset.card_lt_card h

/-- Every index below `n` is realized as the rank of some vertex. -/
theorem exists_rank_eq {y : Fin n → ℝ} (hy : Function.Injective y) {i : ℕ} (hi : i < n) :
    ∃ v, rank y v = i := by
  let f : Fin n → Fin n := fun v => ⟨rank y v, rank_lt_n y v⟩
  have hf : Function.Injective f := fun _ _ h => rank_injective hy (congrArg Fin.val h)
  obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.mp hf) ⟨i, hi⟩
  exact ⟨v, congrArg Fin.val hv⟩

/-- At most one vertex has a given rank when `y` is injective. -/
theorem card_rank_eq_le {y : Fin n → ℝ} (hy : Function.Injective y) (i : ℕ) :
    (Finset.univ.filter fun v => rank y v = i).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact rank_injective hy (ha.trans hb.symm)

/-- The vertices with rank below `#{u | y u ≤ 0}` are precisely those with `y v ≤ 0`. -/
theorem rank_lt_lowerCount_iff (y : Fin n → ℝ) (v : Fin n) :
    rank y v < (Finset.univ.filter fun u => y u ≤ 0).card ↔ y v ≤ 0 := by
  classical
  constructor
  · intro h
    by_contra hv
    push Not at hv
    apply absurd h
    apply not_lt.mpr
    apply Finset.card_le_card
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    linarith
  · intro hv
    apply lt_of_lt_of_le _ (Finset.card_le_card
      (s := Finset.univ.filter fun u => y u < y v ∨ u = v) _)
    · rw [Finset.filter_or, Finset.card_union_of_disjoint]
      · simp only [rank, Finset.filter_eq', Finset.mem_univ, ite_true, Finset.card_singleton]
        omega
      · rw [Finset.disjoint_left]
        intro u hu hu'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hu'
        exact lt_irrefl _ (hu' ▸ hu)
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      rcases hu with hu | rfl
      · linarith
      · exact hv

end Rank

/-! ### Cubic pathwidth-to-cutwidth bridge -/

/-- At a vertex of degree three, two incident edges outside a set of at least two incident edges
coincide. -/
private theorem eq_of_two_le_ncard {V E : Type*} [Finite E] {G : Multigraph V E} {v : V}
    {R : E → Prop} (h2 : 2 ≤ {f ∈ G.incidenceSet v | R f}.ncard)
    (hv : (G.incidenceSet v).ncard = 3) {a b : E}
    (ha : a ∈ G.incidenceSet v) (hb : b ∈ G.incidenceSet v) (hRa : ¬ R a) (hRb : ¬ R b) :
    a = b := by
  by_contra hne
  have hsub : {f ∈ G.incidenceSet v | R f} ⊆ G.incidenceSet v \ {a, b} := by
    rintro f ⟨hf, hRf⟩
    refine ⟨hf, ?_⟩
    rintro (rfl | rfl)
    exacts [hRa hRf, hRb hRf]
  have := ncard_le_ncard hsub
  rw [ncard_sdiff (by simp [insert_subset_iff, ha, hb]), ncard_pair hne, hv] at this
  omega

/-- **From vertex intervals (pathwidth) to a vertex layout (cutwidth) on cubic multigraphs.**
If every vertex `v` carries a nonempty interval `[s v, e v] ⊆ [0, T]` such that every edge joins
two vertices whose intervals overlap inside `{0, …, T}`, and every `intervalBag s e t` (`t ≤ T`)
has cardinality at most `w`, then the cubic multigraph admits a layout of width at most `w + 1`. -/
theorem exists_width_le_of_intervals {V E : Type*} [Fintype V] [Finite E]
    (G : Multigraph V E) (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    (T : ℕ) (s e : V → ℕ) (hse : ∀ v, s v ≤ e v) (heT : ∀ v, e v ≤ T)
    (hedge : ∀ a : E, ∃ t ≤ T,
      s (G.src a) ≤ t ∧ t ≤ e (G.src a) ∧ s (G.tgt a) ≤ t ∧ t ≤ e (G.tgt a))
    {w : ℕ} (hw : ∀ t ≤ T, (intervalBag s e t).card ≤ w) :
    ∃ π : Layout V, G.width π ≤ w + 1 := by
  classical
  have : Fintype E := Fintype.ofFinite E
  have _ := hse
  choose tE htE htE_sl htE_sr htE_tl htE_tr using hedge
  let K : ℕ := Fintype.card E + 1
  have hKpos : 0 < K := Nat.succ_pos _
  let eIdx : E ≃ Fin (Fintype.card E) := Fintype.equivFin E
  let score : E → ℕ := fun a => tE a * K + (eIdx a).val
  have hscore_eq (a : E) : score a = (eIdx a).val + K * tE a := by
    dsimp only [score]; rw [add_comm, mul_comm]
  have hidx (a : E) : (eIdx a).val < K := Nat.lt_succ_of_lt (eIdx a).isLt
  have hscore_inj : Function.Injective score := fun a b hab => eIdx.injective <| Fin.ext <| by
    simpa only [hscore_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hidx _)] using
      congrArg (· % K) hab
  have hmed_exists : ∀ v, ∃ m, G.IsMedian score v m := fun v => G.exists_isMedian (h3 v) score
  choose med hmed using hmed_exists
  obtain ⟨π, hπ⟩ := Layout.exists_threshold med
  refine ⟨π, (G.width_le_iff π).2 fun t => ?_⟩
  rcases lt_or_ge t (Nat.card V) with htlt | htge
  swap
  · rw [G.frontier_of_card_le π htge, ncard_empty]
    omega
  obtain ⟨m, hP, hPc⟩ := hπ t htlt
  let P : Set V := π.initial t
  have hdiv_mem (a : E) : score a / K = tE a := by
    rw [hscore_eq, Nat.add_mul_div_left _ _ hKpos, Nat.div_eq_of_lt (hidx a), zero_add]
  have ht_le_div {a : E} {m₀ : ℕ} (h : score a ≤ m₀) : tE a ≤ m₀ / K :=
    (hdiv_mem a).symm.trans_le (Nat.div_le_div_right h)
  have hdiv_le_t {a : E} {m₀ : ℕ} (h : m₀ ≤ score a) : m₀ / K ≤ tE a :=
    (Nat.div_le_div_right h).trans_eq (hdiv_mem a)
  set i : ℕ := min (m / K) T
  have hiT : i ≤ T := min_le_right _ _
  have hm_le_i {a : E} (h : score a ≤ m) : tE a ≤ i := le_min (ht_le_div h) (htE a)
  have hi_le_m {a : E} (h : m ≤ score a) : i ≤ tE a := (min_le_left _ _).trans (hdiv_le_t h)
  -- Partition `G.edgeCut P` into `< m`, `= m`, and `> m`.
  let F_lt : Set E := {a ∈ G.edgeCut P | score a < m}
  let F_eq : Set E := {a ∈ G.edgeCut P | score a = m}
  let F_gt : Set E := {a ∈ G.edgeCut P | m < score a}
  have hpart : G.edgeCut P ⊆ F_lt ∪ F_eq ∪ F_gt := by
    intro a ha
    rcases lt_trichotomy (score a) m with h | h | h
    · exact Or.inl (Or.inl ⟨ha, h⟩)
    · exact Or.inl (Or.inr ⟨ha, h⟩)
    · exact Or.inr ⟨ha, h⟩
  have hmem_t (v : V) (a : E) (hav : a ∈ G.incidenceSet v) : s v ≤ tE a ∧ tE a ≤ e v := by
    rcases hav with rfl | rfl
    · exact ⟨htE_sl a, htE_sr a⟩
    · exact ⟨htE_tl a, htE_tr a⟩
  -- `F_eq` has at most one element by injectivity of `score`.
  have hFeq : F_eq.ncard ≤ 1 := by
    rw [ncard_le_one_iff]
    rintro a b ⟨_, ha⟩ ⟨_, hb⟩
    exact hscore_inj (ha.trans hb.symm)
  -- `F_lt` injects into `(intervalBag s e i : Set V) \ P`.
  let outEnd : E → V := fun a => if G.src a ∈ P then G.tgt a else G.src a
  have houtEnd {a : E} (ha : a ∈ G.edgeCut P) : outEnd a ∉ P ∧ a ∈ G.incidenceSet (outEnd a) := by
    rw [Multigraph.mem_edgeCut] at ha
    dsimp only [outEnd]
    split_ifs with h
    · exact ⟨fun h' => ha (iff_of_true h h'), Or.inr rfl⟩
    · exact ⟨h, Or.inl rfl⟩
  have hFlt : F_lt.ncard ≤ ((intervalBag s e i : Set V) \ P).ncard := by
    refine ncard_le_ncard_of_injOn outEnd ?_ ?_
    · rintro a ⟨ha, hlt⟩
      obtain ⟨hvP, hav⟩ := houtEnd ha
      obtain ⟨a', ha', hle'⟩ := (hmed (outEnd a)).exists_le_score
      have h1 : tE a ≤ i := hm_le_i hlt.le
      have h2 : i ≤ tE a' := hi_le_m ((hPc _ hvP).trans hle')
      have hs1 := (hmem_t _ a hav).1
      have he2 := (hmem_t _ a' ha').2
      exact ⟨mem_intervalBag.2 ⟨by omega, by omega⟩, hvP⟩
    · rintro a ⟨ha, hlt⟩ b ⟨hb, hlt'⟩ heq
      obtain ⟨hvP, hav⟩ := houtEnd ha
      obtain ⟨_, hbv⟩ := houtEnd hb
      rw [← heq] at hbv
      exact eq_of_two_le_ncard (hmed (outEnd a)).2 (h3 _) hav hbv
        (hlt.trans_le (hPc _ hvP)).not_ge (hlt'.trans_le (hPc _ hvP)).not_ge
  -- `F_gt` injects into `(intervalBag s e i : Set V) ∩ P`.
  let inEnd : E → V := fun a => if G.src a ∈ P then G.src a else G.tgt a
  have hinEnd {a : E} (ha : a ∈ G.edgeCut P) : inEnd a ∈ P ∧ a ∈ G.incidenceSet (inEnd a) := by
    rw [Multigraph.mem_edgeCut] at ha
    dsimp only [inEnd]
    split_ifs with h
    · exact ⟨h, Or.inl rfl⟩
    · exact ⟨by tauto, Or.inr rfl⟩
  have hFgt : F_gt.ncard ≤ ((intervalBag s e i : Set V) ∩ P).ncard := by
    refine ncard_le_ncard_of_injOn inEnd ?_ ?_
    · rintro a ⟨ha, hgt⟩
      obtain ⟨huP, hau⟩ := hinEnd ha
      obtain ⟨a', ha', hle'⟩ := (hmed (inEnd a)).exists_score_le
      have h1 : tE a' ≤ i := hm_le_i (hle'.trans (hP _ huP))
      have h2 : i ≤ tE a := hi_le_m hgt.le
      have hs1 := (hmem_t _ a' ha').1
      have he2 := (hmem_t _ a hau).2
      exact ⟨mem_intervalBag.2 ⟨by omega, by omega⟩, huP⟩
    · rintro a ⟨ha, hgt⟩ b ⟨hb, hgt'⟩ heq
      obtain ⟨huP, hau⟩ := hinEnd ha
      obtain ⟨_, hbu⟩ := hinEnd hb
      rw [← heq] at hbu
      exact eq_of_two_le_ncard (hmed (inEnd a)).1 (h3 _) hau hbu
        ((hP _ huP).trans_lt hgt).not_ge ((hP _ huP).trans_lt hgt').not_ge
  -- Recombine the two disjoint parts of `intervalBag s e i`.
  have hsum : ((intervalBag s e i : Set V) \ P).ncard +
      ((intervalBag s e i : Set V) ∩ P).ncard = (intervalBag s e i).card := by
    have hdisj : Disjoint ((intervalBag s e i : Set V) \ P) ((intervalBag s e i : Set V) ∩ P) :=
      Set.disjoint_left.mpr fun _ hx hy => hx.2 hy.2
    rw [← ncard_union_eq hdisj, Set.sdiff_union_inter, ncard_coe_finset]
  have hbound : (G.edgeCut P).ncard ≤ F_lt.ncard + F_eq.ncard + F_gt.ncard :=
    (ncard_le_ncard hpart).trans
      ((ncard_union_le _ _).trans (Nat.add_le_add_right (ncard_union_le _ _) _))
  have _ := heT
  have hbag := hw i hiT
  change (G.edgeCut P).ncard ≤ w + 1
  omega

end Cslib.Circuits.Frontier.Switched
