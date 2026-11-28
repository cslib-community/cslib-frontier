/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Local
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Scores
import Mathlib.Tactic.Linarith

/-!
# Ordering a cubic multigraph by median edge scores

Give every edge of a multigraph a real *score*, and let every vertex have exactly three edges.
Each vertex then has a *median* score (`Multigraph.exists_isMedian`, from `median3`), and
listing the vertices by their medians is a layout. This file bounds the frontiers of that layout
by how the scores fall around a grid of thresholds `a, a + δ, ..., a + M δ`. A vertex
*straddles* a threshold `t` when one of its edges scores below `t` and another at least `t`
(`Multigraph.EdgeStraddles`).

**The cut of a prefix** (`Multigraph.ncard_edgeCut_le_of_isMedian`). Let `P` be a set of
vertices whose medians are at most some `m`, while the medians outside `P` are at least `m`.

* An edge leaving `P` that scores below a threshold `t ≤ m` is charged to its endpoint outside
  `P`. That endpoint straddles `t`, and it is charged at most once, since at most one of its
  three edges scores below its median.
* An edge leaving `P` that scores at least a threshold `t' > m` is charged to its endpoint
  inside `P`, again at most once. That endpoint has an edge scoring at most its median `≤ m`:
  if this edge scores below `t`, the endpoint straddles `t`; otherwise the edge scores in the
  window `[t, t')`.

So if `a + i δ ≤ m < a + (i + 1) δ`, the cut of `P` has at most

`#(vertices straddling a + i δ) + 3 #(edges scoring in the window [a + i δ, a + (i + 1) δ))`

edges. If `m` lies below the grid, or above it, the cut has at most three times as many edges
as score in the lower tail, or in the upper tail.

**The layout** (`Multigraph.exists_width_le_of_edgeScore`). Every prefix of the layout by medians
has the property above, so a single bound on the tails, the straddling vertices and the windows
bounds the width.

## Main definitions

* `Cslib.Circuits.Frontier.StraddlesOn`: scores straddle a threshold on a set.
* `Cslib.Circuits.Frontier.Multigraph.EdgeStraddles`: a vertex straddles a threshold.
* `Cslib.Circuits.Frontier.Multigraph.IsMedian`: a median of the scores of the edges at a
  vertex.

## Main results

* `Cslib.Circuits.Frontier.Multigraph.exists_isMedian`: medians exist at vertices with
  three edges.
* `Cslib.Circuits.Frontier.Multigraph.ncard_edgeCut_le_of_isMedian`: the cut of a prefix.
* `Cslib.Circuits.Frontier.Multigraph.exists_width_le_of_edgeScore`: the layout by median scores.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set

/-- Scores `score` *straddle* a threshold `t` on a set `S`: some element of `S` scores below `t`
and some element of `S` scores at least `t`. -/
def StraddlesOn {ι α : Type*} [LinearOrder α] (score : ι → α) (t : α) (S : Set ι) : Prop :=
  (∃ f ∈ S, score f < t) ∧ (∃ f ∈ S, t ≤ score f)

/-- Whether `score` straddles `t` on `S` depends only on the values of `score` on `S`. -/
theorem straddlesOn_congr {ι α : Type*} [LinearOrder α] {score score' : ι → α} {t : α}
    {S : Set ι} (h : ∀ f ∈ S, score f = score' f) :
    StraddlesOn score t S ↔ StraddlesOn score' t S :=
  and_congr (exists_congr fun f => and_congr_right fun hf => by rw [h f hf])
    (exists_congr fun g => and_congr_right fun hg => by rw [h g hg])

namespace Multigraph

variable {V E : Type*} (G : Multigraph V E) {α : Type*} [LinearOrder α]

/-- The vertex `v` *straddles* the threshold `t` under the edge scores `score`: an edge at `v`
scores below `t` and another scores at least `t`. -/
def EdgeStraddles (score : E → α) (t : α) (v : V) : Prop :=
  StraddlesOn score t (G.incidenceSet v)

/-- `m` is a *median* of the scores of the edges at `v`: at least two edges at `v` score at most
`m`, and at least two score at least `m`. -/
def IsMedian (score : E → α) (v : V) (m : α) : Prop :=
  2 ≤ {e ∈ G.incidenceSet v | score e ≤ m}.ncard ∧
    2 ≤ {e ∈ G.incidenceSet v | m ≤ score e}.ncard

variable {G}

/-- Whether `v` straddles `t` depends only on the scores of the edges at `v`. -/
theorem edgeStraddles_congr {score score' : E → α} {t : α} {v : V}
    (h : ∀ e ∈ G.incidenceSet v, score e = score' e) :
    G.EdgeStraddles score t v ↔ G.EdgeStraddles score' t v :=
  straddlesOn_congr h

/-- **Medians exist.** At a vertex with three edges, the median of their three scores is a
median. -/
theorem exists_isMedian {v : V} (hv : (G.incidenceSet v).ncard = 3) (score : E → α) :
    ∃ m, G.IsMedian score v m := by
  classical
  obtain ⟨e₀, e₁, e₂, h01, h02, h12, hs⟩ := ncard_eq_three.mp hv
  -- Counting the edges at `v` with a property.
  have hcount (p : E → Prop) [DecidablePred p] : {e ∈ G.incidenceSet v | p e}.ncard =
      (if p e₀ then 1 else 0) + (if p e₁ then 1 else 0) + (if p e₂ then 1 else 0) := by
    have : {e ∈ G.incidenceSet v | p e} = ↑(({e₀, e₁, e₂} : Finset E).filter p) :=
      Set.ext fun e => by simp [hs]
    rw [this, ncard_coe_finset, Finset.card_filter, Finset.sum_insert (by simp [h01, h02]),
      Finset.sum_insert (by simp [h12]), Finset.sum_singleton, add_assoc]
  refine ⟨median3 (score e₀) (score e₁) (score e₂), ?_⟩
  simpa only [IsMedian, hcount] using two_le_median3 (score e₀) (score e₁) (score e₂)

namespace IsMedian

variable {score : E → α} {v : V} {m : α}

/-- Some edge at `v` scores at most a median. -/
theorem exists_score_le (h : G.IsMedian score v m) :
    ∃ e ∈ G.incidenceSet v, score e ≤ m :=
  nonempty_of_ncard_ne_zero (s := {e ∈ G.incidenceSet v | score e ≤ m}) (by have := h.1; omega)

/-- Some edge at `v` scores at least a median. -/
theorem exists_le_score (h : G.IsMedian score v m) :
    ∃ e ∈ G.incidenceSet v, m ≤ score e :=
  exists_score_le (α := αᵒᵈ) (score := OrderDual.toDual ∘ score) ⟨h.2, h.1⟩

variable [Finite E]

/-- At a vertex with three edges, at most one edge scores below a median. -/
private theorem eq_of_score_lt (h : G.IsMedian score v m) (hv : (G.incidenceSet v).ncard = 3)
    {e e' : E} (he : e ∈ G.incidenceSet v) (he' : e' ∈ G.incidenceSet v) (hlt : score e < m)
    (hlt' : score e' < m) : e = e' := by
  by_contra hne
  have hsub : {f ∈ G.incidenceSet v | m ≤ score f} ⊆ G.incidenceSet v \ {e, e'} :=
    fun f ⟨hf, hmf⟩ => ⟨hf, fun h => (Set.mem_insert_iff.mp h).elim
      (fun heq => (hmf.trans_eq (congrArg score heq)).not_gt hlt)
      (fun heq => (hmf.trans_eq (congrArg score (Set.mem_singleton_iff.mp heq))).not_gt hlt')⟩
  have := h.2.trans (ncard_le_ncard hsub)
  rw [ncard_sdiff (by simp [insert_subset_iff, he, he']), ncard_pair hne, hv] at this; omega

/-- At a vertex with three edges, at most one edge scores above a median. -/
private theorem eq_of_lt_score (h : G.IsMedian score v m) (hv : (G.incidenceSet v).ncard = 3)
    {e e' : E} (he : e ∈ G.incidenceSet v) (he' : e' ∈ G.incidenceSet v) (hlt : m < score e)
    (hlt' : m < score e') : e = e' :=
  eq_of_score_lt (α := αᵒᵈ) (score := OrderDual.toDual ∘ score) ⟨h.2, h.1⟩ hv he he' hlt hlt'

end IsMedian

/-! ### The cut of a prefix -/

section Cut

/-- An edge leaving `P` has an endpoint outside `P`. -/
private theorem exists_notMem_of_mem_edgeCut {P : Set V} [DecidablePred (· ∈ P)] {e : E}
    (he : e ∈ G.edgeCut P) :
    (if G.src e ∈ P then G.tgt e else G.src e) ∉ P ∧
      e ∈ G.incidenceSet (if G.src e ∈ P then G.tgt e else G.src e) := by
  rw [mem_edgeCut] at he
  split_ifs with h
  · exact ⟨fun h' => he (iff_of_true h h'), Or.inr rfl⟩
  · exact ⟨h, Or.inl rfl⟩

/-- An edge leaving `P` has an endpoint inside `P`. -/
private theorem exists_mem_of_mem_edgeCut {P : Set V} [DecidablePred (· ∈ P)] {e : E}
    (he : e ∈ G.edgeCut P) :
    (if G.src e ∈ P then G.src e else G.tgt e) ∈ P ∧
      e ∈ G.incidenceSet (if G.src e ∈ P then G.src e else G.tgt e) := by
  rw [mem_edgeCut] at he
  split_ifs with h
  · exact ⟨h, Or.inl rfl⟩
  · exact ⟨by tauto, Or.inr rfl⟩

variable [Finite E] {score : E → α} {med : V → α} {P : Set V} {m : α}

/-- Every edge is counted below `t`, between `t` and `t'`, or from `t'` on. -/
private theorem ncard_le_add_add (F : Set E) (score : E → α) (t t' : α) :
    F.ncard ≤ {e ∈ F | score e < t}.ncard + {e ∈ F | t ≤ score e ∧ score e < t'}.ncard +
      {e ∈ F | t' ≤ score e}.ncard := by
  refine (ncard_le_ncard (t := {e ∈ F | score e < t} ∪
      {e ∈ F | t ≤ score e ∧ score e < t'} ∪ {e ∈ F | t' ≤ score e}) fun e he => ?_).trans
    ((ncard_union_le _ _).trans (Nat.add_le_add_right (ncard_union_le _ _) _))
  by_cases h₁ : score e < t
  · exact Or.inl (Or.inl ⟨he, h₁⟩)
  by_cases h₂ : score e < t'
  · exact Or.inl (Or.inr ⟨he, not_lt.mp h₁, h₂⟩)
  · exact Or.inr ⟨he, not_lt.mp h₂⟩

/-- **Charging low edges.** If the medians outside `P` are at least `m`, the edges leaving `P`
that score below a threshold `t ≤ m` are no more than the vertices outside `P` that straddle
`t`. -/
private theorem ncard_edgeCut_score_lt_le [Finite V] (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    (hmed : ∀ v, G.IsMedian score v (med v)) (hPc : ∀ v ∉ P, m ≤ med v) {t : α}
    (ht : t ≤ m) :
    {e ∈ G.edgeCut P | score e < t}.ncard ≤ {v | v ∉ P ∧ G.EdgeStraddles score t v}.ncard := by
  classical
  refine ncard_le_ncard_of_injOn (fun e => if G.src e ∈ P then G.tgt e else G.src e) ?_ ?_
  · rintro e ⟨he, hlt⟩
    obtain ⟨hv, hev⟩ := exists_notMem_of_mem_edgeCut he
    obtain ⟨e', he', hle⟩ := (hmed _).exists_le_score
    exact ⟨hv, ⟨e, hev, hlt⟩, ⟨e', he', ht.trans ((hPc _ hv).trans hle)⟩⟩
  · rintro e ⟨he, hlt⟩ e' ⟨he', hlt'⟩ heq
    obtain ⟨hv, hev⟩ := exists_notMem_of_mem_edgeCut he
    dsimp only at heq
    exact (hmed _).eq_of_score_lt (h3 _) hev (heq ▸ (exists_notMem_of_mem_edgeCut he').2)
      (hlt.trans_le (ht.trans (hPc _ hv))) (hlt'.trans_le (ht.trans (hPc _ hv)))

/-- **Charging high edges.** If the medians inside `P` are at most `m`, the edges leaving `P`
that score at least a threshold `t > m` are no more than the vertices inside `P` with an edge
scoring at least `t`. -/
private theorem ncard_edgeCut_le_score_le [Finite V] (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    (hmed : ∀ v, G.IsMedian score v (med v)) (hP : ∀ u ∈ P, med u ≤ m) {t : α}
    (ht : m < t) :
    {e ∈ G.edgeCut P | t ≤ score e}.ncard ≤
      {u | u ∈ P ∧ ∃ e ∈ G.incidenceSet u, t ≤ score e}.ncard := by
  classical
  refine ncard_le_ncard_of_injOn (fun e => if G.src e ∈ P then G.src e else G.tgt e) ?_ ?_
  · rintro e ⟨he, hle⟩
    obtain ⟨hu, heu⟩ := exists_mem_of_mem_edgeCut he
    exact ⟨hu, e, heu, hle⟩
  · rintro e ⟨he, hle⟩ e' ⟨he', hle'⟩ heq
    obtain ⟨hu, heu⟩ := exists_mem_of_mem_edgeCut he
    dsimp only at heq
    exact (hmed _).eq_of_lt_score (h3 _) heu (heq ▸ (exists_mem_of_mem_edgeCut he').2)
      (((hP _ hu).trans_lt ht).trans_le hle) (((hP _ hu).trans_lt ht).trans_le hle')

/-- The endpoints of a set of edges number at most twice the edges. -/
theorem ncard_endpoints_le (F : Set E) :
    {w | ∃ e ∈ F, G.src e = w ∨ G.tgt e = w}.ncard ≤ 2 * F.ncard := by
  refine (ncard_le_ncard (t := G.src '' F ∪ G.tgt '' F) ?_).trans
    ((ncard_union_le _ _).trans ?_)
  · rintro w ⟨e, he, rfl | rfl⟩
    exacts [Or.inl ⟨e, he, rfl⟩, Or.inr ⟨e, he, rfl⟩]
  · have := ncard_image_le (f := G.src) (s := F)
    have := ncard_image_le (f := G.tgt) (s := F)
    omega

/-- **The cut of a prefix.** Let the vertices of `P` have medians at most `m`, and the others
medians at least `m`. If three times the edges scoring in each tail, and the vertices straddling
each grid threshold plus three times the edges scoring in the following window, are at most
`B`, then at most `B` edges leave `P`. -/
theorem ncard_edgeCut_le_of_isMedian [Finite V] (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    {score : E → ℝ} {med : V → ℝ} (hmed : ∀ v, G.IsMedian score v (med v)) {P : Set V}
    {m : ℝ} (hP : ∀ u ∈ P, med u ≤ m) (hPc : ∀ v ∉ P, m ≤ med v) {a δ : ℝ} (hδ : 0 < δ)
    {M : ℕ} {B : ℝ} (low : 3 * ({e | score e < a}.ncard : ℝ) ≤ B)
    (high : 3 * ({e | a + M * δ ≤ score e}.ncard : ℝ) ≤ B)
    (mid : ∀ i < M, ({v | G.EdgeStraddles score (a + i * δ) v}.ncard : ℝ) +
      3 * ({e | a + i * δ ≤ score e ∧ score e < a + (i + 1) * δ}.ncard : ℝ) ≤ B) :
    ((G.edgeCut P).ncard : ℝ) ≤ B := by
  -- The edges leaving `P` scoring in a set lie among all the edges scoring in it.
  have hsub (p : ℝ → Prop) : {e ∈ G.edgeCut P | p (score e)}.ncard ≤ {e | p (score e)}.ncard :=
    ncard_le_ncard fun e he => he.2
  -- The empty window between a threshold and itself.
  have hempty (t : ℝ) : {e ∈ G.edgeCut P | t ≤ score e ∧ score e < t}.ncard = 0 :=
    (ncard_eq_zero).mpr (eq_empty_of_forall_notMem fun e h => h.2.1.not_gt h.2.2)
  rcases lt_or_ge m a with hlow | hge
  · -- Below the grid: the vertices of `P` charged by high edges are endpoints of low edges.
    have hU : {u | u ∈ P ∧ ∃ e ∈ G.incidenceSet u, a ≤ score e} ⊆
        {w | ∃ e ∈ {e | score e < a}, G.src e = w ∨ G.tgt e = w} := by
      rintro u ⟨hu, -⟩
      obtain ⟨e, he, hle⟩ := (hmed u).exists_score_le
      exact ⟨e, (hle.trans (hP u hu)).trans_lt hlow, he⟩
    have := ncard_le_add_add (G.edgeCut P) score a a
    have := G.ncard_edgeCut_le_score_le h3 hmed hP hlow
    have := (ncard_le_ncard hU).trans (G.ncard_endpoints_le {e | score e < a})
    have := hsub (· < a)
    have := hempty a
    have hnat : (G.edgeCut P).ncard ≤ 3 * {e | score e < a}.ncard := by omega
    exact (by exact_mod_cast hnat : ((G.edgeCut P).ncard : ℝ) ≤ _).trans low
  set top := a + M * δ
  rcases le_or_gt top m with htop | hlt
  · -- Above the grid: the vertices outside `P` charged by low edges are endpoints of high edges.
    have hV : {v | v ∉ P ∧ G.EdgeStraddles score top v} ⊆
        {w | ∃ e ∈ {e | top ≤ score e}, G.src e = w ∨ G.tgt e = w} := by
      rintro v ⟨hv, -⟩
      obtain ⟨e, he, hle⟩ := (hmed v).exists_le_score
      exact ⟨e, htop.trans ((hPc v hv).trans hle), he⟩
    have := ncard_le_add_add (G.edgeCut P) score top top
    have := G.ncard_edgeCut_score_lt_le h3 hmed hPc htop
    have := (ncard_le_ncard hV).trans (G.ncard_endpoints_le {e | top ≤ score e})
    have := hsub (top ≤ ·)
    have := hempty top
    have hnat : (G.edgeCut P).ncard ≤ 3 * {e | top ≤ score e}.ncard := by omega
    exact (by exact_mod_cast hnat : ((G.edgeCut P).ncard : ℝ) ≤ _).trans high
  -- Inside the grid: `t = a + i δ ≤ m < a + (i + 1) δ = t'`.
  obtain ⟨i, hiM, ht, ht'⟩ := exists_grid_index hδ hge hlt
  set t := a + i * δ
  set t' := a + (i + 1) * δ
  set W := {e | t ≤ score e ∧ score e < t'}
  set S := {v | G.EdgeStraddles score t v}
  -- The vertices of `P` charged by high edges straddle `t` or are endpoints of window edges.
  have hU : {u | u ∈ P ∧ ∃ e ∈ G.incidenceSet u, t' ≤ score e} ⊆
      {u | u ∈ P ∧ G.EdgeStraddles score t u} ∪
        {w | ∃ e ∈ W, G.src e = w ∨ G.tgt e = w} := by
    rintro u ⟨hu, e, he, hle⟩
    obtain ⟨f, hf, hfle⟩ := (hmed u).exists_score_le
    by_cases hft : score f < t
    · exact Or.inl ⟨hu, ⟨f, hf, hft⟩, ⟨e, he, by linarith⟩⟩
    · exact Or.inr ⟨f, ⟨not_lt.mp hft, by linarith [hP u hu]⟩, hf⟩
  -- The straddling vertices inside and outside `P` are all the straddling vertices.
  have hS : {v | v ∉ P ∧ G.EdgeStraddles score t v}.ncard +
      {u | u ∈ P ∧ G.EdgeStraddles score t u}.ncard ≤ S.ncard := by
    rw [← ncard_union_eq (s := {v | v ∉ P ∧ G.EdgeStraddles score t v})
      (t := {v | v ∈ P ∧ G.EdgeStraddles score t v})
      (disjoint_left.mpr fun v hv hv' => hv.1 hv'.1)]
    exact ncard_le_ncard fun v hv => hv.elim (·.2) (·.2)
  have := ncard_le_add_add (G.edgeCut P) score t t'
  have := G.ncard_edgeCut_score_lt_le h3 hmed hPc ht
  have := G.ncard_edgeCut_le_score_le h3 hmed hP ht'
  have := (ncard_le_ncard hU).trans (ncard_union_le _ _)
  have := G.ncard_endpoints_le W
  have : _ ≤ W.ncard := hsub (fun x => t ≤ x ∧ x < t')
  have hnat : (G.edgeCut P).ncard ≤ S.ncard + 3 * W.ncard := by omega
  calc ((G.edgeCut P).ncard : ℝ) ≤ S.ncard + 3 * W.ncard := by exact_mod_cast hnat
    _ ≤ B := mid i hiM

end Cut

/-! ### The layout -/

/-- **The layout by median scores.** Let every vertex have three edges, score the edges, and fix
a grid `a, a + δ, ..., a + M δ`. If three times the edges scoring in each tail, and the vertices
straddling each grid threshold plus three times the edges scoring in the following window, are
at most `B`, then listing the vertices by the medians of their scores gives a layout of width at
most `B`. -/
theorem exists_width_le_of_edgeScore [Finite V] [Finite E] (h3 : ∀ v, (G.incidenceSet v).ncard = 3)
    (score : E → ℝ) {a δ : ℝ} (hδ : 0 < δ) (M : ℕ) {B : ℝ}
    (low : 3 * ({e | score e < a}.ncard : ℝ) ≤ B)
    (high : 3 * ({e | a + M * δ ≤ score e}.ncard : ℝ) ≤ B)
    (mid : ∀ i < M, ({v | G.EdgeStraddles score (a + i * δ) v}.ncard : ℝ) +
      3 * ({e | a + i * δ ≤ score e ∧ score e < a + (i + 1) * δ}.ncard : ℝ) ≤ B) :
    ∃ π : Layout V, (G.width π : ℝ) ≤ B := by
  choose med hmed using fun v => exists_isMedian (h3 v) score
  obtain ⟨π, hπ⟩ := Layout.exists_threshold med
  refine ⟨π, G.width_le_of_ncard_frontier_le π (le_trans (by positivity) low) fun t ht => ?_⟩
  obtain ⟨m, hP, hPc⟩ := hπ t ht
  exact ncard_edgeCut_le_of_isMedian h3 hmed hP hPc hδ low high mid

end Multigraph

end Cslib.Circuits.Frontier
