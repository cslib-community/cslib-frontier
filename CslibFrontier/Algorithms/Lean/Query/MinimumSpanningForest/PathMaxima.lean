/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.PathMaxima.Boruvka
public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.PathMaxima.ChainMaxima
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Path maxima in a forest with linearly many comparisons

Path maxima in a forest are a step in the proof of Theorem 4.1 of
[Khanna, Putterman and Song][KhannaPuttermanSong2026], tracked in #8325. The paper states them as
its Lemma 2.9 (§2, p. 12), which it cites from [Komlos1985] (see also [King1997]): given a forest
`F` on `n` vertices and `q` query paths specified by their endpoints, the maximum edge weight on
each query path can be determined with `O(n + q)` comparisons. The paper uses it in §3.5 (p. 22), to
learn the preferred actions of the sampled edges, and in §4 (p. 25), to find the edges that the
certificate forest does not support.

## The statement

* The forest is a set `F : Finset E` of edges of a multigraph `ends : E → Sym2 V` with
  `Cslib.Multigraph.IsAcyclic ends F`. The weights are `w : E → W` into a linear order, learned
  only through an oracle answering `decide (w a ≤ w b)` to the comparison `a ≤ b` of edges; the
  program `Cslib.Query.pathMaxima ends F qs` depends on the multigraph, the forest and the list
  `qs` of queries, never on `w`.
* The answer to a query `(u, v)` is an edge, not a weight. It is characterized by threshold
  connectivity (`Cslib.Query.pathMaxima_eq_some_iff`): `f` is the answer exactly when `f ∈ F`, the
  edges of `F` of weight at most `w f` join `u` and `v`, and those of weight less than `w f` do
  not. With distinct weights, as the paper assumes (§2, p. 11), this is the heaviest edge on the
  path of `F` between `u` and `v`. There is no path when `u = v` or `F` does not join them, and
  exactly then the answer is `none` (`Cslib.Query.pathMaxima_eq_none_iff`).
* The program makes at most `16 * #F + 5 * q` comparisons
  (`Cslib.Query.countQueries_pathMaxima_le`), which is `O(n + q)` since an acyclic `F` with its
  ends among `n` vertices has at most `n - 1` edges (`Cslib.Multigraph.IsAcyclic.card_le`). The
  count needs no distinctness of the weights.

## The algorithm

This follows King's algorithm, after [King1997]. The module proves the step along King's route; it
does not formalize [Komlos1985] or [King1997] as cited results, and their texts were not consulted.
It runs Borůvka phases on `F` (`Cslib.Query.ForestBoruvka`): the blocks of all levels, with the edge
that each block selects as its parent edge, form a full branching tree whose leaves are the
vertices. Each query `(u, v)` is split, without comparisons, at the first level `j` where `u` and
`v` share a block, into the two chains of parent edges of the blocks of `u` and of `v` below `j`.
Komlós's procedure (`Cslib.Query.chainMaxima`) answers all chains with linearly many comparisons,
because the number of blocks that hold an open query at least halves from each level to the next. A
last comparison per query picks the heavier of the two chain maxima.

The answer is right by King's reduction: the heaviest parent edge `f` on the two chains is the
heaviest edge on the path of `F`. No edge of `F` lighter than `f` leaves the block that selected
it, so the edges lighter than `f` do not join `u` and `v`. Conversely, the bottleneck edge `g` of
the path is selected at some level by a block that, since no lighter edge leaves it and `F` is
acyclic, holds exactly one of `u` and `v`; so `g` is on one of the two chains.

## Main definitions

* `Cslib.Query.pathMaxima`: path maxima by King's algorithm in `FreeM (LEQuery E)`.

## Main results

* `Cslib.Query.pathMaxima_eq_some_iff`, `Cslib.Query.pathMaxima_eq_none_iff`: correctness, by
  threshold connectivity; no answer exactly when there is no path.
* `Cslib.Query.countQueries_pathMaxima_le`: at most `16 * #F + 5 * q` comparisons.

## References

* [S. Khanna, A. Putterman and J. Song, *A Deterministic Linear Time Algorithm for Minimum
  Spanning Tree*][KhannaPuttermanSong2026], §2, Lemma 2.9, p. 12.
* [J. Komlós, *Linear verification for spanning trees*][Komlos1985]
* [V. King, *A simpler minimum spanning tree verification algorithm*][King1997]
-/

public section

namespace Cslib.Query

open Cslib.Multigraph Finset ForestBoruvka

variable {V E : Type} [DecidableEq V] [DecidableEq E] (ends : E → Sym2 V) (F : Finset E)

/-! ### King's reduction -/

section King

variable {ends F} {W : Type} [LinearOrder W] {w : E → W}

omit [DecidableEq V] [DecidableEq E] in
/-- Distinct vertices joined by a set of edges are joined only if the set is nonempty. -/
private theorem nonempty_of_joins {T : Finset E} {u v : V} (huv : u ≠ v)
    (h : Joins ends (T : Set E) u v) : T.Nonempty := by
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨b, -, e, he, -⟩
  · exact absurd rfl huv
  · exact ⟨e, he⟩

variable {oracle : {ι : Type} → LEQuery E ι → ι}

/-- **King's reduction** (after [King1997]). Let `j` be the first Borůvka level at which `u`
and `v` share a block. The heaviest parent edge `f` of the blocks of `u` and of `v` at the levels
below `j` is the heaviest edge on the path of the forest `F` between `u` and `v`: the edges of `F`
of weight at most `w f` join `u` and `v`, and those lighter than `f` do not. -/
private theorem king (hw : Function.Injective w)
    (horacle : ∀ a b, oracle (.le a b) = decide (w a ≤ w b)) (hF : IsAcyclic ends (F : Set E))
    {u v : V} (huv : u ≠ v) (hjoin : Joins ends (F : Set E) u v) {j : ℕ}
    (hat : Joins ends (levelSet ends F oracle j : Set E) u v)
    (hbefore : ∀ l < j, ¬Joins ends (levelSet ends F oracle l : Set E) u v) {f : E}
    (hf : ∃ l < j, ∃ x, (x = u ∨ x = v) ∧
      (phase ends F (levelSet ends F oracle l)).eval oracle
        (block ends F (levelSet ends F oracle l) x) = some f)
    (hmax : ∀ l < j, ∀ x, (x = u ∨ x = v) → ∀ e,
      (phase ends F (levelSet ends F oracle l)).eval oracle
        (block ends F (levelSet ends F oracle l) x) = some e → w e ≤ w f) :
    f ∈ F ∧ Joins ends {g | g ∈ F ∧ w g ≤ w f} u v ∧
      ¬Joins ends {g | g ∈ F ∧ w g < w f} u v := by
  have hsub : ∀ l, levelSet ends F oracle l ⊆ F := levelSet_subset horacle
  -- the parent edge of a block holding one of `u`, `v` and not the other is a bottleneck
  have hA : ∀ l < j, ∀ x y, (x = u ∧ y = v ∨ x = v ∧ y = u) → ∀ f',
      (phase ends F (levelSet ends F oracle l)).eval oracle
        (block ends F (levelSet ends F oracle l) x) = some f' →
      ¬Joins ends {g | g ∈ F ∧ w g < w f'} x y := by
    intro l hl x y hxy f' hsel hJ
    obtain ⟨-, -, hmin⟩ := phase_eval_eq_some horacle hsel
    by_cases hy : y ∈ block ends F (levelSet ends F oracle l) x
    · rw [mem_block (hsub l)] at hy
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hbefore l hl hy
      · exact hbefore l hl hy.symm
    · obtain ⟨g, ⟨-, hg⟩, hgl⟩ := exists_mem_leaving
        (T := {g | g ∈ F ∧ w g < w f'}) (fun g hg => hg.1) hJ (mem_block_self _ x) hy
      exact absurd (hmin g hgl) (not_le.2 hg)
  obtain ⟨l, hl, x, hx, hsel⟩ := hf
  have hfF : f ∈ F := (mem_leaving.1 (phase_eval_eq_some horacle hsel).2.1).1
  have hnot : ¬Joins ends {g | g ∈ F ∧ w g < w f} u v := by
    rcases hx with rfl | rfl
    · exact hA l hl x v (Or.inl ⟨rfl, rfl⟩) f hsel
    · exact fun h => hA l hl x u (Or.inr ⟨rfl, rfl⟩) f hsel h.symm
  -- the bottleneck edge `g`
  obtain ⟨g, hgF, hgJ, hgnot⟩ := exists_bottleneck (w := w) huv hjoin
  have hfg : w f ≤ w g := by
    by_contra hlt
    have hle : {x | x ∈ F ∧ w x ≤ w g} ⊆ {x | x ∈ F ∧ w x < w f} :=
      fun x hx => ⟨hx.1, hx.2.trans_lt (not_le.1 hlt)⟩
    exact hnot (hgJ.mono hle)
  -- `g` is the only edge of weight at most `w g` that is needed
  have hins : {x | x ∈ F ∧ w x ≤ w g} = insert g {x | x ∈ F ∧ w x < w g} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, le_iff_lt_or_eq, hw.eq_iff]
    constructor
    · rintro ⟨hx, hlt | rfl⟩
      · exact Or.inr ⟨hx, hlt⟩
      · exact Or.inl rfl
    · rintro (rfl | ⟨hx, hlt⟩)
      · exact ⟨hgF, Or.inr rfl⟩
      · exact ⟨hx, Or.inl hlt⟩
  rw [hins, joins_insert_iff] at hgJ
  obtain ⟨a, b, hab, hua, hbv⟩ := hgJ.resolve_left hgnot
  have hlt_sub : {x | x ∈ F ∧ w x < w g} ⊆ (F : Set E) \ {g} :=
    fun x hx => ⟨hx.1, fun h => (Set.mem_singleton_iff.1 h ▸ hx.2).false⟩
  -- `g` is selected at some level `i`
  have hgK : g ∈ levelSet ends F oracle #F := by
    by_contra hg
    have hJ := joins_of_active_eq_empty (hsub _)
      (active_levelSet_card horacle) (Joins.of_mem hgF hab)
    exact isAcyclic_iff.1 hF g hgF a b hab (hJ.mono (T := (F : Set E) \ {g}) fun x hx =>
      ⟨hsub _ hx, fun h => hg (Set.mem_singleton_iff.1 h ▸ hx)⟩)
  have hex : ∃ l, g ∈ levelSet ends F oracle l := ⟨_, hgK⟩
  have hfind : Nat.find hex ≠ 0 := fun h => by
    have := Nat.find_spec hex
    rw [h, levelSet_zero] at this
    simp at this
  set i := Nat.find hex - 1
  have hgi : g ∉ levelSet ends F oracle i := Nat.find_min hex (by omega)
  have hgi' : g ∈ step ends F oracle (levelSet ends F oracle i) := by
    rw [← levelSet_succ, show i + 1 = Nat.find hex by omega]
    exact Nat.find_spec hex
  obtain ⟨c, hc, hcg⟩ := (mem_step.1 hgi').resolve_left hgi
  obtain ⟨-, hgc, hcmin⟩ := phase_eval_eq_some horacle hcg
  obtain ⟨-, x₀, hx₀, y₀, hy₀, hxy₀⟩ := mem_leaving.1 hgc
  -- no edge lighter than `g` leaves the block `c`
  have hclosed : ∀ z ∈ c, ∀ z', Joins ends {x | x ∈ F ∧ w x < w g} z z' → z' ∈ c := by
    intro z hz z' hJ
    by_contra hz'
    obtain ⟨g', ⟨-, hg'⟩, hg'c⟩ := exists_mem_leaving
      (T := {x | x ∈ F ∧ w x < w g}) (fun g hg => hg.1) hJ hz hz'
    exact absurd (hcmin g' hg'c) (not_le.2 hg')
  -- `u` and `v` are not joined at level `i`, since `F` is acyclic
  have hnij : ¬Joins ends (levelSet ends F oracle i : Set E) u v := fun hJ =>
    isAcyclic_iff.1 hF g hgF a b hab ((hua.symm.mono hlt_sub).trans
      ((hJ.mono (T := (F : Set E) \ {g})
        fun x hx => ⟨hsub _ hx, fun h => hgi (Set.mem_singleton_iff.1 h ▸ hx)⟩).trans
        (hbv.symm.mono hlt_sub)))
  have hij : i < j := by
    by_contra hji
    exact hnij (hat.mono (coe_subset.2 (levelSet_mono (not_lt.1 hji))))
  -- the block `c` holds `u` or `v`, so `g` is one of the parent edges below `j`
  have hz : ∃ z, (z = u ∨ z = v) ∧ z ∈ c := by
    rcases Sym2.eq_iff.1 (hxy₀.symm.trans hab) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨u, Or.inl rfl, hclosed _ hx₀ u hua.symm⟩
    · exact ⟨v, Or.inr rfl, hclosed _ hx₀ v hbv⟩
  obtain ⟨z, hzuv, hzc⟩ := hz
  rw [eq_block_of_mem (hsub i) hc hzc] at hcg
  have hgf : w g ≤ w f := hmax i hij z hzuv g hcg
  obtain rfl : f = g := hw (le_antisymm hfg hgf)
  exact ⟨hfF, by rw [hins, joins_insert_iff]; exact Or.inr ⟨a, b, hab, hua, hbv⟩, hnot⟩

end King

/-! ### The program -/

/-- The heavier of two optional edges, by one comparison. -/
private def maxEdge : Option E → Option E → FreeM (LEQuery E) (Option E)
  | some a, some b => do return if ← LEQuery.ask a b then some b else some a
  | a, b => pure (a.or b)

/-- The level `l` of a list of Borůvka levels, `F` with no selection past the last one. -/
private def levelAt (H : List (Finset E × (Finset V → Option E))) (l : ℕ) :
    Finset E × (Finset V → Option E) :=
  H.getD l (F, fun _ => none)

open scoped Classical in
/-- The first of a list of Borůvka levels at which `u` and `v` are joined. -/
private noncomputable def mergeLevel (H : List (Finset E × (Finset V → Option E))) (u v : V) :
    ℕ :=
  H.findIdx fun p => decide (Joins ends (p.1 : Set E) u v)

open scoped Classical in
/-- The queries with distinct ends joined by `F`. -/
private noncomputable def joinedPairs (qs : List (V × V)) : List (V × V) :=
  qs.filter fun p => decide (p.1 ≠ p.2 ∧ Joins ends (F : Set E) p.1 p.2)

/-- The two chain queries of each joined query: from each end up to the level where the ends are
joined. -/
private noncomputable def chainQueries (H : List (Finset E × (Finset V → Option E)))
    (qs : List (V × V)) : List (ChainQuery V) :=
  (joinedPairs ends F qs).flatMap fun p =>
    [⟨p.1, mergeLevel ends H p.1 p.2⟩, ⟨p.2, mergeLevel ends H p.1 p.2⟩]

/-- **Path maxima in a forest** by King's algorithm (after [King1997] and [Komlos1985]). Run `#F`
Borůvka phases on the forest `F`, split each query `(u, v)` at the first level where `u` and `v`
share a block into two chain queries, answer these by Komlós's procedure
(`Cslib.Query.chainMaxima`), and compare the two answers. The result answers `(u, v)` by the
heaviest edge on the path of `F` between `u` and `v` (`Cslib.Query.pathMaxima_eq_some_iff`), and
`none` for a query that is not in `qs`, whose ends are equal, or whose ends `F` does not join. -/
noncomputable def pathMaxima (qs : List (V × V)) : FreeM (LEQuery E) (V → V → Option E) := do
  let H ← levels ends F (#F + 1) ∅
  let ans ← chainMaxima (fun l => block ends F (levelAt F H l).1) (fun l => (levelAt F H l).2)
    (chainQueries ends F H qs) (#F + 1)
  let res ← FreeM.tabulateList (fun p : V × V =>
      maxEdge (ans ⟨p.1, mergeLevel ends H p.1 p.2⟩) (ans ⟨p.2, mergeLevel ends H p.1 p.2⟩))
    (joinedPairs ends F qs)
  return fun u v => (res (u, v)).join

/-! ### Correctness and comparison count -/

section Spec

variable {ends F} {W : Type} [LinearOrder W] {w : E → W}
  {oracle : {ι : Type} → LEQuery E ι → ι}

variable (ends F) in
/-- The Borůvka levels that `pathMaxima` computes against `oracle`. -/
private noncomputable def levelsOf (oracle : {ι : Type} → LEQuery E ι → ι) :
    List (Finset E × (Finset V → Option E)) :=
  (List.range (#F + 1)).map fun l => (levelSet ends F oracle l,
    (phase ends F (levelSet ends F oracle l)).eval oracle)

private theorem levelAt_levelsOf {l : ℕ} (hl : l < #F + 1) :
    levelAt F (levelsOf ends F oracle) l = (levelSet ends F oracle l,
      (phase ends F (levelSet ends F oracle l)).eval oracle) := by
  simp [levelAt, levelsOf, List.getD_eq_getElem?_getD, hl]

private theorem levelAt_levelsOf_fst_subset
    (horacle : ∀ a b, oracle (.le a b) = decide (w a ≤ w b)) (l : ℕ) :
    (levelAt F (levelsOf ends F oracle) l).1 ⊆ F := by
  by_cases hl : l < #F + 1
  · rw [levelAt_levelsOf hl]; exact levelSet_subset horacle l
  · simp [levelAt, levelsOf, List.getD_eq_getElem?_getD, hl]

private theorem levelAt_levelsOf_fst_mono
    (horacle : ∀ a b, oracle (.le a b) = decide (w a ≤ w b)) (l : ℕ) :
    (levelAt F (levelsOf ends F oracle) l).1 ⊆
      (levelAt F (levelsOf ends F oracle) (l + 1)).1 := by
  by_cases hl : l + 1 < #F + 1
  · rw [levelAt_levelsOf hl, levelAt_levelsOf (by omega)]
    exact levelSet_mono (Nat.le_succ l)
  · have : (levelAt F (levelsOf ends F oracle) (l + 1)).1 = F := by
      simp [levelAt, levelsOf, List.getD_eq_getElem?_getD, hl]
    rw [this]
    exact levelAt_levelsOf_fst_subset horacle l

/-- The merge level of distinct vertices joined by `F`: the first level at which they are
joined, which exists since the last level joins all vertices that `F` joins. -/
private theorem mergeLevel_spec (horacle : ∀ a b, oracle (.le a b) = decide (w a ≤ w b))
    {u v : V} (huv : u ≠ v) (h : Joins ends (F : Set E) u v) :
    0 < mergeLevel ends (levelsOf ends F oracle) u v ∧
      mergeLevel ends (levelsOf ends F oracle) u v < #F + 1 ∧
      Joins ends (levelSet ends F oracle (mergeLevel ends (levelsOf ends F oracle) u v) :
        Set E) u v ∧
      ∀ l < mergeLevel ends (levelsOf ends F oracle) u v,
        ¬Joins ends (levelSet ends F oracle l : Set E) u v := by
  classical
  set j := mergeLevel ends (levelsOf ends F oracle) u v with hj
  have hlast : Joins ends (levelSet ends F oracle #F : Set E) u v :=
    joins_of_active_eq_empty (levelSet_subset horacle _)
      (active_levelSet_card horacle) h
  have hlt : j < (levelsOf ends F oracle).length := by
    refine List.findIdx_lt_length_of_exists ⟨_, List.mem_map_of_mem
      (List.mem_range.2 (Nat.lt_succ_self #F)), ?_⟩
    simpa using hlast
  have hlen : (levelsOf ends F oracle).length = #F + 1 := by simp [levelsOf]
  have hat : Joins ends (levelSet ends F oracle j : Set E) u v := by
    have h1 : (fun p : Finset E × (Finset V → Option E) => decide (Joins ends (p.1 : Set E) u v))
        (levelsOf ends F oracle)[j] = true := List.findIdx_getElem (w := hlt)
    simpa only [levelsOf, List.getElem_map, List.getElem_range, decide_eq_true_eq] using h1
  have hbefore : ∀ l < j, ¬Joins ends (levelSet ends F oracle l : Set E) u v := by
    intro l hl
    have h1 : (fun p : Finset E × (Finset V → Option E) => decide (Joins ends (p.1 : Set E) u v))
        ((levelsOf ends F oracle)[l]'(hl.trans hlt)) = false := List.not_of_lt_findIdx hl
    simpa only [levelsOf, List.getElem_map, List.getElem_range, decide_eq_false_iff_not] using h1
  refine ⟨Nat.pos_of_ne_zero fun h0 => ?_, hlen ▸ hlt, hat, hbefore⟩
  rw [h0, levelSet_zero] at hat
  exact (nonempty_of_joins huv hat).ne_empty rfl

/-- Below their merge level, the blocks of `u` and of `v` are left by an edge of `F`. -/
private theorem mem_active_of_lt_mergeLevel
    (horacle : ∀ a b, oracle (.le a b) = decide (w a ≤ w b))
    {u v x : V} (huv : u ≠ v) (h : Joins ends (F : Set E) u v) (hx : x = u ∨ x = v) {l : ℕ}
    (hl : l < mergeLevel ends (levelsOf ends F oracle) u v) :
    block ends F (levelSet ends F oracle l) x ∈
      active ends F (levelSet ends F oracle l) := by
  have hS := levelSet_subset (ends := ends) (F := F) horacle l
  have hn := (mergeLevel_spec horacle huv h).2.2.2 l hl
  obtain ⟨y, hxy, hJ, hn'⟩ : ∃ y, x ≠ y ∧ Joins ends (F : Set E) x y ∧
      ¬Joins ends (levelSet ends F oracle l : Set E) x y := by
    rcases hx with rfl | rfl
    · exact ⟨v, huv, h, hn⟩
    · exact ⟨u, huv.symm, h.symm, fun h' => hn h'.symm⟩
  obtain ⟨e, -, he⟩ := exists_mem_leaving subset_rfl hJ (mem_block_self _ x)
    (fun hy => hn' ((mem_block hS).1 hy))
  exact mem_active.2 ⟨block_mem_blocks
    (mem_verts_of_joins subset_rfl hJ.symm hxy.symm), e, he⟩

omit [DecidableEq E] in
private theorem mem_chainQueries {H : List (Finset E × (Finset V → Option E))}
    {qs : List (V × V)} {h : ChainQuery V} :
    h ∈ chainQueries ends F H qs ↔
      ∃ u v, (u, v) ∈ qs ∧ u ≠ v ∧ Joins ends (F : Set E) u v ∧
      (h.point = u ∨ h.point = v) ∧ h.level = mergeLevel ends H u v := by
  simp only [chainQueries, joinedPairs, List.mem_flatMap, List.mem_filter, List.mem_cons,
    List.not_mem_nil, or_false, decide_eq_true_eq, Prod.exists]
  constructor
  · rintro ⟨u, v, ⟨hq, huv, hj⟩, rfl | rfl⟩
    · exact ⟨u, v, hq, huv, hj, Or.inl rfl, rfl⟩
    · exact ⟨u, v, hq, huv, hj, Or.inr rfl, rfl⟩
  · rintro ⟨u, v, hq, huv, hj, hx, hl⟩
    refine ⟨u, v, ⟨hq, huv, hj⟩, ?_⟩
    rcases hx with hx | hx
    · exact Or.inl (by cases h; simp_all)
    · exact Or.inr (by cases h; simp_all)

omit [DecidableEq E] in
private theorem eval_maxEdge (horacle : ∀ a b, oracle (.le a b) = decide (w a ≤ w b))
    (a b : E) : (maxEdge (some a) (some b)).eval oracle =
      some (if w a ≤ w b then b else a) := by
  simp only [maxEdge, FreeM.eval_bind, LEQuery.eval_ask, horacle, FreeM.eval_pure]
  split_ifs <;> simp_all

omit [DecidableEq E] in
private theorem countQueries_maxEdge_le (a b : Option E) :
    (maxEdge a b).countQueries oracle ≤ 1 := by
  cases a <;> cases b <;> simp [maxEdge]

omit [DecidableEq V] [DecidableEq E] in
/-- The heaviest edge on a path is unique: two edges that both separate `u` from `v` below their
weight, and both join them up to it, are equal. -/
private theorem eq_of_isPathMax (hw : Function.Injective w) {u v : V} {f₁ f₂ : E}
    (h₁ : Joins ends {g | g ∈ F ∧ w g ≤ w f₁} u v ∧
      ¬Joins ends {g | g ∈ F ∧ w g < w f₁} u v)
    (h₂ : Joins ends {g | g ∈ F ∧ w g ≤ w f₂} u v ∧
      ¬Joins ends {g | g ∈ F ∧ w g < w f₂} u v) :
    f₁ = f₂ := by
  refine hw (le_antisymm (not_lt.1 fun hlt => h₁.2 (h₂.1.mono ?_))
    (not_lt.1 fun hlt => h₂.2 (h₁.1.mono ?_)))
  · exact fun g hg => ⟨hg.1, hg.2.trans_lt hlt⟩
  · exact fun g hg => ⟨hg.1, hg.2.trans_lt hlt⟩

/-- **Path maxima are correct**, a step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026]
(the paper's Lemma 2.9, §2, p. 12), along King's route (after [King1997] and [Komlos1985]). Against
an oracle comparing distinct weights `w`, for every query `(u, v)` of `qs`, `pathMaxima` answers
`some f` exactly when `f` is the heaviest edge on the path of the forest `F` between `u` and `v`,
stated by threshold connectivity: the edges of `F` of weight at most `w f` join `u` and `v`, and
those lighter than `f` do not. It answers `none` when `u = v` or `F` does not join them. -/
theorem pathMaxima_eq_some_iff (hw : Function.Injective w)
    (horacle : ∀ a b, oracle (.le a b) = decide (w a ≤ w b)) (hF : IsAcyclic ends (F : Set E))
    {qs : List (V × V)} {u v : V} (hq : (u, v) ∈ qs) (f : E) :
    (pathMaxima ends F qs).eval oracle u v = some f ↔
      f ∈ F ∧ Joins ends {g | g ∈ F ∧ w g ≤ w f} u v ∧
        ¬Joins ends {g | g ∈ F ∧ w g < w f} u v := by
  classical
  have hH : (levels ends F (#F + 1) ∅).eval oracle = levelsOf ends F oracle :=
    eval_levels_empty oracle _
  simp only [pathMaxima, FreeM.eval_bind, FreeM.eval_pure, FreeM.eval_tabulateList, hH]
  by_cases hgood : u ≠ v ∧ Joins ends (F : Set E) u v
  swap
  · -- no answer, and no heaviest edge
    have hnot : (u, v) ∉ joinedPairs ends F qs := by
      simpa [joinedPairs] using fun _ => by simpa using hgood
    simp only [hnot, ite_false, Option.join_none, reduceCtorEq, false_iff]
    rintro ⟨-, hle, hlt⟩
    exact hgood ⟨fun huv => hlt (huv ▸ Joins.refl _),
      hle.mono (show {g | g ∈ F ∧ w g ≤ w f} ⊆ (F : Set E) from fun g hg => hg.1)⟩
  obtain ⟨huv, hjoin⟩ := hgood
  have hmem : (u, v) ∈ joinedPairs ends F qs := by simp [joinedPairs, hq, huv, hjoin]
  simp only [hmem, ite_true, Option.join_some]
  obtain ⟨hj0, hjK, hat, hbefore⟩ := mergeLevel_spec horacle huv hjoin
  set j := mergeLevel ends (levelsOf ends F oracle) u v
  set lab : ℕ → V → Finset V := fun l => block ends F (levelAt F (levelsOf ends F oracle) l).1
  set sel : ℕ → Finset V → Option E := fun l => (levelAt F (levelsOf ends F oracle) l).2
  set cq := chainQueries ends F (levelsOf ends F oracle) qs with hcq_def
  -- the hypotheses of Komlós's procedure
  have hnest : ∀ l x y, lab l x = lab l y → lab (l + 1) x = lab (l + 1) y := by
    intro l x y hxy
    simp only [lab] at hxy ⊢
    rw [block_eq_iff (levelAt_levelsOf_fst_subset horacle l)] at hxy
    rw [block_eq_iff (levelAt_levelsOf_fst_subset horacle (l + 1))]
    exact hxy.mono (coe_subset.2 (levelAt_levelsOf_fst_mono horacle l))
  have hlabsel : ∀ l < #F + 1, ∀ x, sel l (lab l x) =
      (phase ends F (levelSet ends F oracle l)).eval oracle
        (block ends F (levelSet ends F oracle l) x) := by
    intro l hl x
    simp only [sel, lab, levelAt_levelsOf hl]
  have hK : ∀ h ∈ cq, h.level ≤ #F + 1 := by
    intro h hh
    obtain ⟨u', v', -, huv', hj', -, hl⟩ := mem_chainQueries.1 hh
    exact hl ▸ (mergeLevel_spec horacle huv' hj').2.1.le
  have hdef : ∀ h ∈ cq, ∀ l < h.level, (sel l (lab l h.point)).isSome := by
    intro h hh l hl
    obtain ⟨u', v', -, huv', hj', hx, hlev⟩ := mem_chainQueries.1 hh
    rw [hlev] at hl
    have hlK : l < #F + 1 := hl.trans (mergeLevel_spec horacle huv' hj').2.1
    obtain ⟨hb, hne⟩ := mem_active.1
      (mem_active_of_lt_mergeLevel horacle huv' hj' hx hl)
    obtain ⟨e, he⟩ := exists_phase_eval_eq_some horacle hb hne
    rw [hlabsel l hlK, he]
    rfl
  -- the two chain maxima
  have hcu : ⟨u, j⟩ ∈ cq := mem_chainQueries.2 ⟨u, v, hq, huv, hjoin, Or.inl rfl, rfl⟩
  have hcv : ⟨v, j⟩ ∈ cq := mem_chainQueries.2 ⟨u, v, hq, huv, hjoin, Or.inr rfl, rfl⟩
  obtain ⟨eu, heu, hmu⟩ := chainMaxima_correct oracle horacle hnest hK hdef hcu hj0
  obtain ⟨ev, hev, hmv⟩ := chainMaxima_correct oracle horacle hnest hK hdef hcv hj0
  simp only at heu hev hmu hmv
  rw [heu, hev, eval_maxEdge horacle]
  set fm := if w eu ≤ w ev then ev else eu
  have hfm : (fm = eu ∨ fm = ev) ∧ w eu ≤ w fm ∧ w ev ≤ w fm := by
    simp only [fm]
    split_ifs with h
    · exact ⟨Or.inr rfl, h, le_rfl⟩
    · exact ⟨Or.inl rfl, le_rfl, (not_le.1 h).le⟩
  have hspec := king hw horacle hF huv hjoin hat hbefore (f := fm) (by
      rcases hfm.1 with hfe | hfe
      · obtain ⟨l, -, hl, hsel⟩ := hmu.1
        exact ⟨l, hl, u, Or.inl rfl, by rw [← hlabsel l (by omega), hsel, hfe]⟩
      · obtain ⟨l, -, hl, hsel⟩ := hmv.1
        exact ⟨l, hl, v, Or.inr rfl, by rw [← hlabsel l (by omega), hsel, hfe]⟩)
    (by
      rintro l hl x (rfl | rfl) e he
      · rw [← hlabsel l (by omega)] at he
        exact (hmu.2 l (Nat.zero_le _) hl e he).trans hfm.2.1
      · rw [← hlabsel l (by omega)] at he
        exact (hmv.2 l (Nat.zero_le _) hl e he).trans hfm.2.2)
  refine ⟨fun h => Option.some_inj.1 h ▸ hspec, fun h => ?_⟩
  rw [eq_of_isPathMax hw hspec.2 h.2]

/-- **Unanswered queries.** Under the hypotheses of `Cslib.Query.pathMaxima_eq_some_iff`,
`pathMaxima` answers a query `(u, v)` of `qs` by `none` exactly when there is no path: `u = v`, or
the forest `F` does not join `u` and `v`. -/
theorem pathMaxima_eq_none_iff (hw : Function.Injective w)
    (horacle : ∀ a b, oracle (.le a b) = decide (w a ≤ w b)) (hF : IsAcyclic ends (F : Set E))
    {qs : List (V × V)} {u v : V} (hq : (u, v) ∈ qs) :
    (pathMaxima ends F qs).eval oracle u v = none ↔ u = v ∨ ¬Joins ends (F : Set E) u v := by
  rw [Option.eq_none_iff_forall_ne_some]
  refine ⟨fun h => ?_, fun h f hf => ?_⟩
  · by_contra hn
    push Not at hn
    obtain ⟨g, hgF, hg⟩ := exists_bottleneck (w := w) hn.1 hn.2
    exact h g ((pathMaxima_eq_some_iff hw horacle hF hq g).2 ⟨hgF, hg⟩)
  · obtain ⟨-, hle, hlt⟩ := (pathMaxima_eq_some_iff hw horacle hF hq f).1 hf
    rcases h with rfl | h
    · exact hlt (Joins.refl _)
    · exact h (hle.mono (show {g | g ∈ F ∧ w g ≤ w f} ⊆ (F : Set E) from fun g hg => hg.1))

/-- Counts that at least halve from each level to the next add up to at most twice the first. -/
private theorem sum_le_two_mul_of_halving {N : ℕ → ℕ} (hhalf : ∀ l, 2 * N (l + 1) ≤ N l) :
    ∀ d i, ∑ l ∈ range d, N (i + l) ≤ 2 * N i
  | 0, i => by simp
  | d + 1, i => by
    rw [sum_range_succ']
    have hs : ∀ l ∈ range d, N (i + (l + 1)) = N (i + 1 + l) := fun l _ => by
      rw [show i + (l + 1) = i + 1 + l by omega]
    rw [sum_congr rfl hs]
    have := sum_le_two_mul_of_halving hhalf d (i + 1)
    have := hhalf i
    simp only [add_zero]
    omega

/-- **Comparison count of path maxima**, a step in the proof of Theorem 4.1 of
[KhannaPuttermanSong2026] (the paper's Lemma 2.9, §2, p. 12), along King's route (after [King1997]
and [Komlos1985]). Against an oracle comparing weights, `pathMaxima` on a forest `F` with `q`
queries makes at most `16 * #F + 5 * q` comparisons. Since a forest on `n` vertices has fewer than
`n` edges, this is `O(n + q)`. -/
theorem countQueries_pathMaxima_le
    (horacle : ∀ a b, oracle (.le a b) = decide (w a ≤ w b)) (hF : IsAcyclic ends (F : Set E))
    (qs : List (V × V)) :
    (pathMaxima ends F qs).countQueries oracle ≤ 16 * #F + 5 * qs.length := by
  classical
  have hH : (levels ends F (#F + 1) ∅).eval oracle = levelsOf ends F oracle :=
    eval_levels_empty oracle _
  set N : ℕ → ℕ := fun l => #(active ends F (levelSet ends F oracle l))
  have hhalf : ∀ l, 2 * N (l + 1) ≤ N l := two_mul_card_active_succ_le horacle
  have hN0 : N 0 ≤ 2 * #F := card_active_le _
  -- the Borůvka phases
  have h₁ : (levels ends F (#F + 1) ∅).countQueries oracle ≤ 4 * N 0 := by
    rw [countQueries_levels_empty]
    calc ∑ l ∈ range (#F + 1),
          (phase ends F (levelSet ends F oracle l)).countQueries oracle
        ≤ ∑ l ∈ range (#F + 1), 2 * N (0 + l) := sum_le_sum fun l _ => by
          simpa using countQueries_phase_le hF (levelSet_subset horacle l)
      _ = 2 * ∑ l ∈ range (#F + 1), N (0 + l) := (mul_sum _ _ _).symm
      _ ≤ 4 * N 0 := by have := sum_le_two_mul_of_halving hhalf (#F + 1) 0; omega
  -- Komlós's procedure
  set cq := chainQueries ends F (levelsOf ends F oracle) qs with hcq_def
  have hcq : cq.length ≤ 2 * qs.length := by
    simp only [cq, chainQueries, List.length_flatMap, List.length_cons, List.length_nil,
      zero_add, List.map_const', List.sum_replicate, smul_eq_mul]
    have := List.length_filter_le (fun p : V × V => decide (p.1 ≠ p.2 ∧
      Joins ends (F : Set E) p.1 p.2)) qs
    simp only [joinedPairs] at this ⊢
    omega
  have h₂ : (chainMaxima (fun l => block ends F (levelAt F (levelsOf ends F oracle) l).1)
      (fun l => (levelAt F (levelsOf ends F oracle) l).2) cq (#F + 1)).countQueries oracle ≤
        4 * N 0 + 2 * cq.length := by
    refine countQueries_chainMaxima_le _ _ _ oracle (fun l hl => ?_) hhalf
    refine ⟨active ends F (levelSet ends F oracle l), le_rfl, fun h hh hlev => ?_⟩
    obtain ⟨u, v, -, huv, hj, hx, hlv⟩ := mem_chainQueries.1 hh
    rw [levelAt_levelsOf hl]
    exact mem_active_of_lt_mergeLevel horacle huv hj hx (by omega)
  -- the final comparisons
  have h₃ : ∀ ans : ChainQuery V → Option E,
      (FreeM.tabulateList (fun p : V × V => maxEdge (ans ⟨p.1, mergeLevel ends
        (levelsOf ends F oracle) p.1 p.2⟩) (ans ⟨p.2, mergeLevel ends (levelsOf ends F oracle)
          p.1 p.2⟩)) (joinedPairs ends F qs)).countQueries oracle ≤ qs.length := by
    intro ans
    rw [FreeM.countQueries_eq_cost_one, FreeM.cost_tabulateList]
    calc _ ≤ ((joinedPairs ends F qs).map fun _ => 1).sum :=
          List.sum_le_sum fun p _ => by
            rw [← FreeM.countQueries_eq_cost_one]; exact countQueries_maxEdge_le _ _
      _ ≤ qs.length := by
          simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_one, joinedPairs]
          exact List.length_filter_le _ _
  simp only [pathMaxima, FreeM.countQueries_bind, FreeM.countQueries_pure, add_zero, hH]
  rw [← hcq_def]
  have := h₃ ((chainMaxima (fun l => block ends F (levelAt F (levelsOf ends F oracle) l).1)
      (fun l => (levelAt F (levelsOf ends F oracle) l).2) cq (#F + 1)).eval oracle)
  omega

end Spec

end Cslib.Query
