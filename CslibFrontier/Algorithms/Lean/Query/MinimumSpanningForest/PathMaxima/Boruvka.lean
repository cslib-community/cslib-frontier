/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Multigraph.MinimumSpanningForest
public import CslibFrontier.Algorithms.Lean.Query.FreeM.Tabulate
public import CslibFrontier.Algorithms.Lean.Query.Select.MinMax.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Borůvka's levels on a forest

The first half of King's path-maxima algorithm ([King1997]) runs Borůvka phases
([Khanna, Putterman and Song][KhannaPuttermanSong2026], Definition 2.8, p. 12) on a forest
`F ⊆ E` of a multigraph `ends : E → Sym2 V`, in the comparison model `FreeM (LEQuery E)`, and
keeps every level instead of contracting.

At level `l` the selected edges `S = levelSet ends F oracle l` split the ends of the edges of `F`
into *blocks*, the classes of `Joins ends S` (`ForestBoruvka.block`). In a phase each block selects
a lightest edge of `F` leaving it by a linear scan (`ForestBoruvka.phase`), and the selected edges
are added to `S`. Against an oracle comparing weights `w`, the selection is a lightest leaving
edge (`ForestBoruvka.phase_eval_eq_some`), and after `#F` phases no edge of `F` leaves a block, so
the last level joins every pair of vertices that `F` joins
(`ForestBoruvka.active_levelSet_card`, `ForestBoruvka.joins_of_active_eq_empty`).

The count rests on `F` being acyclic. The edges leaving blocks stay acyclic once each block is
contracted to a vertex, so by `Cslib.Multigraph.IsAcyclic.card_le` there are fewer of them than
blocks that they leave, and a phase makes at most twice as many comparisons as there are such
*active* blocks (`ForestBoruvka.countQueries_phase_le`). Every active block of level `l + 1`
contains two active blocks of level `l`, so their number at least halves from one level to the
next (`ForestBoruvka.two_mul_card_active_succ_le`). These blocks, with the selected edges as
parent edges, form King's full branching tree.

Borůvka steps on general multigraphs, contracting after each step, are milestone M1 of #8325.
This module keeps the blocks of every level and the edge each block selects, which the tree
needs, and bounds the
comparisons of the phases on a forest by the halving count of active blocks.

## Main definitions

* `Cslib.Query.ForestBoruvka.block`, `Cslib.Query.ForestBoruvka.blocks`,
  `Cslib.Query.ForestBoruvka.leaving`, `Cslib.Query.ForestBoruvka.active`: the blocks of a set of
  edges, the edges of `F` leaving a block, and the blocks that some edge of `F` leaves.
* `Cslib.Query.ForestBoruvka.phase`, `Cslib.Query.ForestBoruvka.levels`: a Borůvka phase, and the
  levels of `k` phases.
* `Cslib.Query.ForestBoruvka.step`, `Cslib.Query.ForestBoruvka.levelSet`: the same as functions of
  the oracle.

## Main results

* `Cslib.Query.ForestBoruvka.eval_levels_empty`,
  `Cslib.Query.ForestBoruvka.countQueries_levels_empty`: the levels and the comparisons of the
  phases.
* `Cslib.Query.ForestBoruvka.phase_eval_eq_some`,
  `Cslib.Query.ForestBoruvka.exists_phase_eval_eq_some`: a block that an edge of `F` leaves
  selects a lightest such edge.
* `Cslib.Query.ForestBoruvka.active_levelSet_card`,
  `Cslib.Query.ForestBoruvka.joins_of_active_eq_empty`: the last level joins what `F` joins.
* `Cslib.Query.ForestBoruvka.countQueries_phase_le`,
  `Cslib.Query.ForestBoruvka.two_mul_card_active_succ_le`,
  `Cslib.Query.ForestBoruvka.card_active_le`: the comparison count of a phase on a forest, and the
  halving of the active blocks.

## References

* [S. Khanna, A. Putterman and J. Song, *A Deterministic Linear Time Algorithm for Minimum
  Spanning Tree*][KhannaPuttermanSong2026], §2, p. 12.
* [V. King, *A simpler minimum spanning tree verification algorithm*][King1997]
-/

public section

namespace Cslib.Query.ForestBoruvka

open Cslib.Multigraph Finset

variable {V E : Type} [DecidableEq V] [DecidableEq E] (ends : E → Sym2 V) (F : Finset E)

/-! ### Blocks and the edges leaving them -/

/-- The ends of the edges of `F`. -/
def verts : Finset V :=
  F.biUnion fun e => (ends e).toFinset

open scoped Classical in
/-- The *block* of `x` for the edges `S`: the vertices joined to `x` by `S`, among `x` and the ends
of the edges of `F`. For `S ⊆ F` this is all vertices joined to `x` by `S`
(`Cslib.Query.ForestBoruvka.mem_block`). -/
noncomputable def block (S : Finset E) (x : V) : Finset V :=
  insert x {y ∈ verts ends F | Joins ends S x y}

/-- The blocks of the ends of the edges of `F`. -/
noncomputable def blocks (S : Finset E) : Finset (Finset V) :=
  (verts ends F).image (block ends F S)

open scoped Classical in
/-- The edges of `F` with exactly one end in `b`. -/
noncomputable def leaving (b : Finset V) : Finset E :=
  {e ∈ F | ∃ x ∈ b, ∃ y ∉ b, ends e = s(x, y)}

/-! ### Borůvka phases -/

/-- One **Borůvka phase** on `F` from the edges `S`: each block of `S` selects a lightest edge of
`F` leaving it, by a linear scan; a block that no edge of `F` leaves selects nothing. -/
noncomputable def phase (S : Finset E) : FreeM (LEQuery E) (Finset V → Option E) :=
  (fun t b => (t b).join) <$>
    FreeM.tabulateList (fun b => findMin (leaving ends F b).toList)
      (blocks ends F S).toList

/-- The edges `S` together with the edges that the blocks of `S` select. -/
private noncomputable def next (S : Finset E) (sel : Finset V → Option E) : Finset E :=
  S ∪ (blocks ends F S).biUnion fun b => (sel b).toFinset

/-- `k` **Borůvka phases** on `F` from the edges `S`: the edges `S` at the start of each phase,
with the selection that the phase makes. -/
noncomputable def levels :
    ℕ → Finset E → FreeM (LEQuery E) (List (Finset E × (Finset V → Option E)))
  | 0, _ => pure []
  | k + 1, S => do
    let sel ← phase ends F S
    let rest ← levels k (next ends F S sel)
    return (S, sel) :: rest

variable {ends F}

/-! ### Blocks -/

omit [DecidableEq E] in
private theorem mem_verts {x : V} : x ∈ verts ends F ↔ ∃ e ∈ F, x ∈ ends e := by
  simp [verts, Sym2.mem_toFinset]

omit [DecidableEq E] in
private theorem mem_verts_of_ends_eq {e : E} (he : e ∈ F) {x y : V} (h : ends e = s(x, y)) :
    x ∈ verts ends F ∧ y ∈ verts ends F :=
  ⟨mem_verts.2 ⟨e, he, by simp [h]⟩, mem_verts.2 ⟨e, he, by simp [h]⟩⟩

omit [DecidableEq E] in
/-- Distinct vertices joined by edges of `F` are ends of edges of `F`. -/
theorem mem_verts_of_joins {S : Finset E} (hS : S ⊆ F) {x y : V}
    (h : Joins ends (S : Set E) x y) (hxy : x ≠ y) : y ∈ verts ends F := by
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨b, -, e, he, hby⟩
  · exact absurd rfl hxy
  · exact (mem_verts_of_ends_eq (hS he) hby).2

omit [DecidableEq E] in
theorem mem_block {S : Finset E} (hS : S ⊆ F) {x y : V} :
    y ∈ block ends F S x ↔ Joins ends (S : Set E) x y := by
  simp only [block, mem_insert, mem_filter]
  refine ⟨?_, fun h => ?_⟩
  · rintro (rfl | ⟨-, h⟩)
    · exact Joins.refl _
    · exact h
  · by_cases hxy : x = y
    · exact Or.inl hxy.symm
    · exact Or.inr ⟨mem_verts_of_joins hS h hxy, h⟩

omit [DecidableEq E] in
theorem mem_block_self (S : Finset E) (x : V) : x ∈ block ends F S x :=
  mem_insert_self _ _

omit [DecidableEq E] in
theorem block_eq_iff {S : Finset E} (hS : S ⊆ F) {x y : V} :
    block ends F S x = block ends F S y ↔ Joins ends (S : Set E) x y := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := mem_block_self (ends := ends) (F := F) S x
    rw [h, mem_block hS] at this
    exact this.symm
  · ext z
    rw [mem_block hS, mem_block hS]
    exact ⟨h.symm.trans, h.trans⟩

omit [DecidableEq E] in
theorem eq_block_of_mem {S : Finset E} (hS : S ⊆ F) {b : Finset V}
    (hb : b ∈ blocks ends F S) {x : V} (hx : x ∈ b) : b = block ends F S x := by
  obtain ⟨z, -, rfl⟩ := mem_image.1 hb
  exact (block_eq_iff hS).2 ((mem_block hS).1 hx)

omit [DecidableEq E] in
theorem block_mem_blocks {S : Finset E} {x : V} (hx : x ∈ verts ends F) :
    block ends F S x ∈ blocks ends F S :=
  mem_image_of_mem _ hx

omit [DecidableEq V] [DecidableEq E] in
theorem mem_leaving {b : Finset V} {e : E} :
    e ∈ leaving ends F b ↔ e ∈ F ∧ ∃ x ∈ b, ∃ y ∉ b, ends e = s(x, y) := by
  simp [leaving]

omit [DecidableEq V] [DecidableEq E] in
/-- A walk along edges `T ⊆ F` from inside a set `b` of vertices to outside it uses an edge of `T`
leaving `b`. -/
theorem exists_mem_leaving {T : Set E} (hT : T ⊆ F) {b : Finset V} {x y : V}
    (h : Joins ends T x y) (hx : x ∈ b) (hy : y ∉ b) : ∃ e ∈ T, e ∈ leaving ends F b := by
  obtain ⟨e, he, hcut⟩ := h.exists_mem_edgeCut (P := (b : Set V)) hx hy
  obtain ⟨a, c, hac, ha, hc⟩ := Graph.mem_edgeCut_iff.1 hcut
  exact ⟨e, he, mem_leaving.2 ⟨hT he, a, ha, c, hc, hac⟩⟩

omit [DecidableEq E] in
/-- No edge of `S` leaves a block of `S`. -/
private theorem notMem_leaving {S : Finset E} (hS : S ⊆ F) {b : Finset V}
    (hb : b ∈ blocks ends F S) {e : E} (he : e ∈ S) : e ∉ leaving ends F b := by
  intro hl
  obtain ⟨-, x, hx, y, hy, hxy⟩ := mem_leaving.1 hl
  rw [eq_block_of_mem hS hb hx, mem_block hS] at hy
  exact hy (Joins.of_mem he hxy)

/-! ### The phases as a function of the oracle -/

omit [DecidableEq E] in
private theorem eval_phase (oracle : {ι : Type} → LEQuery E ι → ι) (S : Finset E)
    (b : Finset V) : (phase ends F S).eval oracle b =
      if b ∈ blocks ends F S then (findMin (leaving ends F b).toList).eval oracle
      else none := by
  simp only [phase, FreeM.eval_map, FreeM.eval_tabulateList, mem_toList]
  split_ifs <;> rfl

variable (ends F) in
/-- The Borůvka step against `oracle`: the edges `S` together with those its blocks select. -/
noncomputable def step (oracle : {ι : Type} → LEQuery E ι → ι) (S : Finset E) :
    Finset E :=
  next ends F S ((phase ends F S).eval oracle)

private theorem eval_levels (oracle : {ι : Type} → LEQuery E ι → ι) :
    ∀ (k : ℕ) (S : Finset E), (levels ends F k S).eval oracle =
      (List.range k).map fun l =>
        ((step ends F oracle)^[l] S,
          (phase ends F ((step ends F oracle)^[l] S)).eval oracle)
  | 0, S => rfl
  | k + 1, S => by
    simp only [levels, FreeM.eval_bind, FreeM.eval_pure, List.range_succ_eq_map,
      List.map_cons, List.map_map]
    rw [eval_levels oracle k]
    simp only [Function.iterate_zero, id_eq, Function.comp_def, Function.iterate_succ_apply]
    rfl

private theorem countQueries_levels (oracle : {ι : Type} → LEQuery E ι → ι) :
    ∀ (k : ℕ) (S : Finset E), (levels ends F k S).countQueries oracle =
      ∑ l ∈ range k, (phase ends F ((step ends F oracle)^[l] S)).countQueries oracle
  | 0, S => rfl
  | k + 1, S => by
    simp only [levels, FreeM.countQueries_bind, FreeM.countQueries_pure, add_zero]
    rw [countQueries_levels oracle k, sum_range_succ']
    simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq]
    rw [add_comm]
    rfl

omit [DecidableEq E] in
private theorem countQueries_phase (oracle : {ι : Type} → LEQuery E ι → ι) (S : Finset E) :
    (phase ends F S).countQueries oracle =
      ∑ b ∈ blocks ends F S, (#(leaving ends F b) - 1) := by
  rw [phase, FreeM.countQueries_map, FreeM.countQueries_eq_cost_one,
    FreeM.cost_tabulateList, ← sum_map_toList]
  congr 1
  refine List.map_congr_left fun b _ => ?_
  rw [← FreeM.countQueries_eq_cost_one, countQueries_findMin, length_toList]

/-! ### Selection against an oracle comparing weights -/

section Selection

variable {W : Type} [LinearOrder W] {w : E → W} {oracle : {ι : Type} → LEQuery E ι → ι}

omit [DecidableEq E] in
private theorem findMin_eval_spec (horacle : ∀ a b, oracle (.le a b) = decide (w a ≤ w b))
    {xs : List E} (hxs : xs ≠ []) :
    ∃ m, (findMin xs).eval oracle = some m ∧ m ∈ xs ∧ ∀ x ∈ xs, w m ≤ w x := by
  let _ : DecidableRel fun a b : E => w a ≤ w b := fun a b =>
    inferInstanceAs (Decidable (w a ≤ w b))
  have : Std.Total fun a b : E => w a ≤ w b := ⟨fun a b => le_total _ _⟩
  have : IsTrans E fun a b : E => w a ≤ w b := ⟨fun _ _ _ => le_trans⟩
  exact findMin_correct (fun a b => w a ≤ w b) oracle (fun a b => by rw [horacle]) hxs

omit [DecidableEq E] in
/-- Against an oracle comparing weights, a block selects a lightest edge of `F` leaving it. -/
theorem phase_eval_eq_some (horacle : ∀ a b, oracle (.le a b) = decide (w a ≤ w b))
    {S : Finset E} {b : Finset V} {e : E} (h : (phase ends F S).eval oracle b = some e) :
    b ∈ blocks ends F S ∧ e ∈ leaving ends F b ∧
      ∀ e' ∈ leaving ends F b, w e ≤ w e' := by
  rw [eval_phase] at h
  split_ifs at h with hb
  refine ⟨hb, ?_⟩
  by_cases hne : (leaving ends F b).toList = []
  · rw [hne] at h; simp at h
  obtain ⟨m, hm, hmem, hmin⟩ := findMin_eval_spec horacle hne
  rw [hm, Option.some_inj] at h
  subst h
  exact ⟨mem_toList.1 hmem, fun e' he' => hmin e' (mem_toList.2 he')⟩

omit [DecidableEq E] in
/-- Against an oracle comparing weights, a block that an edge of `F` leaves selects an edge. -/
theorem exists_phase_eval_eq_some
    (horacle : ∀ a b, oracle (.le a b) = decide (w a ≤ w b)) {S : Finset E} {b : Finset V}
    (hb : b ∈ blocks ends F S) (hne : (leaving ends F b).Nonempty) :
    ∃ e, (phase ends F S).eval oracle b = some e := by
  obtain ⟨m, hm, -⟩ := findMin_eval_spec (w := w) (oracle := oracle) horacle
    (xs := (leaving ends F b).toList) (by simpa using hne.ne_empty)
  exact ⟨m, by simp [eval_phase, hb, hm]⟩

omit [DecidableEq E] in
/-- A block that no edge of `F` leaves selects nothing. -/
private theorem phase_eval_eq_none {S : Finset E} {b : Finset V}
    (h : leaving ends F b = ∅) : (phase ends F S).eval oracle b = none := by
  rw [eval_phase]
  split_ifs <;> simp [h]

end Selection

/-! ### The levels -/

variable (ends F) in
/-- The blocks of `S` that an edge of `F` leaves. -/
noncomputable def active (S : Finset E) : Finset (Finset V) :=
  {b ∈ blocks ends F S | (leaving ends F b).Nonempty}

omit [DecidableEq E] in
theorem mem_active {S : Finset E} {b : Finset V} :
    b ∈ active ends F S ↔
      b ∈ blocks ends F S ∧ (leaving ends F b).Nonempty :=
  mem_filter

variable (ends F) in
/-- The edges at the start of level `l` of Borůvka's algorithm on `F` against `oracle`. -/
noncomputable def levelSet (oracle : {ι : Type} → LEQuery E ι → ι) (l : ℕ) : Finset E :=
  (step ends F oracle)^[l] ∅

section Levels

variable {W : Type} [LinearOrder W] {w : E → W} {oracle : {ι : Type} → LEQuery E ι → ι}

theorem mem_step {S : Finset E} {e : E} :
    e ∈ step ends F oracle S ↔
      e ∈ S ∨ ∃ b ∈ blocks ends F S, (phase ends F S).eval oracle b = some e := by
  simp [step, next]

private theorem subset_step (S : Finset E) : S ⊆ step ends F oracle S :=
  subset_union_left

private theorem step_subset (horacle : ∀ a b, oracle (.le a b) = decide (w a ≤ w b))
    {S : Finset E} (hS : S ⊆ F) : step ends F oracle S ⊆ F := by
  intro e he
  rcases mem_step.1 he with he | ⟨b, -, hb⟩
  · exact hS he
  · exact (mem_leaving.1 (phase_eval_eq_some horacle hb).2.1).1

/-- The phases from no edges against `oracle` are the levels `levelSet ends F oracle l` and
their selections. -/
theorem eval_levels_empty (oracle : {ι : Type} → LEQuery E ι → ι) (k : ℕ) :
    (levels ends F k ∅).eval oracle = (List.range k).map fun l =>
      (levelSet ends F oracle l,
        (phase ends F (levelSet ends F oracle l)).eval oracle) :=
  eval_levels oracle k ∅

/-- The comparisons of the phases from no edges are those of the phases at each level. -/
theorem countQueries_levels_empty (oracle : {ι : Type} → LEQuery E ι → ι) (k : ℕ) :
    (levels ends F k ∅).countQueries oracle = ∑ l ∈ range k,
      (phase ends F (levelSet ends F oracle l)).countQueries oracle :=
  countQueries_levels oracle k ∅

theorem levelSet_zero : levelSet ends F oracle 0 = ∅ := by
  rw [levelSet, Function.iterate_zero_apply]

theorem levelSet_succ (l : ℕ) : levelSet ends F oracle (l + 1) =
    step ends F oracle (levelSet ends F oracle l) := by
  rw [levelSet, levelSet, Function.iterate_succ_apply']

theorem levelSet_subset (horacle : ∀ a b, oracle (.le a b) = decide (w a ≤ w b))
    (l : ℕ) : levelSet ends F oracle l ⊆ F := by
  induction l with
  | zero => rw [levelSet_zero]; exact empty_subset _
  | succ l ih => rw [levelSet_succ]; exact step_subset horacle ih

theorem levelSet_mono {l l' : ℕ} (h : l ≤ l') :
    levelSet ends F oracle l ⊆ levelSet ends F oracle l' := by
  induction l', h using Nat.le_induction with
  | base => exact subset_rfl
  | succ l' _ ih => rw [levelSet_succ]; exact ih.trans (subset_step _)

/-- When no edge of `F` leaves a block of `S`, the step selects nothing. -/
private theorem step_eq_of_active_eq_empty {S : Finset E}
    (h : active ends F S = ∅) : step ends F oracle S = S := by
  refine Subset.antisymm (fun e he => ?_) (subset_step S)
  rcases mem_step.1 he with he | ⟨b, hb, hbe⟩
  · exact he
  · have hl : leaving ends F b = ∅ := by
      by_contra hne
      have : b ∈ active ends F S :=
        mem_active.2 ⟨hb, nonempty_iff_ne_empty.2 hne⟩
      simp [h] at this
    rw [phase_eval_eq_none hl] at hbe
    cases hbe

/-- When an edge of `F` leaves a block of `S`, the step adds an edge. -/
private theorem card_lt_card_step
    (horacle : ∀ a b, oracle (.le a b) = decide (w a ≤ w b)) {S : Finset E} (hS : S ⊆ F)
    (h : (active ends F S).Nonempty) : #S < #(step ends F oracle S) := by
  obtain ⟨b, hb⟩ := h
  obtain ⟨hbS, hne⟩ := mem_active.1 hb
  obtain ⟨e, he⟩ := exists_phase_eval_eq_some horacle hbS hne
  have hl := (phase_eval_eq_some horacle he).2.1
  refine card_lt_card ⟨subset_step S, fun hsub => ?_⟩
  exact notMem_leaving hS hbS (hsub (mem_step.2 (Or.inr ⟨b, hbS, he⟩))) hl

/-- After `#F` phases no edge of `F` leaves a block. -/
theorem active_levelSet_card
    (horacle : ∀ a b, oracle (.le a b) = decide (w a ≤ w b)) :
    active ends F (levelSet ends F oracle #F) = ∅ := by
  have key : ∀ l, l ≤ #(levelSet ends F oracle l) ∨
      active ends F (levelSet ends F oracle l) = ∅ := by
    intro l
    induction l with
    | zero => exact Or.inl (Nat.zero_le _)
    | succ l ih =>
      rw [levelSet_succ]
      by_cases hA : active ends F (levelSet ends F oracle l) = ∅
      · right; rwa [step_eq_of_active_eq_empty hA]
      · left
        have := card_lt_card_step horacle (levelSet_subset horacle l)
          (nonempty_iff_ne_empty.2 hA)
        have := ih.resolve_right hA
        omega
  refine (key #F).elim (fun hcard => ?_) id
  have hF : levelSet ends F oracle #F = F :=
    eq_of_subset_of_card_le (levelSet_subset horacle _) hcard
  refine filter_eq_empty_iff.2 fun b hb ⟨e, he⟩ => ?_
  rw [hF] at hb
  exact notMem_leaving subset_rfl hb (mem_leaving.1 he).1 he

omit [DecidableEq E] in
/-- When no edge of `F` leaves a block of `S ⊆ F`, the edges `S` join all vertices that `F`
joins. -/
theorem joins_of_active_eq_empty {S : Finset E} (hS : S ⊆ F)
    (h : active ends F S = ∅) {x y : V} (hxy : Joins ends (F : Set E) x y) :
    Joins ends (S : Set E) x y := by
  by_contra hn
  have hx : x ∈ verts ends F :=
    mem_verts_of_joins subset_rfl hxy.symm fun h => hn (h ▸ Joins.refl _)
  obtain ⟨e, -, he⟩ := exists_mem_leaving subset_rfl hxy (mem_block_self S x)
    (fun hy => hn ((mem_block hS).1 hy))
  have : block ends F S x ∈ active ends F S :=
    mem_active.2 ⟨block_mem_blocks hx, ⟨e, he⟩⟩
  simp [h] at this

end Levels

/-! ### Counting on a forest -/

section Counting

/-- An edge of `F` leaves at most two blocks of `S`: those of its ends. -/
private theorem card_filter_mem_leaving_le {S : Finset E} (hS : S ⊆ F) (e : E) :
    #{b ∈ blocks ends F S | e ∈ leaving ends F b} ≤ 2 := by
  calc #{b ∈ blocks ends F S | e ∈ leaving ends F b}
      ≤ #((ends e).toFinset.image (block ends F S)) := by
        refine card_le_card fun b hb => ?_
        obtain ⟨hbS, hl⟩ := mem_filter.1 hb
        obtain ⟨-, x, hx, y, -, hxy⟩ := mem_leaving.1 hl
        exact mem_image.2 ⟨x, by simp [Sym2.mem_toFinset, hxy],
          (eq_block_of_mem hS hbS hx).symm⟩
    _ ≤ #(ends e).toFinset := card_image_le
    _ ≤ 2 := by rw [Sym2.card_toFinset]; split_ifs <;> omega

variable (ends F) in
/-- The edges leaving some block of `S`. -/
private noncomputable def crossing (S : Finset E) : Finset E :=
  (blocks ends F S).biUnion (leaving ends F)

/-- **Double counting**: the edges leaving the blocks of `S`, counted once per block, are at most
twice the edges leaving some block. -/
private theorem sum_card_leaving_le {S : Finset E} (hS : S ⊆ F) :
    ∑ b ∈ blocks ends F S, #(leaving ends F b) ≤ 2 * #(crossing ends F S) := by
  classical
  have h1 : ∀ b ∈ blocks ends F S, #(leaving ends F b) =
      ∑ e ∈ crossing ends F S, if e ∈ leaving ends F b then 1 else 0 := by
    intro b hb
    have hsub : leaving ends F b ⊆ crossing ends F S := by
      unfold crossing; exact subset_biUnion_of_mem _ hb
    rw [← card_filter, filter_mem_eq_inter, inter_eq_right.2 hsub]
  rw [sum_congr rfl h1, sum_comm, mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_le_sum fun e _ => ?_
  rw [← card_filter]
  exact card_filter_mem_leaving_le hS e

/-- **The edges leaving blocks of a forest.** If `F` is acyclic, the edges leaving blocks of
`S ⊆ F` form an acyclic set once each block is contracted to a vertex, so there are fewer of them
than blocks that they leave. -/
private theorem card_crossing_le (hF : IsAcyclic ends (F : Set E)) {S : Finset E} (hS : S ⊆ F) :
    #(crossing ends F S) ≤ #(active ends F S) := by
  classical
  have hq : ∀ u v, block ends F S u = block ends F S v ↔
      Joins ends (S : Set E) u v := fun _ _ => block_eq_iff hS
  have hmem : ∀ e ∈ crossing ends F S, ∃ b ∈ blocks ends F S,
      e ∈ leaving ends F b := fun e he => by simpa [crossing] using he
  -- the ends of a crossing edge lie in blocks that it leaves
  have hX : ∀ e ∈ crossing ends F S, ∀ v ∈ (Sym2.map (block ends F S) ∘ ends) e,
      v ∈ active ends F S := by
    intro e he v hv
    obtain ⟨b, hb, hl⟩ := hmem e he
    obtain ⟨heF, x, hx, y, hy, hxy⟩ := mem_leaving.1 hl
    obtain ⟨z, hz, rfl⟩ := Sym2.mem_map.1 hv
    have hzv := (mem_verts_of_ends_eq heF hxy)
    rw [hxy, Sym2.mem_iff] at hz
    rcases hz with rfl | rfl
    · rw [← eq_block_of_mem hS hb hx]
      exact mem_active.2 ⟨hb, ⟨e, hl⟩⟩
    · refine mem_active.2 ⟨block_mem_blocks hzv.2, e, ?_⟩
      refine mem_leaving.2 ⟨heF, z, mem_block_self S z, x, fun hxz => ?_,
        hxy.trans Sym2.eq_swap⟩
      rw [eq_block_of_mem hS hb hx, mem_block hS] at hy
      exact hy ((mem_block hS).1 hxz).symm
  -- the crossing edges are acyclic in the contracted multigraph
  have hacyc : IsAcyclic (Sym2.map (block ends F S) ∘ ends)
      ((crossing ends F S : Finset E) : Set E) := by
    refine isAcyclic_iff.2 fun g hg a' b' hab' hj => ?_
    obtain ⟨b, hb, hl⟩ := hmem g hg
    obtain ⟨hgF, x, -, y, -, hxy⟩ := mem_leaving.1 hl
    have hgS : g ∉ S := fun h => notMem_leaving hS hb h hl
    rw [Function.comp_apply, hxy, Sym2.map_mk] at hab'
    have hj' : Joins (Sym2.map (block ends F S) ∘ ends)
        (((crossing ends F S : Finset E) : Set E) \ {g})
        (block ends F S x) (block ends F S y) := by
      rcases Sym2.eq_iff.1 hab' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rwa [h₁, h₂]
      · rw [h₁, h₂]; exact hj.symm
    refine isAcyclic_iff.1 hF g hgF x y hxy (((joins_map_iff hq).1 hj').mono ?_)
    rintro f (⟨hf, hfg⟩ | hf)
    · obtain ⟨b', hb', hl'⟩ := hmem f hf
      exact ⟨(mem_leaving.1 hl').1, hfg⟩
    · exact ⟨hS hf, fun h => hgS (Set.mem_singleton_iff.1 h ▸ hf)⟩
  exact (hacyc.card_le hX).trans (Nat.sub_le _ _)

variable {W : Type} [LinearOrder W] {w : E → W} {oracle : {ι : Type} → LEQuery E ι → ι}

omit [DecidableEq E] in
/-- **A Borůvka phase on a forest is cheap**: it makes at most twice as many comparisons as there
are blocks that an edge of `F` leaves. -/
theorem countQueries_phase_le (hF : IsAcyclic ends (F : Set E)) {S : Finset E}
    (hS : S ⊆ F) : (phase ends F S).countQueries oracle ≤ 2 * #(active ends F S) := by
  classical
  rw [countQueries_phase]
  calc ∑ b ∈ blocks ends F S, (#(leaving ends F b) - 1)
      ≤ ∑ b ∈ blocks ends F S, #(leaving ends F b) :=
        sum_le_sum fun _ _ => Nat.sub_le _ _
    _ ≤ 2 * #(crossing ends F S) := sum_card_leaving_le hS
    _ ≤ 2 * #(active ends F S) := Nat.mul_le_mul_left 2 (card_crossing_le hF hS)

/-- **Halving**: every block of level `l + 1` that an edge of `F` leaves contains at least two
such blocks of level `l`. -/
theorem two_mul_card_active_succ_le
    (horacle : ∀ a b, oracle (.le a b) = decide (w a ≤ w b)) (l : ℕ) :
    2 * #(active ends F (levelSet ends F oracle (l + 1))) ≤
      #(active ends F (levelSet ends F oracle l)) := by
  classical
  set S := levelSet ends F oracle l
  set S' := levelSet ends F oracle (l + 1)
  have hS : S ⊆ F := levelSet_subset horacle l
  have hS' : S' ⊆ F := levelSet_subset horacle (l + 1)
  have hSS' : (S : Set E) ⊆ S' := by
    simp only [S', levelSet_succ]; exact coe_subset.2 (subset_step _)
  let fiber : Finset V → Finset (Finset V) := fun B => {b ∈ active ends F S | b ⊆ B}
  have hdisj : ((active ends F S' : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint
      fiber := by
    intro B₁ hB₁ B₂ hB₂ hne
    refine disjoint_left.2 fun b hb₁ hb₂ => hne ?_
    obtain ⟨hb, hbB₁⟩ := mem_filter.1 hb₁
    obtain ⟨z, -, rfl⟩ := mem_image.1 (mem_active.1 hb).1
    have hz := mem_block_self (ends := ends) (F := F) S z
    rw [eq_block_of_mem hS' (mem_active.1 hB₁).1 (hbB₁ hz),
      eq_block_of_mem hS' (mem_active.1 hB₂).1 ((mem_filter.1 hb₂).2 hz)]
  have htwo : ∀ B ∈ active ends F S', 2 ≤ #(fiber B) := by
    intro B hB
    obtain ⟨hBS', e, he⟩ := mem_active.1 hB
    obtain ⟨heF, x, hx, y, hy, hxy⟩ := mem_leaving.1 he
    have hB_eq := eq_block_of_mem hS' hBS' hx
    have hsub : ∀ z, Joins ends (S' : Set E) x z → z ∈ B := fun z hz => by
      rw [hB_eq, mem_block hS']; exact hz
    -- the block of `x` at level `l`
    set b₁ := block ends F S x
    have hb₁B : b₁ ⊆ B := fun z hz => hsub z (((mem_block hS).1 hz).mono hSS')
    have hb₁S : b₁ ∈ blocks ends F S :=
      block_mem_blocks (mem_verts_of_ends_eq heF hxy).1
    have hb₁ : b₁ ∈ active ends F S := mem_active.2 ⟨hb₁S, e,
      mem_leaving.2 ⟨heF, x, mem_block_self S x, y, fun h => hy (hb₁B h), hxy⟩⟩
    -- the edge that it selects, and the block at its other end
    obtain ⟨e₁, he₁⟩ := exists_phase_eval_eq_some horacle hb₁S
      (mem_active.1 hb₁).2
    obtain ⟨he₁F, x₁, hx₁, y₁, hy₁, hxy₁⟩ :=
      mem_leaving.1 (phase_eval_eq_some horacle he₁).2.1
    have he₁S' : e₁ ∈ S' := by
      simp only [S', levelSet_succ]
      exact mem_step.2 (Or.inr ⟨b₁, hb₁S, he₁⟩)
    set b₂ := block ends F S y₁
    have hb₂ : b₂ ∈ active ends F S := by
      refine mem_active.2 ⟨block_mem_blocks
        (mem_verts_of_ends_eq he₁F hxy₁).2, e₁, mem_leaving.2
          ⟨he₁F, y₁, mem_block_self S y₁, x₁, fun h => hy₁ ?_,
            hxy₁.trans Sym2.eq_swap⟩⟩
      rw [eq_block_of_mem hS hb₁S hx₁, mem_block hS]
      exact ((mem_block hS).1 h).symm
    have hb₂B : b₂ ⊆ B := by
      intro z hz
      refine hsub z ((((mem_block hS).1 hx₁).mono hSS').trans
        ((Joins.of_mem he₁S' hxy₁).trans (((mem_block hS).1 hz).mono hSS')))
    have hne : b₁ ≠ b₂ := fun h => hy₁ (h ▸ mem_block_self S y₁)
    calc 2 = #{b₁, b₂} := (card_pair hne).symm
      _ ≤ #(fiber B) := card_le_card (by
        simp [insert_subset_iff, fiber, hb₁, hb₂, hb₁B, hb₂B])
  calc 2 * #(active ends F S')
      = ∑ _B ∈ active ends F S', 2 := by rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ B ∈ active ends F S', #(fiber B) := sum_le_sum htwo
    _ = #((active ends F S').biUnion fiber) := (card_biUnion hdisj).symm
    _ ≤ #(active ends F S) := card_le_card (biUnion_subset.2 fun _ _ => filter_subset _ _)

omit [DecidableEq E] in
/-- At the first level, the blocks are the single vertices, at most two per edge of `F`. -/
theorem card_active_le (S : Finset E) : #(active ends F S) ≤ 2 * #F :=
  calc #(active ends F S) ≤ #(blocks ends F S) := card_filter_le _ _
    _ ≤ #(verts ends F) := card_image_le
    _ ≤ ∑ e ∈ F, #(ends e).toFinset := card_biUnion_le
    _ ≤ ∑ _e ∈ F, 2 := sum_le_sum fun e _ => by rw [Sym2.card_toFinset]; split_ifs <;> omega
    _ = 2 * #F := by rw [sum_const, smul_eq_mul, mul_comm]

end Counting

end Cslib.Query.ForestBoruvka
