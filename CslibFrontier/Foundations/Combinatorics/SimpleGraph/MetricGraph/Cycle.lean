/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/MetricGraph/Cycle.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Geodesic
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic.Linarith

/-!
# Cycle metric graphs and shortest cycles

Any weighted finite simple graph `W` that is not acyclic contains a cycle minimizing total edge
weight. This module establishes the existence of shortest cycles `IsShortestCycle`, defines the
arc-length parameterization `circleMap` of any cycle into `MetricGraph W`, proves that
`circleMap` of a shortest cycle is an isometric embedding of the circle of circumference `L`
(with metric `circleDist L`), and shows `circleMap` is surjective onto `MetricGraph W` whenever
`W.graph` is isomorphic to `cycleGraph (n + 3)`.

## Main definitions

* `SimpleGraph.MetricGraph.IsShortestCycle`: predicate that a cycle minimizes `walkLength W.weight`
  among all cycles in `W.graph`.
* `SimpleGraph.MetricGraph.circleDist`: geodesic distance `(s, t) ↦ min (fract ((t - s)/L) * L) ...`
  on a circle of circumference `L > 0`.
* `SimpleGraph.MetricGraph.circleMap`: arc-length periodic parameterization `ℝ → MetricGraph W` of a
  cycle `c`.

## Main results

* `SimpleGraph.MetricGraph.exists_isShortestCycle`: every non-acyclic finite weighted graph has a
  shortest cycle.
* `SimpleGraph.MetricGraph.circleMap_dist_eq_circleDist`,
  `SimpleGraph.MetricGraph.circleMap_dist_eq_of_le`: `circleMap` of a shortest cycle preserves
  `circleDist L` globally and `|s - t|` on arcs of length `≤ L / 2`.
* `SimpleGraph.MetricGraph.circleMap_surjective_of_cycleGraph`: every cycle in a graph isomorphic
  to `cycleGraph (n + 3)` parameterizes all of `MetricGraph W`.
* `SimpleGraph.MetricGraph.circleMap_local_dichotomy`: every parameter `s` lies either strictly
  inside a cycle dart or at a cycle vertex whose two incident cycle edges are distinct.
-/

public section

open scoped unitInterval

namespace SimpleGraph

namespace MetricGraph

universe u

variable {V : Type u} {W : WeightedGraph V}

/-! ### Walk lengths and shortest cycles -/

section ShortestCycle

private lemma sum_map_eq_sum_toFinset {α : Type*} [DecidableEq α] (f : α → ℝ) (l : List α)
    (hl : l.Nodup) : (l.map f).sum = ∑ x ∈ l.toFinset, f x := by
  induction l with
  | nil => simp
  | cons a xs ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.sum_cons, List.toFinset_cons, Finset.sum_insert
      (by simpa only [List.mem_toFinset] using hl.1), ih hl.2]

private lemma walkLength_perm_eq {G : SimpleGraph V} (w : Sym2 V → ℝ)
    {u₁ v₁ u₂ v₂ : V} {p₁ : G.Walk u₁ v₁} {p₂ : G.Walk u₂ v₂} (hp : p₁.edges.Perm p₂.edges) :
    walkLength w p₁ = walkLength w p₂ :=
  (hp.map w).sum_eq

private lemma weight_le_walkLength_of_mem_edges : ∀ {u v : V} (p : W.graph.Walk u v)
    {e : Sym2 V}, e ∈ p.edges → W.weight e ≤ walkLength W.weight p
  | _, _, .cons hadj q, e, he => by
    rw [Walk.edges_cons, List.mem_cons] at he
    rw [walkLength_cons]
    rcases he with rfl | he'
    · linarith [walkLength_nonneg W.weight W.weight_nonneg q]
    · have hnn : 0 ≤ W.weight s(_, _) := (W.dart_weight_pos ⟨(_, _), hadj⟩).le
      linarith [weight_le_walkLength_of_mem_edges q he']

theorem walkLength_pos_of_not_nil {u v : V} {p : W.graph.Walk u v} (hp : ¬ p.Nil) :
    0 < walkLength W.weight p := by
  cases p with
  | nil => exact absurd .nil hp
  | cons hadj q =>
    rw [walkLength_cons]
    have h1 : 0 < W.weight s(_, _) := W.dart_weight_pos ⟨(_, _), hadj⟩
    have h2 : 0 ≤ walkLength W.weight q := walkLength_nonneg W.weight W.weight_nonneg q
    linarith

theorem walkLength_take_add_drop {u v : V} (p : W.graph.Walk u v) (k : ℕ) :
    walkLength W.weight (p.take k) + walkLength W.weight (p.drop k) = walkLength W.weight p := by
  dsimp only [walkLength]
  rw [Walk.edges_take, Walk.edges_drop, ← List.sum_append, ← List.map_append, List.take_append_drop]

/-- A cycle `c` in `W.graph` is a shortest cycle if it minimizes `walkLength W.weight` among all
cycles in `W.graph`. -/
@[expose] def IsShortestCycle (W : WeightedGraph V) {v₀ : V} (c : W.graph.Walk v₀ v₀) : Prop :=
  c.IsCycle ∧ ∀ {u : V} (c' : W.graph.Walk u u), c'.IsCycle →
    walkLength W.weight c ≤ walkLength W.weight c'

theorem exists_isShortestCycle [Finite V] (hc : ¬ W.graph.IsAcyclic) :
    ∃ (v₀ : V) (c : W.graph.Walk v₀ v₀), IsShortestCycle W c := by
  classical
  obtain ⟨_⟩ := nonempty_fintype V
  let S : Set ℝ :=
    { r | ∃ (u : V) (c : W.graph.Walk u u), c.IsCycle ∧ walkLength W.weight c = r }
  have hsub : S ⊆ Set.range (fun F : Finset (Sym2 V) => ∑ e ∈ F, W.weight e) := by
    rintro r ⟨u, c, hc_cyc, rfl⟩
    refine ⟨c.edges.toFinset, ?_⟩
    exact (sum_map_eq_sum_toFinset W.weight c.edges hc_cyc.isTrail.edges_nodup).symm
  have hfin : Set.Finite S := (Set.finite_range _).subset hsub
  obtain ⟨v₁, c₁, hc₁⟩ := not_isAcyclic_iff_exists_isCycle.mp hc
  have hne : S.Nonempty := ⟨walkLength W.weight c₁, v₁, c₁, hc₁, rfl⟩
  obtain ⟨rmin, hrmin_mem, hrmin_le⟩ :=
    hfin.toFinset.exists_min_image id (hfin.toFinset_nonempty.mpr hne)
  obtain ⟨v₀, c, hc_cyc, hc_len⟩ := hfin.mem_toFinset.mp hrmin_mem
  refine ⟨v₀, c, hc_cyc, fun {u} c' hc' => ?_⟩
  rw [hc_len]
  exact hrmin_le (walkLength W.weight c') (hfin.mem_toFinset.mpr ⟨u, c', hc', rfl⟩)

end ShortestCycle

/-! ### Geodesic distance on the circle of circumference `L` -/

section CircleDist

/-- Shortest arc-length distance between `s` and `t` on a circle of circumference `L > 0`. -/
@[expose] noncomputable def circleDist (L s t : ℝ) : ℝ :=
  min (Int.fract ((t - s) / L) * L) ((1 - Int.fract ((t - s) / L)) * L)

theorem circleDist_nonneg {L : ℝ} (hL : 0 < L) (s t : ℝ) : 0 ≤ circleDist L s t :=
  le_min (mul_nonneg (Int.fract_nonneg _) hL.le)
    (mul_nonneg (sub_nonneg.mpr (Int.fract_lt_one _).le) hL.le)

theorem circleDist_le_half {L : ℝ} (_hL : 0 < L) (s t : ℝ) : circleDist L s t ≤ L / 2 := by
  dsimp only [circleDist]
  have h1 := min_le_left (Int.fract ((t - s) / L) * L) ((1 - Int.fract ((t - s) / L)) * L)
  have h2 : min (Int.fract ((t - s) / L) * L) ((1 - Int.fract ((t - s) / L)) * L) ≤
      L - Int.fract ((t - s) / L) * L :=
    (min_le_right _ _).trans_eq (by ring)
  linarith

@[simp]
theorem circleDist_self {L : ℝ} (hL : 0 < L) (s : ℝ) : circleDist L s s = 0 := by
  simp [circleDist, hL.le]

theorem circleDist_add_int_right {L : ℝ} (hL : 0 < L) (s t : ℝ) (k : ℤ) :
    circleDist L s (t + (k : ℝ) * L) = circleDist L s t := by
  have hdiv : ((t + (k : ℝ) * L) - s) / L = (t - s) / L + (k : ℝ) := by
    rw [add_sub_right_comm, add_div, mul_div_cancel_right₀ _ hL.ne']
  simp only [circleDist, hdiv, Int.fract_add_intCast]

theorem circleDist_symm {L : ℝ} (hL : 0 < L) (s t : ℝ) :
    circleDist L s t = circleDist L t s := by
  by_cases hf : Int.fract ((t - s) / L) = 0
  · obtain ⟨k, hk⟩ := Int.fract_eq_zero_iff.mp hf
    have hts : (s - t) / L = ((-k : ℤ) : ℝ) := by
      rw [← neg_sub t s, neg_div, ← hk, Int.cast_neg]
    have hf' : Int.fract ((s - t) / L) = 0 := hts ▸ Int.fract_intCast (-k)
    simp only [circleDist, hf, hf', zero_mul, sub_zero, one_mul, min_eq_left hL.le]
  · have hneg : (s - t) / L = -((t - s) / L) := by rw [← neg_sub t s, neg_div]
    simp only [circleDist, hneg, Int.fract_neg hf, sub_sub_cancel]
    exact min_comm _ _

theorem circleDist_add_int_left {L : ℝ} (hL : 0 < L) (s t : ℝ) (k : ℤ) :
    circleDist L (s + (k : ℝ) * L) t = circleDist L s t := by
  rw [circleDist_symm hL, circleDist_add_int_right hL, circleDist_symm hL]

theorem circleDist_eq_abs_of_abs_le {L : ℝ} (hL : 0 < L) {s t : ℝ} (hst : |s - t| ≤ L / 2) :
    circleDist L s t = |s - t| := by
  wlog hle : s ≤ t generalizing s t
  · rw [circleDist_symm hL, abs_sub_comm]
    exact this (abs_sub_comm s t ▸ hst) (le_of_not_ge hle)
  have hts : 0 ≤ t - s := sub_nonneg.mpr hle
  have hab : t - s ≤ L / 2 := by rwa [abs_sub_comm, abs_of_nonneg hts] at hst
  have hf : Int.fract ((t - s) / L) = (t - s) / L := Int.fract_eq_self.mpr
    ⟨div_nonneg hts hL.le, (div_lt_one hL).mpr (by linarith)⟩
  rw [circleDist, hf, div_mul_cancel₀ _ hL.ne', one_sub_mul, div_mul_cancel₀ _ hL.ne',
    abs_sub_comm, abs_of_nonneg hts]
  exact min_eq_left (by linarith)

theorem circleDist_le_abs {L : ℝ} (hL : 0 < L) (s t : ℝ) : circleDist L s t ≤ |s - t| := by
  rcases le_or_gt |s - t| (L / 2) with h | h
  · exact (circleDist_eq_abs_of_abs_le hL h).le
  · exact (circleDist_le_half hL s t).trans h.le

theorem exists_eq_add_int_mul_dist {L : ℝ} (hL : 0 < L) (s t : ℝ) :
    ∃ k : ℤ, |s - (t + (k : ℝ) * L)| = circleDist L s t := by
  let n : ℤ := ⌊(t - s) / L⌋
  have hfract : Int.fract ((t - s) / L) * L = t - (n : ℝ) * L - s := by
    dsimp only [n]
    rw [Int.fract, sub_mul, div_mul_cancel₀ _ hL.ne']
    ring
  rcases le_or_gt (Int.fract ((t - s) / L)) (1 / 2) with h | h
  · refine ⟨-n, ?_⟩
    have hcd : circleDist L s t = Int.fract ((t - s) / L) * L :=
      min_eq_left (by nlinarith)
    have heq : t + ((-n : ℤ) : ℝ) * L - s = Int.fract ((t - s) / L) * L := by
      rw [hfract, Int.cast_neg]
      ring
    rw [abs_sub_comm, heq, abs_of_nonneg (mul_nonneg (Int.fract_nonneg _) hL.le), hcd]
  · refine ⟨-(n + 1), ?_⟩
    have hcd : circleDist L s t = (1 - Int.fract ((t - s) / L)) * L :=
      min_eq_right (by nlinarith)
    have heq : s - (t + ((-(n + 1) : ℤ) : ℝ) * L) = (1 - Int.fract ((t - s) / L)) * L := by
      rw [one_sub_mul, hfract, Int.cast_neg, Int.cast_add, Int.cast_one]
      ring
    rw [heq, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr (Int.fract_lt_one _).le) hL.le), hcd]

theorem circleDist_triangle {L : ℝ} (hL : 0 < L) (r s t : ℝ) :
    circleDist L r t ≤ circleDist L r s + circleDist L s t := by
  obtain ⟨k₁, hk₁⟩ := exists_eq_add_int_mul_dist hL r s
  obtain ⟨k₂, hk₂⟩ := exists_eq_add_int_mul_dist hL (s + (k₁ : ℝ) * L) t
  have hr : circleDist L r t = circleDist L r (t + (k₂ : ℝ) * L) :=
    (circleDist_add_int_right hL r t k₂).symm
  have hs : circleDist L s t = circleDist L (s + (k₁ : ℝ) * L) t :=
    (circleDist_add_int_left hL s t k₁).symm
  rw [hr, hs, ← hk₁, ← hk₂]
  exact (circleDist_le_abs hL r (t + (k₂ : ℝ) * L)).trans (abs_sub_le _ (s + (k₁ : ℝ) * L) _)

/-- `s` is its representative `Int.fract (s / L) * L ∈ [0, L)` plus an integer multiple of `L`. -/
private lemma eq_fract_mul_add_floor_mul {L : ℝ} (hL : 0 < L) (s : ℝ) :
    s = Int.fract (s / L) * L + (⌊s / L⌋ : ℝ) * L := by
  simpa only [zsmul_eq_mul] using (Int.fract_div_mul_self_add_zsmul_eq L s hL.ne').symm

private lemma fract_mul_mem_Ico {L : ℝ} (hL : 0 < L) (x : ℝ) :
    0 ≤ Int.fract x * L ∧ Int.fract x * L < L :=
  ⟨mul_nonneg (Int.fract_nonneg _) hL.le, (mul_lt_iff_lt_one_left hL).mpr (Int.fract_lt_one _)⟩

end CircleDist

/-! ### Arc-length parameterization of walks and cycles -/

section CircleMap

/-- Arc-length parameterization of a walk `p : W.graph.Walk u v` into `MetricGraph W`, clamped at
`vertex u` for `s ≤ 0` and at `vertex v` for `walkLength W.weight p ≤ s`. -/
noncomputable def walkPoint : ∀ {u v : V}, W.graph.Walk u v → ℝ → MetricGraph W
  | u, _, .nil, _ => vertex u
  | u, _, .cons (v := b) hadj q, s =>
    let d : W.graph.Dart := ⟨(u, b), hadj⟩
    let w := W.weight d.edge
    if s ≤ w then
      let t : unitInterval :=
        ⟨max 0 (min s w) / w,
          div_nonneg (le_max_left 0 _) (W.dart_weight_pos d).le,
          (div_le_one (W.dart_weight_pos d)).mpr
            (max_le (W.dart_weight_pos d).le (min_le_right _ _))⟩
      edgePoint d t
    else
      walkPoint q (s - w)

private lemma walkPoint_cons_of_le {u b v : V} (hadj : W.graph.Adj u b) (q : W.graph.Walk b v)
    (d : W.graph.Dart) (hd : d = ⟨(u, b), hadj⟩)
    {s : ℝ} (hs0 : 0 ≤ s) (hsw : s ≤ W.weight d.edge)
    (h0 : 0 ≤ s / W.weight d.edge) (h1 : s / W.weight d.edge ≤ 1) :
    walkPoint (.cons hadj q) s = edgePoint d ⟨s / W.weight d.edge, h0, h1⟩ := by
  subst hd
  have hsw' : s ≤ W.weight s(u, b) := hsw
  dsimp only [walkPoint]
  split_ifs
  congr 1
  ext
  simp [min_eq_left hsw', max_eq_right hs0]

private lemma walkPoint_cons_mul {u b v : V} (hadj : W.graph.Adj u b) (q : W.graph.Walk b v)
    (d : W.graph.Dart) (hd : d = ⟨(u, b), hadj⟩) (t : unitInterval) :
    walkPoint (.cons hadj q) ((t : ℝ) * W.weight d.edge) = edgePoint d t := by
  have hw := W.dart_weight_pos d
  have h0 : 0 ≤ (t : ℝ) * W.weight d.edge := mul_nonneg t.property.1 hw.le
  have hle : (t : ℝ) * W.weight d.edge ≤ W.weight d.edge := mul_le_of_le_one_left hw.le t.property.2
  rw [walkPoint_cons_of_le hadj q d hd h0 hle (div_nonneg h0 hw.le) ((div_le_one hw).mpr hle)]
  congr 1
  ext
  exact mul_div_cancel_right₀ (t : ℝ) hw.ne'

private lemma walkPoint_cons_of_gt {u b v : V} (hadj : W.graph.Adj u b) (q : W.graph.Walk b v)
    (d : W.graph.Dart) (hd : d = ⟨(u, b), hadj⟩) {s : ℝ} (hs : W.weight d.edge < s) :
    walkPoint (.cons hadj q) s = walkPoint q (s - W.weight d.edge) := by
  subst hd
  have hns : ¬ s ≤ W.weight (⟨(u, b), hadj⟩ : W.graph.Dart).edge := not_le.mpr hs
  dsimp only [walkPoint]
  split_ifs
  rfl

private lemma walkPoint_cons_eq_end {u b v : V} (hadj : W.graph.Adj u b) (q : W.graph.Walk b v)
    (d : W.graph.Dart) (hd : d = ⟨(u, b), hadj⟩) {s : ℝ} (hs : s = W.weight d.edge) :
    walkPoint (.cons hadj q) s = vertex b := by
  simpa only [hs, Set.Icc.coe_one, one_mul, edgePoint_one, hd] using
    walkPoint_cons_mul hadj q d hd 1

theorem walkPoint_nonpos : ∀ {u v : V} (p : W.graph.Walk u v) {s : ℝ},
    s ≤ 0 → walkPoint p s = vertex u
  | _, _, .nil, _, _ => rfl
  | u, _, .cons (v := b) hadj q, s, hs => by
    let d : W.graph.Dart := ⟨(u, b), hadj⟩
    have hw : 0 < W.weight d.edge := W.dart_weight_pos d
    have hsw : s ≤ W.weight d.edge := hs.trans hw.le
    dsimp only [walkPoint]
    split_ifs with h
    · have h0 : (⟨max 0 (min s (W.weight d.edge)) / W.weight d.edge,
          div_nonneg (le_max_left 0 _) hw.le,
          (div_le_one hw).mpr (max_le hw.le (min_le_right _ _))⟩ : unitInterval) = 0 := by
        ext
        simp [min_eq_left hsw, max_eq_left hs]
      rw [h0, edgePoint_zero]
    · exact absurd hsw h

theorem walkPoint_ge : ∀ {u v : V} (p : W.graph.Walk u v) {s : ℝ},
    walkLength W.weight p ≤ s → walkPoint p s = vertex v
  | _, _, .nil, _, _ => rfl
  | u, v, .cons (v := b) hadj q, s, hs => by
    rw [walkLength_cons] at hs
    let d : W.graph.Dart := ⟨(u, b), hadj⟩
    have hwe : W.weight s(u, b) = W.weight d.edge := rfl
    rw [hwe] at hs
    have hq_nn : 0 ≤ walkLength W.weight q := walkLength_nonneg W.weight W.weight_nonneg q
    by_cases hsw : s ≤ W.weight d.edge
    · have hq_len : walkLength W.weight q = 0 := le_antisymm (by linarith) hq_nn
      have hq_nil : q.Nil := by
        by_contra hnn
        linarith [walkLength_pos_of_not_nil (W := W) hnn]
      cases hq_nil
      rw [walkLength_nil, add_zero] at hs
      exact walkPoint_cons_eq_end hadj .nil d rfl (le_antisymm hsw hs)
    · rw [walkPoint_cons_of_gt hadj q d rfl (lt_of_not_ge hsw)]
      exact walkPoint_ge q (by linarith)

theorem walkPoint_append_of_le : ∀ {u v w : V} (p : W.graph.Walk u v) (q : W.graph.Walk v w)
    {s : ℝ}, s ≤ walkLength W.weight p → walkPoint (p.append q) s = walkPoint p s
  | _, _, _, .nil, q, s, hs => by
    rw [walkLength_nil] at hs
    rw [Walk.nil_append, walkPoint_nonpos q hs]
    rfl
  | u, v, w, .cons (v := b) hadj p', q, s, hs => by
    rw [walkLength_cons] at hs
    have hwe : W.weight (⟨(u, b), hadj⟩ : W.graph.Dart).edge = W.weight s(u, b) := rfl
    dsimp only [Walk.cons_append, walkPoint]
    split_ifs with hsw
    · rfl
    · exact walkPoint_append_of_le p' q (by linarith)

theorem walkPoint_append_of_ge : ∀ {u v w : V} (p : W.graph.Walk u v) (q : W.graph.Walk v w)
    {r : ℝ}, 0 ≤ r → walkPoint (p.append q) (walkLength W.weight p + r) = walkPoint q r
  | _, _, _, .nil, q, r, _ => by
    rw [Walk.nil_append, walkLength_nil, zero_add]
  | u, v, w, .cons (v := b) hadj p', q, r, hr => by
    rw [walkLength_cons, add_assoc]
    dsimp only [Walk.cons_append]
    let d : W.graph.Dart := ⟨(u, b), hadj⟩
    have hwe : W.weight s(u, b) = W.weight d.edge := rfl
    rw [hwe]
    have hp'_nn : 0 ≤ walkLength W.weight p' := walkLength_nonneg W.weight W.weight_nonneg p'
    by_cases hsum : walkLength W.weight p' + r = 0
    · have hp'0 : walkLength W.weight p' = 0 := by linarith
      have hr0 : r = 0 := by linarith
      have hp'_nil : p'.Nil := by
        by_contra hnn
        linarith [walkLength_pos_of_not_nil (W := W) hnn]
      cases hp'_nil
      subst hr0
      rw [walkLength_nil, add_zero, add_zero,
        walkPoint_cons_eq_end hadj (Walk.nil.append q) d rfl rfl, walkPoint_nonpos q le_rfl]
    · have hgt : W.weight d.edge < W.weight d.edge + (walkLength W.weight p' + r) := by
        have : 0 < walkLength W.weight p' + r := lt_of_le_of_ne (by linarith) (Ne.symm hsum)
        linarith
      rw [walkPoint_cons_of_gt hadj (p'.append q) d rfl hgt, add_sub_cancel_left]
      exact walkPoint_append_of_ge p' q hr

theorem dist_walkPoint_le [Finite V] {u v : V} (p : W.graph.Walk u v) (s t : ℝ) :
    Dist.dist (walkPoint p s) (walkPoint p t) ≤ |s - t| := by
  wlog hst : s ≤ t generalizing s t
  · rw [_root_.dist_comm, abs_sub_comm]
    exact this t s (le_of_not_ge hst)
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)]
  induction p generalizing s t with
  | nil => simp [walkPoint, hst]
  | @cons a b c hadj q ih =>
    let d : W.graph.Dart := ⟨(a, b), hadj⟩
    have hw : 0 < W.weight d.edge := W.dart_weight_pos d
    have hedge : ∀ {s t : ℝ}, s ≤ t → t ≤ W.weight d.edge →
        Dist.dist (walkPoint (.cons hadj q) s) (walkPoint (.cons hadj q) t) ≤ t - s := by
      intro s t hst htw
      have hsw := hst.trans htw
      dsimp only [walkPoint]
      rw [ite_eq_left hsw, ite_eq_left htw]
      refine (dist_edgePoint_self_le d _ _).trans ?_
      dsimp only
      rw [min_eq_left hsw, min_eq_left htw, ← sub_div, abs_div, abs_of_pos hw,
        mul_div_cancel₀ _ hw.ne', abs_sub_comm,
        abs_of_nonneg (sub_nonneg.mpr (max_le_max_left 0 hst))]
      exact sub_le_iff_le_add.mpr (max_le (by linarith [le_max_left 0 s])
        (by linarith [le_max_right 0 s]))
    rcases le_or_gt t (W.weight d.edge) with htw | htw
    · exact hedge hst htw
    rw [walkPoint_cons_of_gt hadj q d rfl htw]
    rcases le_or_gt s (W.weight d.edge) with hsw | hsw
    · have h1 := hedge hsw le_rfl
      rw [walkPoint_cons_eq_end hadj q d rfl rfl, ← walkPoint_nonpos q (s := 0) le_rfl] at h1
      linarith [ih 0 (t - W.weight d.edge) (by linarith),
        _root_.dist_triangle (walkPoint (.cons hadj q) s) (walkPoint q 0)
          (walkPoint q (t - W.weight d.edge))]
    · rw [walkPoint_cons_of_gt hadj q d rfl hsw]
      exact (ih (s - W.weight d.edge) (t - W.weight d.edge) (by linarith)).trans_eq (by ring)

private lemma walkPoint_dart_decomp : ∀ {u v : V} (p : W.graph.Walk u v), ¬ p.Nil →
    ∀ {s : ℝ}, 0 ≤ s → s ≤ walkLength W.weight p →
    ∃ (d : W.graph.Dart) (q₁ : W.graph.Walk u d.fst) (q₂ : W.graph.Walk d.snd v)
      (hadj : W.graph.Adj d.fst d.snd) (t : unitInterval),
      d = ⟨(d.fst, d.snd), hadj⟩ ∧ p = q₁.append (.cons hadj q₂) ∧
      walkPoint p s = edgePoint d t ∧ s = walkLength W.weight q₁ + (t : ℝ) * W.weight d.edge
  | _, _, .nil, hp, _, _, _ => absurd .nil hp
  | u, v, .cons (v := b) hadj q, _, s, hs0, hsl => by
    let d : W.graph.Dart := ⟨(u, b), hadj⟩
    have hw : 0 < W.weight d.edge := W.dart_weight_pos d
    by_cases hsw : s ≤ W.weight d.edge
    · let t : unitInterval :=
        ⟨s / W.weight d.edge, div_nonneg hs0 hw.le, (div_le_one hw).mpr hsw⟩
      refine ⟨d, .nil, q, hadj, t, rfl, rfl, ?_, ?_⟩
      · exact walkPoint_cons_of_le hadj q d rfl hs0 hsw
          (div_nonneg hs0 hw.le) ((div_le_one hw).mpr hsw)
      · simp [t, walkLength_nil, div_mul_cancel₀ _ hw.ne']
    · have hq_nn : ¬ q.Nil := by
        intro hqn
        cases hqn
        rw [walkLength_cons, walkLength_nil, add_zero] at hsl
        exact hsw hsl
      rw [walkLength_cons] at hsl
      have hwe : W.weight s(u, b) = W.weight d.edge := rfl
      rw [hwe] at hsl
      obtain ⟨d', q₁', q₂', hadj', t, hd', hq_eq, hpt, hs_eq⟩ :=
        walkPoint_dart_decomp q hq_nn (s := s - W.weight d.edge) (by linarith) (by linarith)
      refine ⟨d', .cons hadj q₁', q₂', hadj', t, hd', ?_, ?_, ?_⟩
      · conv_lhs => rw [hq_eq]
        rfl
      · rw [walkPoint_cons_of_gt hadj q d rfl (lt_of_not_ge hsw), hpt]
      · simp only [walkLength_cons]
        linarith

private lemma walkPoint_last_sub {u v : V} (p : W.graph.Walk u v) (hp : ¬ p.Nil) :
    ∃ (d : W.graph.Dart), d.fst = v ∧ d.edge ∈ p.edges ∧
      ∀ {r : ℝ}, 0 < r → r ≤ W.weight d.edge →
        ∀ (hr0 : 0 ≤ r / W.weight d.edge) (hr1 : r / W.weight d.edge ≤ 1),
          walkPoint p (walkLength W.weight p - r) =
            edgePoint d ⟨r / W.weight d.edge, hr0, hr1⟩ := by
  cases hpr : p.reverse with
  | nil =>
    exfalso; apply hp
    have hlen : p.length = 0 := by rw [← Walk.length_reverse, hpr, Walk.length_nil]
    exact Walk.length_eq_zero_iff.mp hlen
  | @cons _ b _ hadj q =>
    have hp_eq : p = q.reverse.append (.cons hadj.symm .nil) := by
      simpa only [Walk.reverse_reverse, Walk.reverse_cons, Walk.concat_eq_append] using
        congrArg Walk.reverse hpr
    let d : W.graph.Dart := ⟨(v, b), hadj⟩
    let d₀ : W.graph.Dart := ⟨(b, v), hadj.symm⟩
    have hd_w : W.weight d₀.edge = W.weight d.edge := congrArg W.weight (Sym2.eq_swap)
    refine ⟨d, rfl, ?_, fun {r} hr hrw hr0 hr1 => ?_⟩
    · rw [hp_eq, Walk.edges_append, List.mem_append, Walk.edges_cons]
      exact Or.inr (by change s(v, b) ∈ s(b, v) :: _; rw [Sym2.eq_swap]; exact List.mem_cons_self)
    · have hw := W.dart_weight_pos d
      have hlen : walkLength W.weight p = walkLength W.weight q.reverse + W.weight d.edge := by
        rw [hp_eq, walkLength_append, walkLength_cons, walkLength_nil, add_zero]
        exact congrArg _ hd_w
      have hsub : walkLength W.weight p - r =
          walkLength W.weight q.reverse + (W.weight d.edge - r) := by linarith
      rw [hsub]
      conv_lhs => arg 1; rw [hp_eq]
      rw [walkPoint_append_of_ge _ _ (sub_nonneg.mpr hrw),
        walkPoint_cons_of_le hadj.symm .nil d₀ rfl (by linarith) (by linarith)
          (div_nonneg (by linarith) (hd_w ▸ hw.le))
          ((div_le_one (hd_w ▸ hw)).mpr (by linarith)), ← edgePoint_symm d₀]
      congr 1; ext
      simp only [unitInterval.coe_symm_eq, hd_w]
      field_simp; ring


/-- Periodic arc-length parameterization of a cycle `c : W.graph.Walk v₀ v₀` into
`MetricGraph W`. -/
@[expose] noncomputable def circleMap {v₀ : V} {c : W.graph.Walk v₀ v₀} (_ : c.IsCycle)
    (s : ℝ) : MetricGraph W :=
  walkPoint c (Int.fract (s / walkLength W.weight c) * walkLength W.weight c)

theorem circleMap_periodic {v₀ : V} {c : W.graph.Walk v₀ v₀} (hc : c.IsCycle) (s : ℝ) :
    circleMap hc (s + walkLength W.weight c) = circleMap hc s := by
  have hL : 0 < walkLength W.weight c := walkLength_pos_of_not_nil hc.not_nil
  simp only [circleMap, add_div, div_self hL.ne', Int.fract_add_one]

theorem circleMap_add_int_mul {v₀ : V} {c : W.graph.Walk v₀ v₀} (hc : c.IsCycle) (s : ℝ) (k : ℤ) :
    circleMap hc (s + (k : ℝ) * walkLength W.weight c) = circleMap hc s := by
  have hL : 0 < walkLength W.weight c := walkLength_pos_of_not_nil hc.not_nil
  simp only [circleMap, add_div, mul_div_cancel_right₀ _ hL.ne', Int.fract_add_intCast]

theorem circleMap_eq_walkPoint {v₀ : V} {c : W.graph.Walk v₀ v₀} (hc : c.IsCycle) {s : ℝ}
    (hs0 : 0 ≤ s) (hsl : s ≤ walkLength W.weight c) :
    circleMap hc s = walkPoint c s := by
  have hL : 0 < walkLength W.weight c := walkLength_pos_of_not_nil hc.not_nil
  rcases eq_or_lt_of_le hsl with rfl | hlt
  · have hper := circleMap_periodic hc 0
    rw [zero_add] at hper
    rw [hper, circleMap, zero_div, Int.fract_zero, zero_mul, walkPoint_nonpos c le_rfl,
      walkPoint_ge c le_rfl]
  · rw [circleMap, Int.fract_eq_self.mpr ⟨div_nonneg hs0 hL.le, (div_lt_one hL).mpr hlt⟩,
      div_mul_cancel₀ _ hL.ne']

@[simp]
theorem circleMap_zero {v₀ : V} {c : W.graph.Walk v₀ v₀} (hc : c.IsCycle) :
    circleMap hc 0 = vertex v₀ := by
  rw [circleMap_eq_walkPoint hc le_rfl (walkLength_nonneg W.weight W.weight_nonneg c),
    walkPoint_nonpos c le_rfl]

theorem circleMap_dist_le [Finite V] {v₀ : V} {c : W.graph.Walk v₀ v₀} (hc : c.IsCycle)
    (s t : ℝ) :
    Dist.dist (circleMap hc s) (circleMap hc t) ≤ |s - t| := by
  wlog hst : s ≤ t generalizing s t
  · rw [_root_.dist_comm, abs_sub_comm]
    exact this t s (le_of_not_ge hst)
  let L := walkLength W.weight c
  have hL : 0 < L := walkLength_pos_of_not_nil hc.not_nil
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)]
  let d : ℝ := Int.fract ((t - s) / L) * L
  obtain ⟨hd0, hdL⟩ : 0 ≤ d ∧ d < L := fract_mul_mem_Ico hL _
  have hk_nn : 0 ≤ (⌊(t - s) / L⌋ : ℝ) := by
    exact_mod_cast Int.floor_nonneg.mpr (div_nonneg (sub_nonneg.mpr hst) hL.le)
  have ht_shift : t - s = d + (⌊(t - s) / L⌋ : ℝ) * L := eq_fract_mul_add_floor_mul hL _
  have hs_shift := eq_fract_mul_add_floor_mul hL s
  let r := Int.fract (s / L) * L
  obtain ⟨hr0, hrl⟩ : 0 ≤ r ∧ r < L := fract_mul_mem_Ico hL _
  refine le_trans ?_ (show d ≤ t - s by nlinarith)
  rw [show t = (s + d) + (⌊(t - s) / L⌋ : ℝ) * L by linarith,
    circleMap_add_int_mul hc _ ⌊(t - s) / L⌋]
  have hsm : circleMap hc s = walkPoint c r := rfl
  by_cases hsum : r + d ≤ L
  · have htm : circleMap hc (s + d) = walkPoint c (r + d) := by
      rw [show s + d = (r + d) + (⌊s / L⌋ : ℝ) * L by linarith,
        circleMap_add_int_mul hc _ ⌊s / L⌋, circleMap_eq_walkPoint hc (by linarith) hsum]
    rw [hsm, htm]
    exact (dist_walkPoint_le c r (r + d)).trans_eq (by
      rw [abs_sub_comm, add_sub_cancel_left, abs_of_nonneg hd0])
  · have h1 : Dist.dist (walkPoint c r) (vertex v₀) ≤ L - r := by
      rw [← walkPoint_ge c (s := L) le_rfl]
      exact (dist_walkPoint_le c r L).trans_eq (by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hrl.le)])
    have htm : circleMap hc (s + d) = walkPoint c (r + d - L) := by
      rw [show s + d = (r + d - L) + ((⌊s / L⌋ + 1 : ℤ) : ℝ) * L by push_cast; linarith,
        circleMap_add_int_mul hc _ (⌊s / L⌋ + 1),
        circleMap_eq_walkPoint hc (by linarith) (by linarith)]
    have h2 : Dist.dist (vertex v₀) (walkPoint c (r + d - L)) ≤ r + d - L := by
      rw [← walkPoint_nonpos c (s := 0) le_rfl]
      exact (dist_walkPoint_le c 0 (r + d - L)).trans_eq (by
        rw [zero_sub, abs_neg, abs_of_nonneg (by linarith)])
    rw [hsm, htm]
    exact (_root_.dist_triangle _ (vertex v₀) _).trans (by linarith)

theorem circleMap_continuous [Finite V] {v₀ : V} {c : W.graph.Walk v₀ v₀} (hc : c.IsCycle) :
    Continuous (circleMap hc) :=
  continuous_iff_continuousAt.mpr fun _ =>
    Metric.continuousAt_iff.mpr fun ε hε =>
      ⟨ε, hε, fun {y} hy => (circleMap_dist_le hc y _).trans_lt (by simpa [Real.dist_eq] using hy)⟩

theorem circleMap_dist_le_circleDist [Finite V] {v₀ : V} {c : W.graph.Walk v₀ v₀} (hc : c.IsCycle)
    (s t : ℝ) :
    Dist.dist (circleMap hc s) (circleMap hc t) ≤ circleDist (walkLength W.weight c) s t := by
  have hL : 0 < walkLength W.weight c := walkLength_pos_of_not_nil hc.not_nil
  obtain ⟨k, hk⟩ := exists_eq_add_int_mul_dist hL s t
  rw [← hk, ← circleMap_add_int_mul hc t k]
  exact circleMap_dist_le hc s (t + (k : ℝ) * walkLength W.weight c)

end CircleMap

/-! ### Isometric shortest cycles -/

section ShortestCycleIsometry

private lemma isCycle_append_chord {u w : V}
    {q : W.graph.Walk u w} {r : W.graph.Walk w u} (hq : q.IsPath) (hr : r.IsPath)
    (huw : u ≠ w) (hdisj : ∀ x ∈ q.support, x ∈ r.support → x = u ∨ x = w)
    (hlen : 3 ≤ q.length + r.length) :
    (q.append r).IsCycle := by
  rw [Walk.isCycle_iff_isPath_tail_and_le_length]
  refine ⟨?_, by rw [Walk.length_append]; exact hlen⟩
  have hqn : ¬ q.Nil := Walk.not_nil_of_ne huw
  have hrn : ¬ r.Nil := Walk.not_nil_of_ne huw.symm
  cases q with
  | nil => exact absurd .nil hqn
  | cons hadj q' =>
    rw [Walk.cons_append]
    simp only [Walk.tail_cons]
    refine (Walk.isPath_copy (q'.append r) _ _).mpr
      ((Walk.isPath_append q' r).mpr ⟨hq.of_cons, hr.tail, ?_⟩)
    rw [List.disjoint_left]
    intro x hxq' hxr
    have hxq : x ∈ (Walk.cons hadj q').support := List.mem_cons_of_mem _ hxq'
    have hxr' : x ∈ r.support := List.mem_of_mem_tail hxr
    rcases hdisj x hxq hxr' with rfl | rfl
    · exact (Walk.cons_isPath_iff hadj q').mp hq |>.2 hxq'
    · rw [← Walk.support_tail_of_not_nil r hrn] at hxr
      have hrnd := hr.support_nodup
      rw [← Walk.cons_tail_eq r hrn, Walk.support_cons, List.nodup_cons] at hrnd
      exact hrnd.1 hxr

private noncomputable def cycCoord [DecidableEq V] {v₀ : V} (c : W.graph.Walk v₀ v₀) (u : V) : ℝ :=
  if h : u ∈ c.support then walkLength W.weight (c.takeUntil u h) else 0

private lemma cycCoord_of_mem [DecidableEq V] {v₀ : V} {c : W.graph.Walk v₀ v₀} {u : V}
    (hu : u ∈ c.support) : cycCoord c u = walkLength W.weight (c.takeUntil u hu) := by
  dsimp only [cycCoord]
  split_ifs
  rfl

private lemma takeUntil_walkLength_congr [DecidableEq V] {a b x : V} {p q : W.graph.Walk a b}
    (h : p = q) (hp : x ∈ p.support) :
    walkLength W.weight (p.takeUntil x hp) = walkLength W.weight (q.takeUntil x (h ▸ hp)) := by
  subst h
  rfl

private lemma takeUntil_append_of_not_mem_left [DecidableEq V] {a b d : V} {x : V}
    (p : W.graph.Walk a b) (q : W.graph.Walk b d) (hxp : x ∉ p.support)
    (hxq : x ∈ q.support) :
    (p.append q).takeUntil x (Walk.support_subset_support_append_right _ _ hxq) =
      p.append (q.takeUntil x hxq) := by
  induction p with
  | nil => simp
  | cons hadj p' ih =>
    have hne : _ ≠ x := fun h => hxp (h ▸ Walk.start_mem_support _)
    have hxp' : x ∉ p'.support := fun h => hxp (List.mem_cons_of_mem _ h)
    simp only [Walk.cons_append, Walk.takeUntil]
    split_ifs with h
    · exact absurd h hne
    · rw [ih q hxp']

private lemma takeUntil_self_of_isPath [DecidableEq V] {a b : V} (p : W.graph.Walk a b)
    (hp : p.IsPath) : p.takeUntil b p.end_mem_support = p := by
  induction p with
  | nil => rfl
  | @cons u v w hadj q ih =>
    have hne : u ≠ w := by
      rintro rfl
      exact (Walk.cons_isPath_iff hadj q).mp hp |>.2 q.end_mem_support
    simp only [Walk.takeUntil]
    split_ifs with h
    · exact absurd h hne
    · rw [ih hp.of_cons]

private lemma cycCoord_append_eq [DecidableEq V] {v₀ u : V} {c : W.graph.Walk v₀ v₀}
    (hc : c.IsCycle) {p : W.graph.Walk v₀ u} {q : W.graph.Walk u v₀}
    (hc_eq : c = p.append q) (hq : ¬ q.Nil) :
    cycCoord c u = walkLength W.weight p := by
  have hc' : (p.append q).IsCycle := hc_eq ▸ hc
  have hp_path : p.IsPath := hc'.isPath_of_append_left hq
  have hu : u ∈ c.support := hc_eq ▸ Walk.support_subset_support_append_left _ _ p.end_mem_support
  rw [cycCoord_of_mem hu, takeUntil_walkLength_congr hc_eq hu,
    Walk.takeUntil_append_of_mem_left _ _ p.end_mem_support, takeUntil_self_of_isPath p hp_path]

private lemma circleDist_le_min_of_sum_eq {L x y a₁ a₂ : ℝ} (hL : 0 < L)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hsum : a₁ + a₂ = L)
    (harc : y - x = a₁ ∨ x - y = a₂) :
    circleDist L x y ≤ min a₁ a₂ := by
  have step : ∀ {u v b₁ b₂ : ℝ}, 0 ≤ b₁ → 0 ≤ b₂ → b₁ + b₂ = L → v - u = b₁ →
      circleDist L u v ≤ min b₁ b₂ := by
    intro u v b₁ b₂ hb₁ hb₂ hb hvu
    refine le_min ?_ ?_
    · refine (circleDist_le_abs hL u v).trans_eq ?_
      rw [abs_sub_comm, hvu, abs_of_nonneg hb₁]
    · rw [← circleDist_add_int_right hL u v (-1), Int.cast_neg, Int.cast_one, neg_one_mul]
      refine (circleDist_le_abs hL u (v + -L)).trans_eq ?_
      rw [show u - (v + -L) = b₂ by linarith, abs_of_nonneg hb₂]
  rcases harc with hyx | hxy
  · exact step ha₁ ha₂ hsum hyx
  · rw [circleDist_symm hL, min_comm]
    exact step ha₂ ha₁ (add_comm a₂ a₁ ▸ hsum) hxy

private lemma takeUntil_rotate_length [DecidableEq V] {v₀ a w : V} {c : W.graph.Walk v₀ v₀}
    (hc : c.IsCycle) (ha : a ∈ c.support) (hw : w ∈ c.support) (haw : a ≠ w) :
    circleDist (walkLength W.weight c) (cycCoord c a) (cycCoord c w) ≤
      min (walkLength W.weight
          ((c.rotate a ha).takeUntil w ((c.mem_support_rotate_iff a ha).mpr hw)))
        (walkLength W.weight
          ((c.rotate a ha).dropUntil w ((c.mem_support_rotate_iff a ha).mpr hw))) := by
  let L := walkLength W.weight c
  have hL : 0 < L := walkLength_pos_of_not_nil hc.not_nil
  let c₁ := c.takeUntil a ha
  let c₂ := c.dropUntil a ha
  have hc_eq : c₁.append c₂ = c := c.take_spec ha
  have hlen12 : walkLength W.weight c₁ + walkLength W.weight c₂ = L := by
    rw [← walkLength_append, hc_eq]
  have hlen_arc : walkLength W.weight
      ((c.rotate a ha).takeUntil w ((c.mem_support_rotate_iff a ha).mpr hw)) +
      walkLength W.weight
      ((c.rotate a ha).dropUntil w ((c.mem_support_rotate_iff a ha).mpr hw)) = L := by
    rw [← walkLength_append, Walk.take_spec]
    exact walkLength_perm_eq W.weight (c.rotate_edges a ha).perm
  refine circleDist_le_min_of_sum_eq hL
    (walkLength_nonneg W.weight W.weight_nonneg _)
    (walkLength_nonneg W.weight W.weight_nonneg _) hlen_arc ?_
  have ha_coord : cycCoord c a = walkLength W.weight c₁ := cycCoord_of_mem ha
  by_cases hwv0 : w = v₀
  · subst hwv0
    have hc0 : cycCoord c w = 0 := by
      rw [cycCoord_of_mem (Walk.start_mem_support c), Walk.takeUntil_first, walkLength_nil]
    have harc1_eq : (c.rotate a ha).takeUntil w ((c.mem_support_rotate_iff a ha).mpr hw) = c₂ :=
      (Walk.takeUntil_append_of_mem_left c₂ c₁ c₂.end_mem_support).trans
        (takeUntil_self_of_isPath c₂
          ((hc_eq.symm ▸ hc).isPath_of_append_right (Walk.not_nil_of_ne haw.symm)))
    exact Or.inr (by linarith [congrArg (walkLength W.weight) harc1_eq])
  by_cases hwc1 : w ∈ c₁.support
  · have hwc2 : w ∉ c₂.support := fun hw2 => by
      have hcnt := hc.count_support_of_mem hw hwv0
      rw [← hc_eq, Walk.support_append, List.count_append] at hcnt
      have h1 := List.one_le_count_iff.mpr hwc1
      have h2 := List.one_le_count_iff.mpr
        (((Walk.mem_support_iff c₂).mp hw2).resolve_left fun h => haw h.symm)
      omega
    have hcw : cycCoord c w = walkLength W.weight (c₁.takeUntil w hwc1) := by
      rw [cycCoord_of_mem hw, takeUntil_walkLength_congr hc_eq.symm hw,
        Walk.takeUntil_append_of_mem_left c₁ c₂ hwc1]
    have harc1 : walkLength W.weight
        ((c.rotate a ha).takeUntil w ((c.mem_support_rotate_iff a ha).mpr hw)) =
        walkLength W.weight c₂ + walkLength W.weight (c₁.takeUntil w hwc1) :=
      (congrArg (walkLength W.weight)
        (takeUntil_append_of_not_mem_left c₂ c₁ hwc2 hwc1)).trans (walkLength_append _ _ _)
    exact Or.inr (by linarith)
  · have hwc2 : w ∈ c₂.support :=
      List.mem_of_mem_tail ((List.mem_append.mp (Walk.support_append c₁ c₂ ▸
        (hc_eq ▸ hw))).resolve_left hwc1)
    have hcw : cycCoord c w =
        walkLength W.weight c₁ + walkLength W.weight (c₂.takeUntil w hwc2) := by
      rw [cycCoord_of_mem hw, takeUntil_walkLength_congr hc_eq.symm hw,
        takeUntil_append_of_not_mem_left c₁ c₂ hwc1 hwc2, walkLength_append]
    have harc1 : walkLength W.weight
        ((c.rotate a ha).takeUntil w ((c.mem_support_rotate_iff a ha).mpr hw)) =
        walkLength W.weight (c₂.takeUntil w hwc2) :=
      congrArg (walkLength W.weight) (Walk.takeUntil_append_of_mem_left c₂ c₁ hwc2)
    exact Or.inl (by linarith)

private lemma walkLength_eq_of_length_one : ∀ {u v : V} (p : W.graph.Walk u v),
    p.length = 1 → walkLength W.weight p = W.weight s(u, v)
  | _, _, .cons _ .nil, _ => by simp [walkLength_cons, walkLength_nil]

private lemma mem_edges_of_length_eq_one : ∀ {u v : V} (p : W.graph.Walk u v),
    p.length = 1 → s(u, v) ∈ p.edges
  | _, _, .cons _ .nil, _ => List.mem_cons_self

private lemma takeUntil_vert_walkLength_congr [DecidableEq V] {u v : V} (p : W.graph.Walk u v)
    {x y : V} (hxy : x = y) (hx : x ∈ p.support) (hy : y ∈ p.support) :
    walkLength W.weight (p.takeUntil x hx) = walkLength W.weight (p.takeUntil y hy) := by
  subst hxy
  rfl

private lemma takeUntil_snd_walkLength [DecidableEq V] {u : V} (p : W.graph.Walk u u)
    (hp : p.IsCycle) (h : p.snd ∈ p.support) :
    walkLength W.weight (p.takeUntil p.snd h) = W.weight s(u, p.snd) := by
  cases p with
  | nil => exact absurd .nil hp.not_nil
  | @cons _ b _ hadj q =>
    have hsnd : (Walk.cons hadj q).snd = b := by simp
    have hb : b ∈ (Walk.cons hadj q).support := by simpa only [hsnd] using h
    have hcongr : walkLength W.weight ((Walk.cons hadj q).takeUntil (Walk.cons hadj q).snd h) =
        walkLength W.weight ((Walk.cons hadj q).takeUntil b hb) :=
      takeUntil_vert_walkLength_congr (Walk.cons hadj q) hsnd h hb
    rw [hcongr, hsnd, Walk.takeUntil]
    split_ifs with heq
    · exact absurd heq hadj.ne
    · rw [Walk.takeUntil_first, walkLength_cons, walkLength_nil, add_zero]

private lemma isCycle_min_arc_le_edge [DecidableEq V] {a w : V} {cₐ : W.graph.Walk a a}
    (hcₐ : cₐ.IsCycle) (hw : w ∈ cₐ.support) (haw : a ≠ w) (he : s(a, w) ∈ cₐ.edges) :
    min (walkLength W.weight (cₐ.takeUntil w hw)) (walkLength W.weight (cₐ.dropUntil w hw)) ≤
      W.weight s(a, w) := by
  rcases hcₐ.isPath_dropLast.eq_snd_or_eq_penultimate_of_start_mem_edges he with hwsnd | hwpen
  · refine (min_le_left _ _).trans_eq ?_
    rw [takeUntil_vert_walkLength_congr cₐ hwsnd hw (hwsnd ▸ hw),
      takeUntil_snd_walkLength cₐ hcₐ (hwsnd ▸ hw), hwsnd]
  · refine (min_le_right _ _).trans_eq ?_
    have hpen_eq : cₐ.getVert (cₐ.length - 1) = w := by
      have hrev := Walk.getVert_reverse cₐ 1
      have hsnd1 : cₐ.reverse.getVert 1 = cₐ.reverse.snd := by cases cₐ.reverse <;> rfl
      rw [hsnd1, Walk.snd_reverse] at hrev
      exact hrev.symm.trans hwpen.symm
    have hlen_lt := Walk.length_takeUntil_lt_length hw (Ne.symm haw)
    have hl3 := hcₐ.three_le_length
    have hlen_eq : (cₐ.takeUntil w hw).length = cₐ.length - 1 :=
      hcₐ.getVert_injOn' (by simp only [Set.mem_Iio]; omega)
        (by simp only [Set.mem_Iio]; omega)
        ((Walk.getVert_length_takeUntil hw).trans hpen_eq.symm)
    have hdrop_len : (cₐ.dropUntil w hw).length = 1 := by
      have h := congrArg Walk.length (cₐ.take_spec hw)
      rw [Walk.length_append] at h; omega
    rw [walkLength_eq_of_length_one _ hdrop_len, Sym2.eq_swap]

private lemma isCycle_chord_le [DecidableEq V] {v₀ : V} {c : W.graph.Walk v₀ v₀}
    (hs : IsShortestCycle W c) :
    ∀ (n : ℕ) {a b : V} (p : W.graph.Walk a b),
      p.length = n → p.IsPath → a ∈ c.support → b ∈ c.support →
        circleDist (walkLength W.weight c) (cycCoord c a) (cycCoord c b) ≤
          walkLength W.weight p := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro a b p hlen hp ha hb
    let L := walkLength W.weight c
    have hL : 0 < L := walkLength_pos_of_not_nil hs.1.not_nil
    rcases Nat.eq_zero_or_pos n with rfl | hn_pos
    · cases p with
      | nil => rw [circleDist_self hL]; exact walkLength_nonneg W.weight W.weight_nonneg _
      | cons _ _ => rw [Walk.length_cons] at hlen; omega
    classical
    have hex : ∃ k : ℕ, 0 < k ∧ k ≤ p.length ∧ p.getVert k ∈ c.support :=
      ⟨p.length, hlen ▸ hn_pos, le_rfl, by simpa only [Walk.getVert_length] using hb⟩
    let k := Nat.find hex
    have hk := Nat.find_spec hex
    let w := p.getVert k
    have hw : w ∈ c.support := hk.2.2
    let q₁ := p.take k
    let q₂ := p.drop k
    have hq1_len : q₁.length = k := (Walk.take_length p k).trans (min_eq_left hk.2.1)
    have hih := ih q₂.length (by rw [Walk.drop_length]; omega) q₂ rfl (hp.drop k) hw hb
    suffices h1 : circleDist L (cycCoord c a) (cycCoord c w) ≤ walkLength W.weight q₁ by
      exact (circleDist_triangle hL (cycCoord c a) (cycCoord c w) (cycCoord c b)).trans
        (by linarith [walkLength_take_add_drop p k])
    by_cases haw : a = w
    · rw [← haw, circleDist_self hL]; exact walkLength_nonneg W.weight W.weight_nonneg q₁
    let cₐ := c.rotate a ha
    have hcₐ : cₐ.IsCycle := (c.isCycle_rotate ha).mpr hs.1
    have hw' : w ∈ cₐ.support := (c.mem_support_rotate_iff a ha).mpr hw
    refine (takeUntil_rotate_length hs.1 ha hw haw).trans ?_
    by_cases hsub1 : q₁.length = 1 ∧ s(a, w) ∈ cₐ.edges
    · exact (isCycle_min_arc_le_edge hcₐ hw' haw hsub1.2).trans_eq
        (walkLength_eq_of_length_one q₁ hsub1.1).symm
    have harc_disj : ∀ x ∈ q₁.support, x ∈ cₐ.support → x = a ∨ x = w := by
      intro x hxq hxc
      by_contra hne; push Not at hne
      obtain ⟨i, hi_eq, hi_le⟩ := Walk.mem_support_iff_exists_getVert.mp hxq
      rw [hq1_len] at hi_le
      have hgi : p.getVert i = x := by
        simpa only [q₁, Walk.take_getVert, min_eq_right hi_le] using hi_eq
      have hi0 : 0 < i := Nat.pos_of_ne_zero fun h0 =>
        hne.1 (hgi.symm.trans (by rw [h0, Walk.getVert_zero]))
      have hik : i < k := lt_of_le_of_ne hi_le fun h => hne.2 (hgi.symm.trans (by rw [h]))
      exact Nat.find_min hex hik ⟨hi0, hi_le.trans hk.2.1, hgi ▸
        (c.mem_support_rotate_iff a ha).mp hxc⟩
    let arc₂ := cₐ.dropUntil w hw'
    have harc_sum : walkLength W.weight (cₐ.takeUntil w hw') + walkLength W.weight arc₂ = L := by
      rw [← walkLength_append, Walk.take_spec]
      exact walkLength_perm_eq W.weight (c.rotate_edges a ha).perm
    have harc2_path : arc₂.IsPath :=
      ((cₐ.take_spec hw').symm ▸ hcₐ).isPath_of_append_right (Walk.not_nil_of_ne haw)
    have hq1_pos : 0 < q₁.length := hq1_len.symm ▸ hk.1
    have harc2_pos : 0 < arc₂.length :=
      Nat.pos_of_ne_zero (Walk.length_eq_zero_iff.not.mpr (Walk.not_nil_of_ne (Ne.symm haw)))
    have hne1 : q₁.length = 1 → arc₂.length ≠ 1 := fun h1 h => hsub1 ⟨h1, Sym2.eq_swap ▸
      Walk.edges_dropUntil_subset_edges cₐ hw' (mem_edges_of_length_eq_one arc₂ h)⟩
    have hlen3 : 3 ≤ q₁.length + arc₂.length := by omega
    have hcyc : (q₁.append arc₂).IsCycle := isCycle_append_chord (hp.take k) harc2_path haw
      (fun x hx1 hx2 => harc_disj x hx1 (Walk.support_dropUntil_subset_support _ _ hx2)) hlen3
    have hs1 : L ≤ walkLength W.weight q₁ + walkLength W.weight arc₂ :=
      walkLength_append W.weight q₁ arc₂ ▸ hs.2 (q₁.append arc₂) hcyc
    exact (min_le_left _ _).trans (by linarith)

private lemma circleDist_le_vertexDist [Finite V] [DecidableEq V] {v₀ : V}
    {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c) {a b : V}
    (ha : a ∈ c.support) (hb : b ∈ c.support) :
    circleDist (walkLength W.weight c) (cycCoord c a) (cycCoord c b) ≤
      vertexDist W.graph W.weight a b := by
  obtain ⟨p, hp, hlen⟩ :=
    exists_isPath_walkLength_eq_vertexDist W.weight_nonneg (W.connected a b)
  rw [← hlen]
  exact isCycle_chord_le hs p.length p rfl hp ha hb

private lemma walk_cons_tail_eq {u b₁ b₂ v : V} {h₁ : W.graph.Adj u b₁} {h₂ : W.graph.Adj u b₂}
    {p₁ : W.graph.Walk b₁ v} {p₂ : W.graph.Walk b₂ v}
    (he : Walk.cons h₁ p₁ = Walk.cons h₂ p₂) :
    ∃ hb : b₁ = b₂, p₁.copy hb rfl = p₂ := by
  cases he
  exact ⟨rfl, rfl⟩

/-- A trail that starts with the edge `s(u, w)` does not use that edge at a later step. -/
private lemma edge_ne_of_isTrail_cons_append {u w u₂ v₂ v : V} {p : W.graph.Walk u v}
    (ht : p.IsTrail) (h : W.graph.Adj u w) (q : W.graph.Walk w u₂) (h₂ : W.graph.Adj u₂ v₂)
    (r₂ : W.graph.Walk v₂ v) (hp : p = .cons h (q.append (.cons h₂ r₂))) :
    s(u, w) ≠ s(u₂, v₂) := by
  intro he
  have hnd := ht.edges_nodup
  rw [hp, Walk.edges_cons, List.nodup_cons] at hnd
  refine hnd.1 ?_
  rw [he, Walk.edges_append, List.mem_append, Walk.edges_cons]
  exact Or.inr List.mem_cons_self

private lemma walk_decomp_unique_of_isTrail :
    ∀ {u v : V} (p : W.graph.Walk u v), p.IsTrail →
      ∀ {u₁ v₁ u₂ v₂ : V} (q₁ : W.graph.Walk u u₁) (r₁ : W.graph.Walk v₁ v)
        (h₁ : W.graph.Adj u₁ v₁) (q₂ : W.graph.Walk u u₂) (r₂ : W.graph.Walk v₂ v)
        (h₂ : W.graph.Adj u₂ v₂),
        p = q₁.append (.cons h₁ r₁) → p = q₂.append (.cons h₂ r₂) →
        s(u₁, v₁) = s(u₂, v₂) → u₁ = u₂ ∧ v₁ = v₂ ∧ walkLength W.weight q₁ = walkLength W.weight q₂
  | _, _, .nil, _, _, _, _, _, .nil, _, _, _, _, _, hp1, _, _ => by cases hp1
  | _, _, .nil, _, _, _, _, _, .cons _ _, _, _, _, _, _, hp1, _, _ => by cases hp1
  | _, _, .cons _ p', ht, _, _, _, _, q₁, r₁, h₁, q₂, r₂, h₂, hp1, hp2, hedge => by
    cases q₁ with
    | nil => cases q₂ with
      | nil =>
        obtain ⟨hv, _⟩ := walk_cons_tail_eq (hp1.symm.trans hp2)
        exact ⟨rfl, hv, rfl⟩
      | cons hadj2 q₂' =>
        obtain ⟨rfl, -⟩ := walk_cons_tail_eq (hp1.symm.trans hp2)
        exact absurd hedge (edge_ne_of_isTrail_cons_append ht hadj2 q₂' h₂ r₂ hp2)
    | cons hadj1 q₁' => cases q₂ with
      | nil =>
        obtain ⟨rfl, -⟩ := walk_cons_tail_eq (hp2.symm.trans hp1)
        exact absurd hedge.symm (edge_ne_of_isTrail_cons_append ht hadj1 q₁' h₁ r₁ hp1)
      | cons hadj2 q₂' =>
        obtain ⟨rfl, hp1'⟩ := walk_cons_tail_eq hp1
        obtain ⟨rfl, hp2'⟩ := walk_cons_tail_eq hp2
        rw [Walk.copy_rfl_rfl] at hp1' hp2'
        obtain ⟨hu, hv, hlen⟩ := walk_decomp_unique_of_isTrail p' ht.of_cons q₁' r₁ h₁ q₂' r₂ h₂
          hp1' hp2' hedge
        exact ⟨hu, hv, by simp only [walkLength_cons, hlen]⟩

private lemma cycCoord_snd_of_append_cons [DecidableEq V] {v₀ : V} {c : W.graph.Walk v₀ v₀}
    (hc : c.IsCycle) {d : W.graph.Dart} (q₁ : W.graph.Walk v₀ d.fst)
    (q₂ : W.graph.Walk d.snd v₀) (hadj : W.graph.Adj d.fst d.snd)
    (hc_eq : c = q₁.append (.cons hadj q₂)) :
    (walkLength W.weight q₁ + W.weight d.edge = walkLength W.weight c ∧ cycCoord c d.snd = 0) ∨
      cycCoord c d.snd = walkLength W.weight q₁ + W.weight d.edge := by
  cases q₂ with
  | nil =>
    left
    refine ⟨?_, ?_⟩
    · have h := congrArg (walkLength W.weight) hc_eq
      rw [walkLength_append, walkLength_cons, walkLength_nil, add_zero] at h
      exact h.symm
    · rw [cycCoord_of_mem (Walk.start_mem_support c), Walk.takeUntil_first, walkLength_nil]
  | cons hadj2 q₂' =>
    right
    have hc_eq2 : c = (q₁.concat hadj).append (Walk.cons hadj2 q₂') := by
      rw [hc_eq, Walk.concat_eq_append, ← Walk.append_assoc, Walk.cons_append, Walk.nil_append]
    rw [cycCoord_append_eq hc hc_eq2 Walk.not_nil_cons, Walk.concat_eq_append,
      walkLength_append, walkLength_cons, walkLength_nil, add_zero]
    rfl

private lemma circleMap_dart_decomp [DecidableEq V] {v₀ : V} {c : W.graph.Walk v₀ v₀}
    (hc : c.IsCycle) (s : ℝ) :
    ∃ (d : W.graph.Dart) (q₁ : W.graph.Walk v₀ d.fst) (q₂ : W.graph.Walk d.snd v₀)
      (hadj : W.graph.Adj d.fst d.snd) (t : unitInterval),
      d = ⟨(d.fst, d.snd), hadj⟩ ∧ c = q₁.append (.cons hadj q₂) ∧
      circleMap hc s = edgePoint d t ∧
      d.fst ∈ c.support ∧ d.snd ∈ c.support ∧
      circleDist (walkLength W.weight c) s (walkLength W.weight q₁ + (t : ℝ) * W.weight d.edge) =
        0 ∧
      circleDist (walkLength W.weight c) s (cycCoord c d.fst) ≤ (t : ℝ) * W.weight d.edge ∧
      circleDist (walkLength W.weight c) s (cycCoord c d.snd) ≤
        (1 - (t : ℝ)) * W.weight d.edge := by
  let L := walkLength W.weight c
  have hL : 0 < L := walkLength_pos_of_not_nil hc.not_nil
  let r := Int.fract (s / L) * L
  obtain ⟨hr0, hrl⟩ : 0 ≤ r ∧ r < L := fract_mul_mem_Ico hL _
  obtain ⟨d, q₁, q₂, hadj, t, hd, hc_eq, hpt, hr_eq⟩ :=
    walkPoint_dart_decomp c hc.not_nil hr0 hrl.le
  have hs_r : s = r + (⌊s / L⌋ : ℝ) * L := eq_fract_mul_add_floor_mul hL s
  have hcd_s : circleDist L s (walkLength W.weight q₁ + (t : ℝ) * W.weight d.edge) = 0 := by
    rw [← hr_eq, hs_r, circleDist_add_int_left hL, circleDist_self hL]
  have hfst_le : circleDist L s (cycCoord c d.fst) ≤ (t : ℝ) * W.weight d.edge := by
    refine (circleDist_triangle hL s (walkLength W.weight q₁ + (t : ℝ) * W.weight d.edge) _).trans
      ?_
    rw [hcd_s, zero_add, cycCoord_append_eq hc hc_eq Walk.not_nil_cons]
    refine (circleDist_le_abs hL _ _).trans_eq ?_
    rw [add_sub_cancel_left, abs_of_nonneg (mul_nonneg t.property.1 (W.dart_weight_pos d).le)]
  have hsnd_le : circleDist L s (cycCoord c d.snd) ≤ (1 - (t : ℝ)) * W.weight d.edge := by
    refine (circleDist_triangle hL s (walkLength W.weight q₁ + (t : ℝ) * W.weight d.edge) _).trans
      ?_
    rw [hcd_s, zero_add]
    have hmod : circleDist L (walkLength W.weight q₁ + W.weight d.edge) (cycCoord c d.snd) = 0 := by
      rcases cycCoord_snd_of_append_cons hc q₁ q₂ hadj hc_eq with ⟨hlen, hc0⟩ | hcoord
      · rw [hlen, hc0, ← circleDist_add_int_right hL L 0 1, zero_add, Int.cast_one, one_mul,
          circleDist_self hL]
      · rw [hcoord, circleDist_self hL]
    refine (circleDist_triangle hL _ (walkLength W.weight q₁ + W.weight d.edge) _).trans ?_
    rw [hmod, add_zero]
    refine (circleDist_le_abs hL _ _).trans_eq ?_
    rw [show (walkLength W.weight q₁ + (t : ℝ) * W.weight d.edge) -
        (walkLength W.weight q₁ + W.weight d.edge) = -((1 - (t : ℝ)) * W.weight d.edge) by ring,
      abs_neg, abs_of_nonneg (mul_nonneg (unitInterval.one_sub_nonneg t) (W.dart_weight_pos d).le)]
  exact ⟨d, q₁, q₂, hadj, t, hd, hc_eq, hpt,
    hc_eq ▸ Walk.support_subset_support_append_left _ _ q₁.end_mem_support,
    hc_eq ▸ Walk.support_subset_support_append_right _ _
      (List.mem_cons_of_mem _ (Walk.start_mem_support _)),
    hcd_s, hfst_le, hsnd_le⟩

theorem circleMap_dist_eq_circleDist [Finite V] {v₀ : V} {c : W.graph.Walk v₀ v₀}
    (hs : IsShortestCycle W c) (s₁ s₂ : ℝ) :
    Dist.dist (circleMap hs.1 s₁) (circleMap hs.1 s₂) =
      circleDist (walkLength W.weight c) s₁ s₂ := by
  classical
  refine le_antisymm (circleMap_dist_le_circleDist hs.1 s₁ s₂) ?_
  let L := walkLength W.weight c
  have hL : 0 < L := walkLength_pos_of_not_nil hs.1.not_nil
  obtain ⟨d₁, q₁₁, q₁₂, h₁, t₁, _, hc₁, hpt₁, hfst₁, hsnd₁, hcds₁, h1f, h1s⟩ :=
    circleMap_dart_decomp hs.1 s₁
  obtain ⟨d₂, q₂₁, q₂₂, h₂, t₂, _, hc₂, hpt₂, hfst₂, hsnd₂, hcds₂, h2f, h2s⟩ :=
    circleMap_dart_decomp hs.1 s₂
  have hvia : ∀ {u₁ u₂ : V} {b₁ b₂ : ℝ}, u₁ ∈ c.support → u₂ ∈ c.support →
      circleDist L s₁ (cycCoord c u₁) ≤ b₁ → circleDist L s₂ (cycCoord c u₂) ≤ b₂ →
      circleDist L s₁ s₂ ≤ b₁ + vertexDist W.graph W.weight u₁ u₂ + b₂ := by
    intro u₁ u₂ b₁ b₂ hu₁ hu₂ h1 h2
    have := circleDist_le_vertexDist hs hu₁ hu₂
    rw [circleDist_symm hL s₂] at h2
    linarith [circleDist_triangle hL s₁ (cycCoord c u₁) s₂,
      circleDist_triangle hL (cycCoord c u₁) (cycCoord c u₂) s₂]
  have hff := hvia hfst₁ hfst₂ h1f h2f
  have hfs := hvia hfst₁ hsnd₂ h1f h2s
  have hsf := hvia hsnd₁ hfst₂ h1s h2f
  have hss := hvia hsnd₁ hsnd₂ h1s h2s
  rw [hpt₁, hpt₂]
  by_cases he : d₁.edge = d₂.edge
  · obtain ⟨hu, hv, hq_len⟩ :=
      walk_decomp_unique_of_isTrail c hs.1.isTrail q₁₁ q₁₂ h₁ q₂₁ q₂₂ h₂ hc₁ hc₂ he
    have hd_eq : d₁ = d₂ := Dart.toProd_injective (Prod.ext hu hv)
    have hdir : circleDist L s₁ s₂ ≤ |(t₁ : ℝ) - t₂| * W.weight d₂.edge := by
      refine (circleDist_triangle hL _
          (walkLength W.weight q₁₁ + (t₁ : ℝ) * W.weight d₁.edge) _).trans ?_
      rw [hcds₁, zero_add]
      refine (circleDist_triangle hL _
          (walkLength W.weight q₂₁ + (t₂ : ℝ) * W.weight d₂.edge) _).trans ?_
      rw [circleDist_symm hL _ s₂, hcds₂, add_zero]
      refine (circleDist_le_abs hL _ _).trans_eq ?_
      rw [hq_len, hd_eq, add_sub_add_left_eq_sub, ← sub_mul, abs_mul,
        abs_of_nonneg (W.dart_weight_pos d₂).le]
    subst hd_eq
    rw [dist_edgePoint_edgePoint_same]
    exact le_min hdir (le_min (le_min hff hfs) (le_min hsf hss))
  · rw [dist_edgePoint_edgePoint_of_edge_ne he]
    exact le_min (le_min hff hfs) (le_min hsf hss)

theorem circleMap_dist_eq_of_le [Finite V] {v₀ : V} {c : W.graph.Walk v₀ v₀}
    (hs : IsShortestCycle W c) {s₁ s₂ : ℝ} (hle : |s₁ - s₂| ≤ walkLength W.weight c / 2) :
    Dist.dist (circleMap hs.1 s₁) (circleMap hs.1 s₂) = |s₁ - s₂| := by
  have hL : 0 < walkLength W.weight c := walkLength_pos_of_not_nil hs.1.not_nil
  rw [circleMap_dist_eq_circleDist hs s₁ s₂, circleDist_eq_abs_of_abs_le hL hle]

theorem circleMap_injOn [Finite V] {v₀ : V} {c : W.graph.Walk v₀ v₀}
    (hs : IsShortestCycle W c) :
    Set.InjOn (circleMap hs.1) (Set.Ico 0 (walkLength W.weight c)) := by
  intro s₁ hs₁ s₂ hs₂ heq
  have hL : 0 < walkLength W.weight c := walkLength_pos_of_not_nil hs.1.not_nil
  have hcd0 : circleDist (walkLength W.weight c) s₁ s₂ = 0 := by
    rw [← circleMap_dist_eq_circleDist hs s₁ s₂, heq, _root_.dist_self]
  wlog hle : s₁ ≤ s₂ generalizing s₁ s₂
  · exact (this hs₂ hs₁ heq.symm ((circleDist_symm hL s₁ s₂).symm.trans hcd0)
      (le_of_not_ge hle)).symm
  have hf : Int.fract ((s₂ - s₁) / walkLength W.weight c) =
      (s₂ - s₁) / walkLength W.weight c := Int.fract_eq_self.mpr
    ⟨div_nonneg (sub_nonneg.mpr hle) hL.le, (div_lt_one hL).mpr (by linarith [hs₁.1, hs₂.2])⟩
  dsimp only [circleDist] at hcd0
  rw [hf, div_mul_cancel₀ _ hL.ne', one_sub_mul, div_mul_cancel₀ _ hL.ne'] at hcd0
  rcases min_choice (s₂ - s₁) (walkLength W.weight c - (s₂ - s₁)) with hm | hm <;>
    linarith [hs₁.1, hs₂.2]

end ShortestCycleIsometry

/-! ### Pure cycle graphs and local dichotomy along a cycle -/

section CycleStructure

private lemma cycleGraph_adj_eq_add_or_sub {n : ℕ} {a b : Fin (n + 3)}
    (h : (cycleGraph (n + 3)).Adj a b) : b = a - 1 ∨ b = a + 1 := by
  rw [cycleGraph_adj] at h
  rcases h with h | h
  · left
    exact eq_sub_of_add_eq ((add_comm b 1).trans (sub_eq_iff_eq_add.mp h).symm)
  · right
    exact (eq_add_of_sub_eq h).trans (add_comm 1 a)

private lemma cycleGraph_support_of_isCycle {n : ℕ} (e : W.graph ≃g cycleGraph (n + 3))
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hc : c.IsCycle) :
    (∀ v : V, v ∈ c.support) ∧ ∀ {u v : V}, W.graph.Adj u v → s(u, v) ∈ c.edges := by
  classical
  have hstep : ∀ x ∈ c.support, ∀ y : V, W.graph.Adj x y → s(x, y) ∈ c.edges := by
    intro x hx y hadj
    let cₓ := c.rotate x hx
    have hcₓ : cₓ.IsCycle := (c.isCycle_rotate hx).mpr hc
    have ha1 := cycleGraph_adj_eq_add_or_sub (e.map_adj_iff.mpr (Walk.adj_snd hcₓ.not_nil))
    have ha2 := cycleGraph_adj_eq_add_or_sub
      (e.map_adj_iff.mpr (Walk.adj_penultimate hcₓ.not_nil).symm)
    have ha3 := cycleGraph_adj_eq_add_or_sub (e.map_adj_iff.mpr hadj)
    refine (c.rotate_edges x hx).perm.mem_iff.mp ?_
    have hy : y = cₓ.snd ∨ y = cₓ.penultimate := by
      have hne := hcₓ.snd_ne_penultimate
      rcases ha1 with h1 | h1 <;> rcases ha2 with h2 | h2 <;>
        [exact absurd (e.injective (h1.trans h2.symm)) hne;
         exact ha3.imp (fun h => e.injective (h.trans h1.symm))
           (fun h => e.injective (h.trans h2.symm));
         exact ha3.symm.imp (fun h => e.injective (h.trans h1.symm))
           (fun h => e.injective (h.trans h2.symm));
         exact absurd (e.injective (h1.trans h2.symm)) hne]
    rcases hy with rfl | rfl
    · exact Walk.mk_start_snd_mem_edges hcₓ.not_nil
    · rw [Sym2.eq_swap]; exact Walk.mk_penultimate_end_mem_edges hcₓ.not_nil
  have hsup : ∀ v : V, v ∈ c.support := fun v => by
    obtain ⟨p⟩ := W.connected v₀ v
    suffices ∀ {u w : V} (q : W.graph.Walk u w), u ∈ c.support → w ∈ c.support from
      this p (Walk.start_mem_support c)
    intro u w q hu
    induction q with
    | nil => exact hu
    | cons hadj _ ih => exact ih (Walk.snd_mem_support_of_mem_edges _ (hstep _ hu _ hadj))
  exact ⟨hsup, fun hadj => hstep _ (hsup _) _ hadj⟩

private lemma mem_darts_iff_exists_append {u v : V} {p : W.graph.Walk u v} {d : W.graph.Dart} :
    d ∈ p.darts ↔ ∃ (q₁ : W.graph.Walk u d.fst) (q₂ : W.graph.Walk d.snd v)
      (hadj : W.graph.Adj d.fst d.snd),
      d = ⟨(d.fst, d.snd), hadj⟩ ∧ p = q₁.append (.cons hadj q₂) := by
  constructor
  · induction p with
    | nil => simp
    | @cons a b c hadj p' ih =>
      intro hd
      rw [Walk.darts_cons, List.mem_cons] at hd
      rcases hd with rfl | hd'
      · exact ⟨.nil, p', hadj, rfl, rfl⟩
      · obtain ⟨q₁, q₂, hadj', hd_eq, hp'⟩ := ih hd'
        exact ⟨.cons hadj q₁, q₂, hadj', hd_eq, hp' ▸ (Walk.cons_append hadj q₁ _).symm⟩
  · rintro ⟨q₁, q₂, hadj, hd_eq, rfl⟩
    rw [Walk.darts_append, List.mem_append, Walk.darts_cons]
    exact Or.inr (List.mem_cons.mpr (Or.inl hd_eq))

private lemma circleMap_append_cons_mul {v₀ : V} {c : W.graph.Walk v₀ v₀} (hc : c.IsCycle)
    {d : W.graph.Dart} (q₁ : W.graph.Walk v₀ d.fst) (q₂ : W.graph.Walk d.snd v₀)
    (hadj : W.graph.Adj d.fst d.snd) (hd : d = ⟨(d.fst, d.snd), hadj⟩)
    (hc_eq : c = q₁.append (.cons hadj q₂)) (u : unitInterval) :
    circleMap hc (walkLength W.weight q₁ + (u : ℝ) * W.weight d.edge) = edgePoint d u := by
  have hw_le : 0 ≤ (u : ℝ) * W.weight d.edge := mul_nonneg u.property.1 (W.dart_weight_pos d).le
  have hsl : walkLength W.weight q₁ + (u : ℝ) * W.weight d.edge ≤ walkLength W.weight c := by
    have h := congrArg (walkLength W.weight) hc_eq
    rw [walkLength_append, walkLength_cons] at h
    have hwe : W.weight s(d.fst, d.snd) = W.weight d.edge := rfl
    rw [hwe] at h
    nlinarith [u.property.2, (W.dart_weight_pos d).le,
      walkLength_nonneg W.weight W.weight_nonneg q₂]
  rw [circleMap_eq_walkPoint hc (add_nonneg (walkLength_nonneg _ W.weight_nonneg _) hw_le) hsl]
  conv_lhs => arg 1; rw [hc_eq]
  rw [walkPoint_append_of_ge _ _ hw_le]
  exact walkPoint_cons_mul hadj q₂ d hd u

private lemma circleMap_rotate_eq [DecidableEq V] {v₀ v : V} {c : W.graph.Walk v₀ v₀}
    (hc : c.IsCycle) (hv : v ∈ c.support) (r : ℝ) :
    circleMap hc (cycCoord c v + r) = circleMap ((c.isCycle_rotate hv).mpr hc) r := by
  let L := walkLength W.weight c
  have hL : 0 < L := walkLength_pos_of_not_nil hc.not_nil
  let c_v := c.rotate v hv
  have hc_v : c_v.IsCycle := (c.isCycle_rotate hv).mpr hc
  have hLv : walkLength W.weight c_v = L := walkLength_perm_eq W.weight (c.rotate_edges v hv).perm
  wlog hr : 0 ≤ r ∧ r < L generalizing r
  · have hq_eq := eq_fract_mul_add_floor_mul hL r
    conv_lhs => rw [hq_eq, ← add_assoc, circleMap_add_int_mul hc _ ⌊r / L⌋]
    have hrhs : circleMap hc_v r = circleMap hc_v (Int.fract (r / L) * L) := by
      conv_lhs => rw [hq_eq]
      simpa only [hLv] using circleMap_add_int_mul hc_v (Int.fract (r / L) * L) ⌊r / L⌋
    rw [hrhs]
    exact this _ (fract_mul_mem_Ico hL _)
  let c₁ := c.takeUntil v hv
  let c₂ := c.dropUntil v hv
  have hc_eq : c₁.append c₂ = c := c.take_spec hv
  have hsum : walkLength W.weight c₁ + walkLength W.weight c₂ = L := by
    rw [← walkLength_append, hc_eq]
  have hc₁_nn := walkLength_nonneg W.weight W.weight_nonneg c₁
  have hc₂_nn := walkLength_nonneg W.weight W.weight_nonneg c₂
  rw [circleMap_eq_walkPoint hc_v hr.1 (hLv.symm ▸ hr.2.le), cycCoord_of_mem hv]
  by_cases hlt : walkLength W.weight c₁ + r < L
  · rw [circleMap_eq_walkPoint hc (by linarith) hlt.le]
    conv_lhs => arg 1; rw [← hc_eq]
    rw [walkPoint_append_of_ge c₁ c₂ hr.1,
      show c_v = c₂.append c₁ from rfl, walkPoint_append_of_le c₂ c₁ (by linarith)]
  · have hsub0 : 0 ≤ r - walkLength W.weight c₂ := by linarith
    have hsubL : r - walkLength W.weight c₂ ≤ walkLength W.weight c₁ := by linarith
    rw [show walkLength W.weight c₁ + r = (r - walkLength W.weight c₂) + (1 : ℤ) * L by
        push_cast; linarith,
      circleMap_add_int_mul hc _ 1, circleMap_eq_walkPoint hc hsub0 (by linarith)]
    conv_lhs => arg 1; rw [← hc_eq]
    rw [walkPoint_append_of_le c₁ c₂ hsubL, show c_v = c₂.append c₁ from rfl]
    conv_rhs => arg 2; rw [show r = walkLength W.weight c₂ + (r - walkLength W.weight c₂) by ring]
    rw [walkPoint_append_of_ge c₂ c₁ hsub0]

theorem circleMap_surjective_of_cycleGraph {n : ℕ}
    (e : W.graph ≃g cycleGraph (n + 3)) {v₀ : V} {c : W.graph.Walk v₀ v₀} (hc : c.IsCycle) :
    Function.Surjective (circleMap hc) := by
  classical
  obtain ⟨hsup, hedges⟩ := cycleGraph_support_of_isCycle e hc
  intro p
  induction p using ind with
  | vertex v =>
    refine ⟨cycCoord c v, ?_⟩
    rw [← add_zero (cycCoord c v), circleMap_rotate_eq hc (hsup v), circleMap_zero]
  | edgePoint d t ht0 ht1 =>
    have hed : d.edge ∈ c.edges := hedges d.adj
    rw [Walk.edges, List.mem_map] at hed
    obtain ⟨d', hd'_mem, hd'_edge⟩ := hed
    obtain ⟨q₁, q₂, hadj, hd'_eq, hc_eq⟩ := mem_darts_iff_exists_append.mp hd'_mem
    have hpt := circleMap_append_cons_mul hc q₁ q₂ hadj hd'_eq hc_eq
    rcases (dart_edge_eq_iff d' d).mp hd'_edge with rfl | hsymm
    · exact ⟨_, hpt t⟩
    · exact ⟨_, (hpt (unitInterval.symm t)).trans (by rw [hsymm, edgePoint_symm])⟩

private lemma circleMap_local_vertex [DecidableEq V] {v₀ : V} {c : W.graph.Walk v₀ v₀}
    (hc : c.IsCycle) {s : ℝ} (v : V) (hv : v ∈ c.support) (k : ℤ)
    (hcoord : s = cycCoord c v + (k : ℝ) * walkLength W.weight c) :
    ∃ (v' : V) (d₁ d₂ : W.graph.Dart) (δ : ℝ),
      v' ∈ c.support ∧ d₁.fst = v' ∧ d₂.fst = v' ∧ d₁.edge ≠ d₂.edge ∧
      d₁.edge ∈ c.edges ∧ d₂.edge ∈ c.edges ∧ circleMap hc s = vertex v' ∧ 0 < δ ∧
      ∀ r ∈ Set.Ioc 0 δ, r < W.weight d₁.edge ∧ r < W.weight d₂.edge ∧
        ∃ (h10 : 0 ≤ r / W.weight d₁.edge) (h11 : r / W.weight d₁.edge ≤ 1)
          (h20 : 0 ≤ r / W.weight d₂.edge) (h21 : r / W.weight d₂.edge ≤ 1),
          circleMap hc (s - r) = edgePoint d₁ ⟨r / W.weight d₁.edge, h10, h11⟩ ∧
          circleMap hc (s + r) = edgePoint d₂ ⟨r / W.weight d₂.edge, h20, h21⟩ := by
  let L := walkLength W.weight c
  let c_v := c.rotate v hv
  have hc_v : c_v.IsCycle := (c.isCycle_rotate hv).mpr hc
  have hLv : walkLength W.weight c_v = L := walkLength_perm_eq W.weight (c.rotate_edges v hv).perm
  cases hc_v_c : c_v with
  | nil => exact absurd (hc_v_c ▸ Walk.Nil.nil) hc_v.not_nil
  | @cons _ b₀ _ hadj2 q_v =>
    let d₂ : W.graph.Dart := ⟨(v, b₀), hadj2⟩
    obtain ⟨d₁, hd₁_fst, hd₁_edge, hlast⟩ :=
      walkPoint_last_sub q_v (Walk.not_nil_of_isCycle_cons (hc_v_c ▸ hc_v))
    have hnd := (hc_v_c ▸ hc_v).isTrail.edges_nodup
    rw [Walk.edges_cons, List.nodup_cons] at hnd
    have hd₁₂ : d₁.edge ≠ d₂.edge := fun he => by rw [he] at hd₁_edge; exact hnd.1 hd₁_edge
    have hmem_c : ∀ e ∈ (Walk.cons hadj2 q_v).edges, e ∈ c.edges := fun e he => by
      refine (c.rotate_edges v hv).perm.mem_iff.mp ?_
      change e ∈ c_v.edges
      rwa [hc_v_c]
    have hw1 := W.dart_weight_pos d₁
    have hw2 := W.dart_weight_pos d₂
    let δ := min (W.weight d₁.edge) (W.weight d₂.edge) / 2
    have hq_ge1 := weight_le_walkLength_of_mem_edges q_v hd₁_edge
    have hL_tot : walkLength W.weight c_v = W.weight d₂.edge + walkLength W.weight q_v := by
      rw [hc_v_c, walkLength_cons]; rfl
    have hs_v : circleMap hc s = vertex v := by
      rw [hcoord, circleMap_add_int_mul hc _ k, ← add_zero (cycCoord c v),
        circleMap_rotate_eq hc hv, circleMap_zero]
    refine ⟨v, d₁, d₂, δ, hv, hd₁_fst, rfl, hd₁₂,
      hmem_c _ (List.mem_cons_of_mem _ hd₁_edge), hmem_c _ List.mem_cons_self,
      hs_v, by dsimp only [δ]; positivity, fun r hr => ?_⟩
    obtain ⟨hr1, hr2⟩ : r < W.weight d₁.edge ∧ r < W.weight d₂.edge := by
      have hrδ : r ≤ min (W.weight d₁.edge) (W.weight d₂.edge) / 2 := hr.2
      constructor <;> linarith [hr.1, min_le_left (W.weight d₁.edge) (W.weight d₂.edge),
        min_le_right (W.weight d₁.edge) (W.weight d₂.edge)]
    refine ⟨hr1, hr2, div_nonneg hr.1.le hw1.le, (div_le_one hw1).mpr hr1.le,
      div_nonneg hr.1.le hw2.le, (div_le_one hw2).mpr hr2.le, ?_, ?_⟩
    · rw [show s - r = cycCoord c v + (-r) + (k : ℝ) * L by rw [hcoord]; ring,
        circleMap_add_int_mul hc _ k, circleMap_rotate_eq hc hv,
        ← circleMap_add_int_mul hc_v (-r) 1, Int.cast_one, one_mul,
        circleMap_eq_walkPoint hc_v (by linarith [hr.1]) (by linarith [hr.1]),
        neg_add_eq_sub, hL_tot, hc_v_c, add_sub_assoc,
        walkPoint_cons_of_gt hadj2 q_v d₂ rfl (by linarith), add_sub_cancel_left]
      exact hlast hr.1 hr1.le (div_nonneg hr.1.le hw1.le) ((div_le_one hw1).mpr hr1.le)
    · rw [show s + r = cycCoord c v + r + (k : ℝ) * L by rw [hcoord]; ring,
        circleMap_add_int_mul hc _ k, circleMap_rotate_eq hc hv,
        circleMap_eq_walkPoint hc_v hr.1.le (by linarith), hc_v_c]
      exact walkPoint_cons_of_le hadj2 q_v d₂ rfl hr.1.le hr2.le
        (div_nonneg hr.1.le hw2.le) ((div_le_one hw2).mpr hr2.le)

/-- Every parameter `s : ℝ` along a cycle `c` maps either to the interior of a unique cycle dart
(where `circleMap hc` is locally affine along that dart) or to a vertex `v ∈ c.support` whose
incoming and outgoing cycle darts carry distinct edges. -/
theorem circleMap_local_dichotomy {v₀ : V} {c : W.graph.Walk v₀ v₀} (hc : c.IsCycle) (s : ℝ) :
    (∃ (d : W.graph.Dart) (t δ : ℝ), d ∈ c.darts ∧ 0 < t ∧ t < 1 ∧ 0 < δ ∧
      ∀ r ∈ Set.Icc (-δ) δ, 0 < t + r / W.weight d.edge ∧ t + r / W.weight d.edge < 1 ∧
        ∃ h0 : 0 ≤ t + r / W.weight d.edge, ∃ h1 : t + r / W.weight d.edge ≤ 1,
          circleMap hc (s + r) = edgePoint d ⟨t + r / W.weight d.edge, h0, h1⟩) ∨
    (∃ (v : V) (d₁ d₂ : W.graph.Dart) (δ : ℝ),
      v ∈ c.support ∧ d₁.fst = v ∧ d₂.fst = v ∧ d₁.edge ≠ d₂.edge ∧
      d₁.edge ∈ c.edges ∧ d₂.edge ∈ c.edges ∧ circleMap hc s = vertex v ∧ 0 < δ ∧
      ∀ r ∈ Set.Ioc 0 δ, r < W.weight d₁.edge ∧ r < W.weight d₂.edge ∧
        ∃ (h10 : 0 ≤ r / W.weight d₁.edge) (h11 : r / W.weight d₁.edge ≤ 1)
          (h20 : 0 ≤ r / W.weight d₂.edge) (h21 : r / W.weight d₂.edge ≤ 1),
          circleMap hc (s - r) = edgePoint d₁ ⟨r / W.weight d₁.edge, h10, h11⟩ ∧
          circleMap hc (s + r) = edgePoint d₂ ⟨r / W.weight d₂.edge, h20, h21⟩) := by
  classical
  let L := walkLength W.weight c
  have hL : 0 < L := walkLength_pos_of_not_nil hc.not_nil
  let r₀ := Int.fract (s / L) * L
  obtain ⟨hr₀0, hr₀L⟩ : 0 ≤ r₀ ∧ r₀ < L := fract_mul_mem_Ico hL _
  obtain ⟨d, q₁, q₂, hadj, t, hd, hc_eq, _, hr_eq⟩ :=
    walkPoint_dart_decomp c hc.not_nil (s := r₀) hr₀0 hr₀L.le
  have hwpos := W.dart_weight_pos d
  have hs_r₀ : s = r₀ + (⌊s / L⌋ : ℝ) * L := eq_fract_mul_add_floor_mul hL s
  by_cases ht0 : (t : ℝ) = 0
  · exact Or.inr (circleMap_local_vertex hc d.fst
      (hc_eq ▸ Walk.support_subset_support_append_left _ _ q₁.end_mem_support) ⌊s / L⌋ (by
        conv_lhs => rw [hs_r₀]
        rw [hr_eq, ht0, zero_mul, add_zero, cycCoord_append_eq hc hc_eq Walk.not_nil_cons]))
  by_cases ht1 : (t : ℝ) = 1
  · rcases cycCoord_snd_of_append_cons hc q₁ q₂ hadj hc_eq with ⟨hlen_c, _⟩ | hcoord_snd
    · exfalso; rw [ht1, one_mul] at hr_eq; linarith
    · exact Or.inr (circleMap_local_vertex hc d.snd
        (hc_eq ▸ Walk.support_subset_support_append_right _ _
          (List.mem_cons_of_mem _ (Walk.start_mem_support _)))
        ⌊s / L⌋ (by conv_lhs => rw [hs_r₀]; rw [hr_eq, ht1, one_mul, ← hcoord_snd]))
  have ht_pos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht0)
  have ht_lt1 : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 ht1
  have h1t : 0 < (1 - (t : ℝ)) * W.weight d.edge := mul_pos (sub_pos.mpr ht_lt1) hwpos
  let δ := min ((t : ℝ) * W.weight d.edge) ((1 - (t : ℝ)) * W.weight d.edge) / 2
  refine Or.inl ⟨d, (t : ℝ), δ, mem_darts_iff_exists_append.mpr ⟨q₁, q₂, hadj, hd, hc_eq⟩,
    ht_pos, ht_lt1, by dsimp only [δ]; positivity, fun r hr => ?_⟩
  have h2δ : 2 * δ = min ((t : ℝ) * W.weight d.edge) ((1 - (t : ℝ)) * W.weight d.edge) := by
    dsimp only [δ]; ring
  have hδl : 2 * δ ≤ (t : ℝ) * W.weight d.edge := h2δ ▸ min_le_left _ _
  have hδr : 2 * δ ≤ (1 - (t : ℝ)) * W.weight d.edge := h2δ ▸ min_le_right _ _
  have htr : (t : ℝ) + r / W.weight d.edge =
      ((t : ℝ) * W.weight d.edge + r) / W.weight d.edge := by
    rw [add_div, mul_div_cancel_right₀ _ hwpos.ne']
  have hdiv_lo : 0 < (t : ℝ) + r / W.weight d.edge :=
    htr ▸ div_pos (by linarith [hr.1, mul_pos ht_pos hwpos]) hwpos
  have hdiv_hi : (t : ℝ) + r / W.weight d.edge < 1 :=
    htr ▸ (div_lt_one hwpos).mpr (by linarith [hr.2])
  refine ⟨hdiv_lo, hdiv_hi, hdiv_lo.le, hdiv_hi.le, ?_⟩
  have hs_add : s + r =
      (walkLength W.weight q₁ + ((t : ℝ) + r / W.weight d.edge) * W.weight d.edge) +
        (⌊s / L⌋ : ℝ) * L := by
    conv_lhs => rw [hs_r₀]
    rw [hr_eq, add_mul, div_mul_cancel₀ _ hwpos.ne']; ring
  rw [hs_add, circleMap_add_int_mul hc _ ⌊s / L⌋]
  exact circleMap_append_cons_mul hc q₁ q₂ hadj hd hc_eq
    ⟨(t : ℝ) + r / W.weight d.edge, hdiv_lo.le, hdiv_hi.le⟩

end CycleStructure

end MetricGraph

end SimpleGraph
