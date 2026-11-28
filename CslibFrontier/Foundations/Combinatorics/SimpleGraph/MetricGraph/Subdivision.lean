/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/MetricGraph/Subdivision.lean`)

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Geodesic
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# Subdivisions of metric graphs and piecewise-affine distance

This module constructs arbitrary finite vertex subdivisions of a `WeightedGraph`, establishes the
isometric equivalence `MetricGraph (subdivide W B hV) ≃ᵢ MetricGraph W`, and proves that the
distance from any fixed point `p : MetricGraph W` is affine along every subdivided edge once the
subdivision includes the distance breakpoints (at most three per edge). The STOC 2027
submission 1056 reference (Definition 5.1 / Lemma 5.2) comes from Issue #4324 context and was
not verified against the primary manuscript.

## Main definitions

* `SimpleGraph.MetricGraph.subdivide`: subdivide a weighted graph `W` at a finite set of points
  `B : Finset (MetricGraph W)` containing all original vertices.
* `SimpleGraph.MetricGraph.subdivideEquiv`: the isometric equivalence
  `MetricGraph (subdivide W B hV) ≃ᵢ MetricGraph W`.
* `SimpleGraph.MetricGraph.pointBreakpoints`: a finite set containing all vertices and at most
  three interior breakpoints per edge where `t ↦ dist p (edgePoint d t)` changes slope.

## Main results

* `SimpleGraph.MetricGraph.vertexDist_subdivide`: vertex distances in `subdivide W B hV` agree
  with geodesic distances in `MetricGraph W`.
* `SimpleGraph.MetricGraph.subdivideEquiv_vertex`,
  `SimpleGraph.MetricGraph.subdivideEquiv_edgePoint`: explicit evaluation of `subdivideEquiv`.
* `SimpleGraph.MetricGraph.dist_subdivide_edgePoint_affine`: for any subdivision containing
  `pointBreakpoints W p`, the distance from `p` is affine along every subdivided edge.
-/

public section

open scoped unitInterval

namespace SimpleGraph

namespace MetricGraph

universe u

variable {V : Type u} {W : WeightedGraph V}

/-! ### Subdivision graph and weights -/

/-- Two distinct points `x, y ∈ B` are adjacent in the `B`-subdivision if they lie at `s < t`
along some dart `d` of `W` with no point of `B` strictly between them on `d`. -/
@[expose] def SubAdj (W : WeightedGraph V) (B : Finset (MetricGraph W))
    (x y : { z : MetricGraph W // z ∈ B }) : Prop :=
  x ≠ y ∧ ∃ (d : W.graph.Dart) (s t : unitInterval),
    (s : ℝ) < t ∧ edgePoint d s = x.val ∧ edgePoint d t = y.val ∧
      ∀ r : unitInterval, (s : ℝ) < r → (r : ℝ) < t → edgePoint d r ∉ B

theorem subAdj_symm {B : Finset (MetricGraph W)}
    {x y : { z : MetricGraph W // z ∈ B }} (h : SubAdj W B x y) :
    SubAdj W B y x := by
  rcases h with ⟨hne, d, s, t, hst, hs, ht, hmid⟩
  refine ⟨hne.symm, d.symm, unitInterval.symm t, unitInterval.symm s, ?_,
    (edgePoint_symm d t).trans ht, (edgePoint_symm d s).trans hs, fun r hr1 hr2 hrB => ?_⟩
  · simp only [unitInterval.coe_symm_eq]; linarith
  · simp only [unitInterval.coe_symm_eq] at hr1 hr2
    exact hmid (unitInterval.symm r) (by simp only [unitInterval.coe_symm_eq]; linarith)
      (by simp only [unitInterval.coe_symm_eq]; linarith)
      (by simpa only [edgePoint_symm'] using hrB)

/-- Two strictly ordered endpoint witnesses along darts of `W` that represent the same ordered
pair of points must agree on the dart and both parameters. -/
theorem subAdj_witness_eq {d₁ d₂ : W.graph.Dart} {s₁ t₁ s₂ t₂ : unitInterval}
    (hs₁ : (s₁ : ℝ) < t₁) (hs₂ : (s₂ : ℝ) < t₂)
    (heq₁ : edgePoint d₁ s₁ = (edgePoint d₂ s₂ : MetricGraph W))
    (heq₂ : edgePoint d₁ t₁ = (edgePoint d₂ t₂ : MetricGraph W)) :
    d₁ = d₂ ∧ s₁ = s₂ ∧ t₁ = t₂ := by
  have ht10 : 0 < (t₁ : ℝ) := lt_of_le_of_lt s₁.property.1 hs₁
  have hs11 : (s₁ : ℝ) < 1 := lt_of_lt_of_le hs₁ t₁.property.2
  have interior_edge {r₁ r₂ : unitInterval} (hr0 : 0 < (r₁ : ℝ)) (hr1 : (r₁ : ℝ) < 1)
      (heq : edgePoint d₁ r₁ = (edgePoint d₂ r₂ : MetricGraph W)) : d₁.edge = d₂.edge := by
    rcases edgePoint_eq_edgePoint_iff.mp heq with
      ⟨h1, _⟩ | ⟨h2, _⟩ | ⟨_, _, _, _, ⟨heq', _⟩ | ⟨hsym, _⟩⟩
    · exact absurd (congrArg Subtype.val h1) hr0.ne'
    · exact absurd (congrArg Subtype.val h2) hr1.ne
    · exact congrArg Dart.edge heq'
    · exact hsym ▸ d₂.edge_symm
  have he : d₁.edge = d₂.edge := by
    by_cases ht1 : (t₁ : ℝ) < 1
    · exact interior_edge ht10 ht1 heq₂
    · by_cases hs10 : 0 < (s₁ : ℝ)
      · exact interior_edge hs10 hs11 heq₁
      · have hs1eq : s₁ = 0 := Subtype.ext (le_antisymm (not_lt.mp hs10) s₁.property.1)
        have ht1eq : t₁ = 1 := Subtype.ext (le_antisymm t₁.property.2 (not_lt.mp ht1))
        subst hs1eq ht1eq
        rcases edgePoint_eq_vertex_iff.mp (heq₁.symm.trans (edgePoint_zero d₁)) with
          ⟨h0, hf1⟩ | ⟨h1, _⟩ <;>
          rcases edgePoint_eq_vertex_iff.mp (heq₂.symm.trans (edgePoint_one d₁)) with
            ⟨h0', _⟩ | ⟨h1', hs2⟩
        · rw [h0, h0'] at hs₂; exact absurd hs₂ (lt_irrefl _)
        · rw [← Dart.sym2Mk_fst_snd d₁, ← Dart.sym2Mk_fst_snd d₂, hf1, hs2]
        · have : (s₂ : ℝ) = 1 := congrArg Subtype.val h1
          have : (t₂ : ℝ) = 0 := congrArg Subtype.val h0'
          linarith
        · rw [h1, h1'] at hs₂; exact absurd hs₂ (lt_irrefl _)
  rcases (dart_edge_eq_iff d₁ d₂).mp he with rfl | rfl
  · exact ⟨rfl, edgePoint_injective d₁ heq₁, edgePoint_injective d₁ heq₂⟩
  · have hs' := edgePoint_injective d₂.symm (heq₁.trans (edgePoint_symm d₂ s₂).symm)
    have ht' := edgePoint_injective d₂.symm (heq₂.trans (edgePoint_symm d₂ t₂).symm)
    have hlt : 1 - (s₂ : ℝ) < 1 - (t₂ : ℝ) := by
      simpa only [← unitInterval.coe_symm_eq, ← hs', ← ht'] using hs₁
    linarith

private theorem subAdj_witness_sym2_len {x y : MetricGraph W} (_hne : x ≠ y)
    {d₁ d₂ : W.graph.Dart} {s₁ t₁ s₂ t₂ : unitInterval}
    (hs₁ : (s₁ : ℝ) < t₁) (hs₂ : (s₂ : ℝ) < t₂)
    (heq₁ : s(edgePoint d₁ s₁, edgePoint d₁ t₁) = s(x, y))
    (heq₂ : s(edgePoint d₂ s₂, edgePoint d₂ t₂) = s(x, y)) :
    ((t₁ : ℝ) - s₁) * W.weight d₁.edge = ((t₂ : ℝ) - s₂) * W.weight d₂.edge := by
  have heq : s(edgePoint d₁ s₁, edgePoint d₁ t₁) = s(edgePoint d₂ s₂, edgePoint d₂ t₂) :=
    heq₁.trans heq₂.symm
  rcases Sym2.eq_iff.mp heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨rfl, rfl, rfl⟩ := subAdj_witness_eq hs₁ hs₂ ha hb
    rfl
  · rw [← edgePoint_symm d₂ s₂] at hb
    rw [← edgePoint_symm d₂ t₂] at ha
    have hs₂' : (unitInterval.symm t₂ : ℝ) < unitInterval.symm s₂ := by
      change 1 - (t₂ : ℝ) < 1 - s₂; linarith
    obtain ⟨rfl, rfl, rfl⟩ := subAdj_witness_eq hs₁ hs₂' ha hb
    simp only [unitInterval.coe_symm_eq, Dart.edge_symm]
    ring

open Classical in
/-- Weight of a subdivided edge in `subdivide`: `(t - s) * W.weight d.edge`. -/
noncomputable def subWeight (W : WeightedGraph V) (B : Finset (MetricGraph W))
    (e : Sym2 { z : MetricGraph W // z ∈ B }) : ℝ :=
  if h : ∃ (d : W.graph.Dart) (s t : unitInterval),
      (s : ℝ) < t ∧ s(edgePoint d s, edgePoint d t) = Sym2.map Subtype.val e
  then
    let d := Classical.choose h
    let s := Classical.choose (Classical.choose_spec h)
    let t := Classical.choose (Classical.choose_spec (Classical.choose_spec h))
    ((t : ℝ) - s) * W.weight d.edge
  else 1

theorem subWeight_eq_of_witness {B : Finset (MetricGraph W)}
    {x y : { z : MetricGraph W // z ∈ B }} (hne : x.val ≠ y.val)
    {d : W.graph.Dart} {s t : unitInterval} (hst : (s : ℝ) < t)
    (hs : edgePoint d s = x.val) (ht : edgePoint d t = y.val) :
    subWeight W B s(x, y) = ((t : ℝ) - s) * W.weight d.edge := by
  classical
  have hex : ∃ (d₀ : W.graph.Dart) (s₀ t₀ : unitInterval),
      (s₀ : ℝ) < t₀ ∧ s(edgePoint d₀ s₀, edgePoint d₀ t₀) = Sym2.map Subtype.val s(x, y) :=
    ⟨d, s, t, hst, by change s(edgePoint d s, edgePoint d t) = s(x.val, y.val); rw [hs, ht]⟩
  simp only [subWeight, hex, ↓reduceDIte]
  have hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hex))
  have hsym2 : s(edgePoint (Classical.choose hex) (Classical.choose (Classical.choose_spec hex)),
      edgePoint (Classical.choose hex)
        (Classical.choose (Classical.choose_spec (Classical.choose_spec hex)))) =
      s(x.val, y.val) := by
    change _ = Sym2.map Subtype.val s(x, y)
    exact hspec.2
  exact subAdj_witness_sym2_len hne hspec.1 hst hsym2 (by rw [hs, ht])

private def subdivideGraph (W : WeightedGraph V) (B : Finset (MetricGraph W)) :
    SimpleGraph { z : MetricGraph W // z ∈ B } where
  Adj := SubAdj W B
  symm := ⟨fun _ _ h => subAdj_symm h⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Along dart `d`, there is a walk in the `B`-subdivision between any two points `s ≤ t`
of `B` on `d`, of total length `(t - s) * W.weight d.edge`. -/
private theorem exists_walk_along_dart {B : Finset (MetricGraph W)}
    (d : W.graph.Dart) (s t : unitInterval)
    (hs : edgePoint d s ∈ B) (ht : edgePoint d t ∈ B) (hle : (s : ℝ) ≤ t) :
    ∃ p : (subdivideGraph W B).Walk ⟨edgePoint d s, hs⟩ ⟨edgePoint d t, ht⟩,
      walkLength (subWeight W B) p = ((t : ℝ) - s) * W.weight d.edge := by
  classical
  let P (s : unitInterval) : Finset unitInterval :=
    (B.preimage (edgePoint d) (edgePoint_injective d).injOn).filter
      (fun r => (s : ℝ) < r ∧ (r : ℝ) ≤ t)
  have hmain : ∀ n s (hs : edgePoint d s ∈ B) (hle : (s : ℝ) ≤ t), (P s).card ≤ n →
      ∃ p : (subdivideGraph W B).Walk ⟨edgePoint d s, hs⟩ ⟨edgePoint d t, ht⟩,
        walkLength (subWeight W B) p = ((t : ℝ) - s) * W.weight d.edge := by
    intro n
    induction n with
    | zero =>
      intro s hs hle hcard
      have heq : s = t := Subtype.ext <| le_antisymm hle <| not_lt.mp fun hst => by
        have hpos : 0 < (P s).card :=
          Finset.card_pos.mpr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_preimage.mpr ht, hst, le_rfl⟩⟩
        omega
      subst heq; exact ⟨Walk.nil, by simp⟩
    | succ n ih =>
      intro s hs hle hcard
      by_cases hst : (s : ℝ) < t
      · have htP : t ∈ P s := Finset.mem_filter.mpr ⟨Finset.mem_preimage.mpr ht, hst, le_rfl⟩
        let rmin := (P s).min' ⟨t, htP⟩
        have hrP := Finset.mem_filter.mp ((P s).min'_mem ⟨t, htP⟩)
        have hrB : edgePoint d rmin ∈ B := Finset.mem_preimage.mp hrP.1
        have hsr : (s : ℝ) < rmin := hrP.2.1
        have hrt : (rmin : ℝ) ≤ t := hrP.2.2
        have hno : ∀ r : unitInterval, (s : ℝ) < r → (r : ℝ) < rmin → edgePoint d r ∉ B :=
          fun r h1 h2 hr => not_le.mpr h2 <| (P s).min'_le r
            (Finset.mem_filter.mpr ⟨Finset.mem_preimage.mpr hr, h1, h2.le.trans hrt⟩)
        have hsub : P rmin ⊂ P s := Finset.ssubset_iff_subset_ne.mpr
          ⟨fun r hr => by rcases Finset.mem_filter.mp hr with ⟨hr1, h1, h2⟩
                          exact Finset.mem_filter.mpr ⟨hr1, hsr.trans h1, h2⟩,
           fun heq => by have hm : rmin ∈ P s := (P s).min'_mem ⟨t, htP⟩
                         rw [← heq] at hm
                         exact (Finset.mem_filter.mp hm).2.1.false⟩
        obtain ⟨q, hq⟩ := ih rmin hrB hrt
          (Nat.lt_succ_iff.mp ((Finset.card_lt_card hsub).trans_le hcard))
        have hne : (edgePoint d s : MetricGraph W) ≠ edgePoint d rmin :=
          fun h => hsr.ne (congrArg Subtype.val (edgePoint_injective d h))
        have hadj : (subdivideGraph W B).Adj ⟨edgePoint d s, hs⟩ ⟨edgePoint d rmin, hrB⟩ :=
          ⟨fun h => hne (congrArg Subtype.val h), d, s, rmin, hsr, rfl, rfl, hno⟩
        refine ⟨Walk.cons hadj q, ?_⟩
        rw [walkLength_cons, hq, subWeight_eq_of_witness hne hsr rfl rfl]; ring
      · have heq : s = t := Subtype.ext (le_antisymm hle (not_lt.mp hst))
        subst heq; exact ⟨Walk.nil, by simp⟩
  exact hmain (P s).card s hs hle le_rfl

/-- Subdivide a connected weighted graph `W` at a finite set of points `B` containing
all original vertices. -/
noncomputable def subdivide (W : WeightedGraph V)
    (B : Finset (MetricGraph W)) (hV : ∀ v : V, vertex v ∈ B) :
    WeightedGraph { z : MetricGraph W // z ∈ B } where
  graph := subdivideGraph W B
  weight := subWeight W B
  weight_pos {x y} h := by
    rcases h with ⟨hne, d, s, t, hst, hs, ht, _⟩
    rw [subWeight_eq_of_witness (fun h1 => hne (Subtype.ext h1)) hst hs ht]
    exact mul_pos (sub_pos.mpr hst) (W.dart_weight_pos d)
  connected := by
    classical
    rw [connected_iff_exists_forall_reachable]
    obtain ⟨v₀⟩ := W.connected.nonempty
    refine ⟨⟨vertex v₀, hV v₀⟩, fun ⟨x, hx⟩ => ?_⟩
    have hVreach : ∀ u : V,
        (subdivideGraph W B).Reachable ⟨vertex v₀, hV v₀⟩ ⟨vertex u, hV u⟩ := fun u => by
      obtain ⟨p⟩ := W.connected v₀ u
      induction p with
      | nil => exact Reachable.refl _
      | cons h _ ih =>
        let d : W.graph.Dart := ⟨(_, _), h⟩
        have h0 : edgePoint d 0 = (vertex d.fst : MetricGraph W) := edgePoint_zero d
        have h1 : edgePoint d 1 = (vertex d.snd : MetricGraph W) := edgePoint_one d
        obtain ⟨q, _⟩ := exists_walk_along_dart d 0 1 (h0 ▸ hV d.fst) (h1 ▸ hV d.snd) zero_le_one
        have hq' : (subdivideGraph W B).Reachable ⟨edgePoint d 0, h0 ▸ hV d.fst⟩
            ⟨edgePoint d 1, h1 ▸ hV d.snd⟩ := ⟨q⟩
        rw [show (⟨edgePoint d 0, h0 ▸ hV d.fst⟩ : { z // z ∈ B }) = ⟨vertex d.fst, hV d.fst⟩
            from Subtype.ext h0,
          show (⟨edgePoint d 1, h1 ▸ hV d.snd⟩ : { z // z ∈ B }) = ⟨vertex d.snd, hV d.snd⟩
            from Subtype.ext h1] at hq'
        exact hq'.trans ih
    induction x using ind_simple with
    | vertex u => exact hVreach u
    | edgePoint d s =>
      have h0 : edgePoint d 0 = (vertex d.fst : MetricGraph W) := edgePoint_zero d
      obtain ⟨q, _⟩ := exists_walk_along_dart d 0 s (h0 ▸ hV d.fst) hx s.property.1
      exact (hVreach d.fst).trans ⟨by simpa only [h0] using q⟩

@[simp]
theorem subdivide_adj_iff {B : Finset (MetricGraph W)} {hV : ∀ v, vertex v ∈ B}
    {x y : { z : MetricGraph W // z ∈ B }} :
    (subdivide W B hV).graph.Adj x y ↔ SubAdj W B x y := Iff.rfl

private theorem walk_in_subdivide_to_metric [Finite V] {B : Finset (MetricGraph W)}
    {hV : ∀ v, vertex v ∈ B} {x y : { z : MetricGraph W // z ∈ B }}
    (p : (subdivide W B hV).graph.Walk x y) :
    dist x.val y.val ≤ walkLength (subdivide W B hV).weight p := by
  induction p with
  | nil => simp
  | cons hadj q ih =>
    rename_i a c z
    have hhadj := hadj
    rcases hhadj with ⟨hne, d, s, t, hst, hs, ht, _⟩
    have hstep : dist a.val c.val ≤ (subdivide W B hV).weight s(a, c) := by
      change dist a.val c.val ≤ subWeight W B s(a, c)
      rw [subWeight_eq_of_witness (fun h1 => hne (Subtype.ext h1)) hst hs ht, ← hs, ← ht]
      exact (dist_edgePoint_self_le d s t).trans_eq <| by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst.le), mul_comm]
    change dist a.val z.val ≤ walkLength (subdivide W B hV).weight (Walk.cons hadj q)
    rw [walkLength_cons]
    exact (dist_triangle a.val c.val z.val).trans (add_le_add hstep ih)

private theorem vertexDist_subdivide_le_of_walk {B : Finset (MetricGraph W)}
    {hV : ∀ v, vertex v ∈ B} {u v : V} (p : W.graph.Walk u v) :
    vertexDist (subdivide W B hV).graph (subdivide W B hV).weight
        ⟨vertex u, hV u⟩ ⟨vertex v, hV v⟩ ≤ walkLength W.weight p := by
  classical
  induction p with
  | nil => simp [vertexDist_self (subdivide W B hV).weight_nonneg]
  | cons h q ih =>
    rename_i a c z
    rw [walkLength_cons]
    let d : W.graph.Dart := ⟨(a, c), h⟩
    have h0 : edgePoint d 0 = (vertex a : MetricGraph W) := edgePoint_zero d
    have h1 : edgePoint d 1 = (vertex c : MetricGraph W) := edgePoint_one d
    obtain ⟨p', hp'⟩ := exists_walk_along_dart (B := B) d 0 1 (h0 ▸ hV a) (h1 ▸ hV c) zero_le_one
    have hstep : vertexDist (subdivide W B hV).graph (subdivide W B hV).weight
        ⟨vertex a, hV a⟩ ⟨vertex c, hV c⟩ ≤ W.weight s(a, c) := by
      have hle : vertexDist (subdivide W B hV).graph (subdivide W B hV).weight
          ⟨edgePoint d 0, h0 ▸ hV a⟩ ⟨edgePoint d 1, h1 ▸ hV c⟩ ≤ W.weight s(a, c) :=
        (vertexDist_le (subdivide W B hV).weight_nonneg p').trans_eq <| by
          change walkLength (subWeight W B) p' = _; rw [hp']; simp [d]
      simpa only [h0, h1] using hle
    exact (vertexDist_triangle (subdivide W B hV).weight_nonneg
      ((subdivide W B hV).connected _ _) ((subdivide W B hV).connected _ _)).trans
      (add_le_add hstep ih)

/-- Vertex shortest-path distance in `subdivide W B hV` equals geodesic distance in
`MetricGraph W`. -/
theorem vertexDist_subdivide [Finite V] {B : Finset (MetricGraph W)}
    {hV : ∀ v : V, vertex v ∈ B} (x y : { z : MetricGraph W // z ∈ B }) :
    vertexDist (subdivide W B hV).graph (subdivide W B hV).weight x y = dist x.val y.val := by
  classical
  refine le_antisymm ?_ ?_
  · let D := vertexDist (subdivide W B hV).graph (subdivide W B hV).weight
    have hcomm (a b : { z : MetricGraph W // z ∈ B }) : D a b = D b a := vertexDist_comm a b
    have htri (a b c : { z : MetricGraph W // z ∈ B }) : D a c ≤ D a b + D b c :=
      vertexDist_triangle (subdivide W B hV).weight_nonneg
        ((subdivide W B hV).connected a b) ((subdivide W B hV).connected b c)
    have hVdist (u v : V) :
        D ⟨vertex u, hV u⟩ ⟨vertex v, hV v⟩ ≤ dist (vertex u : MetricGraph W) (vertex v) := by
      obtain ⟨p, -, hp⟩ := exists_isPath_walkLength_eq_vertexDist W.weight_nonneg (W.connected u v)
      rw [dist_vertex, ← hp]
      exact vertexDist_subdivide_le_of_walk p
    have hSameEdge (d : W.graph.Dart) (s t : unitInterval)
        (hs : edgePoint d s ∈ B) (ht : edgePoint d t ∈ B) :
        D ⟨edgePoint d s, hs⟩ ⟨edgePoint d t, ht⟩ ≤ |(s : ℝ) - t| * W.weight d.edge := by
      wlog hst : (s : ℝ) ≤ t generalizing s t
      · rw [hcomm, abs_sub_comm]
        exact this t s ht hs (le_of_not_ge hst)
      obtain ⟨p', hp'⟩ := exists_walk_along_dart d s t hs ht hst
      exact (vertexDist_le (subdivide W B hV).weight_nonneg p').trans_eq <| hp'.trans <| by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)]
    -- From `x` to an endpoint of `d`, then along `d`.
    have hvia (x : { z : MetricGraph W // z ∈ B })
        (hx : ∀ v, D x ⟨vertex v, hV v⟩ ≤ dist x.val (vertex v))
        (d : W.graph.Dart) (t : unitInterval) (ht : edgePoint d t ∈ B) :
        D x ⟨edgePoint d t, ht⟩ ≤ min (dist x.val (vertex d.fst) + (t : ℝ) * W.weight d.edge)
          (dist x.val (vertex d.snd) + (1 - (t : ℝ)) * W.weight d.edge) := by
      have h0 := hSameEdge d 0 t (edgePoint_zero d ▸ hV d.fst) ht
      have h1 := hSameEdge d 1 t (edgePoint_one d ▸ hV d.snd) ht
      simp only [edgePoint_zero, edgePoint_one, Set.Icc.coe_zero, Set.Icc.coe_one, zero_sub,
        abs_neg, abs_of_nonneg t.property.1, abs_of_nonneg (unitInterval.one_sub_nonneg t)] at h0 h1
      refine le_min ?_ ?_ <;> linarith [hx d.fst, hx d.snd,
        htri x ⟨_, hV d.fst⟩ ⟨_, ht⟩, htri x ⟨_, hV d.snd⟩ ⟨_, ht⟩]
    have hve (v : V) (y : { z : MetricGraph W // z ∈ B }) :
        D ⟨vertex v, hV v⟩ y ≤ dist (vertex v : MetricGraph W) y.val := by
      rcases y with ⟨py, hy⟩
      induction py using ind_simple with
      | vertex u => exact hVdist v u
      | edgePoint d t =>
        refine (hvia _ (hVdist v) d t hy).trans_eq ?_
        rw [dist_vertex_edgePoint, dist_vertex, dist_vertex]
    rcases x with ⟨px, hpx⟩
    induction px using ind_simple with
    | vertex u => exact hve u y
    | edgePoint d₁ t₁ =>
      have hx (v : V) :
          D ⟨edgePoint d₁ t₁, hpx⟩ ⟨vertex v, hV v⟩ ≤ dist (edgePoint d₁ t₁) (vertex v) := by
        rw [hcomm, dist_comm]
        exact hve v _
      rcases y with ⟨py, hy⟩
      induction py using ind_simple with
      | vertex v => exact hx v
      | edgePoint d₂ t₂ =>
        by_cases he : d₁.edge = d₂.edge
        · obtain ⟨r, hr⟩ : ∃ r, (edgePoint d₁ t₁ : MetricGraph W) = edgePoint d₂ r := by
            rcases (dart_edge_eq_iff d₁ d₂).mp he with rfl | rfl
            exacts [⟨t₁, rfl⟩, ⟨_, (edgePoint_symm' d₂ t₁).symm⟩]
          simp only [hr] at hx ⊢
          rw [dist_edgePoint_eq_min_same]
          exact le_min (hSameEdge d₂ r t₂ _ hy) (hvia _ hx d₂ t₂ hy)
        · rw [dist_edgePoint_eq_min_of_edge_ne he]
          exact hvia _ hx d₂ t₂ hy
  · obtain ⟨p, -, hp⟩ := exists_isPath_walkLength_eq_vertexDist
      (subdivide W B hV).weight_nonneg ((subdivide W B hV).connected x y)
    exact hp ▸ walk_in_subdivide_to_metric p

/-! ### Isometric equivalence between a subdivision and the original metric graph -/

private noncomputable def interpUnit (s t r : unitInterval) (hst : (s : ℝ) ≤ t) : unitInterval :=
  ⟨(1 - (r : ℝ)) * s + r * t,
    add_nonneg (mul_nonneg (unitInterval.one_sub_nonneg r) s.property.1)
      (mul_nonneg r.property.1 t.property.1),
    by nlinarith [r.property.1, r.property.2, s.property.2, t.property.2]⟩

private theorem interpUnit_zero (s t : unitInterval) (hst : (s : ℝ) ≤ t) :
    interpUnit s t 0 hst = s := by
  ext; simp [interpUnit]

private theorem interpUnit_one (s t : unitInterval) (hst : (s : ℝ) ≤ t) :
    interpUnit s t 1 hst = t := by
  ext; simp [interpUnit]

private theorem interpUnit_symm (s t r : unitInterval) (hst : (s : ℝ) ≤ t)
    (hst' : (unitInterval.symm t : ℝ) ≤ unitInterval.symm s) :
    interpUnit (unitInterval.symm t) (unitInterval.symm s) (unitInterval.symm r) hst' =
      unitInterval.symm (interpUnit s t r hst) := by
  ext
  change (1 - (1 - (r : ℝ))) * (1 - t) + (1 - r) * (1 - s) = 1 - ((1 - r) * s + r * t)
  ring

private theorem interpUnit_mem_Icc (s t r : unitInterval) (hst : (s : ℝ) ≤ t) :
    (s : ℝ) ≤ interpUnit s t r hst ∧ (interpUnit s t r hst : ℝ) ≤ t := by
  constructor <;> dsimp only [interpUnit] <;> nlinarith [r.property.1, r.property.2, hst]

private theorem abs_interpUnit_sub (s t r₁ r₂ : unitInterval) (hst : (s : ℝ) ≤ t) :
    |(interpUnit s t r₁ hst : ℝ) - interpUnit s t r₂ hst| = |(r₁ : ℝ) - r₂| * (t - s) := by
  dsimp only [interpUnit]
  have hsub : ((1 - (r₁ : ℝ)) * s + r₁ * t) - ((1 - (r₂ : ℝ)) * s + r₂ * t) =
      ((r₁ : ℝ) - r₂) * (t - s) := by ring
  rw [hsub, abs_mul, abs_of_nonneg (sub_nonneg.mpr hst)]

private noncomputable def subDartOrigin {B : Finset (MetricGraph W)}
    {hV : ∀ v, vertex v ∈ B} (d' : (subdivide W B hV).graph.Dart) : W.graph.Dart :=
  Classical.choose d'.adj.2

private noncomputable def subDartStart {B : Finset (MetricGraph W)}
    {hV : ∀ v, vertex v ∈ B} (d' : (subdivide W B hV).graph.Dart) : unitInterval :=
  Classical.choose (Classical.choose_spec d'.adj.2)

private noncomputable def subDartEnd {B : Finset (MetricGraph W)}
    {hV : ∀ v, vertex v ∈ B} (d' : (subdivide W B hV).graph.Dart) : unitInterval :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec d'.adj.2))

private theorem subDart_spec {B : Finset (MetricGraph W)} {hV : ∀ v, vertex v ∈ B}
    (d' : (subdivide W B hV).graph.Dart) :
    (subDartStart d' : ℝ) < subDartEnd d' ∧
    edgePoint (subDartOrigin d') (subDartStart d') = d'.fst.val ∧
    edgePoint (subDartOrigin d') (subDartEnd d') = d'.snd.val ∧
    ∀ r : unitInterval, (subDartStart d' : ℝ) < r → (r : ℝ) < subDartEnd d' →
      edgePoint (subDartOrigin d') r ∉ B :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec d'.adj.2))

private theorem subDart_weight {B : Finset (MetricGraph W)} {hV : ∀ v, vertex v ∈ B}
    (d' : (subdivide W B hV).graph.Dart) :
    (subdivide W B hV).weight d'.edge =
      ((subDartEnd d' : ℝ) - subDartStart d') * W.weight (subDartOrigin d').edge := by
  have hsp := subDart_spec d'
  have hne : d'.fst.val ≠ d'.snd.val := fun h => d'.fst_ne_snd (Subtype.ext h)
  exact subWeight_eq_of_witness hne hsp.1 hsp.2.1 hsp.2.2.1

private theorem subDartStart_lt_end {B : Finset (MetricGraph W)} {hV : ∀ v, vertex v ∈ B}
    (d' : (subdivide W B hV).graph.Dart) : (subDartStart d' : ℝ) < subDartEnd d' :=
  (subDart_spec d').1

private theorem subDart_symm {B : Finset (MetricGraph W)} {hV : ∀ v, vertex v ∈ B}
    (d' : (subdivide W B hV).graph.Dart) :
    subDartOrigin d'.symm = (subDartOrigin d').symm ∧
    subDartStart d'.symm = unitInterval.symm (subDartEnd d') ∧
    subDartEnd d'.symm = unitInterval.symm (subDartStart d') := by
  have h1 := subDart_spec d'
  have h2 := subDart_spec d'.symm
  refine subAdj_witness_eq h2.1
    (by change 1 - (subDartEnd d' : ℝ) < 1 - subDartStart d'; linarith [h1.1]) ?_ ?_
  · rw [h2.2.1, edgePoint_symm]
    exact h1.2.2.1.symm
  · rw [h2.2.2.1, edgePoint_symm]
    exact h1.2.1.symm

private noncomputable def subdivideToMetric {B : Finset (MetricGraph W)}
    (hV : ∀ v : V, vertex v ∈ B) :
    MetricGraph (subdivide W B hV) → MetricGraph W :=
  lift (fun x => x.val)
    (fun d' r => edgePoint (subDartOrigin d')
      (interpUnit (subDartStart d') (subDartEnd d') r (subDartStart_lt_end d').le))
    (fun d' => by simp only [interpUnit_zero]; exact (subDart_spec d').2.1)
    (fun d' => by simp only [interpUnit_one]; exact (subDart_spec d').2.2.1)
    (fun d' r => by
      obtain ⟨hO, hS, hE⟩ := subDart_symm d'
      have hst := (subDartStart_lt_end d').le
      have hst' := (subDartStart_lt_end d'.symm).le
      have hcongr :
          interpUnit (subDartStart d'.symm) (subDartEnd d'.symm) (unitInterval.symm r) hst' =
          unitInterval.symm (interpUnit (subDartStart d') (subDartEnd d') r hst) := by
        simp only [hS, hE]
        exact interpUnit_symm _ _ r hst _
      rw [hcongr, hO, edgePoint_symm])

private theorem subdivideToMetric_dist_le [Finite V] {B : Finset (MetricGraph W)}
    (hV : ∀ v : V, vertex v ∈ B) (p q : MetricGraph (subdivide W B hV)) :
    dist (subdivideToMetric hV p) (subdivideToMetric hV q) ≤ dist p q := by
  refine dist_map_le_of_edgePoint_dist_le (subdivideToMetric hV) (fun d' r₁ r₂ => ?_) p q
  simp only [subdivideToMetric, lift_edgePoint]
  refine (dist_edgePoint_self_le _ _ _).trans_eq ?_
  rw [subDart_weight d', abs_interpUnit_sub]
  ring

private theorem subInterval_outside_of_mem {B : Finset (MetricGraph W)}
    {hV : ∀ v : V, vertex v ∈ B} (d' : (subdivide W B hV).graph.Dart)
    {r : unitInterval} (hrB : edgePoint (subDartOrigin d') r ∈ B) :
    (r : ℝ) ≤ subDartStart d' ∨ (subDartEnd d' : ℝ) ≤ r := by
  by_contra hnot
  push Not at hnot
  exact (subDart_spec d').2.2.2 r hnot.1 hnot.2 hrB

private theorem subInterval_disjoint_of_edge_ne {B : Finset (MetricGraph W)}
    {hV : ∀ v : V, vertex v ∈ B} {d₁' d₂' : (subdivide W B hV).graph.Dart}
    (hne : d₁'.edge ≠ d₂'.edge) (heq : subDartOrigin d₁' = subDartOrigin d₂') :
    (subDartEnd d₁' : ℝ) ≤ subDartStart d₂' ∨ (subDartEnd d₂' : ℝ) ≤ subDartStart d₁' := by
  by_contra hnot
  rcases not_or.mp hnot with ⟨h1, h2⟩
  push Not at h1 h2
  have hsp1 := subDart_spec d₁'
  have hsp2 := subDart_spec d₂'
  have hs1 : (subDartStart d₁' : ℝ) ≤ subDartStart d₂' :=
    (subInterval_outside_of_mem d₂' (heq ▸ hsp1.2.1 ▸ d₁'.fst.property)).resolve_right h2.not_ge
  have hs2 : (subDartStart d₂' : ℝ) ≤ subDartStart d₁' :=
    (subInterval_outside_of_mem d₁'
      (heq.symm ▸ hsp2.2.1 ▸ d₂'.fst.property)).resolve_right h1.not_ge
  have ht1 : (subDartEnd d₁' : ℝ) ≤ subDartEnd d₂' :=
    (subInterval_outside_of_mem d₁'
      (heq.symm ▸ hsp2.2.2.1 ▸ d₂'.snd.property)).resolve_left h2.not_ge
  have ht2 : (subDartEnd d₂' : ℝ) ≤ subDartEnd d₁' :=
    (subInterval_outside_of_mem d₂' (heq ▸ hsp1.2.2.1 ▸ d₁'.snd.property)).resolve_left h1.not_ge
  have hfst : d₁'.fst = d₂'.fst :=
    Subtype.ext (by rw [← hsp1.2.1, ← hsp2.2.1, heq, Subtype.ext (le_antisymm hs1 hs2)])
  have hsnd : d₁'.snd = d₂'.snd :=
    Subtype.ext (by rw [← hsp1.2.2.1, ← hsp2.2.2.1, heq, Subtype.ext (le_antisymm ht1 ht2)])
  exact hne (by rw [← Dart.sym2Mk_fst_snd d₁', ← Dart.sym2Mk_fst_snd d₂', hfst, hsnd])

private theorem subEdge_dist_fst_le {B : Finset (MetricGraph W)}
    {hV : ∀ v : V, vertex v ∈ B} (d' : (subdivide W B hV).graph.Dart) (r : unitInterval) :
    dist (edgePoint d' r : MetricGraph (subdivide W B hV)) (vertex d'.fst) ≤
      ((interpUnit (subDartStart d') (subDartEnd d') r (subDartStart_lt_end d').le : ℝ) -
        subDartStart d') * W.weight (subDartOrigin d').edge := by
  rw [← edgePoint_zero d']
  refine (dist_edgePoint_self_le d' r 0).trans_eq ?_
  rw [subDart_weight d', show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero,
    abs_of_nonneg r.property.1]
  dsimp only [interpUnit]; ring

private theorem subEdge_dist_snd_le {B : Finset (MetricGraph W)}
    {hV : ∀ v : V, vertex v ∈ B} (d' : (subdivide W B hV).graph.Dart) (r : unitInterval) :
    dist (edgePoint d' r : MetricGraph (subdivide W B hV)) (vertex d'.snd) ≤
      ((subDartEnd d' : ℝ) -
        interpUnit (subDartStart d') (subDartEnd d') r (subDartStart_lt_end d').le) *
        W.weight (subDartOrigin d').edge := by
  rw [← edgePoint_one d']
  refine (dist_edgePoint_self_le d' r 1).trans_eq ?_
  rw [subDart_weight d', show ((1 : unitInterval) : ℝ) = 1 from rfl, abs_sub_comm,
    abs_of_nonneg (unitInterval.one_sub_nonneg r)]
  dsimp only [interpUnit]; ring

private theorem subEdge_dist_edge_le_of_sameOrigin [Finite V] {B : Finset (MetricGraph W)}
    {hV : ∀ v : V, vertex v ∈ B} {d₁' d₂' : (subdivide W B hV).graph.Dart}
    (hne : d₁'.edge ≠ d₂'.edge) (hO : subDartOrigin d₁' = subDartOrigin d₂')
    (r₁ r₂ : unitInterval) :
    dist (edgePoint d₁' r₁ : MetricGraph (subdivide W B hV)) (edgePoint d₂' r₂) ≤
      |(interpUnit (subDartStart d₁') (subDartEnd d₁') r₁ (subDartStart_lt_end d₁').le : ℝ) -
        interpUnit (subDartStart d₂') (subDartEnd d₂') r₂ (subDartStart_lt_end d₂').le| *
        W.weight (subDartOrigin d₁').edge := by
  have hmem1 := interpUnit_mem_Icc
    (subDartStart d₁') (subDartEnd d₁') r₁ (subDartStart_lt_end d₁').le
  have hmem2 := interpUnit_mem_Icc
    (subDartStart d₂') (subDartEnd d₂') r₂ (subDartStart_lt_end d₂').le
  have h_step {a' b' : (subdivide W B hV).graph.Dart} {ra rb : unitInterval}
      (hOO : subDartOrigin a' = subDartOrigin b') (hab : (subDartEnd a' : ℝ) ≤ subDartStart b') :
      dist (edgePoint a' ra : MetricGraph (subdivide W B hV)) (edgePoint b' rb) ≤
        ((interpUnit (subDartStart b') (subDartEnd b') rb (subDartStart_lt_end b').le : ℝ) -
          interpUnit (subDartStart a') (subDartEnd a') ra (subDartStart_lt_end a').le) *
          W.weight (subDartOrigin a').edge := by
    have hmid : dist (vertex a'.snd : MetricGraph (subdivide W B hV)) (vertex b'.fst) ≤
        ((subDartStart b' : ℝ) - subDartEnd a') * W.weight (subDartOrigin a').edge := by
      rw [dist_vertex, vertexDist_subdivide, ← (subDart_spec a').2.2.1, ← (subDart_spec b').2.1,
        hOO]
      exact (dist_edgePoint_self_le _ _ _).trans_eq <| by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab), mul_comm]
    have htri := dist_triangle4 (edgePoint a' ra : MetricGraph (subdivide W B hV))
      (vertex a'.snd) (vertex b'.fst) (edgePoint b' rb)
    rw [dist_comm (vertex b'.fst) (edgePoint b' rb)] at htri
    have hs2 := subEdge_dist_fst_le b' rb
    rw [← hOO] at hs2
    linarith [subEdge_dist_snd_le a' ra]
  rcases subInterval_disjoint_of_edge_ne hne hO with h12 | h21
  · rw [abs_sub_comm (interpUnit _ _ r₁ _ : ℝ),
      abs_of_nonneg (sub_nonneg.mpr (hmem1.2.trans (h12.trans hmem2.1)))]
    exact h_step hO h12
  · rw [dist_comm, abs_of_nonneg (sub_nonneg.mpr (hmem2.2.trans (h21.trans hmem1.1))), hO]
    exact h_step hO.symm h21

private theorem dist_subEdge_origVertex_le [Finite V] {B : Finset (MetricGraph W)}
    {hV : ∀ v : V, vertex v ∈ B} (d' : (subdivide W B hV).graph.Dart) (r : unitInterval) :
    let u := interpUnit (subDartStart d') (subDartEnd d') r (subDartStart_lt_end d').le
    dist (edgePoint d' r : MetricGraph (subdivide W B hV))
        (vertex ⟨vertex (subDartOrigin d').fst, hV _⟩) ≤
      (u : ℝ) * W.weight (subDartOrigin d').edge ∧
    dist (edgePoint d' r : MetricGraph (subdivide W B hV))
        (vertex ⟨vertex (subDartOrigin d').snd, hV _⟩) ≤
      (1 - (u : ℝ)) * W.weight (subDartOrigin d').edge := by
  intro u
  constructor
  · have hd2 : dist (vertex d'.fst : MetricGraph (subdivide W B hV))
        (vertex ⟨vertex (subDartOrigin d').fst, hV _⟩) ≤
        (subDartStart d' : ℝ) * W.weight (subDartOrigin d').edge := by
      rw [dist_vertex, vertexDist_subdivide]
      change dist d'.fst.val (vertex (subDartOrigin d').fst) ≤ _
      rw [← (subDart_spec d').2.1, ← edgePoint_zero (subDartOrigin d')]
      exact (dist_edgePoint_self_le _ _ _).trans_eq <| by
        rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero,
          abs_of_nonneg (subDartStart d').property.1, mul_comm]
    linarith [dist_triangle (edgePoint d' r : MetricGraph (subdivide W B hV))
      (vertex d'.fst) (vertex ⟨vertex (subDartOrigin d').fst, hV _⟩), subEdge_dist_fst_le d' r]
  · have hd2 : dist (vertex d'.snd : MetricGraph (subdivide W B hV))
        (vertex ⟨vertex (subDartOrigin d').snd, hV _⟩) ≤
        (1 - (subDartEnd d' : ℝ)) * W.weight (subDartOrigin d').edge := by
      rw [dist_vertex, vertexDist_subdivide]
      change dist d'.snd.val (vertex (subDartOrigin d').snd) ≤ _
      rw [← (subDart_spec d').2.2.1, ← edgePoint_one (subDartOrigin d')]
      exact (dist_edgePoint_self_le _ _ _).trans_eq <| by
        rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, abs_sub_comm (subDartEnd d' : ℝ) 1,
          abs_of_nonneg (unitInterval.one_sub_nonneg (subDartEnd d')), mul_comm]
    linarith [dist_triangle (edgePoint d' r : MetricGraph (subdivide W B hV))
      (vertex d'.snd) (vertex ⟨vertex (subDartOrigin d').snd, hV _⟩), subEdge_dist_snd_le d' r]

private theorem dist_vertex_subEdge_le_subdivideToMetric [Finite V] {B : Finset (MetricGraph W)}
    (hV : ∀ v : V, vertex v ∈ B) (d' : (subdivide W B hV).graph.Dart) (r : unitInterval)
    (x : { z // z ∈ B }) :
    dist (vertex x : MetricGraph (subdivide W B hV)) (edgePoint d' r) ≤
      dist x.val (subdivideToMetric hV (edgePoint d' r)) := by
  rcases x with ⟨x, hx⟩
  simp only [subdivideToMetric, lift_edgePoint]
  let u := interpUnit (subDartStart d') (subDartEnd d') r (subDartStart_lt_end d').le
  obtain ⟨h0, h1⟩ := dist_subEdge_origVertex_le d' r
  have hVbound (z : { z : MetricGraph W // z ∈ B }) (v : V) {off : ℝ}
      (hoff : dist (edgePoint d' r : MetricGraph (subdivide W B hV)) (vertex ⟨vertex v, hV v⟩) ≤
        off) :
      dist (vertex z : MetricGraph (subdivide W B hV)) (edgePoint d' r) ≤
        dist z.val (vertex v) + off := by
    have hv : dist (vertex z : MetricGraph (subdivide W B hV)) (vertex ⟨vertex v, hV v⟩) =
        dist z.val (vertex v) := by rw [dist_vertex, vertexDist_subdivide]
    rw [dist_comm] at hoff
    linarith [dist_triangle (vertex z : MetricGraph (subdivide W B hV))
      (vertex ⟨vertex v, hV v⟩) (edgePoint d' r)]
  have sameDartCase (s₀ : unitInterval) (hs₀ : edgePoint (subDartOrigin d') s₀ ∈ B) :
      dist (vertex ⟨edgePoint (subDartOrigin d') s₀, hs₀⟩ : MetricGraph (subdivide W B hV))
        (edgePoint d' r) ≤ |(s₀ : ℝ) - u| * W.weight (subDartOrigin d').edge := by
    have hmem := interpUnit_mem_Icc (subDartStart d') (subDartEnd d') r (subDartStart_lt_end d').le
    -- Distance from `s₀` to an endpoint of `d'`, measured along the original dart.
    have hz (y : { z // z ∈ B }) {t : unitInterval} (hy : edgePoint (subDartOrigin d') t = y.val) :
        dist (vertex ⟨edgePoint (subDartOrigin d') s₀, hs₀⟩ : MetricGraph (subdivide W B hV))
          (vertex y) ≤ |(s₀ : ℝ) - t| * W.weight (subDartOrigin d').edge := by
      rw [dist_vertex, vertexDist_subdivide, ← hy, mul_comm]
      exact dist_edgePoint_self_le _ _ _
    rcases subInterval_outside_of_mem d' hs₀ with hs0 | hs0
    · have h := hz d'.fst (subDart_spec d').2.1
      rw [abs_of_nonpos (sub_nonpos.mpr hs0)] at h
      rw [abs_of_nonpos (sub_nonpos.mpr (hs0.trans hmem.1))]
      linarith [subEdge_dist_fst_le d' r, dist_comm (vertex d'.fst) (edgePoint d' r),
        dist_triangle (vertex ⟨_, hs₀⟩) (vertex d'.fst) (edgePoint d' r)]
    · have h := hz d'.snd (subDart_spec d').2.2.1
      rw [abs_of_nonneg (sub_nonneg.mpr hs0)] at h
      rw [abs_of_nonneg (sub_nonneg.mpr (hmem.2.trans hs0))]
      linarith [subEdge_dist_snd_le d' r, dist_comm (vertex d'.snd) (edgePoint d' r),
        dist_triangle (vertex ⟨_, hs₀⟩) (vertex d'.snd) (edgePoint d' r)]
  induction x using ind_simple with
  | vertex v =>
    rw [dist_vertex_edgePoint (W := W), ← dist_vertex (W := W), ← dist_vertex (W := W)]
    exact le_min (hVbound _ _ h0) (hVbound _ _ h1)
  | edgePoint d₀ s₀ =>
    by_cases he : d₀.edge = (subDartOrigin d').edge
    · obtain ⟨s, hs⟩ : ∃ s, (edgePoint d₀ s₀ : MetricGraph W) = edgePoint (subDartOrigin d') s := by
        rcases (dart_edge_eq_iff d₀ (subDartOrigin d')).mp he with rfl | rfl
        exacts [⟨s₀, rfl⟩, ⟨_, (edgePoint_symm' _ s₀).symm⟩]
      simp only [hs]
      rw [dist_edgePoint_eq_min_same (W := W)]
      exact le_min (sameDartCase _ _) (le_min (hVbound _ _ h0) (hVbound _ _ h1))
    · rw [dist_edgePoint_eq_min_of_edge_ne (W := W) he]
      exact le_min (hVbound _ _ h0) (hVbound _ _ h1)

private theorem dist_le_subdivideToMetric [Finite V] {B : Finset (MetricGraph W)}
    (hV : ∀ v : V, vertex v ∈ B) (p q : MetricGraph (subdivide W B hV)) :
    dist p q ≤ dist (subdivideToMetric hV p) (subdivideToMetric hV q) := by
  have hViaEdge (d₁' d₂' : (subdivide W B hV).graph.Dart) (r₁ r₂ : unitInterval) :
      dist (edgePoint d₁' r₁ : MetricGraph (subdivide W B hV)) (edgePoint d₂' r₂) ≤
        let u₁ := interpUnit (subDartStart d₁') (subDartEnd d₁') r₁ (subDartStart_lt_end d₁').le
        let u₂ := interpUnit (subDartStart d₂') (subDartEnd d₂') r₂ (subDartStart_lt_end d₂').le
        min
          (min ((u₁ : ℝ) * W.weight (subDartOrigin d₁').edge +
                  vertexDist W.graph W.weight (subDartOrigin d₁').fst (subDartOrigin d₂').fst +
                  (u₂ : ℝ) * W.weight (subDartOrigin d₂').edge)
               ((u₁ : ℝ) * W.weight (subDartOrigin d₁').edge +
                  vertexDist W.graph W.weight (subDartOrigin d₁').fst (subDartOrigin d₂').snd +
                  (1 - (u₂ : ℝ)) * W.weight (subDartOrigin d₂').edge))
          (min ((1 - (u₁ : ℝ)) * W.weight (subDartOrigin d₁').edge +
                  vertexDist W.graph W.weight (subDartOrigin d₁').snd (subDartOrigin d₂').fst +
                  (u₂ : ℝ) * W.weight (subDartOrigin d₂').edge)
               ((1 - (u₁ : ℝ)) * W.weight (subDartOrigin d₁').edge +
                  vertexDist W.graph W.weight (subDartOrigin d₁').snd (subDartOrigin d₂').snd +
                  (1 - (u₂ : ℝ)) * W.weight (subDartOrigin d₂').edge)) := by
    obtain ⟨h10, h11⟩ := dist_subEdge_origVertex_le d₁' r₁
    obtain ⟨h20, h21⟩ := dist_subEdge_origVertex_le d₂' r₂
    have step {u₁ u₂ : V} {o₁ o₂ : ℝ}
        (h₁ : dist (edgePoint d₁' r₁ : MetricGraph (subdivide W B hV))
          (vertex ⟨vertex u₁, hV u₁⟩) ≤ o₁)
        (h₂ : dist (edgePoint d₂' r₂ : MetricGraph (subdivide W B hV))
          (vertex ⟨vertex u₂, hV u₂⟩) ≤ o₂) :
        dist (edgePoint d₁' r₁ : MetricGraph (subdivide W B hV)) (edgePoint d₂' r₂) ≤
          o₁ + vertexDist W.graph W.weight u₁ u₂ + o₂ := by
      have h := dist_triangle4 (edgePoint d₁' r₁ : MetricGraph (subdivide W B hV))
        (vertex ⟨vertex u₁, hV u₁⟩) (vertex ⟨vertex u₂, hV u₂⟩) (edgePoint d₂' r₂)
      rw [dist_vertex, vertexDist_subdivide, dist_vertex] at h
      rw [dist_comm] at h₂
      linarith only [h, h₁, h₂]
    exact le_min (le_min (step h10 h20) (step h10 h21)) (le_min (step h11 h20) (step h11 h21))
  induction p using ind_simple with
  | vertex x =>
    induction q using ind_simple with
    | vertex y =>
      simp only [subdivideToMetric, lift_vertex, dist_vertex, vertexDist_subdivide, le_refl]
    | edgePoint d' r =>
      simp only [subdivideToMetric, lift_vertex]
      exact dist_vertex_subEdge_le_subdivideToMetric hV d' r x
  | edgePoint d₁' r₁ =>
    induction q using ind_simple with
    | vertex y =>
      rw [dist_comm, dist_comm (subdivideToMetric hV (edgePoint d₁' r₁))]
      simp only [subdivideToMetric, lift_vertex]
      exact dist_vertex_subEdge_le_subdivideToMetric hV d₁' r₁ y
    | edgePoint d₂' r₂ =>
      have hSameOrigin (d₂'' : (subdivide W B hV).graph.Dart) (r₂' : unitInterval)
          (hO : subDartOrigin d₁' = subDartOrigin d₂'') :
          dist (edgePoint d₁' r₁ : MetricGraph (subdivide W B hV)) (edgePoint d₂'' r₂') ≤
            dist (subdivideToMetric hV (edgePoint d₁' r₁))
              (subdivideToMetric hV (edgePoint d₂'' r₂')) := by
        simp only [subdivideToMetric, lift_edgePoint]
        rw [← hO, dist_edgePoint_edgePoint_same (W := W)]
        refine le_min ?_ (by simpa only [← hO] using hViaEdge d₁' d₂'' r₁ r₂')
        by_cases hde : d₁'.edge = d₂''.edge
        · rcases (dart_edge_eq_iff d₁' d₂'').mp hde with rfl | hsym
          · refine (dist_edgePoint_self_le d₁' r₁ r₂').trans_eq ?_
            rw [subDart_weight d₁', abs_interpUnit_sub]; ring
          · have h := congrArg subDartOrigin hsym
            rw [hO, (subDart_symm d₂'').1] at h
            exact absurd h.symm (subDartOrigin d₂'').symm_ne
        · exact subEdge_dist_edge_le_of_sameOrigin hde hO r₁ r₂'
      by_cases he : (subDartOrigin d₁').edge = (subDartOrigin d₂').edge
      · rcases (dart_edge_eq_iff (subDartOrigin d₁') (subDartOrigin d₂')).mp he with hO | hO
        · exact hSameOrigin d₂' r₂ hO
        · rw [← edgePoint_symm d₂' r₂]
          exact hSameOrigin d₂'.symm (unitInterval.symm r₂) (hO.trans (subDart_symm d₂').1.symm)
      · simp only [subdivideToMetric, lift_edgePoint, dist_edgePoint_edgePoint_of_edge_ne he]
        exact hViaEdge d₁' d₂' r₁ r₂

/-- The isometric equivalence `MetricGraph (subdivide W B hV) ≃ᵢ MetricGraph W`. -/
noncomputable def subdivideEquiv [Finite V] {B : Finset (MetricGraph W)}
    (hV : ∀ v : V, vertex v ∈ B) :
    MetricGraph (subdivide W B hV) ≃ᵢ MetricGraph W where
  toEquiv := Equiv.ofBijective (subdivideToMetric hV) ⟨by
    intro p q hpq
    exact dist_eq_zero.mp <| le_antisymm
      (by simpa only [hpq, dist_self] using dist_le_subdivideToMetric hV p q) dist_nonneg, by
    intro y
    induction y using ind_simple with
    | vertex v => exact ⟨vertex ⟨vertex v, hV v⟩, by simp only [subdivideToMetric, lift_vertex]⟩
    | edgePoint d u =>
      by_cases hu : edgePoint d u ∈ B
      · exact ⟨vertex ⟨edgePoint d u, hu⟩, by simp only [subdivideToMetric, lift_vertex]⟩
      · classical
        let P : Finset unitInterval := B.preimage (edgePoint d) (edgePoint_injective d).injOn
        have hP_mem (r : unitInterval) : r ∈ P ↔ edgePoint d r ∈ B := Finset.mem_preimage
        have hu0 : (0 : ℝ) < u := lt_of_le_of_ne u.property.1 fun h => hu <| by
          rw [show u = 0 from Subtype.ext h.symm, edgePoint_zero]; exact hV d.fst
        have hu1 : (u : ℝ) < 1 := lt_of_le_of_ne u.property.2 fun h => hu <| by
          rw [show u = 1 from Subtype.ext h, edgePoint_one]; exact hV d.snd
        let P_lt := P.filter (fun q : unitInterval => (q : ℝ) < u)
        let P_gt := P.filter (fun q : unitInterval => (u : ℝ) < q)
        have hlt_ne : P_lt.Nonempty := ⟨0, Finset.mem_filter.mpr
          ⟨(hP_mem 0).mpr (by rw [edgePoint_zero]; exact hV d.fst), hu0⟩⟩
        have hgt_ne : P_gt.Nonempty := ⟨1, Finset.mem_filter.mpr
          ⟨(hP_mem 1).mpr (by rw [edgePoint_one]; exact hV d.snd), hu1⟩⟩
        let s : unitInterval := P_lt.max' hlt_ne
        let t : unitInterval := P_gt.min' hgt_ne
        have hsF := Finset.mem_filter.mp (P_lt.max'_mem hlt_ne)
        have htF := Finset.mem_filter.mp (P_gt.min'_mem hgt_ne)
        have hst : (s : ℝ) < t := hsF.2.trans htF.2
        have hno : ∀ r : unitInterval, (s : ℝ) < r → (r : ℝ) < t → edgePoint d r ∉ B := by
          intro r hsr hrt hrB
          have hrP := (hP_mem r).mpr hrB
          rcases lt_trichotomy (r : ℝ) u with hru | hru | hur
          · exact absurd (Finset.le_max' P_lt r (Finset.mem_filter.mpr ⟨hrP, hru⟩))
              (not_le_of_gt hsr)
          · exact hu ((congrArg (edgePoint d) (Subtype.ext hru)).symm ▸ hrB)
          · exact absurd (Finset.min'_le P_gt r (Finset.mem_filter.mpr ⟨hrP, hur⟩))
              (not_le_of_gt hrt)
        have hneV : (⟨edgePoint d s, (hP_mem s).mp hsF.1⟩ : { z // z ∈ B }) ≠
            ⟨edgePoint d t, (hP_mem t).mp htF.1⟩ :=
          fun h => hst.ne (congrArg Subtype.val (edgePoint_injective d (congrArg Subtype.val h)))
        let d' : (subdivide W B hV).graph.Dart :=
          ⟨(_, _), ⟨hneV, d, s, t, hst, rfl, rfl, hno⟩⟩
        obtain ⟨_, rfl_s, rfl_t⟩ :=
          subAdj_witness_eq (subDart_spec d').1 hst (subDart_spec d').2.1 (subDart_spec d').2.2.1
        let τ : unitInterval := ⟨((u : ℝ) - s) / (t - s),
          div_nonneg (sub_nonneg.mpr hsF.2.le) (sub_nonneg.mpr hst.le),
          div_le_one_of_le₀ (by linarith) (sub_nonneg.mpr hst.le)⟩
        refine ⟨edgePoint d' τ, ?_⟩
        simp only [subdivideToMetric, lift_edgePoint]
        congr 1; ext
        change (1 - (((u : ℝ) - s) / (t - s))) * subDartStart d' +
            (((u : ℝ) - s) / (t - s)) * subDartEnd d' = (u : ℝ)
        rw [rfl_s, rfl_t]
        field_simp [sub_ne_zero.mpr hst.ne']; ring⟩
  isometry_toFun := Isometry.of_dist_eq fun p q =>
    le_antisymm (subdivideToMetric_dist_le hV p q) (dist_le_subdivideToMetric hV p q)

@[simp]
theorem subdivideEquiv_vertex [Finite V] {B : Finset (MetricGraph W)}
    (hV : ∀ v : V, vertex v ∈ B) (x : { z : MetricGraph W // z ∈ B }) :
    subdivideEquiv hV (vertex x) = x.val := by
  change subdivideToMetric hV (vertex x) = x.val
  simp only [subdivideToMetric, lift_vertex]

theorem subdivideEquiv_edgePoint [Finite V] {B : Finset (MetricGraph W)}
    (hV : ∀ v : V, vertex v ∈ B) (d' : (subdivide W B hV).graph.Dart) (τ : unitInterval) :
    ∃ (d : W.graph.Dart) (s t : unitInterval) (_hst : (s : ℝ) < t),
      edgePoint d s = (d'.fst : MetricGraph W) ∧ edgePoint d t = (d'.snd : MetricGraph W) ∧
      (∀ r : unitInterval, (s : ℝ) < r → (r : ℝ) < t → edgePoint d r ∉ B) ∧
      (subdivide W B hV).weight d'.edge = ((t : ℝ) - s) * W.weight d.edge ∧
      subdivideEquiv hV (edgePoint d' τ) =
        edgePoint d ⟨(1 - (τ : ℝ)) * s + τ * t,
          add_nonneg
            (mul_nonneg (unitInterval.one_sub_nonneg τ) (unitInterval.nonneg s))
            (mul_nonneg (unitInterval.nonneg τ) (unitInterval.nonneg t)),
          (add_le_add
            (mul_le_of_le_one_right (unitInterval.one_sub_nonneg τ) (unitInterval.le_one s))
            (mul_le_of_le_one_right (unitInterval.nonneg τ) (unitInterval.le_one t))).trans_eq
            (sub_add_cancel 1 (τ : ℝ))⟩ := by
  have hsp := subDart_spec d'
  refine ⟨subDartOrigin d', subDartStart d', subDartEnd d', hsp.1, hsp.2.1, hsp.2.2.1, hsp.2.2.2,
    subDart_weight d', ?_⟩
  change subdivideToMetric hV (edgePoint d' τ) = _
  simp only [subdivideToMetric, lift_edgePoint, interpUnit]

/-! ### Per-subdivided-edge affine distance from a point -/


/-- Choose a canonical dart orienting an undirected edge `e : G.edgeSet`. -/
noncomputable def edgeDartOfSym2 {G : SimpleGraph V} (e : G.edgeSet) : G.Dart :=
  ⟨Quot.out e.val, by
    have hmem : Quot.mk (Sym2.Rel V) (Quot.out e.val) ∈ G.edgeSet := by
      rw [Quot.out_eq]
      exact e.property
    exact G.mem_edgeSet.mp hmem⟩

/-- The chosen canonical dart `edgeDartOfSym2 e` lies on edge `e`. -/
@[simp]
theorem edgeDartOfSym2_edge {G : SimpleGraph V} (e : G.edgeSet) :
    (edgeDartOfSym2 e).edge = e.val :=
  Quot.out_eq e.val

/-- If `c` is strictly interior to `[0, 1]` and `edgePoint (edgeDartOfSym2 e) u` agrees with
`edgePoint (edgeDartOfSym2 e') c`, then `e = e'` and `u = c`. -/
theorem edgePoint_edgeDartOfSym2_eq_iff_of_mem_Ioo {e e' : W.graph.edgeSet}
    {u c : unitInterval} (hc0 : (0 : ℝ) < c) (hc1 : (c : ℝ) < 1) :
    edgePoint (edgeDartOfSym2 e) u = (edgePoint (edgeDartOfSym2 e') c : MetricGraph W) ↔
      e = e' ∧ u = c := by
  constructor
  · intro heq
    rcases edgePoint_eq_edgePoint_iff.mp heq with
      ⟨_, ⟨hc0', _⟩ | ⟨hc1', _⟩⟩ | ⟨_, ⟨hc0', _⟩ | ⟨hc1', _⟩⟩ |
      ⟨_, _, _, _, ⟨hd, hu⟩ | ⟨hsym, _⟩⟩
    · exact absurd (congrArg Subtype.val hc0') hc0.ne'
    · exact absurd (congrArg Subtype.val hc1') hc1.ne
    · exact absurd (congrArg Subtype.val hc0') hc0.ne'
    · exact absurd (congrArg Subtype.val hc1') hc1.ne
    · have h' := congrArg Dart.edge hd
      rw [edgeDartOfSym2_edge, edgeDartOfSym2_edge] at h'
      exact ⟨Subtype.ext h', hu⟩
    · have h' := congrArg Dart.edge hsym
      rw [edgeDartOfSym2_edge, Dart.edge_symm, edgeDartOfSym2_edge] at h'
      have he : e = e' := Subtype.ext h'
      subst he
      exact absurd hsym.symm (edgeDartOfSym2 e).symm_ne
  · rintro ⟨rfl, rfl⟩
    rfl

open Classical in
/-- At most three breakpoints along dart `d` where `t ↦ dist p (edgePoint d t)` changes slope. -/
noncomputable def dartBreakpoints [Finite V] (W : WeightedGraph V) (p : MetricGraph W)
    (d : W.graph.Dart) : Finset (MetricGraph W) :=
  let a := dist p (vertex d.fst)
  let b := dist p (vertex d.snd)
  let w := W.weight d.edge
  if h : ∃ s₀ : unitInterval, edgePoint d s₀ = p then
    let s₀ := Classical.choose h
    let c₁ := min ((s₀ : ℝ) * w) (b + w)
    let c₂ := min (-(s₀ : ℝ) * w) a
    let t₂ := Set.projIcc 0 1 zero_le_one ((c₁ - a) / (2 * w))
    let t₃ := Set.projIcc 0 1 zero_le_one ((b + w - c₂) / (2 * w))
    {edgePoint d s₀, edgePoint d t₂, edgePoint d t₃}
  else
    {edgePoint d (Set.projIcc 0 1 zero_le_one ((b + w - a) / (2 * w)))}

theorem dartBreakpoints_card_le [Finite V] (W : WeightedGraph V) (p : MetricGraph W)
    (d : W.graph.Dart) : (dartBreakpoints W p d).card ≤ 3 := by
  classical
  unfold dartBreakpoints
  split_ifs
  · exact (Finset.card_insert_le _ _).trans
      (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))
  · simp

theorem dartBreakpoints_symm [Finite V] (W : WeightedGraph V) (p : MetricGraph W)
    (d : W.graph.Dart) : dartBreakpoints W p d.symm = dartBreakpoints W p d := by
  classical
  have hw := W.dart_weight_pos d
  have hboth : (∃ s₀ : unitInterval, edgePoint d.symm s₀ = p) ↔
      (∃ s₀ : unitInterval, edgePoint d s₀ = p) :=
    ⟨fun ⟨s₀, hs⟩ => ⟨unitInterval.symm s₀, by simpa only [edgePoint_symm'] using hs⟩,
     fun ⟨s₀, hs⟩ => ⟨unitInterval.symm s₀, (edgePoint_symm d s₀).trans hs⟩⟩
  by_cases h : ∃ s₀ : unitInterval, edgePoint d s₀ = p
  · have hs : ∃ s₀ : unitInterval, edgePoint d.symm s₀ = p := hboth.mpr h
    simp only [dartBreakpoints, hs, h, ↓reduceDIte]
    set s := Classical.choose h
    set s' := Classical.choose hs
    have hs_eq : s' = unitInterval.symm s :=
      edgePoint_injective d.symm <|
        (Classical.choose_spec hs).trans ((edgePoint_symm d s).trans (Classical.choose_spec h)).symm
    let a := dist p (vertex d.fst); let b := dist p (vertex d.snd); let w := W.weight d.edge
    have hw0 : w ≠ 0 := hw.ne'
    have hsnd : d.symm.snd = d.fst := rfl
    have hsym_t2 : Set.projIcc 0 1 zero_le_one ((min ((s' : ℝ) * W.weight d.symm.edge)
          (dist p (vertex d.symm.snd) + W.weight d.symm.edge) - dist p (vertex d.symm.fst)) /
          (2 * W.weight d.symm.edge)) =
        unitInterval.symm
          (Set.projIcc 0 1 zero_le_one ((b + w - min (-(s : ℝ) * w) a) / (2 * w))) := by
      rw [unitInterval.symm_projIcc]; congr 1
      simp only [Dart.fst_symm, hsnd, Dart.edge_symm, hs_eq, unitInterval.coe_symm_eq]
      change (min ((1 - (s : ℝ)) * w) (a + w) - b) / (2 * w) =
        1 - (b + w - min (-(s : ℝ) * w) a) / (2 * w)
      have : min ((1 - (s : ℝ)) * w) (a + w) = w + min (-(s : ℝ) * w) a := by
        rw [← min_add_add_left]; congr 1 <;> ring
      rw [this]; field_simp [hw0]; ring
    have hsym_t3 : Set.projIcc 0 1 zero_le_one
        ((dist p (vertex d.symm.snd) + W.weight d.symm.edge -
          min (-(s' : ℝ) * W.weight d.symm.edge) (dist p (vertex d.symm.fst))) /
          (2 * W.weight d.symm.edge)) =
        unitInterval.symm
          (Set.projIcc 0 1 zero_le_one ((min ((s : ℝ) * w) (b + w) - a) / (2 * w))) := by
      rw [unitInterval.symm_projIcc]; congr 1
      simp only [Dart.fst_symm, hsnd, Dart.edge_symm, hs_eq, unitInterval.coe_symm_eq]
      change (a + w - min (-(1 - (s : ℝ)) * w) b) / (2 * w) =
        1 - (min ((s : ℝ) * w) (b + w) - a) / (2 * w)
      have : min (-(1 - (s : ℝ)) * w) b = min ((s : ℝ) * w) (b + w) - w := by
        rw [← min_sub_sub_right]; congr 1 <;> ring
      rw [this]; field_simp [hw0]; ring
    rw [show edgePoint d.symm s' = edgePoint d s from by rw [hs_eq, edgePoint_symm],
      hsym_t2, edgePoint_symm, hsym_t3, edgePoint_symm]
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · have hns : ¬ ∃ s₀ : unitInterval, edgePoint d.symm s₀ = p := by rwa [hboth]
    simp only [dartBreakpoints, h, hns, ↓reduceDIte]
    have hsnd : d.symm.snd = d.fst := rfl
    have hsym_eq : Set.projIcc 0 1 zero_le_one
        ((dist p (vertex d.symm.snd) + W.weight d.symm.edge -
          dist p (vertex d.symm.fst)) / (2 * W.weight d.symm.edge)) =
        unitInterval.symm (Set.projIcc 0 1 zero_le_one ((dist p (vertex d.snd) + W.weight d.edge -
          dist p (vertex d.fst)) / (2 * W.weight d.edge))) := by
      rw [unitInterval.symm_projIcc]; congr 1
      simp only [Dart.fst_symm, hsnd, Dart.edge_symm]
      field_simp [hw.ne']; ring
    rw [hsym_eq, edgePoint_symm]

open Classical in
/-- Finite set of all original vertices together with at most three breakpoints per edge for
`p : MetricGraph W`. -/
noncomputable def pointBreakpoints [Finite V] (W : WeightedGraph V)
    (p : MetricGraph W) : Finset (MetricGraph W) :=
  let : Fintype V := Fintype.ofFinite V
  let : Fintype W.graph.edgeSet := Fintype.ofFinite _
  (Finset.univ.image vertex) ∪
    (Finset.univ.biUnion fun e : W.graph.edgeSet => dartBreakpoints W p (edgeDartOfSym2 e))

theorem vertex_mem_pointBreakpoints [Finite V] (W : WeightedGraph V) (p : MetricGraph W)
    (v : V) : vertex v ∈ pointBreakpoints W p := by
  classical
  simp only [pointBreakpoints, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl ⟨v, rfl⟩

theorem dartBreakpoints_subset_pointBreakpoints [Finite V] (W : WeightedGraph V)
    (p : MetricGraph W) (d : W.graph.Dart) :
    dartBreakpoints W p d ⊆ pointBreakpoints W p := by
  classical
  intro q hq
  simp only [pointBreakpoints, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
  refine Or.inr ⟨⟨d.edge, d.edge_mem⟩, ?_⟩
  rcases (dart_edge_eq_iff (edgeDartOfSym2 ⟨d.edge, d.edge_mem⟩) d).mp
      (edgeDartOfSym2_edge _) with he | he
  · rwa [he]
  · rwa [he, dartBreakpoints_symm]

open Classical in
theorem pointBreakpoints_sdiff_card_le [Finite V] (W : WeightedGraph V) (p : MetricGraph W) :
    let : Fintype V := Fintype.ofFinite V
    (pointBreakpoints W p \ Finset.univ.image vertex).card ≤
      3 * Nat.card W.graph.edgeSet := by
  intro _
  let : Fintype W.graph.edgeSet := Fintype.ofFinite _
  refine (Finset.card_le_card (t := Finset.univ.biUnion
      fun e : W.graph.edgeSet => dartBreakpoints W p (edgeDartOfSym2 e)) ?_).trans ?_
  · intro q hq
    simp only [Finset.mem_sdiff, pointBreakpoints, Finset.mem_union] at hq
    exact hq.1.resolve_left hq.2
  · refine Finset.card_biUnion_le.trans ?_
    calc ∑ e : W.graph.edgeSet, (dartBreakpoints W p (edgeDartOfSym2 e)).card
        ≤ ∑ _ : W.graph.edgeSet, 3 :=
          Finset.sum_le_sum fun e _ => dartBreakpoints_card_le W p _
      _ = 3 * Nat.card W.graph.edgeSet := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm, Fintype.card_eq_nat_card]

private theorem dist_point_edgePoint_piecewise_affine [Finite V] (W : WeightedGraph V)
    (p : MetricGraph W) (d : W.graph.Dart) {s t : unitInterval} (hst : (s : ℝ) < t)
    (hno : ∀ q ∈ dartBreakpoints W p d, ∀ r : unitInterval,
      (s : ℝ) < r → (r : ℝ) < t → edgePoint d r ≠ q) :
    ∃ α β : ℝ, ∀ r : unitInterval, (s : ℝ) ≤ r → (r : ℝ) ≤ t →
      dist p (edgePoint d r) = α + β * r := by
  classical
  have hw := W.dart_weight_pos d
  let a := dist p (vertex d.fst)
  let b := dist p (vertex d.snd)
  let w := W.weight d.edge
  have avoids {u : unitInterval} (hu : edgePoint d u ∈ dartBreakpoints W p d) :
      (u : ℝ) ≤ s ∨ (t : ℝ) ≤ u := by
    by_contra hnot
    push Not at hnot
    exact hno (edgePoint d u) hu u hnot.1 hnot.2 rfl
  -- The minimum of a decreasing and an increasing affine function is affine on `[s, t]` when
  -- their (clamped) crossing point is a breakpoint, hence outside `(s, t)`.
  have affine_min {u v : ℝ}
      (hs' : ∀ r : unitInterval, (s : ℝ) ≤ r → (r : ℝ) ≤ t →
        dist p (edgePoint d r) = min (u - (r : ℝ) * w) (v + (r : ℝ) * w))
      (hmem : edgePoint d (Set.projIcc 0 1 zero_le_one ((u - v) / (2 * w))) ∈
        dartBreakpoints W p d) :
      ∃ α β : ℝ, ∀ r : unitInterval, (s : ℝ) ≤ r → (r : ℝ) ≤ t →
        dist p (edgePoint d r) = α + β * r := by
    rcases avoids hmem with hle | hle <;> rw [Set.coe_projIcc] at hle
    · refine ⟨u, -w, fun r hrs hrt => ?_⟩
      have hc : (u - v) / (2 * w) ≤ r :=
        ((min_le_iff.mp ((le_max_right _ _).trans hle)).resolve_left
          (hst.trans_le t.property.2).not_ge).trans hrs
      rw [div_le_iff₀ (by linarith)] at hc
      rw [hs' r hrs hrt, min_eq_left (by linarith)]; ring
    · refine ⟨v, w, fun r hrs hrt => ?_⟩
      have hc : (r : ℝ) ≤ (u - v) / (2 * w) :=
        hrt.trans
          (le_min_iff.mp ((le_max_iff.mp hle).resolve_left (s.property.1.trans_lt hst).not_ge)).2
      rw [le_div_iff₀ (by linarith)] at hc
      rw [hs' r hrs hrt, min_eq_right (by linarith)]; ring
  by_cases hp : ∃ s₀ : unitInterval, edgePoint d s₀ = p
  · let s₀ := Classical.choose hp
    have hp_eq : p = edgePoint d s₀ := (Classical.choose_spec hp).symm
    let c₁ := min ((s₀ : ℝ) * w) (b + w)
    let c₂ := min (-(s₀ : ℝ) * w) a
    let t₂ := Set.projIcc 0 1 zero_le_one ((c₁ - a) / (2 * w))
    let t₃ := Set.projIcc 0 1 zero_le_one ((b + w - c₂) / (2 * w))
    have hformula (r : unitInterval) :
        dist p (edgePoint d r) =
          min (|(s₀ : ℝ) - r| * w) (min (a + (r : ℝ) * w) (b + (1 - (r : ℝ)) * w)) := by
      dsimp only [a, b, w]; rw [hp_eq]; exact dist_edgePoint_eq_min_same d s₀ r
    have hmem : edgePoint d s₀ ∈ dartBreakpoints W p d ∧
        edgePoint d t₂ ∈ dartBreakpoints W p d ∧ edgePoint d t₃ ∈ dartBreakpoints W p d := by
      dsimp only [dartBreakpoints]; split_ifs
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact ⟨Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩
    rcases avoids hmem.1 with hs₀s | hts₀
    · refine affine_min (fun r hrs _ => ?_) hmem.2.2
      rw [hformula r, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hs₀s.trans hrs))]
      have hc2eq : c₂ + (r : ℝ) * w = min (((r : ℝ) - s₀) * w) (a + (r : ℝ) * w) := by
        dsimp only [c₂]; rw [← min_add_add_right]; congr 1; ring
      rw [← min_assoc, min_comm _ (b + (1 - (r : ℝ)) * w), ← hc2eq]; congr 1; ring
    · refine affine_min (fun r _ hrt => ?_) hmem.2.1
      rw [hformula r, abs_of_nonneg (sub_nonneg.mpr (hrt.trans hts₀))]
      have hc1eq : c₁ - (r : ℝ) * w = min (((s₀ : ℝ) - r) * w) (b + (1 - (r : ℝ)) * w) := by
        dsimp only [c₁]; rw [← min_sub_sub_right]; congr 1 <;> ring
      rw [min_comm (a + (r : ℝ) * w), ← min_assoc, ← hc1eq]
  · have hformula (r : unitInterval) :
        dist p (edgePoint d r) = min (b + w - (r : ℝ) * w) (a + (r : ℝ) * w) := by
      have hm : dist p (edgePoint d r) = min (a + (r : ℝ) * w) (b + (1 - (r : ℝ)) * w) := by
        induction p using ind_simple with
        | vertex u =>
          rw [dist_vertex_edgePoint]; dsimp only [a, b, w]; rw [dist_vertex, dist_vertex]
        | edgePoint d₀ s₀ =>
          have hne : d₀.edge ≠ d.edge := fun he => by
            rcases (dart_edge_eq_iff d₀ d).mp he with rfl | rfl
            exacts [hp ⟨s₀, rfl⟩, hp ⟨_, edgePoint_symm' d s₀⟩]
          exact dist_edgePoint_eq_min_of_edge_ne hne s₀ r
      rw [hm, min_comm]; congr 1; ring
    have hmem : edgePoint d (Set.projIcc 0 1 zero_le_one ((b + w - a) / (2 * w))) ∈
        dartBreakpoints W p d := by
      dsimp only [dartBreakpoints]; split_ifs; exact Finset.mem_singleton_self _
    exact affine_min (fun r _ _ => hformula r) hmem

/-- On any subdivision containing `pointBreakpoints W p`, the distance from `p` is affine
along every subdivided edge. -/
theorem dist_subdivide_edgePoint_affine [Finite V] {p : MetricGraph W}
    {B : Finset (MetricGraph W)} (hV : ∀ v : V, vertex v ∈ B) (hBp : pointBreakpoints W p ⊆ B)
    (d' : (subdivide W B hV).graph.Dart) (τ : unitInterval) :
    dist p (subdivideEquiv hV (edgePoint d' τ)) =
      (1 - (τ : ℝ)) * dist p (subdivideEquiv hV (vertex d'.fst)) +
        (τ : ℝ) * dist p (subdivideEquiv hV (vertex d'.snd)) := by
  obtain ⟨d, s, t, hst, hs, ht, hno, _, heq⟩ := subdivideEquiv_edgePoint hV d' τ
  have hsub := dartBreakpoints_subset_pointBreakpoints W p d |>.trans hBp
  obtain ⟨α, β, haff⟩ := dist_point_edgePoint_piecewise_affine W p d hst
    (fun q hq r hsr hrt => fun hreq => hno r hsr hrt (hreq ▸ hsub hq))
  let u := interpUnit s t τ hst.le
  obtain ⟨hu1, hu2⟩ := interpUnit_mem_Icc s t τ hst.le
  have h1 := haff s le_rfl hst.le
  have h2 := haff t hst.le le_rfl
  have h3 : dist p (edgePoint d u) = α + β * u := haff u hu1 hu2
  change subdivideEquiv hV (edgePoint d' τ) = edgePoint d u at heq
  rw [heq, subdivideEquiv_vertex, subdivideEquiv_vertex, ← hs, ← ht, h1, h2, h3]
  dsimp only [u, interpUnit]
  ring

theorem dist_subdivide_edgePoint_affine' [Finite V] {B : Finset (MetricGraph W)}
    (hV : ∀ v : V, vertex v ∈ B) {p' : MetricGraph (subdivide W B hV)}
    (hBp : pointBreakpoints W (subdivideEquiv hV p') ⊆ B)
    (d' : (subdivide W B hV).graph.Dart) (τ : unitInterval) :
    dist p' (edgePoint d' τ) =
      (1 - (τ : ℝ)) * dist p' (vertex d'.fst) +
        (τ : ℝ) * dist p' (vertex d'.snd) := by
  have hiso := (subdivideEquiv hV).isometry
  rw [← hiso.dist_eq, ← hiso.dist_eq p' (vertex d'.fst), ← hiso.dist_eq p' (vertex d'.snd)]
  exact dist_subdivide_edgePoint_affine hV hBp d' τ

end MetricGraph

end SimpleGraph
