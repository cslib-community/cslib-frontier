/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.ReferenceDrawing
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.SubdivisionEdges
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.PrescribedOrder
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Restriction
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.SplitOrder
import CslibFrontier.Foundations.Geometry.Polygonal.RayOrder
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup

/-!
# Literal clockwise order of actual reference stars

An original dart selects the first or last segment of its own twice-subdivided occurrence,
retaining its end tag. Its outgoing reference germ points from its original center to the
fresh leaf named by its original binary dart index. Both ends of an original loop remain
distinct.

At a prescribed center, the literal reversed leaf block follows the center in `referenceOrder`.
Actual leaf ranks and actual outgoing arguments therefore decrease along the prescribed word.
Their reversed angular triples have precisely the word's clockwise cyclic order. Nonzero
germs and local direction injectivity are derived internally, with no supplied rotation or
geometric order certificate. Degree zero, one and two need no special convention.

These are local statements about the intentionally crossing reference drawing. They supply
neither a global embedding nor generic position, frozen placement, move realization or a
Hanani–Tutte/query-completeness theorem. The remaining full recognition and source-model
objective is tracked in [#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

## Main results

* `Cslib.Complexity.Graph.RotationRecognition.frozen_iff_exists_subdivisionDart`: the stored
  flag selects exactly the indexed first/last segments of originally fixed ends.
* `Cslib.Complexity.Graph.RotationRecognition.referenceDrawing_subdivisionDart_germ`: the
  actual outgoing vector from that center to that leaf.
* `Cslib.Complexity.Graph.RotationRecognition.referenceDrawing_fixedWord_arg_lt_iff`: actual
  arguments decrease in the literal prescribed word, including comparison with itself.
* `Cslib.Complexity.Graph.RotationRecognition.referenceDrawing_fixedWord_directions_injective`:
  distinct selected original darts have distinct actual directions.
* `Cslib.Complexity.Graph.RotationRecognition.referenceDrawing_fixedWord_clockwise_iff`:
  clockwise angular triples are exactly the prescribed word's directed cyclic triples.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Polygonal

/-- The actual stored frozen bit selects exactly the first or last segment of an originally
fixed indexed end. This raw combinatorial classifier does not require `Valid`. -/
theorem frozen_iff_exists_subdivisionDart (I : FixedRotationInput)
    (e : Fin (subdivisionGraph I).edges.length) :
    ((subdivide I)[e.val]'(by
      simpa only [subdivisionGraph, List.length_map] using e.isLt)).frozen = true ↔
      ∃ d : Dart I.graph, e = (subdivisionDart I d).1 ∧
        (I.orders.getD d.vertex none).isSome = true := by
  have he : e.val < (subdivide I).length := by
    simpa only [subdivisionGraph, List.length_map] using e.isLt
  constructor
  · intro hf
    let i := (subdivisionEdgeIndex I e).original
    let k := (subdivisionEdgeIndex I e).piece
    have hlookup := subdivide_getElem? I i k
    have hindex : 3 * i.val + k.val = e.val := (subdivisionEdgeIndex_val I e).symm
    rw [hindex] at hlookup
    have hget := Option.some.inj ((List.getElem?_eq_getElem he).symm.trans hlookup)
    have hk : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 := by have := k.isLt; omega
    rcases hk with hk | hk | hk
    · refine ⟨(i, false), Fin.ext ?_, ?_⟩
      · change e.val = 3 * i.val + 0
        omega
      · rw [hget] at hf
        simpa only [Fin.getElem_fin, hk, List.getElem_cons_zero, Segment.frozen,
          Dart.vertex, Graph.edgeEndpoint, Bool.false_eq_true, ↓reduceIte,
          List.getD_eq_getElem _ _ i.isLt] using hf
    · rw [hget] at hf
      simp only [Fin.getElem_fin, hk, List.getElem_cons_succ, List.getElem_cons_zero,
        Segment.frozen, Bool.false_eq_true] at hf
    · refine ⟨(i, true), Fin.ext ?_, ?_⟩
      · change e.val = 3 * i.val + 2
        omega
      · rw [hget] at hf
        simpa only [Fin.getElem_fin, hk, List.getElem_cons_succ, List.getElem_cons_zero,
          Segment.frozen, Dart.vertex, Graph.edgeEndpoint, ↓reduceIte,
          List.getD_eq_getElem _ _ i.isLt] using hf
  · rintro ⟨⟨i, b⟩, rfl, hf⟩
    cases b
    · have hlookup := subdivide_getElem? I i 0
      have hbound : 3 * i.val < (subdivide I).length := by rw [length_subdivide]; omega
      have hget := Option.some.inj ((List.getElem?_eq_getElem hbound).symm.trans
        (by simpa only [Fin.val_zero, Nat.add_zero] using hlookup))
      change ((subdivide I)[3 * i.val]).frozen = true
      rw [hget]
      change (I.orders.getD I.graph.edges[i].1 none).isSome = true
      simpa only [Fin.getElem_fin, Dart.vertex, Graph.edgeEndpoint, Bool.false_eq_true, ↓reduceIte,
        List.getD_eq_getElem _ _ i.isLt] using hf
    · have hlookup := subdivide_getElem? I i 2
      have hbound : 3 * i.val + 2 < (subdivide I).length := by rw [length_subdivide]; omega
      have hget := Option.some.inj ((List.getElem?_eq_getElem hbound).symm.trans hlookup)
      change ((subdivide I)[3 * i.val + 2]).frozen = true
      rw [hget]
      change (I.orders.getD I.graph.edges[i].2 none).isSome = true
      simpa only [Fin.getElem_fin, Dart.vertex, Graph.edgeEndpoint, ↓reduceIte,
        List.getD_eq_getElem _ _ i.isLt] using hf

/-- The actual outgoing first/last route vector points from the original center to its leaf. -/
theorem referenceDrawing_subdivisionDart_germ (I : FixedRotationInput) (d : Dart I.graph) :
    (referenceDrawing I).germ (subdivisionDart I d) =
      referencePoint I (I.graph.vertices.length + d.index) - referencePoint I d.vertex := by
  have hends := subdivisionDart_endpoints I d
  have hline (a : Dart (subdivisionGraph I)) :
      (referenceDrawing I).germ a =
        referencePoint I a.reverse.vertex - referencePoint I a.vertex := by
    rcases a with ⟨e, b⟩
    cases b <;> rfl
  rw [hline, hends.1, hends.2]

/-- Every selected outgoing vector is nonzero, even at either end of an original loop. -/
theorem referenceDrawing_subdivisionDart_germ_ne_zero {I : FixedRotationInput} (hI : Valid I)
    (d : Dart I.graph) : (referenceDrawing I).germ (subdivisionDart I d) ≠ 0 :=
  (referenceDrawing_simple hI (subdivisionDart I d).1).germ_ne_zero (subdivisionDart I d).2

private theorem fixedWord_rank_spec {I : FixedRotationInput} (hI : Valid I) {v : ℕ}
    {word : List ℕ} (hw : I.orders.getD v none = some word) :
    v ∈ referenceOrder I ∧
      ∀ d ∈ word, I.graph.vertices.length + d ∈ referenceOrder I ∧
        (referenceOrder I).idxOf v <
          (referenceOrder I).idxOf (I.graph.vertices.length + d) ∧
        (referenceOrder I).idxOf (I.graph.vertices.length + d) =
          (referenceOrder I).idxOf v + word.length - word.idxOf d := by
  have hv : v < I.graph.vertices.length := by
    by_contra hn
    have ho : I.orders.length ≤ v := by rw [hI.2.2.1]; omega
    rw [List.getD_eq_default _ _ ho] at hw
    contradiction
  obtain ⟨before, after, hcenters⟩ := List.mem_iff_append.mp (List.mem_range.mpr hv)
  let block := fun u => u :: ((fixedWord I u).reverse.map fun d => I.graph.vertices.length + d)
  let blockPrefix := before.flatMap block
  let blockSuffix := after.flatMap block ++
    ((List.range (2 * I.graph.edges.length)).map (fun d => I.graph.vertices.length + d)).filter
      (fun x => !(centerBlocks I).any fun y => decide (y = x))
  have hshape : referenceOrder I =
      blockPrefix ++ v ::
        (word.reverse.map (fun d => I.graph.vertices.length + d) ++ blockSuffix) := by
    change (List.range I.graph.vertices.length).flatMap block ++
      ((List.range (2 * I.graph.edges.length)).map
        (fun d => I.graph.vertices.length + d)).filter
        (fun x => !(centerBlocks I).any fun y => decide (y = x)) = _
    rw [hcenters, List.flatMap_append, List.flatMap_cons]
    have hblock : block v = v :: word.reverse.map (fun d => I.graph.vertices.length + d) := by
      simp only [block, fixedWord, hw, Option.getD_some]
    rw [hblock]
    simp only [blockPrefix, blockSuffix, List.append_assoc, List.cons_append]
  have hn := (referenceOrder_enumerates hI).1
  have hvpos : blockPrefix.length < (referenceOrder I).length := by rw [hshape]; simp
  have hvget : (referenceOrder I)[blockPrefix.length] = v := by
    rw [List.getElem_of_eq hshape hvpos, List.getElem_append_right (by omega)]
    simp
  have hvrank : (referenceOrder I).idxOf v = blockPrefix.length := by
    rw [← hvget]
    exact hn.idxOf_getElem _ hvpos
  refine ⟨hvget ▸ List.getElem_mem hvpos, ?_⟩
  intro d hd
  let i := word.idxOf d
  have hi : i < word.length := List.idxOf_lt_length_of_mem hd
  let k := word.length - 1 - i
  have hk : k < word.reverse.length := by simp only [List.length_reverse]; dsimp [k]; omega
  have hpos : blockPrefix.length + (k + 1) < (referenceOrder I).length := by
    rw [hshape]
    simp only [List.length_append, List.length_cons, List.length_map, List.length_reverse]
    omega
  have hget : (referenceOrder I)[blockPrefix.length + (k + 1)] =
      I.graph.vertices.length + d := by
    rw [List.getElem_of_eq hshape hpos, List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left, List.getElem_cons_succ]
    rw [List.getElem_append_left (by simpa only [List.length_map] using hk),
      List.getElem_map, List.getElem_reverse]
    have heq : word.length - 1 - k = i := by dsimp [k]; omega
    simp only [heq]
    exact congrArg (fun x : ℕ => I.graph.vertices.length + x)
      (List.getElem_idxOf (x := d) (xs := word) hi)
  have hrank : (referenceOrder I).idxOf (I.graph.vertices.length + d) =
      blockPrefix.length + (k + 1) := by
    rw [← hget]
    exact hn.idxOf_getElem _ hpos
  refine ⟨hget ▸ List.getElem_mem hpos, ?_, ?_⟩
  · rw [hvrank, hrank]
    omega
  · rw [hvrank, hrank]
    dsimp [k, i]
    omega

/-- Actual outgoing arguments decrease along the literal prescribed word. No inequality
between the two darts is assumed: comparing a dart with itself also satisfies this iff. -/
theorem referenceDrawing_fixedWord_arg_lt_iff {I : FixedRotationInput} (hI : Valid I)
    {v : ℕ} {word : List ℕ} (hw : I.orders.getD v none = some word)
    {d e : Dart I.graph} (hd : d.index ∈ word) (he : e.index ∈ word) :
    ((referenceDrawing I).germ (subdivisionDart I d)).arg <
      ((referenceDrawing I).germ (subdivisionDart I e)).arg ↔
        word.idxOf e.index < word.idxOf d.index := by
  have hs := fixedWord_rank_spec hI hw
  have hdv := fixedWord_dart_vertex hI hw hd
  have hev := fixedWord_dart_vertex hI hw he
  have hdl := hs.2 d.index hd
  have hel := hs.2 e.index he
  -- Both actual leaf names and the center belong to the enumeration before reading ranks.
  have hdc : ((referenceOrder I).idxOf v : ℝ) <
      ((referenceOrder I).idxOf (I.graph.vertices.length + d.index) : ℝ) :=
    Nat.cast_lt.mpr hdl.2.1
  have hec : ((referenceOrder I).idxOf v : ℝ) <
      ((referenceOrder I).idxOf (I.graph.vertices.length + e.index) : ℝ) :=
    Nat.cast_lt.mpr hel.2.1
  rw [referenceDrawing_subdivisionDart_germ, referenceDrawing_subdivisionDart_germ,
    hdv, hev]
  change (parabolaPoint _ - parabolaPoint _).arg <
    (parabolaPoint _ - parabolaPoint _).arg ↔ _
  rw [arg_parabolaChord_lt_iff (Nat.cast_nonneg _) hdc hec, Nat.cast_lt,
    hdl.2.2, hel.2.2]
  have hdi := List.idxOf_lt_length_of_mem hd
  have hei := List.idxOf_lt_length_of_mem he
  omega

/-- The actual directions at a fixed center distinguish original indexed ends, including
the two ends of an original loop and ends of parallel occurrences. -/
theorem referenceDrawing_fixedWord_directions_injective {I : FixedRotationInput} (hI : Valid I)
    {v : ℕ} {word : List ℕ} (hw : I.orders.getD v none = some word)
    {d e : Dart I.graph} (hd : d.index ∈ word) (he : e.index ∈ word)
    (heq : (referenceDrawing I).direction (subdivisionDart I d) =
      (referenceDrawing I).direction (subdivisionDart I e)) : d = e := by
  have harg : ((referenceDrawing I).germ (subdivisionDart I d)).arg =
      ((referenceDrawing I).germ (subdivisionDart I e)).arg :=
    Complex.arg_coe_angle_eq_iff.mp heq
  have hde := referenceDrawing_fixedWord_arg_lt_iff hI hw hd he
  have hed := referenceDrawing_fixedWord_arg_lt_iff hI hw he hd
  have hrank : word.idxOf d.index = word.idxOf e.index := by
    simp only [harg, lt_self_iff_false, false_iff] at hde hed
    omega
  exact (Dart.indexEquiv I.graph).injective
    (Fin.ext ((List.idxOf_inj hd).mp hrank))

/-- Clockwise is the reversed angular order `c,b,a`, since `sbtw` increases counterclockwise.
For three distinct original darts, this is exactly increasing cyclic order in the prescribed
word. No rotation or embedding of the full reference drawing is asserted. -/
theorem referenceDrawing_fixedWord_clockwise_iff {I : FixedRotationInput} (hI : Valid I)
    {v : ℕ} {word : List ℕ} (hw : I.orders.getD v none = some word)
    {a b c : Dart I.graph} (ha : a.index ∈ word) (hb : b.index ∈ word) (hc : c.index ∈ word)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    sbtw ((referenceDrawing I).direction (subdivisionDart I c))
      ((referenceDrawing I).direction (subdivisionDart I b))
      ((referenceDrawing I).direction (subdivisionDart I a)) ↔
        (word.idxOf a.index < word.idxOf b.index ∧ word.idxOf b.index < word.idxOf c.index) ∨
        (word.idxOf b.index < word.idxOf c.index ∧ word.idxOf c.index < word.idxOf a.index) ∨
        (word.idxOf c.index < word.idxOf a.index ∧ word.idxOf a.index < word.idxOf b.index) := by
  let D := referenceDrawing I
  let A := fun d : Dart I.graph => (D.germ (subdivisionDart I d)).arg
  have hmem {d : Dart I.graph} (hd : d.index ∈ word) :
      A d ∈ Set.Ioo (-(Real.pi / 2)) (-(Real.pi / 2) + 2 * Real.pi) := by
    have hs := (fixedWord_rank_spec hI hw).2 d.index hd
    have hv := fixedWord_dart_vertex hI hw hd
    have hre : 0 < (D.germ (subdivisionDart I d)).re := by
      rw [referenceDrawing_subdivisionDart_germ, hv]
      change 0 < ((referenceOrder I).idxOf (I.graph.vertices.length + d.index) : ℝ) -
        ((referenceOrder I).idxOf v : ℝ)
      exact sub_pos.mpr (Nat.cast_lt.mpr hs.2.1)
    refine ⟨Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hre), ?_⟩
    have hupper := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hre)
    dsimp [A]
    linarith only [hupper, Real.pi_pos]
  have hne {d e : Dart I.graph} (hd : d.index ∈ word) (he : e.index ∈ word) (hne : d ≠ e) :
      A d ≠ A e := by
    intro h
    exact hne (referenceDrawing_fixedWord_directions_injective hI hw hd he
      (congrArg (fun x : ℝ => (x : Real.Angle)) h))
  change sbtw (A c : Real.Angle) (A b : Real.Angle) (A a : Real.Angle) ↔ _
  rw [sbtw_angle_iff_cyclic_lt (hmem hc) (hmem hb) (hmem ha)
    (hne hc hb hbc.symm) (hne hb ha hab.symm) (hne hc ha hac.symm)]
  simp only [A, D, referenceDrawing_fixedWord_arg_lt_iff hI hw hc hb,
    referenceDrawing_fixedWord_arg_lt_iff hI hw hb ha,
    referenceDrawing_fixedWord_arg_lt_iff hI hw ha hc]
  tauto

/-- The boundary ports at a vertex realizing a prescribed word have the same clockwise
triples as the matching reference rays. The radius changes the port positions but does not
change their order as seen from the original center. -/
theorem cutPort_clockwise_iff_reference {I : FixedRotationInput} (hI : Valid I)
    {D : PolygonalDrawing I.graph} {r : RotationSystem I.graph}
    (hReal : D.Realizes r) (hfixed : Realizes I r) {ρ : ℝ} (hρ : 0 < ρ)
    {v : ℕ} {word : List ℕ} (hw : I.orders.getD v none = some word)
    {a b c : Dart I.graph} (ha : a.index ∈ word) (hb : b.index ∈ word) (hc : c.index ∈ word)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    sbtw (((D.cutPort ρ c - D.vertex v).arg : ℝ) : Real.Angle)
      (((D.cutPort ρ b - D.vertex v).arg : ℝ) : Real.Angle)
      (((D.cutPort ρ a - D.vertex v).arg : ℝ) : Real.Angle) ↔
    sbtw ((referenceDrawing I).direction (subdivisionDart I c))
      ((referenceDrawing I).direction (subdivisionDart I b))
      ((referenceDrawing I).direction (subdivisionDart I a)) := by
  have hav := fixedWord_dart_vertex hI hw ha
  have hbv := fixedWord_dart_vertex hI hw hb
  have hcv := fixedWord_dart_vertex hI hw hc
  exact (hReal.cutPort_clockwise v hρ (Metric.mem_ball_self hρ)
    a b c hav hbv hcv hab hbc hac).trans
    ((hfixed.mem_rotationInterval_iff_fixedWord hI hw ha hb hc hab hbc hac).trans
      (referenceDrawing_fixedWord_clockwise_iff hI hw ha hb hc hab hbc hac).symm)

end Cslib.Complexity.Graph.RotationRecognition
