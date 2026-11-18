/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.ReferenceDrawing
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
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
Hanani–Tutte/query-completeness theorem. The remaining recognition objective is tracked in
[issue #3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

## Main definitions

* `Cslib.Complexity.Graph.RotationRecognition.subdivisionDart`: the original end's actual
  first/last subdivision dart, preserving occurrence and end tag.

## Main results

* `Cslib.Complexity.Graph.RotationRecognition.subdivisionDart_endpoints`: the original center
  and the fresh leaf named by the original binary dart index.
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

/-- Retain the original occurrence and end tag while selecting its incident first or last
subdivision segment. In particular, the two original loop ends select different segments. -/
@[expose] def subdivisionDart (I : FixedRotationInput) (d : Dart I.graph) :
    Dart (subdivisionGraph I) :=
  (⟨3 * d.1.val + if d.2 then 2 else 0, by
    have hi := d.1.isLt
    simp only [subdivisionGraph, List.length_map, length_subdivide]
    cases d.2 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩, d.2)

private theorem subdivide_getElem? (I : FixedRotationInput)
    (i : Fin I.graph.edges.length) (k : Fin 3) :
    (subdivide I)[3 * i.val + k.val]? = some
      ([((I.graph.edges[i].1, I.graph.vertices.length + 2 * i.val),
          (I.orders.getD I.graph.edges[i].1 none).isSome),
        ((I.graph.vertices.length + 2 * i.val, I.graph.vertices.length + 2 * i.val + 1), false),
        ((I.graph.vertices.length + 2 * i.val + 1, I.graph.edges[i].2),
          (I.orders.getD I.graph.edges[i].2 none).isSome)] : List Segment)[k] := by
  let entries := I.graph.edges.zipIdx
  let emit : (ℕ × ℕ) × ℕ → List Segment := fun ((u, v), j) =>
    [((u, I.graph.vertices.length + 2 * j), (I.orders.getD u none).isSome),
      ((I.graph.vertices.length + 2 * j, I.graph.vertices.length + 2 * j + 1), false),
      ((I.graph.vertices.length + 2 * j + 1, v), (I.orders.getD v none).isSome)]
  have hi : i.val < entries.length := by simp [entries]
  have hsplit : entries = entries.take i.val ++ entries[i.val] :: entries.drop (i.val + 1) := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  have hprefix : ((entries.take i.val).flatMap emit).length = 3 * i.val := by
    simp [emit, List.length_flatMap, Nat.min_eq_left hi.le, Nat.mul_comm]
  change (entries.flatMap emit)[3 * i.val + k.val]? = _
  rw [hsplit, List.flatMap_append, List.flatMap_cons,
    List.getElem?_append_right (by omega), hprefix]
  have hsub : 3 * i.val + k.val - 3 * i.val = k.val := by omega
  rw [hsub, List.getElem?_append_left (by simp [emit])]
  simp [emit, entries, List.getElem_zipIdx]

/-- The selected outgoing end has its original center and its own fresh occurrence leaf. -/
theorem subdivisionDart_endpoints (I : FixedRotationInput) (d : Dart I.graph) :
    (subdivisionDart I d).vertex = d.vertex ∧
      (subdivisionDart I d).reverse.vertex = I.graph.vertices.length + d.index := by
  rcases d with ⟨⟨i, hi⟩, b⟩
  cases b
  · have h := subdivide_getElem? I ⟨i, hi⟩ 0
    simp only [Fin.getElem_fin, Fin.val_zero, Nat.add_zero, List.getElem_cons_zero] at h
    have he : (subdivisionGraph I).edges.getD (3 * i) (0, 0) =
        (I.graph.edges[i].1, I.graph.vertices.length + 2 * i) := by
      simp only [subdivisionGraph, List.getD_eq_getElem?_getD, List.getElem?_map, h]
      rfl
    change ((subdivisionGraph I).edges.getD (3 * i) (0, 0)).1 =
      (I.graph.edges.getD i (0, 0)).1 ∧
      ((subdivisionGraph I).edges.getD (3 * i) (0, 0)).2 = I.graph.vertices.length + 2 * i
    rw [he, List.getD_eq_getElem _ _ hi]
    exact ⟨rfl, rfl⟩
  · have h := subdivide_getElem? I ⟨i, hi⟩ 2
    change (subdivide I)[3 * i + 2]? = some
      ((I.graph.vertices.length + 2 * i + 1, I.graph.edges[i].2),
        (I.orders.getD I.graph.edges[i].2 none).isSome) at h
    have he : (subdivisionGraph I).edges.getD (3 * i + 2) (0, 0) =
        (I.graph.vertices.length + 2 * i + 1, I.graph.edges[i].2) := by
      simp only [subdivisionGraph, List.getD_eq_getElem?_getD, List.getElem?_map, h]
      rfl
    change ((subdivisionGraph I).edges.getD (3 * i + 2) (0, 0)).2 =
      (I.graph.edges.getD i (0, 0)).2 ∧
      ((subdivisionGraph I).edges.getD (3 * i + 2) (0, 0)).1 =
        I.graph.vertices.length + (2 * i + 1)
    rw [he, List.getD_eq_getElem _ _ hi, Nat.add_assoc]
    exact ⟨rfl, rfl⟩

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

private theorem fixedWord_dart_vertex {I : FixedRotationInput} (hI : Valid I) {v : ℕ}
    {word : List ℕ} (hw : I.orders.getD v none = some word)
    {d : Dart I.graph} (hd : d.index ∈ word) : d.vertex = v := by
  have hf := (hI.2.2.2 v word hw).2 d.index |>.mp hd
  exact (Dart.vertex_index d).symm.trans (mem_fiber.mp hf).2

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

end Cslib.Complexity.Graph.RotationRecognition
