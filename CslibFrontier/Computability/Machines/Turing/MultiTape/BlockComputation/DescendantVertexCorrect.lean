/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DescendantVertex
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.NativeChildVertex
import CslibFrontier.Foundations.Data.List.SortedCount
import Mathlib.Data.List.GetD

/-!
# Exact descriptors of compressed vertex origins

`NativeAncestry` is a semantic trace of actual `NativeChild.nativeChild` constructions. Each
frame has the exact parent vertex count and its native symbol agrees with the group's word
table on every parent vertex. The trace stores the call parameters needed to identify packet
descriptors at birth; none of this data is added to the encoded compressed query.

Every valid descendant vertex has a unique numerical origin. At an accepted origin its indexed
descriptor is exactly the descriptor at birth. In particular, retaining an earlier packet does
not replace its context with the precision or interpolation data of a later split. Distinct
origins are distinguished by their indices and stages, even when their descriptors coincide.

These are original semantics of the native child construction and its compressed provenance
relation. Machine running-time claims remain with the native programs.

## Main results

* `Turing.MultiTapeTM.DescendantVertex.HasOrigin.unique`: numerical origins are unique.
* `Turing.MultiTapeTM.DescendantVertex.NativeAncestry.descriptor_eq_birthDescriptor`: an
  accepted origin preserves the actual descriptor at birth.
* `Turing.MultiTapeTM.DescendantVertex.NativeAncestry.existsUnique_origin`: each in-range
  vertex of a represented native ancestry has exactly one numerical origin.
-/

public section

namespace Turing.MultiTapeTM.DescendantVertex

open Cslib BalancedSchedules Circuits.Frontier NativeChild NativeChild.EndpointQuery
open DescendantEndpoint (Frame)

/-- A represented actual seed computes the mathematical label symbol on every genuine key. -/
theorem symbol_ofSeed {U a : ℕ} (edges : ℕ) (seed : SeededLabels.Seed U (6 * a))
    (i : Fin a) (group : ℕ) (v : Fin U) :
    symbol (Frame.ofSeed edges seed i group) v = (Labels.ofSeed U a seed i group).symbol v := by
  have h := MultiTapeATM.SeededChildCounts.symbol_of_seed seed i group 0 v
    ⟨0, fun _ _ => False⟩
  simpa only [symbol, rankQuery, Frame.ofSeed, Labels.split, Labels.ofSeed, v.isLt,
    ite_true] using h

private theorem getElem?_retained (f : Frame) {v : ℕ} (hv : v < f.vertices)
    (hg : symbol f v = f.group) :
    ((List.range f.vertices).filter fun u => symbol f u = f.group)[retained f v]? = some v := by
  have h := List.getElem?_filter_countP_take (fun u => decide (symbol f u = f.group))
    (l := List.range f.vertices) (r := v) (by simpa using hv) (by simpa using hg)
  simpa only [List.take_range, retained, List.getElem_range] using h

private theorem retained_lt (f : Frame) {v : ℕ} (hv : v < f.vertices)
    (hg : symbol f v = f.group) : retained f v < retained f f.vertices := by
  have h := (List.getElem?_eq_some_iff.mp (getElem?_retained f hv hg)).1
  simpa only [retained, Nat.min_self, List.countP_eq_length_filter] using h

/-- An accepted birth stage belongs to the original network or to a stored split. -/
theorem HasOrigin.stage_le {frames : List Frame} {vertices vertex : ℕ} {origin : Origin}
    (h : HasOrigin vertices vertex origin frames) : origin.stage ≤ frames.length := by
  cases frames with
  | nil => exact h.2.1.le
  | cons f fs =>
    simp only [List.length_cons]
    rcases h.2 with h | h <;> omega

/-- A current vertex has at most one birth stage and index, regardless of descriptor equality. -/
theorem HasOrigin.unique {frames : List Frame} {vertices vertex : ℕ} {left right : Origin}
    (hl : HasOrigin vertices vertex left frames) (hr : HasOrigin vertices vertex right frames) :
    left = right := by
  induction frames generalizing vertices vertex with
  | nil =>
    obtain ⟨_, hls, hli⟩ := hl
    obtain ⟨_, hrs, hri⟩ := hr
    cases left
    cases right
    simp only at hls hli hrs hri
    congr <;> omega
  | cons f fs ih =>
    rcases hl.2 with ⟨hls, hli⟩ | ⟨hls, u, hu, hgu, hli, hlu⟩
    · rcases hr.2 with ⟨hrs, hri⟩ | ⟨hrs, v, hv, hgv, hri, _⟩
      · cases left
        cases right
        simp only at hls hli hrs hri
        congr <;> omega
      · have hlt := retained_lt f hv hgv
        omega
    · rcases hr.2 with ⟨hrs, hri⟩ | ⟨hrs, v, hv, hgv, hri, hrv⟩
      · have hlt := retained_lt f hu hgu
        omega
      · have hgetu := getElem?_retained f hu hgu
        have hgetv := getElem?_retained f hv hgv
        have heq : retained f u = retained f v := hli.symm.trans hri
        rw [heq] at hgetu
        have huv : u = v := Option.some.inj (hgetu.symm.trans hgetv)
        subst v
        exact ih hlu hrv

/-- A semantic trace of actual native children. Its call data describes the mathematical
networks and their birth descriptors; it is not an encoded input or runtime certificate. -/
inductive NativeAncestry {T : Type} (root : DescribedNetwork (VertexDesc T)) :
    List Frame → DescribedNetwork (VertexDesc T) → Type
  | nil : NativeAncestry root [] root
  | cons {frames : List Frame} {parent : DescribedNetwork (VertexDesc T)} {f : Frame}
      (older : NativeAncestry root frames parent)
      (fl : List ℕ) (pt : ℕ) (t : ℤ) (ζ : List ℕ) (rows : ℕ)
      (packing : (List (List ℕ) × List (List ℕ)) × ℕ × List (ℕ × ℕ)) (β : List ℕ)
      (size : f.vertices = parent.vertices.length)
      (labels : ∀ v, v < f.vertices → symbol f v =
        (groupsOf rows f.coordinate parent.vertices.length packing.1).getD v 0) :
      NativeAncestry root (f :: frames)
        (nativeChild fl f.coordinates f.coordinate pt t ζ rows parent packing β f.group)

variable {T : Type} {root : DescribedNetwork (VertexDesc T)}

/-- Read an original descriptor at stage zero, or the exact packet descriptor in its birth
network. Subsequent calls only pass the lookup to the older trace. -/
@[expose] def NativeAncestry.birthDescriptor : {frames : List Frame} →
    {D : DescribedNetwork (VertexDesc T)} → NativeAncestry root frames D →
      Origin → Option (VertexDesc T)
  | [], _, .nil, origin =>
    if origin.stage = 0 then (root.vertices[origin.index]?).map Prod.snd else none
  | _, _, .cons (frames := fs) (parent := parent) (f := f)
      older fl pt t ζ rows packing β _ _, origin =>
    if origin.stage = fs.length + 1 then
      ((nativeChild fl f.coordinates f.coordinate pt t ζ rows parent packing β f.group).vertices[
        retained f f.vertices + origin.index]?).map Prod.snd
    else older.birthDescriptor origin

private theorem retained_eq_count {f : Frame} {rows : ℕ}
    {D : DescribedNetwork (VertexDesc T)}
    {packing : (List (List ℕ) × List (List ℕ)) × ℕ × List (ℕ × ℕ)}
    (hsize : f.vertices = D.vertices.length)
    (hlabels : ∀ v, v < f.vertices → symbol f v =
      (groupsOf rows f.coordinate D.vertices.length packing.1).getD v 0) (bound : ℕ) :
    retained f bound =
      ((groupsOf rows f.coordinate D.vertices.length packing.1).take bound).count f.group := by
  let split : Split := ⟨f.vertices, f.group, symbol f, fun _ _ _ => False⟩
  exact Split.vertexRank_eq (s := split)
    (by simpa only [groupsOf, List.length_map, List.length_range] using hsize)
    (fun v hv => hlabels v hv) bound

/-- The descriptor at an accepted descendant number is exactly the descriptor at its stated
birth. This equality retains an inherited packet's original context and exponent slice. -/
theorem NativeAncestry.descriptor_eq_birthDescriptor {frames : List Frame}
    {D : DescribedNetwork (VertexDesc T)} (ancestry : NativeAncestry root frames D)
    {vertex : ℕ} {origin : Origin}
    (h : HasOrigin D.vertices.length vertex origin frames) :
    (D.vertices[vertex]?).map Prod.snd = ancestry.birthDescriptor origin := by
  induction ancestry generalizing vertex with
  | nil =>
    obtain ⟨_, hs, hi⟩ := h
    simp [NativeAncestry.birthDescriptor, hs, hi]
  | @cons frames parent f older fl pt t ζ rows packing β hsize hlabels ih =>
    rcases h.2 with ⟨hstage, hindex⟩ | ⟨hstage, v, hv, hg, hindex, hparent⟩
    · simp [NativeAncestry.birthDescriptor, hstage, hindex]
    · have hne : origin.stage ≠ frames.length + 1 := by omega
      rw [NativeAncestry.birthDescriptor, ite_eq_right hne]
      have hvr : v < parent.vertices.length := by omega
      have hvg : (groupsOf rows f.coordinate parent.vertices.length packing.1).getD v 0 =
          f.group := (hlabels v hv).symm.trans hg
      have hlookup := getElem?_vertices_nativeChild_retained fl f.coordinates f.coordinate
        pt t ζ rows parent packing β f.group hvr hvg
      dsimp only at hlookup
      rw [hindex, retained_eq_count hsize hlabels, hlookup]
      change some (parent.vertices.getD v defaultVertex).2 = older.birthDescriptor origin
      have hold := ih (by simpa only [hsize] using hparent)
      simpa only [List.getD_eq_getElem _ _ hvr, List.getElem?_eq_getElem hvr,
        Option.map_some] using hold

/-- Every actual descendant vertex has one numerical origin; the proof follows the exact
retained/packet alternative at its list index. -/
theorem NativeAncestry.existsUnique_origin {frames : List Frame}
    {D : DescribedNetwork (VertexDesc T)} (ancestry : NativeAncestry root frames D)
    {vertex : ℕ} (hvertex : vertex < D.vertices.length) :
    ∃! origin, HasOrigin D.vertices.length vertex origin frames := by
  suffices ∃ origin, HasOrigin D.vertices.length vertex origin frames by
    obtain ⟨origin, horigin⟩ := this
    exact ⟨origin, horigin, fun _ h => h.unique horigin⟩
  induction ancestry generalizing vertex with
  | nil => exact ⟨⟨0, vertex⟩, hvertex, rfl, rfl⟩
  | @cons frames parent f older fl pt t ζ rows packing β hsize hlabels ih =>
    have hlookup := List.getElem?_eq_getElem hvertex
    rcases (getElem?_vertices_nativeChild_iff fl f.coordinates f.coordinate pt t ζ rows parent
      packing β f.group).mp hlookup with
      ⟨v, hv, hg, hindex, _⟩ | ⟨q, hq, hindex, _⟩
    · obtain ⟨origin, horigin⟩ := ih hv
      refine ⟨origin, hvertex, Or.inr ⟨?_, v, ?_, ?_, ?_, ?_⟩⟩
      · exact horigin.stage_le
      · omega
      · exact (hlabels v (by omega)).trans hg
      · rw [retained_eq_count hsize hlabels]
        exact hindex.symm
      · simpa only [hsize] using horigin
    · refine ⟨⟨frames.length + 1, q⟩, hvertex, Or.inl ⟨rfl, ?_⟩⟩
      rw [retained_eq_count hsize hlabels, hsize,
        List.take_of_length_le (by simp [groupsOf])]
      exact hindex.symm

end Turing.MultiTapeTM.DescendantVertex
