/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.OrthogonalDrawing.Encoding
public import CslibFrontier.Computability.Complexity.Problems.Graph.OrthogonalDrawing.Routes
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Certificate
public import CslibFrontier.Foundations.Geometry.Orthogonal.Subdivision
import Mathlib.Data.List.GetD
import Mathlib.Tactic.IntervalCases

/-!
# Executed clockwise successors of an orthogonal drawing

Each dart reads the actual first or last segment of its supplied route. Four scans of the
actual dart list look for the next occupied cardinal ray, in the clockwise order east,
south, west, north. Binary vertex labels and coordinates remain lookup/comparison data;
neither coordinate magnitudes nor vertex names bound a loop.

This module defines the finite computation and its output bounds. Correctness requires
comparing it with actual segment germs and deriving numerical genus; neither invariant
is an input to the computation.
-/

public section

namespace Cslib.Complexity.Graph.OrthogonalDrawing

open Cslib.Orthogonal

/-- A dart's actual endpoint label, with the same zero fallback as indexed graph darts. -/
@[expose] def endpoint (G : Graph) (i : ℕ) : ℕ :=
  G.incidenceVertices.getD i 0

/-- The next point on the route leaving an indexed dart's endpoint. Shared normalization
first fixes the graph's edge orientation; malformed lists keep the original zero fallback. -/
@[expose] def exitNeighbor (G : Graph) (d : OrthogonalDrawing) (i : ℕ) : Point :=
  let route := (sourceRoute G d (i / 2)).reverse
  if i % 2 = 0 then route.getD 1 (0, 0)
  else route.getD (route.length - 2) (0, 0)

/-- A fixed clockwise rank: east, south, west, north. The direction function's existing
fallback also makes this a total rank on malformed or degenerate segments. -/
@[expose] def clockwiseRank (a b : Point) : ℕ :=
  let ray := direction a b
  if ray = (1, 0) then 0 else if ray = (0, -1) then 1 else if ray = (-1, 0) then 2 else 3

/-- Clockwise cardinal rank of the actual outgoing end segment of an indexed route. -/
@[expose] def dartRank (G : Graph) (d : OrthogonalDrawing) (i : ℕ) : ℕ :=
  clockwiseRank (drawingPosition G d (endpoint G i)) (exitNeighbor G d i)

/-- Enumerate candidate successors by positive clockwise displacement, keeping every
indexed incidence distinct. The only nonconstant scan bound is the actual edge-list length. -/
@[expose] def clockwiseCandidates (G : Graph) (d : OrthogonalDrawing) (i : ℕ) : List ℕ :=
  (List.range 4).flatMap fun step =>
    (List.range (2 * G.edges.length)).filter fun j =>
      decide (endpoint G j = endpoint G i ∧
        dartRank G d j = (dartRank G d i + step + 1) % 4)

/-- Next occupied clockwise cardinal ray. The fourth pass includes the starting ray,
so a genuine degree-one vertex fixes its only dart. -/
@[expose] def clockwiseSuccessor (G : Graph) (d : OrthogonalDrawing) (i : ℕ) : ℕ :=
  (clockwiseCandidates G d i).headD i

/-- Emit one actual binary successor entry per indexed edge end. This does not perform
a planarity search or use an abstract rotation chosen in a proof. -/
@[expose] def rotationCertificate (G : Graph) (d : OrthogonalDrawing) : RotationCertificate :=
  ⟨(List.range (2 * G.edges.length)).map (clockwiseSuccessor G d)⟩

/-- An indexed dart reads the corresponding actual route end, with the original total
fallbacks. This separates binary edge/end arithmetic from geometric callers. -/
theorem exitNeighbor_index (G : Graph) (d : OrthogonalDrawing)
    (e : Fin G.edges.length) (side : Bool) :
    exitNeighbor G d (Dart.index (G := G) (e, side)) =
      let r := (sourceRoute G d e).reverse
      if side then r.getD (r.length - 2) (0, 0) else r.getD 1 (0, 0) := by
  cases side <;> simp only [exitNeighbor, Dart.index, Bool.toNat_false, Bool.toNat_true,
    Nat.add_zero, Bool.false_eq_true, ↓reduceIte, Nat.mul_div_right _ two_pos, Nat.mul_mod_right,
    show (2 * e.val + 1) / 2 = e.val by omega, show (2 * e.val + 1) % 2 = 1 by omega,
    Nat.one_ne_zero]

/-- Every direction has one of the four fixed ranks, even on malformed route data. -/
theorem clockwiseRank_lt (a b : Point) : clockwiseRank a b < 4 := by
  dsimp only [clockwiseRank]
  split_ifs <;> omega

/-- The output table has exactly the actual number of indexed darts. -/
@[simp] theorem length_rotationCertificate (G : Graph) (d : OrthogonalDrawing) :
    (rotationCertificate G d).successor.length = 2 * G.edges.length := by
  simp [rotationCertificate]

/-- A candidate is precisely a same-vertex dart together with its positive clockwise
displacement. Distinct edge occurrences and end tags remain distinct natural indices. -/
theorem mem_clockwiseCandidates_iff (G : Graph) (d : OrthogonalDrawing) (i j : ℕ) :
    j ∈ clockwiseCandidates G d i ↔
      ∃ step < 4, j < 2 * G.edges.length ∧ endpoint G j = endpoint G i ∧
        dartRank G d j = (dartRank G d i + step + 1) % 4 := by
  simp only [clockwiseCandidates, List.mem_flatMap, List.mem_range, List.mem_filter,
    decide_eq_true_eq]

/-- Every actual input dart appears in the fourth pass. In particular the executed scan
has a candidate even before requiring a valid geometric drawing. -/
theorem self_mem_clockwiseCandidates (G : Graph) (d : OrthogonalDrawing) {i : ℕ}
    (hi : i < 2 * G.edges.length) : i ∈ clockwiseCandidates G d i := by
  apply (mem_clockwiseCandidates_iff G d i i).mpr
  refine ⟨3, by decide, hi, rfl, ?_⟩
  have hr := clockwiseRank_lt (drawingPosition G d (endpoint G i)) (exitNeighbor G d i)
  change dartRank G d i < 4 at hr
  omega

/-- The executed successor remains an actual same-vertex dart on every raw drawing.
Its geometric correctness requires more, but no malformed point list can escape this bound. -/
theorem clockwiseSuccessor_spec (G : Graph) (d : OrthogonalDrawing) {i : ℕ}
    (hi : i < 2 * G.edges.length) :
    clockwiseSuccessor G d i < 2 * G.edges.length ∧
      endpoint G (clockwiseSuccessor G d i) = endpoint G i := by
  have hm := self_mem_clockwiseCandidates G d hi
  have hc : clockwiseSuccessor G d i ∈ clockwiseCandidates G d i := by
    unfold clockwiseSuccessor
    generalize hword : clockwiseCandidates G d i = word at hm ⊢
    cases word with
    | nil => simp at hm
    | cons head tail => exact List.mem_cons_self
  obtain ⟨_, _, hb, hv, _⟩ := (mem_clockwiseCandidates_iff G d i _).mp hc
  exact ⟨hb, hv⟩

/-- The executed scan returns the unique dart on the first occupied clockwise ray.
The hypotheses concern the actual four bounded scans, including the fourth return ray;
they do not supply a permutation or a genus certificate. -/
theorem clockwiseSuccessor_eq_of_firstRay (G : Graph) (d : OrthogonalDrawing)
    {i j step : ℕ} (hj : j < 2 * G.edges.length) (hstep : step < 4)
    (hv : endpoint G j = endpoint G i)
    (hr : dartRank G d j = (dartRank G d i + step + 1) % 4)
    (hbefore : ∀ k < step, ∀ b < 2 * G.edges.length,
      endpoint G b = endpoint G i →
        dartRank G d b ≠ (dartRank G d i + k + 1) % 4)
    (hunique : ∀ b < 2 * G.edges.length, endpoint G b = endpoint G i →
      dartRank G d b = dartRank G d j → b = j) :
    clockwiseSuccessor G d i = j := by
  let slice (k : ℕ) := (List.range (2 * G.edges.length)).filter fun b =>
    decide (endpoint G b = endpoint G i ∧
      dartRank G d b = (dartRank G d i + k + 1) % 4)
  have hempty (k : ℕ) (hk : k < step) : slice k = [] :=
    List.filter_eq_nil_iff.mpr fun b hb => by
      simp only [decide_eq_true_eq, not_and]
      exact hbefore k hk b (List.mem_range.mp hb)
  have hmem : j ∈ slice step :=
    List.mem_filter.mpr ⟨List.mem_range.mpr hj, decide_eq_true ⟨hv, hr⟩⟩
  obtain ⟨tail, htail⟩ : ∃ tail, slice step = j :: tail := by
    cases hs : slice step with
    | nil => simp [hs] at hmem
    | cons b tail =>
      have hb := List.mem_filter.mp (hs ▸ List.mem_cons_self)
      obtain ⟨hvertex, hrank⟩ := of_decide_eq_true hb.2
      exact ⟨tail, by rw [hunique b (List.mem_range.mp hb.1) hvertex (hrank.trans hr.symm)]⟩
  change ((List.range 4).flatMap slice).headD i = j
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  interval_cases step
  · rw [htail]; rfl
  · rw [hempty 0 (by omega), List.nil_append, htail]; rfl
  · rw [hempty 0 (by omega), hempty 1 (by omega)]; simp [htail]
  · rw [hempty 0 (by omega), hempty 1 (by omega), hempty 2 (by omega)]; simp [htail]

end Cslib.Complexity.Graph.OrthogonalDrawing
