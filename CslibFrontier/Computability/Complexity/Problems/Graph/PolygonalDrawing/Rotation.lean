/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Germs
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Basic
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.FiberOrder
import CslibFrontier.Foundations.Geometry.Polygonal.AngleOrder
import Mathlib.Data.Finset.Sort

/-!
# The clockwise rotation of a polygonal embedding

The actual outgoing germs of an embedding determine one rotation at every vertex. Sorting
their principal arguments in decreasing order chooses a cyclic start without changing their
clockwise circular order. No rotation is supplied as an additional premise. Loops retain both
ends, and empty fibers, arbitrary degrees and disconnected components need no special choice.

This is a static construction for finite polygonal embeddings with arbitrary complex
coordinates. It makes no claim about recognition, coordinate encodings or runtime.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

variable {G : Graph} {D : PolygonalDrawing G}

private theorem arg_injective_at (hD : D.IsEmbedding) (v : ℕ) :
    Function.Injective (fun d : {d : Dart G // d.vertex = v} => -(D.germ d.val).arg) := by
  intro a b hab
  apply Subtype.ext
  apply hD.directions_injective a.val b.val (a.property.trans b.property.symm)
  exact congrArg (fun x : ℝ => (x : Real.Angle)) (neg_injective hab)

@[instance_reducible] private noncomputable def clockwiseOrder (hD : D.IsEmbedding) (v : ℕ) :
    LinearOrder {d : Dart G // d.vertex = v} :=
  LinearOrder.lift' (fun d => -(D.germ d.val).arg) (arg_injective_at hD v)

private noncomputable def clockwiseRank (hD : D.IsEmbedding) (v : ℕ) :
    {d : Dart G // d.vertex = v} ≃ Fin (Fintype.card {d : Dart G // d.vertex = v}) := by
  -- The dart subtype also inherits its unrelated lexicographic order.
  -- Bind the germ order's primitive relations explicitly.
  letI := clockwiseOrder hD v
  letI : LE {d : Dart G // d.vertex = v} := (clockwiseOrder hD v).toLE
  letI : LT {d : Dart G // d.vertex = v} := (clockwiseOrder hD v).toLT
  exact (Fintype.orderIsoFinOfCardEq {d : Dart G // d.vertex = v} rfl).symm.toEquiv

private theorem clockwiseRank_lt_iff (hD : D.IsEmbedding) (v : ℕ)
    (a b : {d : Dart G // d.vertex = v}) :
    clockwiseRank hD v a < clockwiseRank hD v b ↔
      (D.germ b.val).arg < (D.germ a.val).arg := by
  let := clockwiseOrder hD v
  let : Preorder {d : Dart G // d.vertex = v} := (clockwiseOrder hD v).toPreorder
  let : LE {d : Dart G // d.vertex = v} := (clockwiseOrder hD v).toLE
  let : LT {d : Dart G // d.vertex = v} := (clockwiseOrder hD v).toLT
  change (Fintype.orderIsoFinOfCardEq {d : Dart G // d.vertex = v} rfl).symm a <
    (Fintype.orderIsoFinOfCardEq {d : Dart G // d.vertex = v} rfl).symm b ↔ _
  rw [OrderIso.lt_iff_lt]
  change -(D.germ a.val).arg < -(D.germ b.val).arg ↔ _
  exact neg_lt_neg_iff

/-- The rotation read from an embedding's actual outgoing rays, in clockwise order. -/
noncomputable def IsEmbedding.rotation (hD : D.IsEmbedding) : RotationSystem G :=
  RotationSystem.ofFiberEquiv (clockwiseRank hD)

/-- Reading the clockwise rotation of an embedding recovers its literal geometric order.
The nonzero and distinct-ray conditions follow from full route simplicity and contacts. -/
theorem IsEmbedding.realizes_rotation (hD : D.IsEmbedding) : D.Realizes hD.rotation := by
  refine ⟨hD.germ_ne_zero, hD.directions_injective, ?_⟩
  intro a b c hab hbc hneab hnebc hneac
  let a' : {d : Dart G // d.vertex = a.vertex} := ⟨a, rfl⟩
  let b' : {d : Dart G // d.vertex = a.vertex} := ⟨b, hab.symm⟩
  let c' : {d : Dart G // d.vertex = a.vertex} := ⟨c, (hab.trans hbc).symm⟩
  let m := min (D.germ a).arg (min (D.germ b).arg (D.germ c).arg)
  let cut := (-Real.pi + m) / 2
  have hm : -Real.pi < m :=
    lt_min (Complex.neg_pi_lt_arg _) (lt_min (Complex.neg_pi_lt_arg _)
      (Complex.neg_pi_lt_arg _))
  have hcut : cut < m := by dsimp [cut]; linarith
  have hcut' : -Real.pi < cut := by dsimp [cut]; linarith
  have mem_turn (x : ℂ) (hx : m ≤ x.arg) :
      x.arg ∈ Set.Ioo cut (cut + 2 * Real.pi) :=
    ⟨hcut.trans_le hx, by linarith [Complex.arg_le_pi x]⟩
  have ha := mem_turn (D.germ a) (min_le_left _ _)
  have hb := mem_turn (D.germ b) ((min_le_right _ _).trans (min_le_left _ _))
  have hc := mem_turn (D.germ c) ((min_le_right _ _).trans (min_le_right _ _))
  have harg {x y : Dart G} (hxy : x.vertex = y.vertex) (hne : x ≠ y) :
      (D.germ x).arg ≠ (D.germ y).arg := fun h =>
    hne (hD.directions_injective x y hxy (congrArg (fun t : ℝ => (t : Real.Angle)) h))
  rw [show hD.rotation = RotationSystem.ofFiberEquiv (clockwiseRank hD) from rfl,
    RotationSystem.mem_rotationInterval_ofFiberEquiv_iff (clockwiseRank hD) a.vertex
      a' b' c' (fun h => hneab (congrArg Subtype.val h))
      (fun h => hnebc (congrArg Subtype.val h)) (fun h => hneac (congrArg Subtype.val h))]
  simp only [clockwiseRank_lt_iff, a', b', c', direction]
  exact (Polygonal.sbtw_angle_iff_cyclic_lt hc hb ha
    (harg hbc.symm hnebc.symm) (harg hab.symm hneab.symm)
    (harg (hab.trans hbc).symm hneac.symm)).trans (by tauto)

end Cslib.Complexity.Graph.PolygonalDrawing
