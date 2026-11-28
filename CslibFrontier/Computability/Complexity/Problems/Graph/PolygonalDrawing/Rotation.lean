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
# The clockwise rotation of outgoing polygonal germs

Distinct outgoing directions determine one rotation at every vertex. Sorting
their principal arguments in decreasing order chooses a cyclic start without changing their
clockwise circular order. No rotation is supplied as an additional premise. Loops retain both
ends, and empty fibers, arbitrary degrees and disconnected components need no special choice.

This is a static construction for finite polygonal drawings with arbitrary complex
coordinates. It makes no claim about recognition, coordinate encodings or runtime.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

variable {G : Graph} {D : PolygonalDrawing G}

section Directions

variable (hdir : ∀ a b : Dart G, a.vertex = b.vertex → D.direction a = D.direction b → a = b)

include hdir

private theorem arg_injective_at (v : ℕ) :
    Function.Injective (fun d : {d : Dart G // d.vertex = v} => -(D.germ d.val).arg) := by
  intro a b hab
  apply Subtype.ext
  apply hdir a.val b.val (a.property.trans b.property.symm)
  exact congrArg (fun x : ℝ => (x : Real.Angle)) (neg_injective hab)

@[instance_reducible] private noncomputable def clockwiseOrder (v : ℕ) :
    LinearOrder {d : Dart G // d.vertex = v} :=
  LinearOrder.lift' (fun d => -(D.germ d.val).arg) (arg_injective_at hdir v)

private noncomputable def clockwiseRank (v : ℕ) :
    {d : Dart G // d.vertex = v} ≃ Fin (Fintype.card {d : Dart G // d.vertex = v}) := by
  -- The dart subtype also inherits its unrelated lexicographic order.
  -- Bind the germ order's primitive relations explicitly.
  letI := clockwiseOrder hdir v
  letI : LE {d : Dart G // d.vertex = v} := (clockwiseOrder hdir v).toLE
  letI : LT {d : Dart G // d.vertex = v} := (clockwiseOrder hdir v).toLT
  exact (Fintype.orderIsoFinOfCardEq {d : Dart G // d.vertex = v} rfl).symm.toEquiv

private theorem clockwiseRank_lt_iff (v : ℕ)
    (a b : {d : Dart G // d.vertex = v}) :
    clockwiseRank hdir v a < clockwiseRank hdir v b ↔
      (D.germ b.val).arg < (D.germ a.val).arg := by
  let := clockwiseOrder hdir v
  let : Preorder {d : Dart G // d.vertex = v} := (clockwiseOrder hdir v).toPreorder
  let : LE {d : Dart G // d.vertex = v} := (clockwiseOrder hdir v).toLE
  let : LT {d : Dart G // d.vertex = v} := (clockwiseOrder hdir v).toLT
  change (Fintype.orderIsoFinOfCardEq {d : Dart G // d.vertex = v} rfl).symm a <
    (Fintype.orderIsoFinOfCardEq {d : Dart G // d.vertex = v} rfl).symm b ↔ _
  rw [OrderIso.lt_iff_lt]
  change -(D.germ a.val).arg < -(D.germ b.val).arg ↔ _
  exact neg_lt_neg_iff

end Directions

/-- Read the clockwise rotation from the distinct outgoing directions at each vertex. -/
noncomputable def rotationOfDirections (D : PolygonalDrawing G)
    (hdir : ∀ a b : Dart G, a.vertex = b.vertex → D.direction a = D.direction b → a = b) :
    RotationSystem G := RotationSystem.ofFiberEquiv (clockwiseRank hdir)

/-- Nonzero, distinct outgoing rays realize the rotation read from their directions.
The rest of the routes may cross. -/
theorem realizes_rotationOfDirections (D : PolygonalDrawing G) (hnz : ∀ d, D.germ d ≠ 0)
    (hdir : ∀ a b : Dart G, a.vertex = b.vertex → D.direction a = D.direction b → a = b) :
    D.Realizes (D.rotationOfDirections hdir) := by
  refine ⟨hnz, hdir, ?_⟩
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
    hne (hdir x y hxy (congrArg (fun t : ℝ => (t : Real.Angle)) h))
  rw [rotationOfDirections,
    RotationSystem.mem_rotationInterval_ofFiberEquiv_iff (clockwiseRank hdir) a.vertex
      a' b' c' (fun h => hneab (congrArg Subtype.val h))
      (fun h => hnebc (congrArg Subtype.val h)) (fun h => hneac (congrArg Subtype.val h))]
  simp only [clockwiseRank_lt_iff, a', b', c', direction]
  exact (Polygonal.sbtw_angle_iff_cyclic_lt hc hb ha
    (harg hbc.symm hnebc.symm) (harg hab.symm hneab.symm)
    (harg (hab.trans hbc).symm hneac.symm)).trans (by tauto)

/-- The rotation read from an embedding's actual outgoing rays, in clockwise order. -/
noncomputable def IsEmbedding.rotation (hD : D.IsEmbedding) : RotationSystem G :=
  D.rotationOfDirections hD.directions_injective

/-- Reading the clockwise rotation of an embedding recovers its literal geometric order.
The nonzero and distinct-ray conditions follow from full route simplicity and contacts. -/
theorem IsEmbedding.realizes_rotation (hD : D.IsEmbedding) : D.Realizes hD.rotation :=
  D.realizes_rotationOfDirections hD.germ_ne_zero hD.directions_injective

/-- A drawing realizes at most one literal clockwise successor at each dart. -/
theorem Realizes.rotate_eq {r s : RotationSystem G} (hr : D.Realizes r) (hs : D.Realizes s)
    (d : Dart G) : r.rotate d = s.rotate d :=
  r.rotate_eq_of_same_incident_intervals s d fun e f hde hef hnde hnef hndf =>
    (hr.clockwise d e f hde hef hnde hnef hndf).symm.trans
      (hs.clockwise d e f hde hef hnde hnef hndf)

end Cslib.Complexity.Graph.PolygonalDrawing
