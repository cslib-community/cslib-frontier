/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Basic
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Transport
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.EdgeDeletion

/-!
# Transport of polygonal realizations along indexed edge equivalences

An equivalence of edge positions retaining their two named endpoints transports actual
routes, every real segment contact, and the literal clockwise rotation. Equal declared
membership suffices; declaration lists need not be equal or without repetitions.
-/

public section

namespace Cslib.Complexity.Graph

namespace RotationSystem

/-- Transporting a literal rotation back along the inverse dart equivalence recovers it. -/
theorem transport_symm {G H : Graph} (r : RotationSystem G) (e : Dart G ≃ Dart H)
    (hv : ∀ a b, (e a).vertex = (e b).vertex ↔ a.vertex = b.vertex)
    (hw : ∀ a b, (e.symm a).vertex = (e.symm b).vertex ↔ a.vertex = b.vertex) :
    (r.transport e hv).transport e.symm hw = r := by
  cases r with
  | mk σ hσ =>
    unfold transport
    congr 1
    exact e.permCongr.symm_apply_apply σ

/-- Dart conjugacy retains every literal forward iterate of a rotation. -/
theorem pow_transport {G H : Graph} (r : RotationSystem G) (e : Dart G ≃ Dart H)
    (hv : ∀ a b, (e a).vertex = (e b).vertex ↔ a.vertex = b.vertex)
    (n : ℕ) (a : Dart G) :
    ((r.transport e hv).rotate ^ n) (e a) = e ((r.rotate ^ n) a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ', Equiv.Perm.mul_apply]
    simp [transport]

/-- A dart equivalence preserves first-hit distances, including different vertex fibers. -/
theorem rotationDistance_transport {G H : Graph} (r : RotationSystem G)
    (e : Dart G ≃ Dart H)
    (hv : ∀ a b, (e a).vertex = (e b).vertex ↔ a.vertex = b.vertex) (a b : Dart G) :
    (r.transport e hv).rotationDistance (e a) (e b) = r.rotationDistance a b := by
  classical
  by_cases hab : a.vertex = b.vertex
  · apply (r.transport e hv).rotationDistance_eq _ _ ((hv a b).mpr hab)
    · rw [r.pow_transport, r.pow_rotationDistance a b hab]
    · intro k hk heq
      rw [r.pow_transport] at heq
      exact r.pow_ne_of_lt_rotationDistance a b hab hk (e.injective heq)
  · have h₁ : ¬r.rotate.SameCycle a b := fun h => hab ((r.sameCycle_iff _ _).mp h)
    have h₂ : ¬(r.transport e hv).rotate.SameCycle (e a) (e b) := fun h =>
      hab ((hv a b).mp (((r.transport e hv).sameCycle_iff _ _).mp h))
    simp only [rotationDistance, h₁, h₂, ↓reduceDIte]

/-- Literal directed rotation intervals commute with dart conjugacy. -/
theorem mem_rotationInterval_transport {G H : Graph} (r : RotationSystem G)
    (e : Dart G ≃ Dart H)
    (hv : ∀ a b, (e a).vertex = (e b).vertex ↔ a.vertex = b.vertex) (a b c : Dart G) :
    e b ∈ (r.transport e hv).rotationInterval (e a) (e c) ↔
      b ∈ r.rotationInterval a c := by
  classical
  simp only [rotationInterval, r.rotationDistance_transport, Finset.mem_image,
    r.pow_transport, e.injective.eq_iff]

end RotationSystem

namespace PolygonalDrawing

/-- Reindex routes by actual edge occurrences, retaining the end tag and named endpoints.
The declaration list may be changed separately. -/
@[expose] def edgeTransport {G H : Graph} (D : PolygonalDrawing G)
    (e : Fin G.edges.length ≃ Fin H.edges.length)
    (hv : ∀ i b, Dart.vertex (e i, b) = Dart.vertex (i, b)) : PolygonalDrawing H where
  vertex := D.vertex
  route j := D.route (e.symm j)
  endpoint_eq j b := (D.endpoint_eq _ _).trans
    (congrArg D.vertex (by simpa only [e.apply_symm_apply] using (hv (e.symm j) b).symm))

/-- Indexed edge transport preserves the full real-affine embedding semantics.
Repeated declarations are compared by membership, not by their list positions. -/
theorem IsEmbedding.edgeTransport {G H : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (e : Fin G.edges.length ≃ Fin H.edges.length)
    (hv : ∀ i b, Dart.vertex (e i, b) = Dart.vertex (i, b))
    (hm : ∀ v, v ∈ G.vertices ↔ v ∈ H.vertices) : (D.edgeTransport e hv).IsEmbedding := by
  refine ⟨?_, fun i => hD.simple (e.symm i), ?_, ?_⟩
  · intro a ha b hb heq
    exact hD.vertices_injective ((hm _).mpr ha) ((hm _).mpr hb) heq
  · intro i j t ht v hmem heq
    obtain ⟨b, hb, hvb⟩ := hD.vertex_contacts (e.symm i) j t ht v ((hm _).mpr hmem) heq
    refine ⟨b, hb, ?_⟩
    rw [← hvb]
    simpa only [e.apply_symm_apply] using hv (e.symm i) b
  · intro i j hij k l s t hs ht heq
    obtain ⟨b, c, hb, hc, hvbc⟩ := hD.edge_contacts (e.symm i) (e.symm j)
      (fun h => hij (e.symm.injective h)) k l s t hs ht heq
    refine ⟨b, c, hb, hc, ?_⟩
    calc
      Dart.vertex (i, b) = Dart.vertex (e.symm i, b) := by
        simpa only [e.apply_symm_apply] using hv (e.symm i) b
      _ = Dart.vertex (e.symm j, c) := hvbc
      _ = Dart.vertex (j, c) := by
        simpa only [e.apply_symm_apply] using (hv (e.symm j) c).symm

/-- Actual germ vectors retain the edge occurrence and end tag under transport. -/
theorem germ_edgeTransport {G H : Graph} (D : PolygonalDrawing G)
    (e : Fin G.edges.length ≃ Fin H.edges.length)
    (hv : ∀ i b, Dart.vertex (e i, b) = Dart.vertex (i, b)) (a : Dart G) :
    (D.edgeTransport e hv).germ (e a.1, a.2) = D.germ a := by
  simp [germ, edgeTransport]

/-- Edge reindexing retains exact clockwise realization, including the two distinct
ends of every loop. No reflection or change of the planar coordinates is used. -/
theorem Realizes.edgeTransport {G H : Graph} {D : PolygonalDrawing G}
    {r : RotationSystem G} (hR : D.Realizes r)
    (e : Fin G.edges.length ≃ Fin H.edges.length)
    (hv : ∀ i b, Dart.vertex (e i, b) = Dart.vertex (i, b)) :
    (D.edgeTransport e hv).Realizes
      (r.transport (e.prodCongr (Equiv.refl Bool)) (by
        intro a b
        change Dart.vertex (e a.1, a.2) = Dart.vertex (e b.1, b.2) ↔ _
        rw [hv, hv])) := by
  let E : Dart G ≃ Dart H := e.prodCongr (Equiv.refl Bool)
  have hdir (a : Dart G) : (D.edgeTransport e hv).direction (E a) = D.direction a := by
    change (((D.edgeTransport e hv).germ (e a.1, a.2)).arg : Real.Angle) = _
    rw [D.germ_edgeTransport]
    rfl
  have hvertex (a : Dart G) : (E a).vertex = a.vertex := hv a.1 a.2
  have hvE : ∀ a b, (E a).vertex = (E b).vertex ↔ a.vertex = b.vertex := by
    intro a b
    rw [hvertex, hvertex]
  refine ⟨?_, ?_, ?_⟩
  · intro a
    obtain ⟨a, rfl⟩ := E.surjective a
    change (D.edgeTransport e hv).germ (e a.1, a.2) ≠ 0
    rw [D.germ_edgeTransport]
    exact hR.nonzero a
  · intro a b hab heq
    obtain ⟨a, rfl⟩ := E.surjective a
    obtain ⟨b, rfl⟩ := E.surjective b
    rw [hvertex, hvertex] at hab
    rw [hdir, hdir] at heq
    exact congrArg E (hR.directions_injective a b hab heq)
  · intro a b c hab hbc hneab hnebc hneac
    obtain ⟨a, rfl⟩ := E.surjective a
    obtain ⟨b, rfl⟩ := E.surjective b
    obtain ⟨c, rfl⟩ := E.surjective c
    rw [hvertex, hvertex] at hab hbc
    rw [hdir, hdir, hdir]
    exact (hR.clockwise a b c hab hbc (fun h => hneab (congrArg E h))
      (fun h => hnebc (congrArg E h)) (fun h => hneac (congrArg E h))).trans
      (r.mem_rotationInterval_transport E hvE a b c).symm

end PolygonalDrawing
end Cslib.Complexity.Graph
