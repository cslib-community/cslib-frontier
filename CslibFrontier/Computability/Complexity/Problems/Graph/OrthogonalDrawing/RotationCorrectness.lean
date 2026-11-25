/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.OrthogonalDrawing.PolygonalGerms
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Rotation
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateLookup
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Converse
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Sectors
import Mathlib.Data.List.GetD

/-!
# Correctness of the executed orthogonal clockwise table

The four-ray scan reads the same outgoing directions as the actual polygonal conversion.
The next dart of its induced clockwise rotation leaves an empty sector; therefore the scan
returns precisely that dart, including a singleton fiber. The complete emitted table is the
canonical table of this rotation and passes the full numerical genus-zero checker.

The input supplies only an actual orthogonal drawing with its full real contact proof.
Neither a rotation nor a genus certificate is assumed. Polynomial-time computation is
provided separately by the native orthogonal rotation module.
-/

public section

namespace Cslib.Complexity.Graph.OrthogonalDrawing

private theorem successor_eq_of_realizes {G : Graph} {d : OrthogonalDrawing}
    {D : PolygonalDrawing G} {r : RotationSystem G} (hR : D.Realizes r)
    (hdir : ∀ a, D.direction a =
      ((-(dartRank G d a.index : ℝ) * Real.pi / 2 : ℝ) : Real.Angle)) (a : Dart G) :
    clockwiseSuccessor G d a.index = (r.rotate a).index := by
  let s := r.rotate a
  have hsv : s.vertex = a.vertex := r.vertex_rotate a
  have hrank (b : Dart G) : dartRank G d b.index < 4 := clockwiseRank_lt _ _
  have hinj (b c : Dart G) (hv : b.vertex = c.vertex)
      (he : dartRank G d b.index = dartRank G d c.index) : b = c :=
    hR.directions_injective b c hv (by rw [hdir b, hdir c, he])
  let step := (dartRank G d s.index + 3 - dartRank G d a.index) % 4
  have hstep : step < 4 := Nat.mod_lt _ (by decide)
  have hsray : dartRank G d s.index = (dartRank G d a.index + step + 1) % 4 := by
    have ha := hrank a
    have hs := hrank s
    dsimp only [step]
    omega
  have hdecode (b : ℕ) (hb : b < 2 * G.edges.length) (hv : endpoint G b = endpoint G a.index) :
      ∃ b' : Dart G, b'.index = b ∧ b'.vertex = a.vertex :=
    let b' := (Dart.indexEquiv G).symm ⟨b, hb⟩
    have hbi : b'.index = b := congrArg Fin.val ((Dart.indexEquiv G).apply_symm_apply ⟨b, hb⟩)
    ⟨b', hbi, by simpa only [endpoint, ← hbi, Dart.vertex_index] using hv⟩
  have hsindex : s.index < 2 * G.edges.length := (Dart.indexEquiv G s).isLt
  apply clockwiseSuccessor_eq_of_firstRay G d hsindex hstep
    (by simpa only [endpoint, Dart.vertex_index] using hsv) hsray
  · intro k hk b hb hv he
    obtain ⟨b', hbi, hbv⟩ := hdecode b hb hv
    have hb_rank : dartRank G d b'.index = (dartRank G d a.index + k + 1) % 4 := by
      simpa only [hbi] using he
    have ha := hrank a
    have hs := hrank s
    have hb' := hrank b'
    have hab : dartRank G d a.index ≠ dartRank G d b'.index := by omega
    have hbs' : dartRank G d b'.index ≠ dartRank G d s.index := by omega
    have hba : b' ≠ a := fun h => hab (by rw [h])
    have hbs : b' ≠ s := fun h => hbs' (by rw [h])
    have has : dartRank G d a.index ≠ dartRank G d s.index := fun heq =>
      hba (((r.sameCycle_iff a b').mpr hbv.symm).eq_of_left (hinj a s hsv.symm heq).symm).symm
    have hprev : r.rotate.symm s = a := r.rotate.symm_apply_apply a
    have hno := hR.not_sbtw_inverse_rotate s b' (hbv.trans hsv.symm) hbs (hprev.symm ▸ hba)
    rw [hprev, hdir s, hdir b', hdir a] at hno
    exact hno <| (sbtw_clockwiseRanks_iff ha hb' hs hab hbs' has).mpr <| by
      dsimp only [step] at hk
      omega
  · intro b hb hv he
    obtain ⟨b', hbi, hbv⟩ := hdecode b hb hv
    exact hbi.symm.trans <| congrArg Dart.index <|
      hinj b' s (hbv.trans hsv.symm) (by simpa only [hbi] using he)

/-- Every executed successor is exactly the successor read from the actual drawing's
clockwise germs. This includes both tags of every indexed edge occurrence. -/
theorem clockwiseSuccessor_eq_rotate {G : Graph} {d : OrthogonalDrawing}
    (hd : IsPlanarOrthogonalDrawing G d) (a : Dart G) :
    clockwiseSuccessor G d a.index =
      (hd.isEmbedding_polygonalDrawing.rotation.rotate a).index :=
  successor_eq_of_realizes hd.isEmbedding_polygonalDrawing.realizes_rotation
    hd.direction_polygonalDrawing a

/-- The full executed list is the exact canonical table of the internally induced
clockwise rotation, rather than an existentially selected accepting certificate. -/
theorem rotationCertificate_eq_ofRotation {G : Graph} {d : OrthogonalDrawing}
    (hd : IsPlanarOrthogonalDrawing G d) :
    rotationCertificate G d = RotationCertificate.ofRotation
      hd.isEmbedding_polygonalDrawing.rotation := by
  symm
  refine (RotationCertificate.ofRotation_eq_iff _ _).mpr
    ⟨length_rotationCertificate G d, fun a => ?_⟩
  rw [List.getD_eq_getElem _ _
    (by rw [length_rotationCertificate]; exact (Dart.indexEquiv G a).isLt)]
  simpa only [rotationCertificate, List.getElem_map, List.getElem_range] using
    clockwiseSuccessor_eq_rotate hd a

/-- A genuine supplied orthogonal embedding makes the actually computed table pass the
full rotation and componentwise Euler checker. No genus or order provider is a premise. -/
theorem verifyGenusZero_rotationCertificate {G : Graph} {d : OrthogonalDrawing}
    (hd : IsPlanarOrthogonalDrawing G d) :
    RotationCertificate.verifyGenusZero G (rotationCertificate G d) = true := by
  have hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices := fun v hv => by
    obtain ⟨e, he, hv⟩ := List.mem_flatMap.mp hv
    obtain rfl | rfl := by simpa using hv
    · exact (hd.endpointsDeclared e he).1
    · exact (hd.endpointsDeclared e he).2
  rw [rotationCertificate_eq_ofRotation hd, RotationCertificate.verifyGenusZero_eq_true_iff]
  refine ⟨RotationCertificate.verifyRotation_ofRotation _ hG, ?_⟩
  rw [RotationCertificate.decode_ofRotation _ hG]
  exact hd.isEmbedding_polygonalDrawing.numericalGenusZero hG
    hd.isEmbedding_polygonalDrawing.realizes_rotation

end Cslib.Complexity.Graph.OrthogonalDrawing
