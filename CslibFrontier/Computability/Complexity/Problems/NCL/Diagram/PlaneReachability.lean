/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.CompileReachability
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.PlaneWord.Reachability

/-!
# Decision semantics of drawn plane words

The checked plane-word wrapper preserves the three reachability semantics of a valid closed
diagram. Typing follows from the diagram itself.

## Main results

* `Cslib.Complexity.NCL.Diagram.mem_plane_AndOrNCL_iff` and its edge variants.
-/

public section

namespace Cslib.Complexity.NCL.Diagram

variable {Γ : List Color → List Color → Type} (I : Interp Γ) (D : Diagram Γ [] [])

/-- The configuration problem on a checked plane word is the diagram's configuration problem. -/
theorem mem_plane_AndOrNCL_iff (hp : (D.toWord I 0).checkPlane = true)
    (hv : (Word.compile (D.toWord I 0)).Valid) (s t : D.Edge → Bool) :
    ⟨D.toWord I 0, D.bits s, D.bits t⟩ ∈ PlaneWordAndOrNCL ↔
      (D.graph I).Legal s ∧ (D.graph I).Reachable s t := by
  change (D.toWord I 0).checkPlane = true ∧ (D.toWord I 0).WellTyped [] [] ∧ _ ↔ _
  rw [and_iff_right hp, and_iff_right (wellTyped_toWord I D)]
  exact mem_compile_AndOrNCL_iff I D hv s t

/-- The edge problem on a checked plane word is the diagram's edge problem. -/
theorem mem_plane_AndOrNCLEdge_iff (hp : (D.toWord I 0).checkPlane = true)
    (hv : (Word.compile (D.toWord I 0)).Valid) (s : D.Edge → Bool) (e : D.Edge) :
    ⟨D.toWord I 0, D.bits s, D.num e⟩ ∈ PlaneWordAndOrNCLEdge ↔
      (D.graph I).Legal s ∧ (D.graph I).CanReverse s e := by
  change (D.toWord I 0).checkPlane = true ∧ (D.toWord I 0).WellTyped [] [] ∧ _ ↔ _
  rw [and_iff_right hp, and_iff_right (wellTyped_toWord I D)]
  exact mem_compile_AndOrNCLEdge_iff I D hv s e

/-- Directional edge reachability on a checked plane word is the diagram's same question. -/
theorem mem_plane_AndOrNCLEdgeToEdge_iff (hp : (D.toWord I 0).checkPlane = true)
    (hv : (Word.compile (D.toWord I 0)).Valid) (eA eB : D.Edge) (dA dB : Bool) :
    ⟨D.toWord I 0, ⟨D.num eA, dA⟩, ⟨D.num eB, dB⟩⟩ ∈ PlaneWordAndOrNCLEdgeToEdge ↔
      ∃ s t, (D.graph I).Legal s ∧ s eA = dA ∧ t eB = dB ∧ (D.graph I).Reachable s t := by
  change (D.toWord I 0).checkPlane = true ∧ (D.toWord I 0).WellTyped [] [] ∧ _ ↔ _
  rw [and_iff_right hp, and_iff_right (wellTyped_toWord I D)]
  exact mem_compile_AndOrNCLEdgeToEdge_iff I D hv eA eB dA dB

end Cslib.Complexity.NCL.Diagram
