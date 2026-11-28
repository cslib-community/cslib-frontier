/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Compile
public import CslibFrontier.Computability.Complexity.Problems.NCL.Reachability

/-!
# Decision semantics of compiled diagrams

Compile a closed diagram's finite graph and serialize its configurations in creation order.
All three decision problems agree with the diagram's original reachability semantics.

## Main results

* `Cslib.Complexity.NCL.Diagram.compile_valid`: structural graph validity after compilation.
* `Cslib.Complexity.NCL.Diagram.mem_compile_AndOrNCL_iff` and its edge variants: decision semantics.
-/

public section

namespace Cslib.Complexity.NCL.Diagram

variable {Γ : List Color → List Color → Type} (I : Interp Γ)

/-- Compile a closed, well-formed AND/OR diagram to valid graph data. -/
theorem compile_valid (D : Diagram Γ [] []) (ha : (D.graph I).IsAndOr)
    (hw : (D.graph I).WellFormed) :
    (Word.compile (D.toWord I 0)).Valid := by
  rw [compile_toWord]
  exact AndOrGraph.ofFinite_valid _ (finiteGraph_isAndOr I D ha)
    (finiteGraph_wellFormed I D hw)

private theorem config_bits (D : Diagram Γ [] []) (s : D.Edge → Bool) :
    (AndOrGraph.ofFinite (finiteGraph I D)).config (D.bits s) = s ∘ D.numEquiv.symm := by
  exact AndOrGraph.config_ofFn _ _

/-- Compiling a closed valid diagram preserves fixed-target configuration reachability. -/
theorem mem_compile_AndOrNCL_iff (D : Diagram Γ [] [])
    (hv : (Word.compile (D.toWord I 0)).Valid) (s t : D.Edge → Bool) :
    ⟨Word.compile (D.toWord I 0), D.bits s, D.bits t⟩ ∈ AndOrNCL ↔
      (D.graph I).Legal s ∧ (D.graph I).Reachable s t := by
  rw [compile_toWord] at hv ⊢
  rw [AndOrGraph.ofFinite_mem_AndOrNCL_iff (finiteGraph I D) hv]
  simp only [length_bits, true_and]
  rw [config_bits, config_bits]
  exact and_congr (finiteSimulation I D).legal_enc_iff (finite_reachable_iff I D)

/-- Compiling a closed valid diagram preserves configuration-to-edge reachability. -/
theorem mem_compile_AndOrNCLEdge_iff (D : Diagram Γ [] [])
    (hv : (Word.compile (D.toWord I 0)).Valid) (s : D.Edge → Bool) (e : D.Edge) :
    ⟨Word.compile (D.toWord I 0), D.bits s, D.num e⟩ ∈ AndOrNCLEdge ↔
      (D.graph I).Legal s ∧ (D.graph I).CanReverse s e := by
  rw [compile_toWord] at hv ⊢
  have h := AndOrGraph.ofFinite_mem_AndOrNCLEdge_iff (finiteGraph I D) hv
    (D.bits s) (D.numEquiv e)
  rw [numEquiv_val, length_bits] at h
  simp only [true_and] at h
  rw [h]
  rw [config_bits]
  exact and_congr (finiteSimulation I D).legal_enc_iff (finite_canReverse_iff I D e)

/-- Compiling a closed valid diagram preserves directional edge-to-edge reachability. -/
theorem mem_compile_AndOrNCLEdgeToEdge_iff (D : Diagram Γ [] [])
    (hv : (Word.compile (D.toWord I 0)).Valid) (eA eB : D.Edge) (dA dB : Bool) :
    ⟨Word.compile (D.toWord I 0), ⟨D.num eA, dA⟩, ⟨D.num eB, dB⟩⟩ ∈ AndOrNCLEdgeToEdge ↔
      ∃ s t, (D.graph I).Legal s ∧ s eA = dA ∧ t eB = dB ∧ (D.graph I).Reachable s t := by
  rw [compile_toWord] at hv ⊢
  have h := AndOrGraph.ofFinite_mem_AndOrNCLEdgeToEdge_iff (finiteGraph I D) hv
    (D.numEquiv eA) (D.numEquiv eB) dA dB
  rw [numEquiv_val, numEquiv_val] at h
  exact h.trans (finite_exists_reachable_iff I D eA eB dA dB)

/-- Serializing a legal orientation gives a correctly sized legal compiled configuration. -/
theorem compile_bits_legal (D : Diagram Γ [] [])
    (hv : (Word.compile (D.toWord I 0)).Valid) {s : D.Edge → Bool}
    (hs : (D.graph I).Legal s) :
    (D.bits s).length = (Word.compile (D.toWord I 0)).edgeCount ∧
      (Word.compile (D.toWord I 0)).graph.Legal
        ((Word.compile (D.toWord I 0)).config (D.bits s)) := by
  have h := (mem_compile_AndOrNCL_iff I D hv s s).2 ⟨hs, .refl⟩
  exact ⟨h.2.1, h.2.2.2.1⟩

end Cslib.Complexity.NCL.Diagram
