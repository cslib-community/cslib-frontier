/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Finite
public import CslibFrontier.Computability.Complexity.Problems.NCL.Instance

/-!
# Compiling words to finite graph data

Run a word from an empty wire stack and retain its vertices and final edge count. Compiling a
closed diagram's word gives precisely its finite graph serialization.

## Main definitions

* `Cslib.Complexity.NCL.Word.compile`: execute a word and return graph data.

## Main results

* `Cslib.Complexity.NCL.Diagram.compile_toWord`: the compiler agrees with diagram semantics.
* `Cslib.Complexity.NCL.Diagram.compileSimulation`: a shared simulation for compiled diagrams.
-/

public section

namespace Cslib.Complexity.NCL

/-- Run a word from the empty stack and retain its vertex list and edge count. -/
@[expose] def Word.compile (w : Word) : AndOrGraph :=
  let st := Word.run w ⟨[], 0, []⟩
  ⟨st.verts, st.next⟩

namespace Diagram

variable {Γ : List Color → List Color → Type} (I : Interp Γ) {a b : List Color}

/-- Serializing finite diagram semantics emits its numbered vertex list and exact edge count. -/
theorem ofFinite_finiteGraph (D : Diagram Γ a b) :
    AndOrGraph.ofFinite (finiteGraph I D) =
      ⟨(finiteVertexList I D).map (Vertex.map Fin.val), a.length + D.innerCount⟩ := by
  apply AndOrGraph.ext
  · let L := vertexList I D
    let f : Vertex D.Edge → Vertex ℕ := fun v => (v.map D.numEquiv).map Fin.val
    change List.ofFn (fun i : Fin L.length => f (L.get i)) = _
    simp only [finiteVertexList, List.map_map]
    change List.ofFn (fun i : Fin L.length => f (L.get i)) = L.map f
    rw [List.ofFn_comp', List.ofFn_get]
  · rfl

/-- Compiling the word of a closed diagram gives exactly its finite graph data. -/
theorem compile_toWord (D : Diagram Γ [] []) :
    Word.compile (D.toWord I 0) = AndOrGraph.ofFinite (finiteGraph I D) := by
  unfold Word.compile
  rw [run_toWord_finite, ofFinite_finiteGraph]
  simp

/-- Numbered diagram edges lie inside the compiled finite graph. -/
theorem num_lt_compile (D : Diagram Γ [] []) (e : D.Edge) :
    D.num e < (Word.compile (D.toWord I 0)).edgeCount := by
  rw [compile_toWord]
  exact num_lt _ _

/-- Word compilation preserves the interpreted graph's configurations and reachability. -/
@[expose] def compileSimulation (D : Diagram Γ [] []) :
    ConstraintGraph.Simulation (D.graph I) (Word.compile (D.toWord I 0)).graph :=
  (compile_toWord I D).symm ▸
    (finiteSimulation I D).trans (AndOrGraph.ofFiniteSimulation (finiteGraph I D))

end Diagram

end Cslib.Complexity.NCL
