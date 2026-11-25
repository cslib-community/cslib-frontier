/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.PolyTime
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.OfFinite
import all CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.OfFinite

/-!
# Exact compiler output on serialized finite graphs

An existing loop-free finite graph and two finite orientations give an input of the generic
compiler. Its complete output equals the original canonical plane word and the two existing
incidence plane simulation configurations.

## Main results

* `Planar.Embedding.PolyTime.compile_ofFinite`: exact word, initial bits, and target bits.
-/

public section

namespace Cslib.Complexity.NCL.Planar.Embedding.PolyTime

open Diagram

/-- Compiling serialized finite graph data retains the exact original canonical plane word and
both actual plane simulation orientations, including their original vertex and edge order. -/
theorem compile_ofFinite {n m : ℕ} (G : ConstraintGraph (Fin n) (Fin m))
    (h : (AndOrGraph.ofFinite G).Valid)
    (ha : ∀ v ∈ List.ofFn G, v.IsAndOr)
    (hw : ConstraintGraph.WellFormed (fun i : Fin (List.ofFn G).length => (List.ofFn G).get i))
    (hl : ConstraintGraph.LoopFree (fun i : Fin (List.ofFn G).length => (List.ofFn G).get i))
    (s t : Fin m → Bool) :
    compile (⟨⟨AndOrGraph.ofFinite G, List.ofFn s, List.ofFn t⟩,
      h, by exact loopFree_ofFinite G hl, List.length_ofFn, List.length_ofFn⟩ : Input) =
      ⟨(planeDiagram (List.ofFn G) hw).toWord Prim.interp 0,
        (planeDiagram (List.ofFn G) hw).bits ((planeSimulation (List.ofFn G) ha hw hl).enc s),
        (planeDiagram (List.ofFn G) hw).bits ((planeSimulation (List.ofFn G) ha hw hl).enc t)⟩ := by
  let x : Input := ⟨⟨AndOrGraph.ofFinite G, List.ofFn s, List.ofFn t⟩,
    h, by exact loopFree_ofFinite G hl, List.length_ofFn, List.length_ofFn⟩
  change (⟨(compile x).word, (compile x).initial, (compile x).target⟩ :
    PlaneWordAndOrNCL.Instance) = _
  rw [compile_word, compile_initial, compile_target]
  rw [planarize_ofFinite G h hw, planarize_bits_ofFinite G h ha hw hl s,
    planarize_bits_ofFinite G h ha hw hl t]

end Cslib.Complexity.NCL.Planar.Embedding.PolyTime
