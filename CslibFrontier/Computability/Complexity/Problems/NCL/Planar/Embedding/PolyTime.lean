/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.PolyTime.EmitCorrectness
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.PlaneWord.Reachability

/-!
# Generic canonical planarization in polynomial time

The input is the existing finite AND/OR instance restricted to valid loop-free graph records and
correctly sized initial and target bit lists. Its encoding is the restriction of the existing
standard instance encoding. The output is the actual canonical planar word and canonical
simulation configurations, with the original primitive and edge numbering.

## Main definitions

* `Planar.Embedding.PolyTime.Input`: valid loop-free graph data and two full orientation lists.
* `Planar.Embedding.PolyTime.compile`: the executable finite-template compiler.

## Main results

* `Planar.Embedding.PolyTime.computableInPolyTime_compile`: standard PT compiler.
* `Planar.Embedding.PolyTime.compile_word`, `compile_initial`, `compile_target`: exact output.
* `Planar.Embedding.PolyTime.mem_compile_iff`: preservation of the existing decision problem.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Planar.Embedding.PolyTime

open Diagram _root_.Turing.MultiTapeTM

/-- Valid loop-free finite AND/OR graph records with full orientation lists. -/
abbrev Input := {x : AndOrNCL.Instance // x.graph.Valid ∧ x.graph.graph.LoopFree ∧
  x.initial.length = x.graph.edgeCount ∧ x.target.length = x.graph.edgeCount}

theorem Input.valid (x : Input) : x.val.graph.Valid := x.property.1

theorem Input.loopFree (x : Input) : x.val.graph.graph.LoopFree := x.property.2.1

theorem Input.initial_length (x : Input) : x.val.initial.length = x.val.graph.edgeCount :=
  x.property.2.2.1

theorem Input.target_length (x : Input) : x.val.target.length = x.val.graph.edgeCount :=
  x.property.2.2.2

/-- The restriction of the existing standard AND/OR instance encoding. -/
@[expose] def encInput : Input ↪ List Bool :=
  (Function.Embedding.subtype _).trans encAndOrNCL

private def emitInstance (x : AndOrNCL.Instance) : PlaneWordAndOrNCL.Instance :=
  ⟨expand (Emit.program x x.initial), configurationBits (Emit.program x x.initial),
    configurationBits (Emit.program x x.target)⟩

private theorem computableInPolyTime_emitInstance :
    ComputableInPolyTime emitInstance encAndOrNCL encPlaneWordAndOrNCL := by
  have hi := Emit.computableInPolyTime_program.comp
    (ComputableInPolyTime.id'.prod (g := AndOrNCL.Instance.initial) (by fun_prop))
  have ht := Emit.computableInPolyTime_program.comp
    (ComputableInPolyTime.id'.prod (g := AndOrNCL.Instance.target) (by fun_prop))
  unfold emitInstance
  fun_prop

/-- Compile finite incidence data by sources, canonical adjacent swaps, and edge caps. -/
def compile (x : Input) : PlaneWordAndOrNCL.Instance := emitInstance x.val

/-- The actual generic canonical planarizer is polynomial-time under the restricted encoding. -/
@[fun_prop]
theorem computableInPolyTime_compile :
    ComputableInPolyTime compile encInput encPlaneWordAndOrNCL :=
  computableInPolyTime_emitInstance.comp
    (show ComputableInPolyTime Subtype.val encInput encAndOrNCL from .of_eq (fun _ => rfl))

/-- The compiler emits exactly the existing canonical plane word. -/
theorem compile_word (x : Input) : (compile x).word = planarize x.val.graph (Input.valid x) :=
  expand_emit_program x.val (Input.valid x)
    (Input.initial_length x) x.val.initial

/-- The compiler's initial bits are the actual canonical planar simulation extension. -/
theorem compile_initial (x : Input) : (compile x).initial =
    (planarizeDiagram x.val.graph (Input.valid x)).bits
      ((planarizeDiagramSimulation x.val.graph (Input.valid x) (Input.loopFree x)).enc
        (x.val.graph.config x.val.initial)) :=
  configurationBits_emit_program x.val (Input.valid x) (Input.loopFree x)
    (Input.initial_length x) x.val.initial

/-- The compiler's target bits are the actual canonical planar simulation extension. -/
theorem compile_target (x : Input) : (compile x).target =
    (planarizeDiagram x.val.graph (Input.valid x)).bits
      ((planarizeDiagramSimulation x.val.graph (Input.valid x) (Input.loopFree x)).enc
        (x.val.graph.config x.val.target)) :=
  configurationBits_emit_program x.val (Input.valid x) (Input.loopFree x)
    (Input.initial_length x) x.val.target

/-- Generic canonical planarization preserves and reflects fixed-target reachability. -/
theorem mem_compile_iff (x : Input) : compile x ∈ PlaneWordAndOrNCL ↔ x.val ∈ AndOrNCL := by
  change (compile x).word.checkPlane = true ∧ (compile x).word.WellTyped [] [] ∧
    (⟨Word.compile (compile x).word, (compile x).initial, (compile x).target⟩ :
      AndOrNCL.Instance) ∈ AndOrNCL ↔ _
  rw [compile_word, compile_initial, compile_target, and_iff_right (planarize_checkPlane _ _),
    and_iff_right (planarize_wellTyped _ _)]
  unfold planarize
  rw [mem_compile_AndOrNCL_iff Prim.interp _ (planarize_compile_valid _ _)]
  refine (and_congr (planarizeDiagramSimulation x.val.graph x.valid x.loopFree).legal_enc_iff
    (planarizeDiagramSimulation x.val.graph x.valid x.loopFree).reachable_enc_iff).trans ?_
  change _ ↔ x.val.graph.Valid ∧ x.val.initial.length = x.val.graph.edgeCount ∧
    x.val.target.length = x.val.graph.edgeCount ∧ _
  simp only [x.valid, x.initial_length, x.target_length, true_and]

end Cslib.Complexity.NCL.Planar.Embedding.PolyTime
