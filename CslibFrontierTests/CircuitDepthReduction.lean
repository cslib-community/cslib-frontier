/-
Copyright (c) 2026 Uladzislau Artsemyeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uladzislau Artsemyeu
-/

module
-- upstream: local-only (tests for Valiant depth reduction on straight-line programs)

import CslibFrontier.Computability.Circuit.DepthReduction
import Cslib.Computability.Circuit.Boolean.Basic

/-!
# Tests for Valiant depth reduction

Module-encapsulated client tests exercising `Program.valiantDepthReduction`,
`Program.exists_cutProgram`, and `Program.exists_depthReduced_program`, including the `k = 0`
boundary, `0`-ary constant gates, and concrete Boolean trace preservation.
-/

set_option linter.privateModule false

namespace Cslib.Circuits.Tests.DepthReduction

open Cslib.Circuits.Boolean

/-! ### `k = 0` empty program boundary -/

example :
    ∃ cut : Finset (Fin 0),
      cut.card ≤ 2 * 0 * 0 / 0 ∧
      ∀ w : Wire 2 0, (Program.empty : Program signature 2 0).residualWireDepths cut w ≤ 2 ^ 0 :=
  (Program.empty : Program signature 2 0).valiantDepthReduction trivial (by decide) (by decide)

/-! ### `0`-ary constant gate depth convention and residual depth behavior -/

private def constThenNotProg : Program signature 1 2 :=
  ((Program.empty : Program signature 1 0).gate
      ⟨Boolean.Op.const true, Fin.elim0⟩).gate
    ⟨Boolean.Op.not, fun _ => Wire.gate ⟨0, by decide⟩⟩

example : constThenNotProg.residualWireDepths ∅ (.gate ⟨0, by decide⟩) = 1 := by
  rw [Program.residualWireDepths_empty]
  decide

example : constThenNotProg.residualWireDepths ∅ (.gate ⟨1, by decide⟩) = 2 := by
  rw [Program.residualWireDepths_empty]
  decide

example :
    ∃ cut : Finset (Fin 2),
      cut.card ≤ 1 * 1 * 2 / 2 ∧
      ∀ w : Wire 1 2, constThenNotProg.residualWireDepths cut w ≤ 2 ^ (2 - 1) :=
  constThenNotProg.valiantDepthReduction (by decide) (by decide) (by decide)

/-! ### Semantic cut program and concrete Boolean trace check -/

private def twoLayerProg : Program signature 2 2 :=
  ((Program.empty : Program signature 2 0).gate
      ⟨Boolean.Op.and, fun i => if i = 0 then Wire.input 0 else Wire.input 1⟩).gate
    ⟨Boolean.Op.or, fun i => if i = 0 then Wire.gate ⟨0, by decide⟩ else Wire.input 0⟩

example :
    let cut : Finset (Fin 2) := {⟨0, by decide⟩}
    ∃ (q : Program signature (2 + cut.card) (2 - cut.card))
      (wireMap : Wire 2 2 → Wire (2 + cut.card) (2 - cut.card))
      (cutGate : Fin cut.card → Fin 2),
      q.FanInAtMost 2 ∧
      q.depth ≤ 1 ∧
      q.trace interpretation
          (Fin.append (fun i => i == 0) (fun j => twoLayerProg.eval interpretation
            (fun i => i == 0) (cutGate j)))
          (wireMap (.gate ⟨1, by decide⟩)) =
        twoLayerProg.trace interpretation (fun i => i == 0) (.gate ⟨1, by decide⟩) := by
  intro cut
  obtain ⟨q, wireMap, cutGate, _, hFan, hDepth, hSurj, hTrace⟩ :=
    twoLayerProg.exists_cutProgram cut
  refine ⟨q, wireMap, cutGate, hFan 2 (by decide), ?_,
    hTrace interpretation (fun i => i == 0) (.gate ⟨1, by decide⟩)⟩
  rw [Program.depth_le_iff]
  intro k
  obtain ⟨j, hj⟩ := hSurj k
  rw [← Program.wireDepths_gateWire, ← hj, hDepth]
  have hBound : ∀ a : Fin 2, twoLayerProg.residualWireDepths cut (.gate a) ≤ 1 := by
    decide
  exact hBound j

example :
    ∃ (m : ℕ) (q : Program signature (2 + m) (2 - m))
      (wireMap : Wire 2 2 → Wire (2 + m) (2 - m)) (cutGate : Fin m → Fin 2),
      m ≤ 2 * 1 * 2 / 2 ∧ q.FanInAtMost 2 ∧ q.depth ≤ 2 ^ (2 - 1) ∧
      q.trace interpretation
          (Fin.append (fun i => i == 0) (fun j => twoLayerProg.eval interpretation
            (fun i => i == 0) (cutGate j)))
          (wireMap (.gate ⟨1, by decide⟩)) = true := by
  obtain ⟨m, q, wireMap, cutGate, hm, hFan, hDepth, hTrace⟩ :=
    twoLayerProg.exists_depthReduced_program (r := 2) (k := 2) (t := 1)
      (by decide) (by decide) (by decide)
  refine ⟨m, q, wireMap, cutGate, hm, hFan, hDepth, ?_⟩
  rw [hTrace interpretation (fun i => i == 0) (.gate ⟨1, by decide⟩)]
  decide

example :
    ∃ (m : ℕ) (q : Program signature (2 + m) (2 - m))
      (wireMap : Wire 2 2 → Wire (2 + m) (2 - m)) (cutGate : Fin m → Fin 2),
      m ≤ 2 * 2 * 2 / 2 ∧ q.FanInAtMost 2 ∧ q.depth ≤ 2 ^ (2 - 2) ∧
      q.trace interpretation
          (Fin.append (fun _ => false) (fun j => twoLayerProg.eval interpretation
            (fun _ => false) (cutGate j)))
          (wireMap (.gate ⟨1, by decide⟩)) = false := by
  obtain ⟨m, q, wireMap, cutGate, hm, hFan, hDepth, hTrace⟩ :=
    twoLayerProg.exists_depthReduced_program (r := 2) (k := 2) (t := 2)
      (by decide) (by decide) (by decide)
  refine ⟨m, q, wireMap, cutGate, hm, hFan, hDepth, ?_⟩
  rw [hTrace interpretation (fun _ => false) (.gate ⟨1, by decide⟩)]
  decide

end Cslib.Circuits.Tests.DepthReduction
