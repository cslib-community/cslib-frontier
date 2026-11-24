/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.PolyTime.OfFinite
import CslibFrontier.Computability.Complexity.Problems.NCL.Instance.Incidence

/-! Empty inputs and the explicit loop-free boundary of the generic planar compiler. -/

open Cslib.Complexity.NCL Planar.Embedding.PolyTime

namespace CslibFrontierTests.NCLPlanarCompiler

private def emptyGraph : AndOrGraph := ⟨[], 0⟩

private theorem empty_valid : emptyGraph.Valid :=
  (AndOrGraph.checkValid_eq_true_iff _).1 (by decide +kernel)

private def emptyInput : Input := ⟨⟨emptyGraph, [], []⟩, empty_valid,
  (by intro i; exact i.elim0), rfl, rfl⟩

example : (compile emptyInput).word = [] := by
  rw [compile_word]
  rfl

example : compile emptyInput ∈ PlaneWordAndOrNCL := by
  rw [mem_compile_iff]
  refine ⟨empty_valid, rfl, rfl, ?_, .refl⟩
  intro i
  exact i.elim0

private def loopGraph : AndOrGraph :=
  ⟨[.or ⟨0, false⟩ ⟨0, true⟩ ⟨1, false⟩,
    .or ⟨1, true⟩ ⟨2, false⟩ ⟨2, true⟩], 3⟩

example : loopGraph.Valid := (AndOrGraph.checkValid_eq_true_iff _).1 (by decide +kernel)

-- Valid native graph data may contain self-loops; the compiler's input excludes them explicitly.
example : ¬∃ x : Input, x.val.graph = loopGraph := by
  rintro ⟨x, hx⟩
  have hl := Input.loopFree x
  rw [hx] at hl
  let i : Fin loopGraph.vertices.length := ⟨0, by decide +kernel⟩
  have hn : ¬((loopGraph.graph i).ports.map (·.port.edge)).Nodup := by decide +kernel
  exact hn (hl i)

end CslibFrontierTests.NCLPlanarCompiler
