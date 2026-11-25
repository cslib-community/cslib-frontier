/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.PolyTime.Serialization
import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.PolyTime.Bundles
import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.PolyTime.RoutingCorrectness
import all CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.PolyTime.Routing
import all CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.PolyTime.Emit

/-! Actual crossing order, retained bits, and emission on unrestricted graph records. -/

-- The fixtures and examples are local to this test module.
set_option linter.privateModule false

open Cslib.Complexity.NCL Cslib.Complexity.NCL.Planar.Embedding
open PolyTime Diagram

namespace CslibFrontierTests.NCLPlanarEmission

private def a : Wire := ⟨⟨0, false⟩, .red, false⟩
private def b : Wire := ⟨⟨1, true⟩, .blue, true⟩
private def c : Wire := ⟨⟨2, false⟩, .red, true⟩

example : (RoutingData.mk [c, a, b] [a, b, c] 2).program =
    [(3, .cross .blue .red true true), (2, .cross .red .red false true)] := by
  decide +kernel

example : extendedBits (gen (.source [.red, .blue, .red] 2))
    (Sum.elim Fin.elim0 (fun i : Fin 3 => ![false, true, false] i)) =
      [false, true, false] := rfl

private def vertex : Vertex ℕ :=
  ⟨[⟨⟨8, false⟩, 1⟩, ⟨⟨3, true⟩, 2⟩, ⟨⟨5, false⟩, 1⟩], 2⟩

-- An explicit source vertex emits its original port order, colors, and stub directions.
example : Emit.program ⟨⟨[vertex], 9⟩, [], []⟩ [] =
    [(0, .source .red .blue .red false true false)] := by
  decide +kernel

-- The routing and cap loops use the input bit list rather than the binary edge-count field.
example : Emit.program ⟨⟨[], 1000000⟩, [], []⟩ [] = [] := rfl

end CslibFrontierTests.NCLPlanarEmission
