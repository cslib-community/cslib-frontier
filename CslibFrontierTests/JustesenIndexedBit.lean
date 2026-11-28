/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator.SeedRank
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.JustesenBit

/-! Check that the retained-rank weight evaluator can use the indexed Justesen bit. -/

set_option linter.privateModule false

namespace CslibFrontierTests.JustesenIndexedBit

open Cslib Cslib.Code.JustesenFamily Cslib.Reachability.Hoza Cslib.Reachability.Hoza.SeedRank
open Turing.MultiTapeTM

private def codeBit (p : FieldContext × ℕ) (index : ℕ) : Bool :=
  p.1.indexedBit p.2 index

/-- The binary label and retained context give the weight used by the isolation theorem. -/
example {w n : ℕ} (rank : Fin (2 ^ codeLength w n)) (vertex : Fin (n + 1) × Fin w) :
    weightRank codeBit
        ⟨⟨(fieldContext w n, vertex.2.val), rank.val, codeLength w n⟩, vertex.1.val⟩ =
      generatedWeight ((BitString.equivFin _).symm rank) vertex :=
  weightRank_eq_generatedWeight codeBit (fieldContext w n, vertex.2.val) rank vertex
    (fieldContext_indexedBit_eq vertex.2)

/-- The native retained-rank weight evaluator accepts the indexed bit at its existing encoding. -/
example :
    let encContext := encPair encFieldContext encNat
    ComputableInSpace (weightRank codeBit) (encWeightRequest encContext) encNat
      (fun q => (encWeightRequest encContext q).length + q.seed.width) := by
  let : Inhabited FieldContext := ⟨⟨0, 0, []⟩⟩
  exact weightRank_inSpace (encPair encFieldContext encNat) codeBit
    fieldContext_indexedBit_inSpace

end CslibFrontierTests.JustesenIndexedBit
