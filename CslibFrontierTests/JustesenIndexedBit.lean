/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator.SeedRank
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.JustesenBit

/-! Checked clients for composing the indexed Justesen bit with the retained seed-rank scan. -/

set_option linter.privateModule false

namespace CslibFrontierTests.JustesenIndexedBit

open Cslib.Code.JustesenFamily Cslib.Reachability.Hoza.SeedRank
open Turing.MultiTapeTM Turing.BinaryField

private def codeBit (p : FieldContext × ℕ) (index : ℕ) : Bool :=
  p.1.indexedBit p.2 index

/-- The retained context and binary label supply exactly the bit in the isolation proof. -/
example {w n : ℕ} (label : Fin w) (j : Fin (codeLength w n)) :
    codeBit (fieldContext w n, label.val) j.val = indexedCodeword label j :=
  (fieldContext_indexedBit_eq label j).trans (indexedCodewordMod_eq label j)

/-- The retained-rank digit scan can use the indexed evaluator at its existing callback
encoding. -/
example (heval : ComputableInSpace HornerInput.evaluate encHornerInput encCoefficients
      (fun p => (encHornerInput p).length)) :
    let encContext := encPair encFieldContext encNat
    ComputableInSpace (accumulateRank codeBit) (encRequest encContext) encNat
      (fun q => (encRequest encContext q).length + q.width) := by
  let : Inhabited FieldContext := ⟨⟨0, 0, []⟩⟩
  exact accumulateRank_inSpace (encPair encFieldContext encNat) codeBit
    (fieldContext_indexedBit_inSpace_of_horner heval)

end CslibFrontierTests.JustesenIndexedBit
