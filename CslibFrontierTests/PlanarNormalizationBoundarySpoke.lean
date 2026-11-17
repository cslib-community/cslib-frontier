/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.FreshSpoke

/-! Low-import clients of literal fresh-spoke attachment, including a repeated degree-four
variable in the body-plus-probe. Only actual support, rather than the whole label type, must
avoid the new marker. No normalization or finite label alphabet is required.
-/

namespace CslibFrontierTests.PlanarNormalizationBoundarySpoke

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Complexity.CSP.OrderedBoundary

noncomputable section

example : Witness ([⟨(), [5, 6, 7]⟩] : CSP Unit ℕ) [5, 6, 7] :=
  Witness.namedAtom () (fun i : Fin 3 => i.val + 5) (by
    intro i j he
    apply Fin.ext
    change i.val + 5 = j.val + 5 at he
    omega)

private def repeated : CSP Unit ℕ := [⟨(), [0, 0, 0]⟩]

private def repeatedWitness : Witness repeated [0] where
  certificate := ⟨[6, 3, 0, 5, 2, 1, 4, 7]⟩
  accepted := by decide +kernel

example : Witness (repeated ++ [⟨(), [0, 1]⟩]) [1] :=
  repeatedWitness.freshSpoke (left := []) (right := []) ()
    (by decide +kernel) (by decide +kernel)

example : Witness ([⟨(), [0, 1]⟩] : CSP Unit ℕ) [1] :=
  (Witness.empty [0] (by decide +kernel)).freshSpoke (left := []) (right := []) ()
    (by decide +kernel) (by decide +kernel)

end

end CslibFrontierTests.PlanarNormalizationBoundarySpoke
