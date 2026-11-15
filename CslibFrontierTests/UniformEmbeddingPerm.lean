/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Probability.PMF.EmbeddingPerm

/-!
# Domain-permutation invariance of uniform embeddings: an ordinary client

Exercises `Cslib.Probability.PMF.uniformOfFintype_embedding_map_perm_trans` and
`Cslib.Probability.PMF.uniformOfFintype_embedding_bind_perm_trans` through an ordinary import:
under a uniform injection `Fin 2 ↪ Fin 3`, the images of `0` and `1` have the same law.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.UniformEmbeddingPerm

open Cslib.Probability

private instance : Nonempty (Fin 2 ↪ Fin 3) := ⟨Fin.castLEEmb (by decide)⟩

/-- Under a uniform injection `Fin 2 ↪ Fin 3`, the images of `0` and `1` have the same law, by
precomposing with `Equiv.swap 0 1`. -/
example : (PMF.uniformOfFintype (Fin 2 ↪ Fin 3)).map (fun j => j 0) =
    (PMF.uniformOfFintype (Fin 2 ↪ Fin 3)).map (fun j => j 1) := by
  conv_lhs => rw [← PMF.uniformOfFintype_embedding_map_perm_trans (Equiv.swap (0 : Fin 2) 1),
    PMF.map_comp]
  rfl

end CslibFrontierTests.UniformEmbeddingPerm
