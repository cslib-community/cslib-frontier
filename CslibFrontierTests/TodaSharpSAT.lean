/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Classes.Toda.SharpSAT
import CslibFrontier.Computability.Complexity.Classes.PP.Bit

/-! Checked clients of Toda's theorem with the fixed `#SAT` bit oracle, `PH ⊆ P^{#SAT}`
[Arora and Barak, Theorem 9.11], and of the bit lemma for parsimoniously `#P`-hard functions,
used through ordinary imports. -/

set_option linter.privateModule false

namespace CslibFrontierTests.TodaSharpSAT

open Cslib Cslib.Complexity Turing.MultiTapeTM

/-- **Toda's theorem, `PH ⊆ P^{#SAT}`**, applied to the universal language via `P ⊆ NP ⊆ PH`:
the fixed oracle language is the bit graph of `#SAT` on `encCNF` formulas. -/
example : (Set.univ : Set (List Bool)) ∈ PWithOracle (bitGraph encCNF SharpSAT) encBits :=
  PH_subset_PWithOracle_bitGraph_SharpSAT (NP_subset_PH
    (P_subset_NP ⟨fun _ => true, .const true, fun _ => by simp⟩))

/-- `coNP ⊆ P^{#SAT}`. -/
example : coNP encBits ⊆ PWithOracle (bitGraph encCNF SharpSAT) encBits :=
  coNP_subset_PH.trans PH_subset_PWithOracle_bitGraph_SharpSAT

/-- `PP ⊆ P^{#SAT}`: the bit lemma applies to any `#P` function bit, not only Toda's. -/
example : PP encBits ⊆ PWithOracle (bitGraph encCNF SharpSAT) encBits := fun _ hA =>
  let ⟨_, hf, _, h⟩ := exists_SharpP_testBit_of_mem_PP hA
  CookLevin.SharpSAT_sharpPHard.mem_PWithOracle_bitGraph_of_testBit hf h

end CslibFrontierTests.TodaSharpSAT
