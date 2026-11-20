/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.QMA

/-!
# Quantum verification of classical witnesses

`QCMA` uses the same polynomial-time circuit verifiers as `QMA`, with a classical witness
[Aaronson, Kuperberg][AaronsonKuperberg2007]. Both completeness and soundness refer to
computational basis witnesses.

## Main definitions

* `QCMA`: quantum classical Merlin–Arthur.
* `BQNP`: Kitaev's name for `QMA` [Kitaev, Shen, Vyalyi][KitaevShenVyalyi2002].
-/

@[expose] public section

namespace Cslib.Complexity

open Quantum

variable {α : Type}

/-- Kitaev's alternate name for quantum Merlin–Arthur. -/
abbrev BQNP (enc : α ↪ List Bool) : Set (Set α) := QMA enc

/-- Quantum verification with a classical witness, completeness `2 / 3` and soundness `1 / 3`. -/
def QCMA (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ V : UniformVerifierFamily, ∀ a,
    (a ∈ A → ∃ w : Fin (V.witnessLength (enc a).length) → Bool,
      2 / 3 ≤ V.acceptProb (enc a) (ket w)) ∧
    (a ∉ A → ∀ w : Fin (V.witnessLength (enc a).length) → Bool,
      V.acceptProb (enc a) (ket w) ≤ 1 / 3)}


/-- A BQP decider can be used as a QCMA verifier with an empty witness. -/
theorem BQP_subset_QCMA {enc : α ↪ List Bool} : BQP enc ⊆ QCMA enc := by
  rintro A ⟨F, hF⟩
  refine ⟨UniformVerifierFamily.ofCircuitFamily F, fun a => ⟨?_, ?_⟩⟩
  · intro ha
    refine ⟨fun _ => false, ?_⟩
    simpa only [UniformVerifierFamily.acceptProb_ofCircuitFamily, norm_ket, one_pow, one_mul]
      using (hF a).1 ha
  · intro ha w
    simpa only [UniformVerifierFamily.acceptProb_ofCircuitFamily, norm_ket, one_pow, one_mul]
      using (hF a).2 ha

end Cslib.Complexity
