/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Computable.Defs
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelNormalForm
import Mathlib.Data.Fintype.Option

/-!
# Internal normalized witnesses for total computability

Total computability has no normal-form premise. This module applies the existing single-machine
normalization theorem and exposes its native realizing machine, rather than a second numerical
computability predicate. Composition and Rice's self-reference compiler use the resulting clean
final configuration. This module is a proof dependency of the public computability facade.
-/

public section

namespace Turing.MultiTapeTM.Internal.TotalComputability

/-- A total realizing machine can be normalized without changing its encoded function.
The arbitrary time and workspace functions remain independent. -/
theorem normalizedMachine {α β : Type*} {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (h : IsComputable f encIn encOut) :
    ∃ t s : α → ℕ, ∃ (k : ℕ) (State : Type) (_ : Finite State)
      (tm : MultiTapeTM k Bool State),
      ∀ a, tm.ComputesTidilyInTimeAndSpace (encIn a) (encOut (f a)) (t a) (s a) := by
  obtain ⟨t, s, k, State, hfin, tm, htm⟩ := h
  let : Finite State := hfin
  exact ⟨fun a => 2 * t a + 3 * s a + 2 * k + 4,
    fun a => 2 * s a + 2 * k * (3 * s a + 2 * k + 3),
    k + k, _, inferInstance, tidy false true tm,
    fun a => (htm a).computesTidily_tidy Bool.false_ne_true⟩

end Turing.MultiTapeTM.Internal.TotalComputability
