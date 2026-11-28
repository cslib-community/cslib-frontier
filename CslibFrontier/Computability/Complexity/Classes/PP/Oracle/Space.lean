/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PP.Oracle
public import CslibFrontier.Computability.Complexity.Classes.Space
import CslibFrontier.Computability.Complexity.Classes.Oracle.Space
import CslibFrontier.Computability.Complexity.Classes.SharpP.Space
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain

/-!
# Majority with a polynomial-space oracle

A strict polynomial-time majority verifier is evaluated in polynomial space by simulating
its oracle and streaming all polynomial-length certificates. The binary acceptance counter
reuses the verifier workspace, and exact ties reject. The oracle's cost is included.

## Main results

* `Cslib.Complexity.PPWithOracle_subset_PSPACE`: majority relative to a polynomial-space oracle.
-/

public section
namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- Majority with a polynomial-space oracle is in polynomial space. The verifier's clock bounds
query length; simulating each oracle answer charges its polynomial workspace. -/
theorem PPWithOracle_subset_PSPACE {A : Set (List Bool)} (hA : A ∈ PSPACE encBits) :
    PPWithOracle A enc ⊆ PSPACE enc := by
  rintro L ⟨p, V, hV, hL⟩
  obtain ⟨T, S, hS, hV⟩ := hV.exists_computableInO hA
  have hcount := computableInPolySpace_acceptCount (r := fun a => p.eval (enc a).length)
    (ComputableInPolySpace.of_inSpace hS (ComputableInSpace.of_inO hV))
    ((ComputableInPolyTime.unary_eval p).comp (.encoding_length enc))
  have hpow : ComputableInPolyTime (fun a => 2 ^ p.eval (enc a).length) enc encNat :=
    ComputableInPolyTime.binary_two_pow.comp (by fun_prop)
  have hdouble : ComputableInPolyTime (fun n : ℕ => 2 * n) encNat encNat := by fun_prop
  have htest := (ComputableInPolySpace.of_polyTime ComputableInPolyTime.binary_lt).comp
    ((ComputableInPolySpace.of_polyTime hpow).prod
      ((ComputableInPolySpace.of_polyTime hdouble).comp hcount))
  exact ⟨_, htest, fun a => by simpa using hL a⟩

end Cslib.Complexity
