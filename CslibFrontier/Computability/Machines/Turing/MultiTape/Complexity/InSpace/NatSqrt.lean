/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.StoredCount
import CslibFrontier.Foundations.Data.List.OfFn
import Mathlib.Data.Nat.Sqrt

/-!
# Floor square root in linear space

The floor square root of `n` counts the positive integers whose squares are at most `n`. A
stored binary counter enumerates the candidates and tests each one by binary multiplication.

## Main results

* `Turing.MultiTapeTM.ComputableInSpace.natSqrt`: binary floor square root uses space linear
  in the input bit length.
-/

namespace Turing.MultiTapeTM.ComputableInSpace

/-- The floor square root of a binary natural is computable in linear space. -/
public theorem natSqrt : ComputableInSpace Nat.sqrt encNat encNat (fun n => (encNat n).length) := by
  let test := fun (p : ℕ × ℕ) => !(decide (p.2 < (p.1 + 1) * (p.1 + 1)))
  have hid : ComputableInSpace id encNat encNat (fun n => (encNat n).length) :=
    of_inO (ComputableInO.of_eq (f := id) fun _ => rfl)
  have hi := budget_natSucc (fst encNat encNat)
  have htest : ComputableInSpace test (encPair encNat encNat) encBool
      (fun p => (encNat p.1).length + (encNat p.2).length) :=
    (budget_finite (encC := encBool) not (budget_natLt (snd encNat encNat)
      (budget_natMul hi hi))).weaken (.of_le_linear 2 2 fun p => by
        simp only [length_encPair]; omega)
  have hcount : ComputableInSpace (fun n => (List.range n).countP fun i => test (i, n))
      encNat encNat (fun n => (encNat n).length) :=
    (countWith hid htest).weaken (.of_le_linear 2 0 fun n => by
      have := Nat.log2_le_self (encNat n).length
      omega)
  apply hcount.of_enc_eq
  intro n
  congr 1
  rw [List.countP_range_eq_card_filter, ← Finset.card_range n.sqrt]
  symm
  refine Finset.card_bij (fun (j : Fin n) _ => j.val) ?_ ?_ ?_
  · intro j hj
    have h := (Finset.mem_filter.mp hj).2
    simpa [test, ← Nat.le_sqrt] using h
  · intro a _ b _ hab
    exact Fin.ext hab
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    refine ⟨⟨j, hj'.trans_le (Nat.sqrt_le_self n)⟩, ?_, rfl⟩
    simp [test, ← Nat.le_sqrt, hj']

end Turing.MultiTapeTM.ComputableInSpace
