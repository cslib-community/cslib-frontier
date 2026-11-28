/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import CslibFrontier.Foundations.Data.BitString.List.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Polynomial-time fixed-width binary words

## Main results

* `Cslib.Complexity.binaryWord_polyTime`: `BitString.binaryWord (w x) (a x)` is computable in
  polynomial time when `w` is computed in unary and `a` in binary.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- The fixed-width binary word of a computed number is computable in polynomial time. -/
theorem binaryWord_polyTime {α : Type} {input : α ↪ List Bool} {w a : α → ℕ}
    (hw : ComputableInPolyTime w input encUnary) (ha : ComputableInPolyTime a input encNat) :
    ComputableInPolyTime (fun x => BitString.binaryWord (w x) (a x)) input encBits := by
  have hbits := (ComputableInPolyTime.of_eq (f := Nat.bits)
    (encIn := encNat) (encOut := encBits) fun _ => rfl).comp ha
  have hpadding := ComputableInPolyTime.unary_sub.comp
    (hw.prod (ComputableInPolyTime.length_bits.comp hbits))
  have hplain := ComputableInPolyTime.bitsAppend
    ((ComputableInPolyTime.bitsReplicate false).comp hpadding)
    (ComputableInPolyTime.bitsReverse.comp hbits)
  simpa only [BitString.binaryWord, Function.comp_def] using hplain

end Cslib.Complexity
