/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
public import CslibFrontier.Foundations.Data.Nat.ChineseRemainder

/-!
# Polynomial-time two-modulus Chinese Remainder recombination

Polynomial-time certificate for `Cslib.crtCombine` on binary naturals (`Turing.MultiTapeTM.encNat`).

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.crtCombine'`: `Cslib.crtCombine` is computable in
  polynomial time whenever its five natural-number arguments are.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Two-modulus Chinese Remainder recombination `Cslib.crtCombine` is computable in polynomial time
on binary naturals. -/
@[fun_prop, program_certificate]
theorem crtCombine' {α : Type} {input : α ↪ List Bool} {D L a xL inv : α → ℕ}
    (hD : ComputableInPolyTime D input encNat)
    (hL : ComputableInPolyTime L input encNat)
    (ha : ComputableInPolyTime a input encNat)
    (hxL : ComputableInPolyTime xL input encNat)
    (hinv : ComputableInPolyTime inv input encNat) :
    ComputableInPolyTime (fun x => Cslib.crtCombine (D x) (L x) (a x) (xL x) (inv x))
      input encNat := by
  unfold Cslib.crtCombine
  exact .binary_add' ha
    (.binary_mul' hD
      (.binary_mod'
        (.binary_mul' (.binary_add' hxL (.binary_sub' hL (.binary_mod' ha hL))) hinv) hL))

end Turing.MultiTapeTM.ComputableInPolyTime
