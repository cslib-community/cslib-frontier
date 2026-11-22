/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Foundations.Data.BitString.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq

/-!
# Polynomial-time row replacement in bit lists

`Cslib.BitString.replaceRow` replaces one fixed-width row in a `count × width` flat bit list,
padding missing bits of the surrounding rows with `false`.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.bitsReplaceRowWithInput`: replacing a computed row in a
  computed raw word at unary `width`, `count`, and row index `j` is polynomial time.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Replacing one fixed-width row of a flat list word is computable in polynomial time. -/
@[fun_prop]
theorem bitsReplaceRowWithInput {α : Type} {encode : α ↪ List Bool}
    {width count j : α → ℕ} {x word : α → List Bool}
    (hwidth : ComputableInPolyTime width encode encUnary)
    (hcount : ComputableInPolyTime count encode encUnary)
    (hj : ComputableInPolyTime j encode encUnary)
    (hx : ComputableInPolyTime x encode encBits)
    (hword : ComputableInPolyTime word encode encBits) :
    ComputableInPolyTime
      (fun a => Cslib.BitString.replaceRow (width a) (count a) (j a) (x a) (word a))
      encode encBits := by
  unfold Cslib.BitString.replaceRow
  apply flatMapToBitsWithInput (unary_range' hcount)
  have hfst := fst encode encUnary
  have hsnd := snd encode encUnary
  exact ite_decide
    (unary_eq' hsnd (hj.comp hfst))
    (hx.comp hfst)
    (bitsRowWithInput (hwidth.comp hfst) hsnd (hword.comp hfst))

end Turing.MultiTapeTM.ComputableInPolyTime
