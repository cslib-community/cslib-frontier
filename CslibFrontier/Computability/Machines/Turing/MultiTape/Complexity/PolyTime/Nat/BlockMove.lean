/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Nat.BlockMove
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Native block movement on binary indices

The raw block permutation performs only binary comparison, addition and truncated subtraction.
Its runtime depends on the encoded operands even for an index beyond the actual block lengths.
This supplies the index arithmetic used by the native ordered-boundary append program.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Move computed binary blocks with the exact total raw-index fallback. No operand is
converted into a unary iteration count. -/
theorem natBlockMove' {α : Type} {input : α ↪ List Bool}
    {before moved after index : α → ℕ}
    (hb : ComputableInPolyTime before input encNat)
    (hm : ComputableInPolyTime moved input encNat)
    (ha : ComputableInPolyTime after input encNat)
    (hi : ComputableInPolyTime index input encNat) :
    ComputableInPolyTime (fun x => Nat.blockMove (before x) (moved x) (after x) (index x))
      input encNat := by
  unfold Nat.blockMove
  fun_prop

end Turing.MultiTapeTM.ComputableInPolyTime
