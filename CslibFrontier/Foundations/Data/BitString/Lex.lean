/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
import Mathlib.Data.List.Lex

/-!
# Lexicographic order on fixed-width bit strings

`Cslib.BitString.lexSwap` tells a caller whether to swap two strings to put them in
lexicographic order. It can also be used to permute data associated with the coordinates.
-/

public section

namespace Cslib.BitString

/-- Whether lexicographic sorting interchanges `a` and `b`. Ties preserve input order. -/
@[expose] def lexSwap {n : ℕ} (a b : Fin n → Bool) : Bool :=
  decide (List.ofFn b < List.ofFn a)

end Cslib.BitString
