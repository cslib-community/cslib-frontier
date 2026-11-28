/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Init
import CslibFrontier.Algorithms.Lean.ZFunction.FromPrefix
import CslibFrontier.Algorithms.Lean.ZFunction.ToPrefix
meta import CslibFrontier.Algorithms.Lean.ZFunction.FromPrefix
meta import CslibFrontier.Algorithms.Lean.ZFunction.ToPrefix
import CslibFrontier.Algorithms.WordRAM.ZFunction.FromPrefix
import CslibFrontier.Algorithms.WordRAM.ZFunction.ToPrefix
meta import CslibFrontier.Algorithms.WordRAM.ZFunction.FromPrefix
meta import CslibFrontier.Algorithms.WordRAM.ZFunction.ToPrefix
meta import CslibFrontier.Computability.WordRAM.Structured.FastEval

/-!
# Conversions between Z-values and KMP prefix tables

The examples exercise shared prefixes of different lengths, overlapping occurrences, and the
first entry where the two table conventions differ.
-/

set_option linter.privateModule false
set_option linter.hashCommand false

namespace Cslib.Algorithms.Lean.ZFunction.Tests

#guard zToPrefix #[] = #[] ∧ fromPrefix #[] = #[]
#guard zToPrefix #[1] = #[0] ∧ fromPrefix #[0] = #[1]

-- The prefixes of "aabcaabdaae" have borders from three distinct occurrences of "aa".
#guard zToPrefix #[11, 1, 0, 0, 3, 1, 0, 0, 2, 1, 0] = #[0, 1, 0, 0, 1, 2, 3, 0, 1, 2, 0]
#guard fromPrefix #[0, 1, 0, 0, 1, 2, 3, 0, 1, 2, 0] = #[11, 1, 0, 0, 3, 1, 0, 0, 2, 1, 0]

-- A singleton Z-table must start with 1. Inverse laws require realizability.
#guard fromPrefix (zToPrefix #[0]) ≠ #[0]

-- The out-of-range entry gets a fresh representative; the next positive entry copies index zero.
#guard prefixWord #[0, 9, 1] = #[0, 1, 0]

example (w : Array Bool) :
    ((prefixTableEquiv Bool) ⟨zArray w, ⟨w, rfl⟩⟩).val = KMP.computePrefix w :=
  zToPrefix_zArray w

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.ZFunction

private meta def checkRun {r : ℕ} (p : Program .standard r) (w budget : ℕ)
    (input expected : List ℕ) : Bool :=
  match p.runFastList w budget input with
  | none => false
  | some (result, steps) => result == expected && steps ≤ budget

-- Empty input at the minimum width, intersecting Z-boxes, and out-of-range numeric entries.
#guard checkRun toPrefixProgram 1 9 [] []
#guard checkRun fromPrefixProgram 1 19 [] []
#guard checkRun toPrefixProgram 4 (20 * 5 + 9) [5, 0, 3, 0, 1] [0, 0, 1, 2, 3]
#guard checkRun fromPrefixProgram 4 (50 * 5 + 19) [0, 0, 1, 2, 3] [5, 0, 3, 0, 1]
#guard checkRun fromPrefixProgram 3 (50 * 3 + 19) [0, 7, 1] [3, 0, 1]
#guard checkRun toPrefixProgram 3 (20 * 3 + 9) [0, 7, 0] [0, 1, 2]

end Cslib.Algorithms.Lean.ZFunction.Tests
