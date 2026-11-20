/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import CslibFrontier.Algorithms.Reachability.DoubleCounting.Scan

/-! # Tests of the bounded double-counting scan -/

-- This file contains only checked clients.
set_option linter.privateModule false

namespace CslibFrontierTests.DoubleCountingScan

open Cslib.DoubleCounting

private def edge (u v : Fin 3) : Bool := u == 0 && v == 1

example (b : Scan.Branch 3) (result : Scan.Result)
    (h : Scan.tallyPrefix edge 0 2 1 b (by decide : 2 ≤ 3) = some result) :
    result.tally.count ≤ 2 ∧ result.tally.lengthSum ≤ 2 :=
  Scan.prefix_registers_le edge 0 2 1 b (by decide) result h

example (b : Scan.Branch 3)
    (hb : (Scan.runM (Scan.readSelection b) Scan.readNext (fun u v => pure (edge u v))
      0 2 1 (expected (fun u v => edge u v = true) 0 1) []).1 = some false) :
    (2 : Fin 3) ∉ Relation.reachableWithin (fun u v => edge u v = true) 0 1 := by
  simpa using (Scan.hit_iff_reachable edge 0 2 1 b false hb).symm

end CslibFrontierTests.DoubleCountingScan
