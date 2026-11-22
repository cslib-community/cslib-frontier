/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.Corollaries
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.CubeFinal
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.GeneralTheorem

/-!
# Theorem 1.1, unconditionally

Theorem 2.3 for the block networks (`cubeBlockBits`, `CubeFinal`: bit `j` of every block network
by the explicit formula of §6), the column adder over schedules (`Exact.clockedBits_of_blockBits`,
`ColumnAdder`), the count test (`Exact.clockedCounting_of_clockedBits`) and the transfer theorem
with doubling clocks (`generalSimulation_of_clocked`, `GeneralTheorem`) give Theorem 1.1 for every
`t(n) ≥ n` (`generalSimulation`); `t` need not be constructible. The endpoints of Theorem 1.1 and
Corollary 1.2 are stated in `CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace`.

## Main results

* `generalSimulation`: Theorem 1.1 for every `t(n) ≥ n`, as `Cross.GeneralSimulation`.
-/

public section

namespace Cslib.Complexity.NtimeDspace.Crossing

open NtimeDspace.Cross

/-- Theorem 1.1 for every `t(n) ≥ n`, as `GeneralSimulation`. -/
theorem generalSimulation : GeneralSimulation :=
  generalSimulation_of_clocked
    (Exact.clockedCounting_of_clockedBits (Exact.clockedBits_of_blockBits cubeBlockBits))

end Cslib.Complexity.NtimeDspace.Crossing
