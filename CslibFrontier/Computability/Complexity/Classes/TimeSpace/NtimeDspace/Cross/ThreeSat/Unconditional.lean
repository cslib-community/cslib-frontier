/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.CubeCounting
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.CubeFinal

/-!
# Corollary 7.2, unconditionally

`CslibFrontier/Computability/Complexity/Classes/TimeSpace/NtimeDspace/Cross/ThreeSatFinal.lean`
proves Corollary 7.2 from `Theorem41`, a residue form of Theorem 2.3 for
every network family with logspace access. Theorem 2.3 in bit form holds for every family
(`cubeCounting`, CubeFinal.lean), and gives the residue form (`theorem41_of_cubeCounting`,
CubeCounting.lean, with every prime `p ≤ s`). This module discharges the hypothesis.

## Main results

* `theorem41`: the residue form of Theorem 2.3 used by Corollary 7.2.
* `cor_9_4_unconditional`: the number of satisfying assignments of a 3-CNF formula with `m ≥ 2`
  clauses in which every variable occurs is computed, bit by bit, in space `O(m/√log m)` and time
  `2^{O(m/√log m)}`.
* `cor_9_4_bits_unconditional`: the same for every bit position, with an added `log₂ |input|`.
-/

public section

namespace Cslib.Complexity.NtimeDspace.Cross.ThreeSat

open NtimeDspace.ProgLang

/-- The residue form of Theorem 2.3 (`Theorem41`), from `cubeCounting`. -/
theorem theorem41 : Theorem41 := CubeCounting.theorem41_of_cubeCounting cubeCounting

/-- **Corollary 7.2.** One deterministic machine computes every bit of the number of satisfying
assignments of a 3-CNF formula with `m ≥ 2` clauses in which every variable occurs, in space
`O(m/√log m)` and time `2^{O(m/√log m)}`. -/
theorem cor_9_4_unconditional :
    ∃ C, Turing.MultiTapeTM.DecidableInTimeAndSpace SmallBitLanguage smallEnc
      (fun a => 2 ^ (C * SqrtLog a.1.φ.length)) (fun a => C * SqrtLog a.1.φ.length) :=
  cor_9_4 theorem41

/-- **Corollary 7.2, every bit position.** -/
theorem cor_9_4_bits_unconditional :
    ∃ C, Turing.MultiTapeTM.DecidableInTimeAndSpace BitLanguage instEnc
      (fun a => 2 ^ (C * bud a)) (fun a => C * bud a) :=
  cor_9_4_bits theorem41

end Cslib.Complexity.NtimeDspace.Cross.ThreeSat
