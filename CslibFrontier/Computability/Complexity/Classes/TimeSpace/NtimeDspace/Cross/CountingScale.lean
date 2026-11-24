/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.CubeStatement

/-!
# Theorem 2.3 in bit form at a general space bound

`CubeCounting` (`CubeStatement.lean`) is the paper's Theorem 2.3 (`thm:counting`) at the space
bound `SqrtLog s = ⌊s / ⌊√⌊log₂ s⌋⌋⌋ + 1`. Section 8 of the paper (`sec:discussion`) asks
what a faster procedure of the same kind would give. `CubeCountingAt D` is the same statement
with `D s` in place of `SqrtLog s`: one closed program on `[s, |w|, j]` computes bit `j` of
`Z(G)` for every network `G` of every family with logspace access, with every value of its
evaluation below `2^(C · D s)` (so space `O(D s)` and time `2^{O(D s)}` after compilation).
`CslibFrontier/Computability/Complexity/Classes/TimeSpace/NtimeDspace/Cross/ThreeSat/AtScale.lean`
derives the paper's consequence for counting 3-SAT.

## Main definitions

* `CubeCountingAt D`: Theorem 2.3 in bit form at the space bound `D`.

## Main results

* `cubeCountingAt_sqrtLog`: at `D = SqrtLog` it is `CubeCounting`.

## References

* The paper (`separating-ntime-from-space.tex`), §2, Theorem 2.3 (`thm:counting`); §8, first
paragraph.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross

open NtimeDspace.ProgLang NtimeDspace.SumProduct

/-- **Theorem 2.3 in bit form at the space bound `D`**: for every family of networks with logspace
access, one closed program over `[s, |w|, j]` computes bit `j` of `Z(G)` for every description `w`
of a network `G` of the family at size `s ≥ s₀`, with every value of its evaluation below
`2^(C · D s)`. -/
def CubeCountingAt (D : ℕ → ℕ) : Prop :=
  ∀ F : LogspaceNetFamily, ∃ (Q : Prog) (C s₀ : ℕ), Prog'.closed 3 Q = true ∧
    ∀ (w : List Bool) (s j : ℕ), F.Mem w s → s₀ ≤ s →
      Q.eval w [s, w.length, j] = (F.net w s).value.toNat / 2 ^ j % 2 ∧
        Q.Bounded w (2 ^ (C * D s)) [s, w.length, j]

theorem cubeCountingAt_sqrtLog : CubeCountingAt SqrtLog ↔ CubeCounting := Iff.rfl

end Cslib.Complexity.NtimeDspace.Cross
