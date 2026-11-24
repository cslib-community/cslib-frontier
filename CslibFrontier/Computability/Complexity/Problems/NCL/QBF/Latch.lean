/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Gate
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Implements
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Occurrence

/-!
# The latch and the locked try

The latch of [HearnDemaine2005, Figure 6] (`Cslib.Complexity.NCL.QBF.latch`), drawn with all its
wires below: an OR vertex with the lock and the branches `upper` and `lower`, an AND vertex on
`upper` with the red edges `A` and `mem`, and an AND vertex on `lower` with the red edges `mem` and
`B`. While the lock points down, away from the OR vertex, the latch is locked: one branch points
into the OR vertex, so the AND vertex on it needs both its red edges. Then `mem` cannot move, and
the red edge on the side that `mem` points into is inactive.

Both quantifiers decide whether to try their suffix by the same part
(`Cslib.Complexity.NCL.QBF.lockedTry`): a latch whose lock enters a conversion to the red `key`,
and the AND vertex `(fork, key; try)`, which lets the try wire leave only when the red `fork` and
`key` both point into it, that is, when the quantifier is tried and its latch is locked.

## Main definitions

* `Cslib.Complexity.NCL.QBF.latch`: the latch `[] → [lock, A, B]`.
* `Cslib.Complexity.NCL.QBF.lockedTry`: the locked try `[fork] → [try, free, A, B]`.

## Main results

* `Cslib.Complexity.NCL.QBF.Latch.not_step_mem`: reversing the latch memory needs its lock
  pointing into the OR vertex.
* `Cslib.Complexity.NCL.QBF.LockedTry.fork_of_tryOut`: trying out needs `fork`.
* `Cslib.Complexity.NCL.QBF.LockedTry.mem_of_a`, `Cslib.Complexity.NCL.QBF.LockedTry.mem_of_b`:
  while trying out, an active red edge of the latch agrees with `mem`.
* `Cslib.Complexity.NCL.QBF.LockedTry.not_step_mem`: while trying out, `mem` cannot move.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF

open Diagram Gate

local notation "R" => Color.red
local notation "B" => Color.blue

namespace Latch

/-- The OR vertex, with the lock, `upper` and `lower` below. -/
@[expose] def orLayer : Diagram Gate [] [B, B, B] := node [] [B, B, B]

/-- The AND vertex on `upper`, with `A` and `mem` below. -/
@[expose] def upperLayer : Diagram Gate [B, B, B] [B, R, R, B] := pad [B] (node [B] [R, R]) [B]

/-- The AND vertex on `mem` and `lower`, with `B` below. -/
@[expose] def lowerLayer : Diagram Gate [B, R, R, B] [B, R, R] := pad [B, R] (node [R, B] [R]) []

end Latch

open Latch in
/-- **The latch** `[] → [lock, A, B]` [HearnDemaine2005, Figure 6]. -/
@[expose]
def latch : Diagram Gate [] [B, R, R] := orLayer.comp (upperLayer.comp lowerLayer)

namespace Latch

/-- The blue lock wire, pointing down when the latch is locked. -/
@[expose] def lock : latch.Edge := latch.bottom 0

/-- The state edge: it points down, into the AND vertex of `B`, or up, into that of `A`. -/
@[expose] def mem : latch.Edge :=
  compRight orLayer (upperLayer.comp lowerLayer) (compLeft upperLayer lowerLayer
    (upperLayer.bottom 2))

/-- Changing the memory requires the lock to point into the OR vertex. -/
theorem not_step_mem {t : latch.Edge → Bool} (ht : (latch.graph Gate.interp).Legal t)
    (ht' : (latch.graph Gate.interp).Legal (reverse t mem)) : t lock = false :=
  eq_of_refutes_step (l := [])
    ((Refutation.split (latch.num mem) .conflict .conflict).refutes (n := 3)
      (by decide +kernel)) ht ht' (by simp)

end Latch

namespace LockedTry

/-- The latch beside `fork`. Below: `fork`, the lock, `A`, `B`. -/
@[expose] def latchLayer : Diagram Gate [R] [R, B, R, R] := pad [R] latch []

/-- The lock enters a conversion. Below: `fork`, `key`, a free wire, `A`, `B`. -/
@[expose] def keyLayer : Diagram Gate [R, B, R, R] [R, R, R, R, R] := pad [R] (gen vnoc) [R, R]

/-- The AND vertex `(fork, key; try)`. Below: `try`, the free wire, `A`, `B`. -/
@[expose]
def tryLayer : Diagram Gate [R, R, R, R, R] [B, R, R, R] := pad [] (node [R, R] [B]) [R, R, R]

end LockedTry

open LockedTry in
/-- **The locked try** `[fork] → [try, free, A, B]`: the try wire may leave only while `fork` is
active and the latch is locked. -/
@[expose]
def lockedTry : Diagram Gate [R] [B, R, R, R] := latchLayer.comp (keyLayer.comp tryLayer)

namespace LockedTry

/-- The state edge of the latch: it points down, into the AND vertex of `B`, or up, into that of
`A`. -/
@[expose] def mem : lockedTry.Edge :=
  compLeft latchLayer (keyLayer.comp tryLayer) (padIn [R] latch [] Latch.mem)

/-- The red wire `fork` above. -/
@[expose] def fork : lockedTry.Edge := .inl 0
/-- The try wire below. -/
@[expose] def tryOut : lockedTry.Edge := lockedTry.bottom 0
/-- The red edge `A` of the latch. -/
@[expose] def a : lockedTry.Edge := lockedTry.bottom 2
/-- The red edge `B` of the latch. -/
@[expose] def b : lockedTry.Edge := lockedTry.bottom 3

/-- The constraint graph of the locked try. -/
abbrev graph : ConstraintGraph (lockedTry.Vtx Gate.interp) lockedTry.Edge :=
  lockedTry.graph Gate.interp

variable {t : lockedTry.Edge → Bool}

/-- **The try wire leaves only while `fork` is active.** -/
theorem fork_of_tryOut (ht : graph.Legal t) (h : t tryOut = true) : t fork = true :=
  eq_of_refutes (l := [(tryOut, true)])
    (Refutation.conflict.refutes (n := 1) (by decide +kernel)) ht (by simp [h])

/-- **While trying out, an active `A` agrees with `mem`.** Trying out needs `key`, so the latch
is locked: one branch points into the OR vertex, and the AND vertex on it needs both its red
edges. -/
theorem mem_of_a (ht : graph.Legal t) (h : t tryOut = true) (ha : t a = true) : t mem = true :=
  eq_of_refutes (l := [(tryOut, true), (a, true)])
    (Refutation.conflict.refutes (n := 3) (by decide +kernel)) ht (by simp [h, ha])

/-- **While trying out, an active `B` agrees with `mem`.** -/
theorem mem_of_b (ht : graph.Legal t) (h : t tryOut = true) (hb : t b = true) : t mem = false :=
  eq_of_refutes (l := [(tryOut, true), (b, true)])
    (Refutation.conflict.refutes (n := 3) (by decide +kernel)) ht (by simp [h, hb])

/-- **While trying out, `mem` cannot move**: with the latch locked, the AND vertex on the branch
into the OR vertex needs `mem` whichever way it points. -/
theorem not_step_mem (ht : graph.Legal t) (ht' : graph.Legal (reverse t mem)) :
    t tryOut = false :=
  eq_of_refutes_step (l := [])
    ((Refutation.split (lockedTry.num mem) .conflict .conflict).refutes (n := 3)
      (by decide +kernel)) ht ht' (by simp)

end LockedTry

end Cslib.Complexity.NCL.QBF
