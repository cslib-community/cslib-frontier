/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Latch

/-!
# The existential quantifier

The existential quantifier of [HearnDemaine2005, Figure 7(a)], drawn as a diagram over
`Cslib.Complexity.NCL.Gate` (`Cslib.Complexity.NCL.QBF.existsGadget`). Its wires are, above, the
satisfied wire `sat` and the try wire `try`; below, `sat`, `try` and the literal wires `pos` and
`neg`. The wire `sat` runs straight through. Every wire is active when it points down, except
`sat`, which is active when it points up.

The try wire enters a conversion to the red `fork`, which tries the locked try
(`Cslib.Complexity.NCL.QBF.lockedTry`); the red edges of its latch are the literal wires. The
two free wires of the conversions end together.

## Main definitions

* `Cslib.Complexity.NCL.QBF.existsGadget`: the gadget.

## Main results

* `Cslib.Complexity.NCL.QBF.ExistsGadget.tryIn_of_tryOut`: trying out needs trying in.
* `Cslib.Complexity.NCL.QBF.ExistsGadget.mem_of_pos`,
  `Cslib.Complexity.NCL.QBF.ExistsGadget.mem_of_neg`: while trying out, an active literal wire
  agrees with `mem`.
* `Cslib.Complexity.NCL.QBF.ExistsGadget.not_step_mem`: while trying out, `mem` cannot move.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF

open Diagram Gate

local notation "R" => Color.red
local notation "B" => Color.blue

namespace ExistsGadget

/-- The try wire enters a conversion. Below: `sat`, `fork`, a free wire. -/
@[expose] def enterLayer : Diagram Gate [B, B] [B, R, R] := pad [B] (gen vnoc) []

/-- `fork` crosses the free wire. -/
@[expose] def crossLayer : Diagram Gate [B, R, R] [B, R, R] := pad [B] (swap R R) []

/-- The locked try. Below: `sat`, a free wire, `try`, a free wire, `pos`, `neg`. -/
@[expose] def lockedLayer : Diagram Gate [B, R, R] [B, R, B, R, R, R] := pad [B, R] lockedTry []

/-- `try` crosses the first free wire, and the free wires end. -/
@[expose] def closeLayer : Diagram Gate [B, R, B, R, R, R] [B, B, R, R] :=
  (pad [B] (swap R B) [R, R, R]).comp (pad [B, B] (gen cap) [R, R])

end ExistsGadget

open ExistsGadget in
/-- **The existential quantifier** `[sat, try] → [sat, try, pos, neg]`. -/
@[expose]
def existsGadget : Diagram Gate [B, B] [B, B, R, R] :=
  enterLayer.comp (crossLayer.comp (lockedLayer.comp closeLayer))

namespace ExistsGadget

/-- The locked try in the gadget. -/
@[expose] def lockedOcc : Occurrence lockedTry existsGadget :=
  .compRight _ (.compRight _ (.compLeft _ (.pad [B, R] [] .refl)))

/-- The wire `sat`. -/
@[expose] def sat : existsGadget.Edge := .inl 0
/-- The try wire above. -/
@[expose] def tryIn : existsGadget.Edge := .inl 1
/-- The try wire below. -/
@[expose] def tryOut : existsGadget.Edge := existsGadget.bottom 1
/-- The literal wire of `true`. -/
@[expose] def pos : existsGadget.Edge := existsGadget.bottom 2
/-- The literal wire of `false`. -/
@[expose] def neg : existsGadget.Edge := existsGadget.bottom 3
/-- The state edge of the latch: it points down when the value is `true`. -/
@[expose] def mem : existsGadget.Edge := lockedOcc.emb LockedTry.mem

/-- The constraint graph of the gadget. -/
abbrev graph : ConstraintGraph (existsGadget.Vtx Gate.interp) existsGadget.Edge :=
  existsGadget.graph Gate.interp

variable {t : existsGadget.Edge → Bool}

/-- **Trying out needs trying in**: the AND vertex `(fork, key; try)` needs `fork`, which the
conversion lets out only when the try wire above points in. -/
theorem tryIn_of_tryOut (ht : graph.Legal t) (h : t tryOut = true) : t tryIn = true := by
  have hfork : t (lockedOcc.emb LockedTry.fork) = true :=
    LockedTry.fork_of_tryOut (lockedOcc.legal ht) h
  exact eq_of_refutes (l := [(lockedOcc.emb LockedTry.fork, true)])
    (Refutation.conflict.refutes (n := 1) (by decide +kernel)) ht (by simp [hfork])

/-- **While trying out, `pos` agrees with `mem`.** -/
theorem mem_of_pos (ht : graph.Legal t) (h : t tryOut = true) (hp : t pos = true) :
    t mem = true :=
  LockedTry.mem_of_a (lockedOcc.legal ht) h hp

/-- **While trying out, `neg` agrees with `mem`.** -/
theorem mem_of_neg (ht : graph.Legal t) (h : t tryOut = true) (hn : t neg = true) :
    t mem = false :=
  LockedTry.mem_of_b (lockedOcc.legal ht) h hn

/-- **While trying out, `mem` cannot move.** -/
theorem not_step_mem (ht : graph.Legal t) (ht' : graph.Legal (reverse t mem)) :
    t tryOut = false :=
  LockedTry.not_step_mem (lockedOcc.legal ht) (lockedOcc.legal_reverse ht')

/-- The value of an existential quantifier in a larger diagram is frozen while trying out. -/
theorem mem_eq_of_step {a b : List Color} {D : Diagram Gate a b}
    (o : Occurrence existsGadget D) {s t : D.Edge → Bool}
    (h : (D.graph Gate.interp).Step s t) (htry : s (o.emb tryOut) = true) :
    s (o.emb mem) = t (o.emb mem) :=
  o.apply_eq_of_not_legal_reverse h fun hm =>
    Bool.noConfusion (htry.symm.trans (not_step_mem (o.legal h.legal_left) hm))

end ExistsGadget

end Cslib.Complexity.NCL.QBF
