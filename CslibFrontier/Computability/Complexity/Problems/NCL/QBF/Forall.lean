/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Latch

/-!
# The universal quantifier

The universal quantifier of [HearnDemaine2005, Figure 7(b)], drawn as a diagram over
`Cslib.Complexity.NCL.Gate` (`Cslib.Complexity.NCL.QBF.forallGadget`). Its wires are, above, the
satisfied wire `satOut` and the try wire `try`; below, the satisfied wire `satIn`, `try` and the
literal wires `pos` and `neg`. Every wire is active when it points down, except the satisfied
wires, which are active when they point up.

The try wire enters an AND vertex that splits it into the red `fork`, which tries the locked try
(`Cslib.Complexity.NCL.QBF.lockedTry`), and the red `rec`. Each red edge of the variable latch is
converted to blue and split into a literal wire and a red signal: `check` on the side of `true`,
`bar` on the side of `false`.

A second latch, the record, remembers that the suffix was satisfied with the variable `false`.
Its lock is the blue `bridge` of the AND vertex `(bar, bridgeSat; bridge)`, so it opens only while
`bar` and the satisfied wire below are both active. Its red edges are `rec` and `recSat`; it is
set when its state edge `recMem` points to `rec`. Then `rec` points away from the try wire, so a
set record needs the quantifier tried. The satisfied wire below is split by the AND vertex
`(checkSat, bridgeSat; satIn)`; the AND vertex `(check, checkSat; satRed)` and a conversion feed
the AND vertex `(recSat, satBlue; satOut)`, so the satisfied wire above is active only when the
record is set, the variable is `true`, and the suffix is satisfied.

## Main definitions

* `Cslib.Complexity.NCL.QBF.forallGadget`: the gadget.

## Main results

The suffix below is assumed to be satisfied only while it is tried, which holds by induction from
the end of the chain of quantifiers.

* `Cslib.Complexity.NCL.QBF.ForallGadget.tryIn_of_tryOut`,
  `Cslib.Complexity.NCL.QBF.ForallGadget.mem_of_pos`,
  `Cslib.Complexity.NCL.QBF.ForallGadget.mem_of_neg`,
  `Cslib.Complexity.NCL.QBF.ForallGadget.not_step_mem`: the variable latch, as in the existential
  quantifier.
* `Cslib.Complexity.NCL.QBF.ForallGadget.satIn_of_satOut`,
  `Cslib.Complexity.NCL.QBF.ForallGadget.mem_of_satOut`,
  `Cslib.Complexity.NCL.QBF.ForallGadget.recMem_of_satOut`: satisfied above needs satisfied
  below, the value `true`, and the record set.
* `Cslib.Complexity.NCL.QBF.ForallGadget.tryIn_of_recMem`: a set record needs trying in.
* `Cslib.Complexity.NCL.QBF.ForallGadget.satIn_of_step_recMem`,
  `Cslib.Complexity.NCL.QBF.ForallGadget.mem_of_step_recMem`: the record moves only while the
  suffix is satisfied with the value `false`.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF

open Diagram Gate

local notation "R" => Color.red
local notation "B" => Color.blue

namespace ForallGadget

/-- The record latch. Below: `satOut`, `bridge`, `recSat`, `rec`, `try`. -/
@[expose] def recordLayer : Diagram Gate [B, B] [B, B, R, R, B] := pad [B] latch [B]

/-- The AND vertex `(rec, fork; try)`. Below: `satOut`, `bridge`, `recSat`, `fork`. -/
@[expose]
def splitLayer : Diagram Gate [B, B, R, R, B] [B, B, R, R] := pad [B, B, R] (node [R, B] [R]) []

/-- The locked try. Below: `satOut`, `bridge`, `recSat`, `try`, a free wire, `A`, `B`. -/
@[expose]
def lockedLayer : Diagram Gate [B, B, R, R] [B, B, R, B, R, R, R] := pad [B, B, R] lockedTry []

/-- The record latch, the split try wire and the locked try. -/
@[expose] def tryBlock : Diagram Gate [B, B] [B, B, R, B, R, R, R] :=
  recordLayer.comp (splitLayer.comp lockedLayer)

/-- The red edges of the variable latch are converted to blue, the free wires of the conversions
end, the blue wires split into `check`, `pos`, `bar`, `neg`, and `try` moves past the free wire
of the locked try, `check` and `bar`. Below: `satOut`, `bridge`, `recSat`, a free wire, `check`,
`bar`, `try`, `pos`, `neg`. -/
@[expose] def literalBlock : Diagram Gate [B, B, R, B, R, R, R] [B, B, R, R, R, R, B, R, R] :=
  (pad [B, B, R, B, R] ((gen conv).tensor (gen conv)) []).comp <|
  (pad [B, B, R, B, R, B] (swap R B) [R]).comp <|
  (pad [B, B, R, B, R, B, B] (gen cap) []).comp <|
  (pad [B, B, R, B, R] ((node [B] [R, R]).tensor (node [B] [R, R])) []).comp <|
  (pad [B, B, R, B, R, R] (swap R R) [R]).comp <|
  pad [B, B, R] (moveRight B [R, R, R] []) [R, R]

/-- The satisfied path, beside `try`, `pos`, `neg` on the right: the AND vertices
`(check, checkSat; satRed)`, `(recSat, satBlue; satOut)`, `(bar, bridgeSat; bridge)` and
`(checkSat, bridgeSat; satIn)`, a conversion from `satRed` to `satBlue`, and the free wires end. -/
@[expose] def satBlock : Diagram Gate [B, B, R, R, R, R, B, R, R] [B, B, R, R] :=
  (pad [B] (swap B R) [R, R, R, B, R, R]).comp <|
  (pad [B, R, B, R] (node [R] [R, B]) [R, B, R, R]).comp <|
  (pad [B, R, B, R, R] (gen vnoc) [R, B, R, R]).comp <|
  (pad [B, R] (moveLeft [B, R, R] R []) [R, R, B, R, R]).comp <|
  (pad [] (node [B, R, R] []) [B, R, R, R, R, B, R, R]).comp <|
  (pad [B] (swap R R) [R, R, B, R, R]).comp <|
  (pad [B, R] (gen cap) [R, B, R, R]).comp <|
  (pad [B] (swap R R) [B, R, R]).comp <|
  (pad [] (node [B, R] [R]) [R, B, R, R]).comp <|
  pad [] (node [R, R] [B]) [B, R, R]

end ForallGadget

open ForallGadget in
/-- **The universal quantifier** `[satOut, try] → [satIn, try, pos, neg]`. -/
@[expose]
def forallGadget : Diagram Gate [B, B] [B, B, R, R] :=
  tryBlock.comp (literalBlock.comp satBlock)

namespace ForallGadget

/-- The record latch in the gadget. -/
@[expose]
def recordOcc : Occurrence latch forallGadget := .compLeft _ (.compLeft _ (.pad [B] [B] .refl))

/-- The locked try in the gadget. -/
@[expose] def lockedOcc : Occurrence lockedTry forallGadget :=
  .compLeft _ (.compRight _ (.compRight _ (.pad [B, B, R] [] .refl)))

/-- The satisfied wire above. -/
@[expose] def satOut : forallGadget.Edge := .inl 0
/-- The try wire above. -/
@[expose] def tryIn : forallGadget.Edge := .inl 1
/-- The satisfied wire below. -/
@[expose] def satIn : forallGadget.Edge := forallGadget.bottom 0
/-- The try wire below. -/
@[expose] def tryOut : forallGadget.Edge := forallGadget.bottom 1
/-- The literal wire of `true`. -/
@[expose] def pos : forallGadget.Edge := forallGadget.bottom 2
/-- The literal wire of `false`. -/
@[expose] def neg : forallGadget.Edge := forallGadget.bottom 3
/-- The state edge of the variable latch: it points down when the value is `true`. -/
@[expose] def mem : forallGadget.Edge := lockedOcc.emb LockedTry.mem
/-- The state edge of the record latch: it points down, to `rec`, when the record is set. -/
@[expose] def recMem : forallGadget.Edge := recordOcc.emb Latch.mem

/-- The constraint graph of the gadget. -/
abbrev graph : ConstraintGraph (forallGadget.Vtx Gate.interp) forallGadget.Edge :=
  forallGadget.graph Gate.interp

variable {t : forallGadget.Edge → Bool}

/-- The assumption that the suffix is satisfied only while it is tried, as a clause: `satIn` is
inactive or `try` below is active. -/
@[expose] def admissible : Vertex forallGadget.Edge := .clause [⟨satIn, true⟩, ⟨tryOut, true⟩]

private theorem sat_admissible (h : t satIn = false → t tryOut = true) :
    ∀ v ∈ [admissible], v.Sat t := by
  simp only [List.mem_singleton, forall_eq]
  cases hs : t satIn
  · exact Vertex.sat_clause (List.mem_cons_of_mem _ List.mem_cons_self) (h hs)
  · exact Vertex.sat_clause List.mem_cons_self hs

/-- **Trying out needs trying in.** -/
theorem tryIn_of_tryOut (ht : graph.Legal t) (h : t tryOut = true) : t tryIn = true :=
  eq_of_refutes (l := [(tryOut, true)])
    (Refutation.conflict.refutes (n := 4) (by decide +kernel)) ht (by simp [h])

/-- **While trying out, `pos` agrees with `mem`.** -/
theorem mem_of_pos (ht : graph.Legal t) (h : t tryOut = true) (hp : t pos = true) :
    t mem = true :=
  eq_of_refutes (l := [(tryOut, true), (pos, true)])
    (Refutation.conflict.refutes (n := 4) (by decide +kernel)) ht (by simp [h, hp])

/-- **While trying out, `neg` agrees with `mem`.** -/
theorem mem_of_neg (ht : graph.Legal t) (h : t tryOut = true) (hn : t neg = true) :
    t mem = false :=
  eq_of_refutes (l := [(tryOut, true), (neg, true)])
    (Refutation.conflict.refutes (n := 4) (by decide +kernel)) ht (by simp [h, hn])

/-- **While trying out, `mem` cannot move.** -/
theorem not_step_mem (ht : graph.Legal t) (ht' : graph.Legal (reverse t mem)) :
    t tryOut = false :=
  LockedTry.not_step_mem (lockedOcc.legal ht) (lockedOcc.legal_reverse ht')

/-- The value of a universal quantifier in a larger diagram is frozen while trying out. -/
theorem mem_eq_of_step {a b : List Color} {D : Diagram Gate a b}
    (o : Occurrence forallGadget D) {s t : D.Edge → Bool}
    (h : (D.graph Gate.interp).Step s t) (htry : s (o.emb tryOut) = true) :
    s (o.emb mem) = t (o.emb mem) :=
  o.apply_eq_of_not_legal_reverse h fun hm =>
    Bool.noConfusion (htry.symm.trans (not_step_mem (o.legal h.legal_left) hm))

/-- **Satisfied above needs satisfied below.** -/
theorem satIn_of_satOut (ht : graph.Legal t) (h : t satOut = false) : t satIn = false :=
  eq_of_refutes (l := [(satOut, false)])
    (Refutation.conflict.refutes (n := 4) (by decide +kernel)) ht (by simp [h])

/-- **Satisfied above needs the value `true`**, if the suffix is satisfied only while tried. -/
theorem mem_of_satOut (ht : graph.Legal t) (hadm : t satIn = false → t tryOut = true)
    (h : t satOut = false) : t mem = true :=
  eq_of_refutes_assuming (l := [(satOut, false)]) [admissible]
    (Refutation.conflict.refutes (n := 6) (by decide +kernel)) ht (sat_admissible hadm)
    (by simp [h])

/-- **Satisfied above needs the record set**, if the suffix is satisfied only while tried. -/
theorem recMem_of_satOut (ht : graph.Legal t) (hadm : t satIn = false → t tryOut = true)
    (h : t satOut = false) : t recMem = true :=
  eq_of_refutes_assuming (l := [(satOut, false)]) [admissible]
    ((Refutation.split (forallGadget.num mem) .conflict .conflict).refutes (n := 3)
      (by decide +kernel)) ht (sat_admissible hadm) (by simp [h])

/-- **A set record needs trying in**, if the suffix is satisfied only while tried: the record
holds `rec` away from the try wire, or is open, which needs the suffix satisfied. -/
theorem tryIn_of_recMem (ht : graph.Legal t) (hadm : t satIn = false → t tryOut = true)
    (h : t recMem = true) : t tryIn = true :=
  eq_of_refutes_assuming (l := [(recMem, true)]) [admissible]
    (Refutation.conflict.refutes (n := 4) (by decide +kernel)) ht (sat_admissible hadm)
    (by simp [h])

/-- **The record moves only while the suffix is satisfied**: its lock opens only then. -/
theorem satIn_of_step_recMem (ht : graph.Legal t) (ht' : graph.Legal (reverse t recMem)) :
    t satIn = false :=
  eq_of_refutes_step (l := [])
    ((Refutation.split (forallGadget.num recMem) .conflict .conflict).refutes (n := 3)
      (by decide +kernel)) ht ht' (by simp)

/-- **The record moves only with the value `false`**, if the suffix is satisfied only while
tried: its lock opens only while `bar` is active. -/
theorem mem_of_step_recMem (ht : graph.Legal t) (ht' : graph.Legal (reverse t recMem))
    (hadm : t satIn = false → t tryOut = true) : t mem = false :=
  eq_of_refutes_step_assuming (l := []) [admissible]
    ((Refutation.split (forallGadget.num recMem) .conflict .conflict).refutes (n := 4)
      (by decide +kernel)) ht ht' (sat_admissible hadm) (by simp)

end ForallGadget

end Cslib.Complexity.NCL.QBF
