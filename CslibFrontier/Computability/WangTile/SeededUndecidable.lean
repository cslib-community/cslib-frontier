/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.OfTM0
public import Mathlib.Computability.Halting
import CslibFrontier.Computability.Machines.Turing.SingleTape.TM0Universal
import Mathlib.Computability.Reduce

/-!
# Undecidability of seeded-quadrant Wang tiling

There is no algorithm deciding whether a finite palette tiles the natural-number quadrant with
a prescribed southwest tile. This is Wang's origin-constrained problem for the first quadrant
as stated in [Robinson1971, §1, p. 178]. Robinson's §4, pp. 190–192 proves the plane variant
with a prescribed tile used at least once, and remarks on p. 192 that the quadrant argument is
similar, crediting Wang.

The proof here is after that tableau argument. The reduction fixes a universal finite-state
`TM0` machine and varies the input forced along the bottom row, instead of varying the machine
on a blank tape. Tiles record two-row, three-cell windows rather than the source's signal tiles;
`TM0` writes and moves in separate steps, and its two-sided tape is explicitly folded onto a
one-sided tape. The resulting seeded quadrant is tileable precisely when the encoded partial
recursive program does not halt on zero.

This is the **seeded-quadrant** problem. The separate `WangTile.Undecidable` module derives
undecidability of the unseeded integer-plane domino problem by concrete seed removal.

## Main definitions

* `Cslib.WangTile.seededReduction`: a primitive-recursive map from codes to seeded palettes.

## Main results

* `Cslib.WangTile.tilesQuadrant_seededReduction_iff`: exact correspondence with nonhalting.
* `Cslib.WangTile.not_computablePred_tilesQuadrant`: seeded-quadrant tiling is undecidable.

## References

* [R. M. Robinson, *Undecidability and nonperiodicity for tilings of the plane*][Robinson1971]

The prior formalization is [lean-wang, revision 64268a3, Robinson reduction](https://github.com/edemaine/lean-wang/blob/64268a3/LeanWang/Robinson/Reduction.lean).
Here the machine and input coding reuse `Turing.TM0.Universal`.
-/

public section

namespace Cslib.WangTile

open Turing.TM0.Universal

open Classical in
/-- Encode a code's run on zero as a seeded-quadrant tiling instance of the fixed universal
machine. Tiles are coded in field order, and an instance as `(tiles, seed)`. -/
noncomputable def seededReduction (c : Nat.Partrec.Code) : SeededInstance :=
  OfTM0.seededInstance M₀' (input (Encodable.encode c))

/-- The map from partial recursive codes to seeded-quadrant instances is primitive recursive. -/
theorem primrec_seededReduction : Primrec seededReduction := by
  classical
  exact (OfTM0.primrec_seededInstance M₀').comp (primrec_input.comp Primrec.encode)

/-- The universal computation tiles a seeded quadrant exactly when the code does not halt. -/
theorem tilesQuadrant_seededReduction_iff (c : Nat.Partrec.Code) :
    TilesQuadrant (seededReduction c) ↔ ¬ (c.eval 0).Dom := by
  classical
  rw [seededReduction, OfTM0.tilesQuadrant_seededInstance_iff, eval_dom_iff,
    Denumerable.ofNat_encode]

/-- **Seeded-quadrant tiling is undecidable**: Wang's origin-constrained first-quadrant problem
as stated in [Robinson1971, §1, p. 178]. Robinson's §4, pp. 190–192 gives the full proof for
the plane with a prescribed tile used at least once; p. 192 remarks that the quadrant case is
similar and credits Wang. The proof here is after that tableau argument: it fixes a universal
machine and varies the bottom-row input instead of the machine on a blank tape, uses two-row,
three-cell window tiles rather than signal tiles, separates `TM0` write and move steps, and folds
the two-sided tape onto a one-sided tape. This does not assert undecidability of the unseeded
plane domino problem. -/
theorem not_computablePred_tilesQuadrant : ¬ ComputablePred TilesQuadrant := by
  intro h
  have hn : ComputablePred (fun c : Nat.Partrec.Code => ¬ (c.eval 0).Dom) :=
    ComputablePred.computable_of_manyOneReducible
      ⟨seededReduction, primrec_seededReduction.to_comp,
        fun c => (tilesQuadrant_seededReduction_iff c).symm⟩ h
  exact ComputablePred.halting_problem 0 (hn.not.of_eq fun _ => not_not)

end Cslib.WangTile
