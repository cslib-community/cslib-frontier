/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.RedPaths.Basic

/-!
# The finite odd-phase shade comparison base

Every live port of the central eight-by-eight quarter square in the depth-four
substitution of tile zero connects to one of the four corners of its odd-phase cycle.
The finite proof shares common path prefixes and checks all local incidences together.

## Main results

* `odd_base_exists_boundedPath`: the required connection stays in a 16 by 16 square.

## References

Adapted from lean-wang revision `64268a3`, `Closed104.CanonicalOddShadeBase`
and the `oddNodes` witnesses in `Closed104.RedShadeGraphPathWitnesses`.
-/

public section
namespace Cslib.WangTile.Robinson

private abbrev grid := iterateRefine 4 (fun _ _ => (0 : Index))

private def targets : List Port := [
  ⟨6, 4, .south⟩, ⟨6, 4, .north⟩, ⟨11, 4, .south⟩, ⟨11, 4, .north⟩,
  ⟨5, 5, .east⟩, ⟨5, 5, .north⟩, ⟨6, 5, .west⟩, ⟨6, 5, .east⟩,
  ⟨6, 5, .south⟩, ⟨6, 5, .north⟩, ⟨7, 5, .west⟩, ⟨7, 5, .east⟩,
  ⟨8, 5, .west⟩, ⟨8, 5, .east⟩, ⟨9, 5, .west⟩, ⟨9, 5, .east⟩,
  ⟨10, 5, .west⟩, ⟨10, 5, .east⟩, ⟨11, 5, .west⟩, ⟨11, 5, .east⟩,
  ⟨11, 5, .south⟩, ⟨11, 5, .north⟩, ⟨4, 6, .west⟩, ⟨4, 6, .east⟩,
  ⟨5, 6, .west⟩, ⟨5, 6, .east⟩, ⟨5, 6, .south⟩, ⟨5, 6, .north⟩,
  ⟨6, 6, .west⟩, ⟨6, 6, .south⟩, ⟨11, 6, .east⟩, ⟨11, 6, .south⟩,
  ⟨5, 7, .south⟩, ⟨5, 7, .north⟩, ⟨5, 8, .south⟩, ⟨5, 8, .north⟩,
  ⟨5, 9, .south⟩, ⟨5, 9, .north⟩, ⟨9, 9, .east⟩, ⟨9, 9, .north⟩,
  ⟨10, 9, .west⟩, ⟨10, 9, .east⟩, ⟨11, 9, .west⟩, ⟨11, 9, .east⟩,
  ⟨5, 10, .south⟩, ⟨5, 10, .north⟩, ⟨9, 10, .south⟩, ⟨9, 10, .north⟩,
  ⟨4, 11, .west⟩, ⟨4, 11, .east⟩, ⟨5, 11, .west⟩, ⟨5, 11, .east⟩,
  ⟨5, 11, .south⟩, ⟨5, 11, .north⟩, ⟨6, 11, .west⟩, ⟨6, 11, .north⟩,
  ⟨9, 11, .south⟩, ⟨9, 11, .north⟩, ⟨11, 11, .east⟩, ⟨11, 11, .north⟩
]

private def checks : List Bool := [
  hasHorizontal (componentAt grid 6 5) (quadrantAt 6 5) && hasVertical (componentAt grid 6 5)
    (quadrantAt 6 5),
  hasVertical (componentAt grid 6 4) (quadrantAt 6 4),
  hasHorizontal (componentAt grid 11 5) (quadrantAt 11 5),
  hasHorizontal (componentAt grid 11 5) (quadrantAt 11 5) && hasVertical (componentAt grid 11 5)
    (quadrantAt 11 5),
  hasVertical (componentAt grid 11 4) (quadrantAt 11 4),
  cornerEast (componentAt grid 5 5) (quadrantAt 5 5) && cornerNorth (componentAt grid 5 5)
    (quadrantAt 5 5),
  hasHorizontal (componentAt grid 6 5) (quadrantAt 6 5),
  hasVertical (componentAt grid 6 5) (quadrantAt 6 5),
  hasHorizontal (componentAt grid 7 5) (quadrantAt 7 5),
  hasHorizontal (componentAt grid 8 5) (quadrantAt 8 5),
  hasHorizontal (componentAt grid 10 5) (quadrantAt 10 5),
  hasHorizontal (componentAt grid 9 5) (quadrantAt 9 5),
  hasVertical (componentAt grid 11 5) (quadrantAt 11 5),
  hasHorizontal (componentAt grid 5 6) (quadrantAt 5 6) && hasVertical (componentAt grid 5 6)
    (quadrantAt 5 6),
  hasHorizontal (componentAt grid 4 6) (quadrantAt 4 6),
  hasHorizontal (componentAt grid 5 6) (quadrantAt 5 6),
  hasVertical (componentAt grid 5 6) (quadrantAt 5 6),
  cornerWest (componentAt grid 6 6) (quadrantAt 6 6) && cornerSouth (componentAt grid 6 6)
    (quadrantAt 6 6),
  cornerWest (componentAt grid 12 5) (quadrantAt 12 5) && cornerNorth (componentAt grid 12 5)
    (quadrantAt 12 5),
  hasHorizontal (componentAt grid 12 6) (quadrantAt 12 6) && hasVertical (componentAt grid 12 6)
    (quadrantAt 12 6),
  cornerEast (componentAt grid 11 6) (quadrantAt 11 6) && cornerSouth (componentAt grid 11 6)
    (quadrantAt 11 6),
  hasVertical (componentAt grid 5 7) (quadrantAt 5 7),
  hasVertical (componentAt grid 5 8) (quadrantAt 5 8),
  cornerEast (componentAt grid 5 12) (quadrantAt 5 12) && cornerSouth (componentAt grid 5 12)
    (quadrantAt 5 12),
  hasVertical (componentAt grid 5 11) (quadrantAt 5 11),
  hasVertical (componentAt grid 5 10) (quadrantAt 5 10),
  hasVertical (componentAt grid 5 9) (quadrantAt 5 9),
  cornerWest (componentAt grid 12 12) (quadrantAt 12 12) && cornerSouth (componentAt grid 12 12)
    (quadrantAt 12 12),
  hasVertical (componentAt grid 12 11) (quadrantAt 12 11),
  hasVertical (componentAt grid 12 10) (quadrantAt 12 10),
  hasVertical (componentAt grid 12 9) (quadrantAt 12 9),
  hasHorizontal (componentAt grid 12 9) (quadrantAt 12 9) && hasVertical (componentAt grid 12 9)
    (quadrantAt 12 9),
  hasHorizontal (componentAt grid 11 9) (quadrantAt 11 9),
  hasHorizontal (componentAt grid 10 9) (quadrantAt 10 9),
  hasHorizontal (componentAt grid 11 12) (quadrantAt 11 12),
  hasHorizontal (componentAt grid 10 12) (quadrantAt 10 12),
  hasHorizontal (componentAt grid 9 12) (quadrantAt 9 12),
  hasHorizontal (componentAt grid 9 12) (quadrantAt 9 12) && hasVertical (componentAt grid 9 12)
    (quadrantAt 9 12),
  hasVertical (componentAt grid 9 11) (quadrantAt 9 11),
  hasVertical (componentAt grid 9 10) (quadrantAt 9 10),
  hasHorizontal (componentAt grid 5 11) (quadrantAt 5 11) && hasVertical (componentAt grid 5 11)
    (quadrantAt 5 11),
  hasHorizontal (componentAt grid 4 11) (quadrantAt 4 11),
  hasHorizontal (componentAt grid 6 12) (quadrantAt 6 12) && hasVertical (componentAt grid 6 12)
    (quadrantAt 6 12),
  cornerWest (componentAt grid 6 11) (quadrantAt 6 11) && cornerNorth (componentAt grid 6 11)
    (quadrantAt 6 11),
  hasHorizontal (componentAt grid 12 11) (quadrantAt 12 11) && hasVertical (componentAt grid 12 11)
    (quadrantAt 12 11),
  hasHorizontal (componentAt grid 11 12) (quadrantAt 11 12) && hasVertical (componentAt grid 11 12)
    (quadrantAt 11 12)
]

private theorem checks_valid : ∀ i : Fin 46, checks.getD i false = true := by
  decide +kernel

private theorem covers : ∀ x y : Fin 8, ∀ s : Side,
    portPresent grid ⟨4 + x.val, 4 + y.val, s⟩ = true →
      (⟨4 + x.val, 4 + y.val, s⟩ : Port) ∈ targets := by
  decide +kernel

private theorem paths {target : Port} (mem : target ∈ targets) :
    ∃ source parity,
      source ∈ ([⟨5, 5, .east⟩, ⟨12, 5, .west⟩, ⟨12, 12, .west⟩, ⟨5, 12, .east⟩] : List Port) ∧
      BoundedPath grid 16 16 source target parity := by
  let inst (p : Port) : Decidable (PortInBounds p 16 16) :=
    inferInstanceAs (Decidable (_ ∧ _))
  have c0 := Bool.and_eq_true_iff.mp
    (show hasHorizontal (componentAt grid 6 5) (quadrantAt 6 5) && hasVertical (componentAt grid 6
      5) (quadrantAt 6 5) = true from checks_valid ⟨0, by decide⟩)
  have c3 := Bool.and_eq_true_iff.mp
    (show hasHorizontal (componentAt grid 11 5) (quadrantAt 11 5) && hasVertical (componentAt grid
      11 5) (quadrantAt 11 5) = true from checks_valid ⟨3, by decide⟩)
  have c5 := Bool.and_eq_true_iff.mp
    (show cornerEast (componentAt grid 5 5) (quadrantAt 5 5) && cornerNorth (componentAt grid 5 5)
      (quadrantAt 5 5) = true from checks_valid ⟨5, by decide⟩)
  have c13 := Bool.and_eq_true_iff.mp
    (show hasHorizontal (componentAt grid 5 6) (quadrantAt 5 6) && hasVertical (componentAt grid 5
      6) (quadrantAt 5 6) = true from checks_valid ⟨13, by decide⟩)
  have c17 := Bool.and_eq_true_iff.mp
    (show cornerWest (componentAt grid 6 6) (quadrantAt 6 6) && cornerSouth (componentAt grid 6 6)
      (quadrantAt 6 6) = true from checks_valid ⟨17, by decide⟩)
  have c18 := Bool.and_eq_true_iff.mp
    (show cornerWest (componentAt grid 12 5) (quadrantAt 12 5) && cornerNorth (componentAt grid 12
      5) (quadrantAt 12 5) = true from checks_valid ⟨18, by decide⟩)
  have c19 := Bool.and_eq_true_iff.mp
    (show hasHorizontal (componentAt grid 12 6) (quadrantAt 12 6) && hasVertical (componentAt grid
      12 6) (quadrantAt 12 6) = true from checks_valid ⟨19, by decide⟩)
  have c20 := Bool.and_eq_true_iff.mp
    (show cornerEast (componentAt grid 11 6) (quadrantAt 11 6) && cornerSouth (componentAt grid 11
      6) (quadrantAt 11 6) = true from checks_valid ⟨20, by decide⟩)
  have c23 := Bool.and_eq_true_iff.mp
    (show cornerEast (componentAt grid 5 12) (quadrantAt 5 12) && cornerSouth (componentAt grid 5
      12) (quadrantAt 5 12) = true from checks_valid ⟨23, by decide⟩)
  have c27 := Bool.and_eq_true_iff.mp
    (show cornerWest (componentAt grid 12 12) (quadrantAt 12 12) && cornerSouth (componentAt grid 12
      12) (quadrantAt 12 12) = true from checks_valid ⟨27, by decide⟩)
  have c31 := Bool.and_eq_true_iff.mp
    (show hasHorizontal (componentAt grid 12 9) (quadrantAt 12 9) && hasVertical (componentAt grid
      12 9) (quadrantAt 12 9) = true from checks_valid ⟨31, by decide⟩)
  have c37 := Bool.and_eq_true_iff.mp
    (show hasHorizontal (componentAt grid 9 12) (quadrantAt 9 12) && hasVertical (componentAt grid 9
      12) (quadrantAt 9 12) = true from checks_valid ⟨37, by decide⟩)
  have c40 := Bool.and_eq_true_iff.mp
    (show hasHorizontal (componentAt grid 5 11) (quadrantAt 5 11) && hasVertical (componentAt grid 5
      11) (quadrantAt 5 11) = true from checks_valid ⟨40, by decide⟩)
  have c42 := Bool.and_eq_true_iff.mp
    (show hasHorizontal (componentAt grid 6 12) (quadrantAt 6 12) && hasVertical (componentAt grid 6
      12) (quadrantAt 6 12) = true from checks_valid ⟨42, by decide⟩)
  have c43 := Bool.and_eq_true_iff.mp
    (show cornerWest (componentAt grid 6 11) (quadrantAt 6 11) && cornerNorth (componentAt grid 6
      11) (quadrantAt 6 11) = true from checks_valid ⟨43, by decide⟩)
  have c44 := Bool.and_eq_true_iff.mp
    (show hasHorizontal (componentAt grid 12 11) (quadrantAt 12 11) && hasVertical (componentAt grid
      12 11) (quadrantAt 12 11) = true from checks_valid ⟨44, by decide⟩)
  have c45 := Bool.and_eq_true_iff.mp
    (show hasHorizontal (componentAt grid 11 12) (quadrantAt 11 12) && hasVertical (componentAt grid
      11 12) (quadrantAt 11 12) = true from checks_valid ⟨45, by decide⟩)
  have h0 : BoundedPath grid 16 16 ⟨5, 5, .east⟩ ⟨5, 5, .east⟩ false := .refl _ (by decide)
  have h1 := h0.trans
    (.ofLink (Link.horizontalMatch 5 5) (by decide) (by decide))
  have h2 := h1.trans
    (.ofLink (Link.crossing 6 5 c0.1 c0.2) (by decide) (by decide))
  have h3 := h2.trans
    (.ofLink (Link.symm (Link.verticalMatch 6 4)) (by decide) (by decide))
  have h4 := h3.trans
    (.ofLink (Link.symm (Link.vertical 6 4 (checks_valid ⟨1, by decide⟩))) (by decide) (by decide))
  have h5 : BoundedPath grid 16 16 ⟨12, 5, .west⟩ ⟨12, 5, .west⟩ false := .refl _ (by decide)
  have h6 := h5.trans
    (.ofLink (Link.symm (Link.horizontalMatch 11 5)) (by decide) (by decide))
  have h7 := h6.trans
    (.ofLink (Link.symm (Link.horizontal 11 5 (checks_valid ⟨2, by decide⟩))) (by decide) (by
      decide))
  have h8 := h7.trans
    (.ofLink (Link.crossing 11 5 c3.1 c3.2) (by decide) (by decide))
  have h9 := h8.trans
    (.ofLink (Link.symm (Link.verticalMatch 11 4)) (by decide) (by decide))
  have h10 := h9.trans
    (.ofLink (Link.symm (Link.vertical 11 4 (checks_valid ⟨4, by decide⟩))) (by decide) (by decide))
  have h11 := h0.trans
    (.ofLink (Link.eastNorth 5 5 c5.1 c5.2) (by decide) (by decide))
  have h12 := h1.trans
    (.ofLink (Link.horizontal 6 5 (checks_valid ⟨6, by decide⟩)) (by decide) (by decide))
  have h13 := h2.trans
    (.ofLink (Link.vertical 6 5 (checks_valid ⟨7, by decide⟩)) (by decide) (by decide))
  have h14 := h12.trans
    (.ofLink (Link.horizontalMatch 6 5) (by decide) (by decide))
  have h15 := h14.trans
    (.ofLink (Link.horizontal 7 5 (checks_valid ⟨8, by decide⟩)) (by decide) (by decide))
  have h16 := h15.trans
    (.ofLink (Link.horizontalMatch 7 5) (by decide) (by decide))
  have h17 := h16.trans
    (.ofLink (Link.horizontal 8 5 (checks_valid ⟨9, by decide⟩)) (by decide) (by decide))
  have h18 := h7.trans
    (.ofLink (Link.symm (Link.horizontalMatch 10 5)) (by decide) (by decide))
  have h19 := h18.trans
    (.ofLink (Link.symm (Link.horizontal 10 5 (checks_valid ⟨10, by decide⟩))) (by decide) (by
      decide))
  have h20 := h19.trans
    (.ofLink (Link.symm (Link.horizontalMatch 9 5)) (by decide) (by decide))
  have h21 := h20.trans
    (.ofLink (Link.symm (Link.horizontal 9 5 (checks_valid ⟨11, by decide⟩))) (by decide) (by
      decide))
  have h22 := h8.trans
    (.ofLink (Link.vertical 11 5 (checks_valid ⟨12, by decide⟩)) (by decide) (by decide))
  have h23 := h11.trans
    (.ofLink (Link.verticalMatch 5 5) (by decide) (by decide))
  have h24 := h23.trans
    (.ofLink (Link.symm (Link.crossing 5 6 c13.1 c13.2)) (by decide) (by decide))
  have h25 := h24.trans
    (.ofLink (Link.symm (Link.horizontalMatch 4 6)) (by decide) (by decide))
  have h26 := h25.trans
    (.ofLink (Link.symm (Link.horizontal 4 6 (checks_valid ⟨14, by decide⟩))) (by decide) (by
      decide))
  have h27 := h24.trans
    (.ofLink (Link.horizontal 5 6 (checks_valid ⟨15, by decide⟩)) (by decide) (by decide))
  have h28 := h23.trans
    (.ofLink (Link.vertical 5 6 (checks_valid ⟨16, by decide⟩)) (by decide) (by decide))
  have h29 := h13.trans
    (.ofLink (Link.verticalMatch 6 5) (by decide) (by decide))
  have h30 := h29.trans
    (.ofLink (Link.symm (Link.westSouth 6 6 c17.1 c17.2)) (by decide) (by decide))
  have h31 := h5.trans
    (.ofLink (Link.westNorth 12 5 c18.1 c18.2) (by decide) (by decide))
  have h32 := h31.trans
    (.ofLink (Link.verticalMatch 12 5) (by decide) (by decide))
  have h33 := h32.trans
    (.ofLink (Link.symm (Link.crossing 12 6 c19.1 c19.2)) (by decide) (by decide))
  have h34 := h33.trans
    (.ofLink (Link.symm (Link.horizontalMatch 11 6)) (by decide) (by decide))
  have h35 := h34.trans
    (.ofLink (Link.eastSouth 11 6 c20.1 c20.2) (by decide) (by decide))
  have h36 := h28.trans
    (.ofLink (Link.verticalMatch 5 6) (by decide) (by decide))
  have h37 := h36.trans
    (.ofLink (Link.vertical 5 7 (checks_valid ⟨21, by decide⟩)) (by decide) (by decide))
  have h38 := h37.trans
    (.ofLink (Link.verticalMatch 5 7) (by decide) (by decide))
  have h39 := h38.trans
    (.ofLink (Link.vertical 5 8 (checks_valid ⟨22, by decide⟩)) (by decide) (by decide))
  have h40 : BoundedPath grid 16 16 ⟨5, 12, .east⟩ ⟨5, 12, .east⟩ false := .refl _ (by decide)
  have h41 := h40.trans
    (.ofLink (Link.eastSouth 5 12 c23.1 c23.2) (by decide) (by decide))
  have h42 := h41.trans
    (.ofLink (Link.symm (Link.verticalMatch 5 11)) (by decide) (by decide))
  have h43 := h42.trans
    (.ofLink (Link.symm (Link.vertical 5 11 (checks_valid ⟨24, by decide⟩))) (by decide) (by
      decide))
  have h44 := h43.trans
    (.ofLink (Link.symm (Link.verticalMatch 5 10)) (by decide) (by decide))
  have h45 := h44.trans
    (.ofLink (Link.symm (Link.vertical 5 10 (checks_valid ⟨25, by decide⟩))) (by decide) (by
      decide))
  have h46 := h45.trans
    (.ofLink (Link.symm (Link.verticalMatch 5 9)) (by decide) (by decide))
  have h47 := h46.trans
    (.ofLink (Link.symm (Link.vertical 5 9 (checks_valid ⟨26, by decide⟩))) (by decide) (by decide))
  have h48 : BoundedPath grid 16 16 ⟨12, 12, .west⟩ ⟨12, 12, .west⟩ false := .refl _ (by decide)
  have h49 := h48.trans
    (.ofLink (Link.westSouth 12 12 c27.1 c27.2) (by decide) (by decide))
  have h50 := h49.trans
    (.ofLink (Link.symm (Link.verticalMatch 12 11)) (by decide) (by decide))
  have h51 := h50.trans
    (.ofLink (Link.symm (Link.vertical 12 11 (checks_valid ⟨28, by decide⟩))) (by decide) (by
      decide))
  have h52 := h51.trans
    (.ofLink (Link.symm (Link.verticalMatch 12 10)) (by decide) (by decide))
  have h53 := h52.trans
    (.ofLink (Link.symm (Link.vertical 12 10 (checks_valid ⟨29, by decide⟩))) (by decide) (by
      decide))
  have h54 := h53.trans
    (.ofLink (Link.symm (Link.verticalMatch 12 9)) (by decide) (by decide))
  have h55 := h54.trans
    (.ofLink (Link.symm (Link.vertical 12 9 (checks_valid ⟨30, by decide⟩))) (by decide) (by
      decide))
  have h56 := h55.trans
    (.ofLink (Link.symm (Link.crossing 12 9 c31.1 c31.2)) (by decide) (by decide))
  have h57 := h56.trans
    (.ofLink (Link.symm (Link.horizontalMatch 11 9)) (by decide) (by decide))
  have h58 := h57.trans
    (.ofLink (Link.symm (Link.horizontal 11 9 (checks_valid ⟨32, by decide⟩))) (by decide) (by
      decide))
  have h59 := h58.trans
    (.ofLink (Link.symm (Link.horizontalMatch 10 9)) (by decide) (by decide))
  have h60 := h59.trans
    (.ofLink (Link.symm (Link.horizontal 10 9 (checks_valid ⟨33, by decide⟩))) (by decide) (by
      decide))
  have h61 := h60.trans
    (.ofLink (Link.symm (Link.horizontalMatch 9 9)) (by decide) (by decide))
  have h62 := h48.trans
    (.ofLink (Link.symm (Link.horizontalMatch 11 12)) (by decide) (by decide))
  have h63 := h62.trans
    (.ofLink (Link.symm (Link.horizontal 11 12 (checks_valid ⟨34, by decide⟩))) (by decide) (by
      decide))
  have h64 := h63.trans
    (.ofLink (Link.symm (Link.horizontalMatch 10 12)) (by decide) (by decide))
  have h65 := h64.trans
    (.ofLink (Link.symm (Link.horizontal 10 12 (checks_valid ⟨35, by decide⟩))) (by decide) (by
      decide))
  have h66 := h65.trans
    (.ofLink (Link.symm (Link.horizontalMatch 9 12)) (by decide) (by decide))
  have h67 := h66.trans
    (.ofLink (Link.symm (Link.horizontal 9 12 (checks_valid ⟨36, by decide⟩))) (by decide) (by
      decide))
  have h68 := h67.trans
    (.ofLink (Link.crossing 9 12 c37.1 c37.2) (by decide) (by decide))
  have h69 := h68.trans
    (.ofLink (Link.symm (Link.verticalMatch 9 11)) (by decide) (by decide))
  have h70 := h69.trans
    (.ofLink (Link.symm (Link.vertical 9 11 (checks_valid ⟨38, by decide⟩))) (by decide) (by
      decide))
  have h71 := h70.trans
    (.ofLink (Link.symm (Link.verticalMatch 9 10)) (by decide) (by decide))
  have h72 := h71.trans
    (.ofLink (Link.symm (Link.vertical 9 10 (checks_valid ⟨39, by decide⟩))) (by decide) (by
      decide))
  have h73 := h72.trans
    (.ofLink (Link.symm (Link.verticalMatch 9 9)) (by decide) (by decide))
  have h74 := h43.trans
    (.ofLink (Link.symm (Link.crossing 5 11 c40.1 c40.2)) (by decide) (by decide))
  have h75 := h74.trans
    (.ofLink (Link.symm (Link.horizontalMatch 4 11)) (by decide) (by decide))
  have h76 := h75.trans
    (.ofLink (Link.symm (Link.horizontal 4 11 (checks_valid ⟨41, by decide⟩))) (by decide) (by
      decide))
  have h77 := h40.trans
    (.ofLink (Link.horizontalMatch 5 12) (by decide) (by decide))
  have h78 := h77.trans
    (.ofLink (Link.crossing 6 12 c42.1 c42.2) (by decide) (by decide))
  have h79 := h78.trans
    (.ofLink (Link.symm (Link.verticalMatch 6 11)) (by decide) (by decide))
  have h80 := h79.trans
    (.ofLink (Link.symm (Link.westNorth 6 11 c43.1 c43.2)) (by decide) (by decide))
  have h81 := h80.trans
    (.ofLink (Link.symm (Link.horizontalMatch 5 11)) (by decide) (by decide))
  have h82 := h51.trans
    (.ofLink (Link.symm (Link.crossing 12 11 c44.1 c44.2)) (by decide) (by decide))
  have h83 := h82.trans
    (.ofLink (Link.symm (Link.horizontalMatch 11 11)) (by decide) (by decide))
  have h84 := h63.trans
    (.ofLink (Link.crossing 11 12 c45.1 c45.2) (by decide) (by decide))
  have h85 := h84.trans
    (.ofLink (Link.symm (Link.verticalMatch 11 11)) (by decide) (by decide))
  simp only [targets, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨5, 5, .east⟩, true, by decide, h4⟩
  · exact ⟨⟨5, 5, .east⟩, true, by decide, h3⟩
  · exact ⟨⟨12, 5, .west⟩, true, by decide, h10⟩
  · exact ⟨⟨12, 5, .west⟩, true, by decide, h9⟩
  · exact ⟨⟨5, 5, .east⟩, false, by decide, h0⟩
  · exact ⟨⟨5, 5, .east⟩, false, by decide, h11⟩
  · exact ⟨⟨5, 5, .east⟩, false, by decide, h1⟩
  · exact ⟨⟨5, 5, .east⟩, false, by decide, h12⟩
  · exact ⟨⟨5, 5, .east⟩, true, by decide, h2⟩
  · exact ⟨⟨5, 5, .east⟩, true, by decide, h13⟩
  · exact ⟨⟨5, 5, .east⟩, false, by decide, h14⟩
  · exact ⟨⟨5, 5, .east⟩, false, by decide, h15⟩
  · exact ⟨⟨5, 5, .east⟩, false, by decide, h16⟩
  · exact ⟨⟨5, 5, .east⟩, false, by decide, h17⟩
  · exact ⟨⟨12, 5, .west⟩, false, by decide, h21⟩
  · exact ⟨⟨12, 5, .west⟩, false, by decide, h20⟩
  · exact ⟨⟨12, 5, .west⟩, false, by decide, h19⟩
  · exact ⟨⟨12, 5, .west⟩, false, by decide, h18⟩
  · exact ⟨⟨12, 5, .west⟩, false, by decide, h7⟩
  · exact ⟨⟨12, 5, .west⟩, false, by decide, h6⟩
  · exact ⟨⟨12, 5, .west⟩, true, by decide, h8⟩
  · exact ⟨⟨12, 5, .west⟩, true, by decide, h22⟩
  · exact ⟨⟨5, 5, .east⟩, true, by decide, h26⟩
  · exact ⟨⟨5, 5, .east⟩, true, by decide, h25⟩
  · exact ⟨⟨5, 5, .east⟩, true, by decide, h24⟩
  · exact ⟨⟨5, 5, .east⟩, true, by decide, h27⟩
  · exact ⟨⟨5, 5, .east⟩, false, by decide, h23⟩
  · exact ⟨⟨5, 5, .east⟩, false, by decide, h28⟩
  · exact ⟨⟨5, 5, .east⟩, true, by decide, h30⟩
  · exact ⟨⟨5, 5, .east⟩, true, by decide, h29⟩
  · exact ⟨⟨12, 5, .west⟩, true, by decide, h34⟩
  · exact ⟨⟨12, 5, .west⟩, true, by decide, h35⟩
  · exact ⟨⟨5, 5, .east⟩, false, by decide, h36⟩
  · exact ⟨⟨5, 5, .east⟩, false, by decide, h37⟩
  · exact ⟨⟨5, 5, .east⟩, false, by decide, h38⟩
  · exact ⟨⟨5, 5, .east⟩, false, by decide, h39⟩
  · exact ⟨⟨5, 12, .east⟩, false, by decide, h47⟩
  · exact ⟨⟨5, 12, .east⟩, false, by decide, h46⟩
  · exact ⟨⟨12, 12, .west⟩, true, by decide, h61⟩
  · exact ⟨⟨12, 12, .west⟩, true, by decide, h73⟩
  · exact ⟨⟨12, 12, .west⟩, true, by decide, h60⟩
  · exact ⟨⟨12, 12, .west⟩, true, by decide, h59⟩
  · exact ⟨⟨12, 12, .west⟩, true, by decide, h58⟩
  · exact ⟨⟨12, 12, .west⟩, true, by decide, h57⟩
  · exact ⟨⟨5, 12, .east⟩, false, by decide, h45⟩
  · exact ⟨⟨5, 12, .east⟩, false, by decide, h44⟩
  · exact ⟨⟨12, 12, .west⟩, true, by decide, h72⟩
  · exact ⟨⟨12, 12, .west⟩, true, by decide, h71⟩
  · exact ⟨⟨5, 12, .east⟩, true, by decide, h76⟩
  · exact ⟨⟨5, 12, .east⟩, true, by decide, h75⟩
  · exact ⟨⟨5, 12, .east⟩, true, by decide, h74⟩
  · exact ⟨⟨5, 12, .east⟩, true, by decide, h81⟩
  · exact ⟨⟨5, 12, .east⟩, false, by decide, h43⟩
  · exact ⟨⟨5, 12, .east⟩, false, by decide, h42⟩
  · exact ⟨⟨5, 12, .east⟩, true, by decide, h80⟩
  · exact ⟨⟨5, 12, .east⟩, true, by decide, h79⟩
  · exact ⟨⟨12, 12, .west⟩, true, by decide, h70⟩
  · exact ⟨⟨12, 12, .west⟩, true, by decide, h69⟩
  · exact ⟨⟨12, 12, .west⟩, true, by decide, h83⟩
  · exact ⟨⟨12, 12, .west⟩, true, by decide, h85⟩

/-- Every live port in the odd root's central square has a bounded path from a root corner.
This is the finite base case of the odd-phase shade comparison, after lean-wang's
`CanonicalOddShadeBase.exists_boundedPath` at revision `64268a3`. -/
theorem odd_base_exists_boundedPath {target : Port}
    (west : 4 ≤ target.x) (east : target.x < 12)
    (south : 4 ≤ target.y) (north : target.y < 12)
    (present : portPresent (iterateRefine 4 (fun _ _ => (0 : Index))) target = true) :
    ∃ source parity,
      source ∈ ([⟨5, 5, .east⟩, ⟨12, 5, .west⟩, ⟨12, 12, .west⟩, ⟨5, 12, .east⟩] : List Port) ∧
      BoundedPath (iterateRefine 4 (fun _ _ => (0 : Index))) 16 16 source target parity := by
  have target_eq : (⟨4 + (target.x - 4), 4 + (target.y - 4), target.side⟩ : Port) = target := by
    cases target
    dsimp at *
    simp only [Port.mk.injEq]
    exact ⟨by omega, by omega, trivial⟩
  have h := covers ⟨target.x - 4, by omega⟩ ⟨target.y - 4, by omega⟩ target.side
  rw [target_eq] at h
  exact paths (h present)

end Cslib.WangTile.Robinson
