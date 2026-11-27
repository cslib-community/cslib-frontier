/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.Tiles

/-!
# Local recognition of corrected Robinson supertiles

A matching four-by-four neighborhood whose central southwest tile has thin phase `a`
has exactly one substitution parent. The one-cell boundary is essential: an isolated
matching two-by-two block need not have a parent.

## Main results

* `existsUnique_centerParent`: the central block of a `Neighborhood` has a unique parent.

## References

The four-by-four argument is the recognition step in [JeandelVanier2020], Proposition 8
(p. 24 of the authors' manuscript). We use the corrected 104-tile alphabet of the prior
formalization [lean-wang](https://github.com/edemaine/lean-wang/tree/64268a3),
the `Robinson.Closed104.LocalRecognizability` and `FiniteRecognizability` modules.
A kernel check enumerates every matching phase-`a` central two-by-two block; each one either is
the child block of an explicit parent or has no matching south or west neighbour pair.
-/

public section
namespace Cslib.WangTile.Robinson

/-- A matching four-by-four index patch with its central block in substitution phase. -/
structure Neighborhood where
  /-- Tile index at each position, increasing east and north. -/
  cell : Fin 4 → Fin 4 → Index
  /-- Every horizontal shared edge matches. -/
  horizontal : ∀ (i : Fin 3) (j : Fin 4),
    (tile (components (cell i.castSucc j))).right =
      (tile (components (cell i.succ j))).left
  /-- Every vertical shared edge matches. -/
  vertical : ∀ (i : Fin 4) (j : Fin 3),
    (tile (components (cell i j.castSucc))).top =
      (tile (components (cell i j.succ))).bottom
  /-- Thin phase at the southwest position of the central block. -/
  phase : (components (cell 1 1)).thin = .a

/-- Tiles indexed by their west edge colour. An edge colour is `thin + 4 * thick + 16 * black`
(`tile`), and the tables below split at `c < 16`, the black digit, only to keep each kernel `match`
small. Soundness uses only that each tile lies in its own buckets (`edgeCert`), so a bucket may
list extra tiles. -/
private def leftTiles (c : ℕ) : List Index :=
  if c < 16 then
    match c with
    | 1 => [10, 19, 26]
    | 2 => [34, 43, 50, 85, 91, 97, 103]
    | 3 => [61, 67, 73, 79]
    | 5 => [17, 22, 30]
    | 6 => [41, 46, 54, 82, 88, 94, 100]
    | 7 => [58, 64, 70, 76]
    | 9 => [16, 20, 28]
    | 10 => [40, 44, 52, 80, 81, 86, 87, 92, 93, 98, 99]
    | 11 => [56, 57, 62, 63, 68, 69, 74, 75]
    | 13 => [8, 18, 24]
    | 14 => [32, 42, 48, 83, 84, 89, 90, 95, 96, 101, 102]
    | 15 => [59, 60, 65, 66, 71, 72, 77, 78]
    | _ => []
  else
    match c with
    | 16 => [7]
    | 17 => [11, 15, 27]
    | 18 => [3, 35, 39, 51]
    | 20 => [5]
    | 21 => [13, 23, 31]
    | 22 => [1, 37, 47, 55]
    | 24 => [4]
    | 25 => [12, 21, 29]
    | 26 => [0, 36, 45, 53]
    | 28 => [6]
    | 29 => [9, 14, 25]
    | 30 => [2, 33, 38, 49]
    | _ => []

/-- Tiles indexed by their east edge colour. -/
private def rightTiles (c : ℕ) : List Index :=
  if c < 16 then
    match c with
    | 1 => [2, 34, 43, 50]
    | 2 => [10, 19, 26]
    | 3 => [6]
    | 5 => [0, 41, 46, 54]
    | 6 => [17, 22, 30]
    | 7 => [4]
    | 9 => [1, 40, 44, 52]
    | 10 => [16, 20, 28]
    | 11 => [5]
    | 13 => [3, 32, 42, 48]
    | 14 => [8, 18, 24]
    | 15 => [7]
    | _ => []
  else
    match c with
    | 16 => [61, 67, 73, 79]
    | 17 => [35, 39, 51, 85, 91, 97, 103]
    | 18 => [11, 15, 27]
    | 20 => [58, 64, 70, 76]
    | 21 => [37, 47, 55, 82, 88, 94, 100]
    | 22 => [13, 23, 31]
    | 24 => [56, 57, 62, 63, 68, 69, 74, 75]
    | 25 => [36, 45, 53, 80, 81, 86, 87, 92, 93, 98, 99]
    | 26 => [12, 21, 29]
    | 28 => [59, 60, 65, 66, 71, 72, 77, 78]
    | 29 => [33, 38, 49, 83, 84, 89, 90, 95, 96, 101, 102]
    | 30 => [9, 14, 25]
    | _ => []

/-- Tiles indexed by their south edge colour. -/
private def bottomTiles (c : ℕ) : List Index :=
  if c < 16 then
    match c with
    | 1 => [63, 66, 67]
    | 2 => [40, 41, 42, 43, 87, 90, 91]
    | 3 => [16, 17, 18, 19]
    | 5 => [57, 60, 61]
    | 6 => [36, 37, 38, 39, 81, 84, 85]
    | 7 => [12, 13, 14, 15]
    | 9 => [69, 72, 73]
    | 10 => [44, 45, 46, 47, 48, 49, 50, 51, 93, 96, 97]
    | 11 => [20, 21, 22, 23, 24, 25, 26, 27]
    | 13 => [75, 78, 79]
    | 14 => [32, 33, 34, 35, 52, 53, 54, 55, 99, 102, 103]
    | 15 => [8, 9, 10, 11, 28, 29, 30, 31]
    | _ => []
  else
    match c with
    | 16 => [7]
    | 17 => [62, 64, 65]
    | 18 => [3, 86, 88, 89]
    | 20 => [6]
    | 21 => [56, 58, 59]
    | 22 => [2, 80, 82, 83]
    | 24 => [4]
    | 25 => [68, 70, 71]
    | 26 => [0, 92, 94, 95]
    | 28 => [5]
    | 29 => [74, 76, 77]
    | 30 => [1, 98, 100, 101]
    | _ => []

/-- Tiles indexed by their north edge colour. -/
private def topTiles (c : ℕ) : List Index :=
  if c < 16 then
    match c with
    | 1 => [1, 87, 90, 91]
    | 2 => [63, 66, 67]
    | 3 => [5]
    | 5 => [0, 81, 84, 85]
    | 6 => [57, 60, 61]
    | 7 => [4]
    | 9 => [2, 93, 96, 97]
    | 10 => [69, 72, 73]
    | 11 => [6]
    | 13 => [3, 99, 102, 103]
    | 14 => [75, 78, 79]
    | 15 => [7]
    | _ => []
  else
    match c with
    | 16 => [16, 17, 18, 19]
    | 17 => [40, 41, 42, 43, 86, 88, 89]
    | 18 => [62, 64, 65]
    | 20 => [12, 13, 14, 15]
    | 21 => [36, 37, 38, 39, 80, 82, 83]
    | 22 => [56, 58, 59]
    | 24 => [20, 21, 22, 23, 24, 25, 26, 27]
    | 25 => [44, 45, 46, 47, 48, 49, 50, 51, 92, 94, 95]
    | 26 => [68, 70, 71]
    | 28 => [8, 9, 10, 11, 28, 29, 30, 31]
    | 29 => [32, 33, 34, 35, 52, 53, 54, 55, 98, 100, 101]
    | 30 => [74, 76, 77]
    | _ => []

/-- Recover the candidate parent from its southwest child `sw` and northeast child `ne`. A
phase-`a` parent is its own southwest child and has northeast child `4`; otherwise the southwest
child is `p - 4` (for `p < 8`) or `p + 24`, so the parent is `sw + 4` or `sw - 24`. -/
private def parentOf (sw ne : Index) : Index :=
  if ne.val == 4 then sw
  else if h : sw.val < 4 then ⟨sw.val + 4, by omega⟩
  else ⟨sw.val - 24, by omega⟩

/-- Every tile lies in its own colour bucket on all four sides, and `parentOf` recovers it from
its southwest and northeast children. Only this direction is needed, so the buckets may list
extra tiles. -/
private def edgeCert : Bool :=
  (List.finRange 104).all fun i =>
    let t := tile (components i)
    (leftTiles t.left).contains i &&
    (rightTiles t.right).contains i &&
    (bottomTiles t.bottom).contains i &&
    (topTiles t.top).contains i &&
    (parentOf (childBlock i 0 0) (childBlock i 1 1) == i)

private theorem edgeCert_ok : edgeCert = true := by decide +kernel

private theorem edgeCert_at (i : Index) :
    i ∈ leftTiles (tile (components i)).left ∧
    i ∈ rightTiles (tile (components i)).right ∧
    i ∈ bottomTiles (tile (components i)).bottom ∧
    i ∈ topTiles (tile (components i)).top ∧
    parentOf (childBlock i 0 0) (childBlock i 1 1) = i := by
  have h := List.all_eq_true.mp edgeCert_ok i (List.mem_finRange i)
  simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hl, hr⟩, hb⟩, ht⟩, hp⟩ := h
  exact ⟨hl, hr, hb, ht, hp⟩

/-- There is a matching horizontal pair of tiles below the central row, whose top colours are
`b1` and `b2`. -/
private def hasSouth2 (b1 b2 : ℕ) : Bool :=
  let s2s := topTiles b2
  (topTiles b1).any fun s1 =>
    let l1 := leftTiles (tile (components s1)).right
    s2s.any fun s2 => l1.contains s2

/-- There is a matching vertical pair of tiles west of the central column, whose right colours
are `l1` and `lu1`. -/
private def hasWest2 (l1 lu1 : ℕ) : Bool :=
  let u0s := rightTiles lu1
  (rightTiles l1).any fun x0 =>
    let b0 := bottomTiles (tile (components x0)).top
    u0s.any fun u0 => b0.contains u0

/-- Every central two-by-two block with a phase-`a` southwest tile and four matching internal
edges either is the child block of `parentOf x1 u2`, or has no matching south pair or no
matching west pair. -/
private def check2x2 : Bool :=
  (List.finRange 104).all fun x1 =>
    let c1 := components x1
    match c1.thin with
    | .a =>
      let t1 := tile c1
      let x2s := (leftTiles t1.right).map fun x2 => (x2, tile (components x2))
      (bottomTiles t1.top).all fun u1 =>
        let tu1 := tile (components u1)
        let u2s := leftTiles tu1.right
        x2s.all fun (x2, t2) =>
          let b2s := bottomTiles t2.top
          u2s.all fun u2 =>
            if b2s.contains u2 then
              let p := parentOf x1 u2
              (childBlock p 0 0 == x1 && childBlock p 1 0 == x2 &&
                childBlock p 0 1 == u1 && childBlock p 1 1 == u2) ||
              !(hasSouth2 t1.bottom t2.bottom && hasWest2 t1.left tu1.left)
            else true
    | _ => true

private theorem check2x2_ok : check2x2 = true := by decide +kernel

/-- The central two-by-two block has a unique substitution parent, with its one-cell context. -/
theorem existsUnique_centerParent (N : Neighborhood) :
    ∃! p : Index,
      childBlock p 0 0 = N.cell 1 1 ∧ childBlock p 1 0 = N.cell 2 1 ∧
      childBlock p 0 1 = N.cell 1 2 ∧ childBlock p 1 1 = N.cell 2 2 := by
  let x1 := N.cell 1 1
  let x2 := N.cell 2 1
  let u1 := N.cell 1 2
  let u2 := N.cell 2 2
  have hh11 : (tile (components x1)).right = (tile (components x2)).left := N.horizontal 1 1
  have hv11 : (tile (components x1)).top = (tile (components u1)).bottom := N.vertical 1 1
  have hh12 : (tile (components u1)).right = (tile (components u2)).left := N.horizontal 1 2
  have hv21 : (tile (components x2)).top = (tile (components u2)).bottom := N.vertical 2 1
  have hv10 : (tile (components (N.cell 1 0))).top = (tile (components x1)).bottom := N.vertical 1 0
  have hv20 : (tile (components (N.cell 2 0))).top = (tile (components x2)).bottom := N.vertical 2 0
  have hh10 : (tile (components (N.cell 1 0))).right = (tile (components (N.cell 2 0))).left :=
    N.horizontal 1 0
  have hh01 : (tile (components (N.cell 0 1))).right = (tile (components x1)).left :=
    N.horizontal 0 1
  have hh02 : (tile (components (N.cell 0 2))).right = (tile (components u1)).left :=
    N.horizontal 0 2
  have hv01 : (tile (components (N.cell 0 1))).top = (tile (components (N.cell 0 2))).bottom :=
    N.vertical 0 1
  have hx2 : x2 ∈ leftTiles (tile (components x1)).right := by
    rw [hh11]; exact (edgeCert_at x2).1
  have hu1 : u1 ∈ bottomTiles (tile (components x1)).top := by
    rw [hv11]; exact (edgeCert_at u1).2.2.1
  have hu2 : u2 ∈ leftTiles (tile (components u1)).right := by
    rw [hh12]; exact (edgeCert_at u2).1
  have hu2b : u2 ∈ bottomTiles (tile (components x2)).top := by
    rw [hv21]; exact (edgeCert_at u2).2.2.1
  have hsouth : hasSouth2 (tile (components x1)).bottom (tile (components x2)).bottom = true := by
    simp only [hasSouth2, List.any_eq_true, List.contains_iff_mem]
    exact ⟨N.cell 1 0, hv10 ▸ (edgeCert_at (N.cell 1 0)).2.2.2.1,
      N.cell 2 0, hv20 ▸ (edgeCert_at (N.cell 2 0)).2.2.2.1,
      hh10.symm ▸ (edgeCert_at (N.cell 2 0)).1⟩
  have hwest : hasWest2 (tile (components x1)).left (tile (components u1)).left = true := by
    simp only [hasWest2, List.any_eq_true, List.contains_iff_mem]
    exact ⟨N.cell 0 1, hh01 ▸ (edgeCert_at (N.cell 0 1)).2.1,
      N.cell 0 2, hh02 ▸ (edgeCert_at (N.cell 0 2)).2.1,
      hv01.symm ▸ (edgeCert_at (N.cell 0 2)).2.2.1⟩
  have h1 := List.all_eq_true.mp check2x2_ok x1 (List.mem_finRange x1)
  dsimp only at h1
  rw [N.phase] at h1
  have h2 := List.all_eq_true.mp h1 u1 hu1
  have h3 := List.all_eq_true.mp h2 (x2, tile (components x2)) (List.mem_map_of_mem hx2)
  have h4 := List.all_eq_true.mp h3 u2 hu2
  have hmem : (bottomTiles (tile (components x2)).top).contains u2 = true :=
    List.contains_iff_mem.mpr hu2b
  simp only [hmem, ↓reduceIte, hsouth, hwest, Bool.and_self, Bool.not_true, Bool.or_false,
    Bool.and_eq_true, beq_iff_eq] at h4
  obtain ⟨⟨⟨hc00, hc10⟩, hc01⟩, hc11⟩ := h4
  refine ⟨parentOf x1 u2, ⟨hc00, hc10, hc01, hc11⟩, ?_⟩
  rintro q ⟨hq00, _, _, hq11⟩
  rw [← (edgeCert_at q).2.2.2.2, hq00, hq11]

end Cslib.WangTile.Robinson
