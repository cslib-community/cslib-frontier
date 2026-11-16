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
Exact enumeration of matching rows, including rejected candidates, proves completeness of
the finite check.
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

private def hFollowers : ℕ → List ℕ
  | 0 | 41 | 46 | 54 => [17, 22, 30]
  | 1 | 40 | 44 | 52 => [16, 20, 28]
  | 2 | 34 | 43 | 50 => [10, 19, 26]
  | 3 | 32 | 42 | 48 => [8, 18, 24]
  | 4 => [58, 64, 70, 76]
  | 5 => [56, 57, 62, 63, 68, 69, 74, 75]
  | 6 => [61, 67, 73, 79]
  | 7 => [59, 60, 65, 66, 71, 72, 77, 78]
  | 8 | 18 | 24 => [32, 42, 48, 83, 84, 89, 90, 95, 96, 101, 102]
  | 9 | 14 | 25 => [2, 33, 38, 49]
  | 10 | 19 | 26 => [34, 43, 50, 85, 91, 97, 103]
  | 11 | 15 | 27 => [3, 35, 39, 51]
  | 12 | 21 | 29 => [0, 36, 45, 53]
  | 13 | 23 | 31 => [1, 37, 47, 55]
  | 16 | 20 | 28 => [40, 44, 52, 80, 81, 86, 87, 92, 93, 98, 99]
  | 17 | 22 | 30 => [41, 46, 54, 82, 88, 94, 100]
  | 33 | 38 | 49 | 83 | 84 | 89 | 90 | 95 | 96 | 101 | 102 => [9, 14, 25]
  | 35 | 39 | 51 | 85 | 91 | 97 | 103 => [11, 15, 27]
  | 36 | 45 | 53 | 80 | 81 | 86 | 87 | 92 | 93 | 98 | 99 => [12, 21, 29]
  | 37 | 47 | 55 | 82 | 88 | 94 | 100 => [13, 23, 31]
  | 56 | 57 | 62 | 63 | 68 | 69 | 74 | 75 => [4]
  | 58 | 64 | 70 | 76 => [5]
  | 59 | 60 | 65 | 66 | 71 | 72 | 77 | 78 => [6]
  | 61 | 67 | 73 | 79 => [7]
  | _ => []

private def vFollowers : ℕ → List ℕ
  | 0 | 81 | 84 | 85 => [57, 60, 61]
  | 1 | 87 | 90 | 91 => [63, 66, 67]
  | 2 | 93 | 96 | 97 => [69, 72, 73]
  | 3 | 99 | 102 | 103 => [75, 78, 79]
  | 4 => [12, 13, 14, 15]
  | 5 => [16, 17, 18, 19]
  | 6 => [20, 21, 22, 23, 24, 25, 26, 27]
  | 7 => [8, 9, 10, 11, 28, 29, 30, 31]
  | 8 | 9 | 10 | 11 | 28 | 29 | 30 | 31 => [5]
  | 12 | 13 | 14 | 15 => [6]
  | 16 | 17 | 18 | 19 => [7]
  | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 => [4]
  | 32 | 33 | 34 | 35 | 52 | 53 | 54 | 55 | 98 | 100 | 101 => [74, 76, 77]
  | 36 | 37 | 38 | 39 | 80 | 82 | 83 => [56, 58, 59]
  | 40 | 41 | 42 | 43 | 86 | 88 | 89 => [62, 64, 65]
  | 44 | 45 | 46 | 47 | 48 | 49 | 50 | 51 | 92 | 94 | 95 => [68, 70, 71]
  | 56 | 58 | 59 => [2, 80, 82, 83]
  | 57 | 60 | 61 => [36, 37, 38, 39, 81, 84, 85]
  | 62 | 64 | 65 => [3, 86, 88, 89]
  | 63 | 66 | 67 => [40, 41, 42, 43, 87, 90, 91]
  | 68 | 70 | 71 => [0, 92, 94, 95]
  | 69 | 72 | 73 => [44, 45, 46, 47, 48, 49, 50, 51, 93, 96, 97]
  | 74 | 76 | 77 => [1, 98, 100, 101]
  | 75 | 78 | 79 => [32, 33, 34, 35, 52, 53, 54, 55, 99, 102, 103]
  | _ => []

private def vPredecessors : ℕ → List ℕ
  | 0 | 92 | 94 | 95 => [68, 70, 71]
  | 1 | 98 | 100 | 101 => [74, 76, 77]
  | 2 | 80 | 82 | 83 => [56, 58, 59]
  | 3 | 86 | 88 | 89 => [62, 64, 65]
  | 4 => [20, 21, 22, 23, 24, 25, 26, 27]
  | 5 => [8, 9, 10, 11, 28, 29, 30, 31]
  | 6 => [12, 13, 14, 15]
  | 7 => [16, 17, 18, 19]
  | 8 | 9 | 10 | 11 | 28 | 29 | 30 | 31 => [7]
  | 12 | 13 | 14 | 15 => [4]
  | 16 | 17 | 18 | 19 => [5]
  | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 => [6]
  | 32 | 33 | 34 | 35 | 52 | 53 | 54 | 55 | 99 | 102 | 103 => [75, 78, 79]
  | 36 | 37 | 38 | 39 | 81 | 84 | 85 => [57, 60, 61]
  | 40 | 41 | 42 | 43 | 87 | 90 | 91 => [63, 66, 67]
  | 44 | 45 | 46 | 47 | 48 | 49 | 50 | 51 | 93 | 96 | 97 => [69, 72, 73]
  | 56 | 58 | 59 => [36, 37, 38, 39, 80, 82, 83]
  | 57 | 60 | 61 => [0, 81, 84, 85]
  | 62 | 64 | 65 => [40, 41, 42, 43, 86, 88, 89]
  | 63 | 66 | 67 => [1, 87, 90, 91]
  | 68 | 70 | 71 => [44, 45, 46, 47, 48, 49, 50, 51, 92, 94, 95]
  | 69 | 72 | 73 => [2, 93, 96, 97]
  | 74 | 76 | 77 => [32, 33, 34, 35, 52, 53, 54, 55, 98, 100, 101]
  | 75 | 78 | 79 => [3, 99, 102, 103]
  | _ => []

private def phaseA (i : ℕ) : Bool :=
  i < 4 || (32 ≤ i && i < 56) || (80 ≤ i && i < 104)

private def rowCertificate (i : Index) : Prop :=
  hFollowers i.val = ((List.finRange 104).filter fun j =>
    decide ((tile (components i)).right = (tile (components j)).left)).map Fin.val ∧
  vFollowers i.val = ((List.finRange 104).filter fun j =>
    decide ((tile (components i)).top = (tile (components j)).bottom)).map Fin.val ∧
  vPredecessors i.val = ((List.finRange 104).filter fun j =>
    decide ((tile (components j)).top = (tile (components i)).bottom)).map Fin.val ∧
  phaseA i.val = decide ((components i).thin = .a)

private instance (i : Index) : Decidable (rowCertificate i) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem rowCertificate_all : ∀ i : Index, rowCertificate i := by decide +kernel

private theorem mem_hFollowers (i j : Index) :
    j.val ∈ hFollowers i.val ↔
      (tile (components i)).right = (tile (components j)).left := by
  rw [(rowCertificate_all i).1]
  simp [Fin.val_inj]

private theorem mem_vFollowers (i j : Index) :
    j.val ∈ vFollowers i.val ↔
      (tile (components i)).top = (tile (components j)).bottom := by
  rw [(rowCertificate_all i).2.1]
  simp [Fin.val_inj]

private theorem mem_vPredecessors (i j : Index) :
    j.val ∈ vPredecessors i.val ↔
      (tile (components j)).top = (tile (components i)).bottom := by
  rw [(rowCertificate_all i).2.2.1]
  simp [Fin.val_inj]

/-- Internal row search record; integer indices keep its finite evaluator small. -/
private structure Row where
  x0 : ℕ
  x1 : ℕ
  x2 : ℕ
  x3 : ℕ
  deriving DecidableEq

private def rows (a : ℕ) : List Row :=
  (hFollowers a).flatMap fun b => (hFollowers b).flatMap fun c =>
    (hFollowers c).map fun d => ⟨a, b, c, d⟩

private def verticalRows (follow : ℕ → List ℕ) (r : Row) : List Row :=
  (follow r.x0).flatMap fun a =>
    ((hFollowers a).filter fun b => b ∈ follow r.x1).flatMap fun b =>
      ((hFollowers b).filter fun c => c ∈ follow r.x2).flatMap fun c =>
        ((hFollowers c).filter fun d => d ∈ follow r.x3).map fun d => ⟨a, b, c, d⟩

private def Row.horizontal (r : Row) : Prop :=
  r.x1 ∈ hFollowers r.x0 ∧ r.x2 ∈ hFollowers r.x1 ∧ r.x3 ∈ hFollowers r.x2

private def Row.vertical (follow : ℕ → List ℕ) (r u : Row) : Prop :=
  u.x0 ∈ follow r.x0 ∧ u.x1 ∈ follow r.x1 ∧
    u.x2 ∈ follow r.x2 ∧ u.x3 ∈ follow r.x3

private theorem mem_rows (r : Row) : r ∈ rows r.x0 ↔ r.horizontal := by
  rcases r with ⟨a, b, c, d⟩
  simp [rows, Row.horizontal, Row.mk.injEq]

private theorem mem_verticalRows (follow : ℕ → List ℕ) (r u : Row) :
    u ∈ verticalRows follow r ↔ u.horizontal ∧ r.vertical follow u := by
  rcases u with ⟨a, b, c, d⟩
  simp only [verticalRows, List.mem_flatMap, List.mem_filter, decide_eq_true_eq,
    List.mem_map, Row.mk.injEq, Row.horizontal, Row.vertical]
  constructor
  · rintro ⟨a', ha, b', ⟨hb, hb'⟩, c', ⟨hc, hc'⟩, d', ⟨hd, hd'⟩, heq⟩
    rcases heq with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨⟨hb, hc, hd⟩, ha, hb', hc', hd'⟩
  · rintro ⟨⟨hb, hc, hd⟩, ha, hb', hc', hd'⟩
    exact ⟨a, ha, b, ⟨hb, hb'⟩, c, ⟨hc, hc'⟩, d, ⟨hd, hd'⟩, rfl, rfl, rfl, rfl⟩

private def pairs (a : ℕ) : List (Row × Row) :=
  ((rows a).filter fun r => phaseA r.x1).flatMap fun r =>
    (verticalRows vFollowers r).map fun u => (r, u)

private def extendable (r u : Row) : Bool :=
  !(verticalRows vPredecessors r).isEmpty && !(verticalRows vFollowers u).isEmpty

private def children (p : Index) : Row :=
  ⟨(childBlock p 0 0).val, (childBlock p 1 0).val,
    (childBlock p 0 1).val, (childBlock p 1 1).val⟩

private def center (r u : Row) : Row := ⟨r.x1, r.x2, u.x1, u.x2⟩

private def candidates (r u : Row) : List Index :=
  (List.finRange 104).filter fun i => decide (children i = center r u)

private def check (r u : Row) : Bool := !extendable r u || (candidates r u).length == 1

private def checkBucket (i : ℕ) : Bool := (pairs i).all fun (r, u) => check r u

private theorem all_buckets : ∀ i : Index, checkBucket i.val = true := by decide +kernel

private theorem mem_pairs (r u : Row) (hr : r.horizontal)
    (hu : u.horizontal) (hv : r.vertical vFollowers u) (hphase : phaseA r.x1 = true) :
    (r, u) ∈ pairs r.x0 := by
  simp only [pairs, List.mem_flatMap, List.mem_filter, List.mem_map]
  exact ⟨r, ⟨(mem_rows r).mpr hr, hphase⟩, u,
    (mem_verticalRows vFollowers r u).mpr ⟨hu, hv⟩, rfl⟩

private theorem uniqueParent_spec (r u : Row) (hu : (candidates r u).length = 1) :
    ∃! p : Index, children p = center r u := by
  obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp hu
  have hmem (q : Index) : q ∈ candidates r u ↔ children q = center r u := by
    simp [candidates]
  refine ⟨p, (hmem p).mp ?_, ?_⟩
  · rw [hp]; exact List.mem_singleton_self p
  · intro q hq
    have := (hmem q).mpr hq
    simpa only [hp, List.mem_singleton] using this

private theorem bucket_recognition (south r u north : Row)
    (hs : south.horizontal) (hr : r.horizontal) (hu : u.horizontal) (hn : north.horizontal)
    (hsr : r.vertical vPredecessors south) (hru : r.vertical vFollowers u)
    (hun : u.vertical vFollowers north) (ha : phaseA r.x1 = true)
    (hc : checkBucket r.x0 = true) :
    ∃! p : Index, children p = center r u := by
  have hsmem := (mem_verticalRows vPredecessors r south).mpr ⟨hs, hsr⟩
  have hnmem := (mem_verticalRows vFollowers u north).mpr ⟨hn, hun⟩
  have hex : extendable r u = true := by
    have h1 := List.isEmpty_eq_false_iff_exists_mem.mpr ⟨south, hsmem⟩
    have h2 := List.isEmpty_eq_false_iff_exists_mem.mpr ⟨north, hnmem⟩
    simp only [extendable, h1, h2, Bool.not_false, Bool.and_self]
  have hcheck := List.all_eq_true.mp hc (r, u) (mem_pairs r u hr hu hru ha)
  apply uniqueParent_spec r u
  simpa only [check, hex, Bool.not_true, Bool.false_or, beq_iff_eq] using hcheck

/-- The central two-by-two block has a unique substitution parent, with its one-cell context. -/
theorem existsUnique_centerParent (N : Neighborhood) :
    ∃! p : Index,
      childBlock p 0 0 = N.cell 1 1 ∧ childBlock p 1 0 = N.cell 2 1 ∧
      childBlock p 0 1 = N.cell 1 2 ∧ childBlock p 1 1 = N.cell 2 2 := by
  let row (j : Fin 4) : Row :=
    ⟨(N.cell 0 j).val, (N.cell 1 j).val, (N.cell 2 j).val, (N.cell 3 j).val⟩
  have hh (j : Fin 4) : (row j).horizontal :=
    ⟨(mem_hFollowers _ _).mpr (N.horizontal 0 j),
      (mem_hFollowers _ _).mpr (N.horizontal 1 j),
      (mem_hFollowers _ _).mpr (N.horizontal 2 j)⟩
  have hv (j : Fin 3) : (row j.castSucc).vertical vFollowers (row j.succ) :=
    ⟨(mem_vFollowers _ _).mpr (N.vertical 0 j),
      (mem_vFollowers _ _).mpr (N.vertical 1 j),
      (mem_vFollowers _ _).mpr (N.vertical 2 j),
      (mem_vFollowers _ _).mpr (N.vertical 3 j)⟩
  have hi : (row 1).vertical vPredecessors (row 0) :=
    ⟨(mem_vPredecessors _ _).mpr (N.vertical 0 0),
      (mem_vPredecessors _ _).mpr (N.vertical 1 0),
      (mem_vPredecessors _ _).mpr (N.vertical 2 0),
      (mem_vPredecessors _ _).mpr (N.vertical 3 0)⟩
  have ha : phaseA (row 1).x1 = true := by
    rw [(rowCertificate_all (N.cell 1 1)).2.2.2, N.phase]
    rfl
  have hb : checkBucket (row 1).x0 = true := all_buckets (N.cell 0 1)
  have h := bucket_recognition (row 0) (row 1) (row 2) (row 3)
    (hh 0) (hh 1) (hh 2) (hh 3) hi (hv 1) (hv 2) ha hb
  simpa only [children, center, row, Row.mk.injEq, Fin.val_inj] using h

end Cslib.WangTile.Robinson
