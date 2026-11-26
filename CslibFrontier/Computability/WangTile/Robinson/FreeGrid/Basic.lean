/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.Shading.Geometry
public import CslibFrontier.Computability.WangTile.Robinson.Signals
import CslibFrontier.Computability.WangTile.Robinson.Canonical.Patches
import CslibFrontier.Computability.WangTile.Robinson.RedPaths.Certificates
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Arbitrarily large marked free grids in Robinson planes

For every size, each decoded scaffold plane contains a uniformly light board with that many
consecutive free rows and columns. Their southwest crossing is the northeast quarter of
corrected tile zero. The hierarchy provides a zero-root substituted patch; canonical shade
comparison supplies sparse free lines, and sorting all free lines above the marker fills gaps.

## Main definitions

* `MarkedFreeGrid`: consecutive free rows and columns with a marked
  southwest crossing, indexed by `Fin (n + 1)`.

## Main results

* `exists_markedFreeGrid`: every scaffold plane contains such grids of every size
  inside uniformly light oriented boards.

## References

The construction uses the corrected Robinson scaffold of [JeandelVanier2020]. After
[lean-wang](https://github.com/edemaine/lean-wang/tree/64268a3/LeanWang/Robinson/Closed104),
revision `64268a3`: `CanonicalEvenFreeLines`, `CanonicalOddFreeLines`,
`CanonicalShadeComparison`, `CanonicalOddShadeComparison`, `ShadedMarkedFreeGrid`,
`SparseFreeLineDecodedMarkedGrid` and `ShadedConsecutiveFreeGrid`. Closed coordinate formulas
replace branch lists, and one shade comparison handles both parity phases.
-/

public section

namespace Cslib.WangTile.Robinson

open Canonical

/-- Consecutive free rows and columns inside one board, with a marked southwest crossing.
The parameter `n` denotes one less than the number of selected rows and columns. -/
structure MarkedFreeGrid (indexGrid : ℕ → ℕ → Index)
    (shadeGrid : ℕ → ℕ → ShadeState) (west east south north n : ℕ) where
  /-- Increasing quarter coordinates of columns. -/
  column : Fin (n + 1) → ℕ
  /-- Increasing quarter coordinates of rows. -/
  row : Fin (n + 1) → ℕ
  /-- Columns are distinct and increasing. -/
  column_strictMono : StrictMono column
  /-- Rows are distinct and increasing. -/
  row_strictMono : StrictMono row
  /-- Columns lie to the right of the west boundary. -/
  column_west : ∀ i, quarterWest west < column i
  /-- Columns lie to the left of the east boundary. -/
  column_east : ∀ i, column i < quarterEast east
  /-- Rows lie above the south boundary. -/
  row_south : ∀ i, quarterSouth south < row i
  /-- Rows lie below the north boundary. -/
  row_north : ∀ i, row i < quarterNorth north
  /-- Selected columns have no horizontal light obstruction. -/
  freeColumn : ∀ i, IsFreeColumn indexGrid shadeGrid south north (column i)
  /-- Selected rows have no vertical light obstruction. -/
  freeRow : ∀ i, IsFreeRow indexGrid shadeGrid west east (row i)
  /-- No unselected free column lies between consecutive selected columns. -/
  noFreeColumnBetween : ∀ (i : Fin n) (k : ℕ),
    column i.castSucc < k → k < column i.succ →
      ¬IsFreeColumn indexGrid shadeGrid south north k
  /-- No unselected free row lies between consecutive selected rows. -/
  noFreeRowBetween : ∀ (i : Fin n) (k : ℕ),
    row i.castSucc < k → k < row i.succ →
      ¬IsFreeRow indexGrid shadeGrid west east k
  /-- The southwest crossing is the northeast quarter of tile zero. -/
  marker : QuarterIndex.mk (indexGrid (column 0 / 2) (row 0 / 2))
    (quadrantAt (column 0) (row 0)) = ⟨0, .northeast⟩

/-- Sorting an initial segment preserves its minimum and leaves no gaps. -/
private theorem select_lines {n lo hi : ℕ} {p : ℕ → Prop}
    (f : Fin (n + 1) → ℕ) (hf : StrictMono f)
    (hmem : ∀ i, lo < f i ∧ f i < hi ∧ p (f i)) :
    ∃ g : Fin (n + 1) → ℕ, StrictMono g ∧ g 0 = f 0 ∧
      (∀ i, lo < g i ∧ g i < hi ∧ p (g i)) ∧
      ∀ (i : Fin n) (k : ℕ), g i.castSucc < k → k < g i.succ → ¬p k := by
  classical
  let s := (Finset.Ioo lo hi).filter (fun k => f 0 ≤ k ∧ p k)
  have mem (i : Fin (n + 1)) : f i ∈ s :=
    Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨(hmem i).1, (hmem i).2.1⟩,
      hf.monotone (Fin.zero_le i), (hmem i).2.2⟩
  have card : n + 1 ≤ s.card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective
      (fun i : Fin (n + 1) => (⟨f i, mem i⟩ : s))
      (fun _ _ h => hf.injective (congrArg Subtype.val h))
  let g := s.orderEmbOfCardLe card
  have gmem := s.orderEmbOfCardLe_mem card
  have properties i : lo < g i ∧ g i < hi ∧ p (g i) := by
    have h := Finset.mem_filter.mp (gmem i)
    exact ⟨(Finset.mem_Ioo.mp h.1).1, (Finset.mem_Ioo.mp h.1).2, h.2.2⟩
  let inv {k : ℕ} (hk : k ∈ s) := (s.orderIsoOfFin rfl).symm ⟨k, hk⟩
  have hinv {k : ℕ} (hk : k ∈ s) : (s.orderEmbOfFin rfl (inv hk) : ℕ) = k :=
    congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨k, hk⟩)
  refine ⟨g, g.strictMono, le_antisymm
      (((s.orderEmbOfFin rfl).monotone (Nat.zero_le (inv (mem 0)).val)).trans_eq (hinv (mem 0)))
      (Finset.mem_filter.mp (gmem 0)).2.1,
    properties, fun i k hl hu hp => ?_⟩
  have hk : k ∈ s := Finset.mem_filter.mpr
    ⟨Finset.mem_Ioo.mpr ⟨(properties i.castSucc).1.trans hl, hu.trans (properties i.succ).2.1⟩,
      (Finset.mem_filter.mp (gmem i.castSucc)).2.1.trans hl.le, hp⟩
  have hlo : (i : ℕ) < (inv hk).val :=
    (s.orderEmbOfFin rfl).lt_iff_lt.mp (hl.trans_eq (hinv hk).symm)
  have hhi : (inv hk).val < i.val + 1 :=
    (s.orderEmbOfFin rfl).lt_iff_lt.mp ((hinv hk).trans_lt hu)
  omega

/-- Fill all gaps in sparse free lines without moving their marked southwest crossing. -/
private theorem MarkedFreeGrid.ofSparse
    {g : ℕ → ℕ → Index} {s : ℕ → ℕ → ShadeState}
    {west east south north n : ℕ}
    (columns rows : Fin (n + 1) → ℕ)
    (hcolumns : StrictMono columns) (hrows : StrictMono rows)
    (column_mem : ∀ i, quarterWest west < columns i ∧ columns i < quarterEast east ∧
      IsFreeColumn g s south north (columns i))
    (row_mem : ∀ i, quarterSouth south < rows i ∧ rows i < quarterNorth north ∧
      IsFreeRow g s west east (rows i))
    (marker : QuarterIndex.mk (g (columns 0 / 2) (rows 0 / 2))
      (quadrantAt (columns 0) (rows 0)) = ⟨0, .northeast⟩) :
    Nonempty (MarkedFreeGrid g s west east south north n) := by
  obtain ⟨c, hc, hc0, cmem, cnext⟩ := select_lines columns hcolumns column_mem
  obtain ⟨r, hr, hr0, rmem, rnext⟩ := select_lines rows hrows row_mem
  exact ⟨{
    column := c, row := r
    column_strictMono := hc, row_strictMono := hr
    column_west := fun i => (cmem i).1, column_east := fun i => (cmem i).2.1
    row_south := fun i => (rmem i).1, row_north := fun i => (rmem i).2.1
    freeColumn := fun i => (cmem i).2.2, freeRow := fun i => (rmem i).2.2
    noFreeColumnBetween := cnext, noFreeRowBetween := rnext
    marker := by simpa only [hc0, hr0] using marker }⟩

private theorem crossing_ne {g : ℕ → ℕ → Index} {s : ℕ → ℕ → ShadeState}
    {w e b t w' e' b' t' x y : ℕ} {shade shade' : Shade}
    (valid : ValidShadeGrid g s) (c : CycleOn g w e b t) (d : CycleOn g w' e' b' t')
    (hs : CycleShade s w e b t shade) (ht : CycleShade s w' e' b' t' shade')
    (hx : x = quarterWest w ∨ x = quarterEast e)
    (hy : y = quarterSouth b' ∨ y = quarterNorth t')
    (xlo : quarterWest w' < x) (xhi : x < quarterEast e')
    (ylo : quarterSouth b < y) (yhi : y < quarterNorth t) : shade ≠ shade' := by
  have ⟨vertical, first⟩ : hasVertical (componentAt g x y) (quadrantAt x y) = true ∧
      (s x y).south = some shade := by
    rcases hx with rfl | rfl
    · exact ⟨CycleOn.west_path c ylo yhi, (hs.west_at c valid ylo yhi).1⟩
    · exact ⟨CycleOn.east_path c ylo yhi, (hs.east_at c valid ylo yhi).1⟩
  have ⟨horizontal, second⟩ : hasHorizontal (componentAt g x y) (quadrantAt x y) = true ∧
      (s x y).west = some shade' := by
    rcases hy with rfl | rfl
    · exact ⟨CycleOn.south_path d xlo xhi, (ht.south_at d valid xlo xhi).1⟩
    · exact ⟨CycleOn.north_path d xlo xhi, (ht.north_at d valid xlo xhi).1⟩
  exact fun eq =>
    (valid.rules x y).crossing_opposite horizontal vertical (by rw [first, second, eq])

private theorem root_cycle (g : ℕ → ℕ → Index) :
    CycleOn (iterateRefine 2 g) 1 3 1 3 :=
  CycleOn.congr (fixed_cycle (g 0 0)) (fun x y hx hy =>
    iterateRefine_eq_of_root_eq (g := fun _ _ => g 0 0) (h := g) rfl 2 x y (by omega) (by omega))

private theorem large_cycle (g : ℕ → ℕ → Index) (level : ℕ) :
    CycleOn (iterateRefine (level + 2) g)
      (2 ^ level) (3 * 2 ^ level) (2 ^ level) (3 * 2 ^ level) := by
  simpa only [iterateRefine_add, Nat.mul_one, Nat.one_mul, Nat.mul_comm] using
    (root_cycle g).iterateRefine level

private theorem small_cycle (g : ℕ → ℕ → Index) (level : ℕ) (hlevel : 1 ≤ level) :
    CycleOn (iterateRefine (level + 2) g)
      (2 ^ (level - 1)) (3 * 2 ^ (level - 1))
      (2 ^ (level - 1)) (3 * 2 ^ (level - 1)) := by
  simpa only [iterateRefine_add, show level - 1 + 2 + 1 = level + 2 by omega, Nat.mul_one,
    Nat.one_mul, Nat.mul_comm] using (root_cycle (iterateRefine 1 g)).iterateRefine (level - 1)

private theorem has_light_cycle (g : ℕ → ℕ → Index)
    {s : ℕ → ℕ → ShadeState} (level : ℕ) (hlevel : 1 ≤ level)
    (valid : ValidShadeGrid (iterateRefine (level + 2) g) s) :
    CycleShade s (2 ^ level) (3 * 2 ^ level) (2 ^ level) (3 * 2 ^ level) .light ∨
    CycleShade s (2 ^ (level - 1)) (3 * 2 ^ (level - 1))
      (2 ^ (level - 1)) (3 * 2 ^ (level - 1)) .light := by
  obtain ⟨a, ha⟩ := CycleOn.exists_cycleShade (large_cycle g level) valid
  obtain ⟨b, hb⟩ := CycleOn.exists_cycleShade (small_cycle g level hlevel) valid
  have pow_eq : 2 ^ level = 2 * 2 ^ (level - 1) := by rw [← pow_succ', Nat.sub_add_cancel hlevel]
  have positive : 0 < 2 ^ (level - 1) := pow_pos (by decide) _
  have neq := crossing_ne valid (large_cycle g level) (small_cycle g level hlevel) ha hb
    (Or.inl rfl) (Or.inr rfl)
    (by simp only [quarterWest, pow_eq]; omega)
    (by simp only [quarterWest, quarterEast, pow_eq]; omega)
    (by simp only [quarterSouth, quarterNorth, pow_eq]; omega)
    (by simp only [quarterNorth, pow_eq]; omega)
  cases a <;> cases b
  exacts [Or.inl ha, Or.inl ha, Or.inr hb, (neq rfl).elim]

private theorem exists_refined_zero (base : IndexPlane) (depth : ℕ) :
    ∃ (g : ℕ → ℕ → Index) (u v : ℤ), g 0 0 = 0 ∧
      (fun x y : ℕ => base.index (u + x) (v + y)) = iterateRefine depth g := by
  obtain ⟨a, b, hab⟩ := (tower base).every_tile depth 0
  obtain ⟨u, v, h⟩ := (tower base).refined_patch depth 0 a b
  exact ⟨fun x y => ((tower base).plane depth).index (a + x) (b + y), u, v,
    by simpa using hab, by simpa only [(tower base).zero, Nat.zero_add] using h⟩

private theorem cell_cycle (g : ℕ → ℕ → Index) (bx by₀ : ℕ) :
    CycleOn (iterateRefine 2 g) (4 * bx + 1) (4 * bx + 3)
      (4 * by₀ + 1) (4 * by₀ + 3) := by
  have same (x y : ℕ) (hx : x < 4) (hy : y < 4) :
      indexThick (iterateRefine 2 g (4 * bx + x) (4 * by₀ + y)) =
        indexThick (fineGrid (g bx by₀) x y) := by
    simpa only [componentAt,
      show (8 * bx + 2 * x) / 2 = 4 * bx + x by omega,
      show (8 * by₀ + 2 * y) / 2 = 4 * by₀ + y by omega,
      show 2 * x / 2 = x by omega, show 2 * y / 2 = y by omega] using
      componentAt_two_block g bx by₀ (2 * x) (2 * y) (by omega) (by omega)
  have lc := fixed_cycle (g bx by₀)
  refine ⟨by omega, by omega,
    (same 1 1 (by decide) (by decide)).trans lc.southwest,
    (same 3 1 (by decide) (by decide)).trans lc.southeast,
    (same 1 3 (by decide) (by decide)).trans lc.northwest,
    (same 3 3 (by decide) (by decide)).trans lc.northeast,
    fun x _ _ => ?_, fun x _ _ => ?_, fun y _ _ => ?_, fun y _ _ => ?_⟩
  · rw [show x = 4 * bx + 2 by omega, same 2 1 (by decide) (by decide)]
    exact lc.southLane 2 (by decide) (by decide)
  · rw [show x = 4 * bx + 2 by omega, same 2 3 (by decide) (by decide)]
    exact lc.northLane 2 (by decide) (by decide)
  · rw [show y = 4 * by₀ + 2 by omega, same 1 2 (by decide) (by decide)]
    exact lc.westLane 2 (by decide) (by decide)
  · rw [show y = 4 * by₀ + 2 by omega, same 3 2 (by decide) (by decide)]
    exact lc.eastLane 2 (by decide) (by decide)

private theorem scaled_cell_cycle (g : ℕ → ℕ → Index) (depth bx by₀ : ℕ) :
    CycleOn (iterateRefine (depth + 2) g)
      (2 ^ depth * (4 * bx + 1)) (2 ^ depth * (4 * bx + 3))
      (2 ^ depth * (4 * by₀ + 1)) (2 ^ depth * (4 * by₀ + 3)) := by
  simpa only [iterateRefine_add] using (cell_cycle g bx by₀).iterateRefine depth

private theorem corner_shade_opposite
    (g : ℕ → ℕ → Index) (depth bx by₀ : ℕ) (cx cy : Fin 2)
    {s : ℕ → ℕ → ShadeState} {shade childShade : Shade}
    (valid : ValidShadeGrid (iterateRefine (depth + 1 + 2) g) s)
    (ancestor : CycleShade s
      (2 ^ (depth + 1) * (4 * bx + 1)) (2 ^ (depth + 1) * (4 * bx + 3))
      (2 ^ (depth + 1) * (4 * by₀ + 1)) (2 ^ (depth + 1) * (4 * by₀ + 3)) shade)
    (descendant : CycleShade s
      (2 ^ depth * (4 * (2 * bx + cx.val) + 1))
      (2 ^ depth * (4 * (2 * bx + cx.val) + 3))
      (2 ^ depth * (4 * (2 * by₀ + cy.val) + 1))
      (2 ^ depth * (4 * (2 * by₀ + cy.val) + 3)) childShade) :
    childShade = shade.opposite := by
  have child_cycle :=
    scaled_cell_cycle (iterateRefine 1 g) depth (2 * bx + cx.val) (2 * by₀ + cy.val)
  rw [iterateRefine_add, show depth + 2 + 1 = depth + 1 + 2 by omega] at child_cycle
  apply Shade.eq_opposite_of_ne
  let x := if cx.val = 0 then quarterWest (2 ^ (depth + 1) * (4 * bx + 1))
    else quarterEast (2 ^ (depth + 1) * (4 * bx + 3))
  let y := if cy.val = 0 then quarterNorth (2 ^ depth * (4 * (2 * by₀ + cy.val) + 3))
    else quarterSouth (2 ^ depth * (4 * (2 * by₀ + cy.val) + 1))
  apply crossing_ne valid (scaled_cell_cycle g (depth + 1) bx by₀) child_cycle
    ancestor descendant (x := x) (y := y)
  all_goals
    have positive : 0 < 2 ^ depth := pow_pos (by decide) _
    fin_cases cx <;> fin_cases cy <;>
      simp [x, y, quarterWest, quarterEast, quarterSouth, quarterNorth, pow_succ] <;> nlinarith

private theorem cell_half {scale block cell : ℕ}
    (lower : 2 * scale * block ≤ cell) (upper : cell < 2 * scale * (block + 1)) :
    ∃ corner : Fin 2, scale * (2 * block + corner.val) ≤ cell ∧
      cell < scale * (2 * block + corner.val + 1) := by
  by_cases h : cell < scale * (2 * block + 1)
  · refine ⟨0, ?_, ?_⟩ <;> dsimp <;> nlinarith
  · refine ⟨1, ?_, ?_⟩ <;> dsimp <;> nlinarith

/-- Each binary refinement step changes the shade between a board and each of its four
corner descendants. Iterating gives the shade of every finest cell cycle. -/
private theorem descendant_shade (depth : ℕ) (g : ℕ → ℕ → Index)
    {s : ℕ → ℕ → ShadeState} {shade : Shade}
    (valid : ValidShadeGrid (iterateRefine (depth + 2) g) s)
    (bx by₀ cellX cellY : ℕ)
    (ancestor : CycleShade s
      (2 ^ depth * (4 * bx + 1)) (2 ^ depth * (4 * bx + 3))
      (2 ^ depth * (4 * by₀ + 1)) (2 ^ depth * (4 * by₀ + 3)) shade)
    (xlo : 2 ^ depth * bx ≤ cellX) (xhi : cellX < 2 ^ depth * (bx + 1))
    (ylo : 2 ^ depth * by₀ ≤ cellY) (yhi : cellY < 2 ^ depth * (by₀ + 1)) :
    CycleShade s (4 * cellX + 1) (4 * cellX + 3) (4 * cellY + 1) (4 * cellY + 3)
      (Shade.opposite^[depth] shade) := by
  induction depth generalizing g bx by₀ shade with
  | zero =>
    simp only [pow_zero, Nat.one_mul] at ancestor xlo xhi ylo yhi
    simpa only [Function.iterate_zero_apply, show cellX = bx by omega, show cellY = by₀ by omega]
      using ancestor
  | succ depth ih =>
    obtain ⟨cx, xlo', xhi'⟩ := cell_half
      (show 2 * 2 ^ depth * bx ≤ cellX by simpa only [pow_succ'] using xlo)
      (show cellX < 2 * 2 ^ depth * (bx + 1) by simpa only [pow_succ'] using xhi)
    obtain ⟨cy, ylo', yhi'⟩ := cell_half
      (show 2 * 2 ^ depth * by₀ ≤ cellY by simpa only [pow_succ'] using ylo)
      (show cellY < 2 * 2 ^ depth * (by₀ + 1) by simpa only [pow_succ'] using yhi)
    have valid' : ValidShadeGrid (iterateRefine (depth + 2) (iterateRefine 1 g)) s := by
      rwa [iterateRefine_add]
    obtain ⟨childShade, child⟩ := CycleOn.exists_cycleShade
      (scaled_cell_cycle (iterateRefine 1 g) depth (2 * bx + cx.val) (2 * by₀ + cy.val)) valid'
    rw [corner_shade_opposite g depth bx by₀ cx cy valid ancestor child] at child
    simpa only [Function.iterate_succ_apply] using
      ih (iterateRefine 1 g) valid' (2 * bx + cx.val) (2 * by₀ + cy.val) child xlo' xhi' ylo' yhi'

/-- The distinguished local source port reads the shade of its translated finest cell cycle. -/
private theorem cell_source_value
    {g : ℕ → ℕ → Index} {s : ℕ → ℕ → ShadeState} {shade : Shade}
    (valid : ValidShadeGrid g s) (bx by₀ : ℕ)
    (cycle : CycleOn g (4 * bx + 1) (4 * bx + 3) (4 * by₀ + 1) (4 * by₀ + 3))
    (shaded : CycleShade s (4 * bx + 1) (4 * bx + 3)
      (4 * by₀ + 1) (4 * by₀ + 3) shade) :
    value s (translatePort cycleSource (8 * bx) (8 * by₀)) = some shade := by
  have h := shaded.south_at cycle valid (qx := 8 * bx + 4)
    (by simp only [quarterWest]; omega) (by simp only [quarterEast]; omega)
  simpa only [value, translatePort, cycleSource, quarterSouth,
    show 2 * (4 * by₀ + 1) + 1 = 8 * by₀ + 3 by omega] using h.1

/-- A root board determines the source shade in every finest descendant cell. -/
private theorem root_descendant_source (depth : ℕ) (g : ℕ → ℕ → Index)
    {s : ℕ → ℕ → ShadeState} {shade : Shade}
    (valid : ValidShadeGrid (iterateRefine (depth + 2) g) s)
    (root : CycleShade s (2 ^ depth) (3 * 2 ^ depth) (2 ^ depth) (3 * 2 ^ depth) shade)
    (cellX cellY : ℕ) (hx : cellX < 2 ^ depth) (hy : cellY < 2 ^ depth) :
    value s (translatePort cycleSource (8 * cellX) (8 * cellY)) =
      some (Shade.opposite^[depth] shade) := by
  have shaded := descendant_shade depth g valid 0 0 cellX cellY
    (by simpa only [Nat.mul_zero, Nat.zero_mul, Nat.zero_add, Nat.mul_one, Nat.one_mul,
      Nat.mul_comm] using root)
    (by simp) (by simpa only [Nat.zero_add, Nat.mul_one] using hx)
    (by simp) (by simpa only [Nat.zero_add, Nat.mul_one] using hy)
  have cycle := cell_cycle (iterateRefine depth g) cellX cellY
  rw [iterateRefine_add, Nat.add_comm 2 depth] at cycle
  exact cell_source_value valid cellX cellY cycle shaded

/-- The sparse branch at index zero is even; every positive index is an odd branch. -/
private def offset (depth index : ℕ) : ℕ :=
  if index = 0 then 2 * 4 ^ depth else 2 * 4 ^ depth + 2 * 4 ^ (index - 1) - 1

/-- The quarter coordinate in a phase whose scale is multiplied by `phaseScale` (1 or 2). -/
private def coordinate (phaseScale depth index : ℕ) : ℕ :=
  2 * phaseScale * 4 ^ depth + 1 + phaseScale * offset depth index

private theorem offset_bounds (depth index : ℕ) (hi : index ≤ depth) :
    0 < offset depth index ∧ offset depth index < 3 * 4 ^ depth := by
  have hp : 0 < 4 ^ depth := pow_pos (by decide) _
  by_cases hz : index = 0
  · simp only [offset, ite_eq_left hz]; omega
  · have hpow : 4 ^ index ≤ 4 ^ depth := pow_le_pow_right' (by decide) hi
    have hstep : 4 ^ index = 4 ^ (index - 1) * 4 := by
      simpa only [Nat.sub_add_cancel (Nat.pos_of_ne_zero hz)] using pow_succ 4 (index - 1)
    have hsmall : 0 < 4 ^ (index - 1) := pow_pos (by decide) _
    simp only [offset, ite_eq_right hz]; omega

private theorem offset_strictMono (depth : ℕ) : StrictMono (offset depth) := by
  intro i j hij
  by_cases hi : i = 0
  · have hp : 0 < 4 ^ (j - 1) := pow_pos (by decide) _
    simp only [offset, ite_eq_left hi, ite_eq_right (show j ≠ 0 by omega)]; omega
  · have hp : 4 ^ (i - 1) < 4 ^ (j - 1) := Nat.pow_lt_pow_right (by decide) (by omega)
    have hpos : 0 < 4 ^ depth := pow_pos (by decide) _
    simp only [offset, ite_eq_right hi, ite_eq_right (show j ≠ 0 by omega)]; omega

/-- Closed coordinates form a strictly increasing sequence. -/
private theorem coordinate_strictMono {phaseScale : ℕ} (hs : 0 < phaseScale) (depth : ℕ) :
    StrictMono (coordinate phaseScale depth) :=
  fun _ _ hij => Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left (offset_strictMono depth hij) hs) _

/-- Every selected coordinate lies strictly inside its phase's board. -/
private theorem coordinate_bounds {phaseScale depth index : ℕ} (hs : 0 < phaseScale)
    (hi : index ≤ depth) :
    2 * (phaseScale * 4 ^ depth) + 1 < coordinate phaseScale depth index ∧
      coordinate phaseScale depth index < 6 * (phaseScale * 4 ^ depth) := by
  obtain ⟨hpos, hbound⟩ := offset_bounds depth index hi
  dsimp only [coordinate]
  constructor <;> nlinarith

/-- The first line passes through the persistent northeast marker. -/
private theorem coordinate_zero (phaseScale depth : ℕ) :
    coordinate phaseScale depth 0 = 4 * phaseScale * 4 ^ depth + 1 := by
  simp only [coordinate, offset, ↓reduceIte]; ring

/-- The two new descendants of the first offset, and the unique descendant of each tail offset. -/
private theorem offset_children (depth index : ℕ) :
    offset (depth + 1) index =
      if index = 0 then 4 * offset depth 0
      else if index = 1 then 4 * offset depth 0 + 1
      else 4 * offset depth (index - 1) + 3 := by
  rcases index with _ | _ | index
  · simp [offset, pow_succ]; omega
  · simp [offset, pow_succ]; omega
  · have hp : 0 < 4 ^ depth := pow_pos (by decide) _
    have hq : 0 < 4 ^ index := pow_pos (by decide) _
    simp only [offset, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Nat.reduceEqDiff, Nat.add_sub_cancel, pow_succ]
    omega

/-- The geometric axis of a free-line scan. -/
private inductive LineAxis where
  | row
  | column
  deriving DecidableEq

/-- No selected obstruction along a quarter row or column. -/
private def clear (axis : LineAxis) (flipped : Bool) (node : Node) (along fixed : ℕ) : Prop :=
  let x := if axis = .column then fixed else along
  let y := if axis = .column then along else fixed
  let raw := node.block.at (x % 2) (y % 2)
  let state := if flipped then ShadeState.flip raw else raw
  if axis = .column then
    selectedHorizontalFor (components node.parent).thick
      (quadrantAt x y) state = none
  else selectedVerticalFor (components node.parent).thick
      (quadrantAt x y) state = none

private def fineNode (axis : LineAxis) (node : Node) (along fixed : ℕ) : Node :=
  node.child (if axis = .column then childPosition (fixed / 2) (along / 2)
    else childPosition (along / 2) (fixed / 2))

private def fineClear (axis : LineAxis) (flipped : Bool) (node : Node) (along fixed : ℕ) : Prop :=
  clear axis flipped (fineNode axis node along fixed) along fixed

private instance (axis : LineAxis) (flipped : Bool) (node : Node) (along fixed : ℕ) :
    Decidable (clear axis flipped node along fixed) := by
  unfold clear
  infer_instance

private instance (axis : LineAxis) (flipped : Bool) (node : Node) (along fixed : ℕ) :
    Decidable (fineClear axis flipped node along fixed) := by
  unfold fineClear
  infer_instance

private local instance (P : LineAxis → Prop) [Decidable (P .row)] [Decidable (P .column)] :
    Decidable (∀ a, P a) :=
  decidable_of_iff (P .row ∧ P .column)
    ⟨fun ⟨h1, h2⟩ a => LineAxis.casesOn a h1 h2, fun h => ⟨h .row, h .column⟩⟩

private local instance {n : ℕ} (P : Fin n → Prop) [∀ i, Decidable (P i)] :
    Decidable (∀ i : Fin n, P i) :=
  decidable_of_iff ((List.finRange n).all (fun i => decide (P i)) = true)
    ⟨fun h i => of_decide_eq_true ((List.all_eq_true.mp h) i (List.mem_finRange i)),
     fun h => List.all_eq_true.mpr fun i _ => decide_eq_true (h i)⟩

/-- Complete direct semantic obligations used by the even line recurrence. -/
private def EvenRules (node : Node) : Prop :=
  ∀ axis : LineAxis,
    ((∀ a : Fin 2, clear axis true node a 0) →
      ∀ a : Fin 8, fineClear axis true node a 0) ∧
    ((∀ a : Fin 2, clear axis true node a 1) →
      ∀ a : Fin 8, fineClear axis true node a 1 ∧ fineClear axis true node a 2) ∧
    (∀ a : Fin 6, ∀ fixed : Fin 3, fineClear axis true node (a.val + 2) fixed) ∧
    (∀ a : Fin 2, clear axis true (node.child 10) a 1)

/-- Irredundant core of `EvenRules`, checking `a ∈ {2, …, 7}` once in the third conjunct. -/
private def EvenRulesCore (node : Node) : Prop :=
  ∀ axis : LineAxis,
    ((∀ a : Fin 2, clear axis true node a 0) →
      ∀ a : Fin 2, fineClear axis true node a 0) ∧
    ((∀ a : Fin 2, clear axis true node a 1) →
      ∀ a : Fin 2, fineClear axis true node a 1 ∧ fineClear axis true node a 2) ∧
    (∀ a : Fin 6, ∀ fixed : Fin 3, fineClear axis true node (a.val + 2) fixed) ∧
    (∀ a : Fin 2, clear axis true (node.child 10) a 1)

private instance (node : Node) : Decidable (EvenRulesCore node) := by
  unfold EvenRulesCore
  infer_instance

section

private def evenChunk (b : ℕ) : Bool :=
  (List.range 78).all fun k =>
    decide (EvenRulesCore ⟨⟨(78 * b + k) % 312, Nat.mod_lt _ (by decide)⟩⟩)

private theorem even_checked0 : evenChunk 0 = true := by decide +kernel
private theorem even_checked1 : evenChunk 1 = true := by decide +kernel
private theorem even_checked2 : evenChunk 2 = true := by decide +kernel
private theorem even_checked3 : evenChunk 3 = true := by decide +kernel

private theorem evenRules (node : Node) : EvenRules node := by
  rcases node with ⟨⟨k, hk⟩⟩
  have hchunk : evenChunk (k / 78) = true := by
    rcases (show k / 78 = 0 ∨ k / 78 = 1 ∨ k / 78 = 2 ∨ k / 78 = 3 by omega) with h | h | h | h <;>
      rw [h]
    exacts [even_checked0, even_checked1, even_checked2, even_checked3]
  have hcore : EvenRulesCore ⟨⟨k, hk⟩⟩ := by
    simpa only [show (78 * (k / 78) + k % 78) % 312 = k by omega, decide_eq_true_eq] using
      (List.all_eq_true.mp hchunk) (k % 78) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  intro axis
  obtain ⟨h0, h1, htail, h10⟩ := hcore axis
  refine ⟨fun hc a => ?_, fun hc a => ?_, htail, h10⟩
  · by_cases ha : a.val < 2
    · exact h0 hc ⟨a.val, ha⟩
    · simpa only [show a.val - 2 + 2 = a.val by omega] using
        htail ⟨a.val - 2, by omega⟩ ⟨0, by decide⟩
  · by_cases ha : a.val < 2
    · exact h1 hc ⟨a.val, ha⟩
    · let idx : Fin 6 := ⟨a.val - 2, by omega⟩
      simpa only [idx, show a.val - 2 + 2 = a.val by omega] using
        And.intro (htail idx ⟨1, by decide⟩) (htail idx ⟨2, by decide⟩)

private def rowEven : List ℕ :=
  [260, 253, 252, 222, 262, 177, 176, 79, 174, 77, 156, 186, 158, 184, 11, 250, 73, 224]

private def rowOdd : List ℕ :=
  [189, 291, 279, 289, 173, 290, 280, 270, 305, 304, 303, 193, 269, 249, 264, 298, 178, 296, 171,
    284, 225, 282, 159, 242, 243, 191, 187, 254, 274, 226, 205, 139, 194, 128]

private def rowBoundaryEven : List ℕ :=
  [261, 185]

private def rowBoundaryOdd : List ℕ :=
  [95, 24, 22, 93]

private def columnEven : List ℕ :=
  [274, 253, 249, 166, 193, 191, 177, 173, 78, 171, 72, 237, 280, 272, 10, 243, 9, 190]

private def columnOdd : List ℕ :=
  [148, 305, 181, 298, 176, 291, 287, 284, 262, 257, 214, 252, 301, 186, 212, 289, 275, 282, 250,
    303, 244, 296, 208, 265, 174, 227, 184, 142, 146, 260, 162, 131, 233, 197]

private def columnBoundaryEven : List ℕ :=
  [278, 192]

private def columnBoundaryOdd : List ℕ :=
  [124, 108, 106, 122]

private def interiorClass (axis : LineAxis) (odd : Bool) : List ℕ :=
  if axis = .column then (if odd then columnOdd else columnEven)
  else (if odd then rowOdd else rowEven)

private def boundaryClass (axis : LineAxis) (odd : Bool) : List ℕ :=
  if axis = .column then (if odd then columnBoundaryOdd else columnBoundaryEven)
  else (if odd then rowBoundaryOdd else rowBoundaryEven)

private def classChild (axis : LineAxis) (node : Node) (along fixed : Fin 4) : Node :=
  node.child (if axis = .column then childPosition fixed along else childPosition along fixed)

/-- The source's three transitions: even→even at 0, even→odd at 1, odd→odd at 3. -/
private structure Transition where
  old : Bool
  new : Bool
  fixed : Fin 4

/-- The three geometric recurrence steps for an odd-phase strip. -/
private inductive StripStep where
  | evenToEven
  | evenToOdd
  | oddToOdd
  deriving DecidableEq

private def transition : StripStep → Transition
  | .evenToEven => ⟨false, false, 0⟩
  | .evenToOdd => ⟨false, true, 1⟩
  | .oddToOdd => ⟨true, true, 3⟩

private theorem odd_clear_mem : ∀ axis : LineAxis, ∀ odd : Bool,
    ∀ k ∈ interiorClass axis odd, ∀ hk : k < 312,
      ∀ along : Fin 2, clear axis false ⟨⟨k, hk⟩⟩ along 1 := by
  decide +kernel

private theorem odd_clear : ∀ axis : LineAxis, ∀ odd : Bool, ∀ node : Node,
    node.code.val ∈ interiorClass axis odd →
      ∀ along : Fin 2, clear axis false node along 1 :=
  fun axis odd ⟨⟨k, hk⟩⟩ hmem => odd_clear_mem axis odd k hmem hk

private theorem odd_transitions_mem :
    ∀ axis : LineAxis, ∀ which ∈ [StripStep.evenToEven, .evenToOdd, .oddToOdd],
      let step := transition which
      (∀ k ∈ interiorClass axis step.old, ∀ hk : k < 312,
        ∀ along : Fin 4, (classChild axis ⟨⟨k, hk⟩⟩ along step.fixed).code.val ∈
          interiorClass axis step.new) ∧
      (∀ k ∈ boundaryClass axis step.old, ∀ hk : k < 312,
        (classChild axis ⟨⟨k, hk⟩⟩ 0 step.fixed).code.val ∈ boundaryClass axis step.new ∧
        ∀ along : Fin 3,
          (classChild axis ⟨⟨k, hk⟩⟩ ⟨along.val + 1, by omega⟩ step.fixed).code.val ∈
          interiorClass axis step.new) := by
  decide +kernel

private theorem odd_transitions : ∀ axis : LineAxis, ∀ which : StripStep, ∀ node : Node,
    let step := transition which
    (node.code.val ∈ interiorClass axis step.old →
      ∀ along : Fin 4, (classChild axis node along step.fixed).code.val ∈
        interiorClass axis step.new) ∧
    (node.code.val ∈ boundaryClass axis step.old →
      (classChild axis node 0 step.fixed).code.val ∈ boundaryClass axis step.new ∧
      ∀ along : Fin 3,
        (classChild axis node ⟨along.val + 1, by omega⟩ step.fixed).code.val ∈
        interiorClass axis step.new) := by
  intro axis which ⟨⟨k, hk⟩⟩
  have h := odd_transitions_mem axis which (by cases which <;> decide)
  exact ⟨fun hi => h.1 k hi hk, fun hb => h.2 k hb hk⟩

private theorem odd_base (axis : LineAxis) :
    (∀ along : Fin 3,
      (if axis = .column then supertileNodeGrid 2 seedNode 4 (along.val + 3)
        else supertileNodeGrid 2 seedNode (along.val + 3) 4).code.val ∈
        interiorClass axis false) ∧
    (if axis = .column then supertileNodeGrid 2 seedNode 4 2
      else supertileNodeGrid 2 seedNode 2 4).code.val ∈ boundaryClass axis false := by
  cases axis <;> decide +kernel

private theorem source_dark : ∀ node : Node,
    (supertileShadeGrid 1 node 4 3).west = some .dark := by
  decide +kernel

private theorem odd_cycle_colours :
    (supertileShadeGrid 2 seedNode 5 5).east = some .light ∧
    (supertileShadeGrid 2 seedNode 12 5).west = some .light ∧
    (supertileShadeGrid 2 seedNode 12 12).west = some .light ∧
    (supertileShadeGrid 2 seedNode 5 12).east = some .light := by
  decide +kernel

end

private def canonicalStates (flipped : Bool) (level : ℕ) (root : Node) :
    ℕ → ℕ → ShadeState := fun x y =>
  if flipped then ShadeState.flip (supertileShadeGrid level root x y)
    else supertileShadeGrid level root x y

private theorem canonical_valid (flipped : Bool) (level : ℕ) (root : Node) :
    ShadeValidOn (supertileIndexGrid level root) (canonicalStates flipped level root)
      (2 * 4 ^ level) (2 * 4 ^ level) := by
  have valid := supertile_validShadeRectangle level root
  cases flipped
  · exact valid
  · exact ⟨fun x y hx hy => ShadeState.flip_allowed (valid.allowed x y hx hy),
      fun x y hx hy => congrArg (Option.map Shade.opposite) (valid.hmatch x y hx hy),
      fun x y hx hy => congrArg (Option.map Shade.opposite) (valid.vmatch x y hx hy)⟩

private theorem canonicalStates_sparse (flipped : Bool) (level : ℕ) (root : Node) (p : Port) :
    value (canonicalStates flipped (level + 1) root) (sparsePort p) =
      value (canonicalStates flipped level root) p := by
  cases p with
  | mk x y side =>
    cases side <;> simp [value, canonicalStates, sparsePort, supertileShadeGrid_sparse]

private theorem canonicalStates_block (flipped : Bool) (level : ℕ) (root : Node)
    (bx by₀ : ℕ) (p : Port) (hx : p.x < 8) (hy : p.y < 8) :
    value (canonicalStates flipped (level + 1) root)
      (translatePort p (8 * bx) (8 * by₀)) =
      value (canonicalStates flipped 1 (supertileNodeGrid level root bx by₀)) p := by
  cases p with
  | mk x y side =>
    cases side <;> simp [value, canonicalStates, translatePort,
      supertileShadeGrid_block level root bx by₀ x y hx hy]

private def nodeAt (axis : LineAxis) (level : ℕ) (root : Node) (along fixed : ℕ) : Node :=
  if axis = .column then supertileNodeGrid level root fixed along
  else supertileNodeGrid level root along fixed

private def clearAt (axis : LineAxis) (flipped : Bool) (level : ℕ) (root : Node)
    (along fixed : ℕ) : Prop :=
  clear axis flipped (nodeAt axis level root (along / 2) (fixed / 2))
    (along % 2) (fixed % 2)

private def LineFree (axis : LineAxis) (phase depth : ℕ) (flipped : Bool)
    (root : Node) (fixed : ℕ) : Prop :=
  ∀ along, 2 * (phase * 4 ^ depth) + 1 < along →
    along < 6 * (phase * 4 ^ depth) → clearAt axis flipped (depth + phase) root along fixed

private theorem clearAt_succ_block (axis : LineAxis) (flipped : Bool) (level : ℕ) (root : Node)
    (blockAlong blockFixed along fixed : ℕ) (ha : along < 8) (hf : fixed < 8) :
    clearAt axis flipped (level + 1) root (8 * blockAlong + along)
      (8 * blockFixed + fixed) ↔
      fineClear axis flipped (nodeAt axis level root blockAlong blockFixed) along fixed := by
  have ha2 : (8 * blockAlong + along) % 2 = along % 2 := by omega
  have hf2 : (8 * blockFixed + fixed) % 2 = fixed % 2 := by omega
  cases axis <;> simp only [clearAt, nodeAt, reduceCtorEq, ↓reduceIte] <;>
  · rw [show (8 * blockAlong + along) / 2 = 4 * blockAlong + along / 2 by omega,
      show (8 * blockFixed + fixed) / 2 = 4 * blockFixed + fixed / 2 by omega,
      supertileNodeGrid_block _ _ _ _ _ _ (by omega) (by omega)]
    simp [fineClear, fineNode, clear, ha2, hf2, quadrantAt]

private theorem even_base (axis : LineAxis) (root : Node) :
    LineFree axis 1 0 true root 5 := by
  intro along hlo hhi
  have hdiv : along / 2 = 2 := by norm_num at hlo hhi; omega
  have h := (evenRules root axis).2.2.2 ⟨along % 2, Nat.mod_lt _ (by decide)⟩
  cases axis <;> simpa [LineFree, clearAt, nodeAt, hdiv, supertileNodeGrid,
    childPosition, blockPosition, clear, quadrantAt] using h

private theorem even_refine {axis : LineAxis} {root : Node} {depth old child fixed : ℕ}
    (oldFree : LineFree axis 1 depth true root old)
    (hchild : child = 8 * (old / 2) + fixed) (hfixed : fixed < 3)
    (refines : ∀ node : Node,
      (∀ along : Fin 2, clear axis true node along (old % 2)) →
      ∀ along : Fin 8, fineClear axis true node along fixed) :
    LineFree axis 1 (depth + 1) true root child := by
  intro along lower upper
  have hlocal : along % 8 < 8 := Nat.mod_lt _ (by decide)
  simp only [Nat.one_mul, pow_succ] at lower upper
  rw [show along = 8 * (along / 8) + along % 8 by omega, hchild]
  apply (clearAt_succ_block axis true (depth + 1) root _ _ _ _ hlocal (by omega)).2
  by_cases hb : along / 8 = 4 ^ depth
  · have hlocalLower : 2 ≤ along % 8 := by omega
    simpa only [show along % 8 - 2 + 2 = along % 8 by omega] using
      (evenRules (nodeAt axis (depth + 1) root (along / 8) (old / 2)) axis).2.2.1
        ⟨along % 8 - 2, by omega⟩ ⟨fixed, hfixed⟩
  · refine refines _ (fun a => ?_) ⟨along % 8, hlocal⟩
    have hparent := oldFree (2 * (along / 8) + a.val)
      (by simp only [Nat.one_mul]; omega) (by simp only [Nat.one_mul]; omega)
    simpa only [clearAt, show (2 * (along / 8) + a.val) / 2 = along / 8 by omega,
      show (2 * (along / 8) + a.val) % 2 = a.val by omega] using hparent

private theorem even_child {axis : LineAxis} {root : Node} {depth old child : ℕ}
    (hold : LineFree axis 1 depth true root (2 * 4 ^ depth + 1 + old))
    (hchild : (old % 2 = 0 ∧ (child = 4 * old ∨ child = 4 * old + 1)) ∨
      (old % 2 = 1 ∧ child = 4 * old + 3)) :
    LineFree axis 1 (depth + 1) true root (2 * 4 ^ (depth + 1) + 1 + child) := by
  have step (fixed parity : ℕ) (hfixed : fixed < 3)
      (hp : (2 * 4 ^ depth + 1 + old) % 2 = parity)
      (hc : 2 * 4 ^ (depth + 1) + 1 + child = 8 * ((2 * 4 ^ depth + 1 + old) / 2) + fixed)
      (certificate : ∀ node : Node,
        (∀ along : Fin 2, clear axis true node along parity) →
          ∀ along : Fin 8, fineClear axis true node along fixed) :=
    even_refine hold hc hfixed (by simpa only [hp] using certificate)
  rcases hchild with ⟨hparity, rfl | rfl⟩ | ⟨hparity, rfl⟩
  · exact step 1 1 (by decide) (by omega) (by rw [pow_succ]; omega)
      (fun node hclear along => ((evenRules node axis).2.1 hclear along).1)
  · exact step 2 1 (by decide) (by omega) (by rw [pow_succ]; omega)
      (fun node hclear along => ((evenRules node axis).2.1 hclear along).2)
  · exact step 0 0 (by decide) (by omega) (by rw [pow_succ]; omega)
      (fun node hclear along => (evenRules node axis).1 hclear along)

private theorem offset_parity (depth index : ℕ) :
    offset depth index % 2 = if index = 0 then 0 else 1 := by
  by_cases h : index = 0
  · simp [offset, h]
  · have hp : 0 < 4 ^ depth := pow_pos (by decide) _
    have hq : 0 < 4 ^ (index - 1) := pow_pos (by decide) _
    simp only [offset, ite_eq_right h]; omega

private theorem offset_parent {depth index : ℕ} (hi : index ≤ depth + 1) :
    ∃ previous, previous ≤ depth ∧
      ((offset depth previous % 2 = 0 ∧
        (offset (depth + 1) index = 4 * offset depth previous ∨
         offset (depth + 1) index = 4 * offset depth previous + 1)) ∨
      (offset depth previous % 2 = 1 ∧
        offset (depth + 1) index = 4 * offset depth previous + 3)) := by
  by_cases hz : index = 0
  · exact ⟨0, Nat.zero_le _, Or.inl ⟨by simp [offset_parity],
      Or.inl (by simp [offset_children, hz])⟩⟩
  · by_cases ho : index = 1
    · exact ⟨0, Nat.zero_le _, Or.inl ⟨by simp [offset_parity],
        Or.inr (by simp [offset_children, ho])⟩⟩
    · exact ⟨index - 1, by omega, Or.inr ⟨by simp [offset_parity, show index - 1 ≠ 0 by omega],
        by simp [offset_children, hz, ho]⟩⟩

private theorem even_free (axis : LineAxis) (root : Node) (depth index : ℕ)
    (hi : index ≤ depth) : LineFree axis 1 depth true root (coordinate 1 depth index) := by
  induction depth generalizing index with
  | zero =>
      obtain rfl : index = 0 := by omega
      simpa [coordinate, offset] using even_base axis root
  | succ depth ih =>
      obtain ⟨previous, hp, hchild⟩ := offset_parent hi
      have hold := ih previous hp
      simp only [coordinate, Nat.one_mul] at hold ⊢
      exact even_child hold hchild

private def stripNode (axis : LineAxis) (depth offset along : ℕ) : Node :=
  nodeAt axis (depth + 2) seedNode along (2 * 4 ^ depth + offset)

private def StripClassified (axis : LineAxis) (odd : Bool) (depth offset : ℕ) : Prop :=
  (∀ along, 2 * 4 ^ depth < along → along < 6 * 4 ^ depth →
    (stripNode axis depth offset along).code.val ∈ interiorClass axis odd) ∧
  (stripNode axis depth offset (2 * 4 ^ depth)).code.val ∈ boundaryClass axis odd

private theorem stripNode_succ (axis : LineAxis) {depth old child : ℕ} (fixed : Fin 4)
    (hc : child = 4 * old + fixed.val) (along : ℕ) :
    stripNode axis (depth + 1) child along =
      classChild axis (stripNode axis depth old (along / 4))
        ⟨along % 4, Nat.mod_lt _ (by decide)⟩ fixed := by
  have hd : (2 * 4 ^ (depth + 1) + child) / 4 = 2 * 4 ^ depth + old := by rw [hc, pow_succ]; omega
  have hm : (2 * 4 ^ (depth + 1) + child) % 4 = fixed.val := by rw [hc, pow_succ]; omega
  cases axis <;>
    simp [stripNode, nodeAt, supertileNodeGrid, classChild, childPosition, hd, hm,
      Nat.mod_eq_of_lt fixed.isLt]

private theorem strip_step {axis : LineAxis} {depth old child : ℕ} (which : StripStep)
    (hold : StripClassified axis (transition which).old depth old)
    (hc : child = 4 * old + (transition which).fixed.val) :
    StripClassified axis (transition which).new (depth + 1) child := by
  constructor
  · intro along hlo hhi
    rw [pow_succ] at hlo hhi
    rw [stripNode_succ axis _ hc]
    have checked := odd_transitions axis which (stripNode axis depth old (along / 4))
    by_cases hb : along / 4 = 2 * 4 ^ depth
    · have hlocal : 0 < along % 4 := by omega
      simpa only [Fin.val_mk, show along % 4 - 1 + 1 = along % 4 by omega] using
        (checked.2 (hb ▸ hold.2)).2 ⟨along % 4 - 1, by omega⟩
    · exact checked.1 (hold.1 _ (by omega) (by omega)) _
  · rw [stripNode_succ axis _ hc]
    have hd : (2 * 4 ^ (depth + 1)) / 4 = 2 * 4 ^ depth := by rw [pow_succ]; omega
    have hm : (2 * 4 ^ (depth + 1)) % 4 = 0 := by rw [pow_succ]; omega
    simp only [hd, hm]
    exact ((odd_transitions axis which _).2 hold.2).1

private theorem odd_classified (axis : LineAxis) (depth index : ℕ) (hi : index ≤ depth) :
    StripClassified axis (decide (index ≠ 0)) depth (offset depth index) := by
  induction depth generalizing index with
  | zero =>
      obtain rfl : index = 0 := by omega
      constructor
      · intro along hlo hhi
        norm_num at hlo hhi
        have h := (odd_base axis).1 ⟨along - 3, by omega⟩
        cases axis <;>
          simpa [stripNode, nodeAt, offset, show along - 3 + 3 = along by omega] using h
      · have h := (odd_base axis).2
        cases axis <;> simpa [stripNode, nodeAt, offset] using h
  | succ depth ih =>
      have go (which : StripStep) (prev : ℕ) (hp : prev ≤ depth)
          (hodd : (transition which).old = decide (prev ≠ 0))
          (hnew : (transition which).new = decide (index ≠ 0))
          (hoff : offset (depth + 1) index =
            4 * offset depth prev + (transition which).fixed.val) :=
        hnew ▸ strip_step (which := which) (hodd ▸ ih prev hp) hoff
      rcases index with _ | _ | index
      · exact go .evenToEven 0 (Nat.zero_le _) rfl rfl (by simp [offset_children, transition])
      · exact go .evenToOdd 0 (Nat.zero_le _) rfl rfl (by simp [offset_children, transition])
      · exact go .oddToOdd (index + 1) (by omega) rfl rfl (by simp [offset_children, transition])

private theorem odd_free (axis : LineAxis) (depth index : ℕ) (hi : index ≤ depth) :
    LineFree axis 2 depth false seedNode (coordinate 2 depth index) := by
  intro along hlo hhi
  have hmem := (odd_classified axis depth index hi).1 (along / 2) (by omega) (by omega)
  have hd : coordinate 2 depth index / 2 = 2 * 4 ^ depth + offset depth index := by
    dsimp only [coordinate]; omega
  have hm : coordinate 2 depth index % 2 = 1 := by dsimp only [coordinate]; omega
  simpa only [clearAt, hd, hm, stripNode] using
    odd_clear axis (decide (index ≠ 0)) (stripNode axis depth (offset depth index) (along / 2))
      hmem ⟨along % 2, Nat.mod_lt _ (by decide)⟩

private theorem state_eq_of_present_eq {grid other : ℕ → ℕ → Index}
    {actual canonical : ℕ → ℕ → ShadeState} {x y : ℕ}
    (valid : ValidShadeGrid grid actual)
    (allowed : locallyAllowed
      ⟨other (x / 2) (y / 2), quadrantAt x y⟩ (canonical x y) = true)
    (geometry : componentAt other x y = componentAt grid x y)
    (agree : ∀ side, portPresent grid ⟨x, y, side⟩ = true →
      value actual ⟨x, y, side⟩ = value canonical ⟨x, y, side⟩) :
    actual x y = canonical x y := by
  have values (side : Side) : value actual ⟨x, y, side⟩ = value canonical ⟨x, y, side⟩ := by
    by_cases hp : portPresent grid ⟨x, y, side⟩ = true
    · exact agree side hp
    · have hg : portPresent other ⟨x, y, side⟩ = portPresent grid ⟨x, y, side⟩ := by
        cases side <;> simp only [portPresent] <;> rw [geometry]
      have ha := value_isSome_eq_portPresent valid ⟨x, y, side⟩
      have hc := value_isSome_eq_portPresent_of_allowed ⟨x, y, side⟩ allowed
      cases hactual : value actual ⟨x, y, side⟩ <;>
        cases hcanonical : value canonical ⟨x, y, side⟩ <;> simp_all
  have hw := values .west; have he := values .east
  have hs := values .south; have hn := values .north
  cases ha : actual x y; cases hc : canonical x y
  simp only [value, ha, hc] at hw he hs hn; congr

private theorem sparse_block {bx by₀ : ℕ} {p : Port} (hx : p.x < 2) (hy : p.y < 2) :
    sparsePort (translatePort p (2 * bx) (2 * by₀)) =
      translatePort (sparsePort p) (8 * bx) (8 * by₀) := by
  rcases p with ⟨x, y, side⟩
  simp only [sparsePort, sparseCoordinate, translatePort, Port.mk.injEq]
  exact ⟨by omega, by omega, trivial⟩

/-- Data for the two-level shade comparison in the even and odd canonical phases. -/
private structure RefinementComparison where
  scale : ℕ → ℕ
  grid : ℕ → ℕ → ℕ → Index
  states : ℕ → ℕ → ℕ → ShadeState
  localStates : ℕ → ℕ → ℕ → ℕ → ℕ → ShadeState
  scale_succ : ∀ d, scale (d + 1) = 4 * scale d
  grid_succ : ∀ d, iterateRefine 2 (grid d) = grid (d + 1)
  cycle : ∀ d, CycleOn (grid d) (scale d) (3 * scale d) (scale d) (3 * scale d)
  base : ∀ actual, ValidShadeGrid (grid 0) actual →
    CycleShade actual (scale 0) (3 * scale 0) (scale 0) (3 * scale 0) .light →
    ∀ p, 2 * scale 0 ≤ p.x → p.x < 6 * scale 0 →
      2 * scale 0 ≤ p.y → p.y < 6 * scale 0 → portPresent (grid 0) p = true →
      value actual p = value (states 0) p
  local_sound : ∀ d bx by₀, scale d ≤ bx → bx < 3 * scale d →
    scale d ≤ by₀ → by₀ < 3 * scale d → ∀ {a b parity},
    BoundedPath (fineGrid (grid d bx by₀)) 8 8 a b parity →
    Related parity (value (localStates d bx by₀) a) (value (localStates d bx by₀) b)
  block : ∀ d bx by₀ p, p.x < 8 → p.y < 8 →
    value (states (d + 1)) (translatePort p (8 * bx) (8 * by₀)) =
      value (localStates d bx by₀) p
  sparse : ∀ d p, value (states (d + 1)) (sparsePort p) = value (states d) p
  new_source : ∀ d actual bx by₀, ValidShadeGrid (grid (d + 1)) actual →
    CycleShade actual (scale (d + 1)) (3 * scale (d + 1))
      (scale (d + 1)) (3 * scale (d + 1)) .light →
    scale d ≤ bx → bx < 3 * scale d → scale d ≤ by₀ → by₀ < 3 * scale d →
    value actual (translatePort cycleSource (8 * bx) (8 * by₀)) =
      value (localStates d bx by₀) cycleSource

private theorem RefinementComparison.agreement_sparse (C : RefinementComparison)
    {d : ℕ} {actual : ℕ → ℕ → ShadeState}
    (validFine : ValidShadeGrid (iterateRefine 2 (C.grid d)) actual)
    (ih : ∀ p, 2 * C.scale d ≤ p.x → p.x < 6 * C.scale d →
      2 * C.scale d ≤ p.y → p.y < 6 * C.scale d → portPresent (C.grid d) p = true →
      value (coarsen actual) p = value (C.states d) p)
    {bx by₀ : ℕ} {old : Port} (hbx : C.scale d ≤ bx) (hbX : bx < 3 * C.scale d)
    (hby : C.scale d ≤ by₀) (hbY : by₀ < 3 * C.scale d)
    (oldPresent : portPresent (coarseGrid (C.grid d bx by₀)) old = true)
    (oldBounds : old.x < 2 ∧ old.y < 2)
    (sourceBounds : (sparsePort old).x < 8 ∧ (sparsePort old).y < 8) :
    value actual (translatePort (sparsePort old) (8 * bx) (8 * by₀)) =
      value (C.localStates d bx by₀) (sparsePort old) := by
  let oldGlobal := translatePort old (2 * bx) (2 * by₀)
  have oldGlobalPresent : portPresent (C.grid d) oldGlobal = true := by
    have heq := portPresent_local (C.grid d) oldGlobal
    simp only [oldGlobal, translatePort,
      show (2 * bx + old.x) / 2 = bx by omega, show (2 * by₀ + old.y) / 2 = by₀ by omega,
      show (2 * bx + old.x) % 2 = old.x by omega,
      show (2 * by₀ + old.y) % 2 = old.y by omega] at heq
    exact heq.symm.trans oldPresent
  have previous := ih oldGlobal
    (by dsimp only [oldGlobal, translatePort]; omega)
    (by dsimp only [oldGlobal, translatePort]; omega)
    (by dsimp only [oldGlobal, translatePort]; omega)
    (by dsimp only [oldGlobal, translatePort]; omega) oldGlobalPresent
  have sparseActual : value actual (sparsePort oldGlobal) = value (C.states d) oldGlobal :=
    Eq.trans ((livePortPath (C.grid d) oldGlobal oldGlobalPresent).sound validFine)
      ((value_coarsen actual oldGlobal).symm.trans previous)
  have blockValue := C.block d bx by₀ (sparsePort old) sourceBounds.1 sourceBounds.2
  rw [← sparse_block (bx := bx) (by₀ := by₀) oldBounds.1 oldBounds.2] at blockValue ⊢
  exact sparseActual.trans ((C.sparse d oldGlobal).symm.trans blockValue)

private theorem RefinementComparison.agreement (C : RefinementComparison) :
    ∀ d actual, ValidShadeGrid (C.grid d) actual →
    CycleShade actual (C.scale d) (3 * C.scale d) (C.scale d) (3 * C.scale d) .light →
    ∀ p, 2 * C.scale d ≤ p.x → p.x < 6 * C.scale d →
      2 * C.scale d ≤ p.y → p.y < 6 * C.scale d → portPresent (C.grid d) p = true →
      value actual p = value (C.states d) p := by
  intro d
  induction d with
  | zero => exact C.base
  | succ d ih =>
      intro actual valid shaded p hpx hpX hpy hpY present
      have validFine : ValidShadeGrid (iterateRefine 2 (C.grid d)) actual :=
        (C.grid_succ d).symm ▸ valid
      let bx := p.x / 8; let by₀ := p.y / 8
      let localPort : Port := ⟨p.x % 8, p.y % 8, p.side⟩
      have hx : localPort.x < 8 := Nat.mod_lt _ (by decide)
      have hy : localPort.y < 8 := Nat.mod_lt _ (by decide)
      have hlocation : translatePort localPort (8 * bx) (8 * by₀) = p := by
        rcases p with ⟨x, y, side⟩
        simp only [localPort, bx, by₀, translatePort, Port.mk.injEq]
        exact ⟨by omega, by omega, trivial⟩
      have localPresent : portPresent (fineGrid (C.grid d bx by₀)) localPort = true := by
        rwa [portPresent_two_block (C.grid d) bx by₀ localPort hx hy, C.grid_succ, hlocation]
      obtain ⟨source, hsource, parity, path⟩ :=
        exists_boundedPath (C.grid d bx by₀) (mem_portsIn_iff.mpr ⟨hx, hy⟩) localPresent
      have actualPath := boundedPath_two_block (C.grid d) bx by₀ path
      rw [C.grid_succ, hlocation] at actualPath
      have ⟨hbx, hbX, hby, hbY⟩ :
          C.scale d ≤ bx ∧ bx < 3 * C.scale d ∧ C.scale d ≤ by₀ ∧ by₀ < 3 * C.scale d := by
        rw [C.scale_succ] at hpx hpX hpy hpY; dsimp only [bx, by₀]; omega
      have finish (h : value actual (translatePort source (8 * bx) (8 * by₀)) =
          value (C.localStates d bx by₀) source) :
          value actual p = value (C.states (d + 1)) p := by
        have rel1 := actualPath.sound valid
        have rel2 := C.local_sound d bx by₀ hbx hbX hby hbY path
        rw [h] at rel1
        rw [← C.block d bx by₀ localPort hx hy, hlocation] at rel2
        exact Related.right_unique rel1 rel2
      rcases source_cases hsource with heq | ⟨old, _, oldPresent, heq⟩
      · subst source
        exact finish (C.new_source d actual bx by₀ valid shaded hbx hbX hby hbY)
      · subst source
        have coarseShaded : CycleShade (coarsen actual) (C.scale d) (3 * C.scale d)
            (C.scale d) (3 * C.scale d) .light :=
          CycleShade.coarsen validFine (C.cycle d)
            (by convert shaded using 1 <;> rw [C.scale_succ] <;> omega)
        have sourceBounds := path.first_inBounds
        have oldBounds : old.x < 2 ∧ old.y < 2 := by
          dsimp only [PortInBounds, sparsePort, sparseCoordinate] at sourceBounds; omega
        exact finish (C.agreement_sparse validFine
          (ih (coarsen actual) (ValidShadeGrid.coarsen validFine) coarseShaded)
          hbx hbX hby hbY oldPresent oldBounds sourceBounds)

private theorem canonical_source (flipped : Bool) (node : Node) :
    value (canonicalStates flipped 1 node) cycleSource =
      some (if flipped then .light else .dark) := by
  have dark := source_dark node
  cases flipped <;> simp [value, canonicalStates, ShadeState.flip, dark,
    cycleSource, Shade.opposite]

private def initialLevel (flipped : Bool) : ℕ := if flipped then 1 else 2
private def phaseScale (flipped : Bool) (depth : ℕ) : ℕ :=
  (if flipped then 1 else 2) * 4 ^ depth
private def phaseGrid (flipped : Bool) (depth : ℕ) (coarse : ℕ → ℕ → Index) :
    ℕ → ℕ → Index := iterateRefine (2 * (depth + initialLevel flipped)) coarse

private theorem phaseScale_succ (flipped : Bool) (depth : ℕ) :
    phaseScale flipped (depth + 1) = 4 * phaseScale flipped depth := by
  simp only [phaseScale, pow_succ]
  ring

private theorem phase_cycle (flipped : Bool) (depth : ℕ) (coarse : ℕ → ℕ → Index) :
    CycleOn (phaseGrid flipped depth coarse) (phaseScale flipped depth)
      (3 * phaseScale flipped depth) (phaseScale flipped depth) (3 * phaseScale flipped depth) := by
  cases flipped
  · have power : 2 ^ (2 * depth + 2 - 1) = 2 * 4 ^ depth := by
      rw [show 2 * depth + 2 - 1 = 1 + 2 * depth by omega, pow_add, pow_mul]; norm_num
    simpa only [phaseGrid, phaseScale, initialLevel, Bool.false_eq_true, ↓reduceIte,
      show 2 * depth + 2 + 2 = 2 * (depth + 2) by omega, power] using
      small_cycle coarse (2 * depth + 2) (by omega)
  · have power : 2 ^ (2 * depth) = 4 ^ depth := by norm_num [pow_mul]
    simpa only [phaseGrid, phaseScale, initialLevel, ↓reduceIte, Nat.one_mul,
      show 2 * depth + 2 = 2 * (depth + 1) by omega, power] using large_cycle coarse (2 * depth)

private theorem phase_base (flipped : Bool) (coarse : ℕ → ℕ → Index)
    (rootEq : coarse 0 0 = 0) (actual : ℕ → ℕ → ShadeState)
    (valid : ValidShadeGrid (phaseGrid flipped 0 coarse) actual)
    (shaded : CycleShade actual (phaseScale flipped 0) (3 * phaseScale flipped 0)
      (phaseScale flipped 0) (3 * phaseScale flipped 0) .light)
    (target : Port) (west : 2 * phaseScale flipped 0 ≤ target.x)
    (east : target.x < 6 * phaseScale flipped 0)
    (south : 2 * phaseScale flipped 0 ≤ target.y)
    (north : target.y < 6 * phaseScale flipped 0)
    (present : portPresent (phaseGrid flipped 0 coarse) target = true) :
    value actual target =
      value (canonicalStates flipped (initialLevel flipped) seedNode) target := by
  let level := initialLevel flipped
  let canonical := canonicalStates flipped level seedNode
  let baseGrid := iterateRefine (2 * level) (coarseGrid 0)
  have geometry (x y : ℕ) (hx : x < 2 * 4 ^ level) (hy : y < 2 * 4 ^ level) :
      componentAt baseGrid x y = componentAt (phaseGrid flipped 0 coarse) x y := by
    unfold componentAt
    rw [show baseGrid (x / 2) (y / 2) = phaseGrid flipped 0 coarse (x / 2) (y / 2) from by
      simpa only [baseGrid, phaseGrid, Nat.zero_add] using
        iterateRefine_eq_of_root_eq (g := coarseGrid 0) (h := coarse) rootEq.symm
          (2 * level) (x / 2) (y / 2)
          (by simpa [pow_mul] using (show x / 2 < 4 ^ level by omega))
          (by simpa [pow_mul] using (show y / 2 < 4 ^ level by omega))]
  have canonicalValid : ShadeValidOn baseGrid canonical (2 * 4 ^ level) (2 * 4 ^ level) := by
    simpa only [supertileIndexGrid_eq_iterateRefine, seedNode_parent] using
      canonical_valid flipped level seedNode
  have targetBounds : target.x < 2 * 4 ^ level ∧ target.y < 2 * 4 ^ level := by
    cases flipped <;> norm_num [phaseScale, initialLevel, level] at * <;> omega
  have basePresent : portPresent baseGrid target = true := by
    rcases target with ⟨x, y, side⟩
    cases side <;> simp only [portPresent] <;>
      rw [geometry x y targetBounds.1 targetBounds.2] <;> exact present
  have finish {width : ℕ} {source : Port} {parity : Bool} (bound : width ≤ 2 * 4 ^ level)
      (path : BoundedPath baseGrid width width source target parity)
      (actualSource : value actual source = some .light)
      (canonicalSource : value canonical source = some .light) :
      value actual target = value canonical target := by
    have actualRelation := (boundedPath_translate (offsetX := 0) (offsetY := 0)
      (by decide) (by decide)
      (fun x y hx hy => by simpa only [Nat.zero_add] using geometry x y (by omega) (by omega))
      path).sound valid
    simp only [translatePort, Nat.zero_add, actualSource] at actualRelation
    have canonicalRelation := path.sound
      (fun x y hx hy => canonicalValid.allowed x y (by omega) (by omega))
      (fun x y hx hy => canonicalValid.hmatch x y (by omega) (by omega))
      (fun x y hx hy => canonicalValid.vmatch x y (by omega) (by omega))
    rw [canonicalSource] at canonicalRelation
    exact Related.right_unique actualRelation canonicalRelation
  cases flipped
  · obtain ⟨source, parity, sourceMem, path⟩ :=
      odd_base_exists_boundedPath west east south north basePresent
    simp only [List.mem_cons, List.not_mem_nil, or_false] at sourceMem
    have ok (hact : value actual source = some .light)
        (hcan : value (canonicalStates false 2 seedNode) source = some .light) :=
      finish (by decide) path hact hcan
    rcases sourceMem with rfl | rfl | rfl | rfl
    · exact ok shaded.southwest (by simpa [canonicalStates, value] using odd_cycle_colours.1)
    · exact ok shaded.southeast (by simpa [canonicalStates, value] using odd_cycle_colours.2.1)
    · exact ok shaded.northeast (by simpa [canonicalStates, value] using odd_cycle_colours.2.2.1)
    · exact ok shaded.northwest (by simpa [canonicalStates, value] using odd_cycle_colours.2.2.2)
  · obtain ⟨parity, path⟩ := base_exists_boundedPath west east south north basePresent
    exact finish (by decide) path
      (shaded.south_at (phase_cycle true 0 coarse) valid (by decide) (by decide)).1
      (canonical_source true seedNode)

private theorem phase_source (flipped : Bool) (depth : ℕ) (coarse : ℕ → ℕ → Index)
    (actual : ℕ → ℕ → ShadeState) (bx by₀ : ℕ)
    (valid : ValidShadeGrid (phaseGrid flipped (depth + 1) coarse) actual)
    (shaded : CycleShade actual (phaseScale flipped (depth + 1))
      (3 * phaseScale flipped (depth + 1))
      (phaseScale flipped (depth + 1)) (3 * phaseScale flipped (depth + 1)) .light)
    (hx : bx < 3 * phaseScale flipped depth) (hy : by₀ < 3 * phaseScale flipped depth) :
    value actual (translatePort cycleSource (8 * bx) (8 * by₀)) =
      some (if flipped then .light else .dark) := by
  let k := if flipped then 2 * (depth + 1) else 2 * (depth + 1) + 1
  let g' := if flipped then coarse else iterateRefine 1 coarse
  have valid' : ValidShadeGrid (iterateRefine (k + 2) g') actual := by
    cases flipped <;> simp only [k, g', Bool.false_eq_true, ↓reduceIte, iterateRefine_add]
    · exact (show 2 * (depth + 1) + 1 + 2 + 1 = 2 * (depth + 1 + 2) by omega) ▸ valid
    · exact (show 2 * (depth + 1) + 2 = 2 * (depth + 1 + 1) by omega) ▸ valid
  have scaleEq : 2 ^ k = phaseScale flipped (depth + 1) := by
    cases flipped <;> simp [k, phaseScale, pow_add, pow_mul]
    ring
  have h := root_descendant_source k g' valid' (by simpa only [scaleEq] using shaded) bx by₀
    (by rw [scaleEq, phaseScale_succ]; omega) (by rw [scaleEq, phaseScale_succ]; omega)
  cases flipped <;> simp only [k, Bool.false_eq_true, ↓reduceIte] at h
  · rwa [Function.Involutive.iterate_two_mul_add_one Shade.opposite_opposite] at h
  · rwa [Function.Involutive.iterate_two_mul Shade.opposite_opposite] at h

private def phaseComparison (flipped : Bool) (coarse : ℕ → ℕ → Index)
    (rootEq : coarse 0 0 = 0) : RefinementComparison where
  scale := phaseScale flipped
  grid := fun depth => phaseGrid flipped depth coarse
  states := fun depth => canonicalStates flipped (depth + initialLevel flipped) seedNode
  localStates := fun depth bx by₀ => canonicalStates flipped 1
    (supertileNodeGrid (depth + initialLevel flipped) seedNode bx by₀)
  scale_succ := phaseScale_succ flipped
  grid_succ := fun depth => by
    simp only [phaseGrid, iterateRefine_add]; congr 1; omega
  cycle := fun depth => phase_cycle flipped depth coarse
  base := fun actual valid shaded p hx hX hy hY present => by
    simpa only [Nat.zero_add] using
      phase_base flipped coarse rootEq actual valid shaded p hx hX hy hY present
  local_sound := by
    intro depth bx by₀ _ hx _ hy a b parity path
    have bound (z : ℕ) (hz : z < 3 * phaseScale flipped depth) :
        z < 4 ^ (depth + initialLevel flipped) := by
      cases flipped <;> simp [phaseScale, initialLevel, pow_add] at * <;> omega
    have parentEq : (supertileNodeGrid (depth + initialLevel flipped) seedNode bx by₀).parent =
        phaseGrid flipped depth coarse bx by₀ :=
      supertileIndexGrid_eq_of_root_eq (depth + initialLevel flipped) seedNode coarse
        (rootEq.trans seedNode_parent.symm) (bound bx hx) (bound by₀ hy)
    have finiteValid := canonical_valid flipped 1
      (supertileNodeGrid (depth + initialLevel flipped) seedNode bx by₀)
    rw [supertileIndexGrid_eq_iterateRefine, parentEq] at finiteValid
    exact path.sound finiteValid.allowed finiteValid.hmatch finiteValid.vmatch
  block := fun depth bx by₀ p hx hy => by
    simpa only [Nat.add_right_comm depth 1 (initialLevel flipped)] using
      canonicalStates_block flipped (depth + initialLevel flipped) seedNode bx by₀ p hx hy
  sparse := fun depth p => by
    simpa only [Nat.add_right_comm depth 1 (initialLevel flipped)] using
      canonicalStates_sparse flipped (depth + initialLevel flipped) seedNode p
  new_source := fun depth actual bx by₀ valid shaded _ hX _ hY =>
    (phase_source flipped depth coarse actual bx by₀ valid shaded hX hY).trans
      (canonical_source flipped _).symm

private theorem phase_bound (flipped : Bool) (depth z : ℕ)
    (hz : z < 6 * phaseScale flipped depth) :
    z < 2 * 4 ^ (depth + initialLevel flipped) := by
  cases flipped <;> simp [phaseScale, initialLevel, pow_add] at * <;> omega

private theorem phase_component (flipped : Bool) (depth : ℕ) (coarse : ℕ → ℕ → Index)
    (rootEq : coarse 0 0 = 0) (x y : ℕ)
    (hx : x < 6 * phaseScale flipped depth) (hy : y < 6 * phaseScale flipped depth) :
    componentAt (supertileIndexGrid (depth + initialLevel flipped) seedNode) x y =
      componentAt (phaseGrid flipped depth coarse) x y := by
  have hX := phase_bound flipped depth x hx
  have hY := phase_bound flipped depth y hy
  unfold componentAt
  rw [supertileIndexGrid_eq_of_root_eq (depth + initialLevel flipped) seedNode coarse
    (rootEq.trans seedNode_parent.symm) (by omega) (by omega)]
  rfl

private theorem phase_state (flipped : Bool) (depth : ℕ) (coarse : ℕ → ℕ → Index)
    (rootEq : coarse 0 0 = 0) (actual : ℕ → ℕ → ShadeState)
    (valid : ValidShadeGrid (phaseGrid flipped depth coarse) actual)
    (shaded : CycleShade actual (phaseScale flipped depth) (3 * phaseScale flipped depth)
      (phaseScale flipped depth) (3 * phaseScale flipped depth) .light)
    (x y : ℕ) (west : 2 * phaseScale flipped depth ≤ x)
    (east : x < 6 * phaseScale flipped depth) (south : 2 * phaseScale flipped depth ≤ y)
    (north : y < 6 * phaseScale flipped depth) :
    actual x y = canonicalStates flipped (depth + initialLevel flipped) seedNode x y :=
  state_eq_of_present_eq (other := supertileIndexGrid (depth + initialLevel flipped) seedNode) valid
    ((canonical_valid flipped _ seedNode).allowed x y
      (phase_bound flipped depth x east) (phase_bound flipped depth y north))
    (phase_component flipped depth coarse rootEq x y east north)
    fun side present => (phaseComparison flipped coarse rootEq).agreement depth actual valid
      shaded ⟨x, y, side⟩ west east south north present

/-- Either phase gives depth+1 free lines, with one formula for the two axes. -/
private theorem phase_free (axis : LineAxis) (flipped : Bool) (depth index : ℕ)
    (hi : index ≤ depth)
    (coarse : ℕ → ℕ → Index) (rootEq : coarse 0 0 = 0)
    (actual : ℕ → ℕ → ShadeState)
    (valid : ValidShadeGrid (phaseGrid flipped depth coarse) actual)
    (shaded : CycleShade actual (phaseScale flipped depth) (3 * phaseScale flipped depth)
      (phaseScale flipped depth) (3 * phaseScale flipped depth) .light)
    (along : ℕ) (lower : 2 * phaseScale flipped depth + 1 < along)
    (upper : along < 6 * phaseScale flipped depth) :
    let fixed := coordinate (if flipped then 1 else 2) depth index
    let x := if axis = .column then fixed else along
    let y := if axis = .column then along else fixed
    if axis = .column then selectedHorizontalFor
      (componentAt (phaseGrid flipped depth coarse) x y) (quadrantAt x y) (actual x y) = none
    else selectedVerticalFor
      (componentAt (phaseGrid flipped depth coarse) x y) (quadrantAt x y) (actual x y) = none := by
  let fixed := coordinate (if flipped then 1 else 2) depth index
  have fixedBounds : 2 * phaseScale flipped depth + 1 < fixed ∧
      fixed < 6 * phaseScale flipped depth :=
    coordinate_bounds (by cases flipped <;> decide) hi
  have canonicalFree : LineFree axis (if flipped then 1 else 2) depth flipped seedNode fixed := by
    cases flipped
    · exact odd_free axis depth index hi
    · exact even_free axis seedNode depth index hi
  have free := canonicalFree along lower upper
  have stateEq (x y : ℕ) (hx : 2 * phaseScale flipped depth + 1 < x)
      (hX : x < 6 * phaseScale flipped depth) (hy : 2 * phaseScale flipped depth + 1 < y)
      (hY : y < 6 * phaseScale flipped depth) :=
    phase_state flipped depth coarse rootEq actual valid shaded x y (by omega) hX (by omega) hY
  cases axis <;> simp only [↓reduceIte, reduceCtorEq] at * <;>
  · rw [stateEq _ _ (by omega) (by omega) (by omega) (by omega),
      ← phase_component flipped depth coarse rootEq _ _ (by omega) (by omega)]
    simpa [LineFree, clearAt, nodeAt, clear, canonicalStates, initialLevel,
      supertileShadeGrid, supertileIndexGrid, componentAt, quadrantAt, Nat.mod_mod] using free

private theorem marker_checks :
    iterateRefine 4 (fun _ _ => (0 : Index)) 4 4 = 0 ∧
    iterateRefine 4 (fun _ _ => (0 : Index)) 8 8 = 0 ∧
    childBlock (childBlock 0 0 0) 0 0 = 0 := by
  decide +kernel

private theorem marker_ray (coarse : ℕ → ℕ → Index) (base depth : ℕ)
    (start : iterateRefine 4 coarse base base = 0) :
    iterateRefine (2 * depth + 4) coarse (base * 4 ^ depth) (base * 4 ^ depth) = 0 := by
  induction depth with
  | zero => simpa only [Nat.mul_zero, Nat.zero_add, pow_zero, Nat.mul_one] using start
  | succ depth ih =>
    rw [show 2 * (depth + 1) + 4 = 2 + (2 * depth + 4) by omega, ← iterateRefine_add,
      show base * 4 ^ (depth + 1) = 2 * (2 * (base * 4 ^ depth)) by rw [pow_succ]; ring]
    let prev := iterateRefine (2 * depth + 4) coarse
    let coord := base * 4 ^ depth
    change refineIndexGrid (refineIndexGrid prev) (2 * (2 * coord)) (2 * (2 * coord)) = 0
    have first := refineIndexGrid_child (refineIndexGrid prev) (2 * coord) (2 * coord) 0 0
    have second := refineIndexGrid_child prev coord coord 0 0
    simp only [Fin.val_zero, Nat.add_zero] at first second
    rw [first, second, show prev coord coord = 0 from ih]
    exact marker_checks.2.2

private theorem phase_marker (flipped : Bool) (depth : ℕ)
    (positive : flipped = true → 0 < depth)
    (coarse : ℕ → ℕ → Index) (rootEq : coarse 0 0 = 0) :
    QuarterIndex.mk
      (phaseGrid flipped depth coarse
        (coordinate (if flipped then 1 else 2) depth 0 / 2)
        (coordinate (if flipped then 1 else 2) depth 0 / 2))
      (quadrantAt (coordinate (if flipped then 1 else 2) depth 0)
        (coordinate (if flipped then 1 else 2) depth 0)) = ⟨0, .northeast⟩ := by
  have index : phaseGrid flipped depth coarse (2 * phaseScale flipped depth)
      (2 * phaseScale flipped depth) = 0 := by
    have ray (base k : ℕ) (hstart : iterateRefine 4 (fun _ _ => (0 : Index)) base base = 0)
        (hb : base < 2 ^ 4) (hlev : 2 * (depth + initialLevel flipped) = 2 * k + 4)
        (hcoord : 2 * phaseScale flipped depth = base * 4 ^ k) :
        phaseGrid flipped depth coarse (2 * phaseScale flipped depth)
          (2 * phaseScale flipped depth) = 0 := by
      rw [phaseGrid, hlev, hcoord]
      exact marker_ray coarse base k
        ((iterateRefine_eq_of_root_eq (h := fun _ _ => 0) rootEq 4 base base hb hb).trans hstart)
    cases flipped
    · exact ray 4 depth marker_checks.1 (by decide) (by simp [initialLevel]; omega)
        (by simp [phaseScale]; ring)
    · have hd := positive rfl
      obtain ⟨extra, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : depth ≠ 0)
      exact ray 8 extra marker_checks.2.1 (by decide) (by simp [initialLevel]; omega)
        (by simp [phaseScale, pow_succ]; ring)
  have first : coordinate (if flipped then 1 else 2) depth 0 =
      4 * phaseScale flipped depth + 1 := by
    rw [coordinate_zero]; simp only [phaseScale]; ring
  have odd : (4 * phaseScale flipped depth + 1) % 2 = 1 := by omega
  rw [first, show (4 * phaseScale flipped depth + 1) / 2 = 2 * phaseScale flipped depth by omega,
    index]
  simp [quadrantAt, Quadrant.ofBits, odd]

private theorem phase_marked (flipped : Bool) (depth n : ℕ) (hn : n ≤ depth)
    (positive : flipped = true → 0 < depth)
    (coarse : ℕ → ℕ → Index) (rootEq : coarse 0 0 = 0)
    (actual : ℕ → ℕ → ShadeState)
    (valid : ValidShadeGrid (phaseGrid flipped depth coarse) actual)
    (shaded : CycleShade actual (phaseScale flipped depth) (3 * phaseScale flipped depth)
      (phaseScale flipped depth) (3 * phaseScale flipped depth) .light) :
    Nonempty (MarkedFreeGrid (phaseGrid flipped depth coarse) actual
      (phaseScale flipped depth) (3 * phaseScale flipped depth)
      (phaseScale flipped depth) (3 * phaseScale flipped depth) n) := by
  let lines : Fin (n + 1) → ℕ := fun i => coordinate (if flipped then 1 else 2) depth i
  have positiveScale : 0 < (if flipped then 1 else 2 : ℕ) := by cases flipped <;> decide
  have hle (i : Fin (n + 1)) : (i : ℕ) ≤ depth := Nat.le_trans (Nat.lt_succ_iff.mp i.isLt) hn
  have bounds (i : Fin (n + 1)) : 2 * phaseScale flipped depth + 1 < lines i ∧
      lines i < 6 * phaseScale flipped depth :=
    coordinate_bounds positiveScale (hle i)
  have hi (i : Fin (n + 1)) : lines i < 2 * (3 * phaseScale flipped depth) := by
    have := (bounds i).2; omega
  have mono : StrictMono lines := fun _ _ hij => coordinate_strictMono positiveScale depth hij
  refine MarkedFreeGrid.ofSparse lines lines mono mono
    (fun i => ⟨(bounds i).1, hi i, fun along lower upper =>
      phase_free .column flipped depth i (hle i)
        coarse rootEq actual valid shaded along lower
        (by dsimp only [quarterNorth] at upper; omega)⟩)
    (fun i => ⟨(bounds i).1, hi i, fun along lower upper =>
      phase_free .row flipped depth i (hle i)
        coarse rootEq actual valid shaded along lower
        (by dsimp only [quarterEast] at upper; omega)⟩)
    (phase_marker flipped depth positive coarse rootEq)

/-- For each `n`, every scaffold plane contains a light board with `n + 1` consecutive
marked free rows and columns. -/
theorem exists_markedFreeGrid {P : Cslib.WangTile.Plane scaffold.tiles}
    (D : DecodedPlane P) (R : QuarterPlane.Regrouped D.quarterPlane) (n : ℕ) :
    ∃ (a b : ℤ) (scale : ℕ),
      CycleOn (fun i j => R.parent.index (a + i) (b + j))
        scale (3 * scale) scale (3 * scale) ∧
      CycleShade (fun x y => (D.siteGrid R a b x y).shade)
        scale (3 * scale) scale (3 * scale) .light ∧
      Nonempty (MarkedFreeGrid
        (fun i j => R.parent.index (a + i) (b + j))
        (fun x y => (D.siteGrid R a b x y).shade)
        scale (3 * scale) scale (3 * scale) n) := by
  obtain ⟨coarse, a, b, rootEq, patch⟩ := exists_refined_zero R.parent (2 * n + 4)
  let states := fun x y => (D.siteGrid R a b x y).shade
  have valid : ValidShadeGrid (iterateRefine (2 * n + 4) coarse) states :=
    patch ▸ (D.validGrid R a b).shadeValid
  have finish (flipped : Bool) (depth : ℕ) (hn : n ≤ depth)
      (positive : flipped = true → 0 < depth)
      (gridEq : phaseGrid flipped depth coarse = iterateRefine (2 * n + 4) coarse)
      (shaded : CycleShade states (phaseScale flipped depth) (3 * phaseScale flipped depth)
        (phaseScale flipped depth) (3 * phaseScale flipped depth) .light) :
      ∃ scale, CycleOn (fun i j => R.parent.index (a + i) (b + j))
          scale (3 * scale) scale (3 * scale) ∧
        CycleShade states scale (3 * scale) scale (3 * scale) .light ∧
        Nonempty (MarkedFreeGrid
          (fun i j => R.parent.index (a + i) (b + j)) states
          scale (3 * scale) scale (3 * scale) n) := by
    rw [patch, ← gridEq]
    exact ⟨_, phase_cycle flipped depth coarse, shaded, phase_marked flipped depth n hn positive
      coarse rootEq states (gridEq.symm ▸ valid) shaded⟩
  rcases has_light_cycle coarse (2 * n + 2) (by omega)
      (s := states) (by simpa only [Nat.add_assoc] using valid) with large | small
  · have power : 2 ^ (2 * n + 2) = 4 ^ (n + 1) := by
      rw [show 2 * n + 2 = 2 * (n + 1) by omega, pow_mul]; norm_num
    exact ⟨a, b, finish true (n + 1) (by omega) (fun _ => Nat.succ_pos n) rfl
      (by simpa only [phaseScale, ↓reduceIte, Nat.one_mul, power] using large)⟩
  · have power : 2 ^ (2 * n + 2 - 1) = 2 * 4 ^ n := by
      rw [show 2 * n + 2 - 1 = 1 + 2 * n by omega, pow_add, pow_mul]; norm_num
    exact ⟨a, b, finish false n le_rfl (by simp) rfl
      (by simpa only [phaseScale, Bool.false_eq_true, ↓reduceIte, power] using small)⟩

end Cslib.WangTile.Robinson
