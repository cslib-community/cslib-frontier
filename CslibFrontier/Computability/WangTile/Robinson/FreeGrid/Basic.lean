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
import Mathlib.Logic.Equiv.Fin.Basic
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
  have mem (i : Fin (n + 1)) : f i ∈ s := by
    simp only [s, Finset.mem_filter, Finset.mem_Ioo]
    exact ⟨⟨(hmem i).1, (hmem i).2.1⟩, hf.monotone (Fin.zero_le i), (hmem i).2.2⟩
  have card : n + 1 ≤ s.card := by
    let embed : Fin (n + 1) → s := fun i => ⟨f i, mem i⟩
    have hinj : Function.Injective embed := fun i j h => hf.injective (congrArg Subtype.val h)
    simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective embed hinj
  let g := s.orderEmbOfCardLe card
  have gmem i := s.orderEmbOfCardLe_mem card i
  have properties i : lo < g i ∧ g i < hi ∧ p (g i) := by
    have h := Finset.mem_filter.mp (gmem i)
    exact ⟨(Finset.mem_Ioo.mp h.1).1, (Finset.mem_Ioo.mp h.1).2, h.2.2⟩
  refine ⟨g, g.strictMono, ?_, properties, ?_⟩
  · apply le_antisymm
    · let j := (s.orderIsoOfFin rfl).symm ⟨f 0, mem 0⟩
      have hj : s.orderEmbOfFin rfl j = f 0 :=
        congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨f 0, mem 0⟩)
      exact ((s.orderEmbOfFin rfl).monotone (show Fin.castLE card 0 ≤ j by
        change 0 ≤ j.val
        exact Nat.zero_le _)).trans_eq hj
    · exact (Finset.mem_filter.mp (gmem 0)).2.1
  · intro i k hl hu hp
    have hk : k ∈ s := by
      simp only [s, Finset.mem_filter, Finset.mem_Ioo]
      exact ⟨⟨(properties i.castSucc).1.trans hl,
        hu.trans (properties i.succ).2.1⟩,
        (Finset.mem_filter.mp (gmem i.castSucc)).2.1.trans hl.le, hp⟩
    let j := (s.orderIsoOfFin rfl).symm ⟨k, hk⟩
    have hj : s.orderEmbOfFin rfl j = k :=
      congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨k, hk⟩)
    have lower : Fin.castLE card i.castSucc < j := by
      apply (s.orderEmbOfFin rfl).lt_iff_lt.mp
      exact hl.trans_eq hj.symm
    have upper : j < Fin.castLE card i.succ := by
      apply (s.orderEmbOfFin rfl).lt_iff_lt.mp
      exact hj.trans_lt hu
    simp only [Fin.lt_def, Fin.val_castLE, Fin.val_castSucc, Fin.val_succ] at lower upper
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
  classical
  obtain ⟨c, hc, hc0, cmem, cnext⟩ := select_lines columns hcolumns column_mem
  obtain ⟨r, hr, hr0, rmem, rnext⟩ := select_lines rows hrows row_mem
  exact ⟨{
    column := c, row := r
    column_strictMono := hc, row_strictMono := hr
    column_west := fun i => (cmem i).1
    column_east := fun i => (cmem i).2.1
    row_south := fun i => (rmem i).1
    row_north := fun i => (rmem i).2.1
    freeColumn := fun i => (cmem i).2.2
    freeRow := fun i => (rmem i).2.2
    noFreeColumnBetween := cnext
    noFreeRowBetween := rnext
    marker := by simpa only [hc0, hr0] using marker }⟩

private theorem crossing_ne {g : ℕ → ℕ → Index} {s : ℕ → ℕ → ShadeState}
    {w e b t w' e' b' t' x y : ℕ} {shade shade' : Shade}
    (valid : ValidShadeGrid g s) (c : CycleOn g w e b t) (d : CycleOn g w' e' b' t')
    (hs : CycleShade s w e b t shade) (ht : CycleShade s w' e' b' t' shade')
    (hx : x = quarterWest w ∨ x = quarterEast e)
    (hy : y = quarterSouth b' ∨ y = quarterNorth t')
    (xlo : quarterWest w' < x) (xhi : x < quarterEast e')
    (ylo : quarterSouth b < y) (yhi : y < quarterNorth t) : shade ≠ shade' := by
  have horizontal : hasHorizontal (componentAt g x y) (quadrantAt x y) = true := by
    rcases hy with rfl | rfl
    · exact CycleOn.south_path d xlo xhi
    · exact CycleOn.north_path d xlo xhi
  have vertical : hasVertical (componentAt g x y) (quadrantAt x y) = true := by
    rcases hx with rfl | rfl
    · exact CycleOn.west_path c ylo yhi
    · exact CycleOn.east_path c ylo yhi
  have first : (s x y).south = some shade := by
    rcases hx with rfl | rfl
    · exact (hs.west_at c valid ylo yhi).1
    · exact (hs.east_at c valid ylo yhi).1
  have second : (s x y).west = some shade' := by
    rcases hy with rfl | rfl
    · exact (ht.south_at d valid xlo xhi).1
    · exact (ht.north_at d valid xlo xhi).1
  intro eq
  exact (valid.rules x y).crossing_opposite horizontal vertical (by rw [first, second, eq])

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
  have c := (root_cycle (iterateRefine 1 g)).iterateRefine (level - 1)
  rw [iterateRefine_add, iterateRefine_add] at c
  have eq : level - 1 + 2 + 1 = level + 2 := by omega
  simpa only [eq, Nat.mul_one, Nat.one_mul, Nat.mul_comm] using c

private theorem has_light_cycle (g : ℕ → ℕ → Index)
    {s : ℕ → ℕ → ShadeState} (level : ℕ) (hlevel : 1 ≤ level)
    (valid : ValidShadeGrid (iterateRefine (level + 2) g) s) :
    CycleShade s (2 ^ level) (3 * 2 ^ level) (2 ^ level) (3 * 2 ^ level) .light ∨
    CycleShade s (2 ^ (level - 1)) (3 * 2 ^ (level - 1))
      (2 ^ (level - 1)) (3 * 2 ^ (level - 1)) .light := by
  obtain ⟨a, ha⟩ := CycleOn.exists_cycleShade (large_cycle g level) valid
  obtain ⟨b, hb⟩ := CycleOn.exists_cycleShade (small_cycle g level hlevel) valid
  have pow_eq : 2 ^ level = 2 * 2 ^ (level - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hlevel]
  have positive : 0 < 2 ^ (level - 1) := pow_pos (by decide) _
  have neq := crossing_ne valid (large_cycle g level) (small_cycle g level hlevel) ha hb
    (Or.inl rfl) (Or.inr rfl)
    (by simp only [quarterWest, pow_eq]; omega)
    (by simp only [quarterWest, quarterEast, pow_eq]; omega)
    (by simp only [quarterSouth, quarterNorth, pow_eq]; omega)
    (by simp only [quarterNorth, pow_eq]; omega)
  cases a <;> cases b
  · exact (neq rfl).elim
  · exact Or.inl ha
  · exact Or.inr hb
  · exact (neq rfl).elim

private theorem exists_refined_zero (base : IndexPlane) (depth : ℕ) :
    ∃ (g : ℕ → ℕ → Index) (u v : ℤ), g 0 0 = 0 ∧
      (fun x y : ℕ => base.index (u + x) (v + y)) = iterateRefine depth g := by
  let t := tower base
  obtain ⟨a, b, hab⟩ := t.every_tile depth 0
  obtain ⟨u, v, h⟩ := t.refined_patch depth 0 a b
  refine ⟨fun x y => (t.plane depth).index (a + x) (b + y), u, v, ?_, ?_⟩
  · simpa using hab
  · simpa only [t.zero, Nat.zero_add] using h

private theorem cell_cycle (g : ℕ → ℕ → Index) (bx by₀ : ℕ) :
    CycleOn (iterateRefine 2 g) (4 * bx + 1) (4 * bx + 3)
      (4 * by₀ + 1) (4 * by₀ + 3) := by
  have same (x y : ℕ) (hx : x < 4) (hy : y < 4) :
      indexThick (iterateRefine 2 g (4 * bx + x) (4 * by₀ + y)) =
        indexThick (fineGrid (g bx by₀) x y) := by
    have h := componentAt_two_block g bx by₀ (2 * x) (2 * y)
      (by omega) (by omega)
    simpa only [componentAt,
      show (8 * bx + 2 * x) / 2 = 4 * bx + x by omega,
      show (8 * by₀ + 2 * y) / 2 = 4 * by₀ + y by omega,
      show 2 * x / 2 = x by omega, show 2 * y / 2 = y by omega] using h
  have local_cycle := fixed_cycle (g bx by₀)
  refine ⟨by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (same 1 1 (by decide) (by decide)).trans local_cycle.southwest
  · exact (same 3 1 (by decide) (by decide)).trans local_cycle.southeast
  · exact (same 1 3 (by decide) (by decide)).trans local_cycle.northwest
  · exact (same 3 3 (by decide) (by decide)).trans local_cycle.northeast
  · intro x hl hu
    have hx : x = 4 * bx + 2 := by omega
    rw [hx, same 2 1 (by decide) (by decide)]
    exact local_cycle.southLane 2 (by decide) (by decide)
  · intro x hl hu
    have hx : x = 4 * bx + 2 := by omega
    rw [hx, same 2 3 (by decide) (by decide)]
    exact local_cycle.northLane 2 (by decide) (by decide)
  · intro y hl hu
    have hy : y = 4 * by₀ + 2 := by omega
    rw [hy, same 1 2 (by decide) (by decide)]
    exact local_cycle.westLane 2 (by decide) (by decide)
  · intro y hl hu
    have hy : y = 4 * by₀ + 2 := by omega
    rw [hy, same 3 2 (by decide) (by decide)]
    exact local_cycle.eastLane 2 (by decide) (by decide)

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
  have child_cycle := scaled_cell_cycle (iterateRefine 1 g) depth
    (2 * bx + cx.val) (2 * by₀ + cy.val)
  rw [iterateRefine_add] at child_cycle
  have levels : depth + 2 + 1 = depth + 1 + 2 := by omega
  rw [levels] at child_cycle
  apply Shade.eq_opposite_of_ne
  let x := if cx.val = 0 then quarterWest (2 ^ (depth + 1) * (4 * bx + 1))
    else quarterEast (2 ^ (depth + 1) * (4 * bx + 3))
  let y := if cy.val = 0 then quarterNorth (2 ^ depth * (4 * (2 * by₀ + cy.val) + 3))
    else quarterSouth (2 ^ depth * (4 * (2 * by₀ + cy.val) + 1))
  apply crossing_ne valid (scaled_cell_cycle g (depth + 1) bx by₀) child_cycle
    ancestor descendant (x := x) (y := y)
  · dsimp only [x]
    split_ifs <;> simp
  · dsimp only [y]
    split_ifs <;> simp
  all_goals
    have positive : 0 < 2 ^ depth := pow_pos (by decide) _
    fin_cases cx <;> fin_cases cy <;>
      simp [x, y, quarterWest, quarterEast, quarterSouth, quarterNorth, pow_succ] <;>
      nlinarith

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
    have hx : cellX = bx := by omega
    have hy : cellY = by₀ := by omega
    simpa only [Function.iterate_zero_apply, hx, hy] using ancestor
  | succ depth ih =>
    obtain ⟨cx, xlo', xhi'⟩ := cell_half
      (show 2 * 2 ^ depth * bx ≤ cellX by simpa only [pow_succ'] using xlo)
      (show cellX < 2 * 2 ^ depth * (bx + 1) by simpa only [pow_succ'] using xhi)
    obtain ⟨cy, ylo', yhi'⟩ := cell_half
      (show 2 * 2 ^ depth * by₀ ≤ cellY by simpa only [pow_succ'] using ylo)
      (show cellY < 2 * 2 ^ depth * (by₀ + 1) by simpa only [pow_succ'] using yhi)
    have grid_eq : iterateRefine (depth + 2) (iterateRefine 1 g) =
        iterateRefine (depth + 1 + 2) g := by
      rw [iterateRefine_add]
    have valid' : ValidShadeGrid (iterateRefine (depth + 2) (iterateRefine 1 g)) s := by
      rwa [grid_eq]
    obtain ⟨childShade, child⟩ := CycleOn.exists_cycleShade
      (scaled_cell_cycle (iterateRefine 1 g) depth (2 * bx + cx.val) (2 * by₀ + cy.val)) valid'
    have shade_eq := corner_shade_opposite g depth bx by₀ cx cy valid ancestor child
    rw [shade_eq] at child
    have result := ih (iterateRefine 1 g) valid' (2 * bx + cx.val) (2 * by₀ + cy.val)
      child xlo' xhi' ylo' yhi'
    simpa only [Function.iterate_succ_apply] using result

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
  · simp only [offset, ite_eq_left hz]
    omega
  · have hpow : 4 ^ index ≤ 4 ^ depth := pow_le_pow_right' (by decide) hi
    have hstep : 4 ^ index = 4 ^ (index - 1) * 4 := by
      conv_lhs => rw [show index = (index - 1) + 1 by omega, pow_succ]
    rw [hstep] at hpow
    have hsmall : 0 < 4 ^ (index - 1) := pow_pos (by decide) _
    simp only [offset, ite_eq_right hz]
    omega

private theorem offset_strictMono (depth : ℕ) : StrictMono (offset depth) := by
  intro i j hij
  have hj : j ≠ 0 := by omega
  by_cases hi : i = 0
  · have hp : 0 < 4 ^ (j - 1) := pow_pos (by decide) _
    simp only [offset, ite_eq_left hi, ite_eq_right hj]
    omega
  · have hp : 4 ^ (i - 1) < 4 ^ (j - 1) :=
      Nat.pow_lt_pow_right (by decide) (by omega)
    have hpos : 0 < 4 ^ depth := pow_pos (by decide) _
    simp only [offset, ite_eq_right hi, ite_eq_right hj]
    omega

/-- Closed coordinates form a strictly increasing sequence. -/
private theorem coordinate_strictMono {phaseScale : ℕ} (hs : 0 < phaseScale) (depth : ℕ) :
    StrictMono (coordinate phaseScale depth) := by
  intro i j hij
  exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left
    (offset_strictMono depth hij) hs) _

/-- Every selected coordinate lies strictly inside its phase's board. -/
private theorem coordinate_bounds {phaseScale depth index : ℕ} (hs : 0 < phaseScale)
    (hi : index ≤ depth) :
    2 * (phaseScale * 4 ^ depth) + 1 < coordinate phaseScale depth index ∧
      coordinate phaseScale depth index < 6 * (phaseScale * 4 ^ depth) := by
  obtain ⟨hpos, hbound⟩ := offset_bounds depth index hi
  have hp : 0 < 4 ^ depth := pow_pos (by decide) _
  have hlo := Nat.mul_pos hs hpos
  have hhi := Nat.mul_lt_mul_of_pos_left hbound hs
  dsimp only [coordinate]
  constructor <;> nlinarith

/-- The first line passes through the persistent northeast marker. -/
private theorem coordinate_zero (phaseScale depth : ℕ) :
    coordinate phaseScale depth 0 = 4 * phaseScale * 4 ^ depth + 1 := by
  simp only [coordinate, offset, ↓reduceIte]
  ring

/-- The two new descendants of the first offset, and the unique descendant of each tail offset. -/
private theorem offset_children (depth index : ℕ) :
    offset (depth + 1) index =
      if index = 0 then 4 * offset depth 0
      else if index = 1 then 4 * offset depth 0 + 1
      else 4 * offset depth (index - 1) + 3 := by
  by_cases hz : index = 0
  · simp [offset, hz, pow_succ]
    omega
  · by_cases ho : index = 1
    · simp [offset, ho, pow_succ]
      omega
    · have hs : index - 1 ≠ 0 := by omega
      have hexp : index - 1 = index - 1 - 1 + 1 := by omega
      have hpow : 4 ^ (index - 1) = 4 ^ (index - 1 - 1) * 4 := by
        conv_lhs => rw [hexp, pow_succ]
      have hp : 0 < 4 ^ depth := pow_pos (by decide) _
      have hq : 0 < 4 ^ (index - 1 - 1) := pow_pos (by decide) _
      simp only [offset, ite_eq_right hz, ite_eq_right ho, ↓reduceIte, ite_eq_right hs,
        pow_succ, hpow]
      omega

/-- The geometric axis of a free-line scan. -/
private inductive LineAxis where
  | row
  | column
  deriving DecidableEq

private instance : Fintype LineAxis :=
  Fintype.ofList [.row, .column] (by intro axis; cases axis <;> simp)

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

/-- Complete direct semantic obligations used by the even line recurrence. -/
private def EvenRules (node : Node) : Prop :=
  ∀ axis : LineAxis,
    ((∀ a : Fin 2, clear axis true node a 0) →
      ∀ a : Fin 8, fineClear axis true node a 0) ∧
    ((∀ a : Fin 2, clear axis true node a 1) →
      ∀ a : Fin 8, fineClear axis true node a 1 ∧ fineClear axis true node a 2) ∧
    (∀ a : Fin 6, ∀ fixed : Fin 3, fineClear axis true node (a.val + 2) fixed) ∧
    (∀ a : Fin 2, clear axis true (node.child 10) a 1)

private instance (node : Node) : Decidable (EvenRules node) := by
  unfold EvenRules
  infer_instance

section

-- Serialize the finite certificate proofs to keep their combined peak memory bounded.
set_option Elab.async false

private theorem even_checked0 : ∀ code : Fin 39,
    EvenRules ⟨finProdFinEquiv ((0 : Fin 8), code)⟩ := by
  decide +kernel

private theorem even_checked1 : ∀ code : Fin 39,
    EvenRules ⟨finProdFinEquiv ((1 : Fin 8), code)⟩ := by
  decide +kernel

private theorem even_checked2 : ∀ code : Fin 39,
    EvenRules ⟨finProdFinEquiv ((2 : Fin 8), code)⟩ := by
  decide +kernel

private theorem even_checked3 : ∀ code : Fin 39,
    EvenRules ⟨finProdFinEquiv ((3 : Fin 8), code)⟩ := by
  decide +kernel

private theorem even_checked4 : ∀ code : Fin 39,
    EvenRules ⟨finProdFinEquiv ((4 : Fin 8), code)⟩ := by
  decide +kernel

private theorem even_checked5 : ∀ code : Fin 39,
    EvenRules ⟨finProdFinEquiv ((5 : Fin 8), code)⟩ := by
  decide +kernel

private theorem even_checked6 : ∀ code : Fin 39,
    EvenRules ⟨finProdFinEquiv ((6 : Fin 8), code)⟩ := by
  decide +kernel

private theorem even_checked7 : ∀ code : Fin 39,
    EvenRules ⟨finProdFinEquiv ((7 : Fin 8), code)⟩ := by
  decide +kernel

private theorem evenRules (node : Node) : EvenRules node := by
  have checked : ∀ batch : Fin 8, ∀ code : Fin 39,
      EvenRules ⟨finProdFinEquiv (batch, code)⟩ := by
    intro batch
    fin_cases batch
    · exact even_checked0
    · exact even_checked1
    · exact even_checked2
    · exact even_checked3
    · exact even_checked4
    · exact even_checked5
    · exact even_checked6
    · exact even_checked7
  obtain ⟨⟨batch, code⟩, h⟩ := (finProdFinEquiv (m := 8) (n := 39)).surjective node.code
  have valid := checked batch code
  rwa [h] at valid

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

private instance : Fintype StripStep :=
  Fintype.ofList [.evenToEven, .evenToOdd, .oddToOdd]
    (by intro step; cases step <;> simp)

private def transition : StripStep → Transition
  | .evenToEven => ⟨false, false, 0⟩
  | .evenToOdd => ⟨false, true, 1⟩
  | .oddToOdd => ⟨true, true, 3⟩

private theorem odd_clear : ∀ axis : LineAxis, ∀ odd : Bool, ∀ node : Node,
    node.code.val ∈ interiorClass axis odd →
      ∀ along : Fin 2, clear axis false node along 1 := by
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
  decide +kernel

private theorem odd_base : ∀ axis : LineAxis,
    (∀ along : Fin 3,
      (if axis = .column then supertileNodeGrid 2 seedNode 4 (along.val + 3)
        else supertileNodeGrid 2 seedNode (along.val + 3) 4).code.val ∈
        interiorClass axis false) ∧
    (if axis = .column then supertileNodeGrid 2 seedNode 4 2
      else supertileNodeGrid 2 seedNode 2 4).code.val ∈ boundaryClass axis false := by
  decide +kernel

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
  · constructor
    · intro x y hx hy
      exact ShadeState.flip_allowed (valid.allowed x y hx hy)
    · intro x y hx hy
      change (supertileShadeGrid level root x y).east.map Shade.opposite =
        (supertileShadeGrid level root (x + 1) y).west.map Shade.opposite
      rw [valid.hmatch x y hx hy]
    · intro x y hx hy
      change (supertileShadeGrid level root x y).north.map Shade.opposite =
        (supertileShadeGrid level root x (y + 1)).south.map Shade.opposite
      rw [valid.vmatch x y hx hy]

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
  cases axis
  · simp only [clearAt, nodeAt, reduceCtorEq, ↓reduceIte]
    rw [show (8 * blockAlong + along) / 2 = 4 * blockAlong + along / 2 by omega,
      show (8 * blockFixed + fixed) / 2 = 4 * blockFixed + fixed / 2 by omega,
      supertileNodeGrid_block _ _ _ _ _ _ (by omega) (by omega)]
    simp [fineClear, fineNode, clear, ha2, hf2, quadrantAt]
  · simp only [clearAt, nodeAt, ↓reduceIte]
    rw [show (8 * blockFixed + fixed) / 2 = 4 * blockFixed + fixed / 2 by omega,
      show (8 * blockAlong + along) / 2 = 4 * blockAlong + along / 2 by omega,
      supertileNodeGrid_block _ _ _ _ _ _ (by omega) (by omega)]
    simp [fineClear, fineNode, clear, ha2, hf2, quadrantAt]

private theorem even_base (axis : LineAxis) (root : Node) :
    LineFree axis 1 0 true root 5 := by
  intro along hlo hhi
  have hdiv : along / 2 = 2 := by norm_num at hlo hhi; omega
  have hmod : along % 2 < 2 := Nat.mod_lt _ (by decide)
  have h := (evenRules root axis).2.2.2 ⟨along % 2, hmod⟩
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
  have hlo : 4 ^ depth ≤ along / 8 := by simp only [Nat.one_mul, pow_succ] at lower; omega
  have hhi : along / 8 < 3 * 4 ^ depth := by
    simp only [Nat.one_mul, pow_succ] at upper
    omega
  have halong : along = 8 * (along / 8) + along % 8 := by omega
  rw [halong, hchild]
  apply (clearAt_succ_block axis true (depth + 1) root _ _ _ _ hlocal (by omega)).2
  by_cases hb : along / 8 = 4 ^ depth
  · have hlocalLower : 2 ≤ along % 8 := by
      simp only [Nat.one_mul, pow_succ] at lower
      omega
    have h := (evenRules (nodeAt axis (depth + 1) root (along / 8) (old / 2))
      axis).2.2.1 ⟨along % 8 - 2, by omega⟩ ⟨fixed, hfixed⟩
    simpa only [show along % 8 - 2 + 2 = along % 8 by omega] using h
  · apply refines _ _ ⟨along % 8, hlocal⟩
    intro a
    have hparent := oldFree (2 * (along / 8) + a.val) (by
      simp only [Nat.one_mul]
      omega) (by simp only [Nat.one_mul]; omega)
    have hdiv : (2 * (along / 8) + a.val) / 2 = along / 8 := by omega
    have hmod : (2 * (along / 8) + a.val) % 2 = a.val := by omega
    simpa only [clearAt, hdiv, hmod] using hparent

private theorem even_child {axis : LineAxis} {root : Node} {depth old child : ℕ}
    (hold : LineFree axis 1 depth true root (2 * 4 ^ depth + 1 + old))
    (hchild : (old % 2 = 0 ∧ (child = 4 * old ∨ child = 4 * old + 1)) ∨
      (old % 2 = 1 ∧ child = 4 * old + 3)) :
    LineFree axis 1 (depth + 1) true root (2 * 4 ^ (depth + 1) + 1 + child) := by
  have step (fixed parity : ℕ) (hfixed : fixed < 3)
      (hp : (2 * 4 ^ depth + 1 + old) % 2 = parity)
      (hc : 2 * 4 ^ (depth + 1) + 1 + child =
        8 * ((2 * 4 ^ depth + 1 + old) / 2) + fixed)
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
    simp only [offset, ite_eq_right h]
    omega

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
      have hzero : index = 0 := by omega
      subst index
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
  have hd : (2 * 4 ^ (depth + 1) + child) / 4 = 2 * 4 ^ depth + old := by
    rw [hc, pow_succ]
    omega
  have hm : (2 * 4 ^ (depth + 1) + child) % 4 = fixed.val := by
    rw [hc, pow_succ]
    omega
  cases axis <;>
    simp [stripNode, nodeAt, supertileNodeGrid, classChild, childPosition, hd, hm,
      Nat.mod_eq_of_lt fixed.isLt]

private theorem strip_step {axis : LineAxis} {depth old child : ℕ} (which : StripStep)
    (hold : StripClassified axis (transition which).old depth old)
    (hc : child = 4 * old + (transition which).fixed.val) :
    StripClassified axis (transition which).new (depth + 1) child := by
  constructor
  · intro along hlo hhi
    have hp : 2 * 4 ^ depth ≤ along / 4 := by rw [pow_succ] at hlo; omega
    have hq : along / 4 < 6 * 4 ^ depth := by rw [pow_succ] at hhi; omega
    rw [stripNode_succ axis _ hc]
    have checked := odd_transitions axis which (stripNode axis depth old (along / 4))
    by_cases hb : along / 4 = 2 * 4 ^ depth
    · have hlocal : 0 < along % 4 := by rw [pow_succ] at hlo; omega
      have hmem : (stripNode axis depth old (along / 4)).code.val ∈
          boundaryClass axis (transition which).old := by rw [hb]; exact hold.2
      have step := (checked.2 hmem).2 ⟨along % 4 - 1, by omega⟩
      simpa only [Fin.val_mk, show along % 4 - 1 + 1 = along % 4 by omega] using step
    · exact checked.1 (hold.1 _ (by omega) hq) _
  · rw [stripNode_succ axis _ hc]
    have hd : (2 * 4 ^ (depth + 1)) / 4 = 2 * 4 ^ depth := by rw [pow_succ]; omega
    have hm : (2 * 4 ^ (depth + 1)) % 4 = 0 := by rw [pow_succ]; omega
    simp only [hd, hm]
    exact ((odd_transitions axis which _).2 hold.2).1

private theorem odd_classified (axis : LineAxis) (depth index : ℕ) (hi : index ≤ depth) :
    StripClassified axis (decide (index ≠ 0)) depth (offset depth index) := by
  induction depth generalizing index with
  | zero =>
      have hi0 : index = 0 := by omega
      subst index
      constructor
      · intro along hlo hhi
        have hl : 3 ≤ along := by norm_num at hlo; omega
        have hu : along < 6 := by norm_num at hhi; omega
        have h := (odd_base axis).1 ⟨along - 3, by omega⟩
        have heq : along - 3 + 3 = along := by omega
        cases axis <;> simpa [stripNode, nodeAt, offset, heq] using h
      · have h := (odd_base axis).2
        cases axis <;> simpa [stripNode, nodeAt, offset] using h
  | succ depth ih =>
      by_cases hz : index = 0
      · subst index
        have h := strip_step (which := .evenToEven) (ih 0 (by omega))
          (show offset (depth + 1) 0 = 4 * offset depth 0 + (transition .evenToEven).fixed.val by
            simp [offset_children, transition])
        simpa [transition] using h
      · by_cases ho : index = 1
        · subst index
          have h := strip_step (which := .evenToOdd) (ih 0 (by omega))
            (show offset (depth + 1) 1 = 4 * offset depth 0 + (transition .evenToOdd).fixed.val by
              simp [offset_children, transition])
          simpa [transition] using h
        · have hp : index - 1 ≠ 0 := by omega
          have previous := ih (index - 1) (by omega)
          have h := strip_step (which := .oddToOdd) (by simpa [transition, hp] using previous)
            (show offset (depth + 1) index =
                4 * offset depth (index - 1) + (transition .oddToOdd).fixed.val by
              simp [offset_children, transition, hz, ho])
          simpa [transition, hz] using h

private theorem odd_free (axis : LineAxis) (depth index : ℕ) (hi : index ≤ depth) :
    LineFree axis 2 depth false seedNode (coordinate 2 depth index) := by
  intro along hlo hhi
  have hl : 2 * 4 ^ depth < along / 2 := by omega
  have hu : along / 2 < 6 * 4 ^ depth := by omega
  have hmem := (odd_classified axis depth index hi).1 (along / 2) hl hu
  have hd : coordinate 2 depth index / 2 = 2 * 4 ^ depth + offset depth index := by
    dsimp only [coordinate]
    omega
  have hm : coordinate 2 depth index % 2 = 1 := by
    dsimp only [coordinate]
    omega
  have h := odd_clear axis (decide (index ≠ 0))
    (stripNode axis depth (offset depth index) (along / 2)) hmem
    ⟨along % 2, Nat.mod_lt _ (by decide)⟩
  simpa only [clearAt, hd, hm, stripNode] using h

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
      have hf := Bool.eq_false_of_not_eq_true hp
      rw [hf] at ha
      rw [hg, hf] at hc
      cases hactual : value actual ⟨x, y, side⟩ <;>
        cases hcanonical : value canonical ⟨x, y, side⟩ <;> simp_all
  have hw := values .west
  have he := values .east
  have hs := values .south
  have hn := values .north
  cases ha : actual x y
  cases hc : canonical x y
  simp only [value, ha, hc] at hw he hs hn
  congr

private theorem sparse_block {bx by₀ : ℕ} {p : Port} (hx : p.x < 2) (hy : p.y < 2) :
    sparsePort (translatePort p (2 * bx) (2 * by₀)) =
      translatePort (sparsePort p) (8 * bx) (8 * by₀) := by
  rcases p with ⟨x, y, side⟩
  simp only [sparsePort, sparseCoordinate, translatePort, Port.mk.injEq]
  constructor
  · omega
  constructor
  · omega
  · trivial

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
      have validFine : ValidShadeGrid (iterateRefine 2 (C.grid d)) actual := by
        rw [C.grid_succ]
        exact valid
      let coarseStates := coarsen actual
      have coarseValid : ValidShadeGrid (C.grid d) coarseStates :=
        ValidShadeGrid.coarsen validFine
      have coarseShaded : CycleShade coarseStates (C.scale d) (3 * C.scale d)
          (C.scale d) (3 * C.scale d) .light := by
        apply CycleShade.coarsen validFine (C.cycle d)
        convert shaded using 1 <;> rw [C.scale_succ] <;> omega
      let bx := p.x / 8
      let by₀ := p.y / 8
      let localPort : Port := ⟨p.x % 8, p.y % 8, p.side⟩
      have hx : localPort.x < 8 := Nat.mod_lt _ (by decide)
      have hy : localPort.y < 8 := Nat.mod_lt _ (by decide)
      have hlocation : translatePort localPort (8 * bx) (8 * by₀) = p := by
        rcases p with ⟨x, y, side⟩
        simp only [localPort, bx, by₀, translatePort, Port.mk.injEq]
        constructor
        · omega
        constructor
        · omega
        · trivial
      have localPresent : portPresent (fineGrid (C.grid d bx by₀)) localPort = true := by
        rw [portPresent_two_block (C.grid d) bx by₀ localPort hx hy, C.grid_succ, hlocation]
        exact present
      obtain ⟨source, hsource, parity, path⟩ :=
        exists_boundedPath (C.grid d bx by₀) (mem_portsIn_iff.mpr ⟨hx, hy⟩) localPresent
      have actualPath := boundedPath_two_block (C.grid d) bx by₀ path
      rw [C.grid_succ, hlocation] at actualPath
      have hbx : C.scale d ≤ bx := by
        rw [C.scale_succ] at hpx
        dsimp only [bx]
        omega
      have hbX : bx < 3 * C.scale d := by
        rw [C.scale_succ] at hpX
        dsimp only [bx]
        omega
      have hby : C.scale d ≤ by₀ := by
        rw [C.scale_succ] at hpy
        dsimp only [by₀]
        omega
      have hbY : by₀ < 3 * C.scale d := by
        rw [C.scale_succ] at hpY
        dsimp only [by₀]
        omega
      have canonicalRelation := C.local_sound d bx by₀ hbx hbX hby hbY path
      have targetEq := C.block d bx by₀ localPort hx hy
      rw [hlocation] at targetEq
      have finish (h : value actual (translatePort source (8 * bx) (8 * by₀)) =
          value (C.localStates d bx by₀) source) :
          value actual p = value (C.states (d + 1)) p := by
        have relation := actualPath.sound valid
        rw [h] at relation
        rw [← targetEq] at canonicalRelation
        exact Related.right_unique relation canonicalRelation
      rcases source_cases hsource with heq | ⟨old, _, oldPresent, heq⟩
      · subst source
        exact finish (C.new_source d actual bx by₀ valid shaded hbx hbX hby hbY)
      · subst source
        have oldBounds : old.x < 2 ∧ old.y < 2 := by
          have h := path.first_inBounds
          dsimp only [PortInBounds, sparsePort, sparseCoordinate] at h
          omega
        let oldGlobal := translatePort old (2 * bx) (2 * by₀)
        have oldGlobalPresent : portPresent (C.grid d) oldGlobal = true := by
          have heq := portPresent_local (C.grid d) oldGlobal
          have hdx : oldGlobal.x / 2 = bx := by dsimp [oldGlobal, translatePort]; omega
          have hdy : oldGlobal.y / 2 = by₀ := by dsimp [oldGlobal, translatePort]; omega
          have hmx : oldGlobal.x % 2 = old.x := by dsimp [oldGlobal, translatePort]; omega
          have hmy : oldGlobal.y % 2 = old.y := by dsimp [oldGlobal, translatePort]; omega
          rw [hdx, hdy, hmx, hmy] at heq
          exact heq.symm.trans oldPresent
        have hox : 2 * C.scale d ≤ oldGlobal.x := by dsimp [oldGlobal, translatePort]; omega
        have hoX : oldGlobal.x < 6 * C.scale d := by dsimp [oldGlobal, translatePort]; omega
        have hoy : 2 * C.scale d ≤ oldGlobal.y := by dsimp [oldGlobal, translatePort]; omega
        have hoY : oldGlobal.y < 6 * C.scale d := by dsimp [oldGlobal, translatePort]; omega
        have previous := ih coarseStates coarseValid coarseShaded oldGlobal
          hox hoX hoy hoY oldGlobalPresent
        have sparseActual : value actual (sparsePort oldGlobal) =
            value (C.states d) oldGlobal := by
          have pathEq := (livePortPath (C.grid d) oldGlobal oldGlobalPresent).sound validFine
          exact Eq.trans pathEq ((value_coarsen actual oldGlobal).symm.trans
            previous)
        have sourceGlobalEq : sparsePort oldGlobal =
            translatePort (sparsePort old) (8 * bx) (8 * by₀) :=
          sparse_block oldBounds.1 oldBounds.2
        have sourceBounds := path.first_inBounds
        have blockValue := C.block d bx by₀ (sparsePort old) sourceBounds.1 sourceBounds.2
        rw [← sourceGlobalEq] at blockValue
        apply finish
        rw [← sourceGlobalEq]
        exact sparseActual.trans ((C.sparse d oldGlobal).symm.trans blockValue)

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
  · have levelEq : 2 * depth + 2 + 2 = 2 * (depth + 2) := by omega
    have power : 2 ^ (2 * depth + 2 - 1) = 2 * 4 ^ depth := by
      rw [show 2 * depth + 2 - 1 = 1 + 2 * depth by omega, pow_add, pow_mul]
      norm_num
    simpa only [phaseGrid, phaseScale, initialLevel, Bool.false_eq_true, ↓reduceIte,
      levelEq, power] using small_cycle coarse (2 * depth + 2) (by omega)
  · have levelEq : 2 * depth + 2 = 2 * (depth + 1) := by omega
    have power : 2 ^ (2 * depth) = 4 ^ depth := by norm_num [pow_mul]
    simpa only [phaseGrid, phaseScale, initialLevel, ↓reduceIte,
      Nat.one_mul, levelEq, power] using large_cycle coarse (2 * depth)

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
    rw [show baseGrid (x / 2) (y / 2) = phaseGrid flipped 0 coarse (x / 2) (y / 2) from
      by
        simpa only [baseGrid, phaseGrid, Nat.zero_add] using
          iterateRefine_eq_of_root_eq (g := coarseGrid 0) (h := coarse) rootEq.symm
            (2 * level) (x / 2) (y / 2)
            (by simpa [pow_mul] using (show x / 2 < 4 ^ level by omega))
            (by simpa [pow_mul] using (show y / 2 < 4 ^ level by omega))]
  have canonicalValid : ShadeValidOn baseGrid canonical (2 * 4 ^ level) (2 * 4 ^ level) := by
    have h := canonical_valid flipped level seedNode
    rw [supertileIndexGrid_eq_iterateRefine, seedNode_parent] at h
    exact h
  have targetBounds : target.x < 2 * 4 ^ level ∧ target.y < 2 * 4 ^ level := by
    cases flipped <;> norm_num [phaseScale, initialLevel, level] at * <;> omega
  have basePresent : portPresent baseGrid target = true := by
    cases target with
    | mk x y side =>
      cases side <;> simp only [portPresent] <;>
        rw [geometry x y targetBounds.1 targetBounds.2] <;> exact present
  have finish {width : ℕ} {source : Port} {parity : Bool}
      (bound : width ≤ 2 * 4 ^ level)
      (path : BoundedPath baseGrid width width source target parity)
      (actualSource : value actual source = some .light)
      (canonicalSource : value canonical source = some .light) :
      value actual target = value canonical target := by
    have actualPath := boundedPath_translate (offsetX := 0) (offsetY := 0)
      (by decide) (by decide)
      (fun x y hx hy => by
        simpa only [Nat.zero_add] using (geometry x y (by omega) (by omega))) path
    have actualRelation := actualPath.sound valid
    simp only [translatePort, Nat.zero_add] at actualRelation
    rw [actualSource] at actualRelation
    have canonicalRelation := path.sound
      (fun x y hx hy => canonicalValid.allowed x y (by omega) (by omega))
      (fun x y hx hy => canonicalValid.hmatch x y (by omega) (by omega))
      (fun x y hx hy => canonicalValid.vmatch x y (by omega) (by omega))
    rw [canonicalSource] at canonicalRelation
    exact Related.right_unique actualRelation canonicalRelation
  cases flipped
  · obtain ⟨source, parity, sourceMem, path⟩ := odd_base_exists_boundedPath
      west east south north basePresent
    have colours := odd_cycle_colours
    apply finish (by decide) path
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at sourceMem
      rcases sourceMem with rfl | rfl | rfl | rfl
      · exact shaded.southwest
      · exact shaded.southeast
      · exact shaded.northeast
      · exact shaded.northwest
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at sourceMem
      rcases sourceMem with rfl | rfl | rfl | rfl
      · simpa only [canonical, level, initialLevel, canonicalStates, Bool.false_eq_true,
          ↓reduceIte, value] using colours.1
      · simpa only [canonical, level, initialLevel, canonicalStates, Bool.false_eq_true,
          ↓reduceIte, value] using colours.2.1
      · simpa only [canonical, level, initialLevel, canonicalStates, Bool.false_eq_true,
          ↓reduceIte, value] using colours.2.2.1
      · simpa only [canonical, level, initialLevel, canonicalStates, Bool.false_eq_true,
          ↓reduceIte, value] using colours.2.2.2
  · obtain ⟨parity, path⟩ := base_exists_boundedPath west east south north basePresent
    apply finish (by decide) path
    · exact (shaded.south_at (phase_cycle true 0 coarse) valid (by decide) (by decide)).1
    · exact canonical_source true seedNode

private theorem phase_source (flipped : Bool) (depth : ℕ) (coarse : ℕ → ℕ → Index)
    (actual : ℕ → ℕ → ShadeState) (bx by₀ : ℕ)
    (valid : ValidShadeGrid (phaseGrid flipped (depth + 1) coarse) actual)
    (shaded : CycleShade actual (phaseScale flipped (depth + 1))
      (3 * phaseScale flipped (depth + 1))
      (phaseScale flipped (depth + 1)) (3 * phaseScale flipped (depth + 1)) .light)
    (hx : bx < 3 * phaseScale flipped depth) (hy : by₀ < 3 * phaseScale flipped depth) :
    value actual (translatePort cycleSource (8 * bx) (8 * by₀)) =
      some (if flipped then .light else .dark) := by
  have invol : Function.Involutive Shade.opposite := Shade.opposite_opposite
  cases flipped
  · have valid' : ValidShadeGrid
        (iterateRefine (2 * (depth + 1) + 1 + 2) (iterateRefine 1 coarse)) actual := by
      rw [iterateRefine_add,
        show 2 * (depth + 1) + 1 + 2 + 1 = 2 * (depth + 1 + 2) by omega]
      exact valid
    have scaleEq : 2 ^ (2 * (depth + 1) + 1) = phaseScale false (depth + 1) := by
      simp only [phaseScale, Bool.false_eq_true, ↓reduceIte, pow_add, pow_mul]
      ring
    have shaded' : CycleShade actual (2 ^ (2 * (depth + 1) + 1))
        (3 * 2 ^ (2 * (depth + 1) + 1)) (2 ^ (2 * (depth + 1) + 1))
        (3 * 2 ^ (2 * (depth + 1) + 1)) .light := by
      simpa only [scaleEq] using shaded
    have h := root_descendant_source (2 * (depth + 1) + 1) (iterateRefine 1 coarse)
      valid' shaded' bx by₀
      (by rw [scaleEq, phaseScale_succ]; omega)
      (by rw [scaleEq, phaseScale_succ]; omega)
    rw [invol.iterate_two_mul_add_one] at h
    exact h
  · have valid' : ValidShadeGrid (iterateRefine (2 * (depth + 1) + 2) coarse) actual := by
      rw [show 2 * (depth + 1) + 2 = 2 * (depth + 1 + 1) by omega]
      exact valid
    have scaleEq : 2 ^ (2 * (depth + 1)) = phaseScale true (depth + 1) := by
      norm_num [phaseScale, pow_mul]
    have shaded' : CycleShade actual (2 ^ (2 * (depth + 1)))
        (3 * 2 ^ (2 * (depth + 1))) (2 ^ (2 * (depth + 1)))
        (3 * 2 ^ (2 * (depth + 1))) .light := by
      simpa only [scaleEq] using shaded
    have h := root_descendant_source (2 * (depth + 1)) coarse valid' shaded' bx by₀
      (by rw [scaleEq, phaseScale_succ]; omega)
      (by rw [scaleEq, phaseScale_succ]; omega)
    rw [invol.iterate_two_mul] at h
    exact h

private def phaseComparison (flipped : Bool) (coarse : ℕ → ℕ → Index)
    (rootEq : coarse 0 0 = 0) : RefinementComparison where
  scale := phaseScale flipped
  grid := fun depth => phaseGrid flipped depth coarse
  states := fun depth => canonicalStates flipped (depth + initialLevel flipped) seedNode
  localStates := fun depth bx by₀ => canonicalStates flipped 1
    (supertileNodeGrid (depth + initialLevel flipped) seedNode bx by₀)
  scale_succ := phaseScale_succ flipped
  grid_succ := by
    intro depth
    simp only [phaseGrid, iterateRefine_add]
    congr 1
    omega
  cycle := fun depth => phase_cycle flipped depth coarse
  base := by
    intro actual valid shaded p hx hX hy hY present
    simpa only [Nat.zero_add] using
      phase_base flipped coarse rootEq actual valid shaded p hx hX hy hY present
  local_sound := by
    intro depth bx by₀ _ hx _ hy a b parity path
    let node := supertileNodeGrid (depth + initialLevel flipped) seedNode bx by₀
    have bound (z : ℕ) (hz : z < 3 * phaseScale flipped depth) :
        z < 4 ^ (depth + initialLevel flipped) := by
      cases flipped <;> simp [phaseScale, initialLevel, pow_add] at * <;> omega
    have parentEq : node.parent = phaseGrid flipped depth coarse bx by₀ :=
      supertileIndexGrid_eq_of_root_eq (depth + initialLevel flipped) seedNode coarse
        (rootEq.trans seedNode_parent.symm) (bound bx hx) (bound by₀ hy)
    have finiteValid := canonical_valid flipped 1 node
    rw [supertileIndexGrid_eq_iterateRefine, parentEq] at finiteValid
    exact path.sound finiteValid.allowed finiteValid.hmatch finiteValid.vmatch
  block := by
    intro depth bx by₀ p hx hy
    simpa only [Nat.add_right_comm depth 1 (initialLevel flipped)] using
      canonicalStates_block flipped (depth + initialLevel flipped) seedNode bx by₀ p hx hy
  sparse := by
    intro depth p
    simpa only [Nat.add_right_comm depth 1 (initialLevel flipped)] using
      canonicalStates_sparse flipped (depth + initialLevel flipped) seedNode p
  new_source := by
    intro depth actual bx by₀ valid shaded hx hX hy hY
    exact (phase_source flipped depth coarse actual bx by₀ valid shaded hX hY).trans
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
    actual x y = canonicalStates flipped (depth + initialLevel flipped) seedNode x y := by
  apply state_eq_of_present_eq
    (other := supertileIndexGrid (depth + initialLevel flipped) seedNode) valid
    ((canonical_valid flipped _ seedNode).allowed x y
      (phase_bound flipped depth x east) (phase_bound flipped depth y north))
    (phase_component flipped depth coarse rootEq x y east north)
  intro side present
  exact (phaseComparison flipped coarse rootEq).agreement depth actual valid shaded
    ⟨x, y, side⟩ west east south north present

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
      fixed < 6 * phaseScale flipped depth := by
    exact coordinate_bounds (by cases flipped <;> decide) hi
  have canonicalFree : LineFree axis (if flipped then 1 else 2) depth flipped seedNode fixed := by
    cases flipped
    · exact odd_free axis depth index hi
    · exact even_free axis seedNode depth index hi
  have free := canonicalFree along lower upper
  have stateEq (x y : ℕ) (hx : 2 * phaseScale flipped depth + 1 < x)
      (hX : x < 6 * phaseScale flipped depth) (hy : 2 * phaseScale flipped depth + 1 < y)
      (hY : y < 6 * phaseScale flipped depth) :=
    phase_state flipped depth coarse rootEq actual valid shaded x y (by omega) hX (by omega) hY
  cases axis
  · change selectedVerticalFor
      (componentAt (phaseGrid flipped depth coarse) along fixed) (quadrantAt along fixed)
      (actual along fixed) = none
    rw [stateEq along fixed lower upper fixedBounds.1 fixedBounds.2,
      ← phase_component flipped depth coarse rootEq along fixed upper fixedBounds.2]
    simpa [LineFree, clearAt, nodeAt, clear, canonicalStates, initialLevel,
      supertileShadeGrid, supertileIndexGrid, componentAt, quadrantAt, Nat.mod_mod] using free
  · change selectedHorizontalFor
      (componentAt (phaseGrid flipped depth coarse) fixed along) (quadrantAt fixed along)
      (actual fixed along) = none
    rw [stateEq fixed along fixedBounds.1 fixedBounds.2 lower upper,
      ← phase_component flipped depth coarse rootEq fixed along fixedBounds.2 upper]
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
    rw [show 2 * (depth + 1) + 4 = 2 + (2 * depth + 4) by omega,
      ← iterateRefine_add]
    have position : base * 4 ^ (depth + 1) = 2 * (2 * (base * 4 ^ depth)) := by
      rw [pow_succ]
      ring
    rw [position]
    let previous := iterateRefine (2 * depth + 4) coarse
    let coordinate := base * 4 ^ depth
    change refineIndexGrid (refineIndexGrid previous) (2 * (2 * coordinate))
      (2 * (2 * coordinate)) = 0
    have first := refineIndexGrid_child (refineIndexGrid previous)
      (2 * coordinate) (2 * coordinate) 0 0
    have second := refineIndexGrid_child previous coordinate coordinate 0 0
    simp only [Fin.val_zero, Nat.add_zero] at first second
    rw [first, second]
    dsimp only [previous, coordinate]
    rw [ih]
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
    cases flipped
    · have start : iterateRefine 4 coarse 4 4 = 0 :=
        (iterateRefine_eq_of_root_eq (h := fun _ _ => 0) rootEq 4 4 4 (by decide) (by decide)).trans
          marker_checks.1
      change iterateRefine (2 * (depth + 2)) coarse (2 * (2 * 4 ^ depth))
        (2 * (2 * 4 ^ depth)) = 0
      rw [show 2 * (depth + 2) = 2 * depth + 4 by omega,
        show 2 * (2 * 4 ^ depth) = 4 * 4 ^ depth by omega]
      exact marker_ray coarse 4 depth start
    · have hd := positive rfl
      obtain ⟨extra, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : depth ≠ 0)
      have start : iterateRefine 4 coarse 8 8 = 0 :=
        (iterateRefine_eq_of_root_eq (h := fun _ _ => 0) rootEq 4 8 8 (by decide) (by decide)).trans
          marker_checks.2.1
      change iterateRefine (2 * (extra + 1 + 1)) coarse
        (2 * (1 * 4 ^ (extra + 1))) (2 * (1 * 4 ^ (extra + 1))) = 0
      simp only [Nat.one_mul, pow_succ]
      rw [show 2 * (extra + 1 + 1) = 2 * extra + 4 by omega,
        show 2 * (4 ^ extra * 4) = 8 * 4 ^ extra by omega]
      exact marker_ray coarse 8 extra start
  have first : coordinate (if flipped then 1 else 2) depth 0 =
      4 * phaseScale flipped depth + 1 := by
    rw [coordinate_zero]
    simp only [phaseScale]
    ring
  rw [first]
  have half : (4 * phaseScale flipped depth + 1) / 2 = 2 * phaseScale flipped depth := by omega
  have phase : quadrantAt (4 * phaseScale flipped depth + 1)
      (4 * phaseScale flipped depth + 1) = .northeast := by
    have odd : (4 * phaseScale flipped depth + 1) % 2 = 1 := by omega
    simp [quadrantAt, Quadrant.ofBits, odd]
  rw [half, index, phase]

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
  have increasing : StrictMono lines := by
    intro i j hij
    exact coordinate_strictMono positiveScale depth hij
  have bounds (i : Fin (n + 1)) : 2 * phaseScale flipped depth + 1 < lines i ∧
      lines i < 6 * phaseScale flipped depth := coordinate_bounds positiveScale
    (show i.val ≤ depth by have := i.isLt; omega)
  refine MarkedFreeGrid.ofSparse lines lines increasing increasing ?_ ?_
    (phase_marker flipped depth positive coarse rootEq)
  · intro i
    refine ⟨(bounds i).1, ?_, ?_⟩
    · change lines i < 2 * (3 * phaseScale flipped depth)
      have h := (bounds i).2
      omega
    · intro along lower upper
      exact phase_free .column flipped depth i (by have := i.isLt; omega)
        coarse rootEq actual valid shaded along lower (by
          dsimp only [quarterNorth] at upper
          omega)
  · intro i
    refine ⟨(bounds i).1, ?_, ?_⟩
    · change lines i < 2 * (3 * phaseScale flipped depth)
      have h := (bounds i).2
      omega
    · intro along lower upper
      exact phase_free .row flipped depth i (by have := i.isLt; omega)
        coarse rootEq actual valid shaded along lower (by
          dsimp only [quarterEast] at upper
          omega)

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
  have valid : ValidShadeGrid (iterateRefine (2 * n + 4) coarse) states := by
    rw [← patch]
    exact (D.validGrid R a b).shadeValid
  refine ⟨a, b, ?_⟩
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
    have phaseValid : ValidShadeGrid (phaseGrid flipped depth coarse) states := by
      rw [gridEq]
      exact valid
    refine ⟨phaseScale flipped depth, ?_, shaded, ?_⟩
    · rw [patch, ← gridEq]
      exact phase_cycle flipped depth coarse
    · rw [patch, ← gridEq]
      exact phase_marked flipped depth n hn positive coarse rootEq states phaseValid shaded
  have light := has_light_cycle coarse (2 * n + 2) (by omega)
    (s := states) (by simpa only [Nat.add_assoc] using valid)
  rcases light with large | small
  · have gridEq : phaseGrid true (n + 1) coarse = iterateRefine (2 * n + 4) coarse := by
      unfold phaseGrid initialLevel
      congr 1
    have power : 2 ^ (2 * n + 2) = 4 ^ (n + 1) := by
      rw [show 2 * n + 2 = 2 * (n + 1) by omega, pow_mul]
      norm_num
    apply finish true (n + 1) (by omega) (by intro _; omega) gridEq
    simpa only [phaseScale, ↓reduceIte, Nat.one_mul, power] using large
  · have gridEq : phaseGrid false n coarse = iterateRefine (2 * n + 4) coarse := by
      unfold phaseGrid initialLevel
      congr 1
    have power : 2 ^ (2 * n + 2 - 1) = 2 * 4 ^ n := by
      rw [show 2 * n + 2 - 1 = 1 + 2 * n by omega, pow_add, pow_mul]
      norm_num
    apply finish false n le_rfl (by simp) gridEq
    simpa only [phaseScale, Bool.false_eq_true, ↓reduceIte, power] using small

end Cslib.WangTile.Robinson
