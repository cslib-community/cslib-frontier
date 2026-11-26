/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.Tiles
import CslibFrontier.Computability.WangTile.Robinson.Recognizability
import CslibFrontier.Computability.WangTile.Compactness
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.FinCases

/-!
# The corrected Robinson substitution hierarchy

The thin layer fixes a parity class of southwest child corners. Local recognizability recovers
one parent at every such corner, and reflection of matching along substituted boundaries makes
the recovered parents a matching plane. Repeating this construction gives a tower. Every tile
occurs at every level, and finite iterated substitution patches establish nonemptiness by
compactness.

## Main definitions

* `IndexPlane`: an indexed matching plane over the corrected 104-tile alphabet.
* `Parent`: a matching substitution parent, with its parity alignment.
* `Tower`: a sequence of substitution parents above a prescribed plane.

## Main results

* `exists_plane_eq`: a pointwise index-plane representation of any tiling by `tileSet`.
* `nonempty_parent`: every matching plane has a matching substitution parent.
* `tower`: every matching plane admits a parent tower.
* `Tower.every_tile`: every tile type occurs at every level of any such tower.
* `tilesPlane_tileSet`: the concrete corrected palette tiles the plane.

## References

The substitution hierarchy is the matching and recognition construction of
[JeandelVanier2020], §3.2, Proposition 8, for the corrected 104-tile variant.
Derived from the hierarchy in
[lean-wang](https://github.com/edemaine/lean-wang/tree/64268a3/LeanWang/Robinson/Closed104),
revision `64268a3`. The finite-patch nonemptiness proof and the factorization of the recurrence
certificate through tile 0 are original reorganizations of the substitution argument.
-/

public section

namespace Cslib.WangTile.Robinson

/-- A matching plane indexed by the corrected Robinson alphabet. -/
structure IndexPlane where
  /-- The corrected tile index at an integer lattice point. -/
  index : ℤ → ℤ → Index
  /-- Horizontal neighbours have equal edge colours. -/
  horizontal : ∀ x y, (tile (components (index x y))).right =
    (tile (components (index (x + 1) y))).left
  /-- Vertical neighbours have equal edge colours. -/
  vertical : ∀ x y, (tile (components (index x y))).top =
    (tile (components (index x (y + 1)))).bottom

/-- Every tiling by the concrete palette has a pointwise equal indexed matching plane. -/
theorem exists_plane_eq {f : ℤ → ℤ → WangTile}
    (hf : ∀ x y, f x y ∈ tileSet ∧ (f x y).right = (f (x + 1) y).left ∧
      (f x y).top = (f x (y + 1)).bottom) :
    ∃ P : IndexPlane, ∀ x y, tile (components (P.index x y)) = f x y := by
  choose p hp using fun x y => mem_tileSet.mp (hf x y).1
  exact ⟨⟨p, by simpa only [hp] using fun x y => (hf x y).2.1,
    by simpa only [hp] using fun x y => (hf x y).2.2⟩, hp⟩

/-- A matching parent of a fine plane, including the alignment of its child blocks. -/
structure Parent (fine : IndexPlane) where
  /-- The matching coarse plane. -/
  coarse : IndexPlane
  /-- Horizontal coordinate of the southwest child of the coarse origin. -/
  offsetX : Fin 2
  /-- Vertical coordinate of the southwest child of the coarse origin. -/
  offsetY : Fin 2
  /-- Substitution reproduces all four children at every coarse lattice point. -/
  children : ∀ (x y : ℤ) (i j : Fin 2), childBlock (coarse.index x y) i j =
    fine.index ((offsetX.val : ℤ) + 2 * x + i.val) ((offsetY.val : ℤ) + 2 * y + j.val)

/-- A lattice phase whose unit steps are involutions is invariant under even translations.
This applies both to the thin Robinson layer and to the subdivision quadrants. -/
theorem phase_even_of_involutive {β : Type*} (φ : ℤ → ℤ → β) (e n : β → β)
    (he : Function.Involutive e) (hn : Function.Involutive n)
    (east : ∀ x y, φ (x + 1) y = e (φ x y)) (north : ∀ x y, φ x (y + 1) = n (φ x y))
    (x y u v : ℤ) : φ (x + 2 * u) (y + 2 * v) = φ x y := by
  have hx : Function.Periodic (fun a : ℤ => φ a (y + 2 * v)) 2 := fun a => by
    simpa only [show a + 2 = a + 1 + 1 by omega, east] using he _
  have hy : Function.Periodic (fun b : ℤ => φ x b) 2 := fun b => by
    simpa only [show b + 2 = b + 1 + 1 by omega, north] using hn _
  calc φ (x + 2 * u) (y + 2 * v) = φ x (y + 2 * v) := by
        simpa [mul_comm] using hx.int_mul u x
    _ = φ x y := by simpa [mul_comm] using hy.int_mul v y

private theorem exists_phase_origin (p : IndexPlane) :
    ∃ x y : Fin 2, (components (p.index x.val y.val)).thin = .a := by
  have he := thin_east (p.horizontal 0 0)
  cases h : (components (p.index 0 0)).thin with
  | a => exact ⟨0, 0, h⟩
  | b =>
    have he' : (components (p.index 1 0)).thin = .d := by simpa [h, phaseEast] using he
    exact ⟨1, 1, by simpa [he', phaseNorth] using thin_north (p.vertical 1 0)⟩
  | c => exact ⟨1, 0, by simpa [h, phaseEast] using he⟩
  | d => exact ⟨0, 1, by simpa [h, phaseNorth] using thin_north (p.vertical 0 0)⟩

private def neighborhood (p : IndexPlane) (x y : ℤ)
    (hphase : (components (p.index x y)).thin = .a) : Neighborhood where
  cell i j := p.index (x + i.val - 1) (y + j.val - 1)
  horizontal i j := by
    have hx : x + (i.val : ℤ) - 1 + 1 = x + (i.succ.val : ℤ) - 1 := by
      simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
      omega
    simpa only [Fin.val_castSucc, hx] using
      p.horizontal (x + (i.val : ℤ) - 1) (y + (j.val : ℤ) - 1)
  vertical i j := by
    have hy : y + (j.val : ℤ) - 1 + 1 = y + (j.succ.val : ℤ) - 1 := by
      simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
      omega
    simpa only [Fin.val_castSucc, hy] using
      p.vertical (x + (i.val : ℤ) - 1) (y + (j.val : ℤ) - 1)
  phase := by simpa using hphase

/-- Every matching corrected Robinson plane is a substituted matching plane up to translation. -/
theorem nonempty_parent (fine : IndexPlane) : Nonempty (Parent fine) := by
  obtain ⟨ox, oy, hphase⟩ := exists_phase_origin fine
  have hlocal (x y : ℤ) : ∃ p : Index, ∀ i j : Fin 2,
      childBlock p i j =
        fine.index ((ox.val : ℤ) + 2 * x + i.val) ((oy.val : ℤ) + 2 * y + j.val) := by
    obtain ⟨p, hp, _⟩ := existsUnique_centerParent
      (neighborhood fine ((ox.val : ℤ) + 2 * x) ((oy.val : ℤ) + 2 * y)
        ((phase_even_of_involutive (fun x y => (components (fine.index x y)).thin)
          phaseEast phaseNorth phaseEast_involutive phaseNorth_involutive
          (fun x y => thin_east (fine.horizontal x y))
          (fun x y => thin_north (fine.vertical x y)) ox.val oy.val x y).trans hphase))
    refine ⟨p, fun i j => ?_⟩
    fin_cases i <;> fin_cases j <;>
      simp [neighborhood, add_sub_assoc, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]
  choose coarse hc using hlocal
  refine ⟨⟨⟨coarse, fun x y => (horizontal_iff_children _ _).mpr fun j => ?_,
    fun x y => (vertical_iff_children _ _).mpr fun i => ?_⟩, ox, oy, hc⟩⟩
  · rw [hc x y 1 j, hc (x + 1) y 0 j]
    simpa [mul_add, add_assoc] using
      fine.horizontal ((ox.val : ℤ) + 2 * x + 1) ((oy.val : ℤ) + 2 * y + j.val)
  · rw [hc x y i 1, hc x (y + 1) i 0]
    simpa [mul_add, add_assoc] using
      fine.vertical ((ox.val : ℤ) + 2 * x + i.val) ((oy.val : ℤ) + 2 * y + 1)

/-- A substitution-parent tower above a prescribed indexed plane. -/
structure Tower (base : IndexPlane) where
  /-- The matching plane at each scale. -/
  plane : ℕ → IndexPlane
  /-- Alignment of horizontal child coordinates at each level. -/
  offsetX : ℕ → Fin 2
  /-- Alignment of vertical child coordinates at each level. -/
  offsetY : ℕ → Fin 2
  /-- Level zero is the prescribed plane. -/
  zero : plane 0 = base
  /-- Every adjacent pair of levels is related by the corrected substitution. -/
  children : ∀ (n : ℕ) (x y : ℤ) (i j : Fin 2),
    childBlock ((plane (n + 1)).index x y) i j =
      (plane n).index (((offsetX n).val : ℤ) + 2 * x + i.val)
        (((offsetY n).val : ℤ) + 2 * y + j.val)

private noncomputable def chooseParent (p : IndexPlane) : Parent p :=
  Classical.choice (nonempty_parent p)

private noncomputable def parentPlane (base : IndexPlane) : ℕ → IndexPlane
  | 0 => base
  | n + 1 => (chooseParent (parentPlane base n)).coarse

/-- Repeated desubstitution constructs a parent tower over every matching plane. -/
noncomputable def tower (base : IndexPlane) : Tower base where
  plane := parentPlane base
  offsetX n := (chooseParent (parentPlane base n)).offsetX
  offsetY n := (chooseParent (parentPlane base n)).offsetY
  zero := rfl
  children n := (chooseParent (parentPlane base n)).children

/-- Every level of a parent tower contains a translated refinement of any quadrant
at a higher level. -/
theorem Tower.refined_patch {base : IndexPlane} (t : Tower base) (depth : ℕ) :
    ∀ (level : ℕ) (a b : ℤ), ∃ u v : ℤ,
      (fun x y : ℕ => (t.plane level).index (u + x) (v + y)) =
        iterateRefine depth (fun x y : ℕ => (t.plane (level + depth)).index (a + x) (b + y)) := by
  induction depth with
  | zero => exact fun _ a b => ⟨a, b, rfl⟩
  | succ depth ih =>
    intro level a b
    obtain ⟨u, v, h⟩ := ih (level + 1) a b
    refine ⟨(t.offsetX level).val + 2 * u, (t.offsetY level).val + 2 * v,
      funext fun x => funext fun y => ?_⟩
    have index := congrFun (congrFun h (x / 2)) (y / 2)
    simp only [Nat.add_assoc, Nat.add_comm 1 depth] at index
    simp only [iterateRefine, refineIndexGrid, ← index, t.children]
    congr 1 <;> omega

private theorem expansion_occurs {base : IndexPlane} (t : Tower base)
    (depth level : ℕ) (x y : ℤ) (i j : ℕ) (hi : i < 2 ^ depth) (hj : j < 2 ^ depth) :
    ∃ u v : ℤ, (t.plane level).index u v =
      iterateRefine depth (fun _ _ => (t.plane (level + depth)).index x y) i j := by
  obtain ⟨u, v, patch⟩ := t.refined_patch depth level x y
  exact ⟨u + i, v + j, (congrFun (congrFun patch i) j).trans
    (iterateRefine_eq_of_root_eq (by simp) depth i j hi hj)⟩

/-- Every tile reaches tile `0` along the same path: its southwest child is a phase-`a` tile,
whose northeast child is tile `4`, whose southwest child is tile `0`. -/
private theorem zero_descends_cert :
    ∀ p : Index, childBlock (childBlock (childBlock p 0 0) 1 1) 0 0 = 0 := by
  decide +kernel

private theorem zero_descends :
    ∀ p : Index, ∃ i j : Fin 8, iterateRefine 3 (fun _ _ => p) i j = 0 :=
  fun p => ⟨2, 2, zero_descends_cert p⟩

/-- The parent of `p` in a spanning tree of the child relation rooted at tile `0`; every tile
reaches `0` within five steps (`fromZero_ok`). -/
private def fromZeroParent (p : Index) : Index :=
  if p.val == 0 then 0
  else if h1 : p.val < 4 then ⟨p.val + 4, by omega⟩
  else if h2 : p.val < 32 then
    match p.val with
    | 4 => 0 | 5 => 22 | 6 => 57 | 7 => 4
    | 8 => 18 | 9 => 14 | 10 => 19 | 11 => 15
    | 12 => 57 | 13 => 70 | 14 => 60 | 15 => 61
    | 16 => 5 | 17 => 4 | 18 => 7 | 19 => 6
    | 20 => 1 | 21 => 81 | 22 => 0 | 23 => 94
    | 24 => 3 | 25 => 84 | 26 => 2 | 27 => 85
    | 28 => 16 | 29 => 12 | 30 => 22 | _ => 13
  else if h3 : p.val < 56 then ⟨p.val - 24, by omega⟩
  else if h4 : p.val < 80 then
    match p.val with
    | 56 => 36 | 57 => 0 | 58 => 12 | 59 => 58
    | 60 => 57 | 61 => 4 | 62 => 41 | 63 => 1
    | 64 => 17 | 65 => 64 | 66 => 67 | 67 => 5
    | 68 => 46 | 69 => 2 | 70 => 22 | 71 => 70
    | 72 => 73 | 73 => 6 | 74 => 54 | 75 => 3
    | 76 => 30 | 77 => 76 | 78 => 79 | _ => 7
  else ⟨p.val - 24, by omega⟩

/-- The column of `p` among the children of `fromZeroParent p`. -/
private def fromZeroDx (p : Index) : Fin 2 :=
  if 4 ≤ p.val && p.val < 32 then 1 else 0

/-- The row of `p` among the children of `fromZeroParent p`. -/
private def fromZeroDy (p : Index) : Fin 2 :=
  if (4 ≤ p.val && p.val < 8) || (56 ≤ p.val && p.val < 80) then 1 else 0

private theorem fromZero_ok :
    ((List.finRange 104).all fun p =>
      (childBlock (fromZeroParent p) (fromZeroDx p) (fromZeroDy p) == p) &&
      (fromZeroParent^[5] p == 0)) = true := by
  decide +kernel

private theorem fromZero_child (p : Index) :
    childBlock (fromZeroParent p) (fromZeroDx p) (fromZeroDy p) = p :=
  beq_iff_eq.mp
    (Bool.and_eq_true_iff.mp (List.all_eq_true.mp fromZero_ok p (List.mem_finRange p))).1

private theorem fromZero_root (p : Index) : fromZeroParent^[5] p = 0 :=
  beq_iff_eq.mp
    (Bool.and_eq_true_iff.mp (List.all_eq_true.mp fromZero_ok p (List.mem_finRange p))).2

private theorem descends_step (n : ℕ) (p : Index) :
    ∃ i j : Fin (2 ^ n), iterateRefine n (fun _ _ => fromZeroParent^[n] p) i j = p := by
  induction n generalizing p with
  | zero => exact ⟨0, 0, rfl⟩
  | succ n ih =>
    obtain ⟨i, j, hij⟩ := ih (fromZeroParent p)
    refine ⟨⟨2 * i.val + (fromZeroDx p).val, by rw [pow_succ]; omega⟩,
      ⟨2 * j.val + (fromZeroDy p).val, by rw [pow_succ]; omega⟩, ?_⟩
    simpa only [Function.iterate_succ_apply, iterateRefine, refineIndexGrid_child, hij] using
      fromZero_child p

private theorem descends_zero :
    ∀ p : Index, ∃ i j : Fin 32, iterateRefine 5 (fun _ _ => 0) i j = p := fun p =>
  let ⟨i, j, hij⟩ := descends_step 5 p
  ⟨i, j, by simpa only [fromZero_root p] using hij⟩

/-- Every corrected tile type occurs at every level of every parent tower. -/
theorem Tower.every_tile {base : IndexPlane} (t : Tower base) (level : ℕ) (target : Index) :
    ∃ x y : ℤ, (t.plane level).index x y = target := by
  obtain ⟨i, j, hij⟩ := zero_descends ((t.plane (level + 5 + 3)).index 0 0)
  obtain ⟨x, y, hxy⟩ := expansion_occurs t 3 (level + 5) 0 0 i j i.isLt j.isLt
  obtain ⟨i', j', hij'⟩ := descends_zero target
  obtain ⟨u, v, huv⟩ := expansion_occurs t 5 level x y i' j' i'.isLt j'.isLt
  exact ⟨u, v, by rw [huv, hxy, hij, hij']⟩

private theorem parity_step (x : ℕ) :
    (x % 2 = 0 ∧ (x + 1) % 2 = 1 ∧ (x + 1) / 2 = x / 2) ∨
      (x % 2 = 1 ∧ (x + 1) % 2 = 0 ∧ (x + 1) / 2 = x / 2 + 1) := by
  omega

private theorem expansion_horizontal (n : ℕ) (p : Index) (x y : ℕ)
    (hx : x + 1 < 2 ^ n) :
    (tile (components (iterateRefine n (fun _ _ => p) x y))).right =
      (tile (components (iterateRefine n (fun _ _ => p) (x + 1) y))).left := by
  induction n generalizing x y with
  | zero => omega
  | succ n ih =>
    rcases parity_step x with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
      simp only [iterateRefine, refineIndexGrid, h1, h2, h3]
    · exact child_horizontal _ _
    · exact (horizontal_iff_children _ _).mp (ih (x / 2) (y / 2) (by rw [pow_succ] at hx; omega))
        ⟨y % 2, Nat.mod_lt _ (by decide)⟩

private theorem expansion_vertical (n : ℕ) (p : Index) (x y : ℕ)
    (hy : y + 1 < 2 ^ n) :
    (tile (components (iterateRefine n (fun _ _ => p) x y))).top =
      (tile (components (iterateRefine n (fun _ _ => p) x (y + 1)))).bottom := by
  induction n generalizing x y with
  | zero => omega
  | succ n ih =>
    rcases parity_step y with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
      simp only [iterateRefine, refineIndexGrid, h1, h2, h3]
    · exact child_vertical _ _
    · exact (vertical_iff_children _ _).mp (ih (x / 2) (y / 2) (by rw [pow_succ] at hy; omega))
        ⟨x % 2, Nat.mod_lt _ (by decide)⟩

private theorem square_bound {n x : ℕ} (h : x < n + 1) : x < 2 ^ n :=
  lt_of_lt_of_le h (Nat.succ_le_of_lt (show n < 2 ^ n from Nat.lt_two_pow_self))

private def square (n : ℕ) : Rectangle tileSet (n + 1) (n + 1) where
  tile i j := tile (components (iterateRefine n (fun _ _ => 0) i.val j.val))
  mem _i _j := tile_components_mem _
  horizontal i j hi := expansion_horizontal n 0 i.val j.val (square_bound hi)
  vertical i j hj := expansion_vertical n 0 i.val j.val (square_bound hj)

/-- The corrected Robinson tile set tiles the whole integer plane. -/
theorem tilesPlane_tileSet : TilesPlane tileSet :=
  (tilesPlane_iff_squares tileSet).mpr fun n => ⟨square n⟩

end Cslib.WangTile.Robinson
