/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Flip
public import CslibFrontier.Foundations.Data.BitString.Basic
public import Mathlib.Data.Matrix.Mul

/-!
# Partitions of the Boolean cube into open Hamming spheres

When the dimension is `2 ^ r`, the Boolean cube partitions into open spheres of radius one.
Each sphere contains the neighbors of its center, and does not contain the center itself.
The centers are the kernel of a parity-check map whose labels enumerate every `r`-bit string,
including the zero label. The map is the standard `Matrix.vecMul`, with the coordinate labels as
matrix rows. Flipping the coordinate named by an input's syndrome gives its unique
center. This is [Lupanov1961Formulas, §4, Lemma 3, printed/PDF p. 8 of the English
translation]. The source calls these sets spheres; its definition on p. 7 excludes the center.

## Main results

* `Cslib.BitString.vecMul_flipOn_singleton`: flipping bit `i` adds its row label.
* `Cslib.BitString.exists_openSpherePartition`: a set of `2 ^ (2 ^ r) / 2 ^ r` centers whose
  open spheres partition the cube, expressed as a bijection between center-coordinate pairs
  and inputs. The multiplicative cardinality identity also covers `r = 0`.
-/

public section

namespace Cslib.BitString

open Finset

variable {n r : ℕ}

/-- Flipping coordinate `i` adds its row label to the parity-check matrix product. -/
theorem vecMul_flipOn_singleton (label : Matrix (Fin n) (Fin r) Bool)
    (x : BitString n) (i : Fin n) :
    Matrix.vecMul (flipOn {i} x) label = Matrix.vecMul x label + label i := by
  have hflip : flipOn {i} x = x + Pi.single i (1 : Bool) := by
    funext j
    by_cases h : j = i
    · subst j
      simp only [flipOn_singleton_self, Pi.add_apply, Pi.single_eq_same]
      cases x i <;> rfl
    · simp [flipOn_singleton_of_ne h, h]
  rw [hflip, Matrix.add_vecMul, Matrix.single_one_vecMul]
  rfl

/-- The kernel centers of a complete parity-check labeling have disjoint open spheres covering
the cube. A center and its flipped coordinate are uniquely determined by the resulting point. -/
theorem bijective_flipOn_vecMul_zero (label : Fin n ≃ BitString r) :
    Function.Bijective (fun p :
        {c : BitString n // Matrix.vecMul c (Matrix.of fun i j => label i j) = 0} × Fin n =>
      let ⟨center, i⟩ := p
      flipOn {i} center.val) := by
  constructor
  · rintro ⟨⟨c, hc⟩, i⟩ ⟨⟨d, hd⟩, j⟩ h
    have hij : i = j := by
      apply label.injective
      have hs := congrArg (fun x => Matrix.vecMul x (Matrix.of fun i j => label i j)) h
      simp only [vecMul_flipOn_singleton, hc, hd, zero_add] at hs
      change label i = label j at hs
      exact hs
    subst j
    have hcd : c = d := by
      have := congrArg (flipOn {i}) h
      simpa only [flipOn_flipOn] using this
    subst d
    rfl
  · intro x
    let i := label.symm (Matrix.vecMul x (Matrix.of fun i j => label i j))
    have hc : Matrix.vecMul (flipOn {i} x) (Matrix.of fun i j => label i j) = 0 := by
      rw [vecMul_flipOn_singleton]
      change (Matrix.vecMul x (Matrix.of fun i j => label i j) : BitString r) + label i = 0
      rw [Equiv.apply_symm_apply]
      exact BitString.add_self _
    exact ⟨(⟨flipOn {i} x, hc⟩, i), flipOn_flipOn _ _⟩

/-- **Lupanov's open-sphere partition.** In dimension `2 ^ r`, the cube is partitioned into
open Hamming spheres of radius one. There are exactly `2 ^ (2 ^ r) / 2 ^ r` centers. The
bijection records both coverage and disjointness, including the boundary case `r = 0`.

This is [Lupanov1961Formulas, §4, Lemma 3, printed/PDF p. 8 of the translation]. -/
theorem exists_openSpherePartition (r : ℕ) :
    ∃ C : Finset (BitString (2 ^ r)),
      C.card * 2 ^ r = 2 ^ (2 ^ r) ∧
      Function.Bijective (fun p : {c // c ∈ C} × Fin (2 ^ r) =>
        let ⟨center, i⟩ := p
        flipOn {i} center.val) := by
  classical
  let label : Fin (2 ^ r) ≃ BitString r := (BitString.equivFin r).symm
  let C : Finset (BitString (2 ^ r)) :=
    univ.filter (fun c => Matrix.vecMul c (Matrix.of fun i j => label i j) = 0)
  let e : {c // c ∈ C} ≃
      {c : BitString (2 ^ r) // Matrix.vecMul c (Matrix.of fun i j => label i j) = 0} :=
    { toFun := fun c => ⟨c.1, by simpa only [C, mem_filter, mem_univ, true_and] using c.2⟩
      invFun := fun c => ⟨c.1, by simpa only [C, mem_filter, mem_univ, true_and] using c.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hbij : Function.Bijective
      (fun p : {c // c ∈ C} × Fin (2 ^ r) =>
        let ⟨center, i⟩ := p
        flipOn {i} center.val) := by
    exact (bijective_flipOn_vecMul_zero label).comp
      (e.prodCongr (Equiv.refl _)).bijective
  refine ⟨C, ?_, hbij⟩
  have hcard := Fintype.card_congr (Equiv.ofBijective _ hbij)
  simpa [BitString] using hcard

end Cslib.BitString
