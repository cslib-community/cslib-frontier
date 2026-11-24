/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# `Bool`-linear equivalences for concatenating and partitioning bit strings

Bit strings form `Bool`-modules under coordinatewise exclusive or (`BooleanRing Bool`). This module
packages length congruence, binary concatenation (`Fin.append` / `fstBits` / `sndBits`), and
variable-length block slicing (`finSigmaFinEquiv`) as `Bool`-linear equivalences (`≃ₗ[Bool]`).
Definitions and simp interface equations only.

## Main definitions

* `Cslib.BitString.congrLinearEquiv`: `BitString n₁ ≃ₗ[Bool] BitString n₂` from `n₁ = n₂`.
* `Cslib.BitString.appendLinearEquiv`: `(BitString a × BitString b) ≃ₗ[Bool] BitString (a + b)` via
  `Fin.append` and `(fstBits, sndBits)`.
* `Cslib.BitString.piBlocksLinearEquiv`:
  `BitString (∑ i, b i) ≃ₗ[Bool] (∀ i : Fin t, BitString (b i))` via `finSigmaFinEquiv`.
-/

public section

namespace Cslib.BitString

/-- `Bool`-linear equivalence between bit-string spaces of equal lengths. -/
def congrLinearEquiv {n₁ n₂ : ℕ} (h : n₁ = n₂) : BitString n₁ ≃ₗ[Bool] BitString n₂ where
  toFun x i := x (Fin.cast h.symm i)
  invFun y j := y (Fin.cast h j)
  left_inv x := funext fun j => by simp
  right_inv y := funext fun i => by simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem congrLinearEquiv_apply {n₁ n₂ : ℕ} (h : n₁ = n₂) (x : BitString n₁) (i : Fin n₂) :
    congrLinearEquiv h x i = x (Fin.cast h.symm i) := by
  rfl

@[simp]
theorem congrLinearEquiv_symm {n₁ n₂ : ℕ} (h : n₁ = n₂) :
    (congrLinearEquiv h).symm = congrLinearEquiv h.symm := by
  rfl

/-- `Bool`-linear equivalence concatenating `BitString a × BitString b` into `BitString (a + b)`
via `Fin.append`, with inverse `(fstBits, sndBits)`. -/
def appendLinearEquiv (a b : ℕ) : (BitString a × BitString b) ≃ₗ[Bool] BitString (a + b) where
  toEquiv := Fin.appendEquiv a b
  map_add' p q := funext fun i => by
    induction i using Fin.addCases with
    | left j =>
      simp only [Equiv.toFun_as_coe, Fin.appendEquiv_apply, Prod.fst_add, Fin.append_left,
        Pi.add_apply]
    | right j =>
      simp only [Equiv.toFun_as_coe, Fin.appendEquiv_apply, Prod.snd_add, Fin.append_right,
        Pi.add_apply]
  map_smul' c p := funext fun i => by
    induction i using Fin.addCases with
    | left j =>
      simp only [Equiv.toFun_as_coe, Fin.appendEquiv_apply, Prod.smul_fst, Fin.append_left,
        RingHom.id_apply, Pi.smul_apply]
    | right j =>
      simp only [Equiv.toFun_as_coe, Fin.appendEquiv_apply, Prod.smul_snd, Fin.append_right,
        RingHom.id_apply, Pi.smul_apply]

@[simp]
theorem appendLinearEquiv_apply {a b : ℕ} (p : BitString a × BitString b) :
    appendLinearEquiv a b p = Fin.append p.1 p.2 := by
  rfl

@[simp]
theorem appendLinearEquiv_symm_apply {a b : ℕ} (x : BitString (a + b)) :
    (appendLinearEquiv a b).symm x = (fstBits x, sndBits x) := by
  rfl

/-- `Bool`-linear equivalence partitioning `BitString (∑ i, b i)` into `t` blocks of lengths
`b : Fin t → ℕ` via `finSigmaFinEquiv`. -/
def piBlocksLinearEquiv {t : ℕ} (b : Fin t → ℕ) :
    BitString (∑ i, b i) ≃ₗ[Bool] (∀ i : Fin t, BitString (b i)) where
  toFun x i j := x (finSigmaFinEquiv ⟨i, j⟩)
  invFun g k := g (finSigmaFinEquiv.symm k).1 (finSigmaFinEquiv.symm k).2
  left_inv x := funext fun k => by simp
  right_inv g := funext fun i => funext fun j => by
    change g (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨i, j⟩)).1
      (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨i, j⟩)).2 = g i j
    rw [finSigmaFinEquiv.symm_apply_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem piBlocksLinearEquiv_apply {t : ℕ} (b : Fin t → ℕ) (x : BitString (∑ i, b i)) (i : Fin t)
    (j : Fin (b i)) :
    piBlocksLinearEquiv b x i j = x (finSigmaFinEquiv ⟨i, j⟩) := by
  rfl

@[simp]
theorem piBlocksLinearEquiv_symm_apply {t : ℕ} (b : Fin t → ℕ) (g : ∀ i : Fin t, BitString (b i))
    (k : Fin (∑ i, b i)) :
    (piBlocksLinearEquiv b).symm g k =
      g (finSigmaFinEquiv.symm k).1 (finSigmaFinEquiv.symm k).2 := by
  rfl

end Cslib.BitString
