/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.RingTheory.PowerSeries.Meixner
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The determinant `Ψ`

For Proposition B.2 (prop:identity) of *VP ≠ VNP over every field* [AnthropicVPVNP2026]. There are
four sites `a, b, c, d`; a word at a site is a pair (rows, columns) of tuples of natural numbers
(`Word`). `psi x` is the determinant of the matrix `matM x` with the blocks (rows `a, d | c, b`,
columns `a, d | c, b`) `ad: C`, `cb: -(y - 1) C`, `ac: Λ`, `ab: (y - 1) Λ B`, `dc: Bᵀ Λ`,
`db: -Λ`, and minus the transposes, where `y = x²`. Ring homomorphisms commute with it
(`map_psi`). Its value at `x = 1` and its reflection under `x ↦ 1/x` are proved with
Proposition B.2 (`Separation.Curvature.Identity`).

## Main definitions

* `Word`, `matM`, `psi`, and the blocks `blX`, `blY`, `blU`.

## Main results

* `map_matM`, `map_psi`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Proposition B.2 of the paper; module `Nc.Cross.Psi`
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic.Separation.Curvature

open Matrix Finset PowerSeries

/-- A word at a site: the tuples of row indices and of column indices. -/
@[ext] structure Word (μ : ℕ) where
  /-- The row indices. -/
  row : Fin μ → ℕ
  /-- The column indices. -/
  col : Fin μ → ℕ
  deriving DecidableEq

/-- The word with rows and columns exchanged. -/
def Word.swap {μ : ℕ} (w : Word μ) : Word μ := ⟨w.col, w.row⟩

@[simp] theorem Word.row_swap {μ : ℕ} (w : Word μ) : w.swap.row = w.col := by rfl

@[simp] theorem Word.col_swap {μ : ℕ} (w : Word μ) : w.swap.col = w.row := by rfl

@[simp] theorem Word.swap_swap {μ : ℕ} (w : Word μ) : w.swap.swap = w := by rfl

section blocks

variable {R : Type*} [CommRing R] {μ ν : ℕ}

/-- The block of rows and columns at `a, d`: the paper's `M₁`. -/
def blX (x : R) (sa : Word μ) (sd : Word ν) : Matrix (Fin μ ⊕ Fin ν) (Fin μ ⊕ Fin ν) R :=
  fromBlocks 0 (of fun i j => meixnerC (x ^ 2) (sa.row i) (sd.col j))
    (of fun i j => -meixnerC (x ^ 2) (sa.col j) (sd.row i)) 0

/-- The block of rows and columns at `c, b`: the paper's `M₂`. -/
def blY (x : R) (sc : Word μ) (sb : Word ν) : Matrix (Fin μ ⊕ Fin ν) (Fin μ ⊕ Fin ν) R :=
  fromBlocks 0 (of fun i j => -((x ^ 2 - 1) * meixnerC (x ^ 2) (sc.row i) (sb.col j)))
    (of fun i j => (x ^ 2 - 1) * meixnerC (x ^ 2) (sc.col j) (sb.row i)) 0

/-- The block of rows at `a, d` and columns at `c, b`. -/
def blU (x : R) (sa : Word μ) (sd : Word ν) (sc : Word μ) (sb : Word ν) :
    Matrix (Fin μ ⊕ Fin ν) (Fin μ ⊕ Fin ν) R :=
  fromBlocks (of fun i j => if sa.row i = sc.col j then x ^ (2 * sa.row i + 1) else 0)
    (of fun i j => (x ^ 2 - 1) * (x ^ (2 * sa.row i + 1) * meixnerB (x ^ 2) (sa.row i) (sb.col j)))
    (of fun i j => x ^ (2 * sc.col j + 1) * meixnerB (x ^ 2) (sc.col j) (sd.row i))
    (of fun i j => -(if sd.row i = sb.col j then x ^ (2 * sd.row i + 1) else 0))

/-- The paper's matrix **M**, with the rows and the columns in the order `a, d | c, b`. -/
def matM (x : R) (sa : Word μ) (sb : Word ν) (sc : Word μ) (sd : Word ν) :
    Matrix ((Fin μ ⊕ Fin ν) ⊕ (Fin μ ⊕ Fin ν)) ((Fin μ ⊕ Fin ν) ⊕ (Fin μ ⊕ Fin ν)) R :=
  fromBlocks (blX x sa sd) (blU x sa sd sc sb)
    (-(blU x sa.swap sd.swap sc.swap sb.swap)ᵀ) (blY x sc sb)

/-- The paper's `Ψ = det M`. -/
def psi (x : R) (sa : Word μ) (sb : Word ν) (sc : Word μ) (sd : Word ν) : R :=
    (matM x sa sb sc sd).det

theorem map_matM {S : Type*} [CommRing S] (f : R →+* S) (x : R) (sa : Word μ) (sb : Word ν)
    (sc : Word μ)
    (sd : Word ν) : f.mapMatrix (matM x sa sb sc sd) = matM (f x) sa sb sc sd := by
  ext i j
  rcases i with (i | i) | (i | i) <;> rcases j with (j | j) | (j | j) <;>
    simp [matM, blX, blY, blU, map_meixnerB, map_meixnerC, apply_ite f]

theorem map_psi {S : Type*} [CommRing S] (f : R →+* S) (x : R) (sa : Word μ) (sb : Word ν)
    (sc : Word μ)
    (sd : Word ν) : f (psi x sa sb sc sd) = psi (f x) sa sb sc sd := by
  rw [psi, psi, RingHom.map_det, map_matM]

end blocks

end Cslib.Circuits.Arithmetic.Separation.Curvature
