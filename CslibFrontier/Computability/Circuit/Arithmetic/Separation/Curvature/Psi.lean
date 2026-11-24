/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.RingTheory.PowerSeries.Meixner
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.Terms
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span

/-!
# The determinant `Ψ`

For Proposition B.2 (prop:identity) of *VP ≠ VNP over every field* [AnthropicVPVNP2026]. There are
four sites `a, b, c, d`; a word at a site is a pair (rows, columns) of tuples of natural numbers
(`Word`). `psi x` is the determinant of the matrix `matM x` with the blocks (rows `a, d | c, b`,
columns `a, d | c, b`) `ad: C`, `cb: -(y - 1) C`, `ac: Λ`, `ab: (y - 1) Λ B`, `dc: Bᵀ Λ`,
`db: -Λ`, and minus the transposes, where `y = x²`. Ring homomorphisms commute with it
(`map_psi`).

## Main definitions

* `Word`, `matM`, `psi`, and the blocks `blX`, `blY`, `blU`, `facA`, `facB`.

## Main results

* `map_matM`, `map_psi`, `dvd_det_sub`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Proposition B.2 of the paper; module `Nc.Cross.Psi`
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic.Separation.Curvature

open Matrix Finset PowerSeries

/-- Words: rows and columns at a site. -/
abbrev Word (μ : ℕ) := (Fin μ → ℕ) × (Fin μ → ℕ)

section blocks

variable {R : Type*} [CommRing R] {μ ν : ℕ}

/-- The block of rows and columns at `a, d`: the paper's `M₁`. -/
def blX (x : R) (sa : Word μ) (sd : Word ν) : Matrix (Fin μ ⊕ Fin ν) (Fin μ ⊕ Fin ν) R :=
  fromBlocks 0 (of fun i j => meixnerC (x ^ 2) (sa.1 i) (sd.2 j))
    (of fun i j => -meixnerC (x ^ 2) (sa.2 j) (sd.1 i)) 0

/-- The block of rows and columns at `c, b`: the paper's `M₂`. -/
def blY (x : R) (sc : Word μ) (sb : Word ν) : Matrix (Fin μ ⊕ Fin ν) (Fin μ ⊕ Fin ν) R :=
  fromBlocks 0 (of fun i j => -((x ^ 2 - 1) * meixnerC (x ^ 2) (sc.1 i) (sb.2 j)))
    (of fun i j => (x ^ 2 - 1) * meixnerC (x ^ 2) (sc.2 j) (sb.1 i)) 0

/-- The block of rows at `a, d` and columns at `c, b`. -/
def blU (x : R) (sa : Word μ) (sd : Word ν) (sc : Word μ) (sb : Word ν) :
    Matrix (Fin μ ⊕ Fin ν) (Fin μ ⊕ Fin ν) R :=
  fromBlocks (of fun i j => if sa.1 i = sc.2 j then x ^ (2 * sa.1 i + 1) else 0)
    (of fun i j => (x ^ 2 - 1) * (x ^ (2 * sa.1 i + 1) * meixnerB (x ^ 2) (sa.1 i) (sb.2 j)))
    (of fun i j => x ^ (2 * sc.2 j + 1) * meixnerB (x ^ 2) (sc.2 j) (sd.1 i))
    (of fun i j => -(if sd.1 i = sb.2 j then x ^ (2 * sd.1 i + 1) else 0))

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

/-- The paper's `F`: the rows `([r = i])_{r<K}` for `i ∈ I_a` and `(B(r,i))_{r<K}` for `i ∈ I_d`. -/
def facA (K : ℕ) (x : R) (sa : Word μ) (sd : Word ν) : Matrix (Fin μ ⊕ Fin ν) (Fin K) R :=
  of (Sum.elim (fun i r => if sa.1 i = (r : ℕ) then 1 else 0) fun i r =>
      meixnerB (x ^ 2) r (sd.1 i))

/-- The paper's `G`: the columns `([r = j])_{r<K}` for `j ∈ J_c` and `((y−1)B(r,j))_{r<K}` for `j ∈
J_b`. -/
def facB (K : ℕ) (x : R) (sc : Word μ) (sb : Word ν) : Matrix (Fin K) (Fin μ ⊕ Fin ν) R :=
  of fun r => Sum.elim (fun j => if (r : ℕ) = sc.2 j then 1 else 0)
    fun j => (x ^ 2 - 1) * meixnerB (x ^ 2) r (sb.2 j)

theorem sum_ite_val (K n : ℕ) (f : ℕ → R) :
    ∑ r : Fin K, (if n = (r : ℕ) then f r else 0) = if n < K then f n else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun r => if n = r then f r else 0) K, Finset.sum_ite_eq]
  simp

end blocks

/-- Congruent matrices have congruent determinants. -/
theorem dvd_det_sub {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n] (d : R)
    (M N : Matrix n n R)
    (h : ∀ i j, d ∣ M i j - N i j) : d ∣ M.det - N.det := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, RingHom.map_det, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  exact h i j

end Cslib.Circuits.Arithmetic.Separation.Curvature
