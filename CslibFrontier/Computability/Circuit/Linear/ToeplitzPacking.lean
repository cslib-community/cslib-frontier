/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.LinearAlgebra.Matrix.Circulant
public import Mathlib.Data.Matrix.Block
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Tactic.Ring

/-!
# Packing cyclic Fourier transforms into binary convolution

The absolute trace of a quadratic chirp times a short cyclic character gives a kernel over
`ZMod 2`. The Fourier transform in the short coordinate separates the Frobenius conjugates
of the chirp whenever their frequencies are distinct. Bluestein's diagonal factors then give
one independent cyclic Fourier transform for each conjugate.
-/

public section

namespace Cslib.Circuit.ToeplitzPacking

open Matrix
open scoped BigOperators

variable {n ℓ k : ℕ} {K : Type*} [Field K]

/-- The two-variable convolution kernel, with coefficients in the prime field. -/
@[expose] noncomputable def kernel [Finite K] [Algebra (ZMod 2) K]
    (ρ : AddChar (ZMod n) K) (ψ : AddChar (ZMod ℓ) K) (u : ZMod n)
    (p : ZMod n × ZMod ℓ) : ZMod 2 :=
  Algebra.trace (ZMod 2) K (ρ (-u * p.1 ^ 2) * ψ p.2)

/-- The short Fourier transform applied separately at each long coordinate. -/
@[expose] def shortFourier (ψ : AddChar (ZMod ℓ) K) :
    Matrix (ZMod n × ZMod ℓ) (ZMod n × ZMod ℓ) K :=
  Matrix.of fun p q => if p.1 = q.1 then ψ (p.2 * q.2) else 0

/-- The short-coordinate frequency of each Frobenius conjugate. -/
@[expose] def frequency (p : ZMod n × Fin k) : ZMod n × ZMod ℓ :=
  (p.1, (2 : ZMod ℓ) ^ p.2.val)

/-- The two diagonal scalings in Bluestein's convolution identity. -/
@[expose] def chirp (ρ : AddChar (ZMod n) K) (u : ZMod n) (p : ZMod n × Fin k) : K :=
  ρ (u * p.1 ^ 2) ^ (2 ^ p.2.val)

variable [NeZero n] [NeZero ℓ]

/-- Insert the active frequencies into the short transform after scaling their inputs. -/
@[expose] noncomputable def encode (ρ : AddChar (ZMod n) K) (ψ : AddChar (ZMod ℓ) K)
    (u : ZMod n) : Matrix (ZMod n × ZMod ℓ) (ZMod n × Fin k) K :=
  (shortFourier ψ).submatrix id frequency * Matrix.diagonal (chirp ρ u)

/-- Read the active frequencies of the negative short transform and scale their outputs. -/
@[expose] noncomputable def decode (ρ : AddChar (ZMod n) K) (ψ : AddChar (ZMod ℓ) K)
    (u : ZMod n) : Matrix (ZMod n × Fin k) (ZMod n × ZMod ℓ) K :=
  Matrix.diagonal (chirp ρ u) * (shortFourier (-ψ)).submatrix frequency id

private theorem frequency_sum {ψ : AddChar (ZMod ℓ) K} (hψ : ψ.IsPrimitive)
    (hℓ : (ℓ : K) = 1) (a b : ZMod ℓ) :
    ∑ y : ZMod ℓ, ψ ((a - b) * y) = if a = b then 1 else 0 := by
  by_cases hab : a = b
  · simp [hab, ZMod.card, hℓ]
  · rw [ite_eq_right hab]
    exact AddChar.sum_eq_zero_of_ne_one (hψ (sub_ne_zero.mpr hab))

omit [NeZero ℓ] in
private theorem char_pow (ψ : AddChar (ZMod ℓ) K) (b : ZMod ℓ) (j : ℕ) :
    ψ b ^ (2 ^ j) = ψ ((2 : ZMod ℓ) ^ j * b) := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  norm_cast

variable [Finite K] [Algebra (ZMod 2) K]

private theorem trace_eq (hdegree : Module.finrank (ZMod 2) K = k) (v : K) :
    algebraMap (ZMod 2) K (Algebra.trace (ZMod 2) K v) = ∑ j : Fin k, v ^ (2 ^ j.val) := by
  rw [FiniteField.algebraMap_trace_eq_sum_pow, hdegree, Nat.card_zmod, Finset.sum_range]

/-- Summing the shifted binary kernel against a short character selects a single conjugate. -/
private theorem sum_trace_character {ψ : AddChar (ZMod ℓ) K} (hψ : ψ.IsPrimitive)
    (hℓ : (ℓ : K) = 1) (hdegree : Module.finrank (ZMod 2) K = k)
    (hdistinct : Function.Injective fun j : Fin k => (2 : ZMod ℓ) ^ j.val)
    (v : K) (b : ZMod ℓ) (j : Fin k) :
    ∑ y : ZMod ℓ, algebraMap (ZMod 2) K (Algebra.trace (ZMod 2) K (v * ψ (b - y))) *
      ψ ((2 : ZMod ℓ) ^ j.val * y) = v ^ (2 ^ j.val) * ψ ((2 : ZMod ℓ) ^ j.val * b) := by
  classical
  calc
    _ = ∑ i : Fin k, v ^ (2 ^ i.val) * ψ ((2 : ZMod ℓ) ^ i.val * b) *
          ∑ y : ZMod ℓ, ψ (((2 : ZMod ℓ) ^ j.val - 2 ^ i.val) * y) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [trace_eq hdegree, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_pow, char_pow, mul_assoc, mul_assoc, ← AddChar.map_add_eq_mul,
        ← AddChar.map_add_eq_mul]
      congr 2
      ring
    _ = _ := by simp [frequency_sum hψ hℓ, hdistinct.eq_iff]

private theorem circulant_mul_encode_apply (ρ : AddChar (ZMod n) K) {ψ : AddChar (ZMod ℓ) K}
    (hψ : ψ.IsPrimitive) (hℓ : (ℓ : K) = 1) (hdegree : Module.finrank (ZMod 2) K = k)
    (hdistinct : Function.Injective fun j : Fin k => (2 : ZMod ℓ) ^ j.val)
    (u a x : ZMod n) (b : ZMod ℓ) (j : Fin k) :
    (((Matrix.circulant (kernel ρ ψ u)).map (algebraMap (ZMod 2) K) * encode ρ ψ u)
      (a, b) (x, j)) =
    (ρ (-u * (a - x) ^ 2) ^ (2 ^ j.val) * ψ ((2 : ZMod ℓ) ^ j.val * b)) *
      chirp ρ u (x, j) := by
  classical
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single x]
  · simp only [encode, Matrix.mul_diagonal, Matrix.submatrix_apply, shortFourier, of_apply,
      id_eq, frequency, ↓reduceIte, Matrix.map_apply, circulant_apply, kernel,
      Prod.fst_sub, Prod.snd_sub, ← mul_assoc, ← Finset.sum_mul]
    simpa only [mul_comm _ ((2 : ZMod ℓ) ^ j.val)] using
      congrArg (fun c => c * chirp ρ u (x, j))
        (sum_trace_character hψ hℓ hdegree hdistinct (ρ (-u * (a - x) ^ 2)) b j)
  · intro y _ hy
    simp [encode, Matrix.mul_diagonal, shortFourier, frequency, hy]
  · simp

/-- The binary convolution, between the two short transforms and their diagonal scalings,
computes independent copies of the cyclic Fourier matrix with its Frobenius-conjugate roots. -/
theorem decode_mul_circulant_mul_encode (ρ : AddChar (ZMod n) K) {ψ : AddChar (ZMod ℓ) K}
    (hψ : ψ.IsPrimitive) (hℓ : (ℓ : K) = 1) (hdegree : Module.finrank (ZMod 2) K = k)
    (hdistinct : Function.Injective fun j : Fin k => (2 : ZMod ℓ) ^ j.val)
    (u : ZMod n) (hu : u + u = 1) :
    decode ρ ψ u * (Matrix.circulant (kernel ρ ψ u)).map (algebraMap (ZMod 2) K) *
        encode ρ ψ u =
      Matrix.blockDiagonal (fun j : Fin k => Matrix.of fun a x : ZMod n =>
        ρ (a * x) ^ (2 ^ j.val)) := by
  classical
  ext ⟨a, i⟩ ⟨x, j⟩
  rw [Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp only [decode, Matrix.diagonal_mul, Matrix.submatrix_apply, shortFourier,
      Matrix.of_apply, frequency, id_eq, ↓reduceIte, AddChar.neg_apply,
      circulant_mul_encode_apply ρ hψ hℓ hdegree hdistinct,
      Matrix.blockDiagonal_apply']
    calc
      _ = (chirp ρ u (a, i) * ρ (-u * (a - x) ^ 2) ^ (2 ^ j.val) * chirp ρ u (x, j)) *
          ∑ b : ZMod ℓ, ψ (((2 : ZMod ℓ) ^ j.val - 2 ^ i.val) * b) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        rw [sub_mul]
        simp only [sub_eq_add_neg, AddChar.map_add_eq_mul]
        ring
      _ = _ := by
        simp only [frequency_sum hψ hℓ, hdistinct.eq_iff]
        by_cases hij : i = j
        · subst j
          simp only [↓reduceIte, mul_one, chirp, ← mul_pow, ← AddChar.map_add_eq_mul]
          congr 2
          calc
            _ = (u + u) * (a * x) := by ring
            _ = _ := by rw [hu, one_mul]
        · simp [hij, Ne.symm hij]
  · intro y _ hy
    simp [decode, Matrix.diagonal_mul, shortFourier, frequency, Ne.symm hy]
  · simp

end Cslib.Circuit.ToeplitzPacking
