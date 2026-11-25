/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Linear.FourierSize
public import CslibFrontier.Computability.Circuit.Linear.ToeplitzPacking
import CslibFrontier.Computability.Circuit.Linear.Model.Operations
import CslibFrontier.Foundations.Data.ZMod.Basic

/-!
# Gate bounds for the cyclic Fourier blocks of a Toeplitz reduction

The finite Fourier theorem counts binary linear gates and permits different frequency
enumerations in a batch. A primitive root identifies the explicit cyclic characters
with those enumerations.
-/

public section

open Cslib.Circuit.Linear

namespace Cslib.Circuit.ToeplitzPacking

variable {K : Type} [Field K] {c C : ℝ}
variable {n : ℕ} [NeZero n]

private theorem char_fin_mul (χ : AddChar (ZMod n) K) (x y : Fin n) :
    χ (ZMod.finEquiv n x * ZMod.finEquiv n y) = (χ 1) ^ (x.val * y.val) := by
  rw [← χ.map_nsmul_eq_pow, nsmul_eq_mul, mul_one, Nat.cast_mul, ZMod.finEquiv_eq_natCast,
    ZMod.finEquiv_eq_natCast]

private theorem cyclic_batch_bounds {T : Type} [Fintype T] [DecidableEq T]
    (hF : FourierSizeBounds K c C) (hn : 2 ≤ n) (hT : 1 ≤ Fintype.card T)
    (χ : T → AddChar (ZMod n) K) (hχ : ∀ t, IsPrimitiveRoot (χ t 1) n) :
    let h : ℝ := Fintype.card T * (n : ℝ)
    let M := Matrix.blockDiagonal fun t => Matrix.of (fun x y : ZMod n => χ t (x * y))
    c * h * Real.sqrt (Real.logb 2 n) ≤ (complexity M : ℝ) ∧
      (complexity M : ℝ) ≤ C * h * (1 + Real.logb 2 n) := by
  let e := (Fintype.equivFin T).symm
  let f := (ZMod.finEquiv n).toEquiv
  let B (t : Fin (Fintype.card T)) : FourierBlock K n :=
    { G := ZMod n
      admissible := admissible_zmod (hχ (e t))
      points := f
      frequencies := cyclicCharacterEquiv (hχ (e t))
      inverse := false }
  have hB (t : Fin (Fintype.card T)) : (B t).matrix = dftMatrix n (χ (e t) 1) :=
    reindex_fourierMatrix_zmod (hχ (e t))
  let M := Matrix.blockDiagonal fun t => Matrix.of (fun x y : ZMod n => χ t (x * y))
  have hM : Matrix.reindex (f.prodCongr e).symm (f.prodCongr e).symm M = batchMatrix B := by
    ext ⟨x, t⟩ ⟨y, u⟩
    change (if e t = e u then χ (e t) (f x * f y) else 0) =
      if t = u then (B t).matrix x y else 0
    by_cases h : t = u
    · subst u
      simpa only [↓reduceIte, hB, dftMatrix, Matrix.of_apply, f, RingEquiv.toEquiv_eq_coe,
        RingEquiv.coe_toEquiv] using char_fin_mul (χ (e t)) x y
    · simp only [ite_eq_right h, ite_eq_right (e.injective.ne h)]
  have hc : complexity M = complexity (batchMatrix B) := by
    rw [← hM, complexity_reindex]
  change _ ≤ (complexity M : ℝ) ∧ (complexity M : ℝ) ≤ _
  rw [hc]
  exact hF B hT hn

private theorem short_cost {ℓ : ℕ} [NeZero ℓ] (hF : FourierSizeBounds K c C)
    (hℓ : 2 ≤ ℓ) (ψ : AddChar (ZMod ℓ) K) (hψ : IsPrimitiveRoot (ψ 1) ℓ) :
    (complexity (shortFourier (n := n) ψ) : ℝ) ≤
      C * ((n : ℝ) * ℓ) * (1 + Real.logb 2 ℓ) := by
  let F := Matrix.blockDiagonal (fun _ : ZMod n => Matrix.of fun x y : ZMod ℓ => ψ (x * y))
  let e := Equiv.prodComm (ZMod ℓ) (ZMod n)
  have he : Matrix.reindex e e F = shortFourier ψ := by
    ext ⟨x, i⟩ ⟨y, j⟩
    rfl
  rw [← he, complexity_reindex]
  have hcard : 1 ≤ Fintype.card (ZMod n) := by
    rw [ZMod.card]
    exact Nat.pos_of_neZero _
  have hb := (cyclic_batch_bounds hF hℓ hcard (fun _ => ψ) (fun _ => hψ)).2
  simpa only [F, ZMod.card] using hb

private theorem realizable_encode {ℓ k : ℕ} [NeZero ℓ]
    (ρ : AddChar (ZMod n) K) (ψ : AddChar (ZMod ℓ) K)
    (u : ZMod n) (hdistinct : Function.Injective fun j : Fin k => (2 : ZMod ℓ) ^ j.val) :
    RealizableAtMost (encode (k := k) ρ ψ u) (complexity (shortFourier (n := n) ψ)) := by
  let f : ZMod n × Fin k ↪ ZMod n × ZMod ℓ :=
    Function.Embedding.prodMap (Function.Embedding.refl _) ⟨_, hdistinct⟩
  have h := ((realizableAtMost_complexity (shortFourier (n := n) ψ)).submatrix id f).diagonal
    (fun _ => 1) (chirp ρ u)
  convert h using 1
  ext a ⟨x, i⟩
  simp [encode, Matrix.mul_diagonal, mul_comm, f, frequency]

private theorem realizable_decode {ℓ k : ℕ} [NeZero ℓ]
    (ρ : AddChar (ZMod n) K) (ψ : AddChar (ZMod ℓ) K) (u : ZMod n) :
    RealizableAtMost (decode (k := k) ρ ψ u) (complexity (shortFourier (n := n) (-ψ))) := by
  have h := ((realizableAtMost_complexity (shortFourier (n := n) (-ψ))).submatrix
    (frequency (n := n) (ℓ := ℓ) (k := k)) (Function.Embedding.refl _)).diagonal
      (chirp ρ u) (fun _ => 1)
  convert h using 1
  ext a b
  simp [decode, Matrix.diagonal_mul]

private theorem complexity_repeated_blocks {ι T J : Type} [Fintype ι] [Fintype T] [Fintype J]
    [DecidableEq T] [DecidableEq J] (M : T → Matrix ι ι K) :
    complexity (Matrix.blockDiagonal fun _ : J => Matrix.blockDiagonal M) =
      complexity (Matrix.blockDiagonal fun t : T × J => M t.1) := by
  let e := Equiv.prodAssoc ι T J
  have he : Matrix.reindex e e (Matrix.blockDiagonal fun _ : J => Matrix.blockDiagonal M) =
      Matrix.blockDiagonal (fun t : T × J => M t.1) := by
    ext ⟨x, t, j⟩ ⟨y, a, b⟩
    by_cases ht : t = a <;> by_cases hj : j = b <;>
      simp [e, Matrix.reindex_apply, Matrix.blockDiagonal_apply, ht, hj]
  rw [← he, complexity_reindex]

variable {ℓ k J : ℕ} [NeZero ℓ] [Finite K] [Algebra (ZMod 2) K]

/-- A circuit over the two-element field for any number of copies of the trace convolution
would give one splitting-field circuit for all long Fourier transforms. Only the short
transforms incur an additional charge. Inputs, intermediate wires and outputs can be shared
across all copies in the original binary circuit. -/
theorem fourier_le_batchCost_add (hF : FourierSizeBounds K c C) (hn : 2 ≤ n) (hℓ : 2 ≤ ℓ)
    (hk : 0 < k) (hJ : 0 < J) (hnOdd : Nat.Coprime 2 n)
    (ρ : AddChar (ZMod n) K) (ψ : AddChar (ZMod ℓ) K)
    (hρ : IsPrimitiveRoot (ρ 1) n) (hψroot : IsPrimitiveRoot (ψ 1) ℓ) (hψ : ψ.IsPrimitive)
    (hℓK : (ℓ : K) = 1) (hdegree : Module.finrank (ZMod 2) K = k)
    (hdistinct : Function.Injective fun j : Fin k => (2 : ZMod ℓ) ^ j.val)
    (u : ZMod n) (hu : u + u = 1) :
    c * ((J * k : ℕ) : ℝ) * (n : ℝ) * Real.sqrt (Real.logb 2 n) ≤
      (complexity (Matrix.blockDiagonal fun _ : Fin J => Matrix.circulant (kernel ρ ψ u)) : ℝ) +
        2 * C * (J : ℝ) * n * ℓ * (1 + Real.logb 2 ℓ) := by
  let A := Matrix.circulant (kernel ρ ψ u)
  let φ := algebraMap (ZMod 2) K
  let E := encode (k := k) ρ ψ u
  let H := decode (k := k) ρ ψ u
  let χ (j : Fin k) := ρ ^ (2 ^ j.val)
  let L (j : Fin k) := Matrix.of (fun x y : ZMod n => χ j (x * y))
  have hpack : H * A.map φ * E = Matrix.blockDiagonal L :=
    decode_mul_circulant_mul_encode ρ hψ hℓK hdegree hdistinct u hu
  let B := Matrix.blockDiagonal fun _ : Fin J => A
  have hB := (realizableAtMost_complexity B).mapCoeff φ
  change RealizableAtMost ((Matrix.blockDiagonal fun _ : Fin J => A).map φ) (complexity B) at hB
  rw [Matrix.blockDiagonal_map _ _ (map_zero _)] at hB
  have hs := (((realizable_decode (k := k) ρ ψ u).blockDiagonal (Fin J)).mul hB).mul
    ((realizable_encode ρ ψ u hdistinct).blockDiagonal (Fin J))
  rw [← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul] at hs
  change RealizableAtMost (Matrix.blockDiagonal fun _ : Fin J => H * A.map φ * E) _ at hs
  rw [hpack] at hs
  have hcost := (complexity_le_iff ..).2 hs
  rw [complexity_repeated_blocks] at hcost
  have hprim (j : Fin k × Fin J) : IsPrimitiveRoot (χ j.1 1) n :=
    hρ.pow_of_coprime _ (hnOdd.pow_left _)
  have hcount : 1 ≤ Fintype.card (Fin k × Fin J) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    exact Nat.mul_pos hk hJ
  have hl := (cyclic_batch_bounds hF hn hcount (fun j : Fin k × Fin J => χ j.1) hprim).1
  have hcost' : (complexity (Matrix.blockDiagonal fun j : Fin k × Fin J => L j.1) : ℝ) ≤
      J * (complexity (shortFourier (n := n) (-ψ)) : ℝ) + (complexity B : ℝ) +
        J * (complexity (shortFourier (n := n) ψ) : ℝ) := by
    exact_mod_cast (by simpa only [Fintype.card_fin] using hcost :
      complexity (Matrix.blockDiagonal fun j : Fin k × Fin J => L j.1) ≤ _)
  have hsize := hl.trans hcost'
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] at hsize ⊢
  have hminus : IsPrimitiveRoot ((-ψ) 1) ℓ := by
    simpa only [AddChar.neg_apply'] using hψroot.inv
  have h1 := mul_le_mul_of_nonneg_left (short_cost (n := n) hF hℓ ψ hψroot) (Nat.cast_nonneg J)
  have h2 := mul_le_mul_of_nonneg_left (short_cost (n := n) hF hℓ (-ψ) hminus) (Nat.cast_nonneg J)
  change _ ≤ (complexity B : ℝ) + _
  linarith only [hsize, h1, h2]

end Cslib.Circuit.ToeplitzPacking
