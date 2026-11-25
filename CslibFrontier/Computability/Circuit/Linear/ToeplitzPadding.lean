/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Toeplitz
public import CslibFrontier.Computability.Circuit.Linear.Model.Basic
public import Mathlib.LinearAlgebra.Matrix.Circulant
public import Mathlib.Data.ZMod.Basic
import CslibFrontier.Computability.Circuit.Linear.Model.Rewire
import Mathlib.Data.Nat.ModEq
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Interleaving cyclic convolutions inside a Toeplitz matrix

For coprime cyclic lengths, the Chinese remainder theorem places one copy of a bivariate
convolution on ordinary cyclic diagonals. Placing its entries every `J` diagonals packs
`J` independent copies into the leading principal submatrix. The remaining rows and columns
extend the same diagonals to the requested dimension.
-/

public section

namespace Cslib.Circuit.ToeplitzPacking

open Cslib.Circuit.Linear

/-- Read a cyclic kernel on the quotient coordinates of a common residue class modulo `J`.
Distinct residue classes supply the zero blocks between copies. -/
@[expose] def interleave {α : Type*} [Zero α] {n ℓ : ℕ}
    (h : ZMod n × ZMod ℓ → α) (J M : ℕ) : Matrix (Fin M) (Fin M) α :=
  Matrix.of fun i j => if i.val % J = j.val % J then
    h (((i.val / J : ℕ) : ZMod n) - (j.val / J : ℕ),
       ((i.val / J : ℕ) : ZMod ℓ) - (j.val / J : ℕ)) else 0

private theorem modEq_iff_of_add_eq {a b c d J : ℕ} (he : a + d = b + c) :
    a ≡ c [MOD J] ↔ b ≡ d [MOD J] := by
  have h : a + d ≡ c + b [MOD J] := by rw [he, Nat.add_comm b c]
  exact ⟨fun ha => (ha.add_left_cancel h).symm,
    fun hb => hb.symm.add_right_cancel h⟩

/-- The interleaved extension is constant on ordinary diagonals at every positive dimension. -/
theorem exists_toeplitz_interleave {α : Type*} [Zero α] {n ℓ J M : ℕ}
    (h : ZMod n × ZMod ℓ → α) (hM : M ≠ 0) :
    ∃ a, Matrix.toeplitz a = interleave h J M := by
  apply (Matrix.exists_toeplitz_eq_iff hM hM).2
  intro i i' j j' he
  have hm := modEq_iff_of_add_eq (J := J) he
  change _ % J = _ % J ↔ _ % J = _ % J at hm
  by_cases hij : i.val % J = j.val % J
  · have hij' := hm.mp hij
    have hs : i.val / J + j'.val / J = i'.val / J + j.val / J := by
      obtain rfl | hJ := Nat.eq_zero_or_pos J
      · simp
      apply Nat.eq_of_mul_eq_mul_left hJ
      rw [Nat.mul_add, Nat.mul_add]
      have hi := Nat.mod_add_div i.val J
      have hi' := Nat.mod_add_div i'.val J
      have hj := Nat.mod_add_div j.val J
      have hj' := Nat.mod_add_div j'.val J
      lia
    have eqsub (p : ℕ) :
        ((i.val / J : ℕ) : ZMod p) - (j.val / J : ℕ) =
          ((i'.val / J : ℕ) : ZMod p) - (j'.val / J : ℕ) := by
      apply sub_eq_sub_iff_add_eq_add.mpr
      exact_mod_cast congrArg (fun a : ℕ => (a : ZMod p)) hs
    simp [interleave, hij, hij', eqsub]
  · simp [interleave, hij, mt hm.mpr hij]

private def residueIndex {n ℓ : ℕ} [NeZero n] [NeZero ℓ] (hc : n.Coprime ℓ) :
    (ZMod n × ZMod ℓ) ↪ Fin (n * ℓ) where
  toFun p := ⟨((ZMod.chineseRemainder hc).symm p).val, ZMod.val_lt _⟩
  inj' := fun _ _ he => (ZMod.chineseRemainder hc).symm.injective
    (ZMod.val_injective _ (congrArg Fin.val he))

private theorem residueIndex_spec {n ℓ : ℕ} [NeZero n] [NeZero ℓ] (hc : n.Coprime ℓ)
    (p : ZMod n × ZMod ℓ) :
    (((residueIndex hc p).val : ZMod n), ((residueIndex hc p).val : ZMod ℓ)) = p := by
  let e := ZMod.chineseRemainder hc
  change (((e.symm p).val : ℕ) : ZMod n × ZMod ℓ) = p
  rw [← map_natCast e, ZMod.natCast_zmod_val, e.apply_symm_apply]

/-- A circuit for the padded matrix realizes the whole direct sum, with the same gate budget.
The circuit is free to share intermediate values between different residue classes. -/
theorem complexity_batch_circulant_le_interleave {K : Type*} [CommSemiring K] {n ℓ J M : ℕ}
    [NeZero n] [NeZero ℓ] (hc : n.Coprime ℓ) (hfit : n * ℓ * J ≤ M)
    (h : ZMod n × ZMod ℓ → K) :
    complexity (Matrix.blockDiagonal fun _ : Fin J => Matrix.circulant h) ≤
      complexity (interleave h J M) := by
  let e := ((residueIndex hc).prodMap (Function.Embedding.refl (Fin J))).trans
    (finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb hfit))
  have he (x : ZMod n × ZMod ℓ) (j : Fin J) :
      (e (x,j)).val = j.val + J * (residueIndex hc x).val := rfl
  apply (complexity_le_iff ..).2
  convert (realizableAtMost_complexity (interleave h J M)).submatrix e e using 1
  ext ⟨x,i⟩ ⟨y,j⟩
  have hJ : 0 < J := Nat.zero_lt_of_lt i.isLt
  have hmod (x : ZMod n × ZMod ℓ) (i : Fin J) : (e (x,i)).val % J = i.val := by
    rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]
  have hdiv (x : ZMod n × ZMod ℓ) (i : Fin J) :
      (e (x,i)).val / J = (residueIndex hc x).val := by
    rw [he, Nat.add_mul_div_left _ _ hJ, Nat.div_eq_of_lt i.isLt, Nat.zero_add]
  simp only [Matrix.blockDiagonal_apply', Matrix.submatrix_apply, interleave, Matrix.of_apply,
    hmod, hdiv, Fin.val_inj, Matrix.circulant_apply]
  by_cases hij : i = j
  · simp only [hij, ↓reduceIte]
    exact congrArg h ((congrArg₂ (· - ·) (residueIndex_spec hc x) (residueIndex_spec hc y)).symm)
  · simp [hij]

end Cslib.Circuit.ToeplitzPacking
