/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Linear.ToeplitzComplexity
public import CslibFrontier.Computability.Circuit.Linear.ToeplitzIndexing
public import CslibFrontier.Computability.Circuit.Linear.ToeplitzPadding
public import CslibFrontier.Computability.PolyTime.LinearAlgebra.BitMatrixPrinter

/-!
# A polynomial-time constructible family of hard binary Toeplitz matrices

The executable `binaryToeplitz` is a square binary Toeplitz matrix at every dimension.
A deterministic multitape Turing machine prints all its entries in polynomial time from the
unary dimension. Assuming [OpenAI, Theorem 1.1][OpenAI2026FiniteFourier], its circuit
size is Ω(m √(log₂ m)) for all sufficiently large m.

This construction answers the Toeplitz question on page 6 of the 24 November 2026 note
*Explicit Linear Maps over F₂ That Are Hard for XOR Circuits and Rigid*.
It uses Bluestein's chirp factorization [Bluestein1970] and the finite-field trace
to pack independent cyclic transforms into a binary circulant. Interleaving many copies retains
the logarithmic factor between consecutive construction sizes. The circuits have unrestricted
depth and fan-out. Every binary linear gate has arbitrary coefficients in the two-element
field and the outputs can select wires freely.
-/

public section

namespace Cslib.Circuit.ToeplitzLowerBound

open ToeplitzPacking Cslib.Circuit.Linear
open Turing.MultiTapeTM Filter
open scoped Topology

/-- The dimension-`m` binary Toeplitz matrix, computed from its integer coordinates. -/
@[expose] def binaryToeplitz (m : ℕ) : Matrix (Fin m) (Fin m) (ZMod 2) :=
  Matrix.of fun i j => BitString.bitEquiv.symm (entryBit m i.val j.val)

/-- A polynomial-time multitape machine prints all `m²` bits in row-major order on unary input. -/
theorem binaryToeplitz_polyTime :
    ComputableInPolyTime (fun m => Cslib.Matrix.toBinary (w := 1) (binaryToeplitz m))
      encUnary encBits := by
  apply ComputableInPolyTime.matrixToBinary_one binaryToeplitz
    ComputableInPolyTime.id' ComputableInPolyTime.id'
    (entryBit_polyTime ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _))
      ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _))
      (ComputableInPolyTime.snd _ _))
  intro m i j
  change entryBit m i.val j.val = (BitString.bitEquiv.symm (entryBit m i.val j.val)).val.testBit 0
  cases entryBit m i.val j.val <;> decide

local instance (r : ℕ) : NeZero (long r) := ⟨(long_pos r).ne'⟩
local instance (r : ℕ) : NeZero (short r) := ⟨by have := three_le_short r; lia⟩

private theorem long_dvd (r : ℕ) : long r ∣ 2 ^ degree r - 1 :=
  ⟨short r, (long_mul_short r).symm⟩

private theorem short_dvd (r : ℕ) : short r ∣ 2 ^ degree r - 1 :=
  ⟨long r, (long_mul_short r).symm.trans (Nat.mul_comm ..)⟩

private noncomputable def axisChar {k d : ℕ} [NeZero d] (hk : k ≠ 0) (hd : d ∣ 2 ^ k - 1) :
    AddChar (ZMod d) (BinaryField k) :=
  AddChar.zmodChar d (isPrimitiveRoot_root hk (NeZero.pos d) hd).pow_eq_one

private theorem axisChar_one {k d : ℕ} [NeZero d] (hk : k ≠ 0) (hd : d ∣ 2 ^ k - 1) :
    IsPrimitiveRoot (axisChar hk hd 1) d := by
  rw [axisChar, ← Nat.cast_one (R := ZMod d), AddChar.zmodChar_apply', pow_one]
  exact isPrimitiveRoot_root hk (NeZero.pos d) hd

private noncomputable def stageKernel (r : ℕ) : ZMod (long r) × ZMod (short r) → ZMod 2 :=
  kernel (axisChar (degree_pos r).ne' (long_dvd r)) (axisChar (degree_pos r).ne' (short_dvd r))
    (((long r + 1) / 2 : ℕ) : ZMod (long r))

private theorem trace_index (r x y : ℕ) :
    tracePowers (degree r) (long r) (short r)
      (chirpIndex (long r) (cyclicDiff (long r) x y)) (cyclicDiff (short r) x y) =
    BitString.bitEquiv (stageKernel r ((x : ZMod (long r)) - y, (x : ZMod (short r)) - y)) := by
  let n := long r
  let ℓ := short r
  let u : ZMod n := ((n + 1) / 2 : ℕ)
  have h := tracePowers_eq_kernel (degree_pos r).ne' (long_dvd r) (short_dvd r) u
    (((x : ZMod n) - y), ((x : ZMod ℓ) - y))
  change tracePowers _ _ _ _ _ = _ at h
  convert h using 1
  · congr 1
    · change chirpIndex n (cyclicDiff n x y) = (-u * ((x : ZMod n) - y) ^ 2).val
      rw [chirpIndex_eq_val, cyclicDiff_eq_val, ZMod.natCast_zmod_val]
    · exact cyclicDiff_eq_val ℓ x y
  · rfl

private theorem binaryToeplitz_eq_interleave (m : ℕ) :
    binaryToeplitz m = interleave (stageKernel (stage m)) (m / size (stage m)) m := by
  ext i j
  simp only [binaryToeplitz, Matrix.of_apply, entryBit, interleave]
  split
  · rw [trace_index, RingEquiv.symm_apply_apply]
  · rfl

/-- At each dimension the computed matrix has a single coefficient on each ordinary diagonal. -/
theorem exists_toeplitz_eq_binaryToeplitz (m : ℕ) :
    ∃ a : Fin (m + m - 1) → ZMod 2, Matrix.toeplitz a = binaryToeplitz m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨0, by ext i; exact i.elim0⟩
  rw [binaryToeplitz_eq_interleave]
  exact exists_toeplitz_interleave _ hm.ne'

/-- From the published batched Fourier bounds, the explicit binary Toeplitz family requires
Ω(m √(log₂ m)) gates in shared, unbounded-depth, fan-in-two linear circuits over `ZMod 2`.
The Fourier constants are uniform across fields and orders. -/
theorem binaryToeplitz_size_of_fourierSizeBounds {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hF : ∀ (K : Type) [Field K], FourierSizeBounds K c C) :
    ∀ᶠ m : ℕ in atTop, c / 36 * m * Real.sqrt (Real.logb 2 m) ≤
      (complexity (binaryToeplitz m) : ℝ) := by
  filter_upwards [eventually_batch_bound hc hC] with m hm
  let r := stage m
  let J := m / size r
  obtain ⟨hJ, hfit, hn, hbound⟩ := hm
  let hk := (degree_pos r).ne'
  let ρ := axisChar hk (long_dvd r)
  let ψ := axisChar hk (short_dvd r)
  have hℓ : 2 ≤ short r := le_trans (by decide : 2 ≤ 3) (three_le_short r)
  have hψ := AddChar.zmodChar_primitive_of_primitive_root (short r)
    (isPrimitiveRoot_root hk (NeZero.pos (short r)) (short_dvd r))
  have hℓK : (short r : BinaryField (degree r)) = 1 :=
    natCast_eq_one_of_odd_of_two_eq_zero (odd_short r) (CharP.cast_eq_zero _ 2)
  have hdegree : Module.finrank (ZMod 2) (BinaryField (degree r)) = degree r := by
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (BinaryField.basis hk)
  have hcost := fourier_le_batchCost_add (hF (BinaryField (degree r))) hn hℓ (degree_pos r) hJ
    (odd_long r).coprime_two_left ρ ψ (axisChar_one hk (long_dvd r))
    (axisChar_one hk (short_dvd r)) hψ hℓK hdegree (frobeniusFreq_injective r) _
    (add_half_succ_eq_one (odd_long r))
  have hslots : long r * short r * J ≤ m := by rwa [long_mul_short, Nat.mul_comm]
  have hpad := complexity_batch_circulant_le_interleave (coprime_long_short r) hslots
    (stageKernel r)
  apply hbound
  rw [binaryToeplitz_eq_interleave]
  apply le_trans ?_ (add_le_add (Nat.cast_le.mpr hpad) (le_refl _))
  simpa only [stageKernel, ρ, ψ, hk, r, Nat.cast_mul, mul_assoc] using hcost

end Cslib.Circuit.ToeplitzLowerBound
