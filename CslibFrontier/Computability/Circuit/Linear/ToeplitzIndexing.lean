/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Linear.ToeplitzParameters
public import CslibFrontier.Computability.Circuit.Linear.ToeplitzConstruction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
import CslibFrontier.Foundations.Data.ZMod.Basic
import CslibFrontier.Foundations.Data.ZMod.NatCast
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log

/-!
# Uniform entry evaluation for the binary Toeplitz matrices

The stage and its cyclic dimensions are computed from unary input dimension. The field has at
most four more elements than that dimension, including at the small dimensions below stage zero.
Thus enumerating the binary field and evaluating the traces takes polynomial time in the
dimension. The row and column bookkeeping uses natural representatives of cyclic residues.
-/

public section

namespace Cslib.Circuit.ToeplitzLowerBound

open Turing.MultiTapeTM ComputableInPolyTime

/-- Natural representative of a difference modulo the axis length. -/
@[expose] def cyclicDiff (p x y : ℕ) : ℕ := (x % p + p - y % p) % p

theorem cyclicDiff_eq_val (p x y : ℕ) [NeZero p] :
    cyclicDiff p x y = ((x : ZMod p) - y).val := by
  simp only [cyclicDiff, ZMod.val_sub_eq_mod, ZMod.val_natCast]

/-- Exponent of the negative quadratic chirp in a cyclic group of odd order. -/
@[expose] def chirpIndex (n a : ℕ) : ℕ := (n - (((n + 1) / 2) * a * a) % n) % n

theorem chirpIndex_eq_val (n a : ℕ) [NeZero n] :
    chirpIndex n a = (-(((n + 1) / 2 : ℕ) : ZMod n) * (a : ZMod n) ^ 2).val := by
  calc
    _ = ((chirpIndex n a : ℕ) : ZMod n).val :=
      (ZMod.val_natCast_of_lt (Nat.mod_lt _ (NeZero.pos n))).symm
    _ = _ := by
      apply congrArg ZMod.val
      rw [chirpIndex, ZMod.natCast_mod, ZMod.natCast_sub_mod_eq_neg]
      push_cast
      ring

/-- The natural chirp coefficient represents the inverse of two modulo an odd length. -/
theorem add_half_succ_eq_one {n : ℕ} (hn : Odd n) :
    (((n + 1) / 2 : ℕ) : ZMod n) + (((n + 1) / 2 : ℕ) : ZMod n) = 1 := by
  have h : (n + 1) / 2 + (n + 1) / 2 = n + 1 := by obtain ⟨t, ht⟩ := hn; lia
  rw [← Nat.cast_add, h, Nat.cast_add_one, ZMod.natCast_self, zero_add]

/-- The field can be exhaustively searched in a polynomial in the unary dimension. -/
theorem fieldSize_stage_le (m : ℕ) : 2 ^ degree (stage m) ≤ m + 4 := by
  by_cases h : 3 ≤ m
  · have := (stage_bounds h).1
    rw [← size_add_one]
    lia
  · interval_cases m <;> decide

private theorem stage_polyTime : ComputableInPolyTime stage encUnary encUnary :=
  (unary_log_const 3).comp ((unary_div_const 2).comp (unary_log_two.comp unary_succ))

private theorem fieldParams_polyTime :
    ComputableInPolyTime (fun m => degree (stage m)) encUnary encUnary ∧
    ComputableInPolyTime (fun m => 2 ^ degree (stage m)) encUnary encUnary ∧
    ComputableInPolyTime (fun m => long (stage m)) encUnary encUnary ∧
    ComputableInPolyTime (fun m => short (stage m)) encUnary encUnary ∧
    ComputableInPolyTime (fun m => size (stage m)) encUnary encUnary := by
  have hcap : ComputableInPolyTime (fun m : ℕ => m + 4) encUnary encUnary :=
    unary_add' id' (const 4)
  have hthird : ComputableInPolyTime (fun m => 3 ^ stage m) encUnary encUnary :=
    binary_to_unary_bounded (binary_pow' (const 3) stage_polyTime) hcap fun m => by
      have h1 := (degree (stage m)).lt_two_pow_self
      have h2 := fieldSize_stage_le m
      unfold degree at h1 h2
      lia
  have hk : ComputableInPolyTime (fun m => degree (stage m)) encUnary encUnary :=
    unary_mul' (const 2) hthird
  have hfield : ComputableInPolyTime (fun m => 2 ^ degree (stage m)) encUnary encUnary :=
    binary_to_unary_bounded (binary_pow' (const 2) hk) hcap fieldSize_stage_le
  have hshort : ComputableInPolyTime (fun m => short (stage m)) encUnary encUnary := by
    simpa only [short, pow_succ] using unary_mul' hthird (const 3)
  have hsize : ComputableInPolyTime (fun m => size (stage m)) encUnary encUnary :=
    unary_sub' hfield (const 1)
  exact ⟨hk, hfield, unary_div' hsize hshort, hshort, hsize⟩

private theorem cyclicDiff_polyTime {I : Type} {enc : I ↪ List Bool} {p x y : I → ℕ}
    (hp : ComputableInPolyTime p enc encUnary) (hx : ComputableInPolyTime x enc encUnary)
    (hy : ComputableInPolyTime y enc encUnary) :
    ComputableInPolyTime (fun w => cyclicDiff (p w) (x w) (y w)) enc encUnary :=
  unary_mod' (unary_sub' (unary_add' (unary_mod' hx hp) hp) (unary_mod' hy hp)) hp

private theorem chirpIndex_polyTime {I : Type} {enc : I ↪ List Bool} {n a : I → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (ha : ComputableInPolyTime a enc encUnary) :
    ComputableInPolyTime (fun w => chirpIndex (n w) (a w)) enc encUnary :=
  unary_mod' (unary_sub' hn (unary_mod'
    (unary_mul' (unary_mul' (unary_div' (unary_add' hn (const 1)) (const 2)) ha) ha) hn)) hn

open Cslib.Circuit.ToeplitzPacking (tracePowers tracePowers_polyTime)

/-- Entry of the dimension-`m` Toeplitz matrix at row `i` and column `j`. -/
@[expose] def entryBit (m i j : ℕ) : Bool :=
  let r := stage m
  let copies := m / size r
  if i % copies = j % copies then
    tracePowers (degree r) (long r) (short r)
      (chirpIndex (long r) (cyclicDiff (long r) (i / copies) (j / copies)))
      (cyclicDiff (short r) (i / copies) (j / copies))
  else false

/-- Polynomial-time evaluation from unary dimension, row and column. -/
theorem entryBit_polyTime {I : Type} {enc : I ↪ List Bool} {m i j : I → ℕ}
    (hm : ComputableInPolyTime m enc encUnary) (hi : ComputableInPolyTime i enc encUnary)
    (hj : ComputableInPolyTime j enc encUnary) :
    ComputableInPolyTime (fun w => entryBit (m w) (i w) (j w)) enc encBool := by
  obtain ⟨hk, hfield, hn, hℓ, hsize⟩ := fieldParams_polyTime
  have hcopies := unary_div' hm (hsize.comp hm)
  have hrow := unary_div' hi hcopies
  have hcol := unary_div' hj hcopies
  have ha := cyclicDiff_polyTime (hn.comp hm) hrow hcol
  have hb := cyclicDiff_polyTime (hℓ.comp hm) hrow hcol
  have hkernel := tracePowers_polyTime (hk.comp hm) (hfield.comp hm).polyBounded
    (hn.comp hm) (hℓ.comp hm)
    (chirpIndex_polyTime (hn.comp hm) ha) hb
  have htest := unary_eq' (unary_mod' hi hcopies) (unary_mod' hj hcopies)
  simpa only [entryBit, decide_eq_true_eq, Function.comp_apply] using
    htest.ite hkernel (const false)

end Cslib.Circuit.ToeplitzLowerBound
