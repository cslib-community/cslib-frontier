/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NisanGenerator
public import CslibFrontier.Probability.SaksZhou.Nisan
public import CslibFrontier.Foundations.Data.BitString.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.ListSlice
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatPow
import CslibFrontier.Foundations.Data.List.OfFn

/-!
# Enumerating the shared seeds in Saks–Zhou powering

The low bits of a natural hold all the Toeplitz hash seeds, in the same order as the packed
Nisan generator. Consecutive fields above them hold the individual rounding shifts. Each seed is
visited exactly once, including when a field has zero width. This gives a counter enumeration of
the finite averaging space in the Saks–Zhou construction [SaksZhou1999].

## Main definitions

* `nisanBlockValue` decodes the integer value of an individual walk letter.
* `nisanRoundingShift` reads a rounding shift directly from the packed integer.
* `nisanShiftSeedOfNat` decodes the shared hashes and rounding shifts from a binary counter.

## Main results

* `nisanBlockValue_eq` identifies the packed letter with the little-endian Nisan block.
* `budget_nisanBlockValue` computes the letter in the argument budget plus one block width.
* `budget_nisanRoundingShift` extracts a shift within the work-space budget of its binary arguments.
* `countP_range_nisanShiftSeedOfNat` converts the count of accepted counter values to the
  cardinality of the accepted seed set.
* `seedOfNat_mul_add` combines a fresh initial block with the packed shared hashes for Nisan's
  on-demand generator.

## References

* [M. Saks, S. Zhou, *BP_H SPACE(S) ⊆ DSPACE(S^{3/2})*][SaksZhou1999]
-/

public section

namespace Cslib.Probability.SaksZhou

open Crypto.PRG.Nisan Finset

/-- The value in the `i`-th rounding field following the `k` Toeplitz seeds. -/
@[expose] def nisanRoundingShift (b k d z i : ℕ) : ℕ :=
  (z >>> (k * (3 * b - 1) + i * d)) % 2 ^ d

/-- The low `k * (3 * b - 1)` bits of `z` hold the `k` Toeplitz seeds for `b`-bit
blocks, diagonals first. The next `r` fields of `d` bits hold the rounding shifts, in round
order and little-endian. -/
@[expose] def nisanShiftSeedOfNat (b k r d z : ℕ) : NisanShiftSeed b k r d :=
  (fun l => hashSeedOfNat b z (l * (3 * b - 1)), fun i =>
    ⟨nisanRoundingShift b k d z i, Nat.mod_lt _ (Nat.two_pow_pos _)⟩)

/-- Placing an initial block below the shared seed yields exactly the Nisan input layout.
Bits holding the rounding shifts lie beyond all the requested hashes. -/
theorem seedOfNat_mul_add (b k r d z : ℕ) {x : ℕ} (hx : x < 2 ^ b) :
    seedOfNat b k (z * 2 ^ b + x) =
      (fun i : Fin b => x.testBit i, (nisanShiftSeedOfNat b k r d z).1) := by
  rw [Nat.mul_comm z]
  apply Prod.ext
  · funext i
    simp [seedOfNat, Nat.testBit_two_pow_mul_add, hx]
  · funext l
    apply Prod.ext <;> funext i <;>
      simp [seedOfNat, nisanShiftSeedOfNat, hashSeedOfNat, Nat.testBit_two_pow_mul_add, hx,
        Nat.add_assoc]

/-- The integer value of the `t`-th Nisan block on initial block `x` and shared seed `z`.
Only the low `b` bits of the register are part of the walk letter. -/
@[expose] def nisanBlockValue (b k z x t : ℕ) : ℕ :=
  blockNat b k (z * 2 ^ b + x) t % 2 ^ b

/-- The letter computed from the packed seed has the little-endian numbering of the
corresponding mathematical Nisan block. -/
theorem nisanBlockValue_eq (b k r d z : ℕ) {x t : ℕ} (hx : x < 2 ^ b) (ht : t < 2 ^ k) :
    nisanBlockValue b k z x t = BitString.equivFin b
      (blocks toeplitzHash k (fun i : Fin b => x.testBit i)
        (nisanShiftSeedOfNat b k r d z).1 ⟨t, ht⟩) := by
  let seed := z * 2 ^ b + x
  have hv := testBit_blockNat b k seed t ht
  rw [show seedOfNat b k seed = _ from seedOfNat_mul_add b k r d z hx] at hv
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < b
  · rw [nisanBlockValue, Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]
    exact (congrFun hv ⟨i, hi⟩).trans (BitString.testBit_equivFin _ ⟨i, hi⟩).symm
  · rw [Nat.testBit_lt_two_pow, Nat.testBit_lt_two_pow] <;>
      exact lt_of_lt_of_le (by first | exact Nat.mod_lt _ (Nat.two_pow_pos _) | exact Fin.isLt _)
        (Nat.pow_le_pow_right two_pos (by omega))

/-- The bounded counter visits each shared seed once. -/
theorem bijective_nisanShiftSeedOfNat (b k r d : ℕ) :
    Function.Bijective (fun z : Fin (2 ^ (k * (3 * b - 1) + r * d)) =>
      nisanShiftSeedOfNat b k r d z) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨?_, by rw [Fintype.card_fin, card_nisanShiftSeed]⟩
  intro z z' h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  let H := k * (3 * b - 1)
  by_cases hi : i < H
  · have hh := testBit_eq_of_hashSeeds_eq (n := b) (k := k) (o := 0) hi
        (z := z.val) (z' := z'.val) fun l => by
          simpa only [nisanShiftSeedOfNat, Nat.zero_add] using congrFun (congrArg Prod.fst h) l
    simpa only [Nat.zero_add] using hh
  by_cases hlen : i < H + r * d
  · have hd : 0 < d := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at hlen; omega
    have hround : (i - H) / d < r := (Nat.div_lt_iff_lt_mul hd).mpr (by omega)
    have he := congrArg Fin.val (congrFun (congrArg Prod.snd h) ⟨_, hround⟩)
    have hb := congrArg (fun v : ℕ => v.testBit ((i - H) % d)) he
    have hidx : H + (i - H) / d * d + (i - H) % d = i := by
      have := Nat.div_add_mod (i - H) d
      rw [Nat.mul_comm] at this
      omega
    change k * (3 * b - 1) + (i - H) / d * d + (i - H) % d = i at hidx
    simpa only [nisanShiftSeedOfNat, nisanRoundingShift, Nat.testBit_mod_two_pow,
      decide_eq_true (Nat.mod_lt _ hd), Bool.true_and, Nat.testBit_shiftRight, hidx] using hb
  · have hp : 2 ^ (H + r * d) ≤ 2 ^ i := Nat.pow_le_pow_right two_pos (by omega)
    rw [Nat.testBit_lt_two_pow (z.isLt.trans_le hp), Nat.testBit_lt_two_pow (z'.isLt.trans_le hp)]

/-- An accepting-seed count, and hence either majority test, is unchanged by iterating the
binary counter instead of enumerating all tuples of hashes and shifts. -/
theorem countP_range_nisanShiftSeedOfNat (b k r d : ℕ) (p : NisanShiftSeed b k r d → Bool) :
    ((List.range (2 ^ (k * (3 * b - 1) + r * d))).countP
      fun z => p (nisanShiftSeedOfNat b k r d z)) = #{s | p s = true} := by
  rw [List.countP_range_eq_card_filter]
  exact card_equiv (Equiv.ofBijective _ (bijective_nisanShiftSeedOfNat b k r d)) fun _ => by
    simp [Equiv.ofBijective_apply]

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace

/-- Extract a full rounding shift within the work-space budget for computing the seed and the
binary layout parameters. -/
theorem budget_nisanRoundingShift {α : Type} {enc : α ↪ List Bool} {B b k d z i : α → ℕ}
    (hb : ComputableInSpace b enc encNat B) (hk : ComputableInSpace k enc encNat B)
    (hd : ComputableInSpace d enc encNat B) (hz : ComputableInSpace z enc encNat B)
    (hi : ComputableInSpace i enc encNat B) :
    ComputableInSpace (fun x => nisanRoundingShift (b x) (k x) (d x) (z x) (i x)) enc encNat B :=
  budget_natModTwoPow (budget_comp_linear natShiftRight (budget_prod hz (budget_natAdd
    (budget_natMul hk (budget_natSub (budget_natMul (budget_const 3) hb) (budget_const 1)))
    (budget_natMul hi hd)))) hd

/-- Computing a numeric walk letter uses the budget of the binary arguments and enough room
for one `b`-bit initial block when adjoining it to the shared seed. -/
theorem budget_nisanBlockValue {α : Type} {enc : α ↪ List Bool} {B b k z x t : α → ℕ}
    (hb : ComputableInSpace b enc encNat B) (hk : ComputableInSpace k enc encNat B)
    (hz : ComputableInSpace z enc encNat B) (hx : ComputableInSpace x enc encNat B)
    (ht : ComputableInSpace t enc encNat B) (hwidth : b ≼ B) :
    ComputableInSpace (fun a => nisanBlockValue (b a) (k a) (z a) (x a) (t a)) enc encNat B := by
  have hp := budget_twoPow hb hwidth
  exact budget_natModTwoPow (budget_blockNat hb hk (budget_natAdd (budget_natMul hz hp) hx) ht) hb

end Cslib.Probability.SaksZhou
