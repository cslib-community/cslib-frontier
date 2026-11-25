/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.ToeplitzHash
public import CslibFrontier.Crypto.Primitives.PRG.Nisan.Bits
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Bit
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# A bit of Nisan's generator on demand

Nisan's generator on bit strings (`Cslib.Crypto.PRG.Nisan.bitGenerator`) [Nisan1992] stretches a
seed of `n + k (3 n - 1)` bits into `2 ^ k` blocks of `n` bits. A space-bounded simulation cannot
store the output; it recomputes each requested bit. This module packs the seed into the bits of a
natural, block bits first and then the `k` Toeplitz seeds of `3 n - 1` bits each
(`Cslib.Crypto.PRG.Nisan.seedOfNat`), and computes bit `j` of the output from the packed seed by
running the `k` levels of the generator on one block register
(`Cslib.Crypto.PRG.Nisan.bitGeneratorNat`), as in [Arora and Barak, Section 16.7][AroraBarak07]
and [Vadhan, Section 8.2.1][Vadhan2012].

Bit `j` lies in block `j / n` at offset `j % n`, and block `b` applies the hash of level `ℓ`
exactly when bit `k - 1 - ℓ` of `b` is set (`Cslib.Crypto.PRG.Nisan.blocks_apply_eq_foldl`). The
registers are the level and the block, and every hash is the packed Toeplitz hash
`Cslib.Probability.toeplitzHashNat` of the seed word, which never has more bits than the seed word.
So the bit is computable within work space linear in its encoded arguments
(`Cslib.Crypto.PRG.Nisan.computableInSpace_bitGeneratorNat`), whatever the number of output bits.

## Main definitions

* `Cslib.Crypto.PRG.Nisan.seedOfNat`: the seed of Nisan's generator held in the bits of a
  natural.
* `Cslib.Crypto.PRG.Nisan.blockNat`: a block of Nisan's generator from a packed seed.
* `Cslib.Crypto.PRG.Nisan.bitGeneratorNat`: a bit of Nisan's generator from a packed seed.
* `Cslib.Crypto.PRG.Nisan.NisanBitArgs`: the arguments of `bitGeneratorNat`, with their encoding
  `Cslib.Crypto.PRG.Nisan.encNisanBitArgs`.

## Main results

* `Cslib.Crypto.PRG.Nisan.countP_range_seedOfNat`: the naturals below `2 ^ (n + k (3 n - 1))`
  enumerate the seeds once each.
* `Cslib.Crypto.PRG.Nisan.bitGeneratorNat_eq`: `bitGeneratorNat` is the bit of Nisan's generator.
* `Cslib.Crypto.PRG.Nisan.computableInSpace_bitGeneratorNat`: a bit of Nisan's generator is
  computable within work space linear in its encoded arguments.

## References

* [N. Nisan, *Pseudorandom generators for space-bounded computation*][Nisan1992]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak07], Section 16.7
* [S. Vadhan, *Pseudorandomness*][Vadhan2012], Section 8.2.1
-/

@[expose] public section

namespace Cslib.Crypto.PRG.Nisan

open Cslib.BitString Cslib.Probability

/-! ### Seeds packed in naturals -/

/-- The seed of Nisan's generator on bit strings held in the bits of `z`: the block is bits
`0, …, n - 1`, and hash seed `ℓ` is the `3 n - 1` bits from position `n + ℓ (3 n - 1)` on
(`Cslib.Probability.hashSeedOfNat`). -/
def seedOfNat (n k z : ℕ) : BitSeed n k :=
  (fun i => z.testBit i, fun ℓ => hashSeedOfNat n z (n + ℓ * (3 * n - 1)))

/-- Distinct naturals below `2 ^ (n + k (3 n - 1))` hold distinct seeds. -/
private theorem seedOfNat_injOn (n k : ℕ) :
    Set.InjOn (seedOfNat n k) (Finset.range (2 ^ (n + k * (3 * n - 1)))) := by
  intro z hz z' hz' heq
  simp only [Finset.coe_range, Set.mem_Iio] at hz hz'
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hi : i < n + k * (3 * n - 1)
  · by_cases hin : i < n
    · exact congrFun (congrArg Prod.fst heq) ⟨i, hin⟩
    · have hpos : 0 < 3 * n - 1 := by
        rcases n with _ | n
        · simp at hi
        · omega
      set m := 3 * n - 1 with hm
      have hℓ : (i - n) / m < k := (Nat.div_lt_iff_lt_mul hpos).mpr (by omega)
      have hdm := Nat.div_add_mod (i - n) m
      have hr := Nat.mod_lt (i - n) hpos
      have hseed := congrFun (congrArg Prod.snd heq) ⟨(i - n) / m, hℓ⟩
      simp only [seedOfNat, hashSeedOfNat, Prod.mk.injEq, ← hm] at hseed
      have hmul := Nat.mul_comm ((i - n) / m) m
      by_cases hr' : (i - n) % m < n + n - 1
      · simpa only [show n + (i - n) / m * m + (i - n) % m = i by omega]
          using congrFun hseed.1 ⟨_, hr'⟩
      · simpa only [show n + (i - n) / m * m + (n + n - 1) + ((i - n) % m - (n + n - 1)) = i by
          omega] using congrFun hseed.2 ⟨(i - n) % m - (n + n - 1), by omega⟩
  · have hle : 2 ^ (n + k * (3 * n - 1)) ≤ 2 ^ i := Nat.pow_le_pow_right two_pos (by omega)
    rw [Nat.testBit_lt_two_pow (hz.trans_le hle), Nat.testBit_lt_two_pow (hz'.trans_le hle)]

/-- **Packed seeds enumerate the seeds**: counting the naturals below `2 ^ (n + k (3 n - 1))` whose
seed satisfies `p` counts the seeds satisfying `p`, as `seedOfNat` is a bijection from these
naturals onto the seeds. -/
theorem countP_range_seedOfNat (n k : ℕ) (p : BitSeed n k → Bool) :
    ((List.range (2 ^ (n + k * (3 * n - 1)))).countP fun z => p (seedOfNat n k z)) =
      (Finset.univ.filter fun s => p s = true).card := by
  have himage : (Finset.range (2 ^ (n + k * (3 * n - 1)))).image (seedOfNat n k) =
      Finset.univ :=
    Finset.eq_univ_of_card _ (by
      rw [Finset.card_image_of_injOn (seedOfNat_injOn n k), Finset.card_range, card_bitSeed])
  rw [← himage, Finset.filter_image, Finset.card_image_of_injOn
    ((seedOfNat_injOn n k).mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))),
    List.countP_eq_length_filter]
  simp [Finset.card, Finset.filter_val, Finset.range_val, Multiset.range]

/-! ### A bit of the generator from a packed seed -/

/-- Block `b` of Nisan's generator on bit strings from the seed `seedOfNat n k z`, as a natural
whose low `n` bits are the block: starting from `z`, whose low `n` bits are the seed block, level
`ℓ` applies the packed Toeplitz hash with seed `ℓ` when bit `k - 1 - ℓ` of `b` is set. -/
def blockNat (n k z b : ℕ) : ℕ :=
  (List.range k).foldl (fun x ℓ =>
    if b.testBit (k - 1 - ℓ) then toeplitzHashNat n z (n + ℓ * (3 * n - 1)) x else x) z

/-- Bit `j` of Nisan's generator on bit strings from the seed `seedOfNat n k z`: bit `j % n` of
block `j / n` (`Cslib.Crypto.PRG.Nisan.bitGeneratorNat_eq`). -/
def bitGeneratorNat (n k z j : ℕ) : Bool := (blockNat n k z (j / n)).testBit (j % n)

/-- The low `n` bits of `blockNat n k z b` are block `b` of the generator. -/
private theorem testBit_blockNat (n k z b : ℕ) (hb : b < 2 ^ k) :
    (fun i : Fin n => (blockNat n k z b).testBit i) =
      blocks toeplitzHash k (seedOfNat n k z).1 (seedOfNat n k z).2 ⟨b, hb⟩ := by
  rw [blocks_apply_eq_foldl, blockNat,
    ← show (List.finRange k).map Fin.val = List.range k from
      List.ext_getElem (by simp) fun _ _ _ => by simp, List.foldl_map]
  refine (List.foldl_hom (fun x : ℕ => fun i : Fin n => x.testBit i) fun x ℓ => ?_).symm
  dsimp only
  split
  · exact funext fun i => by rw [testBit_toeplitzHashNat]; rfl
  · rfl

/-- **`bitGeneratorNat` is a bit of Nisan's generator**: on the seed held in the bits of `z`, it
is bit `j` of `bitGenerator n k`. -/
theorem bitGeneratorNat_eq (n k z j : ℕ) (hj : j < 2 ^ k * n) :
    bitGeneratorNat n k z j = bitGenerator n k (seedOfNat n k z) ⟨j, hj⟩ := by
  have hb : j / n < 2 ^ k := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
  have hn : j % n < n := Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro rfl; simp at hj))
  have hsymm : finProdFinEquiv.symm (⟨j, hj⟩ : Fin (2 ^ k * n)) = (⟨j / n, hb⟩, ⟨j % n, hn⟩) := by
    rw [Equiv.symm_apply_eq, Fin.ext_iff, finProdFinEquiv_apply_val]
    exact (Nat.mod_add_div j n).symm
  rw [bitGenerator_apply, blocksEquiv_symm_apply, hsymm]
  exact congrFun (testBit_blockNat n k z (j / n) hb) ⟨j % n, hn⟩

/-! ### The bit in linear space -/

open Turing Turing.MultiTapeTM ComputableInSpace

/-- The arguments of `Cslib.Crypto.PRG.Nisan.bitGeneratorNat`. -/
structure NisanBitArgs where
  /-- The block length. -/
  n : ℕ
  /-- The number of hash seeds. -/
  k : ℕ
  /-- The natural whose bits hold the seed. -/
  z : ℕ
  /-- The position of the requested output bit. -/
  j : ℕ

/-- The arguments of `bitGeneratorNat` as the tuple of their fields, binary naturals in order: the
block length, the number of hash seeds, the seed word and the bit position. -/
enc_structure encNisanBitArgs : NisanBitArgs where
  n : encNat, k : encNat, z : encNat, j : encNat

/-- The state of the level loop: the arguments of the block, the next level and the block. -/
private structure BlockState where
  n : ℕ
  k : ℕ
  z : ℕ
  b : ℕ
  level : ℕ
  block : ℕ

private instance : Inhabited BlockState := ⟨⟨0, 0, 0, 0, 0, 0⟩⟩

private enc_structure encBlockState : BlockState where
  n : encNat, k : encNat, z : encNat, b : encNat, level : encNat, block : encNat

/-- One level of the generator on the block register. -/
private def blockStep (s : BlockState) : BlockState :=
  ⟨s.n, s.k, s.z, s.b, s.level + 1,
    if s.b.testBit (s.k - 1 - s.level) then
      toeplitzHashNat s.n s.z (s.n + s.level * (3 * s.n - 1)) s.block
    else s.block⟩

private theorem iterate_blockStep (n k z b t : ℕ) :
    blockStep^[t] ⟨n, k, z, b, 0, z⟩ = ⟨n, k, z, b, t, (List.range t).foldl (fun x ℓ =>
      if b.testBit (k - 1 - ℓ) then toeplitzHashNat n z (n + ℓ * (3 * n - 1)) x else x) z⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih, List.range_succ, List.foldl_append]
    rfl

/-- The block register never has more bits than the seed word. -/
private theorem size_foldl_le (n k z b : ℕ) (l : List ℕ) (x : ℕ) (hx : x.size ≤ z.size) :
    (l.foldl (fun x ℓ => if b.testBit (k - 1 - ℓ) then
      toeplitzHashNat n z (n + ℓ * (3 * n - 1)) x else x) x).size ≤ z.size := by
  induction l generalizing x with
  | nil => exact hx
  | cons ℓ l ih =>
    refine ih _ ?_
    dsimp only
    split
    · exact Nat.size_le.mpr (toeplitzHashNat_lt_two_pow_size _ _ _ _)
    · exact hx

private theorem blockStep_inSpace :
    ComputableInSpace blockStep encBlockState encBlockState
      fun s => (encBlockState s).length := by
  have h := budget_id (BigOLe.refl fun s => (encBlockState s).length)
  have hn := encBlockState_n_budget h
  have hk := encBlockState_k_budget h
  have hz := encBlockState_z_budget h
  have hb := encBlockState_b_budget h
  have hl := encBlockState_level_budget h
  have hx := encBlockState_block_budget h
  have hhash := budget_comp_lin computableInSpace_toeplitzHashNat (BigOLe.refl _)
    (encToeplitzHashArgs_mk_budget hn hz
      (budget_natAdd hn (budget_natMul hl
        (budget_natSub (budget_natMul (budget_const 3) hn) (budget_const 1)))) hx)
  have hbit := budget_comp_lin natTestBit (linear_mul 32)
    (budget_prod hb (budget_natSub (budget_natSub hk (budget_const 1)) hl))
  exact encBlockState_mk_budget hn hk hz hb (budget_natSucc hl) (budget_ite hbit hhash hx)

/-- **A bit of Nisan's generator in linear space**: `bitGeneratorNat n k z j` is computable within
work space linear in the encoded arguments. The work space holds the arguments, the level and one
block register of at most as many bits as the seed word, and the space of one packed Toeplitz
hash. -/
theorem computableInSpace_bitGeneratorNat :
    ComputableInSpace (fun q : NisanBitArgs => bitGeneratorNat q.n q.k q.z q.j) encNisanBitArgs
      encBool fun q => (encNisanBitArgs q).length := by
  have h := budget_id (BigOLe.refl fun q => (encNisanBitArgs q).length)
  have hn := encNisanBitArgs_n_budget h
  have hk := encNisanBitArgs_k_budget h
  have hz := encNisanBitArgs_z_budget h
  have hj := encNisanBitArgs_j_budget h
  have hinit := encBlockState_mk_budget hn hk hz (budget_natDiv hj hn) (budget_const 0) hz
  have hloop := budget_iterate hk hinit blockStep_inSpace
    (B := fun q => 4 * ((encNisanBitArgs q).length + 1)) (fun q t ht => by
      rw [iterate_blockStep]
      have h1 := length_encNat_mono ht
      have h2 := length_encNat_mono (Nat.div_le_self q.j q.n)
      have h3 := size_foldl_le q.n q.k q.z (q.j / q.n) (List.range t) q.z le_rfl
      simp only [encBlockState_apply, encBlockStateFields, encNisanBitArgs_apply,
        encNisanBitArgsFields, length_encPair, length_encNat_eq_size] at h1 h2 ⊢
      omega) (linear_mul 4)
  refine (budget_comp_lin natTestBit (linear_mul 32)
    (budget_prod (encBlockState_block_budget hloop) (budget_natMod hj hn))).of_enc_eq fun q => ?_
  rw [iterate_blockStep]; rfl

end Cslib.Crypto.PRG.Nisan
