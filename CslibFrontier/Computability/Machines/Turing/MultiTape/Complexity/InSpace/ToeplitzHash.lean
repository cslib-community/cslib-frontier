/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import CslibFrontier.Probability.BitString.ToeplitzHash
public import Cslib.Foundations.Data.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Bit
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.StoredLoop
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import Mathlib.Data.Nat.BinaryRec
import Mathlib.Data.Nat.Bitwise

/-!
# The Toeplitz hash of bits packed in naturals, in linear space

The Toeplitz hash `Cslib.Probability.toeplitzHash` over `Bool` from `n` bits to `n` bits, the map
`x ↦ T x + v` for an `n × n` Toeplitz matrix `T` with diagonals `a` and an offset `v` [Katz and
Lindell, Exercise 4.26][KatzLindell2020], is the hash family of Nisan's generator on bit strings
(`Cslib.Crypto.PRG.Nisan.bitGenerator`) [Nisan1992]. Output bit `i` is
`v i + ∑ j, a (i + (n - 1 - j)) * x j`.

This module reads the seed from the bits of a natural `z` from an offset `o`
(`Cslib.Probability.hashSeedOfNat`) and the hashed block from the low `n` bits of a natural `x`,
and packs the hashed block into a natural (`Cslib.Probability.toeplitzHashNat`), whose bits are the
output bits (`Cslib.Probability.testBit_toeplitzHashNat`). It is computable within work space
linear in the length of the encoded arguments
(`Cslib.Probability.computableInSpace_toeplitzHashNat`): the seed stays on the input tape, and the
work registers hold two counters at most `n`, one bit, and the output bits appended so far.

## Main definitions

* `Cslib.Probability.hashSeedOfNat`: the seed of the Toeplitz hash read from the bits of a natural.
* `Cslib.Probability.toeplitzHashBitNat`: one output bit, by a fold over the columns.
* `Cslib.Probability.toeplitzHashNat`: the hashed block packed into a natural.
* `Cslib.Probability.ToeplitzHashArgs`, `Cslib.Probability.encToeplitzHashArgs`: its arguments and
  their encoding.

## Main results

* `Cslib.Probability.testBit_toeplitzHashNat`: the bits of `toeplitzHashNat` are the output bits of
  the Toeplitz hash.
* `Cslib.Probability.toeplitzHashNat_lt`, `Cslib.Probability.toeplitzHashNat_lt_two_pow_size`: the
  packed hash has at most `n` bits, and no more bits than the seed word.
* `Cslib.Probability.computableInSpace_toeplitzHashNat`: the packed hash in linear space.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, Section 4.6][KatzLindell2020]
* [N. Nisan, *Pseudorandom generators for space-bounded computation*][Nisan1992]
-/

@[expose] public section

namespace Cslib.Probability

open Matrix

/-- The seed of the Toeplitz hash on `n`-bit blocks read from the bits of `z` from offset `o`:
the `2 n - 1` diagonals of the Toeplitz matrix are bits `o, …, o + 2 n - 2` of `z`, and the `n`
bits of the offset vector are the next `n` bits. -/
def hashSeedOfNat (n z o : ℕ) : (Fin (n + n - 1) → Bool) × BitString n :=
  (fun t => z.testBit (o + t), fun i => z.testBit (o + (n + n - 1) + i))

/-- Output bit `i` of the Toeplitz hash with seed `hashSeedOfNat n z o` on the bits of `x`: the
offset bit, then the bits `a (i + (n - 1 - j)) ∧ x j` of the columns `j < n` added by `xor`. -/
def toeplitzHashBitNat (n z o x i : ℕ) : Bool :=
  (List.range n).foldl (fun b j => b ^^ (z.testBit (o + (i + (n - 1 - j))) && x.testBit j))
    (z.testBit (o + (n + n - 1) + i))

/-- The Toeplitz hash with seed `hashSeedOfNat n z o` of the low `n` bits of `x`, packed into a
natural: its bit `i` is output bit `i` (`Cslib.Probability.testBit_toeplitzHashNat`). The bits are
appended most significant first, doubling the accumulator. -/
def toeplitzHashNat (n z o x : ℕ) : ℕ :=
  (List.range n).foldr (fun i acc => 2 * acc + (toeplitzHashBitNat n z o x i).toNat) 0

/-- **The bits of the packed Toeplitz hash bit**: `toeplitzHashBitNat` is output bit `i` of the
Toeplitz hash with seed `hashSeedOfNat n z o` on the low `n` bits of `x`. -/
theorem toeplitzHashBitNat_eq (n z o x : ℕ) (i : Fin n) :
    toeplitzHashBitNat n z o x i =
      toeplitzHash (hashSeedOfNat n z o) (fun j : Fin n => x.testBit j) i := by
  let g : ℕ → Bool := fun j => z.testBit (o + (i + (n - 1 - j))) && x.testBit j
  have hrange : (List.finRange n).map Fin.val = List.range n :=
    List.ext_getElem (by simp) fun _ _ _ => by simp
  have hl (xs : List Bool) (v : Bool) : xs.foldl (· + ·) v = v + xs.sum := by
    simpa [List.sum_eq_foldl, List.foldl_cons] using List.sum_cons (a := v) (l := xs)
  have hfold : (List.range n).foldl (fun b j => b ^^ g j) (z.testBit (o + (n + n - 1) + i)) =
      z.testBit (o + (n + n - 1) + i) + ∑ j : Fin n, g j := by
    simp_rw [← Bool.add_eq_xor, ← hrange, List.foldl_map]
    rw [← List.foldl_map (g := (· + ·)), hl, ← Fin.sum_univ_def]
  simp only [toeplitzHashBitNat, hfold, g, toeplitzHash, hashSeedOfNat, Pi.add_apply, mulVec,
    dotProduct, toeplitz_apply]
  exact add_comm _ _

/-- Bit `k` of a most-significant-first fold of `n` bits. -/
private theorem testBit_foldr_range (g : ℕ → Bool) (n k : ℕ) :
    ((List.range n).foldr (fun i acc => 2 * acc + (g i).toNat) 0).testBit k =
      (decide (k < n) && g k) := by
  induction n generalizing g k with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ_eq_map, List.foldr_cons, List.foldr_map, ← Nat.bit_val]
    cases k <;> simp [Nat.testBit_bit_succ, ih]

/-- **The bits of the packed Toeplitz hash**: bit `i < n` of `toeplitzHashNat n z o x` is output
bit `i` of the Toeplitz hash with seed `hashSeedOfNat n z o` on the low `n` bits of `x`. -/
theorem testBit_toeplitzHashNat (n z o x : ℕ) (i : Fin n) :
    (toeplitzHashNat n z o x).testBit i =
      toeplitzHash (hashSeedOfNat n z o) (fun j : Fin n => x.testBit j) i := by
  simp [toeplitzHashNat, testBit_foldr_range, ← toeplitzHashBitNat_eq, i.isLt]

/-- The packed Toeplitz hash has no bits from position `n` on. -/
theorem toeplitzHashNat_lt (n z o x : ℕ) : toeplitzHashNat n z o x < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun k hk => by
    simp [toeplitzHashNat, testBit_foldr_range, Nat.not_lt.mpr hk]

/-- The packed Toeplitz hash has no bits past those of the seed word: row `i` of the Toeplitz
matrix and bit `i` of the offset are bits of `z` at positions at least `i`. -/
theorem toeplitzHashNat_lt_two_pow_size (n z o x : ℕ) : toeplitzHashNat n z o x < 2 ^ z.size :=
  Nat.lt_pow_two_of_testBit _ fun k hk => by
    have hz (t : ℕ) (ht : k ≤ t) : z.testBit t = false :=
      Nat.testBit_eq_false_of_lt ((Nat.lt_size_self z).trans_le
        (Nat.pow_le_pow_right two_pos (hk.trans ht)))
    have hconst (xs : List ℕ) : xs.foldl (fun b _ => b) false = false := by
      induction xs <;> simp [*]
    rw [toeplitzHashNat, testBit_foldr_range, show toeplitzHashBitNat n z o x k = false by
      simp only [toeplitzHashBitNat, hz _ (by omega : k ≤ o + (n + n - 1) + k),
        fun t => hz (o + (k + t)) (by omega), Bool.false_and, Bool.xor_false]
      exact hconst _, Bool.and_false]

/-! ### The packed Toeplitz hash in linear space -/

open Turing Turing.MultiTapeTM

/-- The arguments of the packed Toeplitz hash `Cslib.Probability.toeplitzHashNat`. -/
structure ToeplitzHashArgs where
  /-- The block length. -/
  n : ℕ
  /-- The natural whose bits hold the seed. -/
  z : ℕ
  /-- The position in `z` of the first seed bit. -/
  o : ℕ
  /-- The natural whose low `n` bits are hashed. -/
  x : ℕ

/-- The arguments of the packed Toeplitz hash as the tuple of their fields, binary naturals in
order: the block length, the seed word, the seed offset and the hashed word. -/
enc_structure encToeplitzHashArgs : ToeplitzHashArgs where
  n : encNat, z : encNat, o : encNat, x : encNat

/-- A query for one output bit of the Toeplitz hash: the arguments and the row. -/
private structure BitQuery where
  args : ToeplitzHashArgs
  i : ℕ

private enc_structure encBitQuery : BitQuery where args : encToeplitzHashArgs, i : encNat

/-- The registers of the column loop of one output bit: the next column and the partial bit. -/
private structure BitReg where
  j : ℕ
  b : Bool

private enc_structure encBitReg : BitReg where j : encNat, b : encBool

/-- The term of column `j` in row `q.i`. -/
private def BitQuery.term (q : BitQuery) (j : ℕ) : Bool :=
  q.args.z.testBit (q.args.o + (q.i + (q.args.n - 1 - j))) && q.args.x.testBit j

/-- The partial output bit of row `q.i` after the columns below `j`. -/
private def BitQuery.partialBit (q : BitQuery) (j : ℕ) : Bool :=
  (List.range j).foldl (fun b k => b ^^ q.term k)
    (q.args.z.testBit (q.args.o + (q.args.n + q.args.n - 1) + q.i))

/-- A round of the column loop: add the term of the next column, or stop after the last. -/
private def bitStep (r : BitReg) (q : BitQuery) : Option BitReg :=
  if r.j < q.args.n then some ⟨r.j + 1, r.b ^^ q.term r.j⟩ else none

private theorem bitStep_inSpace :
    ComputableInSpace (fun p : BitReg × BitQuery => bitStep p.1 p.2)
      (encPair encBitReg encBitQuery) (encOption encBitReg)
      fun p => (encPair encBitReg encBitQuery p).length := by
  have hr := ComputableInSpace.fst encBitReg encBitQuery
  have hq := ComputableInSpace.snd encBitReg encBitQuery
  have hj := encBitReg_j_budget hr
  have ha := encBitQuery_args_budget hq
  have hn := encToeplitzHashArgs_n_budget ha
  have hzb := ComputableInSpace.budget_comp_lin ComputableInSpace.natTestBit
    (ComputableInSpace.linear_mul 32)
    (ComputableInSpace.budget_prod (encToeplitzHashArgs_z_budget ha)
      (ComputableInSpace.budget_natAdd (encToeplitzHashArgs_o_budget ha)
        (ComputableInSpace.budget_natAdd (encBitQuery_i_budget hq)
          (ComputableInSpace.budget_natSub (ComputableInSpace.budget_natPred hn) hj))))
  have hxb := ComputableInSpace.budget_comp_lin ComputableInSpace.natTestBit
    (ComputableInSpace.linear_mul 32)
    (ComputableInSpace.budget_prod (encToeplitzHashArgs_x_budget ha) hj)
  have hnew := ComputableInSpace.budget_finite (encC := encBool)
    (fun t : Bool × Bool × Bool => t.1 ^^ (t.2.1 && t.2.2))
    (ComputableInSpace.budget_prod (encBitReg_b_budget hr) (ComputableInSpace.budget_prod hzb hxb))
  exact (ComputableInSpace.budget_ite (ComputableInSpace.budget_natLt hj hn)
    (ComputableInSpace.budget_optionSome
      (encBitReg_mk_budget (ComputableInSpace.budget_natSucc hj) hnew))
    (ComputableInSpace.budget_const none)).of_enc_eq fun _ => by
      simp only [bitStep, BitQuery.term, decide_eq_true_eq]

/-- One output bit by the column loop, in space linear in the query. -/
private theorem partialBit_inSpace :
    ComputableInSpace (fun q : BitQuery => q.partialBit q.args.n) encBitQuery encBool
      fun q => (encBitQuery q).length := by
  have hq := ComputableInSpace.budget_id (BigOLe.refl fun q => (encBitQuery q).length)
  have ha := encBitQuery_args_budget hq
  have hn := encToeplitzHashArgs_n_budget ha
  have hinit := encBitReg_mk_budget (ComputableInSpace.budget_const (encB := encNat) 0)
    (ComputableInSpace.budget_comp_lin ComputableInSpace.natTestBit
      (ComputableInSpace.linear_mul 32)
      (ComputableInSpace.budget_prod (encToeplitzHashArgs_z_budget ha)
        (ComputableInSpace.budget_natAdd
          (ComputableInSpace.budget_natAdd (encToeplitzHashArgs_o_budget ha)
            (ComputableInSpace.budget_natPred (ComputableInSpace.budget_natAdd hn hn)))
          (encBitQuery_i_budget hq))))
  refine (encBitReg_b_budget (ComputableInSpace.loopWith (encA := encBitQuery) (encR := encBitReg)
    (step := fun p => bitStep p.1 p.2) (B := fun q => 8 * (encBitQuery q).length + 16)
    (fun q j => ⟨j, q.partialBit j⟩) (fun q => q.args.n) hinit bitStep_inSpace
    (fun _ => rfl) (fun q j hj => ?_) (fun q => ?_) (fun q j hj => ?_))).weaken
    (.of_le_linear 10 16 fun q => by have := Nat.log2_le_self (encBitQuery q).length; omega)
  · simp [bitStep, hj, BitQuery.partialBit, List.range_succ]
  · simp [bitStep]
  · have := Turing.MultiTapeTM.length_encNat_mono hj
    have := encToeplitzHashArgs_n_length_le q.args
    have := encBitQuery_args_length_le q
    simp only [length_encPair, encBitReg_apply, encBitRegFields, encBool_apply,
      List.length_singleton]
    omega

/-- The registers of the row loop: the number of rows still to append and the rows appended. -/
private structure HashReg where
  i : ℕ
  acc : ℕ

private enc_structure encHashReg : HashReg where i : encNat, acc : encNat

/-- A round of the row loop: append the next row, most significant first, or stop. -/
private def hashStep (r : HashReg) (a : ToeplitzHashArgs) : Option HashReg :=
  if 0 < r.i then
    some ⟨r.i - 1, 2 * r.acc + (toeplitzHashBitNat a.n a.z a.o a.x (r.i - 1)).toNat⟩
  else none

private theorem hashStep_inSpace :
    ComputableInSpace (fun p : HashReg × ToeplitzHashArgs => hashStep p.1 p.2)
      (encPair encHashReg encToeplitzHashArgs) (encOption encHashReg)
      fun p => (encPair encHashReg encToeplitzHashArgs p).length := by
  have hr := ComputableInSpace.fst encHashReg encToeplitzHashArgs
  have ha := ComputableInSpace.snd encHashReg encToeplitzHashArgs
  have hi := encHashReg_i_budget hr
  have hbit := ComputableInSpace.budget_comp_linear partialBit_inSpace
    (encBitQuery_mk_budget ha (ComputableInSpace.budget_natPred hi))
  exact (ComputableInSpace.budget_ite
    (ComputableInSpace.budget_natLt (ComputableInSpace.budget_const 0) hi)
    (ComputableInSpace.budget_optionSome (encHashReg_mk_budget
      (ComputableInSpace.budget_natPred hi)
      (ComputableInSpace.budget_natAdd
        (ComputableInSpace.budget_natMul (ComputableInSpace.budget_const 2)
          (encHashReg_acc_budget hr))
        (ComputableInSpace.budget_finite Bool.toNat hbit))))
    (ComputableInSpace.budget_const none)).of_enc_eq fun _ => by
      simp only [hashStep, decide_eq_true_eq]; rfl

/-- **The packed Toeplitz hash in linear space**: `toeplitzHashNat n z o x` is computable within
work space linear in the length of the encoded arguments. A loop appends the `n` output bits
most significant first; each bit is computed by an inner loop over the `n` columns, reading the
seed bits of `z` and the bits of `x` from the input. The registers hold two counters at most `n`,
one bit, and the bits appended so far, which are a prefix of the result and so no longer than
`z`. -/
theorem computableInSpace_toeplitzHashNat :
    ComputableInSpace (fun q : ToeplitzHashArgs => toeplitzHashNat q.n q.z q.o q.x)
      encToeplitzHashArgs encNat fun q => (encToeplitzHashArgs q).length := by
  have hq := ComputableInSpace.budget_id (BigOLe.refl fun q => (encToeplitzHashArgs q).length)
  have hinit := encHashReg_mk_budget (encToeplitzHashArgs_n_budget hq)
    (ComputableInSpace.budget_const (encB := encNat) 0)
  refine ((encHashReg_acc_budget (ComputableInSpace.loopWith (encA := encToeplitzHashArgs)
    (encR := encHashReg) (step := fun p => hashStep p.1 p.2)
    (B := fun q => 8 * (encToeplitzHashArgs q).length + 16)
    (fun q j => ⟨q.n - j, toeplitzHashNat q.n q.z q.o q.x / 2 ^ (q.n - j)⟩) (fun q => q.n)
    hinit hashStep_inSpace (fun q => ?_) (fun q j hj => ?_) (fun q => ?_)
    (fun q j _ => ?_))).weaken (.of_le_linear 10 16 fun q => by
      have := Nat.log2_le_self (encToeplitzHashArgs q).length; omega)).of_enc_eq
    fun _ => by simp
  · simp [Nat.div_eq_of_lt (toeplitzHashNat_lt _ _ _ _)]
  · simp only [hashStep, show 0 < q.n - j by omega, ↓reduceIte, Option.some.injEq,
      HashReg.mk.injEq]
    refine ⟨by omega, ?_⟩
    set k := q.n - j - 1
    have htb : (toeplitzHashNat q.n q.z q.o q.x).testBit k =
        toeplitzHashBitNat q.n q.z q.o q.x k := by
      simp [toeplitzHashNat, testBit_foldr_range, show k < q.n by omega]
    rw [← htb, Nat.testBit_eq_decide_div_mod_eq, show q.n - (j + 1) = k by omega,
      show q.n - j = k + 1 by omega, pow_succ, ← Nat.div_div_eq_div_mul]
    generalize toeplitzHashNat q.n q.z q.o q.x / 2 ^ k = m
    rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h] <;> omega
  · simp [hashStep]
  · have := Turing.MultiTapeTM.length_encNat_mono (Nat.sub_le q.n j)
    have : (encNat (toeplitzHashNat q.n q.z q.o q.x / 2 ^ (q.n - j))).length ≤
        (encNat q.z).length :=
      (Turing.MultiTapeTM.length_encNat_mono (Nat.div_le_self _ _)).trans
        ((length_encNat_le_of_lt_two_pow (toeplitzHashNat_lt_two_pow_size q.n q.z q.o q.x)).trans_eq
          (Turing.MultiTapeTM.length_encNat_eq_size q.z).symm)
    have := encToeplitzHashArgs_n_length_le q
    have := encToeplitzHashArgs_z_length_le q
    simp only [length_encPair, encHashReg_apply, encHashRegFields]
    omega

end Cslib.Probability
