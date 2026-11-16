/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MAC.PolynomialEvaluation
public import CslibFrontier.Foundations.Data.BitString.PadBlocks
public import Mathlib.Algebra.Ring.BooleanRing
import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Foundations.Data.BitString.List.LowBits
import CslibFrontier.Probability.HashFamily.Transport

/-!
# GHASH, the keyed hash of GCM

[BonehShoup2023], Section 9.7, defines GHASH by (9.18): for a key `k` and blocks
`z = (z[0], …, z[v - 1])` of the field `GF(2^128)`,
`GHASH(k, z) := z[0] · k ^ v + z[1] · k ^ (v - 1) + ⋯ + z[v - 1] · k`. Here `ghash k z` is this
evaluation over any field, and `ghashBits e` is the same function on `w`-bit blocks for a field
with an additive bit encoding `e : F ≃+ BitString w`. GCM hashes, on line (∗) of Section 9.7, the
associated data `d` and the ciphertext `c`, each padded with zeros to whole 128-bit blocks, followed
by one block holding their two lengths: `gcmHashInput d c`.

The book requires GHASH to be a DUF, and says that the length block maintains "the XOR-DUF
property". An `ε`-XOR-DUF ([BonehShoup2023], Remark 7.3) is an `ε`-DUF whose digests are bit
strings, with XOR as the difference operator. Here it is `Cslib.Probability.IsDeltaUniversalHash`
with digests in `BitString n`, where subtraction is XOR; there is no separate predicate.

Differences from the book:

* **Domain.** The book defines GHASH over `(𝒳, 𝒳^{≤ℓ}, 𝒳)`. On that domain (9.18) is not even
  universal: a leading zero block does not change the hash (`ghash_cons_zero`), so `[]` and `[0]`
  collide under every key (`not_isUniversalHash_ghash`). The XOR-DUF property is proved for every
  family whose last block determines the number of blocks (`isDeltaUniversalHash_ghash`), which
  GCM's length block provides.
* **Bound.** The book gives no `ε` for GHASH; Remark 7.4 gives `(ℓ + 1) / 2 ^ n` for `H_xpoly`,
  which has the extra leading term `k ^ (v + 1)`. Here `ε = ℓ / 2 ^ 128`, with `ℓ` bounding the
  number of blocks hashed, the length block included.
* **Field.** GHASH on 128-bit strings is `ghashBits e` for the field with modulus
  `X^128 + X^7 + X^2 + X + 1` and the standard's bit encoding `e`. Neither is constructed here,
  so the theorems are stated for every field with an additive bit encoding.
* **Length fields.** The book's length fields count bytes. Here they count bits: padding gives the
  bit strings `[false]` and `[false, false]` the same block. The book fixes no bit order; here the
  first 64 bits hold the length of `d` and the last 64 that of `c`, each most significant bit
  first, and bit `j` of block `i` is bit `128 i + j` of the padded field. Each length must be below
  `2 ^ 64` bits, which the book's bound `ℓ = 2 ^ 32 - 1` on the number of blocks implies.
* **Key.** The key is uniform; in GCM it is `E(k, 0^128)` for a block cipher `E`.

## Main definitions

* `Cslib.Crypto.ghash`: (9.18) over a field.
* `Cslib.Crypto.ghashBits`: (9.18) on `w`-bit blocks through an additive bit encoding.
* `Cslib.Crypto.gcmHashInput`: the input of line (∗): both fields padded with zeros, then the
  block `gcmLengthBlock` of their bit lengths.

## Main results

* `Cslib.Crypto.ghash_eq_sum`: (9.18) as printed.
* `Cslib.Crypto.isDeltaUniversalHash_ghash`: GHASH is `ℓ / |F|`-difference universal on every
  injective family of inputs of at most `ℓ` blocks whose last block determines the number of
  blocks; `Cslib.Crypto.isDeltaUniversalHash_ghashBits` is the `ℓ / 2 ^ w`-XOR-DUF on bit strings.
* `Cslib.Crypto.not_isUniversalHash_ghash`: without such a condition GHASH is not universal.
* `Cslib.Crypto.isDeltaUniversalHash_ghashBits_gcmHashInput`: GHASH on the input of line (∗) is
  an `ℓ / 2 ^ 128`-XOR-DUF when both fields are shorter than `2 ^ 64` bits.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, v0.6][BonehShoup2023],
  Section 9.7, printed pp. 381–382; Remarks 7.3 and 7.4, printed p. 269.
-/

public section

namespace Cslib.Crypto

open Cslib.Probability PolynomialEvaluation
open scoped ENNReal

variable {F : Type*} [Field F] {ℓ : ℕ}

/-! ### GHASH over a field -/

/-- GHASH, [BonehShoup2023], (9.18): `ghash k z = z[0] k ^ v + z[1] k ^ (v - 1) + ⋯ + z[v - 1] k`
for `v` blocks. -/
def ghash (k : F) (z : List F) : F := ascendingEval k z.reverse

@[simp] theorem ghash_nil (k : F) : ghash k [] = 0 := by
  rw [ghash, List.reverse_nil, ascendingEval]

/-- One more block is the Horner step `(GHASH(k, z) + a) · k`. -/
theorem ghash_concat (k : F) (z : List F) (a : F) :
    ghash k (z ++ [a]) = (ghash k z + a) * k := by
  simp only [ghash, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, ascendingEval]
  ring

/-- A new first block is multiplied by the highest power of the key. -/
theorem ghash_cons (k a : F) (z : List F) :
    ghash k (a :: z) = a * k ^ (z.length + 1) + ghash k z := by
  rw [ghash, List.reverse_cons, ascendingEval_concat, List.length_reverse, ghash]
  ring

/-- [BonehShoup2023], (9.18) as printed: block `i` of `v` is multiplied by `k ^ (v - i)`. -/
theorem ghash_eq_sum (k : F) (z : List F) :
    ghash k z = ∑ i : Fin z.length, z[i] * k ^ (z.length - i) := by
  induction z with
  | nil => simp
  | cons a z ih =>
    rw [ghash_cons, ih]
    change _ = ∑ i : Fin (z.length + 1), (a :: z)[i] * k ^ (z.length + 1 - i)
    rw [Fin.sum_univ_succ]
    simp

/-- A leading zero block does not change the hash, so (9.18) on its own does not separate inputs
of different lengths. -/
theorem ghash_cons_zero (k : F) (z : List F) : ghash k (0 :: z) = ghash k z := by
  rw [ghash_cons, zero_mul, zero_add]

/-- The hash of [KatzLindell2020], Theorem 4.17 is GHASH of the message followed by its length
code. -/
theorem PolynomialEvaluation.hash_eq_ghash (encodeLength : Fin ℓ → F) (k : F) (m : Message F ℓ) :
    hash encodeLength k m = ghash k (coefficients encodeLength m) := by
  rw [PolynomialEvaluation.hash, ghash]

/-- **GHASH is `ℓ / |F|`-difference universal** on every injective family of inputs of at most `ℓ`
blocks in which inputs with the same last block have the same number of blocks; the empty input
counts as ending in the block `0`. -/
theorem isDeltaUniversalHash_ghash [Fintype F] {X : Type*} (enc : X → List F)
    (hinj : Function.Injective enc)
    (hlast : ∀ x x', (enc x).getLastD 0 = (enc x').getLastD 0 →
      (enc x).length = (enc x').length)
    (hlen : ∀ x, (enc x).length ≤ ℓ) :
    IsDeltaUniversalHash (PMF.uniformOfFintype F) (fun k x => ghash k (enc x))
      (ℓ / Fintype.card F) :=
  isDeltaUniversalHash_ascendingEval (fun x => (enc x).reverse)
    (fun _ _ h => hinj (List.reverse_injective h))
    (fun x x' h => by
      simpa only [List.length_reverse] using hlast x x' (by simpa using h))
    (fun x => by simpa only [List.length_reverse] using hlen x)

/-- **GHASH on all inputs of at most `ℓ ≥ 1` blocks is not universal** for any `ε < 1`: `[]` and
`[0]` collide under every key. -/
theorem not_isUniversalHash_ghash [Fintype F] (hℓ : 1 ≤ ℓ) {ε : ℝ≥0∞} (hε : ε < 1) :
    ¬ IsUniversalHash (PMF.uniformOfFintype F)
      (fun k (z : {z : List F // z.length ≤ ℓ}) => ghash k z) ε := fun hh => by
  have h := hh ⟨[], Nat.zero_le _⟩ ⟨[0], hℓ⟩ (by simp)
  have hset : {k : F | ghash k ([] : List F) = ghash k [0]} = Set.univ :=
    Set.eq_univ_of_forall fun k => by simp [ghash_cons_zero]
  rw [hset, (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _)] at h
  exact absurd (h.trans_lt hε) (lt_irrefl 1)

/-! ### GHASH on bit strings -/

/-- GHASH on `w`-bit blocks: key and blocks are read in the field `F` through the additive bit
encoding `e`, and the digest is written back with `e`. -/
def ghashBits {w : ℕ} (e : F ≃+ BitString w) (k : BitString w) (z : List (BitString w)) :
    BitString w :=
  e (ghash (e.symm k) (z.map e.symm))

/-- `ghashBits e` is `ghash` in the field, read through `e`. -/
theorem ghashBits_def {w : ℕ} (e : F ≃+ BitString w) (k : BitString w)
    (z : List (BitString w)) : ghashBits e k z = e (ghash (e.symm k) (z.map e.symm)) := by
  rw [ghashBits]

/-- **GHASH on bit strings is an `ℓ / 2 ^ w`-XOR-DUF** for a uniform `w`-bit key, on every
injective family of inputs of at most `ℓ` blocks in which inputs with the same last block have the
same number of blocks. -/
theorem isDeltaUniversalHash_ghashBits {w : ℕ} (e : F ≃+ BitString w) {X : Type*}
    (enc : X → List (BitString w)) (hinj : Function.Injective enc)
    (hlast : ∀ x x', (enc x).getLastD 0 = (enc x').getLastD 0 →
      (enc x).length = (enc x').length)
    (hlen : ∀ x, (enc x).length ≤ ℓ) :
    IsDeltaUniversalHash (PMF.uniformOfFintype (BitString w))
      (fun k x => ghashBits e k (enc x)) (ℓ / 2 ^ w) := by
  let : Fintype F := Fintype.ofEquiv (BitString w) e.symm.toEquiv
  have hcard : (Fintype.card F : ℝ≥0∞) = 2 ^ w := by
    rw [Fintype.card_congr e.toEquiv, BitString.card, Nat.cast_pow, Nat.cast_ofNat]
  have h := (isDeltaUniversalHash_ghash (F := F) (ℓ := ℓ) (fun x => (enc x).map e.symm)
    (fun x x' h => hinj (List.map_injective_iff.mpr e.symm.injective h))
    (fun x x' h => by
      simpa only [List.length_map] using hlast x x' (e.symm.injective (by
        rw [← map_zero e.symm, List.getLastD_map, List.getLastD_map] at h
        exact h)))
    (fun x => by simpa only [List.length_map] using hlen x)).postcompose
    e.toAddMonoidHom e.injective
  rw [← PMF.uniformOfFintype_map_equiv e.symm.toEquiv, hcard] at h
  exact IsDeltaUniversalHash.precompose_seed _ _ h

/-! ### The input of line (∗) -/

/-- The bit string `s` padded with zeros to a multiple of 128 bits, as 128-bit blocks. -/
@[expose]
def gcmBlocks (s : List Bool) : List (BitString 128) :=
  BitString.padBlocks 128 ((s.length + 127) / 128 * 128) s

theorem length_gcmBlocks (s : List Bool) : (gcmBlocks s).length = (s.length + 127) / 128 := by
  simp [gcmBlocks]

private theorem gcmBlocks_getElem_apply (s : List Bool) (i : ℕ) (hi : i < (gcmBlocks s).length)
    (j : Fin 128) : (gcmBlocks s)[i] j = s.getD (i * 128 + j) false :=
  BitString.padBlocks_getElem_apply 128 _ s i (by simpa [gcmBlocks] using hi) j

/-- Bit strings of equal length with equal padded blocks are equal. -/
theorem gcmBlocks_inj {s s' : List Bool} (hlen : s.length = s'.length)
    (h : gcmBlocks s = gcmBlocks s') : s = s' := by
  refine List.ext_getElem hlen fun t ht ht' => ?_
  have hi : t / 128 < (gcmBlocks s).length := by rw [length_gcmBlocks]; omega
  have hi' : t / 128 < (gcmBlocks s').length := by rw [length_gcmBlocks]; omega
  have hb : (gcmBlocks s)[t / 128] = (gcmBlocks s')[t / 128] := List.getElem_of_eq h hi
  have hbit := congrFun hb ⟨t % 128, Nat.mod_lt _ (by norm_num)⟩
  rw [gcmBlocks_getElem_apply, gcmBlocks_getElem_apply] at hbit
  have ht128 : t / 128 * 128 + t % 128 = t := Nat.div_add_mod' t 128
  simp only [ht128] at hbit
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht,
    List.getElem?_eq_getElem ht'] using hbit

/-- The block `length(d) ‖ length(c)` of line (∗): the 64-bit numbers `a` and `b`, each most
significant bit first. -/
@[expose]
def gcmLengthBlock (a b : ℕ) : BitString 128 := fun j =>
  if (j : ℕ) < 64 then a.testBit (63 - j) else b.testBit (127 - j)

/-- Lengths below `2 ^ 64` are recovered from the length block. -/
theorem gcmLengthBlock_inj {a b a' b' : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (ha' : a' < 2 ^ 64) (hb' : b' < 2 ^ 64) (h : gcmLengthBlock a b = gcmLengthBlock a' b') :
    a = a' ∧ b = b' := by
  have hfst (x y : ℕ) (i : Fin 64) : gcmLengthBlock x y ⟨63 - i, by omega⟩ = x.testBit i := by
    change (if 63 - (i : ℕ) < 64 then _ else _) = _
    rw [ite_eq_left (by omega), show 63 - (63 - (i : ℕ)) = i by omega]
  have hsnd (x y : ℕ) (i : Fin 64) : gcmLengthBlock x y ⟨127 - i, by omega⟩ = y.testBit i := by
    change (if 127 - (i : ℕ) < 64 then _ else _) = _
    rw [ite_eq_right (by omega), show 127 - (127 - (i : ℕ)) = i by omega]
  refine ⟨BitString.lowBits_injective_of_lt ha ha' ?_,
    BitString.lowBits_injective_of_lt hb hb' ?_⟩ <;>
    rw [BitString.lowBits_eq_ofFn, BitString.lowBits_eq_ofFn] <;>
    refine congrArg List.ofFn (funext fun i => ?_)
  · rw [← hfst a b i, ← hfst a' b' i, h]
  · rw [← hsnd a b i, ← hsnd a' b' i, h]

/-- The input of line (∗), `d' ‖ c' ‖ length(d) ‖ length(c)`: the associated data `d` and the
ciphertext `c` padded with zeros to 128-bit blocks, then their lengths in bits. -/
@[expose]
def gcmHashInput (d c : List Bool) : List (BitString 128) :=
  gcmBlocks d ++ gcmBlocks c ++ [gcmLengthBlock d.length c.length]

theorem length_gcmHashInput (d c : List Bool) :
    (gcmHashInput d c).length = (d.length + 127) / 128 + (c.length + 127) / 128 + 1 := by
  simp only [gcmHashInput, List.length_append, length_gcmBlocks, List.length_singleton]

/-- **GHASH with GCM's padding and length block is an `ℓ / 2 ^ 128`-XOR-DUF.** Let `d x` and `c x`
be the associated data and the ciphertext of the input `x`, which together determine `x`, each
shorter than `2 ^ 64` bits, with at most `ℓ` blocks hashed, the length block included. The field
`F` is any field with an additive encoding `e` as 128-bit strings. -/
theorem isDeltaUniversalHash_ghashBits_gcmHashInput (e : F ≃+ BitString 128) {X : Type*}
    (d c : X → List Bool) (hinj : ∀ x x', d x = d x' → c x = c x' → x = x')
    (hd : ∀ x, (d x).length < 2 ^ 64) (hc : ∀ x, (c x).length < 2 ^ 64)
    (hlen : ∀ x, (gcmHashInput (d x) (c x)).length ≤ ℓ) :
    IsDeltaUniversalHash (PMF.uniformOfFintype (BitString 128))
      (fun k x => ghashBits e k (gcmHashInput (d x) (c x))) (ℓ / 2 ^ 128) := by
  have hlens : ∀ x x',
      (gcmHashInput (d x) (c x)).getLastD 0 = (gcmHashInput (d x') (c x')).getLastD 0 →
      (d x).length = (d x').length ∧ (c x).length = (c x').length := by
    intro x x' h
    simp only [gcmHashInput, List.getLastD_concat] at h
    exact gcmLengthBlock_inj (hd x) (hc x) (hd x') (hc x') h
  refine isDeltaUniversalHash_ghashBits e _ (fun x x' h => ?_) (fun x x' h => ?_) hlen
  · obtain ⟨hdl, hcl⟩ := hlens x x' (congrArg (·.getLastD 0) h)
    simp only [gcmHashInput] at h
    have h1 := List.append_inj_left' h rfl
    have h2 := List.append_inj h1 (by rw [length_gcmBlocks, length_gcmBlocks, hdl])
    exact hinj x x' (gcmBlocks_inj hdl h2.1) (gcmBlocks_inj hcl h2.2)
  · obtain ⟨hdl, hcl⟩ := hlens x x' h
    rw [length_gcmHashInput, length_gcmHashInput, hdl, hcl]

end Cslib.Crypto
