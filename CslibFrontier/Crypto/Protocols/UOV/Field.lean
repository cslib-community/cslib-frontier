/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryField
import CslibFrontier.Foundations.Data.BitString.Binary
import CslibFrontier.Foundations.FieldTheory.Finite.BinaryPolynomial

/-!
# UOV concrete binary fields and element encodings

UOV v3.0 uses
`F16 = F2[X] / (X ^ 4 + X + 1)` and
`F256 = F2[X] / (X ^ 8 + X ^ 4 + X ^ 3 + X + 1)`.  These are exactly the existing
`Cslib.BinaryField 4` and `Cslib.BinaryField 8`: their least-code irreducible moduli have binary
codes `19 = 0b10011` and `283 = 0b100011011`, respectively.

The source stores a field element as the coefficients of its polynomial-basis representative.
Thus bit zero is the constant coefficient and the most significant bit of a nibble or byte is the
coefficient of `X ^ 3` or `X ^ 7`.  The equivalences below are the existing power-basis
`Cslib.BinaryField.equivBits` followed by the little-endian numbering
`Cslib.BitString.equivFin`.  For `F16`, two elements are packed into one byte with the first
element in the least-significant nibble [UOV2026, Section 3.3, p. 19].

This module identifies only the concrete fields and individual-element/pair encodings.  It does
not define UOV keys, matrices, vector serialization, signing, retry behavior, assumptions, or
security games.

## Main definitions

* `Cslib.Crypto.UOV.F16`, `Cslib.Crypto.UOV.F256`: the two UOV implementation fields.
* `Cslib.Crypto.UOV.f16EquivNibble`: polynomial-basis encoding of `F16` by a nibble.
* `Cslib.Crypto.UOV.f256EquivByte`: polynomial-basis encoding of `F256` by a byte.
* `Cslib.Crypto.UOV.f16PairEquivByte`: low-nibble-first packing of two `F16` elements.

## Main results

* `Cslib.Crypto.UOV.f16_modulus`, `Cslib.Crypto.UOV.f256_modulus`: the existing binary fields use
  the exact UOV irreducible polynomials.
* `Cslib.Crypto.UOV.val_f16EquivNibble_mk_polyOfCode`,
  `Cslib.Crypto.UOV.val_f256EquivByte_mk_polyOfCode`: bounded polynomial codes round-trip through
  the source encodings.
* `Cslib.Crypto.UOV.val_f16PairEquivByte`: the first element occupies the low nibble.
* `Cslib.Crypto.UOV.val_f16EquivNibble_root_pow_four`,
  `Cslib.Crypto.UOV.val_f256EquivByte_root_pow_eight`: convention-sensitive evaluations of the
  two quotient relations.

## References

* [W. Beullens et al., *UOV: Unbalanced Oil and Vinegar, Algorithm Specifications and Supporting
  Documentation*, v3.0, Section 3.3, p. 19][UOV2026]
-/

public section

namespace Cslib.Crypto.UOV

open BitString Polynomial

/-- UOV's `F16`, using the library's explicit degree-four binary field. -/
abbrev F16 := BinaryField 4

/-- UOV's `F256`, using the library's explicit degree-eight binary field. -/
abbrev F256 := BinaryField 8

private theorem polyOfCode_step {n k : ℕ} (h : n = 2 * k) : polyOfCode n = X * polyOfCode k :=
  h ▸ polyOfCode_two_mul k

private theorem polyOfCode_step_odd {n k : ℕ} (h : n = 2 * k + 1) :
    polyOfCode n = 1 + X * polyOfCode k :=
  h ▸ polyOfCode_two_mul_add_one k

private theorem polyOfCode_nineteen : polyOfCode 19 = X ^ 4 + X + 1 := by
  rw [polyOfCode_step_odd (k := 9) rfl, polyOfCode_step_odd (k := 4) rfl,
    polyOfCode_step (k := 2) rfl, polyOfCode_two]
  ring

private theorem polyOfCode_two_hundred_eighty_three :
    polyOfCode 283 = X ^ 8 + X ^ 4 + X ^ 3 + X + 1 := by
  rw [polyOfCode_step_odd (k := 141) rfl, polyOfCode_step_odd (k := 70) rfl,
    polyOfCode_step (k := 35) rfl, polyOfCode_step_odd (k := 17) rfl,
    polyOfCode_step_odd (k := 8) rfl, polyOfCode_step (k := 4) rfl,
    polyOfCode_step (k := 2) rfl, polyOfCode_two]
  ring

private theorem polyOfCode_twenty_seven : polyOfCode 0x1b = X ^ 4 + X ^ 3 + X + 1 := by
  rw [polyOfCode_step_odd (k := 13) rfl, polyOfCode_step_odd (k := 6) rfl,
    polyOfCode_step (k := 3) rfl, polyOfCode_three]
  ring

/-- The least-code degree-four irreducible binary polynomial has code `19 = 0b10011`. -/
theorem f16_modulus_code : leastIrreducible 4 = polyOfCode 19 := by
  rw [← polyOfCode_leastIrreducibleCode (B := 32) (by norm_num) (by norm_num),
    show leastIrreducibleCode 32 4 = 19 by decide]

/-- `BinaryField 4` uses UOV's modulus `X ^ 4 + X + 1`. -/
theorem f16_modulus : leastIrreducible 4 = X ^ 4 + X + 1 := by
  rw [f16_modulus_code, polyOfCode_nineteen]

private def codeRange (start count : ℕ) : List ℕ :=
  (List.range count).map (start + ·)

private theorem codeRange_add (start first second : ℕ) :
    codeRange start (first + second) =
      codeRange start first ++ codeRange (start + first) second := by
  simp only [codeRange, List.range_add, List.map_append, List.map_map, Function.comp_def,
    Nat.add_assoc]

private theorem find?_codeRange_split_none {p : ℕ → Bool} {res : Option ℕ}
    (start first second : ℕ)
    (hfirst : (codeRange start first).find? p = none)
    (hrest : (codeRange (start + first) second).find? p = res) :
    (codeRange start (first + second)).find? p = res := by
  rw [codeRange_add, List.find?_append, hfirst, Option.none_or, hrest]

private theorem leastIrreducibleCode_eight : leastIrreducibleCode 512 8 = 283 := by
  let pred : ℕ → Bool := fun m => Nat.log 2 m == 8 && isIrreducibleCode m
  have hlow : (List.range 256).find? pred = none := by
    rw [List.find?_eq_none]
    intro m hm hpred
    have hm_lt : m < 256 := List.mem_range.mp hm
    have hlog : Nat.log 2 m = 8 := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hpred).1
    rcases eq_or_ne m 0 with rfl | hm0
    · norm_num at hlog
    · exact (Nat.log_lt_of_lt_pow hm0 (by simpa using hm_lt)).ne hlog
  have h283_log : Nat.log 2 283 = 8 := by
    decide
  have h283_irreducible : isIrreducibleCode 283 = true := by
    unfold isIrreducibleCode
    rw [Bool.and_eq_true]
    refine ⟨by decide, ?_⟩
    rw [List.all_eq_true]
    intro d _
    by_cases hd32 : d < 32
    · interval_cases d <;> decide
    · simp only [divisorPasses, Bool.or_eq_true, decide_eq_true_eq]
      left
      right
      rw [h283_log]
      have hlog : 5 ≤ Nat.log 2 d :=
        Nat.le_log_of_pow_le one_lt_two (by norm_num; omega)
      norm_num
      omega
  have h283 : (codeRange 283 1).find? pred = some 283 := by
    simp [pred, codeRange, h283_irreducible, h283_log]
  have hwindow : (codeRange 256 28).find? pred = some 283 :=
    find?_codeRange_split_none 256 4 24 (by decide) <|
    find?_codeRange_split_none 260 4 20 (by decide) <|
    find?_codeRange_split_none 264 4 16 (by decide) <|
    find?_codeRange_split_none 268 4 12 (by decide) <|
    find?_codeRange_split_none 272 4 8 (by decide) <|
    find?_codeRange_split_none 276 4 4 (by decide) <|
    find?_codeRange_split_none 280 1 3 (by decide) <|
    find?_codeRange_split_none 281 1 2 (by decide) <|
    find?_codeRange_split_none 282 1 1 (by decide) h283
  have hhigh : (codeRange 256 256).find? pred = some 283 := by
    rw [codeRange_add 256 28 228, List.find?_append, hwindow, Option.some_or]
  unfold leastIrreducibleCode
  rw [show List.range 512 =
      List.range 256 ++ codeRange 256 256 by
        unfold codeRange
        simpa using (List.range_add (n := 256) (m := 256)),
    List.find?_append, hlow, Option.none_or, hhigh, Option.getD_some]

/-- The least-code degree-eight irreducible binary polynomial has code
`283 = 0b100011011`. -/
theorem f256_modulus_code : leastIrreducible 8 = polyOfCode 283 := by
  rw [← polyOfCode_leastIrreducibleCode (B := 512) (by norm_num) (by norm_num),
    leastIrreducibleCode_eight]

/-- `BinaryField 8` uses UOV's modulus `X ^ 8 + X ^ 4 + X ^ 3 + X + 1`. -/
theorem f256_modulus : leastIrreducible 8 = X ^ 8 + X ^ 4 + X ^ 3 + X + 1 := by
  rw [f256_modulus_code, polyOfCode_two_hundred_eighty_three]

/-- UOV's polynomial-basis encoding of an `F16` element as one nibble.  Coordinate zero is the
constant coefficient. -/
noncomputable def f16EquivNibble : F16 ≃ Fin 16 :=
  BinaryField.equivFin (w := 4) (by norm_num)

/-- UOV's polynomial-basis encoding of an `F256` element as one byte.  Coordinate zero is the
constant coefficient. -/
noncomputable def f256EquivByte : F256 ≃ Fin 256 :=
  BinaryField.equivFin (w := 8) (by norm_num)

/-- A bounded polynomial code is unchanged by UOV's `F16` nibble encoding. -/
theorem val_f16EquivNibble_mk_polyOfCode {c : ℕ} (hc : c < 16) :
    (f16EquivNibble (AdjoinRoot.mk (leastIrreducible 4) (polyOfCode c))).val = c := by
  have hc' : c < 2 ^ 4 := by simpa using hc
  simpa only [f16EquivNibble] using
    BinaryField.val_equivFin_mk_polyOfCode (w := 4) (c := c) (by norm_num) hc'

/-- Decoding a nibble gives the class of the binary polynomial with that code. -/
theorem f16EquivNibble_symm_apply (c : Fin 16) :
    f16EquivNibble.symm c = AdjoinRoot.mk (leastIrreducible 4) (polyOfCode c.val) := by
  simpa only [f16EquivNibble] using
    BinaryField.equivFin_symm_eq_mk_polyOfCode (w := 4) (by norm_num) c

/-- A bounded polynomial code is unchanged by UOV's `F256` byte encoding. -/
theorem val_f256EquivByte_mk_polyOfCode {c : ℕ} (hc : c < 256) :
    (f256EquivByte (AdjoinRoot.mk (leastIrreducible 8) (polyOfCode c))).val = c := by
  have hc' : c < 2 ^ 8 := by simpa using hc
  simpa only [f256EquivByte] using
    BinaryField.val_equivFin_mk_polyOfCode (w := 8) (c := c) (by norm_num) hc'

/-- Decoding a byte gives the class of the binary polynomial with that code. -/
theorem f256EquivByte_symm_apply (c : Fin 256) :
    f256EquivByte.symm c = AdjoinRoot.mk (leastIrreducible 8) (polyOfCode c.val) := by
  simpa only [f256EquivByte] using
    BinaryField.equivFin_symm_eq_mk_polyOfCode (w := 8) (by norm_num) c

/-- Pack two `F16` elements into one byte.  The first element is the low nibble and the second is
the high nibble, as in UOV v3.0, Section 3.3. -/
@[expose] noncomputable def f16PairEquivByte : F16 × F16 ≃ Fin 256 :=
  ((Equiv.prodCongr f16EquivNibble f16EquivNibble).trans (Equiv.prodComm _ _)).trans
    finProdFinEquiv

/-- Low-nibble-first packing has unsigned value `low + 16 * high`. -/
theorem val_f16PairEquivByte (low high : F16) :
    (f16PairEquivByte (low, high)).val =
      (f16EquivNibble low).val + 16 * (f16EquivNibble high).val :=
  rfl

/-- The polynomial-basis generator `X` has nibble value `2`, not the bit-reversed value `4`. -/
theorem val_f16EquivNibble_root :
    (f16EquivNibble (AdjoinRoot.root (leastIrreducible 4))).val = 2 := by
  have h := val_f16EquivNibble_mk_polyOfCode (c := 2) (by norm_num)
  simpa only [polyOfCode_two, AdjoinRoot.mk_X] using h

/-- The multiplicative identity has nibble value `1`. -/
theorem val_f16EquivNibble_one : (f16EquivNibble (1 : F16)).val = 1 := by
  have hmk : AdjoinRoot.mk (leastIrreducible 4) (polyOfCode 1) = (1 : F16) := by
    rw [polyOfCode_one]
    exact map_one _
  rw [← hmk]
  exact val_f16EquivNibble_mk_polyOfCode (c := 1) (by norm_num)

private theorem adjoinRoot_pow_eq_mk {w k : ℕ} {p : Polynomial (ZMod 2)}
    (h : X ^ k + p = leastIrreducible w) :
    AdjoinRoot.root (leastIrreducible w) ^ k = AdjoinRoot.mk (leastIrreducible w) p := by
  change (AdjoinRoot.mk (leastIrreducible w) X) ^ k = _
  rw [← map_pow, ← sub_eq_zero, CharTwo.sub_eq_add, ← map_add, h, AdjoinRoot.mk_self]

/-- In UOV's `F16`, the quotient relation is `X ^ 4 = X + 1`, encoded as `0x3`. -/
theorem val_f16EquivNibble_root_pow_four :
    (f16EquivNibble (AdjoinRoot.root (leastIrreducible 4) ^ 4)).val = 3 := by
  rw [adjoinRoot_pow_eq_mk (p := polyOfCode 3) (by rw [f16_modulus, polyOfCode_three]; ring),
    val_f16EquivNibble_mk_polyOfCode (by norm_num)]

/-- The polynomial-basis generator `X` has byte value `2`, not the bit-reversed value `64`. -/
theorem val_f256EquivByte_root :
    (f256EquivByte (AdjoinRoot.root (leastIrreducible 8))).val = 2 := by
  have h := val_f256EquivByte_mk_polyOfCode (c := 2) (by norm_num)
  simpa only [polyOfCode_two, AdjoinRoot.mk_X] using h

/-- In UOV's `F256`, the quotient relation is
`X ^ 8 = X ^ 4 + X ^ 3 + X + 1`, encoded as `0x1b`. -/
theorem val_f256EquivByte_root_pow_eight :
    (f256EquivByte (AdjoinRoot.root (leastIrreducible 8) ^ 8)).val = 0x1b := by
  rw [adjoinRoot_pow_eq_mk (p := polyOfCode 0x1b)
      (by rw [f256_modulus, polyOfCode_twenty_seven]; ring),
    val_f256EquivByte_mk_polyOfCode (by norm_num)]

end Cslib.Crypto.UOV
