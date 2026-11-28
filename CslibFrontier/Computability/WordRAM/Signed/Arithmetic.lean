/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Signed.Encoding
public import CslibFrontier.Computability.WordRAM.Notation
public import CslibFrontier.Computability.WordRAM.Compile
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Signed arithmetic implemented by unsigned word-RAM instructions

The input registers hold the encodings of two signed integers. The routines use only ordinary
unsigned arithmetic, comparisons and branches; no signed operation is added to the machine.
The bounds exclude the final halt; `Exec.executes` adds exactly one instruction.
Registers `left` (index 0) and `right` (index 1) are inputs, `result` (index 2) is the output,
and indices 3 through 8 are scratch, including `two` (index 3). Memory and all other registers
are preserved. `Code.rename` can place the routines in a larger register file.

The source semantics are `GenericRAM.Signed.Arithmetic.eval`, covering all five operations:
addition, subtraction, multiplication, Euclidean division and Euclidean remainder, including
Lean's total zero-divisor conventions (`a / 0 = 0` and `a % 0 = a`). The common `w + 2`
allowance covers exact out-of-range sums, differences and minimum/`-1` quotients; it is not a
minimal-width claim for results that fit the source range.

## Main definitions

* `Signed.add`, `Signed.subtract`, `Signed.multiply`, `Signed.divide`, `Signed.modulo`:
  fixed unsigned instruction blocks.
* `Signed.Frame`: preservation of memory, operands and registers outside the workspace.

## Main results

* `Signed.exec_add`, `Signed.exec_subtract`, `Signed.exec_multiply`, `Signed.exec_divide`,
  `Signed.exec_modulo`: charged executions with two extra unsigned bits, independent of the
  operands and source width.

## References

The instruction blocks and their representation are original implementation choices.
-/

@[expose] public section

namespace Cslib.WordRAM.Signed

variable {r : ℕ}

/-- First encoded operand. -/
abbrev left : Fin (r + 9) := ⟨0, by omega⟩
/-- Second encoded operand. -/
abbrev right : Fin (r + 9) := ⟨1, by omega⟩
/-- Encoded result. -/
abbrev result : Fin (r + 9) := ⟨2, by omega⟩
/-- Constant two, used to extract magnitudes and signs. -/
abbrev two : Fin (r + 9) := ⟨3, by omega⟩
/-- Decoded magnitude of the first operand. -/
abbrev magA : Fin (r + 9) := ⟨4, by omega⟩
/-- Decoded magnitude of the second operand. -/
abbrev magB : Fin (r + 9) := ⟨5, by omega⟩
/-- First operand sign, later reused for the result sign. -/
abbrev signA : Fin (r + 9) := ⟨6, by omega⟩
/-- Second operand sign. -/
abbrev signB : Fin (r + 9) := ⟨7, by omega⟩
/-- Constant zero, used to normalize the result. -/
abbrev zero : Fin (r + 9) := ⟨8, by omega⟩

private def signedValue (m s : ℕ) : ℤ := if s = 0 then m else -(m : ℤ)

private def packed (m s : ℕ) : ℕ := 2 * m + if m = 0 then 0 else s

private theorem encode_signedValue {m s : ℕ} (hs : s ≤ 1) :
    encode (signedValue m s) = packed m s := by
  by_cases hz : m = 0
  · simp [signedValue, packed, encode, hz]
  · by_cases hs0 : s = 0
    · simp [signedValue, packed, encode, hs0, hz]
    · simp [signedValue, packed, encode, show s = 1 by omega, hz, show 0 < m by omega]

private theorem signedValue_encode (z : ℤ) :
    signedValue z.natAbs (if z < 0 then 1 else 0) = z := by
  by_cases hz : z < 0
  · simp [signedValue, hz, Int.ofNat_natAbs_of_nonpos (by omega : z ≤ 0)]
  · simp [signedValue, hz, ← Int.eq_natAbs_of_nonneg (by omega : 0 ≤ z)]

/-- Decode the two input words into four scratch registers in six instructions. -/
def unpack : Code .standard (r + 9) := ram[
  two ← #2; zero ← #0;
  magA ← left / two; magB ← right / two;
  signA ← left % two; signB ← right % two ]

/-- Encode a magnitude and sign, setting the sign of zero to zero. -/
def finish : Code .standard (r + 9) := ram[
  if result = zero then [ result ← #0 ]
  else [ result ← result + result; result ← result + signA ] ]

/-- Add equal-sign magnitudes, or subtract the smaller opposite-sign magnitude. -/
def addMagnitudes : Code .standard (r + 9) := ram[
  if signA = signB then [ result ← magA + magB ]
  else [ if magA < magB then [ result ← magB - magA; signA ← signB ]
         else [ result ← magA - magB ] ] ]

/-- Combine decoded operands and encode their sum. -/
def addCore : Code .standard (r + 9) := ram[ ⟪addMagnitudes⟫; ⟪finish⟫ ]

/-- Add two sign-and-magnitude words, normalizing the sign of zero. -/
def add : Code .standard (r + 9) := ram[ ⟪unpack⟫; ⟪addCore⟫ ]

/-- Reverse the right sign bit; the result register temporarily holds the constant one. -/
def flipRightSign : Code .standard (r + 9) := ram[
  result ← #1; signB ← result - signB ]

/-- Subtract by reversing the second operand's sign before the addition block.
The temporary sign of zero is immaterial and the result is normalized. -/
def subtract : Code .standard (r + 9) := ram[
  ⟪unpack⟫; ⟪flipRightSign⟫; ⟪addCore⟫ ]

/-- Multiply the decoded magnitudes and set the product sign. -/
def multiplyMagnitudes : Code .standard (r + 9) := ram[
  result ← magA * magB;
  if signA = signB then [ signA ← #0 ] else [ signA ← #1 ] ]

/-- Multiply the magnitudes and compare the signs, normalizing the sign of zero. -/
def multiply : Code .standard (r + 9) := ram[
  ⟪unpack⟫; ⟪multiplyMagnitudes⟫; ⟪finish⟫ ]

/-- Compute the Euclidean quotient magnitude and sign from decoded operands. -/
def divideMagnitudes : Code .standard (r + 9) := ram[
  if zero < magB then [
    result ← magA / magB;
    magA ← magA % magB;
    if zero < signA then [
      if zero < magA then [ result ← result + signA ] else [ signA ← signA ] ]
    else [ signA ← signA ];
    if signA = signB then [ signA ← #0 ] else [ signA ← #1 ] ]
  else [ result ← #0; signA ← #0 ] ]

/-- Signed Euclidean division on sign-and-magnitude words, matching Lean's `a / 0 = 0`
convention and, for `b ≠ 0`, Lean's Euclidean `Int.ediv`: the quotient for which `a % b` lies in
`[0, |b|)` (rounding toward `-∞` when `b > 0` and toward `+∞` when `b < 0`). -/
def divide : Code .standard (r + 9) := ram[
  ⟪unpack⟫; ⟪divideMagnitudes⟫; ⟪finish⟫ ]

/-- Compute the encoded Euclidean remainder from decoded operands, preserving `a % 0 = a`. -/
def moduloCore : Code .standard (r + 9) := ram[
  if zero < magB then [
    result ← magA % magB;
    if zero < result then [
      if zero < signA then [ result ← magB - result ] else [ result ← result ];
      result ← result + result ]
    else [ result ← #0 ] ]
  else [ result ← left ] ]

/-- Signed Euclidean remainder on sign-and-magnitude words, matching Lean's `a % 0 = a`
convention and returning a nonnegative remainder below `|b|` when `b ≠ 0`. -/
def modulo : Code .standard (r + 9) := ram[
  ⟪unpack⟫; ⟪moduloCore⟫ ]

private theorem exec_unpack {w : ℕ} {a b : ℤ} (ha : GenericRAM.Signed.Fits w a)
    (hb : GenericRAM.Signed.Fits w b) (x : Data (r + 9))
    (hxa : x.regs left = encode a) (hxb : x.regs right = encode b) :
    ∃ y, ExecWithin (w + 2) unpack x y 6 ∧ y.regs two = 2 ∧ y.regs zero = 0 ∧
      y.regs left = encode a ∧ y.regs magA = a.natAbs ∧ y.regs magB = b.natAbs ∧
      y.regs signA = (if a < 0 then 1 else 0) ∧ y.regs signB = (if b < 0 then 1 else 0) ∧
      y.mem = x.mem := by
  have : Fits (w + 2) (if a < 0 then 1 else 0) := by split_ifs <;> fits
  have : Fits (w + 2) (if b < 0 then 1 else 0) := by split_ifs <;> fits
  wram_exec [unpack, hxa, hxb, encode_div_two, encode_mod_two]
  wram_simp [hxa]

private theorem exec_finish {w : ℕ} (x : Data (r + 9)) {m s : ℕ}
    (hm : x.regs result = m) (hs : x.regs signA = s) (hz : x.regs zero = 0)
    (hfit : Fits w (2 * m + s)) :
    ∃ y, ExecWithin w finish x y 4 ∧ y.regs result = packed m s ∧ y.mem = x.mem := by
  wram_exec [finish, hm, hs, hz]
  · wram_simp [packed, hc]
  · wram_simp [packed, hc, two_mul]

private theorem exec_addCore {w : ℕ} (x : Data (r + 9)) {a b sa sb : ℕ}
    (ha : x.regs magA = a) (hb : x.regs magB = b)
    (hsa : x.regs signA = sa) (hsb : x.regs signB = sb) (hz : x.regs zero = 0)
    (hsa1 : sa ≤ 1) (hsb1 : sb ≤ 1) (hf : Fits w (2 * (a + b) + 1)) :
    ∃ y, ExecWithin w addCore x y 9 ∧
      y.regs result = encode (signedValue a sa + signedValue b sb) ∧ y.mem = x.mem := by
  unfold addCore addMagnitudes
  generalize hfin : (finish : Code .standard (r + 9)) = sub
  wram_exec [ha, hb, hsa, hsb]
  · subst hfin
    wram_call (exec_finish _ (by wram_simp; rfl) (by wram_simp [hsa]; rfl) (by wram_simp [hz])
        (by fits)) with y ⟨hyr, hym⟩
    refine ⟨by omega, ?_, hym⟩
    rw [hyr, ← encode_signedValue hsa1]
    congr 1; unfold signedValue; split_ifs <;> omega
  · subst hfin
    wram_call (exec_finish _ (by wram_simp; rfl) (by wram_simp; rfl) (by wram_simp [hz])
        (by fits)) with y ⟨hyr, hym⟩
    refine ⟨by omega, ?_, hym⟩
    rw [hyr, ← encode_signedValue hsb1]
    congr 1; unfold signedValue; split_ifs <;> omega
  · subst hfin
    wram_call (exec_finish _ (by wram_simp; rfl) (by wram_simp [hsa]; rfl) (by wram_simp [hz])
        (by fits)) with y ⟨hyr, hym⟩
    refine ⟨by omega, ?_, hym⟩
    rw [hyr, ← encode_signedValue hsa1]
    congr 1; unfold signedValue; split_ifs <;> omega

/-- Memory and registers outside the output and six scratch registers are unchanged. -/
def Frame (x y : Data (r + 9)) : Prop :=
  y.mem = x.mem ∧ ∀ i, i.val < 2 ∨ 9 ≤ i.val → y.regs i = x.regs i

private theorem preserves {i : Fin (r + 9)} (hi : i.val < 2 ∨ 9 ≤ i.val) :
    (add (r := r)).Preserves i ∧ (subtract (r := r)).Preserves i ∧
      (multiply (r := r)).Preserves i ∧ (divide (r := r)).Preserves i ∧
      (modulo (r := r)).Preserves i := by
  simp only [add, subtract, multiply, divide, modulo,
    multiplyMagnitudes, divideMagnitudes, moduloCore, unpack, flipRightSign,
    addCore, addMagnitudes, finish,
    Code.Preserves, Op.bin, Op.dest, ne_eq, Option.some.injEq,
    result, two, zero, magA, magB, signA, signB, Fin.ext_iff]
  omega

/-- Signed addition runs within fifteen instructions at unsigned width `w + 2`.
The result is exact even when the sum does not fit the source signed range. -/
theorem exec_add {w : ℕ} {a b : ℤ} (ha : GenericRAM.Signed.Fits w a)
    (hb : GenericRAM.Signed.Fits w b) (x : Data (r + 9))
    (hxa : x.regs left = encode a) (hxb : x.regs right = encode b) :
    ∃ y, ExecWithin (w + 2) add x y 15 ∧
      y.regs result = encode (GenericRAM.Signed.Arithmetic.eval .add a b) ∧ Frame x y := by
  have hrun : ∃ y, ExecWithin (w + 2) add x y 15 ∧
      y.regs result = encode (GenericRAM.Signed.Arithmetic.eval .add a b) ∧ y.mem = x.mem := by
    unfold add
    refine (WP.seq ?_).exists_execWithin
    wram_call (exec_unpack ha hb x hxa hxb) with z ⟨_, hz0, _, hma, hmb, hsa, hsb, hzm⟩
    wram_call (exec_addCore z hma hmb hsa hsb hz0 (by split_ifs <;> omega)
        (by split_ifs <;> omega) (by fits)) with y ⟨hyr, hym⟩
    exact ⟨by omega, by simpa only [signedValue_encode, GenericRAM.Signed.Arithmetic.eval]
      using hyr, hym.trans hzm⟩
  obtain ⟨y, he, hyr, hym⟩ := hrun
  exact ⟨y, he, hyr, hym, fun i hi => he.regs_eq (preserves hi).1⟩

/-- Signed subtraction runs within seventeen instructions at unsigned width `w + 2`.
The result is exact even when the difference does not fit the source signed range. -/
theorem exec_subtract {w : ℕ} {a b : ℤ} (ha : GenericRAM.Signed.Fits w a)
    (hb : GenericRAM.Signed.Fits w b) (x : Data (r + 9))
    (hxa : x.regs left = encode a) (hxb : x.regs right = encode b) :
    ∃ y, ExecWithin (w + 2) subtract x y 17 ∧
      y.regs result = encode (GenericRAM.Signed.Arithmetic.eval .sub a b) ∧ Frame x y := by
  have hrun : ∃ y, ExecWithin (w + 2) subtract x y 17 ∧
      y.regs result = encode (GenericRAM.Signed.Arithmetic.eval .sub a b) ∧ y.mem = x.mem := by
    unfold subtract flipRightSign
    refine (WP.seq ?_).exists_execWithin
    wram_call (exec_unpack ha hb x hxa hxb) with z ⟨_, hz0, _, hma, hmb, hsa, hsb, hzm⟩
    generalize hcore : (addCore : Code .standard (r + 9)) = sub
    wram_exec [hsb]
    subst hcore
    wram_call (exec_addCore _ (by wram_simp [hma]; rfl) (by wram_simp [hmb]; rfl)
        (by wram_simp [hsa]; rfl) (by wram_simp; rfl) (by wram_simp [hz0])
        (by split_ifs <;> omega) (by split_ifs <;> omega) (by fits)) with y ⟨hyr, hym⟩
    have hneg : signedValue b.natAbs (1 - if b < 0 then 1 else 0) = -b := by
      by_cases h : b < 0
      · simp [signedValue, h, Int.ofNat_natAbs_of_nonpos (by omega : b ≤ 0)]
      · simp [signedValue, h, ← Int.eq_natAbs_of_nonneg (by omega : 0 ≤ b)]
    exact ⟨by omega, by simpa only [signedValue_encode, hneg, sub_eq_add_neg,
      GenericRAM.Signed.Arithmetic.eval] using hyr, hym.trans hzm⟩
  obtain ⟨y, he, hyr, hym⟩ := hrun
  exact ⟨y, he, hyr, hym, fun i hi => he.regs_eq (preserves hi).2.1⟩

/-- Signed multiplication runs within fourteen instructions at unsigned width `w + 2`,
provided the mathematical product fits the source signed range. No double-width unsigned
product is needed: the magnitudes' product equals the magnitude of the signed result. -/
theorem exec_multiply {w : ℕ} {a b : ℤ} (ha : GenericRAM.Signed.Fits w a)
    (hb : GenericRAM.Signed.Fits w b) (hp : GenericRAM.Signed.Fits w (a * b))
    (x : Data (r + 9)) (hxa : x.regs left = encode a) (hxb : x.regs right = encode b) :
    ∃ y, ExecWithin (w + 2) multiply x y 14 ∧
      y.regs result = encode (GenericRAM.Signed.Arithmetic.eval .mul a b) ∧ Frame x y := by
  have hprod_fit : Fits (w + 2) (2 * (a.natAbs * b.natAbs) + 1) := by
    rw [← Int.natAbs_mul]; fits
  have hrun : ∃ y, ExecWithin (w + 2) multiply x y 14 ∧
      y.regs result = encode (GenericRAM.Signed.Arithmetic.eval .mul a b) ∧ y.mem = x.mem := by
    unfold multiply multiplyMagnitudes
    refine (WP.seq ?_).exists_execWithin
    wram_call (exec_unpack ha hb x hxa hxb) with z ⟨_, hz0, _, hma, hmb, hsa, hsb, hzm⟩
    generalize hfin : (finish : Code .standard (r + 9)) = sub
    wram_exec [hma, hmb, hsa, hsb] <;>
      · subst hfin
        wram_call (exec_finish _ (by wram_simp; rfl) (by wram_simp; rfl) (by wram_simp [hz0])
            (by fits)) with y ⟨hyr, hym⟩
        refine ⟨by omega, ?_, hym.trans hzm⟩
        rw [hyr, ← encode_signedValue (by decide), ← signedValue_encode a, ← signedValue_encode b]
        dsimp only [signedValue, GenericRAM.Signed.Arithmetic.eval]
        split_ifs at hc ⊢ <;> simp_all
  obtain ⟨y, he, hyr, hym⟩ := hrun
  exact ⟨y, he, hyr, hym, fun i hi => he.regs_eq (preserves hi).2.2.1⟩

private def divMagnitude (a b sa : ℕ) : ℕ :=
  if 0 < b then a / b + if 0 < sa ∧ 0 < a % b then 1 else 0 else 0

private def divSign (b sa sb : ℕ) : ℕ :=
  if 0 < b then if sa = sb then 0 else 1 else 0

private def modMagnitude (a b sa : ℕ) : ℕ :=
  if 0 < a % b then if 0 < sa then b - a % b else a % b else 0

private theorem div_mod_signedValue {m n sa sb : ℕ} (hn : 0 < n) (hsa : sa ≤ 1) (hsb : sb ≤ 1) :
    (modMagnitude m n sa : ℤ) +
      signedValue n sb * signedValue (divMagnitude m n sa) (divSign n sa sb) =
      signedValue m sa := by
  have hrlt : m % n < n := Nat.mod_lt m hn
  have hmn : (n : ℤ) * (m / n : ℕ) + (m % n : ℕ) = (m : ℤ) := by
    exact_mod_cast Nat.div_add_mod m n
  simp only [divMagnitude, divSign, modMagnitude, signedValue, hn, ↓reduceIte]
  generalize m / n = q at hmn ⊢
  generalize m % n = r at hmn hrlt ⊢
  rcases (by omega : sa = 0 ∨ sa = 1) with rfl | rfl <;>
    rcases (by omega : sb = 0 ∨ sb = 1) with rfl | rfl <;>
    by_cases hr0 : 0 < r
  all_goals
    simp only [hr0, ↓reduceIte, Nat.lt_irrefl, zero_lt_one, true_and, false_and,
      Nat.reduceEqDiff, Nat.cast_add, Nat.cast_one, Nat.cast_zero,
      Nat.cast_sub (le_of_lt hrlt), mul_neg, neg_mul, mul_add, mul_one, mul_zero]
    omega

private theorem div_mod_nonzero {a b : ℤ} (hb : b ≠ 0) :
    let sa : ℕ := if a < 0 then 1 else 0
    let sb : ℕ := if b < 0 then 1 else 0
    a / b = signedValue (divMagnitude a.natAbs b.natAbs sa) (divSign b.natAbs sa sb) ∧
      a % b = (modMagnitude a.natAbs b.natAbs sa : ℤ) := by
  dsimp only
  set sa : ℕ := if a < 0 then 1 else 0
  set sb : ℕ := if b < 0 then 1 else 0
  have hn : 0 < b.natAbs := Int.natAbs_pos.mpr hb
  have hrlt : a.natAbs % b.natAbs < b.natAbs := Nat.mod_lt a.natAbs hn
  have heq : (modMagnitude a.natAbs b.natAbs sa : ℤ) +
      b * signedValue (divMagnitude a.natAbs b.natAbs sa) (divSign b.natAbs sa sb) = a := by
    simpa only [sa, sb, signedValue_encode] using
      div_mod_signedValue (m := a.natAbs) (sa := sa) (sb := sb) hn
        (by dsimp only [sa]; split_ifs <;> omega) (by dsimp only [sb]; split_ifs <;> omega)
  have hmod_lt : (modMagnitude a.natAbs b.natAbs sa : ℤ) < (b.natAbs : ℤ) := by
    simp only [modMagnitude, Nat.cast_lt]
    generalize a.natAbs % b.natAbs = r at hrlt ⊢
    split_ifs <;> omega
  by_cases hbp : 0 < b
  · exact (Int.ediv_emod_unique hbp).mpr
      ⟨heq, Nat.cast_nonneg _, by simpa [← Int.eq_natAbs_of_nonneg (le_of_lt hbp)] using hmod_lt⟩
  · exact (Int.ediv_emod_unique' (by omega : b < 0)).mpr
      ⟨heq, Nat.cast_nonneg _,
        by simpa [Int.ofNat_natAbs_of_nonpos (by omega : b ≤ 0)] using hmod_lt⟩

/-- Signed Euclidean division runs within twenty instructions at unsigned width `w + 2`,
including Lean's `a / 0 = 0` convention. The result is exact even at the minimum/`-1`
signed overflow `(-2 ^ (w - 1)) / (-1) = 2 ^ (w - 1)`, where `GenericRAM.Signed.model` faults and
the compiled block returns `encode (2 ^ (w - 1))` without fault reflection. -/
theorem exec_divide {w : ℕ} {a b : ℤ} (ha : GenericRAM.Signed.Fits w a)
    (hb : GenericRAM.Signed.Fits w b) (x : Data (r + 9))
    (hxa : x.regs left = encode a) (hxb : x.regs right = encode b) :
    ∃ y, ExecWithin (w + 2) divide x y 20 ∧
      y.regs result = encode (GenericRAM.Signed.Arithmetic.eval .div a b) ∧ Frame x y := by
  let sa : ℕ := if a < 0 then 1 else 0
  let sb : ℕ := if b < 0 then 1 else 0
  have hsa1 : sa ≤ 1 := by dsimp [sa]; split_ifs <;> omega
  have hqfit : Fits (w + 2) (2 * (a.natAbs / b.natAbs + 1) + 1) := by fits
  have hpre_spec (z : Data (r + 9)) (hz0 : z.regs zero = 0) (hma : z.regs magA = a.natAbs)
      (hmb : z.regs magB = b.natAbs) (hsa' : z.regs signA = sa) (hsb' : z.regs signB = sb) :
      ∃ q, ExecWithin (w + 2) divideMagnitudes z q 10 ∧
        q.regs result = divMagnitude a.natAbs b.natAbs sa ∧
        q.regs signA = divSign b.natAbs sa sb ∧ q.regs zero = 0 ∧ q.mem = z.mem := by
    wram_exec [divideMagnitudes, hz0, hma, hmb, hsa', hsb'] <;>
      · wram_simp [hz0]
        dsimp only [divMagnitude, divSign]
        split_ifs <;> omega
  have hrun : ∃ y, ExecWithin (w + 2) divide x y 20 ∧
      y.regs result = encode (GenericRAM.Signed.Arithmetic.eval .div a b) ∧ y.mem = x.mem := by
    unfold divide
    refine (WP.seq ?_).exists_execWithin
    wram_call (exec_unpack ha hb x hxa hxb) with z ⟨_, hz0, _, hma, hmb, hsa', hsb', hzm⟩
    refine WP.seq ?_
    wram_call (hpre_spec z hz0 hma hmb hsa' hsb') with q ⟨hqm, hqs, hq0, hqmem⟩
    have hdm_le : divMagnitude a.natAbs b.natAbs sa ≤ a.natAbs / b.natAbs + 1 := by
      unfold divMagnitude; generalize a.natAbs / b.natAbs = k; split_ifs <;> omega
    have hds_le : divSign b.natAbs sa sb ≤ 1 := by unfold divSign; split_ifs <;> omega
    wram_call (exec_finish q hqm hqs hq0 (by fits)) with y ⟨hyr, hym⟩
    refine ⟨by omega, ?_, hym.trans (hqmem.trans hzm)⟩
    rw [hyr, ← encode_signedValue hds_le]
    by_cases hb0 : b = 0
    · subst hb0; simp [divMagnitude, divSign, signedValue, GenericRAM.Signed.Arithmetic.eval]
    · simp only [GenericRAM.Signed.Arithmetic.eval, (div_mod_nonzero hb0).1, sa, sb]
  obtain ⟨y, he, hyr, hym⟩ := hrun
  exact ⟨y, he, hyr, hym, fun i hi => he.regs_eq (preserves hi).2.2.2.1⟩

/-- Signed Euclidean remainder runs within thirteen instructions at unsigned width `w + 2`,
including Lean's `a % 0 = a` convention. -/
theorem exec_modulo {w : ℕ} {a b : ℤ} (ha : GenericRAM.Signed.Fits w a)
    (hb : GenericRAM.Signed.Fits w b) (x : Data (r + 9))
    (hxa : x.regs left = encode a) (hxb : x.regs right = encode b) :
    ∃ y, ExecWithin (w + 2) modulo x y 13 ∧
      y.regs result = encode (GenericRAM.Signed.Arithmetic.eval .mod a b) ∧ Frame x y := by
  let sa : ℕ := if a < 0 then 1 else 0
  have hrun : ∃ y, ExecWithin (w + 2) modulo x y 13 ∧
      y.regs result = encode (GenericRAM.Signed.Arithmetic.eval .mod a b) ∧ y.mem = x.mem := by
    unfold modulo moduloCore
    refine (WP.seq ?_).exists_execWithin
    wram_call (exec_unpack ha hb x hxa hxb) with z ⟨_, hz0, hzl, hma, hmb, hsa', _, hzm⟩
    change z.regs signA = sa at hsa'
    wram_exec [hz0, hzl, hma, hmb, hsa']
    · have hb0 : b ≠ 0 := Int.natAbs_pos.mp ‹_›
      have hmod_eq : a % b = (modMagnitude a.natAbs b.natAbs sa : ℤ) := (div_mod_nonzero hb0).2
      wram_simp [hzm, GenericRAM.Signed.Arithmetic.eval, hmod_eq]
      simp only [modMagnitude, ‹0 < a.natAbs % b.natAbs›, ‹0 < sa›, ↓reduceIte, encode,
        show ¬((b.natAbs - a.natAbs % b.natAbs : ℕ) : ℤ) < 0 by omega, Int.natAbs_natCast,
        two_mul, add_zero]
    · have hb0 : b ≠ 0 := Int.natAbs_pos.mp ‹_›
      have hmod_eq : a % b = (modMagnitude a.natAbs b.natAbs sa : ℤ) := (div_mod_nonzero hb0).2
      wram_simp [hzm, GenericRAM.Signed.Arithmetic.eval, hmod_eq]
      simp only [modMagnitude, ‹0 < a.natAbs % b.natAbs›, ‹¬0 < sa›, ↓reduceIte, encode,
        show ¬((a.natAbs % b.natAbs : ℕ) : ℤ) < 0 by omega, Int.natAbs_natCast, two_mul, add_zero]
    · have hb0 : b ≠ 0 := Int.natAbs_pos.mp ‹_›
      have hmod_eq : a % b = (modMagnitude a.natAbs b.natAbs sa : ℤ) := (div_mod_nonzero hb0).2
      wram_simp [hzm, GenericRAM.Signed.Arithmetic.eval, hmod_eq]
      simp only [modMagnitude, ‹¬0 < a.natAbs % b.natAbs›, ↓reduceIte, Nat.cast_zero, encode]
      rfl
    · have hb0 : b = 0 := Int.natAbs_eq_zero.mp (by omega)
      subst hb0
      wram_simp [hzm, GenericRAM.Signed.Arithmetic.eval, Int.emod_zero]
  obtain ⟨y, he, hyr, hym⟩ := hrun
  exact ⟨y, he, hyr, hym, fun i hi => he.regs_eq (preserves hi).2.2.2.2⟩

end Cslib.WordRAM.Signed
