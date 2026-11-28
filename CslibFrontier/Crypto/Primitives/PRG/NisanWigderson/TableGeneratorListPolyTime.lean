/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.HardnessEncoding.PolyTime
public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.TableGeneratorList
import CslibFrontier.Computability.PolyTime.BinaryField
import CslibFrontier.Computability.MCSP.NP
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation

/-!
# The generator of a truth table is computable in polynomial time

`Cslib.Crypto.PRG.NisanWigderson.tableGeneratorList` is certified in the polynomial-time calculus
of multi-tape machines, in the truth table `T`, the unary parameters `S` and `m`, and the seed.
Every loop of the program runs over polynomially many elements: with `n = ⌊log₂ |T|⌋`, the grid
of the low-degree extension has `2 ^ (M b) ≤ |T| 2 ^ b` points, where `b = polyBlock n s` is
`64 (⌊log₂ (n + s + 1)⌋ + 1) + 2048`, so that `2 ^ (4 b + 1) ≤ 2 ^ 8449 (n + s + 1) ^ 256`. The
multiplication tables of the field of degree `4 b` and of the field of degree
`e = binaryFieldDegree N` are found by trial division below `2 ^ (w + 1)`, polynomially large for
the same reason. The encoding program is the one of `Cslib.HardnessEncoding.encodedProgramAt`,
reusing the polynomial-time certificate of the low-degree extension
(`Cslib.HardnessEncoding.computableInPolyTime_ldeVal'`).

## Main results

* `Cslib.Crypto.PRG.NisanWigderson.computableInPolyTime_hornerWord`: Horner's rule on coordinate
  words.
* `Cslib.Crypto.PRG.NisanWigderson.computableInPolyTime_tableSeedLength`: the seed length is
  computable.
* `Cslib.Crypto.PRG.NisanWigderson.computableInPolyTime_tableGeneratorList`: **the generator of a
  truth table is computable in polynomial time from the table**.

## References

* [M. Sudan, L. Trevisan, S. Vadhan, *Pseudorandom generators without the XOR lemma*]
  [SudanTrevisanVadhan2001]
* [N. Nisan, A. Wigderson, *Hardness vs randomness*][NisanWigderson1994]
-/

public section

open Cslib.BinaryField

namespace Cslib.Crypto.PRG.NisanWigderson

open Turing.MultiTapeTM ComputableInPolyTime Cslib.AffineDisperser Cslib.HardnessEncoding
  Cslib.BitString

private theorem binaryFieldDegree_eq (N : ℕ) :
    binaryFieldDegree N = max 1 (Nat.clog 2 N) := rfl

/-! ### Field tables and Horner's rule -/

/-- **The multiplication table of a field of computed degree**: the modulus is found by trial
division below a computed unary bound `B ≥ 2 ^ (w + 1)`. -/
theorem computableInPolyTime_fieldTable_bounded {α : Type} {input : α ↪ List Bool}
    {w B : α → ℕ} (hw : ComputableInPolyTime w input encUnary)
    (hB : ComputableInPolyTime B input encUnary) (hle : ∀ x, 2 ^ (w x + 1) ≤ B x) :
    ComputableInPolyTime (fun x => fieldTable (w x)) input encTable := by
  have hpow : ComputableInPolyTime (fun x => 2 ^ (w x + 1)) input encUnary :=
    binary_to_unary_bounded (binary_two_pow.comp (unary_add' hw (const 1))) hB hle
  have hmod : ComputableInPolyTime (fun x => modulusBits (w x)) input encBits := by
    simpa only [modulusBits, Function.comp_def] using
      computableInPolyTime_bits_unary.comp
        (computableInPolyTime_leastIrreducibleCode.comp (hpow.prod hw))
  unfold fieldTable
  exact computableInPolyTime_powerMulTable.comp hmod

/-- **Horner's rule on coordinate words is polynomial-time**: a fold over the coefficients whose
states are field elements. -/
theorem computableInPolyTime_hornerWord {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {e : α → ℕ} {xp c : α → List Bool}
    (htab : ComputableInPolyTime tab input encTable)
    (he : ComputableInPolyTime e input encUnary)
    (hx : ComputableInPolyTime xp input encBits)
    (hc : ComputableInPolyTime c input encBits) :
    ComputableInPolyTime (fun x => hornerWord (tab x) (e x) (xp x) (c x)) input encBits := by
  have hlist : ComputableInPolyTime (fun x => (c x).reverse) input (encList encBool) :=
    bitsToList.comp (bitsReverse.comp hc)
  let encQ := encPair (encPair input encBits) encBool
  have hxQ : ComputableInPolyTime (fun q : (α × List Bool) × Bool => q.1.1) encQ input :=
    (fst _ _).comp (fst _ _)
  have haccQ : ComputableInPolyTime (fun q : (α × List Bool) × Bool => q.1.2) encQ encBits :=
    (snd _ _).comp (fst _ _)
  have haQ : ComputableInPolyTime (fun q : (α × List Bool) × Bool => q.2) encQ encBool :=
    snd _ _
  have htabQ := htab.comp hxQ
  have heQ := he.comp hxQ
  have hxpQ := hx.comp hxQ
  have hstep : ComputableInPolyTime
      (fun q : (α × List Bool) × Bool => Cslib.BitString.listXor (e q.1.1)
        [if q.2 then [true] else [], fieldMul (tab q.1.1) q.1.2 (xp q.1.1)])
      encQ encBits := by
    have hf := computableInPolyTime_fieldMul' htabQ haccQ hxpQ
    have hite : ComputableInPolyTime (fun q : (α × List Bool) × Bool =>
        if q.2 then [true] else []) encQ encBits :=
      ComputableInPolyTime.ite haQ (const [true]) (const [])
    exact bitsXorWithInput heQ ((ComputableInPolyTime.cons encBits).comp
      (hite.prod ((ComputableInPolyTime.cons encBits).comp (hf.prod (const [])))))
  have h := foldlWithInput_of_bounded_growth (encIn := input) (encA := encBool)
    (encL := encList encBool) (encB := encBits)
    (list := fun x => (c x).reverse) (init := fun _ => [])
    (step := fun x acc a => Cslib.BitString.listXor (e x)
      [if a then [true] else [], fieldMul (tab x) acc (xp x)])
    (const []) ⟨hlist, hstep, inferInstance, inferInstance⟩
    (growth := e) ⟨he.polyBounded, fun x state value _ => by simp⟩
  unfold hornerWord
  exact h

/-! ### The seed cell -/

private theorem length_hornerWord_le (tab : List (List (List Bool))) (e : ℕ) (x c : List Bool) :
    (hornerWord tab e x c).length ≤ e := by
  cases c with
  | nil => simp [hornerWord]
  | cons a c => rw [hornerWord_cons, length_listXor]

/-- **The seed cell of a row is polynomial-time**, for a computed unary bound `B ≥ 2 ^ (e + 1)`. -/
theorem computableInPolyTime_tableCell {α : Type} {input : α ↪ List Bool}
    {e ℓ i j B : α → ℕ} (he : ComputableInPolyTime e input encUnary)
    (hℓ : ComputableInPolyTime ℓ input encUnary) (hi : ComputableInPolyTime i input encUnary)
    (hj : ComputableInPolyTime j input encUnary) (hB : ComputableInPolyTime B input encUnary)
    (hle : ∀ x, 2 ^ (e x + 1) ≤ B x) :
    ComputableInPolyTime (fun x => tableCell (e x) (ℓ x) (i x) (j x)) input encUnary := by
  have htab := computableInPolyTime_fieldTable_bounded he hB hle
  have hjN : ComputableInPolyTime (fun x => j x) input encNat := unary_to_binary.comp hj
  have hiN : ComputableInPolyTime (fun x => i x) input encNat := unary_to_binary.comp hi
  have hxp : ComputableInPolyTime (fun x => lowBits (e x) (j x)) input encBits :=
    bitsLow he hjN
  have hcc : ComputableInPolyTime (fun x => lowBits (ℓ x) (i x)) input encBits :=
    bitsLow hℓ hiN
  have hH := computableInPolyTime_hornerWord htab he hxp hcc
  have hval := bitsBoundedBinaryValueWithInput hB (bitsReverse.comp hH)
  have hpow : ComputableInPolyTime (fun x => 2 ^ e x) input encUnary :=
    binary_to_unary_bounded (binary_two_pow.comp he) hB fun x =>
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)).trans (hle x)
  have h := unary_add' hval (unary_mul' hpow hj)
  have hfun : (fun x => tableCell (e x) (ℓ x) (i x) (j x)) = fun x =>
      boundedBinaryValue (B x)
        (hornerWord (fieldTable (e x)) (e x) (lowBits (e x) (j x)) (lowBits (ℓ x) (i x))).reverse
        + 2 ^ e x * j x := by
    funext x
    have hlen := length_hornerWord_le (fieldTable (e x)) (e x) (lowBits (e x) (j x))
      (lowBits (ℓ x) (i x))
    have hlt : binaryValue (hornerWord (fieldTable (e x)) (e x) (lowBits (e x) (j x))
        (lowBits (ℓ x) (i x))).reverse ≤ B x := by
      refine (binaryValue_lt_two_pow _).le.trans ?_
      rw [List.length_reverse]
      exact (Nat.pow_le_pow_right (by norm_num) hlen).trans
        ((Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)).trans (hle x))
    rw [tableCell, boundedBinaryValue_eq, Nat.min_eq_right hlt]
  rw [hfun]
  exact h

/-- **The seed bits read for an output bit are polynomial-time.** -/
theorem computableInPolyTime_tablePoint {α : Type} {input : α ↪ List Bool}
    {N e ℓ i B : α → ℕ} {z : α → List Bool} (hN : ComputableInPolyTime N input encUnary)
    (he : ComputableInPolyTime e input encUnary)
    (hℓ : ComputableInPolyTime ℓ input encUnary) (hi : ComputableInPolyTime i input encUnary)
    (hB : ComputableInPolyTime B input encUnary) (hz : ComputableInPolyTime z input encBits)
    (hle : ∀ x, 2 ^ (e x + 1) ≤ B x) :
    ComputableInPolyTime (fun x => tablePoint (N x) (e x) (ℓ x) (z x) (i x)) input encBits := by
  unfold tablePoint
  refine mapToBitsWithInput (unary_range' hN) ?_
  have hfst := ComputableInPolyTime.fst input encUnary
  have hcell := computableInPolyTime_tableCell (he.comp hfst) (hℓ.comp hfst) (hi.comp hfst)
    (snd _ _) (hB.comp hfst) fun p => hle p.1
  exact bitsGetDWithInput (hz.comp hfst) hcell false

/-! ### The encoding program -/

/-- **The encoding program of a table decider is polynomial-time**, for computed parameters whose
grid `2 ^ (M b)` and moduli `2 ^ (4 b + 1) ≤ B` are polynomially bounded. -/
theorem computableInPolyTime_encodedProgramAt_table {α : Type} {input : α ↪ List Bool}
    {M b n B : α → ℕ} {T y : α → List Bool}
    (hM : ComputableInPolyTime M input encUnary) (hb : ComputableInPolyTime b input encUnary)
    (hn : ComputableInPolyTime n input encUnary) (hB : ComputableInPolyTime B input encUnary)
    (hT : ComputableInPolyTime T input encBits) (hy : ComputableInPolyTime y input encBits)
    (hbud : PolyBounded (fun x => (input x).length) fun x => 2 ^ (M x * b x))
    (hle : ∀ x, 2 ^ (4 * b x + 1) ≤ B x) :
    ComputableInPolyTime (fun x => encodedProgramAt (M x)
      (fun u => MCSP.tableValue (T x) (u.take (n x))) (y x) (b x)) input encBool := by
  have h4b : ComputableInPolyTime (fun x => 4 * b x) input encUnary := unary_mul' (const 4) hb
  have hpow2b : ∀ x, 2 ^ b x ≤ B x := fun x =>
    (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (hle x)
  have hE : ComputableInPolyTime (fun x => BitString.enumList (b x)) input (encList encBits) :=
    bitsEnumList_of_polyBounded hb (hB.polyBounded.mono hpow2b)
  have hMb : ComputableInPolyTime (fun x => M x * b x) input encUnary := unary_mul' hM hb
  have hEn : ComputableInPolyTime (fun x => BitString.enumList (M x * b x)) input
      (encList encBits) := bitsEnumList_of_polyBounded hMb hbud
  have hfst := ComputableInPolyTime.fst input encBits
  have htest : ComputableInPolyTime (fun p : α × List Bool =>
      MCSP.tableValue (T p.1) ((p.2.take (M p.1 * b p.1)).take (n p.1)))
      (encPair input encBits) encBool :=
    MCSP.computableInPolyTime_tableValue.comp ((hT.comp hfst).prod
      (bitsTakeWithInput (bitsTakeWithInput (snd _ _) (hMb.comp hfst)) (hn.comp hfst)))
  have hpts := filterWithInput
    (test := fun x z => MCSP.tableValue (T x) ((z.take (M x * b x)).take (n x))) hEn htest
  have htab := computableInPolyTime_fieldTable_bounded h4b hB hle
  have hxs : ComputableInPolyTime (fun x => (List.range (M x)).map fun i =>
      ((y x).drop (i * (4 * b x))).take (4 * b x)) input (encList encBits) := by
    have hyP := hy.comp (ComputableInPolyTime.fst input encUnary)
    have h4bP := h4b.comp (ComputableInPolyTime.fst input encUnary)
    exact mapWithInput (unary_range' hM) (bitsTakeWithInput
      (bitsDropWithInput hyP (unary_mul.comp ((snd _ _).prod h4bP))) h4bP)
  have helse : ComputableInPolyTime (fun x =>
      traceBit (((y x).drop (M x * (4 * b x))).take (4 * b x))
        (ldeVal (fieldTable (4 * b x)) (4 * b x) (b x) (M x) (BitString.enumList (b x))
          ((BitString.enumList (M x * b x)).filter fun z =>
            MCSP.tableValue (T x) ((z.take (M x * b x)).take (n x)))
          ((List.range (M x)).map fun i => ((y x).drop (i * (4 * b x))).take (4 * b x))))
      input encBool :=
    computableInPolyTime_traceBit'
      (bitsTakeWithInput (bitsDropWithInput hy (unary_mul' hM h4b)) h4b)
      (computableInPolyTime_ldeVal' htab h4b hb hM hE hpts hxs)
  unfold encodedProgramAt
  exact ite_decide (decide_eq' hb (const 0)) (const false) helse

/-! ### The parameters -/

/-- The degree of the field of the cells is computable. -/
theorem computableInPolyTime_binaryFieldDegree {α : Type} {input : α ↪ List Bool}
    {N : α → ℕ} (hN : ComputableInPolyTime N input encUnary) :
    ComputableInPolyTime (fun x => binaryFieldDegree (N x)) input encUnary := by
  have h : (fun x => binaryFieldDegree (N x)) = fun x => max 1 (Nat.clog 2 (N x)) :=
    funext fun x => binaryFieldDegree_eq _
  rw [h]
  exact unary_max.comp ((const 1).prod ((unary_clog_const 2).comp hN))

/-- `2 ^ (4 b + 1) ≤ 2 ^ 8449 (n + s + 1) ^ 256`: the moduli are polynomially large. -/
theorem two_pow_polyBlock_le (n s : ℕ) :
    2 ^ (4 * polyBlock n s + 1) ≤ 2 ^ 8449 * (n + s + 1) ^ 256 := by
  have h := Nat.pow_log_le_self 2 (show n + s + 1 ≠ 0 by omega)
  calc 2 ^ (4 * polyBlock n s + 1) = (2 ^ Nat.log 2 (n + s + 1)) ^ 256 * 2 ^ 8449 := by
        have h4 : 4 * polyBlock n s + 1 = Nat.log 2 (n + s + 1) * 256 + 8449 := by
          unfold polyBlock
          ring
        rw [h4, pow_add, pow_mul]
    _ ≤ (n + s + 1) ^ 256 * 2 ^ 8449 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h _)
    _ = 2 ^ 8449 * (n + s + 1) ^ 256 := mul_comm _ _

/-- The grid has at most `2 ^ n 2 ^ 8449 (n + s + 1) ^ 256` points. -/
theorem two_pow_polyBlocks_mul_le (n s : ℕ) :
    2 ^ (polyBlocks n s * polyBlock n s) ≤ 2 ^ n * (2 ^ 8449 * (n + s + 1) ^ 256) := by
  have h1 : polyBlocks n s * polyBlock n s ≤ n + polyBlock n s := by
    unfold polyBlocks
    rw [add_mul, one_mul]
    have := Nat.div_mul_le_self n (polyBlock n s)
    omega
  calc 2 ^ (polyBlocks n s * polyBlock n s) ≤ 2 ^ (n + polyBlock n s) :=
        Nat.pow_le_pow_right (by norm_num) h1
    _ = 2 ^ n * 2 ^ polyBlock n s := pow_add _ _ _
    _ ≤ 2 ^ n * (2 ^ 8449 * (n + s + 1) ^ 256) :=
        Nat.mul_le_mul_left _ ((Nat.pow_le_pow_right (by norm_num) (by omega)).trans
          (two_pow_polyBlock_le n s))

/-- The cells are numbered below `2 ^ (e + 1) ≤ 4 N`. -/
theorem two_pow_degree_le (n s : ℕ) :
    2 ^ (binaryFieldDegree (polyArity n s) + 1) ≤ 4 * polyArity n s := by
  have h := two_pow_binaryFieldDegree_le (n := polyArity n s) (by
    have := polyBlock_pos n s
    unfold polyArity
    nlinarith)
  rw [pow_succ]
  omega

/-- `2 ^ ⌊log₂ l⌋ ≤ l + 1`. -/
private theorem two_pow_log_le (l : ℕ) : 2 ^ Nat.log 2 l ≤ l + 1 := by
  rcases Nat.eq_zero_or_pos l with rfl | h
  · simp
  · exact (Nat.pow_log_le_self 2 h.ne').trans (Nat.le_succ _)

section params

variable {α : Type} {input : α ↪ List Bool}

/-- The hardness `tableHardness S m` of the encoding is computable from `S` and `m`. -/
theorem computableInPolyTime_tableHardness {S m : α → ℕ}
    (hS : ComputableInPolyTime S input encUnary) (hm : ComputableInPolyTime m input encUnary) :
    ComputableInPolyTime (fun x => tableHardness (S x) (m x)) input encUnary := by
  unfold tableHardness
  exact unary_add' (unary_add' hS (unary_mul' (const 20)
    ((unary_pow 3).comp (unary_add' hm (const 1))))) (const 2)

/-- The block length `polyBlock n s` is computable from `n` and `s`. -/
theorem computableInPolyTime_polyBlock {n s : α → ℕ}
    (hn : ComputableInPolyTime n input encUnary) (hs : ComputableInPolyTime s input encUnary) :
    ComputableInPolyTime (fun x => polyBlock (n x) (s x)) input encUnary := by
  unfold polyBlock
  exact unary_add' (unary_mul' (const 64) (unary_add' (unary_log_two.comp
    (unary_add' (unary_add' hn hs) (const 1))) (const 1))) (const 2048)

/-- The number of blocks `polyBlocks n s` is computable from `n` and `s`. -/
theorem computableInPolyTime_polyBlocks {n s : α → ℕ}
    (hn : ComputableInPolyTime n input encUnary) (hs : ComputableInPolyTime s input encUnary) :
    ComputableInPolyTime (fun x => polyBlocks (n x) (s x)) input encUnary := by
  unfold polyBlocks
  exact unary_add' (unary_div' hn (computableInPolyTime_polyBlock hn hs)) (const 1)

/-- The block size `tableBlock n S m` of the design is computable from `n`, `S` and `m`. -/
theorem computableInPolyTime_tableBlock {n S m : α → ℕ}
    (hn : ComputableInPolyTime n input encUnary) (hS : ComputableInPolyTime S input encUnary)
    (hm : ComputableInPolyTime m input encUnary) :
    ComputableInPolyTime (fun x => tableBlock (n x) (S x) (m x)) input encUnary := by
  have hs := computableInPolyTime_tableHardness hS hm
  have hb := computableInPolyTime_polyBlock hn hs
  unfold tableBlock polyArity
  exact unary_add' (unary_mul' (computableInPolyTime_polyBlocks hn hs) (unary_mul' (const 4) hb))
    (unary_mul' (const 4) hb)

/-- The design parameter `tableLog m` is computable from `m`. -/
theorem computableInPolyTime_tableLog {m : α → ℕ} (hm : ComputableInPolyTime m input encUnary) :
    ComputableInPolyTime (fun x => tableLog (m x)) input encUnary := by
  unfold tableLog
  exact unary_add' (unary_log_two.comp hm) (const 1)

/-- **The seed length is computable**, in unary, from `n`, `S` and `m`: the field has at most
`2 N` elements for the block size `N`. -/
theorem computableInPolyTime_tableSeedLength {n S m : α → ℕ}
    (hn : ComputableInPolyTime n input encUnary) (hS : ComputableInPolyTime S input encUnary)
    (hm : ComputableInPolyTime m input encUnary) :
    ComputableInPolyTime (fun x => tableSeedLength (n x) (S x) (m x)) input encUnary := by
  have hN := computableInPolyTime_tableBlock hn hS hm
  have hpow : ComputableInPolyTime (fun x => 2 ^ binaryFieldDegree (tableBlock (n x) (S x) (m x)))
      input encUnary :=
    binary_to_unary_bounded (binary_two_pow.comp (computableInPolyTime_binaryFieldDegree hN))
      (unary_mul' (const 4) hN) fun x =>
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)).trans (two_pow_degree_le _ _)
  unfold tableSeedLength
  exact unary_mul' hN hpow

end params

/-- **The generator of a truth table is computable in polynomial time from the table**, in any
input context. The parameters `S` and `m` are unary, and the table `T`, of length `2 ^ n`, is read
with `n` as `Nat.log 2 |T|`: the time is polynomial in `|T| + S + m + |z|`. -/
theorem computableInPolyTime_tableGeneratorList {α : Type} {input : α ↪ List Bool}
    {S m : α → ℕ} {T z : α → List Bool} (hS : ComputableInPolyTime S input encUnary)
    (hm : ComputableInPolyTime m input encUnary) (hT : ComputableInPolyTime T input encBits)
    (hz : ComputableInPolyTime z input encBits) :
    ComputableInPolyTime (fun x => tableGeneratorList (S x) (m x) (T x) (z x)) input
      encBits := by
  unfold tableGeneratorList
  refine mapToBitsWithInput (unary_range' hm) ?_
  have hfst := ComputableInPolyTime.fst input encUnary
  have hn : ComputableInPolyTime (fun p : α × ℕ => Nat.log 2 (T p.1).length)
      (encPair input encUnary) encUnary := unary_log_two.comp (length_bits.comp (hT.comp hfst))
  have hs := computableInPolyTime_tableHardness (hS.comp hfst) (hm.comp hfst)
  have hb := computableInPolyTime_polyBlock hn hs
  have hN := computableInPolyTime_tableBlock hn (hS.comp hfst) (hm.comp hfst)
  have hBc : ComputableInPolyTime (fun p : α × ℕ => 2 ^ 8449 * (Nat.log 2 (T p.1).length +
      tableHardness (S p.1) (m p.1) + 1) ^ 256) (encPair input encUnary) encUnary :=
    unary_mul' (const _) ((unary_pow 256).comp (unary_add' (unary_add' hn hs) (const 1)))
  have hpoint := computableInPolyTime_tablePoint hN (computableInPolyTime_binaryFieldDegree hN)
    (computableInPolyTime_tableLog (hm.comp hfst)) (snd _ _) (unary_mul' (const 4) hN)
    (hz.comp hfst) fun p => two_pow_degree_le _ _
  have hlenT := (length_bits.comp (hT.comp hfst)).polyBounded
  refine computableInPolyTime_encodedProgramAt_table (computableInPolyTime_polyBlocks hn hs) hb
    hn hBc (hT.comp hfst) hpoint ?_ fun p => two_pow_polyBlock_le _ _
  refine ((hlenT.add (.const 1)).mul hBc.polyBounded).mono fun p => ?_
  refine (two_pow_polyBlocks_mul_le _ _).trans ?_
  exact Nat.mul_le_mul_right _ (two_pow_log_le _)

end Cslib.Crypto.PRG.NisanWigderson
