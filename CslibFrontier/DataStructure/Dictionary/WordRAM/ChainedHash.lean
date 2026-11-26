/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.Spec
public import CslibFrontier.DataStructure.HashFamily.WordRAM.MultiplyShift
public import CslibFrontier.Computability.WordRAM.ExactNotation
public import CslibFrontier.DataStructure.WordRAM.Randomized.StateTransition
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Data.Nat.Log
public import CslibFrontier.Tactic.WramOmega.Init
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.CanonicalCall
import CslibFrontier.Computability.WordRAM.SymbolicExec.MemFrame
import CslibFrontier.Tactic.WramOmega

/-!
# Chained Hash Table on the Randomized Word RAM

This file implements a textbook chained hash table ([CLRS2009], Sections 11.2 and 11.3.3,
Theorem 11.3 and Corollary 11.4) realizing the bounded-capacity insert-only dictionary specification
`Cslib.DataStructure.Dictionary.spec U V n_max` (`query` and `insert` up to `n_max` distinct keys,
with deletion deferred to a follow-up) on the randomized Word RAM over `Cslib.WordRAM.Basis.exact`
(and lifted to `Basis.standard` via `StateTransitionImpl.toStandard`).

## Model, specialization, and cost scope

* **Specialization and external word width:** For fixed universe `U` and capacity bound `n_max` and
  an admissible external machine word width `w` (`2 * hashBits U n_max ≤ w`,
  `Fits w (base + space n_max)`, `Fits w V`), the specialized program `subroutineCode U n_max` uses
  precomputed configuration literals (`bucketBits`, `hashBits`, bit masks, and layout offsets baked
  as instruction literals, with `initParams = Fin.elim0`).
* **Charged body cost and oblivious adversary:** The expected time bounds charge initialization and
  subroutine operation **bodies** across an operation history `ops` fixed independently of the
  sampled hash seed (oblivious adversary), excluding caller argument delivery, caller
  control/dispatch loops, and code/configuration construction.
* **Insert-only node pool:** Because `Dictionary.spec U V n_max` is insert-only, both the linear
  space bound `space n_max ≤ 5 * n_max + 8` and sequential bump allocation
  (`allocCount ∈ [0, n_max]`) rely on the absence of deletions; a future deletion extension would
  revisit node-pool slot recycling.

## Design and memory layout

Given key universe `Fin U` and capacity bound `n_max`, the data structure chooses:
* power-of-two bucket count `m = numBuckets n_max = 2 ^ M` with
  `M = bucketBits n_max = Nat.clog 2 (max n_max 2)`, so `max n_max 2 ≤ 2 ^ M ≤ 2 * max n_max 2`
  and the load factor satisfies `n / m ≤ n_max / 2 ^ M ≤ 1`;
* multiply-shift input bit-width `w₀ = hashBits U n_max = max M (Nat.clog 2 (max U 2))`, so
  `0 < w₀`, `M ≤ w₀`, and `U ≤ 2 ^ w₀`.

All state resides in a single contiguous memory block `[base, base + space n_max)` of
`space n_max = 4 + 2 ^ M + 3 * n_max ≤ 5 * n_max + 8 = O(n_max)` words:
* `[base, base + 4)`: 4-word header storing the sampled multiply-shift seed `b < 2 ^ (w₀ - 1)`,
  `M`, `w₀`, and the sequential node allocation counter `allocCount ∈ [0, n_max]`;
* `[base + 4, base + 4 + 2 ^ M)`: bucket head array `head[0 .. 2 ^ M - 1]` storing `0` for an
  empty chain and `idx + 1` for pool slot `idx ∈ [0, allocCount)` (so fresh zeroed memory already
  represents `2 ^ M` empty buckets in `O(1)` instructions);
* `[base + 4 + 2 ^ M, base + 4 + 2 ^ M + 3 * n_max)`: static `n_max`-slot node pool split into
  `key[0 .. n_max - 1]`, `val[0 .. n_max - 1]`, and `next[0 .. n_max - 1]`.

## Operations and expected complexity

* `initSetup`: invokes `MultiplyShift.initCode w₀` (`1` `Instr.rand` call) to sample a uniform odd
  multiplier seed `b ∈ Fin (2 ^ (w₀ - 1))` and writes the 4-word header (`16` instructions total
  for `initFresh` on zeroed memory, `O(n_max)` via `initClear` on arbitrary dirty memory).
* `query u` and `insert u v`: evaluate the bucket index
  `bk = multiplyShift w₀ M b (encodeKey u)` via
  `MultiplyShift.evalCode w₀ M`, traverse the singly-linked chain from `head[bk]` via
  `findInChain`, and either return `val[idx] + 1` / `0` (`query`), overwrite `val[idx] ← v` in place
  on a key hit (`insert`), or bump-allocate slot `allocCount` and prepend it to `head[bk]` on a
  key miss (`insert`).
* By linearity of expectation and the `(2 / 2 ^ M)`-universality of multiply-shift hashing
  (`Cslib.Probability.isUniversalHash_multiplyShift`, [DietzfelbingerHagerupKatajainenPenttonen1997]
  Lemma 2.4; [CLRS2009], Section 11.3.3, Theorem 11.3 and Corollary 11.4), the expected number of
  other keys in `dom s \ {u}` colliding with `u` is at most
  `((dom s).card : ℝ≥0∞) * (2 / 2 ^ M) ≤ n_max * (2 / 2 ^ M) ≤ 2`, giving worst-case expected
  `O(1)` (`chargeVal = 73`) body instructions per operation with zero potential (`potential = 0`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ChainedHash.bucketBits`, `numBuckets`, `hashBits`,
  `space`:
  table dimension parameters and `O(n_max)` memory footprint.
* `Cslib.DataStructure.Dictionary.WordRAM.ChainedHash.subroutineCode`: relocatable `SubroutineCode`
  bundle over `Basis.exact`.
* `Cslib.DataStructure.Dictionary.WordRAM.ChainedHash.Rep`: seed-coupled concrete representation
  invariant.
* `Cslib.DataStructure.Dictionary.WordRAM.ChainedHash.impl`, `implStandard`:
  `Cslib.DataStructure.WordRAM.Randomized.StateTransitionImpl` certificates over `Basis.exact` and
  `Basis.standard`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ChainedHash.space_le`: linear space bound
  `space n_max ≤ 5 * n_max + 8`.
* `Cslib.DataStructure.Dictionary.WordRAM.ChainedHash.expect_collCount_le_card_mul`,
  `expect_collCount_le_two`: universal-hashing expected collision bounds.
* `Cslib.DataStructure.Dictionary.WordRAM.ChainedHash.seq_expected_amortized`: expected subroutine
  body step bound across any admissible oblivious sequence of `query` and `insert` operations.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Sections 11.2 and 11.3.3 (Theorem 11.3 and Corollary 11.4)][CLRS2009]
* [M. Dietzfelbinger, T. Hagerup, J. Katajainen and M. Penttonen, *A Reliable Randomized Algorithm
  for the Closest-Pair Problem*, Lemma 2.4][DietzfelbingerHagerupKatajainenPenttonen1997]
-/

@[expose] public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ChainedHash

open Cslib.WordRAM
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.Probability
open scoped ENNReal

/-! ## 1. Table dimension parameters and arithmetic bounds -/

/-- Logarithmic bucket bit-width `M = ⌈log₂(max n_max 2)⌉`. -/
@[wram_arith]
def bucketBits (n_max : ℕ) : ℕ :=
  Nat.clog 2 (max n_max 2)

/-- Power-of-two bucket count `m = 2 ^ M`. -/
def numBuckets (n_max : ℕ) : ℕ :=
  2 ^ bucketBits n_max

/-- Multiply-shift input bit-width `w₀ = max M ⌈log₂(max U 2)⌉`. -/
def hashBits (U n_max : ℕ) : ℕ :=
  max (bucketBits n_max) (Nat.clog 2 (max U 2))

/-- Total contiguous memory footprint `4 + 2 ^ M + 3 * n_max` words. -/
@[wram_arith]
def space (n_max : ℕ) : ℕ :=
  4 + numBuckets n_max + 3 * n_max

theorem bucketBits_pos (n_max : ℕ) : 0 < bucketBits n_max :=
  (by decide : 0 < Nat.clog 2 2).trans_le (Nat.clog_mono_right 2 (le_max_right n_max 2))

theorem bucketBits_le_hashBits (U n_max : ℕ) : bucketBits n_max ≤ hashBits U n_max :=
  le_max_left _ _

theorem hashBits_pos (U n_max : ℕ) : 0 < hashBits U n_max :=
  (bucketBits_pos n_max).trans_le (bucketBits_le_hashBits U n_max)

theorem max_le_numBuckets (n_max : ℕ) : max n_max 2 ≤ numBuckets n_max :=
  Nat.le_pow_clog (by decide : 1 < 2) (max n_max 2)

theorem le_numBuckets (n_max : ℕ) : n_max ≤ numBuckets n_max :=
  (le_max_left n_max 2).trans (max_le_numBuckets n_max)

theorem two_le_numBuckets (n_max : ℕ) : 2 ≤ numBuckets n_max :=
  (le_max_right n_max 2).trans (max_le_numBuckets n_max)

theorem numBuckets_pos (n_max : ℕ) : 0 < numBuckets n_max :=
  Nat.two_pow_pos _

/-- The power-of-two bucket count `numBuckets n_max` is at most `2 * n_max + 4`. -/
theorem numBuckets_le (n_max : ℕ) : numBuckets n_max ≤ 2 * n_max + 4 := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (bucketBits_pos n_max).ne'
  have hpow : 2 ^ m < max n_max 2 :=
    (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mp (by rw [← bucketBits, hm]; omega)
  have hnb : numBuckets n_max = 2 * 2 ^ m := by rw [numBuckets, hm, pow_succ']
  omega

/-- Linear `O(n_max)` space bound: `space n_max ≤ 5 * n_max + 8`. -/
theorem space_le (n_max : ℕ) : space n_max ≤ 5 * n_max + 8 := by
  have := numBuckets_le n_max; unfold space; omega

theorem le_two_pow_hashBits (U n_max : ℕ) : U ≤ 2 ^ hashBits U n_max := by
  calc
    U ≤ max U 2 := le_max_left U 2
    _ ≤ 2 ^ Nat.clog 2 (max U 2) := Nat.le_pow_clog (by decide : 1 < 2) (max U 2)
    _ ≤ 2 ^ hashBits U n_max :=
      Nat.pow_le_pow_right two_pos (le_max_right (bucketBits n_max) _)

/-- Canonical injection of keys `Fin U` into the multiply-shift domain `Fin (2 ^ hashBits U n_max)`.
-/
def encodeKey {U n_max : ℕ} (u : Fin U) : Fin (2 ^ hashBits U n_max) :=
  ⟨u.val, u.isLt.trans_le (le_two_pow_hashBits U n_max)⟩

@[simp]
theorem encodeKey_val {U n_max : ℕ} (u : Fin U) :
    (encodeKey (n_max := n_max) u).val = u.val := rfl

theorem encodeKey_injective (U n_max : ℕ) :
    Function.Injective (encodeKey (U := U) (n_max := n_max)) :=
  fun _ _ h => Fin.ext (Fin.mk.inj_iff.mp h)

/-- Every multiply-shift hash value lies strictly below `2 ^ M`. -/
theorem multiplyShift_lt_two_pow {w₀ M : ℕ} (hM : M ≤ w₀)
    (b : Fin (2 ^ (w₀ - 1))) (x : Fin (2 ^ w₀)) :
    multiplyShift w₀ M b x < 2 ^ M :=
  Nat.div_lt_of_lt_mul <| by
    rw [← pow_add, Nat.sub_add_cancel hM]; exact Nat.mod_lt _ (by positivity)

theorem multiplyShift_lt_numBuckets {U n_max : ℕ}
    (b : Fin (2 ^ (hashBits U n_max - 1))) (u : Fin U) :
    multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u) < numBuckets n_max :=
  multiplyShift_lt_two_pow (bucketBits_le_hashBits U n_max) b (encodeKey u)

/-! ## 2. Register layout, memory offsets, and structured Word-RAM code -/

/-- Total local register count of the chained hash table (`1` persistent + `21` scratch/caller). -/
abbrev rHash : ℕ := 22

namespace Reg

/-- Multiply-shift seed register (`0`). -/
abbrev regB : Fin rHash := 0
/-- Multiply-shift key register (`1`). -/
abbrev regX : Fin rHash := 1
/-- Multiply-shift bucket output register (`2`). -/
abbrev regOut : Fin rHash := 2
/-- Multiply-shift scratch register 1 (`3`, also `curReg` for `zeroFillCode`). -/
abbrev regT1 : Fin rHash := 3
/-- Multiply-shift scratch register 2 (`4`). -/
abbrev regT2 : Fin rHash := 4
/-- Persistent base address register (`5`). -/
abbrev baseReg : Fin rHash := 5
/-- Bump-allocation frontier register (`6`). -/
abbrev frontierReg : Fin rHash := 6
/-- Operation tag register (`7`: `0` = `query`, `≠ 0` = `insert`). -/
abbrev tagReg : Fin rHash := 7
/-- Input key register `u.val` (`8`). -/
abbrev argU : Fin rHash := 8
/-- Input value register `v` (`9`). -/
abbrev argV : Fin rHash := 9
/-- Output register (`10`: `0` = `none`, `v + 1` = `some v` on `query`). -/
abbrev outReg : Fin rHash := 10
/-- Constant `0` scratch register (`11`, also `zeroReg` for `zeroFillCode`). -/
abbrev zero : Fin rHash := 11
/-- Constant `1` scratch register (`12`, also `oneReg` for `zeroFillCode`). -/
abbrev one : Fin rHash := 12
/-- Bucket head array base `base + 4` (`13`). -/
abbrev headBaseReg : Fin rHash := 13
/-- Node key array base `base + 4 + numBuckets n_max` (`14`). -/
abbrev keyBaseReg : Fin rHash := 14
/-- Node value array base `base + 4 + numBuckets n_max + n_max` (`15`). -/
abbrev valBaseReg : Fin rHash := 15
/-- Node next-pointer array base `base + 4 + numBuckets n_max + 2 * n_max` (`16`). -/
abbrev nextBaseReg : Fin rHash := 16
/-- Current 1-based chain pointer (`17`). -/
abbrev cur : Fin rHash := 17
/-- Current 0-based pool slot index (`18`). -/
abbrev idx : Fin rHash := 18
/-- Key-hit indicator flag (`19`). -/
abbrev found : Fin rHash := 19
/-- Matched 0-based pool slot index (`20`). -/
abbrev matchIdx : Fin rHash := 20
/-- Scratch memory address / value register (`21`). -/
abbrev addr : Fin rHash := 21

end Reg

open Reg

/-- Embedding of the 5 multiply-shift registers (`Fin 5`) into `Fin rHash` (`0..4`). -/
def hashEmbed : Fin 5 → Fin rHash :=
  Fin.castLE (by decide : 5 ≤ rHash)

theorem hashEmbed_injective : Function.Injective hashEmbed :=
  Fin.castLE_injective (by decide : 5 ≤ rHash)

/-- Register classification: only `baseReg` (`5`) is persistent (`false`); all other registers are
caller-overwritable (`true`). -/
def inputMask (i : Fin rHash) : Bool :=
  decide (i ≠ baseReg)

/-- Memory address of the bucket head array `head[0 .. numBuckets n_max - 1]`. -/
@[wram_arith]
def headBase (base : ℕ) : ℕ :=
  base + 4

/-- Memory address of the node key array `key[0 .. n_max - 1]`. -/
@[wram_arith]
def keyBase (base n_max : ℕ) : ℕ :=
  base + 4 + numBuckets n_max

/-- Memory address of the node value array `val[0 .. n_max - 1]`. -/
@[wram_arith]
def valBase (base n_max : ℕ) : ℕ :=
  base + 4 + numBuckets n_max + n_max

/-- Memory address of the node next-pointer array `next[0 .. n_max - 1]`. -/
@[wram_arith]
def nextBase (base n_max : ℕ) : ℕ :=
  base + 4 + numBuckets n_max + 2 * n_max

/-- Bump-allocate `space n_max` words at `frontierReg`, recording `baseReg := frontierReg` and
advancing `frontierReg := baseReg + space n_max`. -/
def allocSpan (n_max : ℕ) : Code .exact rHash := ram_exact[
  baseReg ← frontierReg;
  addr ← #(space n_max);
  frontierReg ← baseReg + addr ]

/-- Store the sampled multiply-shift seed `regB`, `bucketBits n_max`, `hashBits U n_max`, and
initial allocation count `0` into the 4-word header `[base, base + 4)`. -/
def storeHeader (U n_max : ℕ) : Code .exact rHash := ram_exact[
  *baseReg ← regB;
  one ← #1;
  addr ← baseReg + one;
  idx ← #(bucketBits n_max);
  *addr ← idx;
  addr ← addr + one;
  idx ← #(hashBits U n_max);
  *addr ← idx;
  addr ← addr + one;
  zero ← #0;
  *addr ← zero ]

/-- Self-contained hash-table initialization: sample a uniform multiply-shift seed via
`MultiplyShift.initCode` and write the 4-word header. -/
def initSetup (U n_max : ℕ) : Code .exact rHash :=
  .seq ((MultiplyShift.initCode (hashBits U n_max)).rename hashEmbed)
       (storeHeader U n_max)

/-- Load the stored seed `b` into `regB` and copy key `argU` into `regX`. -/
def prepHash : Code .exact rHash := ram_exact[
  regB ← *baseReg;
  regX ← argU ]

/-- Compute array base pointers and load `cur := head[regOut]`, clearing `found` and `matchIdx`. -/
def loadBucketHead (n_max : ℕ) : Code .exact rHash := ram_exact[
  zero ← #0;
  one ← #1;
  addr ← #4;
  headBaseReg ← baseReg + addr;
  addr ← #(numBuckets n_max);
  keyBaseReg ← headBaseReg + addr;
  addr ← #n_max;
  valBaseReg ← keyBaseReg + addr;
  nextBaseReg ← valBaseReg + addr;
  addr ← headBaseReg + regOut;
  cur ← *addr;
  found ← zero;
  matchIdx ← zero ]

/-- Evaluate the bucket index `regOut = multiplyShift w₀ M b (encodeKey u)` and load `head[regOut]`
into `cur`. -/
def evalBucket (U n_max : ℕ) : Code .exact rHash :=
  .seq prepHash
    (.seq ((MultiplyShift.evalCode (hashBits U n_max) (bucketBits n_max)).rename hashEmbed)
      (loadBucketHead n_max))

/-- Single step of chain traversal: inspect slot `idx = cur - 1`; if `key[idx] = argU`, record
`found := 1, matchIdx := idx` and terminate the loop (`cur := 0`), else advance `cur := next[idx]`.
-/
def findInChainBody : Code .exact rHash := ram_exact[
  idx ← cur - one;
  addr ← keyBaseReg + idx;
  regT1 ← *addr;
  if regT1 = argU then [
    found ← one;
    matchIdx ← idx;
    cur ← zero
  ] else [
    addr ← nextBaseReg + idx;
    cur ← *addr
  ] ]

/-- Traverse the singly-linked bucket chain starting at `cur`. -/
def findInChain : Code .exact rHash := ram_exact[
  while zero < cur do [ ⟪findInChainBody⟫ ] ]

/-- Complete `query u` after `findInChain`: return `val[matchIdx] + 1` on a hit, or `0` on a
miss. -/
def finishQuery : Code .exact rHash := ram_exact[
  if zero < found then [
    addr ← valBaseReg + matchIdx;
    regT1 ← *addr;
    outReg ← regT1 + one
  ] else [
    outReg ← zero
  ] ]

/-- Complete `insert u v` on a key hit: overwrite `val[matchIdx] ← argV` in place. -/
def finishInsertHit : Code .exact rHash := ram_exact[
  addr ← valBaseReg + matchIdx;
  *addr ← argV ]

/-- Complete `insert u v` on a key miss: allocate slot `idx = allocCount`, increment `allocCount`,
write `key[idx] := argU`, `val[idx] := argV`, `next[idx] := head[regOut]`, and
`head[regOut] := idx + 1`. -/
def finishInsertMiss : Code .exact rHash := ram_exact[
  addr ← #3;
  addr ← baseReg + addr;
  idx ← *addr;
  regT1 ← idx + one;
  *addr ← regT1;
  addr ← keyBaseReg + idx;
  *addr ← argU;
  addr ← valBaseReg + idx;
  *addr ← argV;
  addr ← headBaseReg + regOut;
  regT2 ← *addr;
  addr ← nextBaseReg + idx;
  *addr ← regT2;
  addr ← headBaseReg + regOut;
  *addr ← regT1 ]

/-- Complete `insert u v` after `findInChain`. -/
def finishInsert : Code .exact rHash := ram_exact[
  if zero < found then [ ⟪finishInsertHit⟫ ] else [ ⟪finishInsertMiss⟫ ] ]

/-- Dispatch post-traversal completion between `query` (`tagReg = 0`) and `insert`
(`tagReg ≠ 0`). -/
def finishOp : Code .exact rHash := ram_exact[
  if tagReg = zero then [ ⟪finishQuery⟫ ] else [ ⟪finishInsert⟫ ] ]

/-- Unified operation dispatcher for `query` and `insert`. -/
def opCode (U n_max : ℕ) : Code .exact rHash :=
  .seq (evalBucket U n_max) (.seq findInChain finishOp)

/-- Relocatable `SubroutineCode` bundle for the chained hash table over `Basis.exact`. -/
def subroutineCode (U n_max : ℕ) : SubroutineCode .exact rHash 0 where
  allocSpan := allocSpan n_max
  initSetup := initSetup U n_max
  code := opCode U n_max
  frontierReg := frontierReg
  baseReg := baseReg
  initParams := Fin.elim0
  curReg := regT1
  zeroReg := zero
  oneReg := one
  incCur := .exactBin .add regT1 regT1 one
  input := inputMask
  output := outReg

/-- Standalone register encoding for `Dictionary.Op U`. -/
def encode {U : ℕ} : Dictionary.Op U → Fin rHash → ℕ
  | .query u => fun i => if i = tagReg then 0 else if i = argU then u.val else 0
  | .insert u v => fun i =>
      if i = tagReg then 1 else if i = argU then u.val else if i = argV then v else 0

/-- Partial argument-matching predicate for inline dictionary calls. -/
def argMatch {U : ℕ} : Dictionary.Op U → (Fin rHash → ℕ) → Prop
  | .query u => fun regs => regs tagReg = 0 ∧ regs argU = u.val
  | .insert u v => fun regs => regs tagReg ≠ 0 ∧ regs argU = u.val ∧ regs argV = v

/-- Output decoder for `Dictionary.spec U V n_max` (`0` = `none`, `v + 1` = `some v` on
`query`). -/
def decode {U V n_max : ℕ} :
    (o : (Dictionary.spec U V n_max).Op) → (Fin rHash → ℕ) →
      Option ((Dictionary.spec U V n_max).Result o)
  | .query _, regs =>
      if regs outReg = 0 then some none else some (some (regs outReg - 1))
  | .insert _ _, _ => some ()

theorem arguments_fit {U V n_max w base : ℕ}
    (hw : 2 * hashBits U n_max ≤ w) (hS : Fits w (base + space n_max)) (hV : Fits w V)
    {s : Dictionary.State U} (o : Dictionary.Op U)
    (hv : (Dictionary.spec U V n_max).valid s o) (i : Fin rHash) :
    Fits w (encode o i) := by
  have hu_fit (u : Fin U) : Fits w u.val :=
    Fits.mono (u.isLt.trans_le (le_two_pow_hashBits U n_max)) (by omega)
  have h1 : Fits w 1 := hS.of_le (by wram_omega)
  cases o with
  | query u => dsimp only [encode]; split_ifs <;> first | exact fits_zero w | exact hu_fit u
  | insert u v =>
    dsimp only [encode]
    split_ifs <;> first | exact h1 | exact hu_fit u | exact hV.of_le hv.2.le | exact fits_zero w

theorem encode_matches {U : ℕ} (o : Dictionary.Op U) (regs : Fin rHash → ℕ) :
    argMatch o (fun i => if inputMask i then encode o i else regs i) := by
  cases o <;> simp +decide [argMatch, encode]

/-! ## 3. Concrete representation invariant and chain length bound -/

/-- Inductive linked-list predicate for a bucket chain in `mem`: `IsChain mem nextBase sz ptr L`
states that following 1-based pointers from `ptr` through `next[idx]` (`mem (nextBase + idx)`)
visits the sequence `L` of 0-based pool indices `< sz` before reaching `0`. -/
inductive IsChain (mem : ℕ → ℕ) (nextBase sz : ℕ) : ℕ → List ℕ → Prop where
  | nil : IsChain mem nextBase sz 0 []
  | cons {idx nextPtr : ℕ} {rest : List ℕ} :
      idx < sz →
      mem (nextBase + idx) = nextPtr →
      IsChain mem nextBase sz nextPtr rest →
      IsChain mem nextBase sz (idx + 1) (idx :: rest)

theorem IsChain.lt_sz {mem : ℕ → ℕ} {nextBase sz ptr : ℕ} {L : List ℕ}
    (h : IsChain mem nextBase sz ptr L) : ∀ idx ∈ L, idx < sz := by
  induction h with
  | nil => simp
  | cons hlt _ _ ih =>
    rintro _ (_ | ⟨_, hm'⟩)
    exacts [hlt, ih _ hm']

theorem IsChain.unique {mem : ℕ → ℕ} {nextBase sz₁ sz₂ ptr : ℕ} {L₁ L₂ : List ℕ}
    (h₁ : IsChain mem nextBase sz₁ ptr L₁) (h₂ : IsChain mem nextBase sz₂ ptr L₂) :
    L₁ = L₂ := by
  induction h₁ generalizing L₂ with
  | nil => cases h₂; rfl
  | cons _ hn₁ _ ih =>
    cases h₂ with | cons _ hn₂ hc₂ => exact congrArg _ (ih (hn₁.symm.trans hn₂ ▸ hc₂))

theorem IsChain.congr_mem {mem mem' : ℕ → ℕ} {nextBase sz ptr : ℕ} {L : List ℕ}
    (h : IsChain mem nextBase sz ptr L)
    (hmem : ∀ idx ∈ L, mem' (nextBase + idx) = mem (nextBase + idx)) :
    IsChain mem' nextBase sz ptr L := by
  induction h with
  | nil => exact .nil
  | cons hlt hn _ ih =>
    exact .cons hlt ((hmem _ List.mem_cons_self).trans hn)
      (ih fun i hi => hmem i (List.mem_cons_of_mem _ hi))

theorem IsChain.mono_sz {mem : ℕ → ℕ} {nextBase sz sz' ptr : ℕ} {L : List ℕ}
    (h : IsChain mem nextBase sz ptr L) (hsz : sz ≤ sz') :
    IsChain mem nextBase sz' ptr L := by
  induction h with
  | nil => exact .nil
  | cons hlt hn _ ih => exact .cons (hlt.trans_le hsz) hn ih

/-- Invariant for a single bucket `bk < numBuckets n_max` with chain `L : List ℕ`. -/
structure BucketInv (U n_max base : ℕ) (b : Fin (2 ^ (hashBits U n_max - 1)))
    (s : Dictionary.State U) (mem : ℕ → ℕ) (bk : ℕ) (L : List ℕ) : Prop where
  /-- `L` is the chain of 0-based slot indices starting at `head[bk]`. -/
  chain : IsChain mem (nextBase base n_max) (Dictionary.dom s).card (mem (headBase base + bk)) L
  /-- Keys stored along `L` are pairwise distinct. -/
  nodup : (L.map fun idx => mem (keyBase base n_max + idx)).Nodup
  /-- Every node `idx ∈ L` stores a key `u ∈ dom s` hashing to `bk` with value `val[idx]`. -/
  sound : ∀ idx ∈ L, ∃ u : Fin U,
    mem (keyBase base n_max + idx) = u.val ∧
    multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u) = bk ∧
    s u = some (mem (valBase base n_max + idx))
  /-- Every key `u ∈ dom s` hashing to `bk` appears in `L`. -/
  complete : ∀ (u : Fin U) (v : ℕ),
    multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u) = bk →
    s u = some v →
    ∃ idx ∈ L, mem (keyBase base n_max + idx) = u.val

private theorem BucketInv.mono_of_mem {U n_max base : ℕ}
    {b : Fin (2 ^ (hashBits U n_max - 1))} {s s' : Dictionary.State U}
    {mem mem' : ℕ → ℕ} {bk : ℕ} {L : List ℕ}
    (hb : BucketInv U n_max base b s mem bk L)
    (hcard : (Dictionary.dom s).card ≤ (Dictionary.dom s').card)
    (hhead : mem' (headBase base + bk) = mem (headBase base + bk))
    (hkey : ∀ j ∈ L, mem' (keyBase base n_max + j) = mem (keyBase base n_max + j))
    (hval : ∀ j ∈ L, mem' (valBase base n_max + j) = mem (valBase base n_max + j))
    (hnext : ∀ j ∈ L, mem' (nextBase base n_max + j) = mem (nextBase base n_max + j))
    (hs : ∀ u : Fin U,
      multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u) = bk → s' u = s u) :
    BucketInv U n_max base b s' mem' bk L :=
  ⟨hhead ▸ (hb.chain.congr_mem hnext).mono_sz hcard, List.map_congr_left hkey ▸ hb.nodup,
    fun j hj => let ⟨u, hk, hbk, hv⟩ := hb.sound j hj
      ⟨u, (hkey j hj).trans hk, hbk, (hs u hbk).trans (hval j hj ▸ hv)⟩,
    fun u v hbk hv => let ⟨j, hj, hk⟩ := hb.complete u v hbk ((hs u hbk).symm.trans hv)
      ⟨j, hj, (hkey j hj).trans hk⟩⟩

theorem BucketInv.congr_mem {U n_max base : ℕ} {b : Fin (2 ^ (hashBits U n_max - 1))}
    {s : Dictionary.State U} {mem mem' : ℕ → ℕ} {bk : ℕ} {L : List ℕ}
    (hb : BucketInv U n_max base b s mem bk L) (hbk : bk < numBuckets n_max)
    (hcard : (Dictionary.dom s).card ≤ n_max)
    (hmem : ∀ a ∈ (Block.mk base (space n_max)).footprint, mem' a = mem a) :
    BucketInv U n_max base b s mem' bk L :=
  hb.mono_of_mem le_rfl (by mem_frame)
    (fun j hj => by have := hb.chain.lt_sz j hj; mem_frame)
    (fun j hj => by have := hb.chain.lt_sz j hj; mem_frame)
    (fun j hj => by have := hb.chain.lt_sz j hj; mem_frame)
    (fun _ _ => rfl)

/-- If `idx₁ ∈ L₁` (in bucket `bk₁`) and `idx₂ ∈ L₂` (in bucket `bk₂`) and `idx₁ = idx₂`, then
`bk₁ = bk₂` and `L₁ = L₂`. -/
theorem BucketInv.eq_of_mem_eq {U n_max base : ℕ} {b : Fin (2 ^ (hashBits U n_max - 1))}
    {s : Dictionary.State U} {mem : ℕ → ℕ} {bk₁ bk₂ idx : ℕ} {L₁ L₂ : List ℕ}
    (hb₁ : BucketInv U n_max base b s mem bk₁ L₁)
    (hb₂ : BucketInv U n_max base b s mem bk₂ L₂)
    (h₁ : idx ∈ L₁) (h₂ : idx ∈ L₂) :
    bk₁ = bk₂ ∧ L₁ = L₂ := by
  obtain ⟨u₁, hk₁, hbk₁, _⟩ := hb₁.sound idx h₁
  obtain ⟨u₂, hk₂, hbk₂, _⟩ := hb₂.sound idx h₂
  obtain rfl : u₁ = u₂ := Fin.ext (hk₁.symm.trans hk₂)
  obtain rfl : bk₁ = bk₂ := hbk₁.symm.trans hbk₂
  exact ⟨rfl, hb₁.chain.unique hb₂.chain⟩

/-- Within a single bucket `bk`, two slots `idx₁, idx₂ ∈ L` have the same stored key if and only if
`idx₁ = idx₂`. -/
theorem BucketInv.idx_eq_of_key_eq {U n_max base : ℕ} {b : Fin (2 ^ (hashBits U n_max - 1))}
    {s : Dictionary.State U} {mem : ℕ → ℕ} {bk idx₁ idx₂ : ℕ} {L : List ℕ}
    (hb : BucketInv U n_max base b s mem bk L)
    (h₁ : idx₁ ∈ L) (h₂ : idx₂ ∈ L)
    (hk : mem (keyBase base n_max + idx₁) = mem (keyBase base n_max + idx₂)) :
    idx₁ = idx₂ :=
  List.inj_on_of_nodup_map hb.nodup h₁ h₂ hk

/-- **Chain length bound**: for any query key `u : Fin U`, the length of the chain `L` in bucket
`bk = multiplyShift w₀ M b (encodeKey u)` is at most `1` plus the number of other keys
`u' ∈ (dom s).erase u` that collide with `u` under `multiplyShift w₀ M b`. -/
theorem BucketInv.length_le {U n_max base : ℕ} {b : Fin (2 ^ (hashBits U n_max - 1))}
    {s : Dictionary.State U} {mem : ℕ → ℕ} {L : List ℕ} (u : Fin U)
    (hb : BucketInv U n_max base b s mem
      (multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u)) L) :
    L.length ≤ 1 + (((Dictionary.dom s).erase u).filter fun u' =>
      multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u') =
        multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u)).card := by
  classical
  let h := fun u' : Fin U => multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u')
  let F := (Dictionary.dom s).filter (h · = h u)
  let F' := ((Dictionary.dom s).erase u).filter (h · = h u)
  have hsub : (L.map fun idx => mem (keyBase base n_max + idx)).toFinset ⊆ F.image Fin.val := by
    intro k hk
    obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    obtain ⟨u', hk', hbk, hv⟩ := hb.sound idx hidx
    exact Finset.mem_image.mpr
      ⟨u', Finset.mem_filter.mpr ⟨Dictionary.mem_dom_iff.mpr ⟨_, hv⟩, hbk⟩, hk'.symm⟩
  have hF_sub : F ⊆ insert u F' := fun u' hu' => by
    obtain ⟨hmem, heq⟩ := Finset.mem_filter.mp hu'
    rcases eq_or_ne u' u with rfl | hne
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne, hmem⟩, heq⟩)
  calc
    L.length = (L.map fun idx => mem (keyBase base n_max + idx)).toFinset.card := by
      rw [List.toFinset_card_of_nodup hb.nodup, List.length_map]
    _ ≤ (F.image Fin.val).card := Finset.card_le_card hsub
    _ ≤ F.card := Finset.card_image_le
    _ ≤ (insert u F').card := Finset.card_le_card hF_sub
    _ ≤ 1 + F'.card := (Finset.card_insert_le u F').trans_eq (Nat.add_comm _ _)

/-- Seed-coupled concrete representation invariant for the chained hash table at `base`. -/
structure Rep (U V n_max w base : ℕ) (b : Fin (2 ^ (hashBits U n_max - 1)))
    (s : Dictionary.State U) (x : Data rHash) : Prop where
  /-- All registers and memory words fit in `w`-bit words. -/
  bounded : x.Bounded w
  /-- Persistent base-address register holds `base`. -/
  reg_base : x.regs baseReg = base
  /-- Header word `base + 0` stores the sampled multiply-shift seed `b.val`. -/
  mem_seed : x.mem base = b.val
  /-- Header word `base + 1` stores `bucketBits n_max`. -/
  mem_M : x.mem (base + 1) = bucketBits n_max
  /-- Header word `base + 2` stores `hashBits U n_max`. -/
  mem_w0 : x.mem (base + 2) = hashBits U n_max
  /-- Header word `base + 3` stores `allocCount = (dom s).card`. -/
  mem_sz : x.mem (base + 3) = (Dictionary.dom s).card
  /-- Current key count is at most `n_max`. -/
  card_le : (Dictionary.dom s).card ≤ n_max
  /-- Every stored value in `s` is strictly less than `V`. -/
  vals_lt : Dictionary.ValuesBounded V s
  /-- Every bucket `bk < numBuckets n_max` satisfies `BucketInv`. -/
  buckets : ∀ bk < numBuckets n_max, ∃ L : List ℕ, BucketInv U n_max base b s x.mem bk L

theorem Rep.unique {U V n_max w base : ℕ} {b : Fin (2 ^ (hashBits U n_max - 1))}
    {s₁ s₂ : Dictionary.State U} {x : Data rHash}
    (hr₁ : Rep U V n_max w base b s₁ x) (hr₂ : Rep U V n_max w base b s₂ x) :
    s₁ = s₂ := by
  funext u
  set bk := multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u)
  obtain ⟨L₁, hb₁⟩ := hr₁.buckets bk (multiplyShift_lt_numBuckets b u)
  obtain ⟨L₂, hb₂⟩ := hr₂.buckets bk (multiplyShift_lt_numBuckets b u)
  obtain rfl : L₁ = L₂ := hb₁.chain.unique hb₂.chain
  have lookup {sa sb : Dictionary.State U} (hba : BucketInv U n_max base b sa x.mem bk L₁)
      (hbb : BucketInv U n_max base b sb x.mem bk L₁) {v : ℕ} (ha : sa u = some v) :
      sb u = some v := by
    obtain ⟨idx, hidx, hk⟩ := hba.complete u v rfl ha
    obtain ⟨u₁, hk₁, _, hs₁⟩ := hba.sound idx hidx
    obtain ⟨u₂, hk₂, _, hs₂⟩ := hbb.sound idx hidx
    rw [Fin.ext (hk₁.symm.trans hk), ha] at hs₁
    exact (Fin.ext (hk₂.symm.trans hk) ▸ hs₂).trans hs₁.symm
  rcases h₁ : s₁ u with _ | v₁
  · rcases h₂ : s₂ u with _ | v₂
    exacts [rfl, absurd (lookup hb₂ hb₁ h₂) (by simp [h₁])]
  · exact (lookup hb₁ hb₂ h₁).symm

theorem Rep.supported {U V n_max w base : ℕ} {b : Fin (2 ^ (hashBits U n_max - 1))}
    {s : Dictionary.State U} {x x' : Data rHash}
    (hreg : ∀ i, inputMask i = false → x'.regs i = x.regs i)
    (hmem : ∀ a ∈ (Block.mk base (space n_max)).footprint, x'.mem a = x.mem a)
    (hbx' : x'.Bounded w) (hr : Rep U V n_max w base b s x) :
    Rep U V n_max w base b s x' :=
  ⟨hbx', by regs_frame, by mem_frame, by mem_frame, by mem_frame, by mem_frame,
    hr.card_le, hr.vals_lt,
    fun bk hbk => let ⟨L, hb⟩ := hr.buckets bk hbk; ⟨L, hb.congr_mem hbk hr.card_le hmem⟩⟩

/-! ## 4. Initialization execution (`allocSpan`, `storeHeader`, `initSetup`) -/

private theorem fits_hashBits {U n_max w : ℕ} (hw : 2 * hashBits U n_max ≤ w) :
    Fits w (hashBits U n_max) :=
  Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right two_pos (by omega))

private theorem fits_bucketBits {U n_max w : ℕ} (hw : 2 * hashBits U n_max ≤ w) :
    Fits w (bucketBits n_max) :=
  (fits_hashBits hw).of_le (bucketBits_le_hashBits U n_max)

private theorem allocSpan_spec {n_max w base : ℕ} (hS : Fits w (base + space n_max))
    {x : Data rHash} (hfr : x.regs frontierReg = base) :
    ∃ x₁, ExecWithin w (allocSpan n_max) x x₁ 3 ∧ x₁.mem = x.mem ∧
      x₁.regs baseReg = base ∧ x₁.regs frontierReg = base + space n_max := by
  unfold allocSpan
  wram_exec [hS.of_le, hfr]
  exact ⟨rfl, by wram_simp, by wram_simp⟩

private theorem storeHeader_spec {U V n_max w base : ℕ}
    (hw : 2 * hashBits U n_max ≤ w) (hS : Fits w (base + space n_max))
    {b : Fin (2 ^ (hashBits U n_max - 1))} {x : Data rHash}
    (hx : x.Bounded w) (hbase : x.regs baseReg = base)
    (hfr : x.regs frontierReg = base + space n_max)
    (hb : x.regs regB = b.val)
    (hz : ∀ a ∈ (Block.mk base (space n_max)).footprint, x.mem a = 0) :
    ∃ y, Exec w (storeHeader U n_max) x y 11 ∧
      y.regs frontierReg = base + space n_max ∧
      Rep U V n_max w base b (Dictionary.empty U) y ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem y.mem := by
  refine WP.Exact.exists_exec (WP.Exact.bounded hx ?_)
  unfold storeHeader
  wram_exec [hS.of_le, fits_bucketBits hw, fits_hashBits hw, hbase, hb]
  intro hy_bdd
  obtain ⟨y, hy, hy_bdd⟩ : ∃ y : Data rHash, y = _ ∧ y.Bounded w := ⟨_, rfl, hy_bdd⟩
  rw [← hy]
  refine ⟨rfl, by regs_frame, ⟨hy_bdd, by regs_frame, by mem_frame, by mem_frame, by mem_frame,
    by rw [Dictionary.card_dom_empty]; mem_frame, by simp, Dictionary.valuesBounded_empty U V,
    fun bk hbk => ⟨[], ?_, List.nodup_nil, (fun _ h => by cases h),
      (fun _ _ _ h => by cases h)⟩⟩, by mem_frame⟩
  have hhead : y.mem (headBase base + bk) = 0 := by mem_frame
  exact hhead ▸ IsChain.nil

private theorem initSetup_spec {U V n_max w base : ℕ}
    (hw : 2 * hashBits U n_max ≤ w) (hS : Fits w (base + space n_max))
    {x₁ : Data rHash} (hx₁ : x₁.Bounded w) (hbase : x₁.regs baseReg = base)
    (hfr : x₁.regs frontierReg = base + space n_max)
    (hz : ∀ a ∈ (Block.mk base (space n_max)).footprint, x₁.mem a = 0) :
    let Seed := Fin (2 ^ (hashBits U n_max - 1))
    let seedLaw := PMF.uniformOfFintype Seed
    ∃ ν₀ : PMF (Seed × Data rHash),
      ExecCodeDist w (initSetup U n_max) x₁ (ν₀.map Prod.snd) 13 ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ 1 * seedLaw θ) ∧
      ∀ p ∈ ν₀.support,
        p.2.regs frontierReg = base + space n_max ∧
        Rep U V n_max w base p.1 (Dictionary.empty U) p.2 ∧
        Modifies (Block.mk base (space n_max)).footprint x₁.mem p.2.mem := by
  classical
  set w₀ := hashBits U n_max
  set Seed := Fin (2 ^ (w₀ - 1))
  set seedLaw := PMF.uniformOfFintype Seed
  let d₁ : Data 5 := x₁.comap hashEmbed
  let x_mid (b : Seed) : Data rHash := (MultiplyShift.initData w₀ d₁ b.val).extend hashEmbed x₁
  have hregB (b : Seed) : (x_mid b).regs regB = b.val := by
    change ((x_mid b).comap hashEmbed).regs MultiplyShift.regB = b.val
    rw [show (x_mid b).comap hashEmbed = _ from Data.comap_extend hashEmbed_injective _ x₁]
    simp [MultiplyShift.initData]
  have hstep2 (b : Seed) : ∃ y, Exec w (storeHeader U n_max) (x_mid b) y 11 ∧
      y.regs frontierReg = base + space n_max ∧ Rep U V n_max w base b (Dictionary.empty U) y ∧
      Modifies (Block.mk base (space n_max)).footprint x₁.mem y.mem := by
    have hbdd : (MultiplyShift.initData w₀ d₁ b.val).Bounded w :=
      ((hx₁.comap hashEmbed).set
        (Fits.mono (Nat.sub_lt (Nat.two_pow_pos _) one_pos) (by omega))).set
        (Fits.mono b.isLt (by omega))
    exact storeHeader_spec hw hS (hbdd.extend hashEmbed_injective hx₁)
      (by regs_frame) (by regs_frame) (hregB b) hz
  let y_init (b : Seed) := Classical.choose (hstep2 b)
  let hys (b : Seed) := Classical.choose_spec (hstep2 b)
  have hinit1 : ExecCodeDist w ((MultiplyShift.initCode w₀).rename hashEmbed)
      x₁ (seedLaw.map x_mid) 2 := by
    refine ((ExecCodeDist.of_execRand (MultiplyShift.initCode_execRand (by omega) d₁)).rename
      hashEmbed_injective (x := x₁)).congr_dist ?_
      (by simp [MultiplyShift.initComp, bind_pure_comp, ProbComp.expect_map, ProbComp.expect_const])
    have heq := (PMF.uniformOfFintype_map_equiv
      (finCongr (Nat.sub_add_cancel (@Nat.one_le_two_pow (w₀ - 1))))).symm
    rw [MultiplyShift.initComp, bind_pure_comp, Functor.map_map, ProbComp.eval_map,
      ProbComp.eval_unifFin, PMF.map_comp, show seedLaw = _ from heq, PMF.map_comp]
    rfl
  let μ₂ (z : Data rHash) : PMF (Data rHash) :=
    if h : z.regs regB < 2 ^ (w₀ - 1) then PMF.pure (y_init ⟨z.regs regB, h⟩) else PMF.pure z
  have hμ₂ (b : Seed) : μ₂ (x_mid b) = PMF.pure (y_init b) := by
    simp [μ₂, hregB b, b.isLt]
  refine ⟨seedLaw.map fun b => (b, y_init b), ?_, fun θ => ?_, fun p hp => ?_⟩
  · refine (hinit1.seq_const (c₂ := storeHeader U n_max) (μ₂ := μ₂) (T₂ := fun _ => 11) (B₂ := 11)
      (fun z hz => by
        obtain ⟨b, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
        exact hμ₂ b ▸ ExecCodeDist.of_exec (hys b).1)
      (fun _ _ => le_rfl)).congr_dist ?_ (by norm_num)
    rw [PMF.bind_map, PMF.map_comp]
    simp only [Function.comp_def, hμ₂]
    rfl
  · rw [PMF.map_comp, show Prod.fst ∘ (fun b : Seed => (b, y_init b)) = id from rfl,
      PMF.map_id, one_mul]
  · obtain ⟨b, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
    exact (hys b).2

/-! ## 5. Deterministic operation execution (`evalBucket`, `findInChain`, `finishOp`, `opCode`) -/

private theorem evalBucket_spec {U V n_max w base : ℕ}
    (hw : 2 * hashBits U n_max ≤ w) (hS : Fits w (base + space n_max))
    {b : Fin (2 ^ (hashBits U n_max - 1))} {s : Dictionary.State U} {x : Data rHash}
    (hr : Rep U V n_max w base b s x) {u : Fin U} (hu : x.regs argU = u.val) :
    let bk := multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u)
    ∃ y, Exec w (evalBucket U n_max) x y 24 ∧
      y.Bounded w ∧
      y.mem = x.mem ∧
      y.regs baseReg = base ∧
      y.regs tagReg = x.regs tagReg ∧
      y.regs argU = u.val ∧
      y.regs argV = x.regs argV ∧
      y.regs regOut = bk ∧
      y.regs zero = 0 ∧
      y.regs one = 1 ∧
      y.regs headBaseReg = headBase base ∧
      y.regs keyBaseReg = keyBase base n_max ∧
      y.regs valBaseReg = valBase base n_max ∧
      y.regs nextBaseReg = nextBase base n_max ∧
      y.regs cur = x.mem (headBase base + bk) ∧
      y.regs found = 0 := by
  intro bk
  have hbk_lt : bk < numBuckets n_max := multiplyShift_lt_numBuckets b u
  have fcur : Fits w (x.mem (base + 4 + bk)) := hr.bounded.2 _
  refine WP.Exact.exists_exec (WP.Exact.bounded hr.bounded ?_)
  unfold evalBucket prepHash loadBucketHead
  wram_exec [hr.reg_base, hr.mem_seed, hu]
  wram_call (MultiplyShift.evalCode_exec (M := bucketBits n_max) (hashBits_pos U n_max) hw)
    canonical [b.isLt, (encodeKey (n_max := n_max) u).isLt]
  refine WP.Exact.name fun x₂ hx₂ => ?_
  have hout2 : x₂.regs regOut = bk := by
    change (x₂.comap hashEmbed).regs MultiplyShift.regOut = bk
    subst hx₂
    rw [Data.comap_extend hashEmbed_injective]
    exact MultiplyShift.evalData_regs_out_eq_multiplyShift _ _ _ b (encodeKey u)
      (by wram_simp) (by wram_simp; rfl)
  have hbase2 : x₂.regs baseReg = base := by regs_frame
  have hmem2 : x₂.mem = x.mem := by subst hx₂; rfl
  wram_exec [hS.of_le, hbase2, hout2, hmem2, fcur]
  intro hy_bdd
  exact ⟨rfl, hy_bdd, by mem_frame, by regs_frame, by regs_frame, by regs_frame, by regs_frame,
    by regs_frame, by wram_simp, by wram_simp, by wram_simp; rfl, by wram_simp; rfl,
    by wram_simp; rfl, by wram_simp; dsimp only [nextBase]; omega,
    by wram_simp; rfl, by wram_simp⟩

/-- One `findInChainBody` iteration at chain index `idx₀` (`cur = idx₀ + 1`) with successor
pointer `ptr'` keeps memory and the frame registers. On a key hit it sets `cur = 0`,
`found = 1` and `matchIdx = idx₀`; otherwise it advances `cur` to `ptr'` and keeps `found`. -/
private theorem findInChainBody_spec {U n_max w base : ℕ} (hS : Fits w (base + space n_max))
    {u : Fin U} {idx₀ ptr' : ℕ} (hidx : idx₀ < n_max) {x : Data rHash}
    (hz : x.regs zero = 0) (ho : x.regs one = 1)
    (hkb : x.regs keyBaseReg = keyBase base n_max)
    (hxb : x.regs nextBaseReg = nextBase base n_max)
    (hu : x.regs argU = u.val) (hcur : x.regs cur = idx₀ + 1)
    (hnext : x.mem (nextBase base n_max + idx₀) = ptr') :
    ∃ x₁, Exec w findInChainBody x x₁ 7 ∧
      x₁.mem = x.mem ∧
      x₁.regs baseReg = x.regs baseReg ∧
      x₁.regs tagReg = x.regs tagReg ∧
      x₁.regs argU = u.val ∧
      x₁.regs argV = x.regs argV ∧
      x₁.regs regOut = x.regs regOut ∧
      x₁.regs zero = 0 ∧
      x₁.regs one = 1 ∧
      x₁.regs headBaseReg = x.regs headBaseReg ∧
      x₁.regs keyBaseReg = keyBase base n_max ∧
      x₁.regs valBaseReg = x.regs valBaseReg ∧
      x₁.regs nextBaseReg = nextBase base n_max ∧
      (x.mem (keyBase base n_max + idx₀) = u.val →
        x₁.regs cur = 0 ∧ x₁.regs found = 1 ∧ x₁.regs matchIdx = idx₀) ∧
      (x.mem (keyBase base n_max + idx₀) ≠ u.val →
        x₁.regs cur = ptr' ∧ x₁.regs found = x.regs found) := by
  refine WP.Exact.exists_exec ?_
  unfold findInChainBody
  wram_exec [hS.of_le, hcur, ho, hz, hkb, hxb, hu, hnext]
  · exact ⟨rfl, by regs_frame, by regs_frame, by regs_frame, by regs_frame, by regs_frame,
      by regs_frame, by regs_frame, by regs_frame, by regs_frame, by regs_frame, by regs_frame,
      fun _ => ⟨by wram_simp, by wram_simp, by wram_simp⟩, fun h => absurd hc h⟩
  · exact ⟨rfl, by regs_frame, by regs_frame, by regs_frame, by regs_frame, by regs_frame,
      by regs_frame, by regs_frame, by regs_frame, by regs_frame, by regs_frame, by regs_frame,
      fun h => absurd h hc, fun _ => ⟨by wram_simp, by regs_frame⟩⟩

private theorem findInChain_spec {U n_max w base sz : ℕ}
    (hS : Fits w (base + space n_max)) (hsz : sz ≤ n_max)
    {mem : ℕ → ℕ} {u : Fin U} {ptr : ℕ} {L : List ℕ} {x : Data rHash}
    (hc : IsChain mem (nextBase base n_max) sz ptr L)
    (hmem : x.mem = mem)
    (hx : x.Bounded w)
    (hz : x.regs zero = 0) (ho : x.regs one = 1)
    (hkb : x.regs keyBaseReg = keyBase base n_max)
    (hxb : x.regs nextBaseReg = nextBase base n_max)
    (hu : x.regs argU = u.val)
    (hcur : x.regs cur = ptr) :
    ∃ y, ExecWithin w findInChain x y (9 * L.length + 2) ∧
      y.Bounded w ∧
      y.mem = mem ∧
      y.regs baseReg = x.regs baseReg ∧
      y.regs tagReg = x.regs tagReg ∧
      y.regs argU = u.val ∧
      y.regs argV = x.regs argV ∧
      y.regs regOut = x.regs regOut ∧
      y.regs zero = 0 ∧
      y.regs one = 1 ∧
      y.regs headBaseReg = x.regs headBaseReg ∧
      y.regs keyBaseReg = keyBase base n_max ∧
      y.regs valBaseReg = x.regs valBaseReg ∧
      y.regs nextBaseReg = nextBase base n_max ∧
      ((∃ i ∈ L, mem (keyBase base n_max + i) = u.val ∧ y.regs found = 1 ∧ y.regs matchIdx = i) ∨
        ((∀ i ∈ L, mem (keyBase base n_max + i) ≠ u.val) ∧ y.regs found = x.regs found)) := by
  induction hc generalizing x with
  | nil =>
    exact ⟨x, (Exec.loop_exit (by simp [Cond.Holds, hz, hcur])).within, hx, hmem, rfl, rfl,
      hu, rfl, rfl, hz, ho, rfl, hkb, rfl, hxb, Or.inr ⟨(fun _ h => by cases h), rfl⟩⟩
  | @cons idx₀ ptr' L' hidx hnext hc' ih =>
    obtain ⟨x₁, he1, hm1, hbase1, htag1, hargU1, hargV1, hout1, hz1, ho1,
        hhb1, hkb1, hvb1, hxb1, hhitR, hmissR⟩ :=
      findInChainBody_spec hS (by omega) hz ho hkb hxb hu hcur (hmem ▸ hnext)
    by_cases hhit : mem (keyBase base n_max + idx₀) = u.val
    · obtain ⟨hcur1, hfnd1, hmidx1⟩ := hhitR (hmem ▸ hhit)
      have he_tot : Exec w findInChain x x₁ (7 + 2 + 2) := Exec.loop_iter
        (by simp [Cond.Holds, hz, hcur]) he1 (Exec.loop_exit (by simp [Cond.Holds, hz1, hcur1]))
      exact ⟨x₁, he_tot.within.mono (by simp), he_tot.within.bounded hx,
        hm1.trans hmem, hbase1, htag1, hargU1, hargV1, hout1, hz1, ho1, hhb1, hkb1, hvb1, hxb1,
        Or.inl ⟨idx₀, List.mem_cons_self, hhit, hfnd1, hmidx1⟩⟩
    · obtain ⟨hcur1, hfnd1⟩ := hmissR (hmem ▸ hhit)
      obtain ⟨y, ⟨m₂, hm₂_le, he2⟩, hy_bdd, hmy, hbase2, htag2, hargU2, hargV2, hout2,
          hz2, ho2, hhb2, hkb2, hvb2, hxb2, hres⟩ :=
        ih (hm1.trans hmem) (he1.within.bounded hx) hz1 ho1 hkb1 hxb1 hargU1 hcur1
      refine ⟨y, ⟨7 + m₂ + 2, by simp; omega,
          Exec.loop_iter (by simp [Cond.Holds, hz, hcur]) he1 he2⟩, hy_bdd, hmy,
        hbase2.trans hbase1, htag2.trans htag1, hargU2, hargV2.trans hargV1,
        hout2.trans hout1, hz2, ho2, hhb2.trans hhb1, hkb2, hvb2.trans hvb1, hxb2,
        hres.imp (fun ⟨i, hi, h⟩ => ⟨i, List.mem_cons_of_mem _ hi, h⟩)
          fun ⟨hm, hf⟩ => ⟨fun i hi => (List.mem_cons.mp hi).elim (· ▸ hhit) (hm i),
            hf.trans hfnd1⟩⟩

private theorem Rep.of_mem_eq {U V n_max w base : ℕ} {b : Fin (2 ^ (hashBits U n_max - 1))}
    {s : Dictionary.State U} {x z : Data rHash}
    (hr : Rep U V n_max w base b s x) (hz : z.Bounded w)
    (hbase : z.regs baseReg = base) (hmem : z.mem = x.mem) :
    Rep U V n_max w base b s z :=
  hr.supported (fun i hi => by
    obtain rfl : i = baseReg := Decidable.of_not_not (of_decide_eq_false hi)
    exact hbase.trans hr.reg_base.symm) (fun a _ => congrFun hmem a) hz

private theorem finishQuery_spec {U V n_max w base : ℕ}
    (hS : Fits w (base + space n_max)) (hV : Fits w V)
    {b : Fin (2 ^ (hashBits U n_max - 1))} {s : Dictionary.State U} {x y : Data rHash}
    (hr : Rep U V n_max w base b s x)
    {u : Fin U} {L : List ℕ}
    (hbL : BucketInv U n_max base b s x.mem
      (multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u)) L)
    (hy_bdd : y.Bounded w) (hmy : y.mem = x.mem)
    (hbase : y.regs baseReg = base) (htag : y.regs tagReg = 0)
    (hz : y.regs zero = 0) (ho : y.regs one = 1)
    (hvb : y.regs valBaseReg = valBase base n_max)
    (hres : (∃ i ∈ L, x.mem (keyBase base n_max + i) = u.val ∧
        y.regs found = 1 ∧ y.regs matchIdx = i) ∨
      ((∀ i ∈ L, x.mem (keyBase base n_max + i) ≠ u.val) ∧ y.regs found = 0)) :
    ∃ z, ExecWithin w finishOp y z 20 ∧
      Rep U V n_max w base b s z ∧
      @decode U V n_max (.query u) z.regs = some (s u) ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem z.mem := by
  refine WP.exists_execWithin (WP.bounded hy_bdd ?_)
  unfold finishOp finishQuery
  rcases hres with ⟨i, hi, hki, hyf, hym⟩ | ⟨hmiss, hyf⟩
  · have hi_lt : i < n_max := (hbL.chain.lt_sz i hi).trans_le hr.card_le
    obtain ⟨u', hku', _, hsu'⟩ := hbL.sound i hi
    obtain rfl : u = u' := Fin.ext (hki.symm.trans hku')
    have fv1 : Fits w (y.mem (valBase base n_max + i) + 1) :=
      hmy ▸ hV.of_le (hr.vals_lt u _ hsu')
    wram_exec [hS.of_le, htag, hz, ho, hyf, hvb, hym, fv1]
    intro hz_bdd
    exact ⟨by omega, hr.of_mem_eq hz_bdd (by regs_frame) hmy,
      by wram_simp; simp [decode, hmy, hsu', Dictionary.spec], by mem_frame⟩
  · have hsu : s u = none := Option.eq_none_iff_forall_not_mem.mpr fun v h =>
      (hbL.complete u v rfl h).elim fun i ⟨hi, hki⟩ => hmiss i hi hki
    wram_exec [htag, hz, hyf]
    intro hz_bdd
    exact ⟨by omega, hr.of_mem_eq hz_bdd (by regs_frame) hmy,
      by wram_simp; simp [decode, hsu, Dictionary.spec], by mem_frame⟩

private theorem finishInsertHit_spec {U V n_max w base : ℕ}
    (hS : Fits w (base + space n_max))
    {b : Fin (2 ^ (hashBits U n_max - 1))} {s : Dictionary.State U} {x y : Data rHash}
    (hr : Rep U V n_max w base b s x)
    {u : Fin U} {v : ℕ} (hv : (Dictionary.spec U V n_max).valid s (.insert u v))
    {L : List ℕ}
    (hbL : BucketInv U n_max base b s x.mem
      (multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u)) L)
    {i : ℕ} (hi : i ∈ L) (hki : x.mem (keyBase base n_max + i) = u.val)
    (hy_bdd : y.Bounded w) (hmy : y.mem = x.mem)
    (hbase : y.regs baseReg = base) (htag : y.regs tagReg ≠ 0) (hargV : y.regs argV = v)
    (hz : y.regs zero = 0) (hvb : y.regs valBaseReg = valBase base n_max)
    (hyf : y.regs found = 1) (hym : y.regs matchIdx = i) :
    ∃ z, ExecWithin w finishOp y z 20 ∧
      Rep U V n_max w base b (Function.update s u (some v)) z ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem z.mem := by
  let s' := Function.update s u (some v)
  have hsz_le : (Dictionary.dom s).card ≤ n_max := hr.card_le
  have hi_lt : i < (Dictionary.dom s).card := hbL.chain.lt_sz i hi
  obtain ⟨u₀, hku₀, _, hsu₀⟩ := hbL.sound i hi
  obtain rfl : u = u₀ := Fin.ext (hki.symm.trans hku₀)
  have hcard_eq : (Dictionary.dom s').card = (Dictionary.dom s).card :=
    Dictionary.card_dom_insert_eq_of_isSome (by simp [hsu₀]) v
  refine WP.exists_execWithin (WP.bounded hy_bdd ?_)
  unfold finishOp finishInsert finishInsertHit
  wram_exec [hS.of_le, htag, hz, hyf, hvb, hym, hargV]
  intro hz_bdd
  obtain ⟨z, hz_eq, hz_bdd⟩ : ∃ z : Data rHash, z = _ ∧ z.Bounded w := ⟨_, rfl, hz_bdd⟩
  rw [← hz_eq]
  refine ⟨by omega, ⟨hz_bdd, by regs_frame, by mem_frame, by mem_frame, by mem_frame,
      by rw [hcard_eq]; mem_frame, hcard_eq ▸ hsz_le,
      Dictionary.valuesBounded_step_of_valid hr.vals_lt hv, fun bk' hbk' => ?_⟩, by mem_frame⟩
  obtain ⟨L', hbL'⟩ := hr.buckets bk' hbk'
  have hhead : z.mem (headBase base + bk') = x.mem (headBase base + bk') := by mem_frame
  have hkey (j : ℕ) (hj : j ∈ L') :
      z.mem (keyBase base n_max + j) = x.mem (keyBase base n_max + j) :=
    by have := hbL'.chain.lt_sz j hj; mem_frame
  refine ⟨L', hcard_eq ▸ hhead ▸ hbL'.chain.congr_mem (fun j hj => by
      have := hbL'.chain.lt_sz j hj; mem_frame),
    List.map_congr_left hkey ▸ hbL'.nodup, fun j hj => ?_, fun u' v' hbk_u' hsv' => ?_⟩
  · obtain ⟨u', hku', hbk_u', hsu'⟩ := hbL'.sound j hj
    refine ⟨u', (hkey j hj).trans hku', hbk_u', ?_⟩
    rcases eq_or_ne j i with rfl | hji
    · obtain rfl : u' = u := Fin.ext (hku'.symm.trans hki)
      have hval_eq : z.mem (valBase base n_max + j) = v := by mem_frame
      simp [hval_eq]
    · have hu'_ne : u' ≠ u := fun h => by
        subst h; subst hbk_u'
        exact hji (hbL.idx_eq_of_key_eq (hbL'.chain.unique hbL.chain ▸ hj) hi (hku'.trans hki.symm))
      have hval_ne : z.mem (valBase base n_max + j) = x.mem (valBase base n_max + j) := by
        have := hbL'.chain.lt_sz j hj; mem_frame
      rw [Function.update_of_ne hu'_ne, hval_ne]; exact hsu'
  · rcases eq_or_ne u' u with rfl | hne
    · subst hbk_u'
      obtain rfl := hbL.chain.unique hbL'.chain
      exact ⟨i, hi, (hkey i hi).trans hki⟩
    · obtain ⟨j, hj, hkj⟩ := hbL'.complete u' v' hbk_u' (by rwa [Function.update_of_ne hne] at hsv')
      exact ⟨j, hj, (hkey j hj).trans hkj⟩

private theorem finishInsertMiss_spec {U V n_max w base : ℕ}
    (hS : Fits w (base + space n_max))
    {b : Fin (2 ^ (hashBits U n_max - 1))} {s : Dictionary.State U} {x y : Data rHash}
    (hr : Rep U V n_max w base b s x)
    {u : Fin U} {v : ℕ} {bk : ℕ}
    (hbk_def : bk = multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u))
    (hv : (Dictionary.spec U V n_max).valid s (.insert u v))
    {L : List ℕ}
    (hbL : BucketInv U n_max base b s x.mem bk L)
    (hmiss : ∀ i ∈ L, x.mem (keyBase base n_max + i) ≠ u.val)
    (hy_bdd : y.Bounded w) (hmy : y.mem = x.mem)
    (hbase : y.regs baseReg = base) (htag : y.regs tagReg ≠ 0)
    (hargU : y.regs argU = u.val) (hargV : y.regs argV = v)
    (hout : y.regs regOut = bk)
    (hz : y.regs zero = 0) (ho : y.regs one = 1)
    (hhb : y.regs headBaseReg = headBase base)
    (hkb : y.regs keyBaseReg = keyBase base n_max)
    (hvb : y.regs valBaseReg = valBase base n_max)
    (hxb : y.regs nextBaseReg = nextBase base n_max)
    (hyf : y.regs found = 0) :
    ∃ z, ExecWithin w finishOp y z 20 ∧
      Rep U V n_max w base b (Function.update s u (some v)) z ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem z.mem := by
  let s' := Function.update s u (some v)
  have hbk_lt : bk < numBuckets n_max := hbk_def ▸ multiplyShift_lt_numBuckets b u
  set sz := (Dictionary.dom s).card
  have hsu : s u = none := Option.eq_none_iff_forall_not_mem.mpr fun v₀ h =>
    (hbL.complete u v₀ hbk_def.symm h).elim fun i ⟨hi, hki⟩ => hmiss i hi hki
  have hsz_lt : sz < n_max := hv.1.resolve_right (by simp [hsu])
  have hcard_eq : (Dictionary.dom s').card = sz + 1 :=
    Dictionary.card_dom_insert_eq_of_eq_none hsu v
  have hmsz : y.mem (base + 3) = sz := hmy ▸ hr.mem_sz
  refine WP.exists_execWithin (WP.bounded hy_bdd ?_)
  unfold finishOp finishInsert finishInsertMiss
  wram_exec [hS.of_le, hbase, htag, hargU, hargV, hout, hz, ho, hhb, hkb, hvb, hxb, hyf, hmsz]
  intro hz_bdd
  obtain ⟨z, hz_eq, hz_bdd⟩ : ∃ z : Data rHash, z = _ ∧ z.Bounded w := ⟨_, rfl, hz_bdd⟩
  rw [← hz_eq]
  have hz_slot_lt : ∀ j < sz,
      z.mem (keyBase base n_max + j) = x.mem (keyBase base n_max + j) ∧
      z.mem (valBase base n_max + j) = x.mem (valBase base n_max + j) ∧
      z.mem (nextBase base n_max + j) = x.mem (nextBase base n_max + j) := by mem_frame
  have hz_sz : z.mem (keyBase base n_max + sz) = u.val ∧ z.mem (valBase base n_max + sz) = v ∧
      z.mem (nextBase base n_max + sz) = x.mem (headBase base + bk) ∧
      z.mem (headBase base + bk) = sz + 1 := by mem_frame
  refine ⟨by omega, ⟨hz_bdd, by regs_frame, by mem_frame, by mem_frame, by mem_frame,
      by rw [hcard_eq]; mem_frame, by rw [hcard_eq]; omega,
      Dictionary.valuesBounded_step_of_valid hr.vals_lt hv, fun bk' hbk' => ?_⟩, by mem_frame⟩
  rcases eq_or_ne bk bk' with rfl | hne
  · have hmap := List.map_congr_left fun j hj => (hz_slot_lt j (hbL.chain.lt_sz j hj)).1
    refine ⟨sz :: L, hz_sz.2.2.2 ▸ .cons (by rw [hcard_eq]; omega) hz_sz.2.2.1
        ((hbL.chain.congr_mem fun j hj => (hz_slot_lt j (hbL.chain.lt_sz j hj)).2.2).mono_sz
          (by rw [hcard_eq]; omega)),
      by rw [List.map_cons, hz_sz.1, hmap, List.nodup_cons]
         exact ⟨fun hm => let ⟨j, hj, hkj⟩ := List.mem_map.mp hm; hmiss j hj hkj, hbL.nodup⟩,
      fun j hj => ?_, fun u' v' hbk_u' hsv' => ?_⟩
    · rcases List.mem_cons.mp hj with rfl | hj'
      · exact ⟨u, hz_sz.1, hbk_def.symm, by simp [hz_sz.2.1]⟩
      · have hj_lt := hbL.chain.lt_sz j hj'
        obtain ⟨u', hku', hbk_u', hsu'⟩ := hbL.sound j hj'
        refine ⟨u', (hz_slot_lt j hj_lt).1.trans hku', hbk_u', ?_⟩
        rw [Function.update_of_ne (by rintro rfl; exact hmiss j hj' hku'),
          (hz_slot_lt j hj_lt).2.1]
        exact hsu'
    · rcases eq_or_ne u' u with rfl | hu'
      · exact ⟨sz, List.mem_cons_self, hz_sz.1⟩
      · obtain ⟨j, hj, hkj⟩ := hbL.complete u' v' hbk_u'
          (by rwa [Function.update_of_ne hu'] at hsv')
        exact ⟨j, List.mem_cons_of_mem _ hj, (hz_slot_lt j (hbL.chain.lt_sz j hj)).1.trans hkj⟩
  · obtain ⟨L', hbL'⟩ := hr.buckets bk' hbk'
    exact ⟨L', hbL'.mono_of_mem (by rw [hcard_eq]; omega) (by mem_frame)
      (fun j hj => (hz_slot_lt j (hbL'.chain.lt_sz j hj)).1)
      (fun j hj => (hz_slot_lt j (hbL'.chain.lt_sz j hj)).2.1)
      (fun j hj => (hz_slot_lt j (hbL'.chain.lt_sz j hj)).2.2)
      fun u' hbk_u' =>
        Function.update_of_ne (by rintro rfl; exact hne (hbk_def.trans hbk_u')) _ _⟩

/-- Number of keys `u' ∈ (dom s).erase u` that collide with `u` under `multiplyShift w₀ M b`. -/
def collCount {U : ℕ} (n_max : ℕ) (s : Dictionary.State U) (u : Fin U)
    (b : Fin (2 ^ (hashBits U n_max - 1))) : ℕ :=
  (((Dictionary.dom s).erase u).filter fun u' =>
    multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u') =
      multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u)).card

/-- Key queried or inserted by a dictionary operation `o : Dictionary.Op U`. -/
def opKey {U : ℕ} : Dictionary.Op U → Fin U
  | .query u => u
  | .insert u _ => u

/-- Deterministic execution of `opCode U n_max` for a fixed seed `b`: executes in at most
`55 + 9 * collCount n_max s (opKey o) b` instructions, preserves `Rep`, decodes the abstract
result, and modifies memory only within `[base, base + space n_max)`. -/
theorem opCode_spec {U V n_max w base : ℕ}
    (hw : 2 * hashBits U n_max ≤ w) (hS : Fits w (base + space n_max)) (hV : Fits w V)
    {b : Fin (2 ^ (hashBits U n_max - 1))} {s : Dictionary.State U} {x : Data rHash}
    (hr : Rep U V n_max w base b s x) (o : Dictionary.Op U)
    (hv : (Dictionary.spec U V n_max).valid s o)
    (harg : argMatch o x.regs) :
    ∃ z, ExecWithin w (opCode U n_max) x z (55 + 9 * collCount n_max s (opKey o) b) ∧
      @decode U V n_max o z.regs = some ((Dictionary.spec U V n_max).stepFn s o).2 ∧
      Rep U V n_max w base b ((Dictionary.spec U V n_max).stepFn s o).1 z ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem z.mem := by
  let u := opKey o
  have hu_reg : x.regs argU = u.val := by
    cases o with | query _ => exact harg.2 | insert _ _ => exact harg.2.1
  obtain ⟨L, hbL⟩ := hr.buckets _ (multiplyShift_lt_numBuckets b u)
  have hL_le : L.length ≤ 1 + collCount n_max s u b := hbL.length_le u
  obtain ⟨x₁, he1, hx₁_bdd, hmx₁, hbase1, htag1, hargU1, hargV1, hout1,
      hz1, ho1, hhb1, hkb1, hvb1, hxb1, hcur1, hfnd1⟩ := evalBucket_spec hw hS hr hu_reg
  obtain ⟨y, he2, hy_bdd, hmy, hbase2, htag2, hargU2, hargV2, hout2,
      hz2, ho2, hhb2, hkb2, hvb2, hxb2, hres⟩ :=
    findInChain_spec hS hr.card_le hbL.chain hmx₁ hx₁_bdd hz1 ho1 hkb1 hxb1 hargU1 hcur1
  have hres' :
      (∃ i ∈ L, x.mem (keyBase base n_max + i) = u.val ∧ y.regs found = 1 ∧ y.regs matchIdx = i) ∨
        ((∀ i ∈ L, x.mem (keyBase base n_max + i) ≠ u.val) ∧ y.regs found = 0) :=
    hres.imp_right fun ⟨hm, hf⟩ => ⟨hm, hf.trans hfnd1⟩
  have liftExec {z} (he3 : ExecWithin w finishOp y z 20) :
      ExecWithin w (opCode U n_max) x z (55 + 9 * collCount n_max s u b) :=
    (he1.within.seq (he2.seq he3)).mono (by omega)
  cases o with
  | query u₀ =>
    obtain ⟨z, he3, hrep_z, hdec_z, hmod_z⟩ := finishQuery_spec hS hV hr hbL hy_bdd hmy
      (hbase2.trans hbase1) (htag2.trans (htag1.trans harg.1)) hz2 ho2 (hvb2.trans hvb1) hres'
    exact ⟨z, liftExec he3, hdec_z, hrep_z, hmod_z⟩
  | insert u₀ v =>
    have htag_y : y.regs tagReg ≠ 0 := by rw [htag2, htag1]; exact harg.1
    have hargV_y := hargV2.trans (hargV1.trans harg.2.2)
    rcases hres' with ⟨i, hi, hki, hyf, hym⟩ | ⟨hmiss, hyf⟩
    · obtain ⟨z, he3, hrep_z, hmod_z⟩ := finishInsertHit_spec hS hr hv hbL hi hki hy_bdd hmy
        (hbase2.trans hbase1) htag_y hargV_y hz2 (hvb2.trans hvb1) hyf hym
      exact ⟨z, liftExec he3, rfl, hrep_z, hmod_z⟩
    · obtain ⟨z, he3, hrep_z, hmod_z⟩ := finishInsertMiss_spec hS hr rfl hv hbL hmiss hy_bdd hmy
        (hbase2.trans hbase1) htag_y hargU2 hargV_y (hout2.trans hout1) hz2 ho2
        (hhb2.trans hhb1) hkb2 (hvb2.trans hvb1) hxb2 hyf
      exact ⟨z, liftExec he3, rfl, hrep_z, hmod_z⟩

/-! ## 6. Expected collision bounds and `Randomized.StateTransitionImpl` certificate -/

/-- By linearity of expectation and `(2 / 2 ^ M)`-universality of multiply-shift hashing
(`isUniversalHash_multiplyShift`), the expected number of keys in `(dom s).erase u` colliding with
`u` under a uniform seed `b ∈ Fin (2 ^ (hashBits U n_max - 1))` is at most
`((dom s).erase u).card * (2 / 2 ^ bucketBits n_max)`. -/
theorem expect_collCount_le_card_mul (U n_max : ℕ) (s : Dictionary.State U) (u : Fin U) :
    let Seed := Fin (2 ^ (hashBits U n_max - 1))
    let seedLaw := PMF.uniformOfFintype Seed
    (∑' b : Seed, seedLaw b * (collCount n_max s u b : ℝ≥0∞)) ≤
      (((Dictionary.dom s).erase u).card : ℝ≥0∞) * (2 / 2 ^ bucketBits n_max) := by
  classical
  let w₀ := hashBits U n_max; let M := bucketBits n_max
  let seedLaw := PMF.uniformOfFintype (Fin (2 ^ (w₀ - 1)))
  let h := fun b u' => multiplyShift w₀ M b (encodeKey (n_max := n_max) u')
  have huniv : IsUniversalHash seedLaw h (2 / 2 ^ M) :=
    (isUniversalHash_multiplyShift (hashBits_pos U n_max)
      (bucketBits_le_hashBits U n_max)).precompose (encodeKey_injective U n_max)
  calc
    (∑' b, seedLaw b * (collCount n_max s u b : ℝ≥0∞))
      = ∑ b, ∑ u' ∈ (Dictionary.dom s).erase u,
          {b' | h b' u' = h b' u}.indicator seedLaw b := by
        rw [tsum_fintype]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [collCount, Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun u' _ => ?_
        split_ifs with he
        · rw [Set.indicator_of_mem he, Nat.cast_one, mul_one]
        · rw [Set.indicator_of_notMem he, Nat.cast_zero, mul_zero]
    _ = ∑ u' ∈ (Dictionary.dom s).erase u, seedLaw.toOuterMeasure {b' | h b' u' = h b' u} := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun u' _ => by rw [PMF.toOuterMeasure_apply, tsum_fintype]
    _ ≤ (((Dictionary.dom s).erase u).card : ℝ≥0∞) * (2 / 2 ^ M) :=
        (Finset.sum_le_sum fun u' hu' => huniv u' u (Finset.mem_erase.mp hu').1).trans_eq
          (by rw [Finset.sum_const, nsmul_eq_mul])

/-- When `(dom s).card ≤ n_max`, the expected collision count is at most `2`. -/
theorem expect_collCount_le_two {U n_max : ℕ} {s : Dictionary.State U}
    (hcard : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    let Seed := Fin (2 ^ (hashBits U n_max - 1))
    let seedLaw := PMF.uniformOfFintype Seed
    (∑' b : Seed, seedLaw b * (collCount n_max s u b : ℝ≥0∞)) ≤ 2 := by
  have hcast : (((Dictionary.dom s).erase u).card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ bucketBits n_max := by
    exact_mod_cast (Finset.card_erase_le.trans hcard).trans (le_numBuckets n_max)
  calc _ ≤ _ := expect_collCount_le_card_mul U n_max s u
    _ ≤ (2 : ℝ≥0∞) ^ bucketBits n_max * (2 / 2 ^ bucketBits n_max) := by gcongr
    _ = 2 := by
      rw [div_eq_mul_inv, mul_comm (2 : ℝ≥0∞), ← mul_assoc,
        ENNReal.mul_inv_cancel (by positivity) (ENNReal.pow_ne_top (by simp)), one_mul]

/-- Worst-case expected instruction charge per dictionary operation (`55 + 9 * 2 = 73`). -/
def chargeVal : ℕ := 73

/-- Constant `O(1)` expected instruction charge for `Dictionary.spec U V n_max`. -/
def charge (U V n_max : ℕ) :
    (Dictionary.spec U V n_max).State → (Dictionary.spec U V n_max).Op → ℕ :=
  fun _ _ => chargeVal

/-- **Chained hash table `Randomized.StateTransitionImpl` certificate over `Basis.exact`.**
Realizes `Dictionary.spec U V n_max` in `space n_max = 4 + 2 ^ M + 3 * n_max = O(n_max)` words of
memory, `O(1)` (`16`-instruction) initialization on zeroed memory (`O(n_max)` via `initClear` on
dirty memory), and `chargeVal = 73 = O(1)` worst-case expected instructions per `query` or `insert`
operation with zero potential (`potential = 0`). -/
noncomputable def impl (U V n_max w base : ℕ)
    (hw : 2 * hashBits U n_max ≤ w)
    (hS : Fits w (base + space n_max))
    (hV : Fits w V) :
    Randomized.StateTransitionImpl (subroutineCode U n_max) (Dictionary.spec U V n_max)
      w base Fin.elim0 (Dictionary.empty U) :=
  Randomized.StateTransitionImpl.ofFn
    (Seed := Fin (2 ^ (hashBits U n_max - 1)))
    (seedLaw := PMF.uniformOfFintype (Fin (2 ^ (hashBits U n_max - 1))))
    (seedSlack := 1)
    (space := space n_max)
    (spanTime := 3)
    (setupTime := 13)
    (initPotential := 0)
    (charge := charge U V n_max)
    (rep := Rep U V n_max w base)
    (potential := fun _ _ => 0)
    (encode := encode)
    (argMatch := argMatch)
    (decode := decode)
    (bounded := fun hr => hr.bounded)
    (arguments_fit := fun o hv i _ => arguments_fit hw hS hV o hv i)
    (encode_matches := encode_matches)
    (rep_supported := fun hreg hmem hbx hr => hr.supported hreg hmem hbx)
    (potential_supported := fun _ _ _ => rfl)
    (clear_nodup := by dsimp [subroutineCode]; decide)
    (params_not_clear := fun j => Fin.elim0 j)
    (incCur_eval := fun {x} hone hfit => by
      change Data.put w x regT1 (x.regs regT1 + x.regs one) =
        some (x.set (subroutineCode U n_max).curReg (x.regs (subroutineCode U n_max).curReg + 1))
      change x.regs one = 1 at hone
      rw [hone]
      exact Data.put_of_fits hfit)
    (span_exec := fun {x} _ hfr _ => by
      obtain ⟨x₁, he, hm, hb, hf⟩ := allocSpan_spec hS hfr
      exact ⟨x₁, he, hm, hb, hf, fun j => Fin.elim0 j⟩)
    (setup_exec := fun {x₁} hx₁ hbase hfr _ hz => by
      obtain ⟨ν₀, he, hseed, hsupp⟩ := initSetup_spec (V := V) hw hS hx₁ hbase hfr hz
      exact ⟨ν₀, he, hseed, fun p hp =>
        ⟨(hsupp p hp).1, (hsupp p hp).2.1, le_rfl, (hsupp p hp).2.2⟩⟩)
    (step_exec := fun {s} o ν hv hseed hsupp => by
      classical
      let seedLaw := PMF.uniformOfFintype (Fin (2 ^ (hashBits U n_max - 1)))
      have hstep_ex : ∀ p : Fin (2 ^ (hashBits U n_max - 1)) × Data rHash,
          ∃ z : Data rHash, p ∈ ν.support →
            ExecWithin w (opCode U n_max) p.2 z (55 + 9 * collCount n_max s (opKey o) p.1) ∧
            @decode U V n_max o z.regs = some ((Dictionary.spec U V n_max).stepFn s o).2 ∧
            Rep U V n_max w base p.1 ((Dictionary.spec U V n_max).stepFn s o).1 z ∧
            Modifies (Block.mk base (space n_max)).footprint p.2.mem z.mem := fun p =>
        if hp : p ∈ ν.support then
          let ⟨hr, harg⟩ := hsupp p hp
          let ⟨z, h⟩ := opCode_spec hw hS hV hr o hv harg
          ⟨z, fun _ => h⟩
        else ⟨p.2, fun h => absurd h hp⟩
      choose z_of hz_spec using hstep_ex
      refine ⟨fun p => PMF.pure (p.1, z_of p),
        fun p => ((55 + 9 * collCount n_max s (opKey o) p.1 : ℕ) : ℝ≥0∞), ?_, ?_, ?_⟩
      · intro p hp
        obtain ⟨he, hdec, hrep, hmod⟩ := hz_spec p hp
        exact ⟨PMF.pure_map Prod.snd _ ▸ ExecCodeDist.of_execWithin he, fun q hq => by
          obtain rfl := (PMF.mem_support_pure_iff _ _).mp hq
          exact ⟨hdec, hrep, hmod⟩⟩
      · intro θ'
        have hmap : (ν.bind fun p => PMF.pure (p.1, z_of p)).map Prod.fst = ν.map Prod.fst := by
          rw [PMF.map_bind]; simp only [PMF.pure_map]; rfl
        exact hmap ▸ hseed θ'
      · obtain ⟨p₀, hp₀⟩ := ν.support_nonempty
        simp only [Nat.cast_zero, mul_zero, tsum_zero, add_zero, Nat.cast_add, Nat.cast_mul,
          Nat.cast_ofNat]
        calc
          (∑' p, ν p * (55 + 9 * (collCount n_max s (opKey o) p.1 : ℝ≥0∞)))
            = 55 + 9 * ∑' p, ν p * (collCount n_max s (opKey o) p.1 : ℝ≥0∞) := by
              simp_rw [mul_add, mul_left_comm _ (9 : ℝ≥0∞)]
              rw [tsum_add, ENNReal.tsum_mul_right, ν.tsum_coe, one_mul, ENNReal.tsum_mul_left]
          _ = 55 + 9 * ∑' b, (ν.map Prod.fst) b * (collCount n_max s (opKey o) b : ℝ≥0∞) := by
              rw [Cslib.Probability.PMF.tsum_map_mul]
          _ ≤ 55 + 9 * ∑' b, seedLaw b * (collCount n_max s (opKey o) b : ℝ≥0∞) := by
              gcongr with b; exact (hseed b).trans_eq (one_mul _)
          _ ≤ 55 + 9 * (2 : ℝ≥0∞) := by
              gcongr; exact expect_collCount_le_two (hsupp p₀ hp₀).1.card_le (opKey o)
          _ = (charge U V n_max s o : ℝ≥0∞) := by dsimp [charge, chargeVal]; norm_num)

/-- **Chained hash table `Randomized.StateTransitionImpl` certificate over `Basis.standard`.**
Obtained from `impl` by basis transport (`Randomized.StateTransitionImpl.toStandard`). -/
noncomputable def implStandard (U V n_max w base : ℕ)
    (hw : 2 * hashBits U n_max ≤ w)
    (hS : Fits w (base + space n_max))
    (hV : Fits w V) :
    Randomized.StateTransitionImpl (subroutineCode U n_max).toStandard (Dictionary.spec U V n_max)
      w base Fin.elim0 (Dictionary.empty U) :=
  (impl U V n_max w base hw hS hV).toStandard

/-- **Expected subroutine body time across an oblivious operation sequence
(`seq_expected_amortized`).**
For fixed `U`, `n_max` and admissible word width `w`, `subroutineCode U n_max` uses precomputed
configuration literals (`initParams = Fin.elim0`). For a valid operation history
`ops : List (Dictionary.Op U)` fixed independently of the sampled seed (oblivious adversary),
running `initFresh` (`16` body instructions on zeroed `[base, base + space n_max)`) and
`C.ExecSteps` across `ops` (which receives each operation's prepared arguments and charges
subroutine operation bodies rather than a complete client/dispatch driver or configuration
construction) has total expected body cost `16 + T_ops ≤ 16 + 73 * ops.length`. -/
theorem seq_expected_amortized (U V n_max w base : ℕ)
    (hw : 2 * hashBits U n_max ≤ w)
    (hS : Fits w (base + space n_max))
    (hV : Fits w V)
    {x : Data rHash} (ops : List (Dictionary.Op U))
    (hx : x.Bounded w) (hfr : x.regs frontierReg = base)
    (hz : ∀ a ∈ (Block.mk base (space n_max)).footprint, x.mem a = 0)
    (hv : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U) ops) :
    let C := impl U V n_max w base hw hS hV
    ∃ (ν₀ ν_final : PMF (C.Seed × Data rHash)) (T_ops : ℝ≥0∞),
      ExecCodeDist w (subroutineCode U n_max).initFresh x (ν₀.map Prod.snd) C.initTime ∧
      C.ExecStepsOfFn (Dictionary.empty U) ops ν₀ ν_final T_ops ∧
      (∀ θ, (ν_final.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ) ∧
      (∀ p ∈ ν_final.support,
        C.rep p.1 ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops).1 p.2) ∧
      C.initTime + T_ops ≤ 16 + (chargeVal * ops.length : ℕ) := by
  intro C
  obtain ⟨ν₀, ν_final, T_ops, he_init, hex_steps, hseed_final, hrep_final, hbound⟩ :=
    C.seq_expected_amortized_ofFn ops hx hfr (fun j => Fin.elim0 j) hz hv
  refine ⟨ν₀, ν_final, T_ops, he_init, hex_steps, hseed_final, hrep_final, ?_⟩
  have hpot : (∑' q, ν_final q * (C.potential q.1 q.2 : ℝ≥0∞)) = 0 := by simp [C, impl]
  have hinit : C.initTime = 16 := by change (3 : ℝ≥0∞) + 13 = 16; norm_num
  have htotal : (Dictionary.spec U V n_max).totalCost C.charge (Dictionary.empty U) ops =
      chargeVal * ops.length :=
    (StateTransitionSpec.totalCost_const (Dictionary.spec U V n_max) chargeVal
      (Dictionary.empty U) ops).trans (Nat.mul_comm _ _)
  rw [hpot, add_zero, htotal] at hbound
  exact hbound.trans_eq (by change C.initTime + ((0 : ℕ) : ℝ≥0∞) + _ = _; simp [hinit])

end Cslib.DataStructure.Dictionary.WordRAM.ChainedHash
