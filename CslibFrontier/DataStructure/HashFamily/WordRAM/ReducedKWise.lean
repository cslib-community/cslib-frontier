/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.HashFamily.WordRAM.Basic
public import CslibFrontier.DataStructure.HashFamily.WordRAM.Tabulation
public import CslibFrontier.Probability.KWiseIndependent.ReducedLimbs
import CslibFrontier.Computability.WordRAM.RegisterFrame
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.UpdateSimp
import CslibFrontier.Tactic.WramOmega
import Mathlib.Data.Nat.Bitwise

/-!
# Universe-Reduced `k`-Wise Independent Hashing with Bit-Packed Tables

This module provides a reusable Word-RAM implementation of the two-stage universe-reduced `k`-wise
independent hash family (`Cslib.Probability.reducedPolyHash U w₀ b b' k`) over
`Cslib.WordRAM.Basis.exact` and lifts it to `Cslib.WordRAM.Basis.standard`:

1. **Two-stage construction without any universe restriction (`U ≤ 2 ^ w₀`, `0 < w₀ ≤ w`)**:
   - **Stage 1 (overflow-free multiply-shift reduction)**: reduces any `w₀`-bit key `u : Fin U`
     (`0 < w₀ ≤ w`) to `R = min w₀ (3 * b)` bits via `multiplyShiftReduced U w₀ (3 * b) α u` using
     `oddMulModWord` (`39` deterministic instructions, no `2 * w₀ ≤ w` restriction).
   - **Stage 2 (limb-aligned trinomial polynomial hash with bit-packed Four-Russians table)**:
     evaluates a degree-`< k` polynomial over `GF(2)[X] / (X^{2·3^t} + X^{3^t} + 1)` on the reduced
     key using `L = reducedLimbCount t ≤ 54` limbs of `c = reducedChunkBits t = 3 ^ (t - 3)` bits
     and a bit-packed Four-Russians carryless multiplication table of
     `reducedTableBits t ≤ max 8 (2 ^ (b / 2)) = o(2 ^ b)` bits (`b' ≤ 3 * b`).
2. **Compact `O(k) + o(2 ^ b) / w`-word memory layout (`space w w₀ b b' k`)**:
   - `[base, base + 1 + k * L)` stores the top seed `α : Fin (2 ^ (w₀ - 1))` (`1` word) and the
     `k * L` `c`-bit limbs of the polynomial coefficients `β : Fin k → Fin (2 ^ (2 * 3 ^ t))`
     (`1 + k * L ≤ 1 + 54 * k = O(k)` words).
   - `[base + 1 + k * L, base + space w w₀ b b' k)` stores the bit-packed carryless multiplication
     table in `tableWords w w₀ b b' = reducedTableWords t w` words.
3. **`O(1)` worst-case evaluation time for fixed `k` (`evalCode w w₀ b b' k`)**:
   - Executes in `evalSteps w₀ b b' k ≤ evalBound k = 47250 * k + 591 = O(k)` deterministic
     instructions completely independent of `w`, `w₀`, `b`, `b'`, and `U`.
4. **Conditional `k`-wise independence and `HashFamily.WordRAM.Impl` packaging**:
   - Conditioned on any top seed `α ∈ reducedGoodTop U w₀ (3 * b) S` that is injective on
     `S : Finset (Fin U)` (failure probability `≤ (#S * (#S - 1)) / 2 ^ min w₀ (3 * b)`), the
     restricted family on `S` is exact `k`-wise independent (`IsKWiseIndependentHash k`).

## Main definitions

* `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.seedWords`,
  `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.tableWords`,
  `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.space`: memory footprint sizes.
* `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.TableRep`,
  `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.SeedRep`,
  `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.Rep`: memory representation predicates.
* `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.initTableCode`,
  `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.resampleCode`,
  `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.evalCode`: Word-RAM programs on `Data 240`.
* `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.impl`,
  `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.implStandard`: `HashFamily.WordRAM.Impl`
  certificates.

## Main results

* `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.space_le`:
  `space w w₀ b b' k ≤ 2 + 54 * k + 2 * max 8 (2 ^ (b / 2)) / w` when `b' ≤ 3 * b`.
* `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.initTableCode_execWithin`: deterministic
  table initialization.
* `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.resampleCode_execRand`,
  `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.map_extractSeed_eval_resampleComp`: exact
  product uniformity of seed resampling.
* `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.evalCode_execWithin`,
  `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise.evalSteps_le`: deterministic evaluation in
  `≤ 47250 * k + 591` instructions.

## References

* [M. Dietzfelbinger, T. Hagerup, J. Katajainen, M. Penttonen, *A Reliable Randomized Algorithm
  for the Closest-Pair Problem*][DietzfelbingerHagerupKatajainenPenttonen1997]
* [S. P. Vadhan, *Pseudorandomness*, Section 3.5.5][Vadhan2012]
* [M. N. Wegman, J. L. Carter, *New hash functions and their use in authentication and set
  equality*][WegmanCarter1981]
-/

public section

open Cslib.WordRAM Cslib.DataStructure.WordRAM.Randomized Cslib.Probability
open scoped ENNReal BigOperators

namespace Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise

/-! ## Section 1: Memory layout, representation predicates, and seed extraction -/

/-- Number of seed words `1 + k * reducedLimbCount (reducedTrinomialStep w₀ b b')` (`1` word for the
multiply-shift seed `α` and `k * L` words for the `c`-bit limbs of the `k` polynomial
coefficients). -/
@[expose] def seedWords (w₀ b b' k : ℕ) : ℕ :=
  1 + k * reducedLimbCount (reducedTrinomialStep w₀ b b')

/-- Number of words `reducedTableWords (reducedTrinomialStep w₀ b b') w` occupied by the bit-packed
Four-Russians carryless multiplication table. -/
@[expose] def tableWords (w w₀ b b' : ℕ) : ℕ :=
  reducedTableWords (reducedTrinomialStep w₀ b b') w

/-- Total memory footprint `seedWords w₀ b b' k + tableWords w w₀ b b'` in words. -/
@[expose] def space (w w₀ b b' k : ℕ) : ℕ :=
  seedWords w₀ b b' k + tableWords w w₀ b b'

/-- Base address `base + seedWords w₀ b b' k` of the bit-packed carryless multiplication table. -/
@[expose] def tabBase (base w₀ b b' k : ℕ) : ℕ :=
  base + seedWords w₀ b b' k

/-- Address `base + 1 + (m.val + L * j.val)` of the `m`-th limb of polynomial coefficient `j`. -/
@[expose] def coeffLimbAddr (base w₀ b b' : ℕ) {k : ℕ}
    (j : Fin k) (m : Fin (reducedLimbCount (reducedTrinomialStep w₀ b b'))) : ℕ :=
  base + 1 + (m.val + reducedLimbCount (reducedTrinomialStep w₀ b b') * j.val)

attribute [local wram_arith] seedWords tableWords space tabBase

theorem and_two_pow_sub_one_lt (a n : ℕ) : a &&& (2 ^ n - 1) < 2 ^ n :=
  Nat.and_lt_two_pow a (Nat.sub_lt (Nat.two_pow_pos n) one_pos)

theorem shiftRight_lt_pow_sub {m h a : ℕ} (hle : h ≤ m) (ha : a < 2 ^ m) :
    a >>> h < 2 ^ (m - h) := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_of_lt_mul (by rwa [← pow_add, Nat.add_sub_of_le hle])

private theorem fits_mask_of_le {w n : ℕ} (h : n ≤ w) : Fits w (2 ^ n - 1) :=
  (Nat.sub_lt (Nat.two_pow_pos n) one_pos).trans_le (Nat.pow_le_pow_right two_pos h)

/-- Bit offset `(idx &&& (2 ^ reducedPackShift t w - 1)) * (2 * reducedChunkBits t)` of a packed
carryless-multiplication table slot fits below the word width `w`. -/
theorem packSlot_sh_lt {t w idx : ℕ} (h2c : 2 * reducedChunkBits t ≤ w) :
    (idx &&& (2 ^ reducedPackShift t w - 1)) * (2 * reducedChunkBits t) < w :=
  (Nat.mul_lt_mul_of_pos_right (and_two_pow_sub_one_lt idx (reducedPackShift t w))
    (by have := reducedChunkBits_pos t; omega)).trans_le (two_pow_reducedPackShift_mul_le h2c)

theorem seedWords_pos (w₀ b b' k : ℕ) : 0 < seedWords w₀ b b' k := by
  wram_omega

theorem seedWords_le (w₀ b b' k : ℕ) : seedWords w₀ b b' k ≤ 1 + 54 * k := by
  have := reducedLimbCount_le (reducedTrinomialStep w₀ b b')
  dsimp only [seedWords]; nlinarith

theorem tableWords_le {w w₀ b b' : ℕ} (hw₀ : w₀ ≤ w) (hb' : b' ≤ 3 * b) (hb'_w : b' ≤ w)
    (hw : 2 ≤ w) :
    tableWords w w₀ b b' ≤ 2 * max 8 (2 ^ (b / 2)) / w + 1 :=
  (reducedTableWords_le (two_mul_reducedChunkBits_le hw₀ hb'_w hw)).trans <|
    Nat.add_le_add_right (Nat.div_le_div_right (Nat.mul_le_mul_left 2 (reducedTableBits_le hb'))) 1

/-- **Compact space bound**: whenever `w₀ ≤ w`, `b' ≤ 3 * b`, `b' ≤ w`, and `2 ≤ w`,
`space w w₀ b b' k` uses at most `2 + 54 * k + 2 * max 8 (2 ^ (b / 2)) / w` words
(`O(k) + o(2 ^ b) / w`). -/
theorem space_le {w w₀ b b' k : ℕ} (hw₀ : w₀ ≤ w) (hb' : b' ≤ 3 * b) (hb'_w : b' ≤ w)
    (hw : 2 ≤ w) :
    space w w₀ b b' k ≤ 2 + 54 * k + 2 * max 8 (2 ^ (b / 2)) / w := by
  have := seedWords_le w₀ b b' k
  have := tableWords_le hw₀ hb' hb'_w hw
  wram_omega

/-- Whenever `2 * reducedChunkBits t ≤ w` and `Fits w (base + space w w₀ b b' k)`, we have strict
inequality `2 * reducedChunkBits t < w` (and hence `2 ^ (2 * reducedChunkBits t) < 2 ^ w`). -/
theorem two_mul_reducedChunkBits_lt_of_fits_space {w base w₀ b b' k : ℕ}
    (hc : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') ≤ w)
    (hfit : Fits w (base + space w w₀ b b' k)) :
    2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w := by
  by_contra hnot
  have heq : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') = w := by omega
  have hc_pos : 0 < 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') :=
    Nat.mul_pos two_pos (reducedChunkBits_pos _)
  have hp0 : reducedPackShift (reducedTrinomialStep w₀ b b') w = 0 := by
    simp [reducedPackShift, ← heq, Nat.div_self hc_pos]
  have htw : tableWords w w₀ b b' = 2 ^ w := by
    simp [tableWords, reducedTableWords, hp0, heq]
  dsimp only [space, Fits] at hfit
  omega

/-- Deterministic precomputed table invariant at `tabBase base w₀ b b' k`: every table word is
`< 2 ^ (2 ^ p * (2 * c))` and every `2 * c`-bit slice `idx < 2 ^ (2 * c)` stores
`clmul (idx >>> c) (idx &&& (2 ^ c - 1))`. -/
@[expose] def TableRep (base w w₀ b b' k : ℕ) (mem : ℕ → ℕ) : Prop :=
  let t := reducedTrinomialStep w₀ b b'
  let c := reducedChunkBits t
  let p := reducedPackShift t w
  let tBase := tabBase base w₀ b b' k
  (∀ wIdx < tableWords w w₀ b b', mem (tBase + wIdx) < 2 ^ (2 ^ p * (2 * c))) ∧
  (∀ idx < 2 ^ (2 * c),
    getLimb (2 * c) (mem (tBase + (idx >>> p))) (idx &&& (2 ^ p - 1)) =
      clmul (idx >>> c) (idx &&& (2 ^ c - 1)))

/-- Seed representation invariant linking `θ : ReducedPolySeed w₀ b b' k` to memory at
`[base, base + seedWords w₀ b b' k)`. -/
@[expose] def SeedRep (base w₀ b b' k : ℕ) (θ : ReducedPolySeed w₀ b b' k) (mem : ℕ → ℕ) : Prop :=
  let t := reducedTrinomialStep w₀ b b'
  let c := reducedChunkBits t
  let L := reducedLimbCount t
  mem base = θ.1.val ∧
  ∀ (j : Fin k) (m : Fin L),
    mem (base + 1 + (m.val + L * j.val)) = getLimb c (θ.2 j).val m.val

/-- Combined table + seed invariant `TableRep ∧ SeedRep`. -/
@[expose] def Rep (base w w₀ b b' k : ℕ) (θ : ReducedPolySeed w₀ b b' k) (mem : ℕ → ℕ) : Prop :=
  TableRep base w w₀ b b' k mem ∧ SeedRep base w₀ b b' k θ mem

/-- Equivalence `(Fin 1 → Fin (2 ^ (w₀ - 1))) ≃ ReducedTopSeed w₀`. -/
@[expose] def topSliceEquiv (w₀ : ℕ) :
    (Fin 1 → Fin (2 ^ (w₀ - 1))) ≃ ReducedTopSeed w₀ :=
  Equiv.funUnique (Fin 1) (Fin (2 ^ (w₀ - 1)))

/-- Equivalence between flat `k * L`-word slices of `c`-bit limbs and
`ReducedBotSeed w₀ b b' k`. -/
@[expose] def botSliceEquiv (w₀ b b' k : ℕ) :
    let t := reducedTrinomialStep w₀ b b'
    (Fin (k * reducedLimbCount t) → Fin (2 ^ reducedChunkBits t)) ≃
      ReducedBotSeed w₀ b b' k :=
  let t := reducedTrinomialStep w₀ b b'
  let c := reducedChunkBits t
  let L := reducedLimbCount t
  (Equiv.arrowCongr finProdFinEquiv (Equiv.refl (Fin (2 ^ c)))).symm.trans <|
    (Equiv.curry (Fin k) (Fin L) (Fin (2 ^ c))).trans <|
      Equiv.arrowCongr (Equiv.refl (Fin k))
        ((limbsEquivFin c L (reducedChunkBits_pos t)).trans
          (finCongr (by rw [reducedLimbCount_mul_chunkBits])))

/-- Extract the top-level multiply-shift seed `α : ReducedTopSeed w₀` from `mem base`. -/
@[expose] def extractTop (base w₀ : ℕ) (mem : ℕ → ℕ) : ReducedTopSeed w₀ :=
  topSliceEquiv w₀ (Tabulation.extractSlice base (w₀ - 1) 1 mem)

/-- Extract the bottom-level polynomial seed `β : ReducedBotSeed w₀ b b' k` from
`[base + 1, base + 1 + k * L)`. -/
@[expose] def extractBot (base w₀ b b' k : ℕ) (mem : ℕ → ℕ) : ReducedBotSeed w₀ b b' k :=
  let t := reducedTrinomialStep w₀ b b'
  botSliceEquiv w₀ b b' k
    (Tabulation.extractSlice (base + 1) (reducedChunkBits t) (k * reducedLimbCount t) mem)

/-- Extract the full seed `(α, β) : ReducedPolySeed w₀ b b' k` from memory. -/
@[expose] def extractSeed (base w₀ b b' k : ℕ) (mem : ℕ → ℕ) : ReducedPolySeed w₀ b b' k :=
  (extractTop base w₀ mem, extractBot base w₀ b b' k mem)

@[simp]
theorem extractTop_val (base w₀ : ℕ) (mem : ℕ → ℕ) :
    (extractTop base w₀ mem).val = (Cslib.WordRAM.wordOfNat (w₀ - 1) (mem base)).val := by
  simp [extractTop, topSliceEquiv, Tabulation.extractSlice]

theorem getLimb_extractBot_val (base w₀ b b' k : ℕ) (mem : ℕ → ℕ)
    (j : Fin k) (m : Fin (reducedLimbCount (reducedTrinomialStep w₀ b b'))) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    getLimb c (extractBot base w₀ b b' k mem j).val m.val =
      (Cslib.WordRAM.wordOfNat c (mem (base + 1 + (m.val + L * j.val)))).val := by
  intro t c L
  exact congrArg Fin.val (congrFun ((limbsEquivFin c L (reducedChunkBits_pos t)).symm_apply_apply
    fun m' => Tabulation.extractSlice (base + 1) c (k * L) mem (finProdFinEquiv (j, m'))) m)

/-- Extracting a seed from memory satisfying `SeedRep` recovers the original seed `θ`. -/
theorem extractSeed_of_seedRep {base w₀ b b' k : ℕ}
    {θ : ReducedPolySeed w₀ b b' k} {mem : ℕ → ℕ}
    (hseed : SeedRep base w₀ b b' k θ mem) :
    extractSeed base w₀ b b' k mem = θ := by
  unfold extractSeed
  obtain ⟨h0, hlimb⟩ := hseed
  refine Prod.ext (Fin.ext ?_) (funext fun j => Fin.ext ?_)
  · dsimp only
    rw [extractTop_val, h0]
    exact Cslib.WordRAM.wordOfNat_val_of_lt θ.1.isLt
  · dsimp only
    set t := reducedTrinomialStep w₀ b b'
    set c := reducedChunkBits t
    set L := reducedLimbCount t
    have hc : 0 < c := reducedChunkBits_pos t
    have hpow : L * c = 2 * 3 ^ t := reducedLimbCount_mul_chunkBits t
    have ha : (extractBot base w₀ b b' k mem j).val < 2 ^ (L * c) :=
      hpow.symm ▸ (extractBot base w₀ b b' k mem j).isLt
    have hb : (θ.2 j).val < 2 ^ (L * c) := hpow.symm ▸ (θ.2 j).isLt
    rw [← packLimbs_getLimb hc L ha, ← packLimbs_getLimb hc L hb]
    refine packLimbs_congr fun m hm => ?_
    have hm' := getLimb_extractBot_val base w₀ b b' k mem j ⟨m, hm⟩
    dsimp only at hm'
    rw [hm', hlimb j ⟨m, hm⟩]
    exact Cslib.WordRAM.wordOfNat_val_of_lt (getLimb_lt c (θ.2 j).val m)

/-! ## Register layout on `Data 240` -/

/-- Reduced-key limb register `20 + m % 54` (`0 ≤ m < L ≤ 54`). -/
@[expose] def xReg (m : ℕ) : Fin 240 :=
  ⟨20 + m % 54, by omega⟩

/-- Horner accumulator limb register `74 + m % 54` (`0 ≤ m < L ≤ 54`). -/
@[expose] def accReg (m : ℕ) : Fin 240 :=
  ⟨74 + m % 54, by omega⟩

/-- Carryless product limb register `128 + d % 108` (`0 ≤ d < 2 * L ≤ 108`). -/
@[expose] def prodReg (d : ℕ) : Fin 240 :=
  ⟨128 + d % 108, by omega⟩

/-- Register embedding `Fin 6 → Fin 240` for `Tabulation.randFillLoop`:
maps `[0, 1, 2, 3, 4, 5] ↦ [3, 4, 5, 6, 7, 0]`. -/
@[expose] def fillMap240 : Fin 6 → Fin 240
  | ⟨0, _⟩ => 3
  | ⟨1, _⟩ => 4
  | ⟨2, _⟩ => 5
  | ⟨3, _⟩ => 6
  | ⟨4, _⟩ => 7
  | ⟨5, _⟩ => 0

theorem injective_fillMap240 : Function.Injective fillMap240 := by
  decide

private theorem tableRep_congr_on_tab {base w w₀ b b' k : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (htab : TableRep base w w₀ b b' k mem₁)
    (heq : ∀ wIdx < tableWords w w₀ b b',
      mem₁ (tabBase base w₀ b b' k + wIdx) = mem₂ (tabBase base w₀ b b' k + wIdx)) :
    TableRep base w w₀ b b' k mem₂ :=
  ⟨fun wIdx hw => heq wIdx hw ▸ htab.1 wIdx hw,
    fun idx hi => heq _ (shiftRight_lt_reducedTableWords hi) ▸ htab.2 idx hi⟩

/-- `TableRep` depends only on memory in `[base, base + space w w₀ b b' k)`. -/
theorem tableRep_congr {base w w₀ b b' k : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (htab : TableRep base w w₀ b b' k mem₁)
    (heq : ∀ a, base ≤ a → a < base + space w w₀ b b' k → mem₁ a = mem₂ a) :
    TableRep base w w₀ b b' k mem₂ :=
  tableRep_congr_on_tab htab fun _ _ => heq _ (by wram_omega) (by wram_omega)

/-- `SeedRep` depends only on memory in `[base, base + space w w₀ b b' k)`. -/
theorem seedRep_congr {base w w₀ b b' k : ℕ} {θ : ReducedPolySeed w₀ b b' k}
    {mem₁ mem₂ : ℕ → ℕ}
    (hseed : SeedRep base w₀ b b' k θ mem₁)
    (heq : ∀ a, base ≤ a → a < base + space w w₀ b b' k → mem₁ a = mem₂ a) :
    SeedRep base w₀ b b' k θ mem₂ :=
  ⟨(heq base le_rfl (by wram_omega)).symm ▸ hseed.1, fun j m =>
    (heq (base + 1 + (m.val + reducedLimbCount (reducedTrinomialStep w₀ b b') * j.val))
      (by omega) (by dsimp only [space, seedWords]; stride_omega [j.isLt, m.isLt])).symm ▸
      hseed.2 j m⟩

/-! ## Section 2: Bit-packed Four-Russians table construction (`initTableCode`) -/

/-- 11-instruction setup before `clmulTabLoop` on `Data 240`. -/
@[expose] def initTableSetupCode (w w₀ b b' k : ℕ) : Code .exact 240 :=
  let t := reducedTrinomialStep w₀ b b'
  let c := reducedChunkBits t
  let p := reducedPackShift t w
  let s := seedWords w₀ b b' k
  .seq (.op (.const 1 s))
  (.seq (.op (.exactBin .add 1 0 1))
  (.seq (.op (.const 2 0))
  (.seq (.op (.const 3 (2 ^ (2 * c))))
  (.seq (.op (.const 4 c))
  (.seq (.op (.const 5 (2 ^ c - 1)))
  (.seq (.op (.const 6 1))
  (.seq (.op (.const 7 p))
  (.seq (.op (.const 8 (2 ^ p - 1)))
  (.seq (.op (.const 9 (2 * c)))
        (.op (.const 18 (2 ^ (2 * c) - 1))))))))))))

/-- Closed-form state after `initTableSetupCode w w₀ b b' k`. -/
@[expose] def initTableSetupData (base w w₀ b b' k : ℕ) (x : Data 240) : Data 240 :=
  let t := reducedTrinomialStep w₀ b b'
  let c := reducedChunkBits t
  let p := reducedPackShift t w
  let s := seedWords w₀ b b' k
  (((((((((((x.set 1 s).set 1 (base + s)).set 2 0).set 3 (2 ^ (2 * c))).set 4 c).set 5
    (2 ^ c - 1)).set 6 1).set 7 p).set 8 (2 ^ p - 1)).set 9 (2 * c)).set 18 (2 ^ (2 * c) - 1))

/-- 29-instruction body of `clmulTabLoop` on `Data 240`, populating slice `idx &&& (2 ^ p - 1)` of
`mem[tabBase + (idx >>> p)]` with `clmul (idx >>> c) (idx &&& (2 ^ c - 1))`. -/
@[expose] def clmulTabBody : Code .exact 240 :=
  .seq (.op (.exactBin .shiftRight 10 2 7))
  (.seq (.op (.exactBin .add 10 1 10))
  (.seq (.op (.exactBin .and 11 2 8))
  (.seq (.op (.exactBin .mul 11 11 9))
  (.seq (.op (.exactBin .shiftLeft 12 6 11))
  (.seq (.op (.exactBin .sub 12 12 6))
  (.seq (.op (.load 13 10))
  (.seq (.op (.exactBin .and 13 13 12))
  (.seq (.op (.store 10 13))
  (.seq (.op (.exactBin .shiftRight 14 2 4))
  (.seq (.op (.exactBin .and 15 2 5))
  (.seq (.op (.exactBin .shiftRight 16 15 6))
  (.seq (.op (.exactBin .shiftLeft 17 14 4))
  (.seq (.op (.exactBin .add 16 17 16))
  (.seq (.op (.exactBin .shiftRight 17 16 7))
  (.seq (.op (.exactBin .add 17 1 17))
  (.seq (.op (.load 17 17))
  (.seq (.op (.exactBin .and 16 16 8))
  (.seq (.op (.exactBin .mul 16 16 9))
  (.seq (.op (.exactBin .shiftRight 17 17 16))
  (.seq (.op (.exactBin .and 17 17 18))
  (.seq (.op (.exactBin .shiftLeft 17 17 6))
  (.seq (.op (.exactBin .and 15 15 6))
  (.seq (.op (.exactBin .mul 15 15 14))
  (.seq (.op (.exactBin .xor 17 15 17))
  (.seq (.op (.exactBin .shiftLeft 17 17 11))
  (.seq (.op (.exactBin .xor 13 13 17))
  (.seq (.op (.store 10 13))
        (.op (.exactBin .add 2 2 6)))))))))))))))))))))))))))))

/-- Loop `while idx < 2 ^ (2 * c) do clmulTabBody` populating the bit-packed carryless
multiplication table. -/
@[expose] def clmulTabLoop : Code .exact 240 :=
  .loop (.lt 2 3) clmulTabBody

/-- Full table initialization program on `Data 240`. -/
@[expose] def initTableCode (w w₀ b b' k : ℕ) : Code .exact 240 :=
  .seq (initTableSetupCode w w₀ b b' k) clmulTabLoop

/-- Exact instruction count `31 * 2 ^ (2 * c) + 13` of `initTableCode w w₀ b b' k`. -/
@[expose] def initTableSteps (w₀ b b' : ℕ) : ℕ :=
  31 * 2 ^ (2 * reducedChunkBits (reducedTrinomialStep w₀ b b')) + 13

/-- Modifying the bit-packed slice `(idx >>> p, idx &&& (2 ^ p - 1))` by clearing all bits at or
above `sh = (idx &&& (2 ^ p - 1)) * (2 * c)` and XORing in `val <<< sh` (`val < 2 ^ (2 * c)`)
preserves `getLimb (2 * c)` at every strictly earlier entry `j < idx`. -/
theorem clmulTab_getLimb_update_lt {p c tBase idx j val : ℕ} {mem : ℕ → ℕ}
    (hj : j < idx) (hval : val < 2 ^ (2 * c)) :
    let wIdx := idx >>> p
    let sh := (idx &&& (2 ^ p - 1)) * (2 * c)
    let w' := (mem (tBase + wIdx) &&& ((1 <<< sh) - 1)) ^^^ (val <<< sh)
    getLimb (2 * c) (Function.update mem (tBase + wIdx) w' (tBase + (j >>> p)))
      (j &&& (2 ^ p - 1)) =
      getLimb (2 * c) (mem (tBase + (j >>> p))) (j &&& (2 ^ p - 1)) := by
  intro wIdx sh w'
  rcases eq_or_ne (j >>> p) wIdx with heq | hne
  · have hlt := and_lt_of_lt_of_shiftRight_eq hj heq
    rw [heq]; update_simp
    simpa only [w', sh, Nat.shiftLeft_eq, one_mul] using
      (getLimb_xor_shiftLeft_of_ne hval hlt.ne).trans (getLimb_and_low hlt)
  · update_simp

/-- Updating word `tBase + wIdx` to a value below `B` preserves the `< B` bound on every word
`tBase + w'` with `w' ≤ wIdx`, assuming all strictly earlier words already satisfy `< B`. -/
theorem update_word_lt {tBase wIdx newW B : ℕ} {mem : ℕ → ℕ}
    (hnew : newW < B) (hold : ∀ w' < wIdx, mem (tBase + w') < B)
    {w' : ℕ} (hw' : w' ≤ wIdx) :
    Function.update mem (tBase + wIdx) newW (tBase + w') < B := by
  rcases eq_or_lt_of_le hw' with rfl | hlt <;> update_simp <;> [exact hnew; exact hold w' hlt]

/-- After masking bits at or above slot `(idx &&& (2 ^ p - 1)) * (2 * c)` of word
`tBase + (idx >>> p)`, reading the packed limb at `prevIdx = ((idx >>> c) <<< c) + (v >>> 1)`
returns `clmul (idx >>> c) ((idx &&& (2 ^ c - 1)) >>> 1)` whenever all strictly earlier entries
`< idx` hold their carryless products. -/
theorem clmulTab_prev_limb {t w tBase idx : ℕ} {mem : ℕ → ℕ}
    (hidx : idx < 2 ^ (2 * reducedChunkBits t))
    (hentry : ∀ i < idx,
      getLimb (2 * reducedChunkBits t)
        (mem (tBase + (i >>> reducedPackShift t w))) (i &&& (2 ^ reducedPackShift t w - 1)) =
          clmul (i >>> reducedChunkBits t) (i &&& (2 ^ reducedChunkBits t - 1))) :
    let c := reducedChunkBits t
    let p := reducedPackShift t w
    let u := idx >>> c
    let v := idx &&& (2 ^ c - 1)
    let prevIdx := (u <<< c) + (v >>> 1)
    let wIdx := idx >>> p
    let masked := mem (tBase + wIdx) &&& ((1 <<< ((idx &&& (2 ^ p - 1)) * (2 * c))) - 1)
    (Function.update mem (tBase + wIdx) masked (tBase + (prevIdx >>> p)) >>>
        ((prevIdx &&& (2 ^ p - 1)) * (2 * c))) &&& (2 ^ (2 * c) - 1) =
      clmul u (v >>> 1) := by
  intro c p u v prevIdx wIdx masked
  obtain ⟨_, _, _, _, hprev_lt, hprev_zero, hprev_u, hprev_v⟩ := clmulTab_index_props hidx
  by_cases hv0 : v = 0
  · have hpeq : prevIdx = idx := hprev_zero hv0
    have hw : prevIdx >>> p = wIdx := congrArg (· >>> p) hpeq
    change getLimb (2 * c) (Function.update mem (tBase + wIdx) masked (tBase + (prevIdx >>> p)))
      (prevIdx &&& (2 ^ p - 1)) = clmul u (v >>> 1)
    rw [hw, show prevIdx &&& (2 ^ p - 1) = idx &&& (2 ^ p - 1) from
        congrArg (· &&& (2 ^ p - 1)) hpeq,
      Function.update_self, show v >>> 1 = 0 by rw [hv0]; rfl, clmul_zero_right]
    simpa only [masked, Nat.shiftLeft_eq, one_mul] using
      getLimb_and_self (2 * c) (mem (tBase + wIdx)) (idx &&& (2 ^ p - 1))
  · have hplt := hprev_lt hv0
    have hkeep := clmulTab_getLimb_update_lt (p := p) (c := c) (tBase := tBase) (mem := mem)
      hplt (val := 0) (Nat.two_pow_pos _)
    simp only [Nat.zero_shiftLeft, Nat.xor_zero] at hkeep
    exact hkeep.trans (by rw [hentry prevIdx hplt, hprev_u, hprev_v])

theorem clmulTabLoop_exec {w tBase t : ℕ}
    (hc_lt : 2 * reducedChunkBits t < w)
    (hfit_end : Fits w (tBase + reducedTableWords t w)) :
    let c := reducedChunkBits t
    let p := reducedPackShift t w
    ∀ rem idx : ℕ, ∀ x : Data 240,
      idx + rem = 2 ^ (2 * c) →
      x.regs 0 = x.regs 0 →
      x.regs 1 = tBase →
      x.regs 2 = idx →
      x.regs 3 = 2 ^ (2 * c) →
      x.regs 4 = c →
      x.regs 5 = 2 ^ c - 1 →
      x.regs 6 = 1 →
      x.regs 7 = p →
      x.regs 8 = 2 ^ p - 1 →
      x.regs 9 = 2 * c →
      x.regs 18 = 2 ^ (2 * c) - 1 →
      (∀ wIdx < idx >>> p, x.mem (tBase + wIdx) < 2 ^ (2 ^ p * (2 * c))) →
      (∀ i < idx,
        getLimb (2 * c) (x.mem (tBase + (i >>> p))) (i &&& (2 ^ p - 1)) =
          clmul (i >>> c) (i &&& (2 ^ c - 1))) →
      ∃ y : Data 240,
        Exec w clmulTabLoop x y (31 * rem + 2) ∧
        y.regs 0 = x.regs 0 ∧
        (∀ wIdx < reducedTableWords t w, y.mem (tBase + wIdx) < 2 ^ (2 ^ p * (2 * c))) ∧
        (∀ i < 2 ^ (2 * c),
          getLimb (2 * c) (y.mem (tBase + (i >>> p))) (i &&& (2 ^ p - 1)) =
            clmul (i >>> c) (i &&& (2 ^ c - 1))) ∧
        (∀ a, (a < tBase + (idx >>> p) ∨ tBase + reducedTableWords t w ≤ a) →
          y.mem a = x.mem a) := by
  intro c p rem
  have hc_pos : 0 < c := reducedChunkBits_pos t
  have hp_le : p ≤ 2 * c := reducedPackShift_le t w
  have hpow_pack : 2 ^ (2 ^ p * (2 * c)) ≤ 2 ^ w := by
    stride_omega [two_pow_reducedPackShift_mul_le hc_lt.le]
  induction rem with
  | zero =>
    intro idx x hsum _ _ h2 h3 _ _ _ _ _ _ _ hword hentry
    have hidx_eq : idx = 2 ^ (2 * c) := by omega
    refine ⟨x, Exec.loop_exit (by simp [Cond.Holds, h2, h3, hidx_eq]), rfl,
      fun wIdx hw => hword wIdx (by rwa [hidx_eq, two_pow_two_mul_chunkBits_shiftRight]),
      fun i hi => hentry i (hidx_eq ▸ hi), fun _ _ => rfl⟩
  | succ rem ih =>
    intro idx x hsum _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h18 hword hentry
    have hidx_lt : idx < 2 ^ (2 * c) := by omega
    have hc_hold : (Cond.lt (2 : Fin 240) 3).Holds x := by simp [Cond.Holds, h2, h3, hidx_lt]
    obtain ⟨hu_lt, hv_lt, _, hprev_le, _, _, _, _⟩ := clmulTab_index_props hidx_lt
    set u := idx >>> c with hu
    set v := idx &&& (2 ^ c - 1) with hv
    set prevIdx := (u <<< c) + (v >>> 1) with hprevIdx
    set wIdx := idx >>> p with hwIdx
    set subIdx := idx &&& (2 ^ p - 1) with hsubIdx
    set sh := subIdx * (2 * c) with hsh
    set prevWIdx := prevIdx >>> p with hprevWIdx
    set prevSub := prevIdx &&& (2 ^ p - 1) with hprevSub
    set prevSh := prevSub * (2 * c) with hprevSh
    set maskedWord := x.mem (tBase + wIdx) &&& ((1 <<< sh) - 1) with hmaskedWord
    set newWord := maskedWord ^^^ (clmul u v <<< sh) with hnewWord
    have hwIdx_lt : wIdx < reducedTableWords t w := shiftRight_lt_reducedTableWords hidx_lt
    have hprevWIdx_le : prevWIdx ≤ wIdx := by
      simpa only [prevWIdx, wIdx, Nat.shiftRight_eq_div_pow] using Nat.div_le_div_right hprev_le
    have hsub_lt : subIdx < 2 ^ p := and_two_pow_sub_one_lt idx p
    have hsh_lt : sh < w := packSlot_sh_lt hc_lt.le
    have hprevSh_lt : prevSh < w := packSlot_sh_lt hc_lt.le
    have hmasked_lt : maskedWord < 2 ^ sh := by
      simpa only [maskedWord, Nat.shiftLeft_eq, one_mul] using
        and_two_pow_sub_one_lt (x.mem (tBase + wIdx)) sh
    have hval_lt : clmul u v < 2 ^ (2 * c) := clmul_lt_two_pow_two_mul hu_lt hv_lt
    have hpow_sub1 : 2 ^ ((subIdx + 1) * (2 * c)) ≤ 2 ^ (2 ^ p * (2 * c)) := by stride_omega
    have hnewWord_lt : newWord < 2 ^ (2 ^ p * (2 * c)) := by
      stride_omega [xor_shiftLeft_lt_two_pow hmasked_lt hval_lt]
    have hprevLimb :
        (Function.update x.mem (tBase + wIdx) maskedWord (tBase + prevWIdx) >>> prevSh) &&&
          (2 ^ (2 * c) - 1) = clmul u (v >>> 1) :=
      clmulTab_prev_limb (w := w) (tBase := tBase) hidx_lt hentry
    have hsh_le : wIdx ≤ (idx + 1) >>> p := by
      simpa only [wIdx, Nat.shiftRight_eq_div_pow] using Nat.div_le_div_right (Nat.le_succ idx)
    have hword' : ∀ w' < (idx + 1) >>> p,
        Function.update x.mem (tBase + wIdx) newWord (tBase + w') < 2 ^ (2 ^ p * (2 * c)) :=
      fun _ hw' => update_word_lt hnewWord_lt hword
        (by have := shiftRight_add_one_le idx p; omega)
    have hentry' : ∀ i < idx + 1,
        getLimb (2 * c) (Function.update x.mem (tBase + wIdx) newWord (tBase + (i >>> p)))
          (i &&& (2 ^ p - 1)) = clmul (i >>> c) (i &&& (2 ^ c - 1)) := by
      intro i hi
      rcases eq_or_ne i idx with rfl | hne
      · change getLimb (2 * c) (Function.update x.mem (tBase + wIdx) newWord (tBase + wIdx))
          subIdx = clmul u v
        update_simp; exact getLimb_xor_shiftLeft_self hmasked_lt hval_lt
      · rw [clmulTab_getLimb_update_lt (by omega) hval_lt, hentry i (by omega)]
    refine WP.Exact.exists_exec (WP.Exact.loop_iter hc_hold ?_)
    unfold clmulTabBody
    have hbit_le : (v &&& 1) * u ≤ u := by stride_omega [Nat.and_le_right (n := v) (m := 1)]
    have hcl_sh1_lt : clmul u (v >>> 1) <<< 1 < 2 ^ (2 * c) :=
      (Nat.shiftLeft_lt (clmul_lt_two_pow hu_lt (shiftRight_lt_pow_sub hc_pos hv_lt))).trans_eq
        (congrArg (2 ^ ·) (by omega))
    have h1sh_lt : Fits w (1 <<< sh) := by rw [Fits, Nat.shiftLeft_eq, one_mul]; stride_omega
    have hfit_masked : Fits w maskedWord := by stride_omega
    have hfit_new : Fits w newWord := by stride_omega
    have hpow_c_le : 2 ^ c ≤ 2 ^ (2 * c) := by stride_omega
    have hfit_2c : Fits w (2 ^ (2 * c)) := by stride_omega
    wram_exec [h1, h2, h4, h5, h6, h7, h8, h9, h18, ← hu, ← hv, ← hprevIdx, ← hwIdx,
      ← hsubIdx, ← hsh, ← hprevWIdx, ← hprevSub, ← hprevSh, ← hmaskedWord, ← hnewWord,
      Data.write_mem, Data.set_mem, hprevLimb, clmul_eq_bit_mul_xor]
    · wram_call (ih (idx + 1) _ (by omega) rfl (by wram_simp [h1]) (by wram_simp)
        (by wram_simp [h3]) (by wram_simp [h4]) (by wram_simp [h5]) (by wram_simp [h6])
        (by wram_simp [h7]) (by wram_simp [h8]) (by wram_simp [h9]) (by wram_simp [h18])
        (by simp only [Data.set_mem, Data.write_mem, Function.update_idem]; exact hword')
        (by simp only [Data.set_mem, Data.write_mem, Function.update_idem]; exact hentry'))
        with y ⟨hy0, hyword, hyentry, hyout⟩
      exact ⟨by omega, hy0.trans (by wram_simp), hyword, hyentry,
        fun a ha => (hyout a (by omega)).trans (by wram_simp)⟩
    all_goals first
      | exact ((Nat.shiftLeft_lt hval_lt).trans_eq
          (congrArg (2 ^ ·) (by rw [add_comm, ← Nat.succ_mul]))).trans_le
          (hpow_sub1.trans hpow_pack)
      | exact ((Nat.shiftRight_le _ _).trans_lt (update_word_lt
          (hmasked_lt.trans_le (Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_right _ hsub_lt.le)))
          hword hprevWIdx_le)).trans_le hpow_pack

private theorem tableSetup_fits {w base w₀ b b' k : ℕ}
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + space w w₀ b b' k)) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let p := reducedPackShift t w
    Fits w (2 ^ (2 * c)) ∧ Fits w (seedWords w₀ b b' k) ∧
      Fits w (tabBase base w₀ b b' k) ∧ Fits w c ∧ Fits w (2 ^ c - 1) ∧
      Fits w p ∧ Fits w (2 ^ p - 1) ∧ Fits w (2 * c) := by
  intro t c p
  have hp_le : p ≤ 2 * c := reducedPackShift_le t w
  exact ⟨by stride_omega, by wram_omega, by wram_omega, by stride_omega, by stride_omega,
    by stride_omega, by stride_omega, by stride_omega⟩

/-- **Deterministic execution of `initTableCode w w₀ b b' k`**: establishes `TableRep`, preserves
`reg 0 = base`, and modifies only `[tabBase base w₀ b b' k, base + space w w₀ b b' k)`. -/
theorem initTableCode_exec {w base w₀ b b' k : ℕ} {x : Data 240}
    (hbase : x.regs 0 = base)
    (hc : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') ≤ w)
    (hfit_space : Fits w (base + space w w₀ b b' k)) :
    ∃ y : Data 240,
      Exec w (initTableCode w w₀ b b' k) x y (initTableSteps w₀ b b') ∧
      y.regs 0 = base ∧
      TableRep base w w₀ b b' k y.mem ∧
      (∀ a, (a < tabBase base w₀ b b' k ∨ base + space w w₀ b b' k ≤ a) → y.mem a = x.mem a) := by
  set t := reducedTrinomialStep w₀ b b' with ht
  set c := reducedChunkBits t with hc_def
  set p := reducedPackShift t w with hp_def
  set s := seedWords w₀ b b' k with hs
  have hc_lt : 2 * c < w := two_mul_reducedChunkBits_lt_of_fits_space hc hfit_space
  obtain ⟨hfit_2c, hfit_s, hfit_tBase, hfit_c, hfit_mask_c, hfit_p, hfit_mask_p, hfit_2c_val⟩ :=
    tableSetup_fits hc_lt hfit_space
  change Fits w (base + s) at hfit_tBase
  have hfit_2c_sub : Fits w (2 ^ (2 * c) - 1) := hfit_2c.of_le (Nat.sub_le _ _)
  have hfit_end : Fits w (tabBase base w₀ b b' k + reducedTableWords t w) := by wram_omega
  wram_exec [initTableCode, initTableSetupCode, hbase, ← ht, ← hc_def, ← hp_def, ← hs]
  wram_call (clmulTabLoop_exec (tBase := tabBase base w₀ b b' k) (t := t) hc_lt hfit_end
    (2 ^ (2 * c)) 0 _ (Nat.zero_add _) rfl (by wram_simp [tabBase, s]) (by wram_simp)
    (by wram_simp [c, t]) (by wram_simp [c, t]) (by wram_simp [c, t]) (by wram_simp)
    (by wram_simp [p, t]) (by wram_simp [p, t]) (by wram_simp [c, t]) (by wram_simp [c, t])
    (by simp) (by simp))
    with y ⟨hy0, hyword, hyentry, hyout⟩
  exact ⟨rfl, hy0.trans (by wram_simp [hbase]), ⟨hyword, hyentry⟩,
    fun a ha => hyout a (by simp only [Nat.zero_shiftRight, Nat.add_zero]; wram_omega)⟩

/-- `ExecWithin` corollary of `initTableCode_exec`. -/
theorem initTableCode_execWithin {w base w₀ b b' k : ℕ} {x : Data 240}
    (hbase : x.regs 0 = base)
    (hc : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') ≤ w)
    (hfit_space : Fits w (base + space w w₀ b b' k)) :
    ∃ y : Data 240,
      ExecWithin w (initTableCode w w₀ b b' k) x y (initTableSteps w₀ b b') ∧
      y.regs 0 = base ∧
      TableRep base w w₀ b b' k y.mem ∧
      (∀ a, (a < tabBase base w₀ b b' k ∨ base + space w w₀ b b' k ≤ a) → y.mem a = x.mem a) := by
  obtain ⟨y, hex, hy0, htab, hmod⟩ := initTableCode_exec hbase hc hfit_space
  exact ⟨y, hex.within, hy0, htab, hmod⟩

/-! ## Section 3: Exact uniform seed resampling (`resampleCode`) -/

/-- 5-instruction setup for the top-seed `Tabulation.randFillLoop` call on `Data 240`. -/
@[expose] def resampleSetup1Code (w₀ : ℕ) : Code .exact 240 :=
  .seq (.op (.copy 3 0))
  (.seq (.op (.const 4 1))
  (.seq (.op (.exactBin .add 4 0 4))
  (.seq (.op (.const 5 (2 ^ (w₀ - 1) - 1)))
        (.op (.const 6 1)))))

/-- State after `resampleSetup1Code w₀`. -/
@[expose] def resampleSetup1Data (base w₀ : ℕ) (x : Data 240) : Data 240 :=
  ((((x.set 3 base).set 4 1).set 4 (base + 1)).set 5 (2 ^ (w₀ - 1) - 1)).set 6 1

/-- 4-instruction setup for the bottom-seed `Tabulation.randFillLoop` call on `Data 240`. -/
@[expose] def resampleSetup2Code (w₀ b b' k : ℕ) : Code .exact 240 :=
  let t := reducedTrinomialStep w₀ b b'
  let c := reducedChunkBits t
  let L := reducedLimbCount t
  .seq (.op (.copy 3 4))
  (.seq (.op (.const 5 (k * L)))
  (.seq (.op (.exactBin .add 4 4 5))
        (.op (.const 5 (2 ^ c - 1)))))

/-- State after `resampleSetup2Code w₀ b b' k`. -/
@[expose] def resampleSetup2Data (base w₀ b b' k : ℕ) (x : Data 240) : Data 240 :=
  let t := reducedTrinomialStep w₀ b b'
  let c := reducedChunkBits t
  let L := reducedLimbCount t
  (((x.set 3 (base + 1)).set 5 (k * L)).set 4 (base + 1 + k * L)).set 5 (2 ^ c - 1)

/-- Structured Word-RAM program on `Data 240` that resamples both `α` and `β` via two sequential
`Tabulation.randFillLoop` calls. -/
@[expose] def resampleCode (w₀ b b' k : ℕ) : Code .exact 240 :=
  .seq (resampleSetup1Code w₀)
  (.seq (Tabulation.randFillLoop.rename fillMap240)
  (.seq (resampleSetup2Code w₀ b b' k)
        (Tabulation.randFillLoop.rename fillMap240)))

/-- Exact instruction count `5 * seedWords w₀ b b' k + 13` of `resampleCode w₀ b b' k`. -/
@[expose] def resampleSteps (w₀ b b' k : ℕ) : ℕ :=
  5 * seedWords w₀ b b' k + 13

/-- Explicit `ProbComp (Data 240 × ℕ)` induced by `resampleCode w₀ b b' k`. -/
@[expose] noncomputable def resampleComp (base w₀ b b' k : ℕ) (x : Data 240) :
    ProbComp (Data 240 × ℕ) := do
  let t := reducedTrinomialStep w₀ b b'
  let c := reducedChunkBits t
  let L := reducedLimbCount t
  let x1 := resampleSetup1Data base w₀ x
  let z1 ← Tabulation.randFillComp (w₀ - 1) base 1 (x1.comap fillMap240)
  let x2 := resampleSetup2Data base w₀ b b' k (z1.1.extend fillMap240 x1)
  let z2 ← Tabulation.randFillComp c (base + 1) (k * L) (x2.comap fillMap240)
  pure (z2.1.extend fillMap240 x2, 5 + (z1.2 + (4 + z2.2)))

private theorem resampleSetup1Code_exec {w base w₀ : ℕ} {x : Data 240}
    (hbase : x.regs 0 = base)
    (hfit_top : Fits w (base + 1))
    (hfit_mask_top : Fits w (2 ^ (w₀ - 1) - 1)) :
    Exec w (resampleSetup1Code w₀) x (resampleSetup1Data base w₀ x) 5 := by
  unfold resampleSetup1Code resampleSetup1Data
  wram_exec [hbase]

private theorem resampleSetup2Code_exec {w base w₀ b b' k : ℕ} {x : Data 240}
    (h4 : x.regs 4 = base + 1)
    (hfit_end : Fits w (base + 1 + k * reducedLimbCount (reducedTrinomialStep w₀ b b')))
    (hfit_mask_c : Fits w (2 ^ reducedChunkBits (reducedTrinomialStep w₀ b b') - 1)) :
    Exec w (resampleSetup2Code w₀ b b' k) x (resampleSetup2Data base w₀ b b' k x) 4 := by
  unfold resampleSetup2Code resampleSetup2Data
  wram_exec [h4]

private theorem randFill_rename_execRand {w bits arrBase len : ℕ} {x : Data 240}
    (hptr : x.regs 3 = arrBase) (hend : x.regs 4 = arrBase + len)
    (hmask : x.regs 5 = 2 ^ bits - 1) (hone : x.regs 6 = 1)
    (hfit_end : Fits w (arrBase + len)) (hfit_mask : Fits w (2 ^ bits - 1)) :
    ExecRand w (Tabulation.randFillLoop.rename fillMap240) x
      ((fun z : Data 6 × ℕ => (z.1.extend fillMap240 x, z.2)) <$>
        Tabulation.randFillComp bits arrBase len (x.comap fillMap240)) :=
  (Tabulation.randFillLoop_execRand len hptr hend hmask hone hfit_end hfit_mask).rename
    injective_fillMap240

/-- **Exact `ExecRand` execution of `resampleCode w₀ b b' k`**. -/
theorem resampleCode_execRand {w base w₀ b b' k : ℕ} {x : Data 240}
    (hbase : x.regs 0 = base)
    (hw₀ : w₀ ≤ w)
    (hc : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') ≤ w)
    (hfit_space : Fits w (base + space w w₀ b b' k)) :
    ExecRand w (resampleCode w₀ b b' k) x (resampleComp base w₀ b b' k x) := by
  set t := reducedTrinomialStep w₀ b b'
  set c := reducedChunkBits t
  set L := reducedLimbCount t
  have hfit_end : Fits w (base + 1 + k * L) := by wram_omega
  have hfit_top : Fits w (base + 1) := by fits
  have hfit_mtop : Fits w (2 ^ (w₀ - 1) - 1) := fits_mask_of_le (by omega)
  have hfit_mc : Fits w (2 ^ c - 1) := fits_mask_of_le (by omega)
  have h1 := resampleSetup1Code_exec hbase hfit_top hfit_mtop
  have hloop1 := randFill_rename_execRand (w := w) (bits := w₀ - 1) (arrBase := base) (len := 1)
    (x := resampleSetup1Data base w₀ x)
    (by wram_simp [resampleSetup1Data]) (by wram_simp [resampleSetup1Data])
    (by wram_simp [resampleSetup1Data]) (by wram_simp [resampleSetup1Data])
    hfit_top hfit_mtop
  have hseq12 := ExecRand.seq
    (m₂ := fun z : Data 240 => (fun z2 : Data 6 × ℕ =>
      (z2.1.extend fillMap240 (resampleSetup2Data base w₀ b b' k z), 4 + z2.2)) <$>
        Tabulation.randFillComp c (base + 1) (k * L)
          ((resampleSetup2Data base w₀ b b' k z).comap fillMap240))
    hloop1 fun z hz => by
      obtain ⟨z1, hz1, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
      obtain ⟨_, _, hend1, _, hone1, _, _, _⟩ := Tabulation.mem_support_randFillComp hz1
      have hy4 : (z1.1.extend fillMap240 (resampleSetup1Data base w₀ x)).regs 4 = base + 1 := by
        rw [Data.extend_regs_of_eq injective_fillMap240 _ _ Tabulation.regEnd 4 rfl, hend1]
        change (resampleSetup1Data base w₀ x).regs 4 = base + 1; wram_simp [resampleSetup1Data]
      have hy6 : (z1.1.extend fillMap240 (resampleSetup1Data base w₀ x)).regs 6 = 1 := by
        rw [Data.extend_regs_of_eq injective_fillMap240 _ _ Tabulation.regOne 6 rfl, hone1]
        change (resampleSetup1Data base w₀ x).regs 6 = 1; wram_simp [resampleSetup1Data]
      simpa only [bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def] using
        (resampleSetup2Code_exec hy4 hfit_end hfit_mc).seqRand <|
          randFill_rename_execRand (by wram_simp [resampleSetup2Data])
            (by wram_simp [resampleSetup2Data, L, t]) (by wram_simp [resampleSetup2Data, c, t])
            (by wram_simp [resampleSetup2Data, hy6]) hfit_end hfit_mc
  simpa only [resampleCode, resampleComp, bind_assoc, pure_bind, map_eq_bind_pure_comp,
    Function.comp_def] using h1.seqRand hseq12

/-- Pathwise postcondition of `resampleComp`: executes in `resampleSteps w₀ b b' k` instructions,
preserves `reg 0 = base` and `TableRep`, establishes `SeedRep`, and modifies only
`[base, base + seedWords w₀ b b' k)`. -/
theorem mem_support_resampleComp {base w w₀ b b' k : ℕ} {x : Data 240}
    (hbase : x.regs 0 = base)
    (htab : TableRep base w w₀ b b' k x.mem)
    {z : Data 240 × ℕ}
    (hz : z ∈ (resampleComp base w₀ b b' k x).support) :
    z.1.regs 0 = base ∧
    TableRep base w w₀ b b' k z.1.mem ∧
    SeedRep base w₀ b b' k (extractSeed base w₀ b b' k z.1.mem) z.1.mem ∧
    (∀ a, (a < base ∨ base + seedWords w₀ b b' k ≤ a) → z.1.mem a = x.mem a) ∧
    z.2 = resampleSteps w₀ b b' k := by
  dsimp only [resampleComp] at hz
  obtain ⟨z1, hz1, hr⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
  obtain ⟨z2, hz2, hpure⟩ := OracleComp.mem_supportWith_bind_iff.mp hr
  cases OracleComp.eq_of_mem_supportWith_pure hpure
  obtain ⟨hsteps1, _, _, _, _, hextra1, hlt1, hframe1⟩ := Tabulation.mem_support_randFillComp hz1
  obtain ⟨hsteps2, _, _, _, _, hextra2, hlt2, hframe2⟩ := Tabulation.mem_support_randFillComp hz2
  have hreg0 : (z2.1.extend fillMap240
      (resampleSetup2Data base w₀ b b' k
        (z1.1.extend fillMap240 (resampleSetup1Data base w₀ x)))).regs 0 = base := by
    rw [Data.extend_regs_of_eq injective_fillMap240 _ _ Tabulation.regExtra 0 rfl, hextra2]
    change (z1.1.extend fillMap240 (resampleSetup1Data base w₀ x)).regs 0 = base
    rw [Data.extend_regs_of_eq injective_fillMap240 _ _ Tabulation.regExtra 0 rfl, hextra1]
    exact hbase
  have hframe : ∀ a, (a < base ∨ base + seedWords w₀ b b' k ≤ a) → z2.1.mem a = x.mem a :=
    fun a ha => (hframe2 a (by wram_omega)).trans (hframe1 a (by wram_omega))
  have htab' : TableRep base w w₀ b b' k z2.1.mem :=
    tableRep_congr_on_tab htab fun _ _ => (hframe _ (Or.inr (by wram_omega))).symm
  refine ⟨hreg0, htab', ⟨?_, fun j m => ?_⟩, hframe, by dsimp [resampleSteps, seedWords]; omega⟩
  · have hm_eq : z2.1.mem base = z1.1.mem base := hframe2 base (Or.inl (by omega))
    have hlt_val : z1.1.mem base < 2 ^ (w₀ - 1) := by simpa using hlt1 0 Nat.one_pos
    change z2.1.mem base = (extractTop base w₀ z2.1.mem).val
    rw [extractTop_val, hm_eq, Cslib.WordRAM.wordOfNat_val_of_lt hlt_val]
  · change z2.1.mem _ = getLimb _ (extractBot base w₀ b b' k z2.1.mem j).val m.val
    rw [getLimb_extractBot_val,
      Cslib.WordRAM.wordOfNat_val_of_lt (hlt2 _ (by stride_omega [j.isLt, m.isLt]))]

private theorem map_equiv_randFill {α : Type*} [Fintype α] [Nonempty α]
    (bits arrBase len : ℕ) (x : Data 6) (e : (Fin len → Fin (2 ^ bits)) ≃ α) :
    (Tabulation.randFillComp bits arrBase len x).eval.map
        (fun z => e (Tabulation.extractSlice arrBase bits len z.1.mem)) =
      PMF.uniformOfFintype α := by
  change ((Tabulation.randFillComp bits arrBase len x).eval.map
    (e ∘ fun z : Data 6 × ℕ => Tabulation.extractSlice arrBase bits len z.1.mem)) = _
  rw [← PMF.map_comp, Tabulation.map_extractSlice_eval_randFillComp,
    PMF.uniformOfFintype_map_equiv]

/-- **Exact product uniformity of `resampleComp`**: `extractSeed base w₀ b b' k z.1.mem` under
`resampleComp base w₀ b b' k x` has distribution
`PMF.uniformOfFintype (ReducedPolySeed w₀ b b' k)`. -/
theorem map_extractSeed_eval_resampleComp (base w₀ b b' k : ℕ) (x : Data 240) :
    ((resampleComp base w₀ b b' k x).eval).map (fun z => extractSeed base w₀ b b' k z.1.mem) =
      PMF.uniformOfFintype (ReducedPolySeed w₀ b b' k) := by
  dsimp only [resampleComp]
  rw [ProbComp.eval_bind, PMF.map_bind, ← PMF.uniformOfFintype_prod,
    ← map_equiv_randFill (w₀ - 1) base 1 ((resampleSetup1Data base w₀ x).comap fillMap240)
      (topSliceEquiv w₀), PMF.bind_map]
  congr 1; funext z1
  set x2 := resampleSetup2Data base w₀ b b' k
    (z1.1.extend fillMap240 (resampleSetup1Data base w₀ x))
  rw [bind_pure_comp, ProbComp.eval_map, PMF.map_comp]
  trans ((Tabulation.randFillComp (reducedChunkBits (reducedTrinomialStep w₀ b b')) (base + 1)
      (k * reducedLimbCount (reducedTrinomialStep w₀ b b')) (x2.comap fillMap240)).eval.map
      ((extractTop base w₀ z1.1.mem, ·) ∘
        fun z2 : Data 6 × ℕ => extractBot base w₀ b b' k z2.1.mem))
  · refine Cslib.Probability.PMF.map_congr_on_support _ _ _ fun z2 hz2 => ?_
    rw [ProbComp.support_eval] at hz2
    obtain ⟨_, _, _, _, _, _, _, hframe2⟩ := Tabulation.mem_support_randFillComp hz2
    change (extractTop base w₀ z2.1.mem, extractBot base w₀ b b' k z2.1.mem) =
      (extractTop base w₀ z1.1.mem, extractBot base w₀ b b' k z2.1.mem)
    congr 1; dsimp only [extractTop]; congr 1 with idx
    dsimp only [Tabulation.extractSlice]
    rw [hframe2 (base + idx.val) (Or.inl (by have := idx.isLt; omega))]; rfl
  · rw [← PMF.map_comp]
    dsimp only [extractBot]
    rw [map_equiv_randFill _ (base + 1) _ _ (botSliceEquiv w₀ b b' k)]; rfl

/-! ## Section 4: Word-RAM `evalCode` and deterministic execution -/

/-- Ascending sequential composition of `n` blocks `f 0, f 1, ..., f (n - 1)`. -/
@[expose] def seqAsc (f : ℕ → Code .exact 240) : ℕ → Code .exact 240
  | 0 => .op (.copy 0 0)
  | n + 1 => .seq (seqAsc f n) (f n)

private theorem seqAsc_exec {w : ℕ} (f : ℕ → Code .exact 240) (step : ℕ)
    (P : ℕ → Data 240 → Prop) (n : ℕ)
    (hstep : ∀ i < n, ∀ x : Data 240, P i x → ∃ y, Exec w (f i) x y step ∧ P (i + 1) y)
    {x : Data 240} (hx : P 0 x) :
    ∃ y, Exec w (seqAsc f n) x y (n * step + 1) ∧ P n y := by
  induction n with
  | zero =>
    have hxself : x.set 0 (x.regs 0) = x := by cases x; simp [Data.set]
    exact ⟨x, by simpa only [seqAsc, Nat.zero_mul, Nat.zero_add, hxself] using
      (Exec.copy (B := .exact) (w := w) (d := 0) (s := 0) (x := x)), hx⟩
  | succ n ih =>
    obtain ⟨y, hy_exec, hy_P⟩ := ih fun i hi => hstep i (Nat.lt_succ_of_lt hi)
    obtain ⟨z, hz_exec, hz_P⟩ := hstep n (Nat.lt_succ_self n) y hy_P
    exact ⟨z, (show (n * step + 1) + step = (n + 1) * step + 1 by ring) ▸ hy_exec.seq hz_exec, hz_P⟩

@[local wram_simps]
private theorem set_lit_regs_xReg (x : Data 240) (n m v : ℕ) [OfNat (Fin 240) n]
    (h : (@OfNat.ofNat (Fin 240) n _).val < 20) :
    (x.set (no_index (OfNat.ofNat n)) v).regs (xReg m) = x.regs (xReg m) :=
  Data.set_regs_of_ne (Fin.ne_of_val_ne (by change 20 + m % 54 ≠ _; omega)) v

@[local wram_simps]
private theorem set_xReg_regs_lit (x : Data 240) (n m v : ℕ) [OfNat (Fin 240) n]
    (h : (@OfNat.ofNat (Fin 240) n _).val < 20) :
    (x.set (xReg m) v).regs (no_index (OfNat.ofNat n)) = x.regs (OfNat.ofNat n) :=
  Data.set_regs_of_ne (Fin.ne_of_val_ne (by change _ ≠ 20 + m % 54; omega)) v

@[local wram_simps]
private theorem set_lit_regs_accReg (x : Data 240) (n m v : ℕ) [OfNat (Fin 240) n]
    (h : (@OfNat.ofNat (Fin 240) n _).val < 20) :
    (x.set (no_index (OfNat.ofNat n)) v).regs (accReg m) = x.regs (accReg m) :=
  Data.set_regs_of_ne (Fin.ne_of_val_ne (by change 74 + m % 54 ≠ _; omega)) v

@[local wram_simps]
private theorem set_accReg_regs_lit (x : Data 240) (n m v : ℕ) [OfNat (Fin 240) n]
    (h : (@OfNat.ofNat (Fin 240) n _).val < 20) :
    (x.set (accReg m) v).regs (no_index (OfNat.ofNat n)) = x.regs (OfNat.ofNat n) :=
  Data.set_regs_of_ne (Fin.ne_of_val_ne (by change _ ≠ 74 + m % 54; omega)) v

@[local wram_simps]
private theorem set_lit_regs_prodReg (x : Data 240) (n d v : ℕ) [OfNat (Fin 240) n]
    (h : (@OfNat.ofNat (Fin 240) n _).val < 20) :
    (x.set (no_index (OfNat.ofNat n)) v).regs (prodReg d) = x.regs (prodReg d) :=
  Data.set_regs_of_ne (Fin.ne_of_val_ne (by change 128 + d % 108 ≠ _; omega)) v

@[local wram_simps]
private theorem set_prodReg_regs_lit (x : Data 240) (n d v : ℕ) [OfNat (Fin 240) n]
    (h : (@OfNat.ofNat (Fin 240) n _).val < 20) :
    (x.set (prodReg d) v).regs (no_index (OfNat.ofNat n)) = x.regs (OfNat.ofNat n) :=
  Data.set_regs_of_ne (Fin.ne_of_val_ne (by change _ ≠ 128 + d % 108; omega)) v

/-- Part 1a of Stage 1 (`12` instructions): loads `α = x.mem (x.regs 0)`, sets half-width masks and
shifts in `regs 5..10`, and splits `α` and `x' = x.regs 1 &&& (2 ^ m - 1)` into `regs 12..15`. -/
@[expose] def halfMulSetupCode (m : ℕ) : Code .exact 240 :=
  let h := m / 2
  .seq (.op (.load 4 0))
  (.seq (.op (.const 5 (2 ^ m - 1)))
  (.seq (.op (.const 6 h))
  (.seq (.op (.const 7 (2 ^ h - 1)))
  (.seq (.op (.const 8 (2 ^ (m - h) - 1)))
  (.seq (.op (.const 9 (2 ^ (m - 2 * h) - 1)))
  (.seq (.op (.const 10 (2 * h)))
  (.seq (.op (.exactBin .and 11 1 5))
  (.seq (.op (.exactBin .and 12 4 7))
  (.seq (.op (.exactBin .shiftRight 13 4 6))
  (.seq (.op (.exactBin .and 14 11 7))
        (.op (.exactBin .shiftRight 15 11 6))))))))))))

/-- Part 1b of Stage 1 (`18` instructions): combines the half-words in `regs 12..15` into
`halfMulMod m α x'` in `reg 3`. -/
@[expose] def halfMulCombineCode : Code .exact 240 :=
  .seq (.op (.exactBin .mul 3 12 14))
  (.seq (.op (.exactBin .and 3 3 5))
  (.seq (.op (.exactBin .mul 16 12 15))
  (.seq (.op (.exactBin .and 16 16 8))
  (.seq (.op (.exactBin .shiftLeft 16 16 6))
  (.seq (.op (.exactBin .add 3 3 16))
  (.seq (.op (.exactBin .and 3 3 5))
  (.seq (.op (.exactBin .mul 16 13 14))
  (.seq (.op (.exactBin .and 16 16 8))
  (.seq (.op (.exactBin .shiftLeft 16 16 6))
  (.seq (.op (.exactBin .add 3 3 16))
  (.seq (.op (.exactBin .and 3 3 5))
  (.seq (.op (.exactBin .and 13 13 9))
  (.seq (.op (.exactBin .and 15 15 9))
  (.seq (.op (.exactBin .mul 16 13 15))
  (.seq (.op (.exactBin .shiftLeft 16 16 10))
  (.seq (.op (.exactBin .add 3 3 16))
        (.op (.exactBin .and 3 3 5))))))))))))))))))

/-- Part 1c of Stage 1 (`9` instructions): finishes `oddMulModWord w₀ α u` and shifts right by
`w₀ - min w₀ (3 * b)` into `reg 3`. -/
@[expose] def finishReduceCode (w₀ b : ℕ) : Code .exact 240 :=
  .seq (.op (.const 6 1))
  (.seq (.op (.exactBin .shiftRight 11 1 6))
  (.seq (.op (.exactBin .add 3 11 3))
  (.seq (.op (.exactBin .and 3 3 5))
  (.seq (.op (.exactBin .shiftLeft 3 3 6))
  (.seq (.op (.exactBin .and 11 1 6))
  (.seq (.op (.exactBin .add 3 11 3))
  (.seq (.op (.const 6 (w₀ - min w₀ (3 * b))))
        (.op (.exactBin .shiftRight 3 3 6)))))))))

/-- Stage 1 of `evalCode` (`39` instructions): computes the multiply-shift reduced key
`oddMulModWord w₀ α u >>> (w₀ - min w₀ (3 * b))` into `reg 3`. -/
@[expose] def reduceKeyCode (w₀ b : ℕ) : Code .exact 240 :=
  .seq (halfMulSetupCode (w₀ - 1))
  (.seq halfMulCombineCode (finishReduceCode w₀ b))

/-- Stage 1 execution: computes
`oddMulModWord w₀ (x.mem (x.regs 0)) (x.regs 1) >>> (w₀ - min w₀ (3 * b))`
into `reg 3` in `39` steps, preserving `reg 0` and memory. -/
theorem reduceKeyCode_exec {w w₀ b : ℕ} (hw₀_pos : 0 < w₀) (hw₀ : w₀ ≤ w) (x : Data 240)
    (hα : x.mem (x.regs 0) < 2 ^ (w₀ - 1)) (hu : x.regs 1 < 2 ^ w₀) :
    ∃ y, Exec w (reduceKeyCode w₀ b) x y 39 ∧
      y.regs 0 = x.regs 0 ∧
      y.regs 3 = oddMulModWord w₀ (x.mem (x.regs 0)) (x.regs 1) >>> (w₀ - min w₀ (3 * b)) ∧
      y.mem = x.mem := by
  have hpow_w0 : 2 ^ w₀ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hw₀
  have hpow_m : 2 ^ (w₀ - 1) < 2 ^ w₀ := Nat.pow_lt_pow_right one_lt_two (by omega)
  have hα_w : x.mem (x.regs 0) < 2 ^ w₀ := hα.trans hpow_m
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hodd⟩ := oddMulModWord_parts_lt hw₀_pos hα hu
  wram_exec [reduceKeyCode, halfMulSetupCode, halfMulCombineCode, finishReduceCode]
  wram_simp [oddMulModWord, halfMulMod]

/-- Step `m` of Stage 2 (`5` instructions): extracts limb `m` of `r_val` from `reg 3` into `xReg m`,
shifts `reg 3` right by `c`, and zeroes `accReg m`. -/
@[expose] def initLimbStep (c m : ℕ) : Code .exact 240 :=
  .seq (.op (.const 10 c))
  (.seq (.op (.const 11 (2 ^ c - 1)))
  (.seq (.op (.exactBin .and (xReg m) 3 11))
  (.seq (.op (.exactBin .shiftRight 3 3 10))
        (.op (.const (accReg m) 0)))))

/-- Stage 2a of `evalCode`: extracts all `L` limbs of the reduced key into `xReg 0 .. xReg (L - 1)`
and zeroes `accReg 0 .. accReg (L - 1)`. -/
@[expose] def initLimbsCode (t : ℕ) : Code .exact 240 :=
  seqAsc (initLimbStep (reducedChunkBits t)) (reducedLimbCount t)

private theorem initLimbsCode_exec {w t r_val : ℕ} (hc_lt : 2 * reducedChunkBits t < w)
    (hr : r_val < 2 ^ w) (x : Data 240) (h3 : x.regs 3 = r_val) :
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    ∃ y, Exec w (initLimbsCode t) x y (L * 5 + 1) ∧
      y.regs 0 = x.regs 0 ∧
      (∀ m < L, y.regs (xReg m) = getLimb c r_val m) ∧
      (∀ m < L, y.regs (accReg m) = 0) ∧
      y.mem = x.mem := by
  intro c L
  have hL_le : L ≤ 54 := reducedLimbCount_le t
  have hfit_c : Fits w c := by stride_omega
  have hfit_mask_c : Fits w (2 ^ c - 1) := by stride_omega
  let P (n : ℕ) (z : Data 240) : Prop :=
    z.regs 0 = x.regs 0 ∧ z.regs 3 = r_val >>> (n * c) ∧
    (∀ m < n, z.regs (xReg m) = getLimb c r_val m) ∧
    (∀ m < n, z.regs (accReg m) = 0) ∧ z.mem = x.mem
  obtain ⟨y, hy_exec, hy0, _, hyx, hya, hymem⟩ :=
    seqAsc_exec (w := w) (initLimbStep c) 5 P L (fun i hi z ⟨hz0, hz3, hzx, hza, hzmem⟩ => by
      have hi54 : i < 54 := hi.trans_le hL_le
      have hfit_limb : Fits w (getLimb c r_val i) := by stride_omega [getLimb_lt c r_val i]
      have hfit_shr : Fits w (r_val >>> ((i + 1) * c)) := (Nat.shiftRight_le _ _).trans_lt hr
      wram_exec [initLimbStep,
        hz3, show (r_val >>> (i * c)) &&& (2 ^ c - 1) = getLimb c r_val i from rfl,
        show (r_val >>> (i * c)) >>> c = r_val >>> ((i + 1) * c) by
          rw [← Nat.shiftRight_add, ← Nat.succ_mul]]
      refine ⟨by wram_simp [hz0], by wram_simp, fun m hm => ?_, fun m hm => ?_, hzmem⟩
      · rcases eq_or_ne m i with rfl | hne <;> wram_simp [hzx]
      · rcases eq_or_ne m i with rfl | hne <;> wram_simp [hza])
      ⟨rfl, by rw [Nat.zero_mul, Nat.shiftRight_zero, h3], fun _ hm => by omega,
        fun _ hm => by omega, rfl⟩
  exact ⟨y, hy_exec, hy0, hyx, hya, hymem⟩

/-- Stage 2b of `evalCode` (`8` instructions): loads table/chunk constants into `regs 4..9` and
`reg 18`. -/
@[expose] def hornerSetupCode (w w₀ b b' k : ℕ) : Code .exact 240 :=
  let t := reducedTrinomialStep w₀ b b'
  let c := reducedChunkBits t
  let p := reducedPackShift t w
  .seq (.op (.const 4 (seedWords w₀ b b' k)))
  (.seq (.op (.exactBin .add 4 0 4))
  (.seq (.op (.const 5 c))
  (.seq (.op (.const 6 (2 ^ c - 1)))
  (.seq (.op (.const 7 p))
  (.seq (.op (.const 8 (2 ^ p - 1)))
  (.seq (.op (.const 9 (2 * c)))
        (.op (.const 18 (2 ^ (2 * c) - 1)))))))))

private theorem hornerSetupCode_exec {w base w₀ b b' k : ℕ}
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + space w w₀ b b' k))
    (x : Data 240) (h0 : x.regs 0 = base) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let p := reducedPackShift t w
    ∃ y, Exec w (hornerSetupCode w w₀ b b' k) x y 8 ∧
      y.regs 0 = base ∧
      y.regs 4 = tabBase base w₀ b b' k ∧
      y.regs 5 = c ∧
      y.regs 6 = 2 ^ c - 1 ∧
      y.regs 7 = p ∧
      y.regs 8 = 2 ^ p - 1 ∧
      y.regs 9 = 2 * c ∧
      y.regs 18 = 2 ^ (2 * c) - 1 ∧
      (∀ r : Fin 240, 20 ≤ r.val → y.regs r = x.regs r) ∧
      y.mem = x.mem := by
  intro t c p
  obtain ⟨hfit_2c, hfit_s, hfit_tBase, hfit_c, hfit_mask_c, hfit_p, hfit_mask_p, hfit_2c_val⟩ :=
    tableSetup_fits hc_lt hfit_space
  simp only [t, c, p] at *
  wram_exec [hornerSetupCode, h0, show base + seedWords w₀ b b' k = tabBase base w₀ b b' k from rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl⟩ <;> wram_simp [h0, t, c, p]

/-- Register invariant preserved across all Stage 3 Horner operations. -/
@[expose] def HornerConsts (base w w₀ b b' k r_val : ℕ) (x : Data 240) : Prop :=
  let t := reducedTrinomialStep w₀ b b'
  let c := reducedChunkBits t
  let p := reducedPackShift t w
  let L := reducedLimbCount t
  x.regs 0 = base ∧
  x.regs 4 = tabBase base w₀ b b' k ∧
  x.regs 5 = c ∧
  x.regs 6 = 2 ^ c - 1 ∧
  x.regs 7 = p ∧
  x.regs 8 = 2 ^ p - 1 ∧
  x.regs 9 = 2 * c ∧
  x.regs 18 = 2 ^ (2 * c) - 1 ∧
  ∀ m < L, x.regs (xReg m) = getLimb c r_val m

private theorem HornerConsts.congr {base w w₀ b b' k r_val : ℕ} {x y : Data 240}
    (hc : HornerConsts base w w₀ b b' k r_val x)
    (hregs : ∀ r : Fin 240, (r.val < 10 ∨ r.val = 18 ∨ (20 ≤ r.val ∧ r.val < 74)) →
      y.regs r = x.regs r) :
    HornerConsts base w w₀ b b' k r_val y := by
  obtain ⟨h0, h4, h5, h6, h7, h8, h9, h18, hx⟩ := hc
  exact ⟨(hregs 0 (by decide)).trans h0, (hregs 4 (by decide)).trans h4,
    (hregs 5 (by decide)).trans h5, (hregs 6 (by decide)).trans h6,
    (hregs 7 (by decide)).trans h7, (hregs 8 (by decide)).trans h8,
    (hregs 9 (by decide)).trans h9, (hregs 18 (by decide)).trans h18,
    fun m hm => (hregs (xReg m) (by dsimp [xReg]; omega)).trans (hx m hm)⟩

/-- Invariant combining `HornerConsts` and the current accumulator limbs in `accReg`. -/
@[expose] def ClmulInv (base w w₀ b b' k r_val acc_val : ℕ) (x : Data 240) : Prop :=
  let t := reducedTrinomialStep w₀ b b'
  let c := reducedChunkBits t
  let L := reducedLimbCount t
  HornerConsts base w w₀ b b' k r_val x ∧
  ∀ m < L, x.regs (accReg m) = getLimb c acc_val m

private theorem ClmulInv.congr {base w w₀ b b' k r_val acc_val : ℕ} {x y : Data 240}
    (h : ClmulInv base w w₀ b b' k r_val acc_val x)
    (hregs : ∀ r : Fin 240, (r.val < 10 ∨ r.val = 18 ∨ (20 ≤ r.val ∧ r.val < 128)) →
      y.regs r = x.regs r) :
    ClmulInv base w w₀ b b' k r_val acc_val y :=
  ⟨h.1.congr fun r hr => hregs r (hr.imp id (Or.imp id fun ⟨h1, h2⟩ => ⟨h1, by omega⟩)),
    fun m hm => (hregs (accReg m) (by dsimp [accReg]; omega)).trans (h.2 m hm)⟩

/-- Zeroes `prodReg 0 .. prodReg (2 * L - 1)`. -/
@[expose] def zeroProdCode (L : ℕ) : Code .exact 240 :=
  seqAsc (fun d => .op (.const (prodReg d) 0)) (2 * L)

private theorem packLimbs_zero_fn (c n : ℕ) : packLimbs c n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [packLimbs, ih]

private theorem zeroProdCode_exec {base w w₀ b b' k r_val acc_val : ℕ}
    (x : Data 240) (hinv : ClmulInv base w w₀ b b' k r_val acc_val x) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    ∃ y, Exec w (zeroProdCode L) x y (2 * L * 1 + 1) ∧
      ClmulInv base w w₀ b b' k r_val acc_val y ∧
      (∀ d < 2 * L, y.regs (prodReg d) < 2 ^ c) ∧
      packLimbs c (2 * L) (fun d => y.regs (prodReg d)) = 0 ∧
      y.mem = x.mem := by
  intro t c L
  have hL_le : L ≤ 54 := reducedLimbCount_le t
  let P (n : ℕ) (z : Data 240) : Prop :=
    ClmulInv base w w₀ b b' k r_val acc_val z ∧ (∀ d < n, z.regs (prodReg d) = 0) ∧ z.mem = x.mem
  obtain ⟨y, hy_exec, hy_inv, hy_zero, hy_mem⟩ :=
    seqAsc_exec (w := w) (fun d => .op (.const (prodReg d) 0)) 1 P (2 * L)
      (fun i hi z ⟨hz_inv, hz_zero, hz_mem⟩ => by
        have hi108 : i < 108 := by omega
        wram_exec
        refine ⟨hz_inv.congr fun r hr => by wram_simp, fun d hd => ?_, hz_mem⟩
        rcases eq_or_ne d i with rfl | hne
        · wram_simp
        · wram_simp [hz_zero d (by omega)])
      ⟨hinv, fun _ hd => by omega, rfl⟩
  exact ⟨y, hy_exec, hy_inv, fun d hd => by rw [hy_zero d hd]; exact Nat.two_pow_pos c,
    by rw [packLimbs_congr (g := fun _ => 0) hy_zero, packLimbs_zero_fn], hy_mem⟩

/-- Inner step `(i, m)` (`13` instructions): looks up `clmul (accLimb i) (xLimb m)` in the
bit-packed Four-Russians table and XORs its low and high `c`-bit halves into `prodReg (i + m)` and
`prodReg (i + m + 1)`. -/
@[expose] def innerClmulStep (i m : ℕ) : Code .exact 240 :=
  .seq (.op (.exactBin .shiftLeft 10 (accReg i) 5))
  (.seq (.op (.exactBin .add 10 10 (xReg m)))
  (.seq (.op (.exactBin .shiftRight 11 10 7))
  (.seq (.op (.exactBin .add 11 4 11))
  (.seq (.op (.load 12 11))
  (.seq (.op (.exactBin .and 11 10 8))
  (.seq (.op (.exactBin .mul 11 11 9))
  (.seq (.op (.exactBin .shiftRight 12 12 11))
  (.seq (.op (.exactBin .and 12 12 18))
  (.seq (.op (.exactBin .and 13 12 6))
  (.seq (.op (.exactBin .shiftRight 14 12 5))
  (.seq (.op (.exactBin .xor (prodReg (i + m)) (prodReg (i + m)) 13))
        (.op (.exactBin .xor (prodReg (i + m + 1)) (prodReg (i + m + 1)) 14)))))))))))))

/-- Row `i` of limb-by-limb carryless multiplication. -/
@[expose] def outerClmulStep (L i : ℕ) : Code .exact 240 :=
  seqAsc (innerClmulStep i) L

/-- Full `L × L` limb-by-limb carryless multiplication into `prodReg 0 .. prodReg (2 * L - 1)`. -/
@[expose] def clmulLimbsCode (L : ℕ) : Code .exact 240 :=
  seqAsc (outerClmulStep L) L

private theorem pair_index_props {c u v : ℕ} (hu : u < 2 ^ c) (hv : v < 2 ^ c) :
    (u <<< c) + v < 2 ^ (2 * c) ∧
    ((u <<< c) + v) >>> c = u ∧
    ((u <<< c) + v) &&& (2 ^ c - 1) = v := by
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod,
    mul_comm u (2 ^ c)]
  refine ⟨?_, by rw [Nat.mul_add_div (Nat.two_pow_pos c), Nat.div_eq_of_lt hv, add_zero],
    by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hv]⟩
  rw [two_mul, pow_add]
  have := Nat.mul_le_mul_left (2 ^ c) hu
  nlinarith

private theorem innerClmulStep_exec {base w w₀ b b' k r_val acc_val i m : ℕ}
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + space w w₀ b b' k))
    (hi : i < reducedLimbCount (reducedTrinomialStep w₀ b b'))
    (hm : m < reducedLimbCount (reducedTrinomialStep w₀ b b'))
    (x : Data 240)
    (hinv : ClmulInv base w w₀ b b' k r_val acc_val x)
    (htab : TableRep base w w₀ b b' k x.mem)
    (hprod_lt : ∀ d < 2 * reducedLimbCount (reducedTrinomialStep w₀ b b'),
      x.regs (prodReg d) < 2 ^ reducedChunkBits (reducedTrinomialStep w₀ b b')) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    let u := getLimb c acc_val i
    let v := getLimb c r_val m
    ∃ y, Exec w (innerClmulStep i m) x y 13 ∧
      ClmulInv base w w₀ b b' k r_val acc_val y ∧
      (∀ d < 2 * L, y.regs (prodReg d) < 2 ^ c) ∧
      packLimbs c (2 * L) (fun d => y.regs (prodReg d)) =
        packLimbs c (2 * L) (fun d => x.regs (prodReg d)) ^^^ (clmul u v <<< ((i + m) * c)) ∧
      y.mem = x.mem := by
  intro t c L u v
  set p := reducedPackShift t w
  set tBase := tabBase base w₀ b b' k
  have hc_pos : 0 < c := reducedChunkBits_pos t
  have hL_le : L ≤ 54 := reducedLimbCount_le t
  have hfit_2c : Fits w (2 ^ (2 * c)) := by stride_omega
  have hpow_c_lt : 2 ^ c < 2 ^ w := by stride_omega
  have hpow_pack_le : 2 ^ (2 ^ p * (2 * c)) ≤ 2 ^ w := by
    stride_omega [two_pow_reducedPackShift_mul_le hc_lt.le]
  have hfit_end : Fits w (tBase + reducedTableWords t w) := by wram_omega
  have ⟨⟨_, h4, h5, h6, h7, h8, h9, h18, hxReg⟩, haccReg⟩ := hinv
  have hu_lt : u < 2 ^ c := getLimb_lt c acc_val i
  have hv_lt : v < 2 ^ c := getLimb_lt c r_val m
  obtain ⟨hidx_lt, hidx_u, hidx_v⟩ := pair_index_props hu_lt hv_lt
  set idx := (u <<< c) + v with hidx
  set wIdx := idx >>> p with hwIdx
  set subIdx := idx &&& (2 ^ p - 1) with hsubIdx
  set sh := subIdx * (2 * c) with hsh
  have hwIdx_lt : wIdx < reducedTableWords t w := shiftRight_lt_reducedTableWords hidx_lt
  have hlimb_eq : (x.mem (tBase + wIdx) >>> sh) &&& (2 ^ (2 * c) - 1) = clmul u v := by
    have := htab.2 idx hidx_lt
    dsimp only [getLimb, wIdx, subIdx, sh, tBase] at this ⊢; rw [this, hidx_u, hidx_v]
  have hcl_lt : clmul u v < 2 ^ (2 * c) := clmul_lt_two_pow_two_mul hu_lt hv_lt
  set lo := clmul u v &&& (2 ^ c - 1) with hlo
  set hi_part := clmul u v >>> c with hhi_part
  have hlo_lt : lo < 2 ^ c := and_two_pow_sub_one_lt _ c
  have hhi_lt : hi_part < 2 ^ c := by
    simpa only [two_mul, Nat.add_sub_cancel] using
      shiftRight_lt_pow_sub (by omega : c ≤ 2 * c) hcl_lt
  have him1_lt : i + m + 1 < 2 * L := by change i < L at hi; change m < L at hm; omega
  have hnew0_lt : x.regs (prodReg (i + m)) ^^^ lo < 2 ^ c :=
    Nat.xor_lt_two_pow (hprod_lt (i + m) (by omega)) hlo_lt
  have hnew1_lt : x.regs (prodReg (i + m + 1)) ^^^ hi_part < 2 ^ c :=
    Nat.xor_lt_two_pow (hprod_lt (i + m + 1) him1_lt) hhi_lt
  have hfit_sh : Fits w sh := (packSlot_sh_lt hc_lt.le).trans Nat.lt_two_pow_self
  have _ : Fits w subIdx := hfit_sh.of_le (Nat.le_mul_of_pos_right _ (by omega))
  have _ : Fits w (x.mem (tBase + wIdx) >>> sh) :=
    ((Nat.shiftRight_le _ _).trans_lt (htab.1 wIdx hwIdx_lt)).trans_le hpow_pack_le
  have _ : Fits w (u <<< c) := ((Nat.le_add_right _ _).trans_lt hidx_lt).trans hfit_2c
  have _ : Fits w wIdx := hfit_end.of_le (by omega)
  have _ : Fits w lo := by stride_omega
  have _ : Fits w hi_part := by stride_omega
  have _ : Fits w (x.regs (prodReg (i + m)) ^^^ lo) := by stride_omega
  have _ : Fits w (x.regs (prodReg (i + m + 1)) ^^^ hi_part) := by stride_omega
  have hu_reg : x.regs (accReg i) = u := haccReg i hi
  have hv_reg : x.regs (xReg m) = v := hxReg m hm
  wram_exec [innerClmulStep, show x.regs 4 = tBase from h4, show x.regs 5 = c from h5,
    show x.regs 6 = 2 ^ c - 1 from h6, show x.regs 7 = p from h7,
    show x.regs 8 = 2 ^ p - 1 from h8, show x.regs 9 = 2 * c from h9,
    show x.regs 18 = 2 ^ (2 * c) - 1 from h18, hu_reg, hv_reg,
    ← hidx, ← hwIdx, ← hsubIdx, ← hsh, hlimb_eq, ← hlo, ← hhi_part]
  refine ⟨hinv.congr fun r hr => by wram_simp, fun d hd => ?_, ?_, rfl⟩
  · rcases eq_or_ne d (i + m + 1) with rfl | hne1
    · wram_simp; exact hnew1_lt
    · rcases eq_or_ne d (i + m) with rfl | hne0
      · wram_simp; exact hnew0_lt
      · wram_simp; exact hprod_lt d hd
  · rw [packLimbs_congr (g := Function.update
        (Function.update (fun d => x.regs (prodReg d)) (i + m) (x.regs (prodReg (i + m)) ^^^ lo))
        (i + m + 1) (x.regs (prodReg (i + m + 1)) ^^^ hi_part)) fun d hd => by
      rcases eq_or_ne d (i + m + 1) with rfl | hne1
      · rw [Function.update_self]; wram_simp
      · rw [Function.update_of_ne hne1]
        rcases eq_or_ne d (i + m) with rfl | hne0
        · rw [Function.update_self]; wram_simp
        · rw [Function.update_of_ne hne0]; wram_simp]
    exact packLimbs_update_pair _ him1_lt hcl_lt

private theorem outerClmulStep_exec {base w w₀ b b' k r_val acc_val i : ℕ}
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + space w w₀ b b' k))
    (hi : i < reducedLimbCount (reducedTrinomialStep w₀ b b'))
    (x : Data 240)
    (hinv : ClmulInv base w w₀ b b' k r_val acc_val x)
    (htab : TableRep base w w₀ b b' k x.mem)
    (hprod_lt : ∀ d < 2 * reducedLimbCount (reducedTrinomialStep w₀ b b'),
      x.regs (prodReg d) < 2 ^ reducedChunkBits (reducedTrinomialStep w₀ b b')) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    ∃ y, Exec w (outerClmulStep L i) x y (L * 13 + 1) ∧
      ClmulInv base w w₀ b b' k r_val acc_val y ∧
      (∀ d < 2 * L, y.regs (prodReg d) < 2 ^ c) ∧
      packLimbs c (2 * L) (fun d => y.regs (prodReg d)) =
        packLimbs c (2 * L) (fun d => x.regs (prodReg d)) ^^^
          (clmul (getLimb c acc_val i) (truncLimbs c L r_val) <<< (i * c)) ∧
      y.mem = x.mem := by
  intro t c L
  let P (m : ℕ) (z : Data 240) : Prop :=
    ClmulInv base w w₀ b b' k r_val acc_val z ∧ (∀ d < 2 * L, z.regs (prodReg d) < 2 ^ c) ∧
    packLimbs c (2 * L) (fun d => z.regs (prodReg d)) =
      packLimbs c (2 * L) (fun d => x.regs (prodReg d)) ^^^
        (clmul (getLimb c acc_val i) (truncLimbs c m r_val) <<< (i * c)) ∧ z.mem = x.mem
  exact seqAsc_exec (innerClmulStep i) 13 P L (fun m hm z ⟨hz_inv, hz_lt, hz_pack, hz_mem⟩ => by
    obtain ⟨z', he, hi', hlt', hpk', hm'⟩ :=
      innerClmulStep_exec hc_lt hfit_space hi hm z hz_inv (hz_mem ▸ htab) hz_lt
    exact ⟨z', he, hi', hlt', by rw [hpk', hz_pack, Nat.xor_assoc, ← clmul_truncLimbs_right_succ],
      hm'.trans hz_mem⟩)
    ⟨hinv, hprod_lt, by simp, rfl⟩

private theorem clmulLimbsCode_exec {base w w₀ b b' k r_val acc_val : ℕ}
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + space w w₀ b b' k))
    (hr_lt : r_val < 2 ^ (reducedLimbCount (reducedTrinomialStep w₀ b b') *
      reducedChunkBits (reducedTrinomialStep w₀ b b')))
    (hacc_lt : acc_val < 2 ^ (reducedLimbCount (reducedTrinomialStep w₀ b b') *
      reducedChunkBits (reducedTrinomialStep w₀ b b')))
    (x : Data 240)
    (hinv : ClmulInv base w w₀ b b' k r_val acc_val x)
    (htab : TableRep base w w₀ b b' k x.mem)
    (hprod_lt : ∀ d < 2 * reducedLimbCount (reducedTrinomialStep w₀ b b'),
      x.regs (prodReg d) < 2 ^ reducedChunkBits (reducedTrinomialStep w₀ b b'))
    (hprod_zero : packLimbs (reducedChunkBits (reducedTrinomialStep w₀ b b'))
      (2 * reducedLimbCount (reducedTrinomialStep w₀ b b')) (fun d => x.regs (prodReg d)) = 0) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    ∃ y, Exec w (clmulLimbsCode L) x y (L * (L * 13 + 1) + 1) ∧
      HornerConsts base w w₀ b b' k r_val y ∧
      (∀ d < 2 * L, y.regs (prodReg d) = getLimb c (clmul acc_val r_val) d) ∧
      y.mem = x.mem := by
  intro t c L
  let P (i : ℕ) (z : Data 240) : Prop :=
    ClmulInv base w w₀ b b' k r_val acc_val z ∧ (∀ d < 2 * L, z.regs (prodReg d) < 2 ^ c) ∧
    packLimbs c (2 * L) (fun d => z.regs (prodReg d)) = clmul (truncLimbs c i acc_val) r_val ∧
    z.mem = x.mem
  obtain ⟨y, hy_exec, hy_inv, hy_lt, hy_pack, hy_mem⟩ :=
    seqAsc_exec (outerClmulStep L) (L * 13 + 1) P L
      (fun i hi z ⟨hz_inv, hz_lt, hz_pack, hz_mem⟩ => by
        obtain ⟨z', he, hi', hlt', hpk', hm'⟩ :=
          outerClmulStep_exec hc_lt hfit_space hi z hz_inv (hz_mem ▸ htab) hz_lt
        exact ⟨z', he, hi', hlt',
          by rw [hpk', hz_pack, truncLimbs_of_lt hr_lt, ← clmul_truncLimbs_left_succ],
          hm'.trans hz_mem⟩)
      ⟨hinv, hprod_lt, by rw [hprod_zero, truncLimbs_zero, clmul_zero_left], rfl⟩
  rw [truncLimbs_of_lt hacc_lt] at hy_pack
  exact ⟨y, hy_exec, hy_inv.1,
    fun d hd => by rw [← hy_pack, getLimb_packLimbs_of_lt c hd (hy_lt d hd)], hy_mem⟩

/-- Step `m < 2 * L₀` of trinomial reduction and seed addition (`6` instructions):
loads limb `m` of coefficient `coeffIdx` from memory, reduces the product limbs in `prodReg`
modulo `X ^ (2 * 3 ^ t) + X ^ (3 ^ t) + 1`, and writes the XOR into `accReg m`. -/
@[expose] def reduceAddStep (L₀ coeffIdx m : ℕ) : Code .exact 240 :=
  .seq (.op (.const 10 (1 + (m + 2 * L₀ * coeffIdx))))
  (.seq (.op (.exactBin .add 10 0 10))
  (.seq (.op (.load 11 10))
  (.seq (if m < L₀ then
          .seq (.op (.exactBin .xor 12 (prodReg m) (prodReg (3 * L₀ + m))))
               (.op (.exactBin .xor 12 12 (prodReg (2 * L₀ + m))))
        else
          .seq (.op (.exactBin .xor 12 (prodReg m) (prodReg (L₀ + m))))
               (.op (.copy 12 12)))
        (.op (.exactBin .xor (accReg m) 12 11)))))

/-- Trinomial reduction and seed addition across all `2 * L₀ = L` limbs. -/
@[expose] def reduceAddCode (L₀ coeffIdx : ℕ) : Code .exact 240 :=
  seqAsc (reduceAddStep L₀ coeffIdx) (2 * L₀)

private theorem reduceAddStep_exec {base w w₀ b b' k r_val P_val : ℕ}
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + space w w₀ b b' k))
    (hP_lt : P_val < 2 ^ (2 * reducedLimbCount (reducedTrinomialStep w₀ b b') *
      reducedChunkBits (reducedTrinomialStep w₀ b b')))
    (θ : ReducedPolySeed w₀ b b' k) (coeffIdx : Fin k) (m : ℕ)
    (hm : m < reducedLimbCount (reducedTrinomialStep w₀ b b'))
    (x : Data 240)
    (hc : HornerConsts base w w₀ b b' k r_val x)
    (hseed : SeedRep base w₀ b b' k θ x.mem)
    (hprod : ∀ d < 2 * reducedLimbCount (reducedTrinomialStep w₀ b b'),
      x.regs (prodReg d) = getLimb (reducedChunkBits (reducedTrinomialStep w₀ b b')) P_val d) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    let L₀ := reducedHalfLimbs t
    let newAcc := reduceTrinomialCode t P_val ^^^ (θ.2 coeffIdx).val
    ∃ y, Exec w (reduceAddStep L₀ coeffIdx.val m) x y 6 ∧
      HornerConsts base w w₀ b b' k r_val y ∧
      (∀ d < 2 * L, y.regs (prodReg d) = getLimb c P_val d) ∧
      y.regs (accReg m) = getLimb c newAcc m ∧
      (∀ i < m, y.regs (accReg i) = x.regs (accReg i)) ∧
      y.mem = x.mem := by
  intro t c L L₀ newAcc
  have hL_eq : L = 2 * L₀ := rfl
  have hL_le : L ≤ 54 := reducedLimbCount_le t
  change m < 2 * L₀ at hm
  change ∀ d < 2 * (2 * L₀), x.regs (prodReg d) = getLimb c P_val d at hprod
  have hpow_c_lt : 2 ^ c < 2 ^ w := by stride_omega
  set off := 1 + (m + 2 * L₀ * coeffIdx.val) with hoff
  have hoff_lt : off < seedWords w₀ b b' k := by
    change 1 + (m + L * coeffIdx.val) < 1 + k * L
    stride_omega [coeffIdx.isLt, show m < L from hm]
  have hfit_off : Fits w off := by wram_omega
  have hfit_addr : Fits w (base + off) := by wram_omega
  have h0 : x.regs 0 = base := hc.1
  have hmem_eq : x.mem (base + off) = getLimb c (θ.2 coeffIdx).val m := by
    have hrep := hseed.2 coeffIdx ⟨m, hm⟩
    rwa [show base + off = base + 1 + (m + L * coeffIdx.val) by
      dsimp only [off, L, L₀, reducedLimbCount]; ring]
  set redLimb := getLimb c (reduceTrinomialCode t P_val) m
  have hnew_eq : redLimb ^^^ getLimb c (θ.2 coeffIdx).val m = getLimb c newAcc m :=
    (getLimb_xor c (reduceTrinomialCode t P_val) (θ.2 coeffIdx).val m).symm
  have hfit_red : Fits w redLimb := (getLimb_lt _ _ _).trans hpow_c_lt
  have hfit_new : Fits w (getLimb c newAcc m) := (getLimb_lt _ _ _).trans hpow_c_lt
  have hp_m : x.regs (prodReg m) = getLimb c P_val m := hprod m (by omega)
  unfold reduceAddStep
  split_ifs with hm_low
  on_goal 1 =>
    have hp_3 : x.regs (prodReg (3 * L₀ + m)) = getLimb c P_val (3 * L₀ + m) :=
      hprod (3 * L₀ + m) (by omega)
    have hp_2 : x.regs (prodReg (2 * L₀ + m)) = getLimb c P_val (2 * L₀ + m) :=
      hprod (2 * L₀ + m) (by omega)
    set v1 := getLimb c P_val m ^^^ getLimb c P_val (3 * L₀ + m) with hv1
    have hfit_v1 : Fits w v1 :=
      (Nat.xor_lt_two_pow (getLimb_lt _ _ _) (getLimb_lt _ _ _)).trans hpow_c_lt
    have hred_eq : v1 ^^^ getLimb c P_val (2 * L₀ + m) = redLimb :=
      (getLimb_reduceTrinomialCode_low t P_val hm_low).symm
    wram_exec [h0, ← hoff, hmem_eq, hp_m, hp_3, ← hv1, hp_2, hred_eq, hnew_eq]
  on_goal 2 =>
    have hzero4 : getLimb c P_val (4 * L₀ + (m - L₀)) = 0 :=
      getLimb_eq_zero_of_lt (hP_lt.trans_le (Nat.pow_le_pow_right two_pos
        (Nat.mul_le_mul_right c (by change 2 * (2 * L₀) ≤ _; omega))))
    have hhigh : getLimb c (reduceTrinomialCode t P_val) (L₀ + (m - L₀)) =
        (getLimb c P_val (L₀ + (m - L₀)) ^^^ getLimb c P_val (4 * L₀ + (m - L₀))) ^^^
          getLimb c P_val (2 * L₀ + (m - L₀)) :=
      getLimb_reduceTrinomialCode_high t P_val (by omega)
    rw [Nat.add_sub_of_le (le_of_not_gt hm_low), show 2 * L₀ + (m - L₀) = L₀ + m by omega,
      hzero4, Nat.xor_zero] at hhigh
    change redLimb = getLimb c P_val m ^^^ getLimb c P_val (L₀ + m) at hhigh
    have hp_1 : x.regs (prodReg (L₀ + m)) = getLimb c P_val (L₀ + m) := hprod (L₀ + m) (by omega)
    wram_exec [h0, ← hoff, hmem_eq, hp_m, hp_1, hhigh.symm, hnew_eq]
  all_goals exact ⟨hc.congr fun r hr => by wram_simp, fun d hd => by wram_simp [hprod d hd],
    by wram_simp, fun i hi => by wram_simp, rfl⟩

private theorem reduceAddCode_exec {base w w₀ b b' k r_val P_val : ℕ}
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + space w w₀ b b' k))
    (hP_lt : P_val < 2 ^ (2 * reducedLimbCount (reducedTrinomialStep w₀ b b') *
      reducedChunkBits (reducedTrinomialStep w₀ b b')))
    (θ : ReducedPolySeed w₀ b b' k) (coeffIdx : Fin k) (x : Data 240)
    (hc : HornerConsts base w w₀ b b' k r_val x)
    (hseed : SeedRep base w₀ b b' k θ x.mem)
    (hprod : ∀ d < 2 * reducedLimbCount (reducedTrinomialStep w₀ b b'),
      x.regs (prodReg d) = getLimb (reducedChunkBits (reducedTrinomialStep w₀ b b')) P_val d) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    let L₀ := reducedHalfLimbs t
    let newAcc := reduceTrinomialCode t P_val ^^^ (θ.2 coeffIdx).val
    ∃ y, Exec w (reduceAddCode L₀ coeffIdx.val) x y (L * 6 + 1) ∧
      HornerConsts base w w₀ b b' k r_val y ∧
      (∀ m < L, y.regs (accReg m) = getLimb c newAcc m) ∧
      y.mem = x.mem := by
  intro t c L L₀ newAcc
  let P (n : ℕ) (z : Data 240) : Prop :=
    HornerConsts base w w₀ b b' k r_val z ∧
    (∀ d < 2 * L, z.regs (prodReg d) = getLimb c P_val d) ∧
    (∀ m < n, z.regs (accReg m) = getLimb c newAcc m) ∧ z.mem = x.mem
  obtain ⟨y, hy_exec, hy_hc, _, hy_acc, hy_mem⟩ :=
    seqAsc_exec (reduceAddStep L₀ coeffIdx.val) 6 P L
      (fun m hm z ⟨hz_hc, hz_prod, hz_acc, hz_mem⟩ => by
        obtain ⟨z', he, hc', hp', hm', hprev, hmem'⟩ :=
          reduceAddStep_exec hc_lt hfit_space hP_lt θ coeffIdx m hm z hz_hc (hz_mem ▸ hseed) hz_prod
        exact ⟨z', he, hc', hp', fun i hi => by
          rcases eq_or_ne i m with rfl | hne
          · exact hm'
          · exact (hprev i (by omega)).trans (hz_acc i (by omega)), hmem'.trans hz_mem⟩)
      ⟨hc, hprod, fun _ hm => by omega, rfl⟩
  exact ⟨y, hy_exec, hy_hc, hy_acc, hy_mem⟩

/-- Step `j < k` of Horner polynomial evaluation: multiplies `accReg` by `xReg` into `prodReg`,
reduces modulo the trinomial, and adds coefficient `k - 1 - j`. -/
@[expose] def hornerStep (t k j : ℕ) : Code .exact 240 :=
  let L₀ := reducedHalfLimbs t
  let L := reducedLimbCount t
  .seq (zeroProdCode L)
  (.seq (clmulLimbsCode L) (reduceAddCode L₀ (k - 1 - j)))

/-- Stage 3 of `evalCode`: `k` Horner steps evaluating `polynomialHash`. -/
@[expose] def hornerCode (t k : ℕ) : Code .exact 240 :=
  seqAsc (hornerStep t k) k

/-- Step count of a single `hornerStep t k j`. -/
@[expose] def hornerStepSteps (t : ℕ) : ℕ :=
  let L := reducedLimbCount t
  (2 * L * 1 + 1) + ((L * (L * 13 + 1) + 1) + (L * 6 + 1))

private theorem hornerCode_exec {base w w₀ b b' k : ℕ}
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + space w w₀ b b' k))
    (θ : ReducedPolySeed w₀ b b' k)
    (r : Fin (2 ^ min w₀ (3 * b)))
    (x : Data 240)
    (hc : HornerConsts base w w₀ b b' k r.val x)
    (htab : TableRep base w w₀ b b' k x.mem)
    (hseed : SeedRep base w₀ b b' k θ x.mem)
    (hacc0 : ∀ m < reducedLimbCount (reducedTrinomialStep w₀ b b'), x.regs (accReg m) = 0) :
    let t := reducedTrinomialStep w₀ b b'
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    let evalVal := (trinomialPolyEval t k (2 ^ min w₀ (3 * b)) θ.2 r).val
    ∃ y, Exec w (hornerCode t k) x y (k * hornerStepSteps t + 1) ∧
      HornerConsts base w w₀ b b' k r.val y ∧
      (∀ m < L, y.regs (accReg m) = getLimb c evalVal m) ∧
      y.mem = x.mem := by
  intro t c L evalVal
  have hLc : L * c = 2 * 3 ^ t := reducedLimbCount_mul_chunkBits t
  have hr_deg : r.val < 2 ^ (2 * 3 ^ t) :=
    r.isLt.trans_le (two_pow_min_le_two_pow_reducedTrinomialDeg w₀ b b')
  have hx_lt : r.val < 2 ^ (L * c) := hLc.symm ▸ hr_deg
  set c_field : Fin k → TrinomialField t := fun j => (TrinomialField.equivFin t).symm (θ.2 j)
  set x_field : TrinomialField t := AdjoinRoot.mk (trinomial t) (polyOfCode r.val)
  have hx_val : (TrinomialField.equivFin t x_field).val = r.val :=
    TrinomialField.val_equivFin_mk_polyOfCode t hr_deg
  have hzero_val : (TrinomialField.equivFin t (0 : TrinomialField t)).val = 0 := by
    rw [show (0 : TrinomialField t) = AdjoinRoot.mk (trinomial t) (polyOfCode 0) by simp]
    exact TrinomialField.val_equivFin_mk_polyOfCode t (by positivity)
  let P (j : ℕ) (z : Data 240) : Prop :=
    HornerConsts base w w₀ b b' k r.val z ∧
    (∀ m < L, z.regs (accReg m) =
      getLimb c (TrinomialField.equivFin t (hornerPrefix t k c_field x_field j)).val m) ∧
    z.mem = x.mem
  obtain ⟨y, hy_exec, hy_hc, hy_acc, hy_mem⟩ :=
    seqAsc_exec (w := w) (hornerStep t k) (hornerStepSteps t) P k
      (fun j hj z ⟨hz_hc, hz_acc, hz_mem⟩ => by
        set acc := hornerPrefix t k c_field x_field j
        have hacc_lt : (TrinomialField.equivFin t acc).val < 2 ^ (L * c) :=
          hLc.symm ▸ (TrinomialField.equivFin t acc).isLt
        have hP_lt : clmul (TrinomialField.equivFin t acc).val r.val < 2 ^ (2 * L * c) := by
          rw [Nat.mul_assoc]; exact clmul_lt_two_pow_two_mul hacc_lt hx_lt
        obtain ⟨z1, e1, hz1_inv, hz1_lt, hz1_0, hz1_mem⟩ := zeroProdCode_exec z ⟨hz_hc, hz_acc⟩
        obtain ⟨z2, e2, hz2_hc, hz2_prod, hz2_mem⟩ :=
          clmulLimbsCode_exec hc_lt hfit_space hx_lt hacc_lt z1 hz1_inv
            (hz1_mem ▸ hz_mem ▸ htab) hz1_lt hz1_0
        obtain ⟨z3, e3, hz3_hc, hz3_acc, hz3_mem⟩ :=
          reduceAddCode_exec hc_lt hfit_space hP_lt θ ⟨k - 1 - j, by omega⟩ z2 hz2_hc
            (hz2_mem ▸ hz1_mem ▸ hz_mem ▸ hseed) hz2_prod
        refine ⟨z3, e1.seq (e2.seq e3), hz3_hc, fun m hm => ?_,
          hz3_mem.trans (hz2_mem.trans (hz1_mem.trans hz_mem))⟩
        rw [hz3_acc m hm]
        congr 1
        dsimp only [hornerPrefix]
        rw [dite_eq_left hj, TrinomialField.val_equivFin_add, TrinomialField.val_equivFin_mul,
          hx_val]
        congr 2
        exact ((TrinomialField.equivFin t).apply_symm_apply _).symm)
      ⟨hc, fun m hm => by rw [hacc0 m hm]; simp [hornerPrefix, hzero_val, getLimb], rfl⟩
  exact ⟨y, hy_exec, hy_hc, fun m hm => by
    rw [hy_acc m hm, hornerPrefix_self_eq_polynomialHash]; rfl, hy_mem⟩

/-- Step `m < L` of Stage 4 (`5` instructions): masks and shifts `accReg m` into `reg 2` to
reconstruct the low `b'` bits of the polynomial evaluation. -/
@[expose] def packOutStep (c b' m : ℕ) : Code .exact 240 :=
  .seq (.op (.const 10 (reducedOutMask c b' m)))
  (.seq (.op (.const 11 (reducedOutShift c b' m)))
  (.seq (.op (.exactBin .and 12 (accReg m) 10))
  (.seq (.op (.exactBin .shiftLeft 12 12 11))
        (.op (.exactBin .xor 2 2 12)))))

/-- Stage 4 of `evalCode`: packs the low `b'` bits of `accReg 0 .. accReg (L - 1)` into `reg 2`. -/
@[expose] def packOutCode (t b' : ℕ) : Code .exact 240 :=
  .seq (.op (.const 2 0))
       (seqAsc (packOutStep (reducedChunkBits t) b') (reducedLimbCount t))

private theorem packOutStep_exec {w t b' evalVal : ℕ}
    (hc_lt : 2 * reducedChunkBits t < w)
    (hb'_le : b' ≤ w)
    (m : ℕ) (hm : m < reducedLimbCount t)
    (x : Data 240)
    (h2 : x.regs 2 = packLimbs (reducedChunkBits t) m (getLimb (reducedChunkBits t) evalVal) &&&
      (2 ^ b' - 1))
    (hacc : ∀ i < reducedLimbCount t,
      x.regs (accReg i) = getLimb (reducedChunkBits t) evalVal i) :
    let c := reducedChunkBits t
    let L := reducedLimbCount t
    ∃ y, Exec w (packOutStep c b' m) x y 5 ∧
      y.regs 0 = x.regs 0 ∧
      y.regs 1 = x.regs 1 ∧
      y.regs 2 = packLimbs c (m + 1) (getLimb c evalVal) &&& (2 ^ b' - 1) ∧
      (∀ i < L, y.regs (accReg i) = getLimb c evalVal i) ∧
      y.mem = x.mem := by
  intro c L
  have hfit_mask : Fits w (reducedOutMask c b' m) := by stride_omega [reducedOutMask_lt c b' m]
  have hfit_shift : Fits w (reducedOutShift c b' m) := by stride_omega [reducedOutShift_le c b' m]
  have hfit_masked : Fits w (getLimb c evalVal m &&& reducedOutMask c b' m) :=
    Nat.and_le_right.trans_lt hfit_mask
  have hfit_shifted : Fits w ((getLimb c evalVal m &&& reducedOutMask c b' m) <<<
      reducedOutShift c b' m) := by
    stride_omega [and_reducedOutMask_shiftLeft_lt c b' m (getLimb c evalVal m)]
  have hfit_next : Fits w (packLimbs c (m + 1) (getLimb c evalVal) &&& (2 ^ b' - 1)) := by
    stride_omega [and_two_pow_sub_one_lt (packLimbs c (m + 1) (getLimb c evalVal)) b']
  have hL_le : L ≤ 54 := reducedLimbCount_le t
  change ∀ i < L, x.regs (accReg i) = getLimb c evalVal i at hacc
  have hnext_eq : x.regs 2 ^^^
      ((getLimb c evalVal m &&& reducedOutMask c b' m) <<< reducedOutShift c b' m) =
      packLimbs c (m + 1) (getLimb c evalVal) &&& (2 ^ b' - 1) := by
    rw [h2, ← packLimbs_and_mask_succ c b' m (getLimb c evalVal)]
  wram_exec [packOutStep, hacc m hm, hnext_eq]
  exact ⟨by wram_simp, by wram_simp, by wram_simp, fun i hi => by wram_simp [hacc i hi], rfl⟩

private theorem packOutCode_exec {w t b' evalVal : ℕ}
    (hc_lt : 2 * reducedChunkBits t < w)
    (hb'_le : b' ≤ w)
    (heval_lt : evalVal < 2 ^ (reducedLimbCount t * reducedChunkBits t))
    (x : Data 240)
    (hacc : ∀ i < reducedLimbCount t,
      x.regs (accReg i) = getLimb (reducedChunkBits t) evalVal i) :
    let L := reducedLimbCount t
    ∃ y, Exec w (packOutCode t b') x y (1 + (L * 5 + 1)) ∧
      y.regs 0 = x.regs 0 ∧
      y.regs 1 = x.regs 1 ∧
      y.regs 2 = evalVal &&& (2 ^ b' - 1) ∧
      y.mem = x.mem := by
  intro L
  set c := reducedChunkBits t
  let P (n : ℕ) (z : Data 240) : Prop :=
    z.regs 0 = x.regs 0 ∧
    z.regs 1 = x.regs 1 ∧
    z.regs 2 = packLimbs c n (getLimb c evalVal) &&& (2 ^ b' - 1) ∧
    (∀ i < L, z.regs (accReg i) = getLimb c evalVal i) ∧
    z.mem = x.mem
  wram_exec [packOutCode]
  wram_call (seqAsc_exec (w := w) (packOutStep c b') 5 P L
    (fun m hm z ⟨hz0, hz1, hz2, hz_acc, hz_mem⟩ => by
      obtain ⟨z', hz'_exec, hz'0, hz'1, hz'2, hz'_acc, hz'_mem⟩ :=
        packOutStep_exec hc_lt hb'_le m hm z hz2 hz_acc
      exact ⟨z', hz'_exec, hz'0.trans hz0, hz'1.trans hz1, hz'2, hz'_acc, hz'_mem.trans hz_mem⟩)
    ⟨by wram_simp, by wram_simp, by wram_simp [packLimbs, Nat.zero_and],
      fun i hi => by wram_simp [hacc i hi], rfl⟩)
    with y ⟨hy0, hy1, hy2, _, hymem⟩
  exact ⟨by omega, hy0, hy1, by rw [hy2, packLimbs_getLimb (reducedChunkBits_pos t) L heval_lt],
    hymem⟩

/-- Complete deterministic Word-RAM hash evaluation program `evalCode w w₀ b b' k` on `Data 240`:
reduces `reg 1` via Stage 1 (`reduceKeyCode`), unpacks limbs and sets up Horner constants via
Stage 2 (`initLimbsCode`, `hornerSetupCode`), runs `k` Horner steps via Stage 3 (`hornerCode`),
and packs the low `b'` bits into `reg 2` via Stage 4 (`packOutCode`). -/
@[expose] def evalCode (w w₀ b b' k : ℕ) : Code .exact 240 :=
  let t := reducedTrinomialStep w₀ b b'
  .seq (reduceKeyCode w₀ b)
  (.seq (initLimbsCode t)
  (.seq (hornerSetupCode w w₀ b b' k)
  (.seq (hornerCode t k)
        (packOutCode t b'))))

/-- Exact instruction count of `evalCode w w₀ b b' k`. -/
@[expose] def evalSteps (w₀ b b' k : ℕ) : ℕ :=
  let t := reducedTrinomialStep w₀ b b'
  let L := reducedLimbCount t
  39 + ((L * 5 + 1) + (8 + ((k * hornerStepSteps t + 1) + (1 + (L * 5 + 1)))))

/-- Parameter-independent `O(k)` upper bound `47250 * k + 591` on `evalSteps w₀ b b' k`. -/
@[expose] def evalBound (k : ℕ) : ℕ :=
  47250 * k + 591

/-- **`evalSteps w₀ b b' k` is `O(k)` (`evalSteps_le`)**:
for all `w₀, b, b', k : ℕ`, `evalSteps w₀ b b' k ≤ evalBound k = 47250 * k + 591`. -/
theorem evalSteps_le (w₀ b b' k : ℕ) : evalSteps w₀ b b' k ≤ evalBound k := by
  dsimp only [evalSteps, hornerStepSteps, evalBound]
  have hL := reducedLimbCount_le (reducedTrinomialStep w₀ b b')
  have hmul : k * (2 * _ * 1 + 1 + ((_ * (_ * 13 + 1) + 1) + (_ * 6 + 1))) ≤ k * 47250 :=
    Nat.mul_le_mul_left k (by nlinarith)
  omega

/-- **Deterministic execution of `evalCode w w₀ b b' k`**:
evaluates `(reducedPolyHash U w₀ b b' k θ u).val` into `reg 2` in `evalSteps w₀ b b' k`
instructions while preserving `reg 0 = base` and all memory. -/
theorem evalCode_exec {base w U w₀ b b' k : ℕ}
    (hw₀_pos : 0 < w₀) (hw₀ : w₀ ≤ w) (hU : U ≤ 2 ^ w₀) (hb' : b' ≤ w)
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + space w w₀ b b' k))
    (θ : ReducedPolySeed w₀ b b' k) (u : Fin U) (x : Data 240)
    (h0 : x.regs 0 = base) (h1 : x.regs 1 = u.val)
    (htab : TableRep base w w₀ b b' k x.mem)
    (hseed : SeedRep base w₀ b b' k θ x.mem) :
    ∃ y, Exec w (evalCode w w₀ b b' k) x y (evalSteps w₀ b b' k) ∧
      y.regs 0 = base ∧
      y.regs 2 = (reducedPolyHash U w₀ b b' k θ u).val ∧
      y.mem = x.mem := by
  set t := reducedTrinomialStep w₀ b b'
  set r := multiplyShiftReduced U w₀ (3 * b) θ.1 u
  have hr_eq : oddMulModWord w₀ (x.mem (x.regs 0)) (x.regs 1) >>> (w₀ - min w₀ (3 * b)) =
      r.val := by
    rw [h0, hseed.1, h1, show w₀ - min w₀ (3 * b) = w₀ - 3 * b by omega]
    exact oddMulModWord_shiftRight_eq_multiplyShiftReduced hw₀_pos θ.1 u
  have hr_lt_w : r.val < 2 ^ w := by stride_omega [r.isLt]
  have heval_lt : (trinomialPolyEval t k (2 ^ min w₀ (3 * b)) θ.2 r).val <
      2 ^ (reducedLimbCount t * reducedChunkBits t) := by
    rw [reducedLimbCount_mul_chunkBits]
    exact (trinomialPolyEval t k (2 ^ min w₀ (3 * b)) θ.2 r).isLt
  unfold evalCode
  refine WP.Exact.exists_exec (WP.Exact.seq ?_)
  wram_call (reduceKeyCode_exec (b := b) hw₀_pos hw₀ x (by rw [h0, hseed.1]; exact θ.1.isLt)
    (by rw [h1]; exact u.isLt.trans_le hU)) with y1 ⟨hy1_0, hy1_3, hy1_mem⟩
  refine WP.Exact.seq ?_
  wram_call (initLimbsCode_exec (t := t) hc_lt hr_lt_w y1 (hy1_3.trans hr_eq))
    with y2 ⟨hy2_0, hy2_x, hy2_acc, hy2_mem⟩
  refine WP.Exact.seq ?_
  wram_call (hornerSetupCode_exec (w := w) (base := base) (k := k) hc_lt hfit_space y2
    (hy2_0.trans (hy1_0.trans h0)))
    with y3 ⟨h3_0, h3_4, h3_5, h3_6, h3_7, h3_8, h3_9, h3_18, h3_hi, hy3_mem⟩
  have hm3 : y3.mem = x.mem := hy3_mem.trans (hy2_mem.trans hy1_mem)
  refine WP.Exact.seq ?_
  wram_call (hornerCode_exec hc_lt hfit_space θ r y3
    ⟨h3_0, h3_4, h3_5, h3_6, h3_7, h3_8, h3_9, h3_18, fun m hm =>
      (h3_hi (xReg m) (by dsimp [xReg]; omega)).trans (hy2_x m hm)⟩
    (hm3 ▸ htab) (hm3 ▸ hseed)
    (fun m hm => (h3_hi (accReg m) (by dsimp [accReg]; omega)).trans (hy2_acc m hm)))
    with y4 ⟨hy4_hc, hy4_acc, hy4_mem⟩
  wram_call (packOutCode_exec hc_lt hb' heval_lt y4 hy4_acc) with y5 ⟨hy5_0, _, hy5_2, hy5_mem⟩
  exact ⟨by dsimp only [evalSteps, t]; ring, hy5_0.trans hy4_hc.1,
    hy5_2.trans (val_trinomialPolyHash t k (2 ^ min w₀ (3 * b)) b' θ.2 r).symm,
    hy5_mem.trans (hy4_mem.trans hm3)⟩

/-- `ExecWithin` wrapper for `evalCode_exec`. -/
theorem evalCode_execWithin {base w U w₀ b b' k : ℕ}
    (hw₀_pos : 0 < w₀) (hw₀ : w₀ ≤ w) (hU : U ≤ 2 ^ w₀) (hb' : b' ≤ w)
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + space w w₀ b b' k))
    (θ : ReducedPolySeed w₀ b b' k) (u : Fin U) (x : Data 240)
    (h0 : x.regs 0 = base) (h1 : x.regs 1 = u.val)
    (htab : TableRep base w w₀ b b' k x.mem)
    (hseed : SeedRep base w₀ b b' k θ x.mem) :
    ∃ y, ExecWithin w (evalCode w w₀ b b' k) x y (evalSteps w₀ b b' k) ∧
      y.mem = x.mem ∧
      y.regs 0 = base ∧
      y.regs 2 = (reducedPolyHash U w₀ b b' k θ u).val := by
  obtain ⟨y, hex, hy0, hy2, hymem⟩ :=
    evalCode_exec hw₀_pos hw₀ hU hb' hc_lt hfit_space θ u x h0 h1 htab hseed
  exact ⟨y, hex.within, hymem, hy0, hy2⟩

/-! ## Section 5: Packaging as `HashFamily.WordRAM.Impl` -/

/-- Package `ReducedKWise` into a reusable `HashFamily.WordRAM.Impl` certificate over
`Basis.exact` on `Data 240`. -/
@[expose] noncomputable def impl {w base U w₀ b b' k : ℕ}
    (hw₀_pos : 0 < w₀) (hw₀ : w₀ ≤ w) (hU : U ≤ 2 ^ w₀) (hb' : b' ≤ w)
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + space w w₀ b b' k)) :
    Impl .exact 240 0 w base U (2 ^ b') ![] where
  Seed := ReducedPolySeed w₀ b b' k
  eval := reducedPolyHash U w₀ b b' k
  space := space w w₀ b b' k
  tableRep := TableRep base w w₀ b b' k
  seedRep := SeedRep base w₀ b b' k
  baseReg := 0
  keyReg := 1
  outReg := 2
  initParams := ![]
  key_ne_base := by decide
  params_ne_base j := Fin.elim0 j
  fits_space := hfit_space
  fits_tag := by stride_omega
  fits_key u := by stride_omega [u.isLt]
  addReg := Op.exactBin .add
  addReg_eval _ _ _ hfit := Data.put_of_fits hfit
  initTableCode := initTableCode w w₀ b b' k
  initTableSteps := initTableSteps w₀ b b'
  resampleCode := resampleCode w₀ b b' k
  resampleSteps := resampleSteps w₀ b b' k
  evalCode := evalCode w w₀ b b' k
  evalSteps := evalSteps w₀ b b' k
  initTable_exec {x} _ hbase _ _ := by
    obtain ⟨y, hex, hy0, htab, hmod⟩ := initTableCode_execWithin hbase hc_lt.le hfit_space
    refine ⟨y, hex, hy0, htab, fun a ha => hmod a ?_⟩
    rw [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt] at ha
    rcases ha with hlt | hge <;> [exact Or.inl (by wram_omega); exact Or.inr hge]
  resample_exec {x} _ hbase htab := by
    refine Impl.resample_exec_of_execRand
      (extractSeed base w₀ b b' k)
      (resampleCode_execRand hbase hw₀ hc_lt.le hfit_space)
      (map_extractSeed_eval_resampleComp base w₀ b b' k x) fun z hz => ?_
    obtain ⟨hz0, htab', hseed', hframe, hsteps⟩ := mem_support_resampleComp hbase htab hz
    refine ⟨hz0, htab', hseed', fun a ha => hframe a ?_, hsteps.le⟩
    rw [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt] at ha
    rcases ha with hlt | hge <;> [exact Or.inl hlt; exact Or.inr (by wram_omega)]
  eval_exec θ u {x} _ hbase hkey htab hseed :=
    evalCode_execWithin hw₀_pos hw₀ hU hb' hc_lt hfit_space θ u x hbase hkey htab hseed

/-- Standard-basis lifting of `impl`. -/
@[expose] noncomputable def implStandard {w base U w₀ b b' k : ℕ}
    (hw₀_pos : 0 < w₀) (hw₀ : w₀ ≤ w) (hU : U ≤ 2 ^ w₀) (hb' : b' ≤ w)
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfit_space : Fits w (base + space w w₀ b b' k)) :
    Impl .standard 240 0 w base U (2 ^ b') ![] :=
  (impl hw₀_pos hw₀ hU hb' hc_lt hfit_space).toStandard

end Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise
