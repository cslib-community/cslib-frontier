/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Absorb
public import CslibFrontier.Computability.WordRAM.Realization.Branch
public import CslibFrontier.Computability.WordRAM.Realization.Loop
public import CslibFrontier.Computability.WordRAM.Realization.Primitive
public import CslibFrontier.Computability.WordRAM.Realization.Reindex
public import CslibFrontier.Computability.WordRAM.Realization.Witness
public import CslibFrontier.DataStructure.Dictionary.WordRAM.BitPackedArray
public import CslibFrontier.DataStructure.Dictionary.WordRAM.BitPackedArrayProg
public import CslibFrontier.DataStructure.HashFamily.WordRAM.DoubleTabulation
public import CslibFrontier.DataStructure.HashFamily.WordRAM.Tabulation
public import CslibFrontier.Probability.KWiseIndependent.DoubleTabulation
public import CslibFrontier.Probability.KWiseIndependent.ReducedLimbs
public import CslibFrontier.Probability.PMF.Uniform
public import CslibFrontier.Probability.Uniform
import CslibFrontier.Computability.WordRAM.Randomized.SymbolicExec
import CslibFrontier.Computability.WordRAM.Realization.LoopCongr
import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.Computability.WordRAM.Width
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.SuppCases
import CslibFrontier.Tactic.WramOmega

/-!
# Universe-Reduced Salted General-`q` Bit-Packed Double Tabulation (`[Thorup2013]`)

This module provides a Word-RAM implementation of universe-reduced salted general-`q` double
tabulation hashing with bit-packed lookup tables:

1. **Stage 1 (`multiplyShiftReduced` via `oddMulModWord`)**: maps any key `u : Fin U`
   (`U ≤ 2 ^ w₀`, `0 < w₀ ≤ w`) to a reduced key `rKey ∈ Fin (2 ^ min w₀ R)` without `2 * w₀ ≤ w`
   overflow, failing injectivity on a window `W_set : Finset (Fin U)` with probability at most
   `(#W_set * (#W_set - 1)) / 2 ^ R`.
2. **Stage 2 (salted general-`q` `doubleTabHash` with bit-packed tables)**: appends a salt character
   `s : Fin s_max` (`s_max ≤ 2 ^ b_char`) to the `c_tab` base-`2 ^ b_char` characters of `rKey`
   (`min w₀ R ≤ c_tab * b_char`) and evaluates `(c_tab + 1, d, b_char, M_out)` double tabulation
   with `d = 2 * q * (c_tab + 1)`. Both `T₁` (`(c_tab + 1) * d * 2 ^ b_char` entries of `b_char`
   bits) and `T₂` (`d * 2 ^ b_char` entries of `M_out` bits) are stored in `BitPackedArray`s so the
   total footprint is `≤ (((c_tab + 1) * d * b_char + d * M_out) * 2 ^ b_char + w - 1) / w + 6`
   words for every word width `w > 0` (including `w ≫ n_max`).
3. **Exact uniform resampling (`resampleCode`) and `Memory.Prog` evaluation (`evalGenProg`)**:
   `resampleCode` populates `(α, T₁, T₂)` from the exact uniform distribution in
   `O((topWords + botWords) + 1)` instructions via `Tabulation.randFillLoop`, and `evalGenProg`
   evaluates the hash in `O(c_tab * d)` deterministic instructions via `Memory.Prog` and `realize`
   (`¬ReadsWidth`, single compiled `Code .exact` independent of `(c_tab, d, b_char, M_out, U, w)`).

## Main definitions

* `Cslib.DataStructure.HashFamily.WordRAM.BitPackedDoubleTabulation.space`,
  `topWords`, `botWords`, `Seed`, `saltedChars`, `evalSalted`, `GoodTop`.
* `Cslib.DataStructure.HashFamily.WordRAM.BitPackedDoubleTabulation.extractSeed`, `SeedRep`,
  `resampleCode`, `resampleSteps`.
* `Cslib.DataStructure.HashFamily.WordRAM.BitPackedDoubleTabulation.HashParams`, `mkHashParams`,
  `evalGenProg`, `evalProg`.

## Main results

* `space_le`: bit-packed word-space bound valid for all `w > 0`.
* `isKWiseIndependentHash_evalSalted_of_goodTop`: conditional exact `k`-wise independence on
  `Fin s_max × W_set` whenever `GoodTop` holds.
* `toOuterMeasure_not_goodTop_le`: explicit union bound on `¬ GoodTop` combining
  `toOuterMeasure_not_injOn_multiplyShiftReduced_le` and `card_not_isKUnique_le`.
* `resampleCode_execRand`, `map_extractSeed_eval_resampleComp`: exact `ExecRand` semantics and
  product uniformity of bit-packed seed resampling.
* `realizes_evalGen`, `evalProg_spec`, `validHistory_evalProg`, `memoryCost_evalProg`:
  `Realizes .exact` certificate, functional correctness, memory admissibility, and cost of
  `evalProg`.

## References

* [M. Dietzfelbinger, T. Hagerup, J. Katajainen, M. Penttonen, *A Reliable Randomized Algorithm for
  the Closest-Pair Problem*][DietzfelbingerHagerupKatajainenPenttonen1997]
* [M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation,
  and High Independence*][Thorup2013]
-/

public section

namespace Cslib.DataStructure.HashFamily.WordRAM.BitPackedDoubleTabulation

open Cslib.WordRAM Cslib.WordRAM.ExactLog Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.Probability Cslib.Probability.PMF
open Finset
open scoped BigOperators ENNReal Cslib.Probability.PMF

/-! ## Section 1: Salted double-tabulation model, conditional `k`-wise independence, and layout -/

/-- Number of entries `(c_tab + 1) * d * 2 ^ b_char` in the top-level bit-packed table `T₁`. -/
abbrev topEntries (c_tab d b_char : ℕ) : ℕ :=
  (c_tab + 1) * d * 2 ^ b_char

/-- Number of entries `d * 2 ^ b_char` in the bottom-level bit-packed table `T₂`. -/
abbrev botEntries (d b_char : ℕ) : ℕ :=
  d * 2 ^ b_char

/-- Number of `w`-bit words storing `T₁` as a `BitPackedArray` of `b_char`-bit entries. -/
@[expose] def topWords (w c_tab d b_char : ℕ) : ℕ :=
  packedWords (topEntries c_tab d b_char) b_char w

/-- Number of `w`-bit words storing `T₂` as a `BitPackedArray` of `M_out`-bit entries. -/
@[expose] def botWords (w d b_char M_out : ℕ) : ℕ :=
  packedWords (botEntries d b_char) M_out w

/-- Word offset `1 + topWords w c_tab d b_char` of the bottom-level bit-packed table `T₂`. -/
@[expose] def offBot (w c_tab d b_char : ℕ) : ℕ :=
  1 + topWords w c_tab d b_char

/-- Total footprint `1 + topWords + botWords` in `w`-bit machine words. -/
@[expose] def space (w c_tab d b_char M_out : ℕ) : ℕ :=
  1 + topWords w c_tab d b_char + botWords w d b_char M_out

attribute [local wram_arith] topWords botWords offBot space

theorem space_pos (w c_tab d b_char M_out : ℕ) : 0 < space w c_tab d b_char M_out := by
  wram_omega

/-- Bit-packed word bound valid for every word width `w`:
`space w c_tab d b_char M_out ≤ (topEntries * b_char + botEntries * M_out + w - 1) / w + 6`. -/
theorem space_le (w c_tab d b_char M_out : ℕ) :
    space w c_tab d b_char M_out ≤
      (topEntries c_tab d b_char * b_char + botEntries d b_char * M_out + w - 1) / w + 6 := by
  wram_omega [packedWords_add_le (topEntries c_tab d b_char) b_char (botEntries d b_char) M_out w]

/-- Combined seed type `(α, T₁, T₂)` for universe-reduced salted double tabulation. -/
abbrev Seed (w₀ c_tab d b_char M_out : ℕ) : Type :=
  Fin (2 ^ (w₀ - 1)) × DoubleTabTopSeed (c_tab + 1) d b_char × DoubleTabBotSeed d b_char M_out

/-- Extract Stage 1 multiplier `α` from seed. -/
abbrev Seed.alpha {w₀ c_tab d b_char M_out : ℕ}
    (θ : Seed w₀ c_tab d b_char M_out) : Fin (2 ^ (w₀ - 1)) := θ.1

/-- Extract Stage 2 top table `T₁` from seed. -/
abbrev Seed.top {w₀ c_tab d b_char M_out : ℕ}
    (θ : Seed w₀ c_tab d b_char M_out) : DoubleTabTopSeed (c_tab + 1) d b_char := θ.2.1

/-- Extract Stage 2 bottom table `T₂` from seed. -/
abbrev Seed.bot {w₀ c_tab d b_char M_out : ℕ}
    (θ : Seed w₀ c_tab d b_char M_out) : DoubleTabBotSeed d b_char M_out := θ.2.2

/-- Salted `(c_tab + 1)`-character tuple: the first `c_tab` characters extract base-`2 ^ b_char`
digits of the reduced key `rKey`, and the final character at index `c_tab` encodes the salt `s`. -/
@[expose] def saltedChars (c_tab b_char : ℕ) {R' s_max : ℕ} (s : Fin s_max) (rKey : Fin R') :
    Fin (c_tab + 1) → Fin (2 ^ b_char) :=
  Fin.snoc (charDigits c_tab b_char rKey) ⟨s.val % 2 ^ b_char, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- Injectivity of `saltedChars` when `s_max ≤ 2 ^ b_char` and `R' ≤ 2 ^ (c_tab * b_char)`. -/
theorem saltedChars_injective {c_tab b_char R' s_max : ℕ}
    (hs : s_max ≤ 2 ^ b_char) (hR' : R' ≤ 2 ^ (c_tab * b_char)) :
    Function.Injective (fun p : Fin s_max × Fin R' => saltedChars c_tab b_char p.1 p.2) := by
  rintro ⟨s₁, r₁⟩ ⟨s₂, r₂⟩ heq
  have hlast := congrFun heq (Fin.last c_tab)
  simp only [saltedChars, Fin.snoc_last, Fin.mk.injEq] at hlast
  rw [Nat.mod_eq_of_lt (s₁.isLt.trans_le hs), Nat.mod_eq_of_lt (s₂.isLt.trans_le hs)] at hlast
  have hinit : charDigits c_tab b_char r₁ = charDigits c_tab b_char r₂ := by
    funext i
    have hi := congrFun heq i.castSucc
    simpa only [saltedChars, Fin.snoc_castSucc] using hi
  exact Prod.ext (Fin.ext hlast) (charDigits_injective hR' hinit)

/-- Universe-reduced salted double tabulation hash mapping `(s, u) : Fin s_max × Fin U` to
`Fin (2 ^ M_out)`. -/
@[expose] def evalSalted (U w₀ R c_tab d b_char M_out s_max : ℕ)
    (θ : Seed w₀ c_tab d b_char M_out) (p : Fin s_max × Fin U) : Fin (2 ^ M_out) :=
  simpleTabEval θ.bot
    (simpleTabTuple θ.top (saltedChars c_tab b_char p.1 (multiplyShiftReduced U w₀ R θ.alpha p.2)))

/-- Good top-seed event on a key window `W_set : Finset (Fin U)`: Stage 1 `multiplyShiftReduced` is
injective on `W_set` and Stage 2 `simpleTabTuple T₁` is `k`-unique. -/
@[expose] def GoodTop (U w₀ R c_tab d b_char k : ℕ) (W_set : Finset (Fin U))
    (α : Fin (2 ^ (w₀ - 1))) (T₁ : DoubleTabTopSeed (c_tab + 1) d b_char) : Prop :=
  Set.InjOn (multiplyShiftReduced U w₀ R α) (W_set : Set (Fin U)) ∧
  IsKUnique k (simpleTabTuple T₁)

/-- **Conditional exact `k`-wise independence on `Fin s_max × W_set`**:
whenever `s_max ≤ 2 ^ b_char`, `min w₀ R ≤ c_tab * b_char`, and `GoodTop` holds for `(α, T₁)`,
the bottom-table family `T₂ ↦ evalSalted ... (α, T₁, T₂)` restricted to `Fin s_max × W_set` is
exact `k`-wise independent. -/
theorem isKWiseIndependentHash_evalSalted_of_goodTop
    {U w₀ R c_tab d b_char M_out s_max k : ℕ} {W_set : Finset (Fin U)}
    {α : Fin (2 ^ (w₀ - 1))} {T₁ : DoubleTabTopSeed (c_tab + 1) d b_char}
    (hs : s_max ≤ 2 ^ b_char) (hcov : min w₀ R ≤ c_tab * b_char)
    (hgood : GoodTop U w₀ R c_tab d b_char k W_set α T₁) :
    IsKWiseIndependentHash k (fun (T₂ : DoubleTabBotSeed d b_char M_out) (p : Fin s_max × W_set) =>
      evalSalted U w₀ R c_tab d b_char M_out s_max (α, T₁, T₂) (p.1, p.2.val)) := by
  refine isKWiseIndependentHash_of_isKUnique
    (f := fun p : Fin s_max × W_set =>
      simpleTabTuple T₁ (saltedChars c_tab b_char p.1 (multiplyShiftReduced U w₀ R α p.2.val)))
    (hgood.2.comp_injective ?_)
  rintro ⟨s₁, ⟨u₁, hu₁⟩⟩ ⟨s₂, ⟨u₂, hu₂⟩⟩ heq
  obtain ⟨rfl, hr⟩ := Prod.mk.inj (saltedChars_injective hs (Nat.pow_le_pow_right two_pos hcov) heq)
  exact Prod.ext rfl (Subtype.ext (hgood.1 hu₁ hu₂ hr))

/-- Probability bound on `¬ IsKUnique k (simpleTabTuple T₁)` under `PMF.uniformOfFintype`, lifted
from `Cslib.Probability.card_not_isKUnique_le`. -/
theorem toOuterMeasure_not_isKUnique_le {c d b q k : ℕ} (hc : 1 ≤ c) (hq : 1 ≤ q)
    (hd : d = 2 * q * c) (hbound : 2 * doubleTabCodeBound c d q k ≤ 2 ^ ((q - 1) * b)) :
    (PMF.uniformOfFintype (DoubleTabTopSeed c d b)).toOuterMeasure
      {T₁ | ¬ IsKUnique k (simpleTabTuple T₁)} ≤
      (2 * (doubleTabCodeBound c d q k : ℝ≥0∞) ^ 2) /
        ((2 : ℝ≥0∞) ^ ((q - 1) * b)) ^ 2 := by
  classical
  rw [toOuterMeasure_uniformOfFintype, ← div_eq_mul_inv,
    ENNReal.div_le_iff_le_mul (Or.inl (Nat.cast_ne_zero.mpr Fintype.card_pos.ne'))
      (Or.inl (ENNReal.natCast_ne_top _)),
    div_eq_mul_inv, mul_right_comm _ _⁻¹, ← div_eq_mul_inv]
  rw [ENNReal.le_div_iff_mul_le
    (Or.inl (pow_ne_zero _ (pow_ne_zero _ (by norm_num : (2 : ℝ≥0∞) ≠ 0))))
    (Or.inl (ENNReal.pow_ne_top (ENNReal.pow_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))))]
  have hle := Nat.cast_le (α := ℝ≥0∞).mpr (card_not_isKUnique_le hc hq hd hbound)
  push_cast at hle
  simpa [mul_comm, mul_left_comm, mul_assoc] using hle

/-- **Explicit failure-probability bound on `¬ GoodTop`**:
for a uniform seed `θ : Seed w₀ c_tab d b_char M_out`, when `0 < w₀`, `U ≤ 2 ^ w₀`, `1 ≤ q`,
`d = 2 * q * (c_tab + 1)`, and `2 * doubleTabCodeBound (c_tab + 1) d q k ≤ 2 ^ ((q - 1) * b_char)`,
the probability that `GoodTop U w₀ R c_tab d b_char k W_set θ.1 θ.2.1` fails is at most
`(#W_set * (#W_set - 1)) / 2 ^ R + 2 * (doubleTabCodeBound (c_tab + 1) d q k) ^ 2 /
(2 ^ ((q - 1) * b_char)) ^ 2`. -/
theorem toOuterMeasure_not_goodTop_le
    {U w₀ R c_tab d b_char M_out q k : ℕ} (hw₀ : 0 < w₀) (hU : U ≤ 2 ^ w₀)
    (hq : 1 ≤ q) (hd : d = 2 * q * (c_tab + 1))
    (hbound : 2 * doubleTabCodeBound (c_tab + 1) d q k ≤ 2 ^ ((q - 1) * b_char))
    (W_set : Finset (Fin U)) :
    (PMF.uniformOfFintype (Seed w₀ c_tab d b_char M_out)).toOuterMeasure
      {θ | ¬ GoodTop U w₀ R c_tab d b_char k W_set θ.1 θ.top} ≤
      ((#W_set * (#W_set - 1) : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ R +
        (2 * (doubleTabCodeBound (c_tab + 1) d q k : ℝ≥0∞) ^ 2) /
          ((2 : ℝ≥0∞) ^ ((q - 1) * b_char)) ^ 2 := by
  let μ := (PMF.uniformOfFintype (Seed w₀ c_tab d b_char M_out)).toOuterMeasure
  let A : Set (Fin (2 ^ (w₀ - 1))) :=
    {α | ¬ Set.InjOn (multiplyShiftReduced U w₀ R α) (W_set : Set (Fin U))}
  let B : Set (DoubleTabTopSeed (c_tab + 1) d b_char) :=
    {T₁ | ¬ IsKUnique k (simpleTabTuple T₁)}
  have hm₁ : μ (Prod.fst ⁻¹' A) = (PMF.uniformOfFintype _).toOuterMeasure A := by
    rw [← uniformOfFintype_prod_map_fst (α := Fin (2 ^ (w₀ - 1)))
      (β := DoubleTabTopSeed (c_tab + 1) d b_char × DoubleTabBotSeed d b_char M_out),
      PMF.toOuterMeasure_map_apply]
  have hm₂ : μ ((Prod.fst ∘ Prod.snd) ⁻¹' B) = (PMF.uniformOfFintype _).toOuterMeasure B := by
    rw [← uniformOfFintype_prod_map_fst (α := DoubleTabTopSeed (c_tab + 1) d b_char)
        (β := DoubleTabBotSeed d b_char M_out),
      ← uniformOfFintype_prod_map_snd (α := Fin (2 ^ (w₀ - 1))),
      PMF.map_comp, PMF.toOuterMeasure_map_apply]
  calc μ {θ | ¬ GoodTop U w₀ R c_tab d b_char k W_set θ.1 θ.top}
      ≤ μ (Prod.fst ⁻¹' A ∪ (Prod.fst ∘ Prod.snd) ⁻¹' B) :=
        μ.mono fun _ h => not_and_or.mp h
    _ ≤ μ (Prod.fst ⁻¹' A) + μ ((Prod.fst ∘ Prod.snd) ⁻¹' B) :=
        MeasureTheory.measure_union_le _ _
    _ ≤ _ := by
        rw [hm₁, hm₂]
        exact add_le_add (toOuterMeasure_not_injOn_multiplyShiftReduced_le hw₀ hU W_set)
          (toOuterMeasure_not_isKUnique_le (by omega) hq hd hbound)

/-! ## Section 2: Bit-packed slice uniformity, `SeedRep`, and `resampleCode` -/

/-- Top-table row index bound: `j * (c_tab + 1) + i < topEntries c_tab d b_char`. -/
private theorem topRow_lt_topEntries {c_tab d b_char i j : ℕ}
    (hi : i < c_tab + 1) (hj : j < d) :
    j * (c_tab + 1) + i < topEntries c_tab d b_char := by
  have hrow : j * (c_tab + 1) + i < (c_tab + 1) * d := by
    simpa only [Nat.mul_comm] using Nat.mul_add_lt_mul_of_lt_of_lt hj hi
  exact Nat.lt_of_lt_of_le hrow (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos b_char))

/-- Top-table flat index bound: `(j * (c_tab + 1) + i) * 2 ^ b_char + ch < topEntries`. -/
private theorem topIdx_lt_topEntries {c_tab d b_char i j ch : ℕ}
    (hi : i < c_tab + 1) (hj : j < d) (hch : ch < 2 ^ b_char) :
    (j * (c_tab + 1) + i) * 2 ^ b_char + ch < topEntries c_tab d b_char := by
  have hrow : j * (c_tab + 1) + i < (c_tab + 1) * d := by
    simpa only [Nat.mul_comm] using Nat.mul_add_lt_mul_of_lt_of_lt hj hi
  simpa only [Nat.mul_comm (2 ^ b_char)] using Nat.mul_add_lt_mul_of_lt_of_lt hrow hch

/-- For `0 < w` and `idx < N`, every bit index `idx * k + j` (`j < k`) lies in word
`(idx * k + j) / w < packedWords N k w`. -/
theorem mul_add_div_lt_packedWords {N k w idx j : ℕ} (hw : 0 < w) (hidx : idx < N) (hj : j < k) :
    (idx * k + j) / w < packedWords N k w := by
  have hle : idx * k + j < N * k := by
    simpa only [Nat.mul_comm] using Nat.mul_add_lt_mul_of_lt_of_lt hidx hj
  have hdiv : (idx * k + j) / w ≤ (N * k + w - 1) / w := Nat.div_le_div_right (by omega)
  unfold packedWords
  omega

/-- Exact bit-level characterization of `readPacked`: for `0 < w`, `k ≤ w`, and `j < k`, bit `j` of
`readPacked arrBase k w mem idx` equals bit `(idx * k + j) % w` of word
`mem (arrBase + (idx * k + j) / w)`. -/
theorem testBit_readPacked {arrBase k w : ℕ} (hw : 0 < w) (hkw : k ≤ w) (mem : ℕ → ℕ)
    (idx : ℕ) {j : ℕ} (hj : j < k) :
    (readPacked arrBase k w mem idx).testBit j =
      (mem (arrBase + (idx * k + j) / w)).testBit ((idx * k + j) % w) := by
  unfold readPacked readBitSlice
  set wOff := wordOffset k w idx
  set bOff := bitOffset k w idx
  set k₀ := lowWidth k w idx
  set k₁ := highWidth k w idx
  have hb_lt : bOff < w := bitOffset_lt hw
  have hk_sum : k₀ + k₁ = k := lowWidth_add_highWidth k w idx
  have hdecomp : idx * k = w * wOff + bOff := by
    rw [show wOff = (idx * k) / w from wordOffset_eq_mul_div hw,
      show bOff = (idx * k) % w from bitOffset_eq_mul_mod k w idx]
    exact (Nat.div_add_mod (idx * k) w).symm
  have hdivMod (q r : ℕ) (hr : r < w) (heq : idx * k + j = r + w * q) :
      (idx * k + j) / w = q ∧ (idx * k + j) % w = r := by
    rw [heq, Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt hr, zero_add,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    exact ⟨rfl, rfl⟩
  change ((mem (arrBase + wOff) >>> bOff &&& 2 ^ k₀ - 1) ^^^
      ((mem (arrBase + wOff + 1) >>> 0 &&& 2 ^ k₁ - 1) <<< k₀)).testBit j = _
  rw [Nat.testBit_xor]
  by_cases hjk₀ : j < k₀
  · have hk₀_le : k₀ ≤ w - bOff := Nat.min_le_right k (w - bOff)
    obtain ⟨hd, hm⟩ := hdivMod wOff (bOff + j) (by omega) (by omega)
    rw [hd, hm, Nat.testBit_and, Nat.testBit_two_pow_sub_one, decide_eq_true hjk₀, Bool.and_true,
      Nat.testBit_shiftRight, Nat.testBit_shiftLeft, decide_eq_false (by omega),
      Bool.false_and, Bool.xor_false]
  · have hk₀_eq : k₀ = w - bOff := Nat.min_eq_right (by dsimp only [k₀, lowWidth] at hjk₀; omega)
    obtain ⟨hd, hm⟩ := hdivMod (wOff + 1) (j - k₀) (by omega)
      (by rw [Nat.mul_add, Nat.mul_one]; omega)
    have hlow : ((mem (arrBase + wOff) >>> bOff) &&& (2 ^ k₀ - 1)).testBit j = false :=
      Nat.testBit_lt_two_pow
        ((Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos _) one_pos)).trans_le
          (Nat.pow_le_pow_right two_pos (not_lt.mp hjk₀)))
    rw [hd, hm, hlow, Bool.false_xor, Nat.testBit_shiftLeft, decide_eq_true (not_lt.mp hjk₀),
      Bool.true_and, Nat.testBit_and, Nat.testBit_two_pow_sub_one, decide_eq_true (by omega),
      Bool.and_true, Nat.shiftRight_zero, Nat.add_assoc]

/-- Extract `N` bit-packed `k`-bit entries from `mem` starting at `arrBase`. -/
@[expose] def extractPackedSlice (arrBase N k w : ℕ) (mem : ℕ → ℕ) : Fin N → Fin (2 ^ k) :=
  fun i => ⟨readPacked arrBase k w mem i.val, readPacked_lt arrBase k w mem i.val⟩

/-- Additive homomorphism projecting `packedWords N k w` `w`-bit strings onto `N` `k`-bit strings
by reading bits `[idx * k, (idx + 1) * k)`. -/
@[expose] def bitPackedProjHom (N k w : ℕ) (hw : 0 < w) :
    (Fin (packedWords N k w) → BitString w) →+ (Fin N → BitString k) where
  toFun words i j :=
    words ⟨(i.val * k + j.val) / w, mul_add_div_lt_packedWords hw i.isLt j.isLt⟩
      ⟨(i.val * k + j.val) % w, Nat.mod_lt _ hw⟩
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem surjective_bitPackedProjHom {N k w : ℕ} (hw : 0 < w) :
    Function.Surjective (bitPackedProjHom N k w hw) := by
  intro target
  refine ⟨fun q r =>
    if hm : q.val * w + r.val < N * k then
      let hk : 0 < k := Nat.pos_of_ne_zero fun hk0 => by simp [hk0] at hm
      target ⟨(q.val * w + r.val) / k, Nat.div_lt_of_lt_mul (Nat.mul_comm k N ▸ hm)⟩
        ⟨(q.val * w + r.val) % k, Nat.mod_lt _ hk⟩
    else false, funext fun i => funext fun j => ?_⟩
  dsimp only [bitPackedProjHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  have hm_eq : (i.val * k + j.val) / w * w + (i.val * k + j.val) % w = i.val * k + j.val := by
    rw [Nat.mul_comm _ w]; exact Nat.div_add_mod _ w
  have hm_lt : (i.val * k + j.val) / w * w + (i.val * k + j.val) % w < N * k := by
    rw [hm_eq]; simpa only [Nat.mul_comm] using Nat.mul_add_lt_mul_of_lt_of_lt i.isLt j.isLt
  rw [dite_eq_left hm_lt]
  have hk_pos : 0 < k := Nat.zero_lt_of_lt j.isLt
  congr 1
  · exact Fin.ext (show ((i.val * k + j.val) / w * w + (i.val * k + j.val) % w) / k = i.val by
      rw [hm_eq, Nat.add_comm, Nat.mul_comm i.val k, Nat.add_mul_div_left _ _ hk_pos,
        Nat.div_eq_of_lt j.isLt, zero_add])
  · exact Fin.ext (show ((i.val * k + j.val) / w * w + (i.val * k + j.val) % w) % k = j.val by
      rw [hm_eq, Nat.add_comm, Nat.mul_comm i.val k, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt j.isLt])

/-- Map from a raw `w`-bit word slice `Fin (packedWords N k w) → Fin (2 ^ w)` to
`Fin N → Fin (2 ^ k)` matching `extractPackedSlice`. -/
@[expose] def packedSliceOfWords (N k w : ℕ) (hw : 0 < w)
    (words : Fin (packedWords N k w) → Fin (2 ^ w)) : Fin N → Fin (2 ^ k) :=
  (Equiv.piCongrRight fun _ : Fin N => BitString.equivFin k)
    (bitPackedProjHom N k w hw
      ((Equiv.piCongrRight fun _ : Fin (packedWords N k w) => (BitString.equivFin w).symm) words))

private theorem extractPackedSlice_eq_packedSliceOfWords {arrBase N k w : ℕ} (hw : 0 < w)
    (hkw : k ≤ w)
    {mem : ℕ → ℕ} (hmem : ∀ q < packedWords N k w, mem (arrBase + q) < 2 ^ w) :
    extractPackedSlice arrBase N k w mem =
      packedSliceOfWords N k w hw (Tabulation.extractSlice arrBase w (packedWords N k w) mem) := by
  funext i
  apply (BitString.equivFin k).symm.injective
  funext j
  rw [BitString.equivFin_symm_apply]
  change (readPacked arrBase k w mem i.val).testBit j.val =
    ((BitString.equivFin k).symm (BitString.equivFin k _)) j
  rw [Equiv.symm_apply_apply, testBit_readPacked hw hkw mem i.val j.isLt]
  change _ = ((BitString.equivFin w).symm
    (wordOfNat w (mem (arrBase + (i.val * k + j.val) / w)))) ⟨(i.val * k + j.val) % w, _⟩
  rw [BitString.equivFin_symm_apply,
    wordOfNat_val_of_lt (hmem _ (mul_add_div_lt_packedWords hw i.isLt j.isLt))]

/-- Pushforward of `PMF.uniformOfFintype (Fin (packedWords N k w) → Fin (2 ^ w))` along
`packedSliceOfWords` is `PMF.uniformOfFintype (Fin N → Fin (2 ^ k))`. -/
theorem uniformOfFintype_map_packedSliceOfWords (N k w : ℕ) (hw : 0 < w) :
    (PMF.uniformOfFintype (Fin (packedWords N k w) → Fin (2 ^ w))).map
      (packedSliceOfWords N k w hw) =
      PMF.uniformOfFintype (Fin N → Fin (2 ^ k)) := by
  let e_in : (Fin (packedWords N k w) → Fin (2 ^ w)) ≃ (Fin (packedWords N k w) → BitString w) :=
    Equiv.piCongrRight fun _ => (BitString.equivFin w).symm
  let e_out : (Fin N → BitString k) ≃ (Fin N → Fin (2 ^ k)) :=
    Equiv.piCongrRight fun _ => BitString.equivFin k
  have hfn : packedSliceOfWords N k w hw = e_out ∘ bitPackedProjHom N k w hw ∘ e_in := rfl
  rw [hfn, ← PMF.map_comp, ← PMF.map_comp, PMF.uniformOfFintype_map_equiv e_in,
    PMF.uniformOfFintype_map_addHom (bitPackedProjHom N k w hw) (surjective_bitPackedProjHom hw),
    PMF.uniformOfFintype_map_equiv e_out]

/-- Extract the full seed `(α, T₁, T₂)` from `[base, base + space w c_tab d b_char M_out)`. -/
@[expose] def extractSeed (base w w₀ c_tab d b_char M_out : ℕ) (mem : ℕ → ℕ) :
    Seed w₀ c_tab d b_char M_out :=
  (wordOfNat (w₀ - 1) (mem base),
    DoubleTabulation.topSliceEquiv (c_tab + 1) d b_char
      (extractPackedSlice (base + 1) (topEntries c_tab d b_char) b_char w mem),
    DoubleTabulation.botSliceEquiv d b_char M_out
      (extractPackedSlice (base + offBot w c_tab d b_char) (botEntries d b_char) M_out w mem))

/-- Representation predicate for `(α, T₁, T₂)` in `[base, base + space w c_tab d b_char M_out)`. -/
@[expose] def SeedRep (base w w₀ c_tab d b_char M_out : ℕ)
    (θ : Seed w₀ c_tab d b_char M_out) (mem : ℕ → ℕ) : Prop :=
  mem base = θ.1.val ∧
  (∀ (i : Fin (c_tab + 1)) (j : Fin d) (ch : Fin (2 ^ b_char)),
    readPacked (base + 1) b_char w mem ((j.val * (c_tab + 1) + i.val) * 2 ^ b_char + ch.val) =
      (θ.top i j ch).val) ∧
  (∀ (j : Fin d) (y : Fin (2 ^ b_char)),
    readPacked (base + offBot w c_tab d b_char) M_out w mem (j.val * 2 ^ b_char + y.val) =
      (θ.bot j y).val)

theorem seedRep_extractSeed {base w w₀ c_tab d b_char M_out : ℕ} {mem : ℕ → ℕ}
    (hα : mem base < 2 ^ (w₀ - 1)) :
    SeedRep base w w₀ c_tab d b_char M_out
      (extractSeed base w w₀ c_tab d b_char M_out mem) mem := by
  refine ⟨(wordOfNat_val_of_lt hα).symm, fun i j ch => ?_, fun j y => ?_⟩
  · change readPacked (base + 1) b_char w mem _ =
      readPacked (base + 1) b_char w mem
        (DoubleTabulation.topIndexEquiv (c_tab + 1) d b_char (i, j, ch)).val
    rw [DoubleTabulation.val_topIndexEquiv]
  · change readPacked (base + offBot w c_tab d b_char) M_out w mem _ =
      readPacked (base + offBot w c_tab d b_char) M_out w mem (finProdFinEquiv (j, y)).val
    rw [finProdFinEquiv_apply_val]
    congr 1; dsimp only; ring

theorem extractSeed_eq_of_seedRep {base w w₀ c_tab d b_char M_out : ℕ}
    {θ : Seed w₀ c_tab d b_char M_out} {mem : ℕ → ℕ}
    (hrep : SeedRep base w w₀ c_tab d b_char M_out θ mem) :
    extractSeed base w w₀ c_tab d b_char M_out mem = θ := by
  rcases θ with ⟨α, T₁, T₂⟩
  rcases hrep with ⟨hα, hT₁, hT₂⟩
  refine Prod.ext (Fin.ext (by dsimp only [extractSeed]; rw [hα, wordOfNat_val_of_lt α.isLt]))
    (Prod.ext (funext fun i => funext fun j => funext fun ch => Fin.ext ?_)
      (funext fun j => funext fun y => Fin.ext ?_))
  · change readPacked _ _ _ _ (DoubleTabulation.topIndexEquiv _ _ _ (i, j, ch)).val = _
    rw [DoubleTabulation.val_topIndexEquiv]; exact hT₁ i j ch
  · change readPacked _ _ _ _ (finProdFinEquiv (j, y)).val = _
    rw [finProdFinEquiv_apply_val, show (j, y).2.val + 2 ^ b_char * (j, y).1.val =
      j.val * 2 ^ b_char + y.val by dsimp only; ring]
    exact hT₂ j y

theorem seedRep_congr_mem {base w w₀ c_tab d b_char M_out : ℕ}
    {θ : Seed w₀ c_tab d b_char M_out} {mem mem' : ℕ → ℕ} (hw : 0 < w)
    (hrep : SeedRep base w w₀ c_tab d b_char M_out θ mem)
    (heq : ∀ a, base ≤ a → a < base + space w c_tab d b_char M_out → mem' a = mem a) :
    SeedRep base w w₀ c_tab d b_char M_out θ mem' := by
  refine ⟨(heq base le_rfl (by wram_omega)).trans hrep.1, fun i j ch => ?_, fun j y => ?_⟩
  · rw [readPacked_congr hw (fun a ⟨ha1, ha2⟩ => heq a (by omega) (by wram_omega))
      (topIdx_lt_topEntries i.isLt j.isLt ch.isLt)]
    exact hrep.2.1 i j ch
  · have hidx : j.val * 2 ^ b_char + y.val < botEntries d b_char := by
      simpa only [Nat.mul_comm] using Nat.mul_add_lt_mul_of_lt_of_lt j.isLt y.isLt
    rw [readPacked_congr hw (fun a ⟨ha1, ha2⟩ => heq a (by omega) (by wram_omega)) hidx]
    exact hrep.2.2 j y

/-- Congruence of `SeedRep` under memory updates preserving `[base, base + space)`. -/
theorem SeedRep.congr_on {base w w₀ c_tab d b_char M_out : ℕ}
    {θ : Seed w₀ c_tab d b_char M_out} {mem mem' : ℕ → ℕ}
    (hrep : SeedRep base w w₀ c_tab d b_char M_out θ mem) (hw : 0 < w)
    (heq : ∀ a, base ≤ a → a < base + space w c_tab d b_char M_out → mem' a = mem a) :
    SeedRep base w w₀ c_tab d b_char M_out θ mem' :=
  seedRep_congr_mem hw hrep heq

/-! ### Single-pass `randFillLoop` seed resampling (`resampleCode`) -/

/-- Combined additive homomorphism projecting `topWords + botWords` `w`-bit strings onto the pair of
bit-packed slices `(Fin topEntries → BitString b_char) × (Fin botEntries → BitString M_out)`. -/
private def bothPackedProjHom (w c_tab d b_char M_out : ℕ) (hw : 0 < w) :
    (Fin (topWords w c_tab d b_char + botWords w d b_char M_out) → BitString w) →+
      (Fin (topEntries c_tab d b_char) → BitString b_char) ×
        (Fin (botEntries d b_char) → BitString M_out) where
  toFun words :=
    (bitPackedProjHom (topEntries c_tab d b_char) b_char w hw
        (fun q => words (Fin.castAdd (botWords w d b_char M_out) q)),
      bitPackedProjHom (botEntries d b_char) M_out w hw
        (fun q => words (Fin.natAdd (topWords w c_tab d b_char) q)))
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem surjective_bothPackedProjHom {w c_tab d b_char M_out : ℕ} (hw : 0 < w) :
    Function.Surjective (bothPackedProjHom w c_tab d b_char M_out hw) := by
  rintro ⟨t₁, t₂⟩
  obtain ⟨w₁, hw₁⟩ := surjective_bitPackedProjHom hw t₁
  obtain ⟨w₂, hw₂⟩ := surjective_bitPackedProjHom hw t₂
  refine ⟨Fin.addCases w₁ w₂, ?_⟩
  have hl : (fun q => Fin.addCases w₁ w₂ (Fin.castAdd (botWords w d b_char M_out) q)) = w₁ :=
    funext Fin.addCases_left
  have hr : (fun q => Fin.addCases w₁ w₂ (Fin.natAdd (topWords w c_tab d b_char) q)) = w₂ :=
    funext Fin.addCases_right
  exact Prod.ext
    ((congrArg (bitPackedProjHom (topEntries c_tab d b_char) b_char w hw) hl).trans hw₁)
    ((congrArg (bitPackedProjHom (botEntries d b_char) M_out w hw) hr).trans hw₂)

/-- Extract `(T₁, T₂)` from a combined `(topWords + botWords)`-word slice of `< 2 ^ w` words. -/
private def tablesOfWords (w c_tab d b_char M_out : ℕ) (hw : 0 < w)
    (words : Fin (topWords w c_tab d b_char + botWords w d b_char M_out) → Fin (2 ^ w)) :
    DoubleTabTopSeed (c_tab + 1) d b_char × DoubleTabBotSeed d b_char M_out :=
  let pair := bothPackedProjHom w c_tab d b_char M_out hw
    ((Equiv.piCongrRight fun _ => (BitString.equivFin w).symm) words)
  (DoubleTabulation.topSliceEquiv (c_tab + 1) d b_char
      ((Equiv.piCongrRight fun _ => BitString.equivFin b_char) pair.1),
    DoubleTabulation.botSliceEquiv d b_char M_out
      ((Equiv.piCongrRight fun _ => BitString.equivFin M_out) pair.2))

private theorem uniformOfFintype_map_tablesOfWords (w c_tab d b_char M_out : ℕ) (hw : 0 < w) :
    (PMF.uniformOfFintype
      (Fin (topWords w c_tab d b_char + botWords w d b_char M_out) → Fin (2 ^ w))).map
        (tablesOfWords w c_tab d b_char M_out hw) =
      PMF.uniformOfFintype
        (DoubleTabTopSeed (c_tab + 1) d b_char × DoubleTabBotSeed d b_char M_out) := by
  let e_in :
      (Fin (topWords w c_tab d b_char + botWords w d b_char M_out) → Fin (2 ^ w)) ≃
        (Fin (topWords w c_tab d b_char + botWords w d b_char M_out) → BitString w) :=
    Equiv.piCongrRight fun _ => (BitString.equivFin w).symm
  let e_out :
      ((Fin (topEntries c_tab d b_char) → BitString b_char) ×
        (Fin (botEntries d b_char) → BitString M_out)) ≃
        (DoubleTabTopSeed (c_tab + 1) d b_char × DoubleTabBotSeed d b_char M_out) :=
    Equiv.prodCongr
      ((Equiv.piCongrRight fun _ => BitString.equivFin b_char).trans
        (DoubleTabulation.topSliceEquiv (c_tab + 1) d b_char))
      ((Equiv.piCongrRight fun _ => BitString.equivFin M_out).trans
        (DoubleTabulation.botSliceEquiv d b_char M_out))
  have hfn : tablesOfWords w c_tab d b_char M_out hw =
      e_out ∘ bothPackedProjHom w c_tab d b_char M_out hw ∘ e_in := rfl
  rw [hfn, ← PMF.map_comp, ← PMF.map_comp, PMF.uniformOfFintype_map_equiv e_in,
    PMF.uniformOfFintype_map_addHom _ (surjective_bothPackedProjHom hw),
    PMF.uniformOfFintype_map_equiv e_out]

/-- Structured Word-RAM program on `Data 12` (keeping `reg 0 = base`) that samples `(α, T₁, T₂)`
into `[base, base + space w c_tab d b_char M_out)`. -/
@[expose] def resampleCode (w w₀ c_tab d b_char M_out : ℕ) : Code .exact 12 :=
  .seq (.seq (.op (.const 5 (2 ^ (w₀ - 1) - 1))) (.rand 7 5))
    (.seq
      (.seq (.op (.store 0 7))
      (.seq (.op (.const 6 1))
      (.seq (.op (.exactBin .add 3 0 6))
      (.seq (.op (.const 4 (space w c_tab d b_char M_out)))
      (.seq (.op (.exactBin .add 4 0 4))
            (.op (.const 5 (2 ^ w - 1))))))))
      (Tabulation.randFillLoop.rename DoubleTabulation.fillMap12))

/-- Instruction count `5 * (topWords + botWords) + 10` of `resampleCode`. -/
@[expose] def resampleSteps (w c_tab d b_char M_out : ℕ) : ℕ :=
  5 * (topWords w c_tab d b_char + botWords w d b_char M_out) + 10

attribute [local wram_arith] resampleSteps

/-- Explicit `ProbComp (Data 12 × ℕ)` induced by `resampleCode`. -/
@[expose] noncomputable def resampleComp (base w w₀ c_tab d b_char M_out : ℕ) (x : Data 12) :
    ProbComp (Data 12 × ℕ) := do
  let kα ← ProbComp.unifFin (2 ^ (w₀ - 1) - 1)
  let x1 := (((((((x.set 5 (2 ^ (w₀ - 1) - 1)).set 7 kα.val).write base kα.val).set 6 1).set 3
    (base + 1)).set 4 (base + space w c_tab d b_char M_out)).set 5 (2 ^ w - 1))
  let z ← Tabulation.randFillComp w (base + 1)
    (topWords w c_tab d b_char + botWords w d b_char M_out)
    (x1.comap DoubleTabulation.fillMap12)
  pure (z.1.extend DoubleTabulation.fillMap12 x1, 2 + (6 + z.2))

theorem resampleCode_execRand {w w₀ base c_tab d b_char M_out : ℕ} {x : Data 12}
    (hw : 0 < w) (hw₀_le : w₀ ≤ w) (hbase : x.regs 0 = base)
    (hfit_end : Fits w (base + space w c_tab d b_char M_out)) :
    ExecRand w (resampleCode w w₀ c_tab d b_char M_out) x
      (resampleComp base w w₀ c_tab d b_char M_out x) := by
  have hfit_mask_α : Fits w (2 ^ (w₀ - 1) - 1) :=
    (Nat.sub_lt (Nat.two_pow_pos _) one_pos).trans_le (Nat.pow_le_pow_right two_pos (by omega))
  have hfit_mask_w : Fits w (2 ^ w - 1) := Nat.sub_lt (Nat.two_pow_pos w) one_pos
  have hfit_one : Fits w 1 := Nat.one_lt_two_pow hw.ne'
  have hsp_eq : (base + 1) + (topWords w c_tab d b_char + botWords w d b_char M_out) =
      base + space w c_tab d b_char M_out := by wram_omega
  unfold resampleCode
  wram_rand_exec (disch := first | fits | omega | wram_omega) [hbase]
  · wram_rand_call (Tabulation.randFillLoop_execRand (bits := w) (arrBase := base + 1)
      (topWords w c_tab d b_char + botWords w d b_char M_out)
      (by simp +decide [DoubleTabulation.fillMap12, Data.comap, Data.write])
      (by simp +decide [DoubleTabulation.fillMap12, Data.comap, Data.write, hsp_eq])
      (by simp +decide [DoubleTabulation.fillMap12, Data.comap, Data.write])
      (by simp +decide [DoubleTabulation.fillMap12, Data.comap, Data.write])
      (hsp_eq.symm ▸ hfit_end) hfit_mask_w) renamed DoubleTabulation.injective_fillMap12
  · have hset : ∀ (d : Data 12) (a b : ℕ), (d.set 4 a).set 4 b = d.set 4 b := fun _ _ _ => by
      simp [Data.set]
    simp only [resampleComp, ← bind_pure_comp, bind_assoc, pure_bind, hset]
    congr 1; funext kα; congr 1; funext z; congr 2; omega

theorem isQueryBounded_resampleComp (base w w₀ c_tab d b_char M_out : ℕ) (x : Data 12) :
    (resampleComp base w w₀ c_tab d b_char M_out x).IsQueryBounded
      (1 + (topWords w c_tab d b_char + botWords w d b_char M_out)) := by
  dsimp only [resampleComp]
  refine (ProbComp.isQueryBounded_unifFin _).bind fun kα => ?_
  simpa only [Nat.add_zero] using
    (Tabulation.isQueryBounded_randFillComp w (base + 1)
      (topWords w c_tab d b_char + botWords w d b_char M_out) _).bind fun _ => .pure _ 0

/-- Pathwise postcondition of `resampleComp`: executes in `resampleSteps` instructions, preserves
`reg 0 = base`, establishes `SeedRep`, preserves `Bounded w`, and modifies only
`[base, base + space)`. -/
theorem mem_support_resampleComp {base w w₀ c_tab d b_char M_out : ℕ} {x : Data 12}
    (hw : 0 < w) (hw₀_le : w₀ ≤ w) (hbase : x.regs 0 = base)
    (hfit_end : Fits w (base + space w c_tab d b_char M_out))
    (hx_bdd : x.Bounded w) {z : Data 12 × ℕ}
    (hz : z ∈ (resampleComp base w w₀ c_tab d b_char M_out x).support) :
    z.1.regs 0 = base ∧
    SeedRep base w w₀ c_tab d b_char M_out
      (extractSeed base w w₀ c_tab d b_char M_out z.1.mem) z.1.mem ∧
    (∀ q < topWords w c_tab d b_char + botWords w d b_char M_out, z.1.mem (base + 1 + q) < 2 ^ w) ∧
    (∀ a, (a < base ∨ base + space w c_tab d b_char M_out ≤ a) → z.1.mem a = x.mem a) ∧
    z.1.Bounded w ∧
    z.2 = resampleSteps w c_tab d b_char M_out := by
  have hbdd := (resampleCode_execRand hw hw₀_le hbase hfit_end).bounded hx_bdd hz
  dsimp only [resampleComp] at hz
  supp_cases hz with ⟨kα, zf, hzf, rfl⟩
  obtain ⟨hsteps, _, _, _, _, hextra, hlt, hframe⟩ := Tabulation.mem_support_randFillComp hzf
  have hmem_base : zf.1.mem base = kα.val := by
    rw [hframe base (Or.inl (by omega))]
    simp [Data.write]
  refine ⟨?_, seedRep_extractSeed (by
    change zf.1.mem base < 2 ^ (w₀ - 1)
    rw [hmem_base]
    have := kα.isLt; have : 1 ≤ 2 ^ (w₀ - 1) := Nat.one_le_two_pow; omega),
    hlt, fun a ha => ?_, hbdd, by wram_omega [hsteps]⟩
  · change ((zf.1.extend DoubleTabulation.fillMap12 _).comap DoubleTabulation.fillMap12).regs
      Tabulation.regExtra = base
    rw [Data.comap_extend DoubleTabulation.injective_fillMap12, hextra]
    simp +decide [DoubleTabulation.fillMap12, Data.comap, Data.write, hbase]
  · rw [show (zf.1.extend DoubleTabulation.fillMap12 _).mem a = zf.1.mem a from rfl,
      hframe a (by wram_omega)]
    simp [Data.write, Function.update_of_ne (by wram_omega : a ≠ base)]

private theorem extractSeed_eq_tablesOfWords {base w w₀ c_tab d b_char M_out : ℕ}
    (hw : 0 < w) (hb_le : b_char ≤ w) (hM_le : M_out ≤ w) {mem : ℕ → ℕ}
    (hlt : ∀ q < topWords w c_tab d b_char + botWords w d b_char M_out,
      mem (base + 1 + q) < 2 ^ w) :
    extractSeed base w w₀ c_tab d b_char M_out mem =
      (wordOfNat (w₀ - 1) (mem base),
        tablesOfWords w c_tab d b_char M_out hw
          (Tabulation.extractSlice (base + 1) w
            (topWords w c_tab d b_char + botWords w d b_char M_out) mem)) := by
  have htop := extractPackedSlice_eq_packedSliceOfWords (arrBase := base + 1)
    (N := topEntries c_tab d b_char) (k := b_char) hw hb_le
    fun q hq => hlt q (by wram_omega)
  have hbot := extractPackedSlice_eq_packedSliceOfWords
    (arrBase := base + offBot w c_tab d b_char) (N := botEntries d b_char) (k := M_out) hw hM_le
    fun q hq => by
      have := hlt (topWords w c_tab d b_char + q) (by wram_omega)
      rwa [show base + 1 + (topWords w c_tab d b_char + q) =
        base + offBot w c_tab d b_char + q by wram_omega] at this
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · dsimp only [extractSeed, tablesOfWords]; rw [htop]; rfl
  · dsimp only [extractSeed, tablesOfWords]; rw [hbot]
    dsimp only [packedSliceOfWords, bothPackedProjHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    congr 3; funext q
    change (BitString.equivFin w).symm (wordOfNat w (mem (base + offBot _ _ _ _ + q.val))) =
      (BitString.equivFin w).symm (wordOfNat w (mem (base + 1 + (topWords _ _ _ _ + q.val))))
    rw [show base + offBot w c_tab d b_char + q.val =
      base + 1 + (topWords w c_tab d b_char + q.val) by wram_omega]

/-- **Exact product uniformity of `resampleComp`**: when `0 < w`, `b_char ≤ w`, and `M_out ≤ w`,
the extracted seed `extractSeed base w w₀ c_tab d b_char M_out z.1.mem` under `resampleComp` has
exact uniform distribution `PMF.uniformOfFintype (Seed w₀ c_tab d b_char M_out)`. -/
theorem map_extractSeed_eval_resampleComp {base w w₀ c_tab d b_char M_out : ℕ}
    (hw : 0 < w) (hb_le : b_char ≤ w) (hM_le : M_out ≤ w) (x : Data 12) :
    ((resampleComp base w w₀ c_tab d b_char M_out x).eval).map
      (fun z => extractSeed base w w₀ c_tab d b_char M_out z.1.mem) =
      PMF.uniformOfFintype (Seed w₀ c_tab d b_char M_out) := by
  let eα : Fin (2 ^ (w₀ - 1) - 1 + 1) ≃ Fin (2 ^ (w₀ - 1)) :=
    finCongr (Nat.sub_add_cancel Nat.one_le_two_pow)
  let W_tot := topWords w c_tab d b_char + botWords w d b_char M_out
  dsimp only [resampleComp]
  rw [ProbComp.eval_bind, ProbComp.eval_unifFin, PMF.map_bind]
  have hinner (kα : Fin (2 ^ (w₀ - 1) - 1 + 1)) :
      (let x1 := (((((((x.set 5 (2 ^ (w₀ - 1) - 1)).set 7 kα.val).write base kα.val).set 6 1).set 3
        (base + 1)).set 4 (base + space w c_tab d b_char M_out)).set 5 (2 ^ w - 1))
       (do let z ← Tabulation.randFillComp w (base + 1) W_tot (x1.comap DoubleTabulation.fillMap12)
           pure (z.1.extend DoubleTabulation.fillMap12 x1, 2 + (6 + z.2))).eval).map
        (fun z : Data 12 × ℕ => extractSeed base w w₀ c_tab d b_char M_out z.1.mem) =
      (PMF.uniformOfFintype
        (DoubleTabTopSeed (c_tab + 1) d b_char × DoubleTabBotSeed d b_char M_out)).map
          (fun T => (eα kα, T)) := by
    dsimp only
    set x1 := (((((((x.set 5 (2 ^ (w₀ - 1) - 1)).set 7 kα.val).write base kα.val).set 6 1).set 3
      (base + 1)).set 4 (base + space w c_tab d b_char M_out)).set 5 (2 ^ w - 1))
    rw [bind_pure_comp, ProbComp.eval_map, PMF.map_comp]
    trans ((Tabulation.randFillComp w (base + 1) W_tot
        (x1.comap DoubleTabulation.fillMap12)).eval.map
      ((fun T => (eα kα, T)) ∘ tablesOfWords w c_tab d b_char M_out hw ∘
        fun zf : Data 6 × ℕ => Tabulation.extractSlice (base + 1) w W_tot zf.1.mem))
    · refine Cslib.Probability.PMF.map_congr_on_support _ _ _ fun zf hzf => ?_
      rw [ProbComp.support_eval] at hzf
      obtain ⟨_, _, _, _, _, _, hlt, hframe⟩ := Tabulation.mem_support_randFillComp hzf
      have hbase : zf.1.mem base = kα.val := by
        rw [hframe base (Or.inl (by omega))]; simp [x1, Data.write]
      dsimp only [Function.comp_apply, Data.extend]
      rw [extractSeed_eq_tablesOfWords hw hb_le hM_le hlt, hbase, wordOfNat_unifFin]
    · rw [← PMF.map_comp, ← PMF.map_comp, Tabulation.map_extractSlice_eval_randFillComp,
        uniformOfFintype_map_tablesOfWords]
  have hbind : _ = (PMF.uniformOfFintype _).bind
      (fun kα => (PMF.uniformOfFintype _).map fun T => (eα kα, T)) :=
    congrArg (PMF.uniformOfFintype _).bind (funext hinner)
  rw [hbind]
  have hprod : ((PMF.uniformOfFintype (Fin (2 ^ (w₀ - 1) - 1 + 1))).map eα).bind
      (fun α => (PMF.uniformOfFintype _).map fun T => (α, T)) =
      PMF.uniformOfFintype (Seed w₀ c_tab d b_char M_out) := by
    rw [PMF.uniformOfFintype_map_equiv eα]; exact uniformOfFintype_prod _ _
  rwa [PMF.bind_map] at hprod


/-! ## Section 3: `Memory.Prog` + `realize` deterministic `O(c_tab * d)` evaluation -/

/-- Runtime register block of 16 precomputed hash parameters for parameter-free `Realizes`. -/
@[expose] def HashParams : Type := Fin 16 → ℕ

instance : WordEncoding HashParams := ⟨16, Function.Embedding.refl (Fin 16 → ℕ)⟩

/-- Construct the 16-word parameter vector for `(w, w₀, R, c_tab, d, b_char, M_out)`. -/
@[expose] def mkHashParams (w w₀ R c_tab d b_char M_out : ℕ) : HashParams := fun i =>
  match i.val with
  | 0 => w
  | 1 => w₀ - R
  | 2 => (w₀ - 1) / 2
  | 3 => 2 * ((w₀ - 1) / 2)
  | 4 => 2 ^ (w₀ - 1) - 1
  | 5 => 2 ^ ((w₀ - 1) / 2) - 1
  | 6 => 2 ^ ((w₀ - 1) - (w₀ - 1) / 2) - 1
  | 7 => 2 ^ ((w₀ - 1) - 2 * ((w₀ - 1) / 2)) - 1
  | 8 => b_char
  | 9 => 2 ^ b_char - 1
  | 10 => 2 ^ b_char
  | 11 => M_out
  | 12 => offBot w c_tab d b_char
  | 13 => c_tab + 1
  | 14 => c_tab
  | _ => d

/-- Word width $w$ in the hash parameter vector. -/
@[expose] def hpW (hp : HashParams) : ℕ := hp 0
/-- Shift count $w₀ - R$ in the hash parameter vector. -/
@[expose] def hpShiftR (hp : HashParams) : ℕ := hp 1
/-- Half-chunk bitwidth $\lfloor(w₀ - 1) / 2\rfloor$ in the hash parameter vector. -/
@[expose] def hpHalfM (hp : HashParams) : ℕ := hp 2
/-- Double half-chunk bitwidth $2 \lfloor(w₀ - 1) / 2\rfloor$ in the hash parameter vector. -/
@[expose] def hpTwoHalfM (hp : HashParams) : ℕ := hp 3
/-- Low chunk mask $2^{w₀ - 1} - 1$ in the hash parameter vector. -/
@[expose] def hpMaskM (hp : HashParams) : ℕ := hp 4
/-- First half-chunk mask in the hash parameter vector. -/
@[expose] def hpMaskHalf (hp : HashParams) : ℕ := hp 5
/-- Second half-chunk mask in the hash parameter vector. -/
@[expose] def hpMaskRem (hp : HashParams) : ℕ := hp 6
/-- Top remainder bit mask in the hash parameter vector. -/
@[expose] def hpMaskTop (hp : HashParams) : ℕ := hp 7
/-- Character bitwidth $b$ in the hash parameter vector. -/
@[expose] def hpBChar (hp : HashParams) : ℕ := hp 8
/-- Character mask $2^b - 1$ in the hash parameter vector. -/
@[expose] def hpMaskB (hp : HashParams) : ℕ := hp 9
/-- Character radix $2^b$ in the hash parameter vector. -/
@[expose] def hpPowB (hp : HashParams) : ℕ := hp 10
/-- Output word count $M_{\mathrm{out}}$ in the hash parameter vector. -/
@[expose] def hpMOut (hp : HashParams) : ℕ := hp 11
/-- Memory word offset of bottom table in the hash parameter vector. -/
@[expose] def hpOffBot (hp : HashParams) : ℕ := hp 12
/-- Chunk count plus one ($c_{\mathrm{tab}} + 1$) in the hash parameter vector. -/
@[expose] def hpCPlusOne (hp : HashParams) : ℕ := hp 13
/-- Chunk count $c_{\mathrm{tab}}$ in the hash parameter vector. -/
@[expose] def hpCTab (hp : HashParams) : ℕ := hp 14
/-- Dimension $d$ in the hash parameter vector. -/
@[expose] def hpD (hp : HashParams) : ℕ := hp 15

@[simp] theorem hpW_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpW (mkHashParams w w₀ R c_tab d b_char M_out) = w := rfl
@[simp] theorem hpShiftR_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpShiftR (mkHashParams w w₀ R c_tab d b_char M_out) = w₀ - R := rfl
@[simp] theorem hpHalfM_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpHalfM (mkHashParams w w₀ R c_tab d b_char M_out) = (w₀ - 1) / 2 := rfl
@[simp] theorem hpTwoHalfM_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpTwoHalfM (mkHashParams w w₀ R c_tab d b_char M_out) = 2 * ((w₀ - 1) / 2) := rfl
@[simp] theorem hpMaskM_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpMaskM (mkHashParams w w₀ R c_tab d b_char M_out) = 2 ^ (w₀ - 1) - 1 := rfl
@[simp] theorem hpMaskHalf_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpMaskHalf (mkHashParams w w₀ R c_tab d b_char M_out) = 2 ^ ((w₀ - 1) / 2) - 1 := rfl
@[simp] theorem hpMaskRem_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpMaskRem (mkHashParams w w₀ R c_tab d b_char M_out) = 2 ^ ((w₀ - 1) - (w₀ - 1) / 2) - 1 := rfl
@[simp] theorem hpMaskTop_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpMaskTop (mkHashParams w w₀ R c_tab d b_char M_out) =
      2 ^ ((w₀ - 1) - 2 * ((w₀ - 1) / 2)) - 1 := rfl
@[simp] theorem hpBChar_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpBChar (mkHashParams w w₀ R c_tab d b_char M_out) = b_char := rfl
@[simp] theorem hpMaskB_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpMaskB (mkHashParams w w₀ R c_tab d b_char M_out) = 2 ^ b_char - 1 := rfl
@[simp] theorem hpPowB_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpPowB (mkHashParams w w₀ R c_tab d b_char M_out) = 2 ^ b_char := rfl
@[simp] theorem hpMOut_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpMOut (mkHashParams w w₀ R c_tab d b_char M_out) = M_out := rfl
@[simp] theorem hpOffBot_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpOffBot (mkHashParams w w₀ R c_tab d b_char M_out) = offBot w c_tab d b_char := rfl
@[simp] theorem hpCPlusOne_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpCPlusOne (mkHashParams w w₀ R c_tab d b_char M_out) = c_tab + 1 := rfl
@[simp] theorem hpCTab_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpCTab (mkHashParams w w₀ R c_tab d b_char M_out) = c_tab := rfl
@[simp] theorem hpD_mk (w w₀ R c_tab d b_char M_out : ℕ) :
    hpD (mkHashParams w w₀ R c_tab d b_char M_out) = d := rfl

/-- Well-formedness envelope for `HashParams` at `base` on a `w`-bit machine. -/
@[expose] def HashEnv (w : ℕ) (hp : HashParams) (base : ℕ) : Prop :=
  ∃ w₀ R c_tab d b_char M_out,
    0 < w ∧ 0 < w₀ ∧ w₀ ≤ w ∧ b_char < w ∧ M_out ≤ w ∧
    topEntries c_tab d b_char < 2 ^ w ∧
    botEntries d b_char < 2 ^ w ∧
    c_tab + 1 < 2 ^ w ∧ d < 2 ^ w ∧
    Fits w (base + space w c_tab d b_char M_out) ∧
    hp = mkHashParams w w₀ R c_tab d b_char M_out

/-- Fit of all 16 words in `mkHashParams` under `HashEnv`. -/
theorem fits_mkHashParams {w base : ℕ} {hp : HashParams} (henv : HashEnv w hp base) (i : Fin 16) :
    Fits w (hp i) := by
  obtain ⟨w₀, R, c_tab, d, b_char, M_out, hw, hw₀, hw₀_le, hb, hM, _, _, hc1, hd_lt, hfit_sp,
    rfl⟩ := henv
  have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
  have mask_lt {k : ℕ} (hk : k ≤ w) : 2 ^ k - 1 < 2 ^ w :=
    (Nat.sub_lt (Nat.two_pow_pos k) one_pos).trans_le (Nat.pow_le_pow_right two_pos hk)
  fin_cases i <;> dsimp only [mkHashParams, Fits]
  · exact hw_lt
  · exact (Nat.sub_le w₀ R).trans_lt (hw₀_le.trans_lt hw_lt)
  · exact (Nat.div_le_self _ 2).trans_lt ((Nat.sub_le w₀ 1).trans_lt (hw₀_le.trans_lt hw_lt))
  · exact (Nat.mul_div_le (w₀ - 1) 2).trans_lt ((Nat.sub_le w₀ 1).trans_lt (hw₀_le.trans_lt hw_lt))
  · exact mask_lt (by omega)
  · exact mask_lt (by omega)
  · exact mask_lt (by omega)
  · exact mask_lt (by omega)
  · exact hb.trans hw_lt
  · exact mask_lt hb.le
  · exact Nat.pow_lt_pow_right (by decide) hb
  · exact hM.trans_lt hw_lt
  · exact hfit_sp.of_le (show offBot w c_tab d b_char ≤ base + space w c_tab d b_char M_out by
      wram_omega)
  · exact hc1
  · exact (Nat.lt_succ_self c_tab).trans hc1
  · exact hd_lt

/-- An iteration whose state-preserving body has constant memory cost `k` costs `n * k`. -/
private theorem memoryCost_iterate_const {δ σ : Type} {body : δ × σ → Memory.Prog σ} {d : δ}
    (s : Memory.State) (k : ℕ)
    (hst : ∀ a, (Memory.spec 0).clientState s (body (d, a)) = s)
    (hcost : ∀ a, memoryCost (body (d, a)) s = k) (n : ℕ) (a : σ) :
    memoryCost (iterate body d n a) s = n * k := by
  induction n generalizing a with
  | zero => simp [iterate]
  | succ n ih =>
    unfold iterate
    rw [memoryCost_bind', hcost, hst, ih]
    ring

/-- Inner-loop body (`p = ((hp, (base, j)), ((i, y_acc), r_cur))`): extracts character `i` from
`r_cur`, reads `T₁[i, j, ch]`, XORs into `y_acc`, and shifts `r_cur` right by `b_char`. -/
@[expose] def innerStepGenProg :
    (HashParams × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ) → Memory.Prog ((ℕ × ℕ) × ℕ)
  | ((hp, (base, j)), ((i, y_acc), r_cur)) => do
    let ch ← pure (r_cur &&& hpMaskB hp)
    let row ← pure (j * hpCPlusOne hp + i)
    let idx₁ ← pure (row * hpPowB hp + ch)
    let one_off ← pure 1
    let t_val ← readPackedGenProg (((base, one_off), (hpBChar hp, hpW hp)), idx₁)
    let i_next ← pure (i + 1)
    let y_next ← pure (y_acc ^^^ t_val)
    let r_next ← pure (r_cur >>> hpBChar hp)
    pure ((i_next, y_next), r_next)

@[simp]
theorem memoryCost_innerStepGenProg (p : (HashParams × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ))
    (s : Memory.State) :
    memoryCost (innerStepGenProg p) s = 2 := by
  rcases p with ⟨⟨hp, base, j⟩, ⟨i, y_acc⟩, r_cur⟩
  rfl

private theorem memoryCost_innerStepGenProg_pos (p : (HashParams × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ))
    (s : Memory.State) :
    1 ≤ memoryCost (innerStepGenProg p) s := by
  rcases p with ⟨⟨hp, base, j⟩, ⟨i, y_acc⟩, r_cur⟩
  simp

/-- Precondition for `innerStepGenProg`. -/
@[expose] def InnerStepGenPre (w : ℕ) :
    (HashParams × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ) → Memory.State → Prop
  | ((hp, (base, j)), ((i, y_acc), _r_cur)), _s =>
    HashEnv w hp base ∧
    j < hpD hp ∧
    i < hpCTab hp ∧
    y_acc < hpPowB hp

private theorem clientResult_innerStepGenProg (hp : HashParams) (base j i y r : ℕ)
    (s : Memory.State) :
    (Memory.spec 0).clientResult s (innerStepGenProg ((hp, (base, j)), ((i, y), r))) =
      ((i + 1, y ^^^ readPacked (base + 1) (hpBChar hp) (hpW hp) s.mem
        ((j * hpCPlusOne hp + i) * hpPowB hp + (r &&& hpMaskB hp))), r >>> hpBChar hp) := rfl

private theorem clientState_iterate_innerStep (ctx : HashParams × (ℕ × ℕ)) (n : ℕ)
    (st : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (iterate innerStepGenProg ctx n st) = s :=
  clientState_iterate_eq_of innerStepGenProg ctx (fun _ _ => rfl) n st s

private theorem memoryCost_iterate_innerStep (ctx : HashParams × (ℕ × ℕ)) (n : ℕ)
    (st : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (iterate innerStepGenProg ctx n st) s = 2 * n := by
  simpa only [Nat.mul_comm] using
    memoryCost_iterate_const s 2 (fun _ => rfl) (fun _ => memoryCost_innerStepGenProg _ s) n st

/-- Shared side-condition pack for a top-table `readPackedGenProg` lookup in `realize`. -/
private theorem topRead_realizeObligs {w c_tab d_par b_char M_out base i j ch : ℕ}
    (hw : 0 < w) (hb : b_char ≤ w) (htop_lt : topEntries c_tab d_par b_char < 2 ^ w)
    (hfit_sp : Fits w (base + space w c_tab d_par b_char M_out))
    (hi : i < c_tab + 1) (hj : j < d_par) (hch : ch < 2 ^ b_char) :
    Fits w (j * (c_tab + 1) + i) ∧
    Fits w ((j * (c_tab + 1) + i) * 2 ^ b_char + ch) ∧
    Fits w 1 ∧
    ∃ N, True ∧ 0 < w ∧ b_char ≤ w ∧
      (j * (c_tab + 1) + i) * 2 ^ b_char + ch < N ∧
      Fits w (base + 1 + packedWords N b_char w) :=
  ⟨(topRow_lt_topEntries hi hj).trans htop_lt,
    (topIdx_lt_topEntries hi hj hch).trans htop_lt,
    Nat.one_lt_two_pow hw.ne',
    topEntries c_tab d_par b_char, trivial, hw, hb, topIdx_lt_topEntries hi hj hch, by wram_omega⟩

private theorem realizes_innerStepGen :
    Realizes .exact innerStepGenProg
      (WordEncoding.encode (α := (HashParams × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      InnerStepGenPre
      (fun _ _ => 0) := by
  realize [realizes_readPackedGen]
  all_goals (
    rcases d with ⟨⟨hp, base, j⟩, ⟨i, y⟩, r⟩
    obtain ⟨⟨w₀, R, c_tab, d_par, b_char, M_out, hw, _, _, hb, _, htop_lt, _, hc1, _,
      hfit_sp, rfl⟩, hj_lt, hi_lt, hy_lt⟩ := h
    simp only [hpW_mk, hpBChar_mk, hpMaskB_mk, hpPowB_mk, hpCPlusOne_mk, hpCTab_mk, hpD_mk] at *
    have htop := topRead_realizeObligs (i := i) hw hb.le htop_lt hfit_sp (by omega) hj_lt
      (Nat.and_lt_two_pow r (Nat.sub_lt (Nat.two_pow_pos _) one_pos))
  )
  · exact htop.1
  · exact htop.2.1
  · exact htop.2.2.1
  · exact htop.2.2.2
  · exact (by omega : i + 1 < c_tab + 1).trans hc1
  · exact (Nat.xor_lt_two_pow hy_lt (readPacked_lt _ _ _ _ _)).trans
      (Nat.pow_lt_pow_right (by decide) hb)

/-- Parameter-free wrapper for `iterate innerStepGenProg`. -/
@[expose] def innerLoopGenProg :
    ((HashParams × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ)) × ℕ → Memory.Prog ((ℕ × ℕ) × ℕ)
  | ((ctx, st), n) => iterate innerStepGenProg ctx n st

private theorem realizes_innerLoopGen :
    Realizes .exact innerLoopGenProg
      (WordEncoding.encode (α := ((HashParams × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ)) × ℕ))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (fun w ((ctx, st), n) s => iterationSafe innerStepGenProg InnerStepGenPre w ctx n st s)
      (fun _ _ => 0) :=
  Realizes.iterate₀
    (WordEncoding.encode (α := HashParams × (ℕ × ℕ)))
    (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
    realizes_innerStepGen
    memoryCost_innerStepGenProg_pos

/-- Outer-loop body (`p = ((hp, (base, (s_val, rKey))), (j, out_acc))`): computes `y_j` across all
`c_tab + 1` characters, reads `T₂[j, y_j]`, and XORs into `out_acc`. -/
@[expose] def outerStepGenProg :
    (HashParams × (ℕ × (ℕ × ℕ))) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | ((hp, (base, (s_val, rKey))), (j, out_acc)) => do
    let zero_v ← pure 0
    let inner_res ← innerLoopGenProg
      (((hp, (base, j)), ((zero_v, zero_v), rKey)), hpCTab hp)
    let ((_i_fin, y_acc), _r_rem) := inner_res
    let row_s ← pure (j * hpCPlusOne hp + hpCTab hp)
    let idx_s ← pure (row_s * hpPowB hp + s_val)
    let one_off ← pure 1
    let t_salt ← readPackedGenProg
      (((base, one_off), (hpBChar hp, hpW hp)), idx_s)
    let y_j ← pure (y_acc ^^^ t_salt)
    let idx₂ ← pure (j * hpPowB hp + y_j)
    let z_j ← readPackedGenProg
      (((base, hpOffBot hp), (hpMOut hp, hpW hp)), idx₂)
    let j_next ← pure (j + 1)
    let out_next ← pure (out_acc ^^^ z_j)
    pure (j_next, out_next)

/-- Extract the XOR accumulator `y` from the inner-loop state `((i, y), r)`. -/
abbrev innerAcc (st : (ℕ × ℕ) × ℕ) : ℕ := st.1.2

private theorem clientState_outerStepGenProg
    (p : (HashParams × (ℕ × (ℕ × ℕ))) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (outerStepGenProg p) = s := by
  rcases p with ⟨⟨hp, base, s_val, rKey⟩, j, out_acc⟩
  unfold outerStepGenProg innerLoopGenProg readPackedGenProg
  simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, clientState_iterate_innerStep,
    StateTransitionSpec.clientState_bind, clientState_readPackedProg,
    StateTransitionSpec.clientState_bind, clientState_readPackedProg]
  rfl

private theorem clientResult_outerStepGenProg
    (hp : HashParams) (base s_val rKey j out_acc : ℕ) (s : Memory.State) :
    let y_acc := innerAcc ((Memory.spec 0).clientResult s
      (iterate innerStepGenProg (hp, (base, j)) (hpCTab hp) ((0, 0), rKey)))
    let t_salt := readPacked (base + 1) (hpBChar hp) (hpW hp) s.mem
      ((j * hpCPlusOne hp + hpCTab hp) * hpPowB hp + s_val)
    let z_j := readPacked (base + hpOffBot hp) (hpMOut hp) (hpW hp) s.mem
      (j * hpPowB hp + (y_acc ^^^ t_salt))
    (Memory.spec 0).clientResult s
      (outerStepGenProg ((hp, (base, (s_val, rKey))), (j, out_acc))) =
      (j + 1, out_acc ^^^ z_j) := by
  unfold outerStepGenProg innerLoopGenProg readPackedGenProg
  simp only [pure_bind]
  rw [StateTransitionSpec.clientResult_bind, clientState_iterate_innerStep,
    StateTransitionSpec.clientResult_bind, clientState_readPackedProg, clientResult_readPackedProg,
    StateTransitionSpec.clientResult_bind, clientState_readPackedProg, clientResult_readPackedProg,
    StateTransitionSpec.clientResult_pure]

private theorem memoryCost_outerStepGenProg
    (hp : HashParams) (base s_val rKey j out_acc : ℕ) (s : Memory.State) :
    memoryCost (outerStepGenProg ((hp, (base, (s_val, rKey))), (j, out_acc))) s =
      2 * (hpCTab hp + 2) := by
  unfold outerStepGenProg innerLoopGenProg readPackedGenProg
  simp only [pure_bind, memoryCost_bind', memoryCost_pure, memoryCost_iterate_innerStep,
    memoryCost_readPackedProg]
  ring

private theorem memoryCost_outerStepGenProg_pos
    (p : (HashParams × (ℕ × (ℕ × ℕ))) × (ℕ × ℕ)) (s : Memory.State) :
    1 ≤ memoryCost (outerStepGenProg p) s := by
  rcases p with ⟨⟨hp, base, s_val, rKey⟩, j, out_acc⟩
  rw [memoryCost_outerStepGenProg]; omega

/-- Loop-safety, state-preservation, and accumulator-range invariant for `innerStepGenProg`. -/
theorem innerLoop_invariant {w : ℕ} {hp : HashParams} {base j : ℕ} {s : Memory.State}
    (henv : HashEnv w hp base) (hj : j < hpD hp) :
    ∀ m i y r, i + m ≤ hpCTab hp → y < hpPowB hp →
      iterationSafe innerStepGenProg InnerStepGenPre w (hp, (base, j)) m ((i, y), r) s ∧
      (Memory.spec 0).clientState s
        (iterate innerStepGenProg (hp, (base, j)) m ((i, y), r)) = s ∧
      innerAcc ((Memory.spec 0).clientResult s
        (iterate innerStepGenProg (hp, (base, j)) m ((i, y), r))) < hpPowB hp := by
  have henv₀ := henv
  obtain ⟨w₀, R, c_tab, d_par, b_char, M_out, hw, _, _, _, _, _, _, _, _, _, rfl⟩ := henv
  intro m
  induction m with
  | zero => exact fun i y r _ hy => ⟨trivial, rfl, hy⟩
  | succ m ih =>
    intro i y r him hy
    simp only [hpCTab_mk, hpPowB_mk] at him hy ⊢
    have hpre : InnerStepGenPre w ((_, (base, j)), ((i, y), r)) s :=
      ⟨henv₀, hj, by simp only [hpCTab_mk]; omega, hy⟩
    have hy' := Nat.xor_lt_two_pow hy (readPacked_lt (base + 1) b_char w s.mem
      ((j * (c_tab + 1) + i) * 2 ^ b_char + (r &&& (2 ^ b_char - 1))))
    obtain ⟨hsafe_m, _, hy_m⟩ := ih (i + 1) _ (r >>> b_char) (by simp only [hpCTab_mk]; omega) hy'
    refine ⟨⟨hpre, hsafe_m⟩, clientState_iterate_innerStep _ _ _ s, ?_⟩
    rw [iterate, StateTransitionSpec.clientResult_bind,
      show (Memory.spec 0).clientState s (innerStepGenProg _) = s from rfl,
      clientResult_innerStepGenProg]
    simpa only [hpW_mk, hpBChar_mk, hpMaskB_mk, hpPowB_mk, hpCPlusOne_mk] using hy_m

/-- Precondition for `outerStepGenProg`. -/
private def OuterStepGenPre (w : ℕ) :
    (HashParams × (ℕ × (ℕ × ℕ))) × (ℕ × ℕ) → Memory.State → Prop
  | ((hp, (base, (s_val, _rKey))), (j, out_acc)), _s =>
    HashEnv w hp base ∧
    s_val < hpPowB hp ∧
    j < hpD hp ∧
    out_acc < 2 ^ hpMOut hp

private theorem mul_add_xor_lt_botEntries {j d_par y t b_char : ℕ}
    (hj : j < d_par) (hy : y < 2 ^ b_char) (ht : t < 2 ^ b_char) :
    j * 2 ^ b_char + (y ^^^ t) < botEntries d_par b_char := by
  simpa only [Nat.mul_comm] using Nat.mul_add_lt_mul_of_lt_of_lt hj (Nat.xor_lt_two_pow hy ht)

private theorem realizes_outerStepGen :
    Realizes .exact outerStepGenProg
      (WordEncoding.encode (α := (HashParams × (ℕ × (ℕ × ℕ))) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      OuterStepGenPre
      (fun _ _ => 0) := by
  realize [realizes_innerLoopGen, realizes_readPackedGen]
  all_goals (
    rcases d with ⟨⟨hp, base, s_val, rKey⟩, j, out⟩
    obtain ⟨henv, hs_lt, hj_lt, hout_lt⟩ := h
    have henv' := henv
    obtain ⟨w₀, R, c_tab, d_par, b_char, M_out, hw, _, _, hb, hM, htop_lt, hbot_lt,
      _, hd_lt, hfit_sp, rfl⟩ := henv
    have hinv := innerLoop_invariant (s := s) henv' hj_lt c_tab 0 0 rKey
      (by simp only [hpCTab_mk]; omega) (Nat.two_pow_pos b_char)
    simp only [hpW_mk, hpBChar_mk, hpPowB_mk, hpMOut_mk, hpOffBot_mk, hpCPlusOne_mk, hpCTab_mk,
      hpD_mk, innerLoopGenProg, readPackedGenProg, clientResult_readPackedProg] at *
    have htop := topRead_realizeObligs (i := c_tab) hw hb.le htop_lt hfit_sp (by omega) hj_lt hs_lt
  )
  · exact hinv.1
  · exact htop.1
  · exact htop.2.1
  · exact htop.2.2.1
  · exact htop.2.2.2
  · exact (Nat.xor_lt_two_pow hinv.2.2 (readPacked_lt _ _ _ _ _)).trans
      (Nat.pow_lt_pow_right (by decide) hb)
  · exact (mul_add_xor_lt_botEntries hj_lt hinv.2.2 (readPacked_lt _ _ _ _ _)).trans hbot_lt
  · exact ⟨botEntries d_par b_char, trivial, hw, hM,
      mul_add_xor_lt_botEntries hj_lt hinv.2.2 (readPacked_lt _ _ _ _ _), by wram_omega⟩
  · exact (by omega : j + 1 ≤ d_par).trans_lt hd_lt
  · exact (Nat.xor_lt_two_pow hout_lt (readPacked_lt _ _ _ _ _)).trans_le
      (Nat.pow_le_pow_right two_pos hM)

/-- Parameter-free wrapper for `iterate outerStepGenProg`. -/
@[expose] def outerLoopGenProg :
    ((HashParams × (ℕ × (ℕ × ℕ))) × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((ctx, st), n) => iterate outerStepGenProg ctx n st

private theorem realizes_outerLoopGen :
    Realizes .exact outerLoopGenProg
      (WordEncoding.encode (α := ((HashParams × (ℕ × (ℕ × ℕ))) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((ctx, st), n) s => iterationSafe outerStepGenProg OuterStepGenPre w ctx n st s)
      (fun _ _ => 0) :=
  Realizes.iterate₀
    (WordEncoding.encode (α := HashParams × (ℕ × (ℕ × ℕ))))
    (WordEncoding.encode (α := ℕ × ℕ))
    realizes_outerStepGen
    memoryCost_outerStepGenProg_pos

private theorem outerLoop_invariant {w : ℕ} {hp : HashParams} {base s_val rKey : ℕ}
    {s : Memory.State}
    (henv : HashEnv w hp base) (hs_lt : s_val < hpPowB hp) :
    ∀ m j out, j + m ≤ hpD hp → out < 2 ^ hpMOut hp →
      iterationSafe outerStepGenProg OuterStepGenPre w (hp, (base, (s_val, rKey))) m (j, out) s ∧
      (Memory.spec 0).clientState s
        (iterate outerStepGenProg (hp, (base, (s_val, rKey))) m (j, out)) = s := by
  intro m
  induction m with
  | zero => exact fun j out _ _ => ⟨trivial, rfl⟩
  | succ m ih =>
    intro j out hjm hout
    have hpre : OuterStepGenPre w ((hp, (base, (s_val, rKey))), (j, out)) s :=
      ⟨henv, hs_lt, by omega, hout⟩
    refine ⟨⟨hpre, ?_⟩, clientState_iterate_eq_of outerStepGenProg _
      (fun _ t => clientState_outerStepGenProg _ t) _ _ s⟩
    rw [clientResult_width, clientState_width, clientState_outerStepGenProg,
      clientResult_outerStepGenProg]
    exact (ih (j + 1) _ (by omega) (Nat.xor_lt_two_pow hout (readPacked_lt _ _ _ _ _))).1

/-- Parameter-free `Memory.Prog` hash evaluation (`p = (hp, ((base, s_val), u_val))`):
computes `rKey = oddMulModWord w₀ (s.mem base) u_val >>> (w₀ - R)` and evaluates `(c_tab + 1, d)`
bit-packed double tabulation in `O(c_tab * d)` deterministic steps. -/
@[expose] def evalGenProg : HashParams × ((ℕ × ℕ) × ℕ) → Memory.Prog ℕ
  | (hp, ((base, s_val), u_val)) => do
    let α_val ← Memory.read base
    let x' ← pure (u_val &&& hpMaskM hp)
    let α₀ ← pure (α_val &&& hpMaskHalf hp)
    let α₁ ← pure (α_val >>> hpHalfM hp)
    let x₀ ← pure (x' &&& hpMaskHalf hp)
    let x₁ ← pure (x' >>> hpHalfM hp)
    let p₀ ← pure ((α₀ * x₀) &&& hpMaskM hp)
    let p₁ ← pure (((α₀ * x₁) &&& hpMaskRem hp) <<< hpHalfM hp)
    let p₂ ← pure (((α₁ * x₀) &&& hpMaskRem hp) <<< hpHalfM hp)
    let p₃ ← pure (((α₁ &&& hpMaskTop hp) * (x₁ &&& hpMaskTop hp)) <<< hpTwoHalfM hp)
    let s₁ ← pure ((p₀ + p₁) &&& hpMaskM hp)
    let s₂ ← pure ((s₁ + p₂) &&& hpMaskM hp)
    let hm ← pure ((s₂ + p₃) &&& hpMaskM hp)
    let one_v ← pure 1
    let rKey ← pure (((u_val &&& one_v) +
      ((((u_val >>> one_v) + hm) &&& hpMaskM hp) <<< one_v)) >>> hpShiftR hp)
    let zero_v ← pure 0
    let out ← outerLoopGenProg
      (((hp, (base, (s_val, rKey))), (zero_v, zero_v)), hpD hp)
    pure out.2

/-- Specialized `Memory.Prog` hash evaluation at concrete `(w, w₀, R, c_tab, d, b_char, M_out)`. -/
@[expose] def evalProg (w w₀ R c_tab d b_char M_out : ℕ) (d_in : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ :=
  evalGenProg (mkHashParams w w₀ R c_tab d b_char M_out, d_in)

/-- Precondition for `evalGenProg`. -/
@[expose] def EvalGenPre (w : ℕ) : HashParams × ((ℕ × ℕ) × ℕ) → Memory.State → Prop
  | (hp, ((base, s_val), u_val)), s =>
    HashEnv w hp base ∧
    s.mem base ≤ hpMaskM hp ∧
    s_val < hpPowB hp ∧
    u_val ≤ (hpMaskM hp <<< 1) + 1

/-- **Parameter-free `Realizes .exact` certificate for `evalGenProg` (`¬ReadsWidth`, single compiled
`Code .exact`)**. -/
theorem realizes_evalGen :
    Realizes .exact evalGenProg
      (WordEncoding.encode (α := HashParams × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := ℕ))
      EvalGenPre
      (fun _ _ => 0) := by
  realize [realizes_outerLoopGen]
  all_goals (
    rcases d with ⟨hp, ⟨base, s_val⟩, u_val⟩
    obtain ⟨henv, hα_le, hs_lt, hu_le⟩ := h
    have henv' := henv
    obtain ⟨w₀, R, c_tab, d_par, b_char, M_out, hw, hw₀, hw₀_le, _, _, _, _, _, _, _, rfl⟩ := henv
    simp only [hpHalfM_mk, hpTwoHalfM_mk, hpMaskM_mk, hpMaskHalf_mk, hpMaskRem_mk, hpMaskTop_mk,
      hpShiftR_mk, hpD_mk] at *
    have hα_lt : s.mem base < 2 ^ (w₀ - 1) := by wram_omega
    have hu_lt : u_val < 2 ^ w₀ := by
      rw [Nat.shiftLeft_eq, pow_one] at hu_le
      have : 2 * 2 ^ (w₀ - 1) = 2 ^ w₀ := by rw [← pow_succ', Nat.sub_add_cancel hw₀]
      wram_omega
    have hpow : 2 ^ w₀ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hw₀_le
    obtain ⟨h1, h2, h3, h4, h5, _, h7, h8, h9, h10, h11, _, h13⟩ :=
      oddMulModWord_parts_lt hw₀ hα_lt hu_lt
  )
  · exact h1.trans_le hpow
  · exact h3.trans_le hpow
  · exact h2.trans_le hpow
  · exact h5.trans_le hpow
  · exact h4.trans_le hpow
  · exact h7.trans_le hpow
  · exact h8.trans_le hpow
  · exact h9.trans_le hpow
  · exact h10.trans_le hpow
  · exact Nat.one_lt_two_pow hw.ne'
  · exact h13.trans_le hpow
  · exact h11.trans_le hpow
  · exact (outerLoop_invariant henv' (by simpa only [hpPowB_mk] using hs_lt) d_par 0 0
      (by simp only [hpD_mk]; omega) (by simp only [hpMOut_mk]; exact Nat.two_pow_pos M_out)).1

/-! ### Functional correctness, `ValidHistory`, and `memoryCost` of `evalProg` -/

/-- Prefix XOR of the first `m ≤ n` `k`-bit entries of `f : Fin n → Fin (2 ^ k)`. -/
private def finXorPrefix {k n : ℕ} (f : Fin n → Fin (2 ^ k)) (m : ℕ) (hm : m ≤ n) : Fin (2 ^ k) :=
  BitString.equivFin k (∑ i : Fin m, (BitString.equivFin k).symm (f (Fin.castLE hm i)))

private theorem val_finXorPrefix_zero {k n : ℕ} (f : Fin n → Fin (2 ^ k)) :
    (finXorPrefix f 0 (Nat.zero_le n)).val = 0 := by
  dsimp only [finXorPrefix]
  rw [Finset.univ_eq_empty, Finset.sum_empty]
  exact BitString.val_equivFin_false k

private theorem val_finXorPrefix_succ {k n : ℕ} (f : Fin n → Fin (2 ^ k)) {m : ℕ}
    (hm : m + 1 ≤ n) :
    (finXorPrefix f (m + 1) hm).val =
      (finXorPrefix f m (Nat.le_of_succ_le hm)).val ^^^ (f ⟨m, hm⟩).val := by
  dsimp only [finXorPrefix]
  rw [Fin.sum_univ_castSucc, BitString.val_equivFin_add, Equiv.apply_symm_apply]
  rfl

private theorem iterate_innerStep_eq {base w w₀ R c_tab d b_char M_out s_max : ℕ}
    {θ : Seed w₀ c_tab d b_char M_out} {s : Memory.State}
    (hrep : SeedRep base w w₀ c_tab d b_char M_out θ s.mem)
    (salt : Fin s_max) (rKey : Fin (2 ^ min w₀ R)) (j : Fin d) :
    let f : Fin (c_tab + 1) → Fin (2 ^ b_char) :=
      fun i => θ.top i j (saltedChars c_tab b_char salt rKey i)
    ∀ m i (him : i + m ≤ c_tab),
      (Memory.spec 0).clientResult s
        (iterate innerStepGenProg
          (mkHashParams w w₀ R c_tab d b_char M_out, (base, j.val)) m
          ((i, (finXorPrefix f i (by omega)).val), rKey.val >>> (i * b_char))) =
        ((i + m, (finXorPrefix f (i + m) (by omega)).val), rKey.val >>> ((i + m) * b_char)) := by
  intro f m
  induction m with
  | zero => intro i _; rfl
  | succ m ih =>
    intro i him
    have hch : (rKey.val >>> (i * b_char)) &&& (2 ^ b_char - 1) =
        (saltedChars c_tab b_char salt rKey ⟨i, by omega⟩).val := by
      change _ = (saltedChars c_tab b_char salt rKey (⟨i, by omega⟩ : Fin c_tab).castSucc).val
      rw [saltedChars, Fin.snoc_castSucc]; rfl
    have hstep : (Memory.spec 0).clientResult s
        (innerStepGenProg ((mkHashParams w w₀ R c_tab d b_char M_out, (base, j.val)),
          ((i, (finXorPrefix f i (by omega)).val), rKey.val >>> (i * b_char)))) =
        ((i + 1, (finXorPrefix f (i + 1) (by omega)).val),
          rKey.val >>> ((i + 1) * b_char)) := by
      rw [clientResult_innerStepGenProg]
      simp only [hpMaskB_mk, hpCPlusOne_mk, hpPowB_mk, hpBChar_mk, hpW_mk]
      rw [hch, hrep.2.1 ⟨i, by omega⟩ j _, ← val_finXorPrefix_succ f (by omega),
        ← Nat.shiftRight_add, Nat.add_mul, Nat.one_mul]
    rw [iterate, StateTransitionSpec.clientResult_bind,
      show (Memory.spec 0).clientState s (innerStepGenProg _) = s from rfl, hstep]
    simpa only [Nat.add_assoc, Nat.add_comm 1 m] using ih (i + 1) (by omega)

private theorem iterate_outerStep_eq {base w w₀ R c_tab d b_char M_out s_max : ℕ}
    {θ : Seed w₀ c_tab d b_char M_out} {s : Memory.State}
    (hs_max : s_max ≤ 2 ^ b_char)
    (hrep : SeedRep base w w₀ c_tab d b_char M_out θ s.mem)
    (salt : Fin s_max) (rKey : Fin (2 ^ min w₀ R)) :
    let chars := saltedChars c_tab b_char salt rKey
    let g : Fin d → Fin (2 ^ M_out) := fun j => θ.bot j (simpleTabTuple θ.top chars j)
    ∀ m j (hjm : j + m ≤ d),
      (Memory.spec 0).clientResult s
        (iterate outerStepGenProg
          (mkHashParams w w₀ R c_tab d b_char M_out, (base, (salt.val, rKey.val))) m
          (j, (finXorPrefix g j (by omega)).val)) =
        (j + m, (finXorPrefix g (j + m) (by omega)).val) := by
  intro chars g m
  induction m with
  | zero => intro j _; rfl
  | succ m ih =>
    intro j hjm
    have hj_lt : j < d := by omega
    let jF : Fin d := ⟨j, hj_lt⟩
    let f : Fin (c_tab + 1) → Fin (2 ^ b_char) := fun i => θ.top i jF (chars i)
    have hin := iterate_innerStep_eq hrep salt rKey jF c_tab 0 (by omega)
    simp only [zero_add, zero_mul, Nat.shiftRight_zero, val_finXorPrefix_zero] at hin
    have hsalt : salt.val = (chars (Fin.last c_tab)).val := by
      dsimp only [chars, saltedChars]; rw [Fin.snoc_last]
      exact (Nat.mod_eq_of_lt (salt.isLt.trans_le hs_max)).symm
    have hstep : (Memory.spec 0).clientResult s
        (outerStepGenProg ((mkHashParams w w₀ R c_tab d b_char M_out,
          (base, (salt.val, rKey.val))), (j, (finXorPrefix g j (by omega)).val))) =
        (j + 1, (finXorPrefix g (j + 1) (by omega)).val) := by
      rw [clientResult_outerStepGenProg]
      dsimp only [hpCTab_mk, hpCPlusOne_mk, hpPowB_mk, hpBChar_mk, hpW_mk, hpOffBot_mk, hpMOut_mk]
      rw [hin, hsalt]
      change (j + 1, (finXorPrefix g j _).val ^^^
        readPacked (base + offBot w c_tab d b_char) M_out w s.mem
          (jF.val * 2 ^ b_char + ((finXorPrefix f c_tab (by omega)).val ^^^
            readPacked (base + 1) b_char w s.mem
              ((jF.val * (c_tab + 1) + (Fin.last c_tab).val) * 2 ^ b_char +
                (chars (Fin.last c_tab)).val)))) = _
      rw [hrep.2.1 (Fin.last c_tab) jF _,
        show (finXorPrefix f c_tab (by omega)).val ^^^
          (θ.top (Fin.last c_tab) jF (chars (Fin.last c_tab))).val =
          (simpleTabTuple θ.top chars jF).val from (val_finXorPrefix_succ f le_rfl).symm,
        hrep.2.2 jF _, ← val_finXorPrefix_succ g (by omega)]
    rw [iterate, StateTransitionSpec.clientResult_bind, clientState_outerStepGenProg, hstep]
    simpa only [Nat.add_assoc, Nat.add_comm 1 m] using ih (j + 1) (by omega)

/-- **Exact functional correctness and state preservation of `evalProg`**:
under `SeedRep`, `evalProg` leaves `s` unchanged and returns `(evalSalted ... θ (salt, u)).val`. -/
theorem evalProg_spec {U w w₀ R c_tab d b_char M_out s_max base : ℕ}
    {θ : Seed w₀ c_tab d b_char M_out} {s : Memory.State}
    (hw₀ : 0 < w₀) (hs_max : s_max ≤ 2 ^ b_char)
    (hrep : SeedRep base w w₀ c_tab d b_char M_out θ s.mem)
    (salt : Fin s_max) (u : Fin U) :
    (Memory.spec 0).clientResult s
      (evalProg w w₀ R c_tab d b_char M_out ((base, salt.val), u.val)) =
      (evalSalted U w₀ R c_tab d b_char M_out s_max θ (salt, u)).val ∧
    (Memory.spec 0).clientState s
      (evalProg w w₀ R c_tab d b_char M_out ((base, salt.val), u.val)) = s := by
  have hrkey : oddMulModWord w₀ (s.mem base) u.val >>> (w₀ - R) =
      (multiplyShiftReduced U w₀ R θ.1 u).val := by
    rw [hrep.1]; exact oddMulModWord_shiftRight_eq_multiplyShiftReduced hw₀ θ.1 u
  have hout := iterate_outerStep_eq hs_max hrep salt (multiplyShiftReduced U w₀ R θ.1 u) d 0
    (by omega)
  simp only [zero_add, val_finXorPrefix_zero] at hout
  unfold evalProg evalGenProg outerLoopGenProg
  simp only [pure_bind, hpMaskM_mk, hpMaskHalf_mk, hpHalfM_mk, hpMaskRem_mk, hpMaskTop_mk,
    hpTwoHalfM_mk, hpShiftR_mk, hpD_mk]
  have hst : (Memory.spec 0).clientState s (Memory.read base) = s := rfl
  have hres : (Memory.spec 0).clientResult s (Memory.read base) = s.mem base := rfl
  refine ⟨?_, ?_⟩
  · rw [StateTransitionSpec.clientResult_bind, hst, hres,
      StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure]
    change ((Memory.spec 0).clientResult s (iterate outerStepGenProg
      (mkHashParams w w₀ R c_tab d b_char M_out,
        (base, (salt.val, oddMulModWord w₀ (s.mem base) u.val >>> (w₀ - R)))) d (0, 0))).2 = _
    rw [hrkey, hout]; rfl
  · rw [StateTransitionSpec.clientState_bind, hst,
      StateTransitionSpec.clientState_bind,
      clientState_iterate_eq_of outerStepGenProg _
        (fun _ t => clientState_outerStepGenProg _ t) _ _ s]
    rfl

/-- Exact `memoryCost` of `evalProg`: `1 + 2 * d * (c_tab + 2)` (`O(c_tab * d)`). -/
theorem memoryCost_evalProg (w w₀ R c_tab d b_char M_out : ℕ) (d_in : (ℕ × ℕ) × ℕ)
    (s : Memory.State) :
    memoryCost (evalProg w w₀ R c_tab d b_char M_out d_in) s = 1 + 2 * d * (c_tab + 2) := by
  unfold evalProg evalGenProg outerLoopGenProg
  simp only [pure_bind, memoryCost_bind', memoryCost_pure, hpD_mk]
  rw [show memoryCost (Memory.read d_in.1.1) s = 1 from rfl,
    show (Memory.spec 0).clientState s (Memory.read d_in.1.1) = s from rfl,
    memoryCost_iterate_const s (2 * (c_tab + 2))
      (fun _ => clientState_outerStepGenProg _ s)
      (fun a => memoryCost_outerStepGenProg _ _ _ _ a.1 a.2 s)]
  ring

private theorem validHistory_iterate_const {δ σ : Type} {w : ℕ}
    {body : δ × σ → Memory.Prog σ} {safe : ℕ → δ × σ → Memory.State → Prop} {d : δ}
    (n : ℕ) (a : σ) (s : Memory.State)
    (hst : ∀ a', (Memory.spec 0).clientState s (body (d, a')) = s)
    (hbody : ∀ a', safe w (d, a') s →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (body (d, a'))))
    (hsafe : iterationSafe body safe w d n a s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (iterate body d n a)) := by
  induction n generalizing a with
  | zero => trivial
  | succ n ih =>
    rw [iterate, validHistory_bind']
    rw [iterationSafe, clientResult_width, clientState_width, hst] at hsafe
    refine ⟨hbody a hsafe.1, ?_⟩
    rw [hst]
    exact ih _ hsafe.2

private theorem validHistory_innerLoop {w w₀ R c_tab d_par b_char M_out base j rKey : ℕ}
    {s : Memory.State}
    (henv : HashEnv w (mkHashParams w w₀ R c_tab d_par b_char M_out) base)
    (hw : 0 < w) (hj : j < d_par)
    (hfr : base + space w c_tab d_par b_char M_out ≤ s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (iterate innerStepGenProg (mkHashParams w w₀ R c_tab d_par b_char M_out, (base, j))
        c_tab ((0, 0), rKey))) := by
  have hinv := innerLoop_invariant (s := s) henv hj c_tab 0 0 rKey
    (by simp only [hpCTab_mk]; omega) (by simp only [hpPowB_mk]; exact Nat.two_pow_pos b_char)
  refine validHistory_iterate_const c_tab ((0, 0), rKey) s (fun _ => rfl)
    (fun ⟨⟨i, y⟩, r⟩ h => ?_) hinv.1
  have hi_lt : i < c_tab := h.2.2.1
  unfold innerStepGenProg readPackedGenProg
  simp only [pure_bind, hpMaskB_mk, hpCPlusOne_mk, hpPowB_mk, hpBChar_mk, hpW_mk]
  rw [validHistory_bind']
  exact ⟨validHistory_readPackedProg hw
    (topIdx_lt_topEntries (by omega) hj
      (Nat.and_lt_two_pow r (Nat.sub_lt (Nat.two_pow_pos _) one_pos))) (by wram_omega), trivial⟩

/-- Memory history admissibility (`ValidHistory`) for `evalGenProg` under `EvalGenPre` and
`base + space ≤ s.frontier`. -/
theorem validHistory_evalGenProg {w : ℕ} {hp : HashParams} {base s_val u_val : ℕ}
    {s : Memory.State}
    (hpre : EvalGenPre w (hp, ((base, s_val), u_val)) s)
    (hfr : base + space w (hpCTab hp) (hpD hp) (hpBChar hp) (hpMOut hp) ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (evalGenProg (hp, ((base, s_val), u_val)))) := by
  obtain ⟨henv, _, hs_lt, _⟩ := hpre
  have henv' := henv
  obtain ⟨w₀, R, c_tab, d_par, b_char, M_out, hw, _, _, _, _, _, _, _, _, _, rfl⟩ := henv
  simp only [hpCTab_mk, hpD_mk, hpBChar_mk, hpMOut_mk, hpPowB_mk] at hfr hs_lt
  unfold evalGenProg outerLoopGenProg
  rw [validHistory_bind']
  refine ⟨⟨show base < s.frontier by wram_omega, trivial⟩, ?_⟩
  change (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s _)
  simp only [pure_bind, hpD_mk]
  rw [validHistory_bind']
  refine ⟨?_, trivial⟩
  suffices ∀ rKey, (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (iterate outerStepGenProg (mkHashParams w w₀ R c_tab d_par b_char M_out,
        (base, (s_val, rKey))) d_par (0, 0))) from this _
  intro rKey
  have hinv := outerLoop_invariant (rKey := rKey) (s := s) henv'
    (by simpa only [hpPowB_mk] using hs_lt) d_par 0 0 (by simp only [hpD_mk]; omega)
    (by simp only [hpMOut_mk]; exact Nat.two_pow_pos _)
  refine validHistory_iterate_const d_par (0, 0) s (fun _ => clientState_outerStepGenProg _ s)
    (fun ⟨j, out⟩ h => ?_) hinv.1
  have hj : j < d_par := h.2.2.1
  have hin := innerLoop_invariant (s := s) henv' hj c_tab 0 0 rKey
    (by simp only [hpCTab_mk]; omega) (by simp only [hpPowB_mk]; exact Nat.two_pow_pos b_char)
  unfold outerStepGenProg innerLoopGenProg readPackedGenProg
  simp only [pure_bind, hpCTab_mk, hpCPlusOne_mk, hpPowB_mk, hpBChar_mk, hpW_mk,
    hpOffBot_mk, hpMOut_mk]
  rw [validHistory_bind', clientState_iterate_innerStep]
  refine ⟨validHistory_innerLoop henv' hw hj hfr, ?_⟩
  rw [validHistory_bind', clientState_readPackedProg, clientResult_readPackedProg]
  refine ⟨validHistory_readPackedProg hw (topIdx_lt_topEntries (by omega) hj hs_lt)
    (by wram_omega), ?_⟩
  rw [validHistory_bind']
  exact ⟨validHistory_readPackedProg hw (mul_add_xor_lt_botEntries hj
    (by simpa only [hpPowB_mk] using hin.2.2) (readPacked_lt _ _ _ _ _)) (by wram_omega), trivial⟩

/-- Specialized `ValidHistory` lemma for `evalProg`. -/
theorem validHistory_evalProg {w w₀ R c_tab d b_char M_out : ℕ} {base s_val u_val : ℕ}
    {s : Memory.State}
    (hpre : EvalGenPre w (mkHashParams w w₀ R c_tab d b_char M_out, ((base, s_val), u_val)) s)
    (hfr : base + space w c_tab d b_char M_out ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (evalProg w w₀ R c_tab d b_char M_out ((base, s_val), u_val))) :=
  validHistory_evalGenProg hpre hfr

end Cslib.DataStructure.HashFamily.WordRAM.BitPackedDoubleTabulation

end
