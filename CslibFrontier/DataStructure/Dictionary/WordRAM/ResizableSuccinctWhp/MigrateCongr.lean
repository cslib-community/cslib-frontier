/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochSchedEq
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.MigrateSlotCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Phase-`5` Seed Uniformity and Prefix Equivariance (`MigrateCongr`)

This module bridges the single-state deterministic invariant stack (`DualEpochInv`), global
schedule determinism (`DualEpochSchedEq`), and direct-I/O confinement (`MigrateSlotRw`) to the
Phase-`5` random-seed sampling fiber required by `MigrateDrain` and `DualEpochExec`:

1. **Uniform epoch seed decoding (`SeedWords`, `seedsOfWords`, `uniform_map_seedsOfWords`):**
   Maps uniform `w`-bit word slices `SeedWords c w N` (with the two Stage-1 odd-multiplier words
   masked modulo `2 ^ (redWidthWhp U - 1)`) onto `PMF.uniformOfFintype (EpochHashSeeds c U N)` and
   derives the `(1 / 2) * N⁻¹ ^ c` per-epoch bad-seed probability bound, together with batched word
   concatenation (`finAppendWords`, `uniform_bind_finAppendWords`).
2. **Phase-`5` prefix-word equivariance (`Ph5StateAt`, `ph5_mutate_step`):**
   Tracks uniform random word batches across Phase `5` (`5 → 5`) and transitions at `5 → 6` into
   `Coupled67` with `seedsDst = seedsOfWords c U w nDst ws_seed`.

## Main definitions

* `SeedWords`, `emptySeedWords`, `seedsOfWords`, `finAppendWords`: seed word tuple, masked decoder,
  and batch word concatenation.
* `Ph5StateAt`, `Coupled67Region`, `Coupled67`: Phase-`5` prefix relation and Phases-`6..7`
  non-seed memory coupling.

## Main results

* `toOuterMeasure_seedWords_not_good_le`, `uniform_bind_finAppendWords`
* `ph5_mutate_step`

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.DataStructure.HashFamily Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.WordRAM.Resizable.Randomized
open Cslib.Probability
open EpochUpdate
open scoped ENNReal

/-! ## Section 1: Uniform Epoch Seed Words (`SeedWords`, `seedsOfWords`, `finAppendWords`) -/

/-- Raw uniform `w`-bit seed word tuple for an epoch of capacity `N` (`0` words when `N = 0`, and
`offBktMeta c w N - 32` words when `0 < N`). -/
abbrev SeedWords (c w N : ℕ) : Type :=
  Fin (if N = 0 then 0 else offBktMeta c w N - 32) → Fin (2 ^ w)

/-- Explicit `NeZero (2 ^ w)` instance for arbitrary word width `w : ℕ`. -/
instance instNeZeroTwoPow (w : ℕ) : NeZero (2 ^ w) :=
  ⟨(Nat.two_pow_pos w).ne'⟩

/-- `SeedWords c w 0` has a single canonical empty word tuple. -/
theorem subsingleton_seedWords_zero (c w : ℕ) : Subsingleton (SeedWords c w 0) := by
  unfold SeedWords
  rw [ite_eq_left rfl]
  infer_instance

/-- Canonical empty word tuple in `SeedWords c w 0`. -/
def emptySeedWords (c w : ℕ) : SeedWords c w 0 :=
  fun i => Fin.elim0 (Fin.cast (ite_eq_left rfl) i)

/-- At capacity `0`, the uniform distribution on `SeedWords c w 0` is `PMF.pure`. -/
theorem uniformOfFintype_seedWords_zero (c w : ℕ) :
    PMF.uniformOfFintype (SeedWords c w 0) = PMF.pure (emptySeedWords c w) := by
  have : Subsingleton (SeedWords c w 0) := subsingleton_seedWords_zero c w
  ext x
  rw [Subsingleton.elim x (emptySeedWords c w), PMF.pure_apply_self, PMF.uniformOfFintype_apply,
    Fintype.card_eq_one_iff.mpr ⟨emptySeedWords c w, fun y => Subsingleton.elim y _⟩]
  simp

/-- Decodes `EpochHashSeeds c U N` from a raw `w`-bit word tuple `ws : SeedWords c w N` by writing
`ws` at offset `32`, masking the two Stage-1 odd-multiplier words modulo `2 ^ (redWidthWhp U - 1)`,
and running `extractEpochSeeds`. -/
@[expose] noncomputable def seedsOfWords (c U w N : ℕ) (ws : SeedWords c w N) :
    EpochHashSeeds c U N :=
  if h0 : N = 0 then Classical.choice inferInstance
  else
    let ws' : Fin (offBktMeta c w N - 32) → Fin (2 ^ w) :=
      fun i => ws (i.cast (ite_eq_right h0).symm)
    let m0 := writeWords (fun _ => 0) 32 ws'
    let mask := 2 ^ (redWidthWhp U - 1) - 1
    let m1 := Function.update (Function.update m0 32 (m0 32 &&& mask))
      (offFpHash c w N) (m0 (offFpHash c w N) &&& mask)
    extractEpochSeeds c U w N 0 m1

private theorem extractSeed_shift_congr {b₁ b₂ w w₀ c_tab d b_char M_out : ℕ}
    {m₁ m₂ : ℕ → ℕ} (hw : 0 < w)
    (heq : ∀ q < BitPackedDoubleTabulation.space w c_tab d b_char M_out,
      m₁ (b₁ + q) = m₂ (b₂ + q)) :
    BitPackedDoubleTabulation.extractSeed b₁ w w₀ c_tab d b_char M_out m₁ =
      BitPackedDoubleTabulation.extractSeed b₂ w w₀ c_tab d b_char M_out m₂ := by
  have hsp : BitPackedDoubleTabulation.space w c_tab d b_char M_out =
      1 + BitPackedDoubleTabulation.topWords w c_tab d b_char +
        BitPackedDoubleTabulation.botWords w d b_char M_out := rfl
  have hsp_pos : 0 < BitPackedDoubleTabulation.space w c_tab d b_char M_out := by omega
  have h0 : m₁ b₁ = m₂ b₂ := by simpa only [Nat.add_zero] using heq 0 hsp_pos
  have htop : BitPackedDoubleTabulation.extractPackedSlice (b₁ + 1)
      (BitPackedDoubleTabulation.topEntries c_tab d b_char) b_char w m₁ =
      BitPackedDoubleTabulation.extractPackedSlice (b₂ + 1)
        (BitPackedDoubleTabulation.topEntries c_tab d b_char) b_char w m₂ := by
    funext i
    apply Fin.ext
    dsimp only [BitPackedDoubleTabulation.extractPackedSlice]
    unfold readPacked readBitSlice
    dsimp only
    have hw1 := wordOffset_add_one_lt_packedWords (k := b_char) hw i.isLt
    have hq0 : 1 + wordOffset b_char w i.val <
        BitPackedDoubleTabulation.space w c_tab d b_char M_out := by
      dsimp only [BitPackedDoubleTabulation.topWords] at hsp; omega
    have hq1 : 1 + wordOffset b_char w i.val + 1 <
        BitPackedDoubleTabulation.space w c_tab d b_char M_out := by
      dsimp only [BitPackedDoubleTabulation.topWords] at hsp; omega
    have ha0 : b₁ + 1 + wordOffset b_char w i.val = b₁ + (1 + wordOffset b_char w i.val) := by
      omega
    have hb0 : b₂ + 1 + wordOffset b_char w i.val = b₂ + (1 + wordOffset b_char w i.val) := by
      omega
    have ha1 : b₁ + 1 + wordOffset b_char w i.val + 1 =
        b₁ + (1 + wordOffset b_char w i.val + 1) := by omega
    have hb1 : b₂ + 1 + wordOffset b_char w i.val + 1 =
        b₂ + (1 + wordOffset b_char w i.val + 1) := by omega
    rw [ha1, hb1, ha0, hb0, heq _ hq0, heq _ hq1]
  have hbot : BitPackedDoubleTabulation.extractPackedSlice
      (b₁ + BitPackedDoubleTabulation.offBot w c_tab d b_char)
      (BitPackedDoubleTabulation.botEntries d b_char) M_out w m₁ =
      BitPackedDoubleTabulation.extractPackedSlice
        (b₂ + BitPackedDoubleTabulation.offBot w c_tab d b_char)
        (BitPackedDoubleTabulation.botEntries d b_char) M_out w m₂ := by
    funext i
    apply Fin.ext
    dsimp only [BitPackedDoubleTabulation.extractPackedSlice]
    unfold readPacked readBitSlice
    dsimp only
    have hw1 := wordOffset_add_one_lt_packedWords (k := M_out) hw i.isLt
    have hq0 : BitPackedDoubleTabulation.offBot w c_tab d b_char + wordOffset M_out w i.val <
        BitPackedDoubleTabulation.space w c_tab d b_char M_out := by
      dsimp only [BitPackedDoubleTabulation.offBot, BitPackedDoubleTabulation.botWords] at hsp ⊢
      omega
    have hq1 : BitPackedDoubleTabulation.offBot w c_tab d b_char + wordOffset M_out w i.val + 1 <
        BitPackedDoubleTabulation.space w c_tab d b_char M_out := by
      dsimp only [BitPackedDoubleTabulation.offBot, BitPackedDoubleTabulation.botWords] at hsp ⊢
      omega
    have ha0 : b₁ + BitPackedDoubleTabulation.offBot w c_tab d b_char + wordOffset M_out w i.val =
        b₁ + (BitPackedDoubleTabulation.offBot w c_tab d b_char + wordOffset M_out w i.val) := by
      omega
    have hb0 : b₂ + BitPackedDoubleTabulation.offBot w c_tab d b_char + wordOffset M_out w i.val =
        b₂ + (BitPackedDoubleTabulation.offBot w c_tab d b_char + wordOffset M_out w i.val) := by
      omega
    have ha1 :
        b₁ + BitPackedDoubleTabulation.offBot w c_tab d b_char + wordOffset M_out w i.val + 1 =
        b₁ + (BitPackedDoubleTabulation.offBot w c_tab d b_char + wordOffset M_out w i.val + 1) :=
      by omega
    have hb1 :
        b₂ + BitPackedDoubleTabulation.offBot w c_tab d b_char + wordOffset M_out w i.val + 1 =
        b₂ + (BitPackedDoubleTabulation.offBot w c_tab d b_char + wordOffset M_out w i.val + 1) :=
      by omega
    rw [ha1, hb1, ha0, hb0, heq _ hq0, heq _ hq1]
  unfold BitPackedDoubleTabulation.extractSeed
  rw [h0, htop, hbot]

/-- Translation invariance of `extractEpochSeeds` after writing `ws` to `[metaDst + 32,
metaDst + offBktMeta c w N)` and masking the two Stage-1 multiplier words (`finishRandFillProg`). -/
private theorem extractEpochSeeds_masked_writeWords_eq {c U w N metaDst : ℕ}
    (hw : 0 < w) (hth : whpThreshold c ≤ N) (mem₀ : ℕ → ℕ)
    (ws : Fin (offBktMeta c w N - 32) → Fin (2 ^ w)) :
    let m_rand := writeWords mem₀ (metaDst + 32) ws
    let mask := 2 ^ (redWidthWhp U - 1) - 1
    let m_masked := Function.update
      (Function.update m_rand (metaDst + 32) (m_rand (metaDst + 32) &&& mask))
      (metaDst + offFpHash c w N) (m_rand (metaDst + offFpHash c w N) &&& mask)
    let ws_seed : SeedWords c w N :=
      fun i => ws (i.cast (ite_eq_right ((whpThreshold_pos c).trans_le hth).ne'))
    extractEpochSeeds c U w N metaDst m_masked = seedsOfWords c U w N ws_seed := by
  dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier]
  have hN_pos : 0 < N := (whpThreshold_pos c).trans_le hth
  have hsp_b := BitPackedDoubleTabulation.space_pos w (cTabWhp c) (dTabWhp c)
    (bCharWhp N) (bWhp N)
  have hsp_f := BitPackedDoubleTabulation.space_pos w (cTabWhp c) (dTabWhp c)
    (bCharWhp N) (fpBitsWhp N)
  have h32_fp : 32 < offFpHash c w N := by unfold offFpHash offBktHash; omega
  have hfp_bm : offFpHash c w N < offBktMeta c w N := by unfold offBktMeta; omega
  unfold seedsOfWords
  rw [dite_eq_right hN_pos.ne']
  dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier]
  set m_rand := writeWords mem₀ (metaDst + 32) ws
  set mask := 2 ^ (redWidthWhp U - 1) - 1
  set m_masked := Function.update
    (Function.update m_rand (metaDst + 32) (m_rand (metaDst + 32) &&& mask))
    (metaDst + offFpHash c w N) (m_rand (metaDst + offFpHash c w N) &&& mask)
  have hite : (if N = 0 then 0 else offBktMeta c w N - 32) = offBktMeta c w N - 32 :=
    ite_eq_right hN_pos.ne'
  have hws_eq : (fun i : Fin (offBktMeta c w N - 32) =>
      ws ((i.cast hite.symm).cast hite)) = ws := by
    funext i; rfl
  rw [hws_eq]
  set m0 := writeWords (fun _ => 0) 32 ws
  set m1 := Function.update (Function.update m0 32 (m0 32 &&& mask))
    (offFpHash c w N) (m0 (offFpHash c w N) &&& mask)
  have hm_eq : ∀ k, 32 ≤ k → k < offBktMeta c w N → m_masked (metaDst + k) = m1 k := by
    intro k hk1 hk2
    have hr_eq : ∀ j, 32 ≤ j → k < offBktMeta c w N → j < offBktMeta c w N →
        m_rand (metaDst + j) = m0 j := by
      intro j hj1 _ hj2
      have h1 : metaDst + j = (metaDst + 32) + (j - 32) := by omega
      have h2 : j = 32 + (j - 32) := by omega
      have hlt : j - 32 < offBktMeta c w N - 32 := by omega
      dsimp only [m_rand, m0]
      rw [h1, writeWords_apply_in mem₀ (metaDst + 32) ws hlt]
      conv_rhs => rw [h2, writeWords_apply_in (fun _ => 0) 32 ws hlt]
    dsimp only [m_masked, m1]
    by_cases hk_fp : k = offFpHash c w N
    · subst hk_fp
      rw [Function.update_self, Function.update_self, hr_eq _ (by omega) hfp_bm hfp_bm]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne hk_fp]
      by_cases hk32 : k = 32
      · subst hk32
        rw [Function.update_self, Function.update_self,
          hr_eq 32 le_rfl (h32_fp.trans hfp_bm) (h32_fp.trans hfp_bm)]
      · rw [Function.update_of_ne (by omega), Function.update_of_ne hk32]
        exact hr_eq k hk1 hk2 hk2
  unfold extractEpochSeeds
  congr 1
  · refine extractSeed_shift_congr hw fun q hq => ?_
    have ha : metaDst + offBktHash + q = metaDst + (32 + q) := by unfold offBktHash; omega
    have hb : 0 + offBktHash + q = 32 + q := by unfold offBktHash; omega
    rw [ha, hb]
    exact hm_eq (32 + q) (by omega) (by unfold offBktMeta offFpHash offBktHash; omega)
  · refine extractSeed_shift_congr hw fun q hq => ?_
    have ha : metaDst + offFpHash c w N + q = metaDst + (offFpHash c w N + q) := by omega
    have hb : 0 + offFpHash c w N + q = offFpHash c w N + q := by omega
    rw [ha, hb]
    exact hm_eq (offFpHash c w N + q) (by omega) (by unfold offBktMeta; omega)

private def maskTruncWord (r w : ℕ) (x : Fin (2 ^ w)) : Fin (2 ^ r) :=
  wordOfNat r (x.val &&& (2 ^ r - 1))

private def bitTruncHom {r w : ℕ} (hr : r ≤ w) : BitString w →+ BitString r where
  toFun f j := f (Fin.castLE hr j)
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem surjective_bitTruncHom {r w : ℕ} (hr : r ≤ w) :
    Function.Surjective (bitTruncHom hr) := by
  intro g
  refine ⟨fun i => if hi : i.val < r then g ⟨i.val, hi⟩ else false, ?_⟩
  funext j
  dsimp only [bitTruncHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Fin.val_castLE]
  rw [dite_eq_left j.isLt]

private theorem uniformOfFintype_map_maskTruncWord {r w : ℕ} (hr : r ≤ w) :
    (PMF.uniformOfFintype (Fin (2 ^ w))).map (maskTruncWord r w) =
      PMF.uniformOfFintype (Fin (2 ^ r)) := by
  have hfn : maskTruncWord r w =
      (BitString.equivFin r) ∘ bitTruncHom hr ∘ (BitString.equivFin w).symm := by
    funext x
    apply (BitString.equivFin r).symm.injective
    rw [Function.comp_apply, Function.comp_apply, Equiv.symm_apply_apply]
    funext j
    rw [BitString.equivFin_symm_apply]
    dsimp only [maskTruncWord, bitTruncHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [BitString.equivFin_symm_apply]
    have hlt : x.val &&& (2 ^ r - 1) < 2 ^ r := by
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos r)
    rw [wordOfNat_val_of_lt hlt, Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_mod_two_pow,
      decide_eq_true j.isLt, Bool.true_and]
    rfl
  rw [hfn, ← PMF.map_comp, ← PMF.map_comp, PMF.uniformOfFintype_map_equiv,
    PMF.uniformOfFintype_map_addHom (bitTruncHom hr) (surjective_bitTruncHom hr),
    PMF.uniformOfFintype_map_equiv]

private theorem extractSeed_eq_tablesOfWords {base w w₀ c_tab d b_char M_out : ℕ}
    (hw : 0 < w) (hbc : b_char ≤ w) (hm : M_out ≤ w) (mem : ℕ → ℕ)
    (ws : Fin (BitPackedDoubleTabulation.topWords w c_tab d b_char +
      BitPackedDoubleTabulation.botWords w d b_char M_out) → Fin (2 ^ w))
    (hmem : ∀ q : Fin (BitPackedDoubleTabulation.topWords w c_tab d b_char +
      BitPackedDoubleTabulation.botWords w d b_char M_out),
      mem (base + 1 + q.val) = (ws q).val) :
    BitPackedDoubleTabulation.extractSeed base w w₀ c_tab d b_char M_out mem =
      (wordOfNat (w₀ - 1) (mem base),
        (BitPackedDoubleTabulation.tablesOfWords w c_tab d b_char M_out hw ws).1,
        (BitPackedDoubleTabulation.tablesOfWords w c_tab d b_char M_out hw ws).2) := by
  let tW := BitPackedDoubleTabulation.topWords w c_tab d b_char
  let bW := BitPackedDoubleTabulation.botWords w d b_char M_out
  have htop_lt : ∀ q < tW, mem (base + 1 + q) < 2 ^ w := fun q hq => by
    rw [hmem ⟨q, by omega⟩]; exact (ws _).isLt
  have hbot_lt : ∀ q < bW,
      mem (base + BitPackedDoubleTabulation.offBot w c_tab d b_char + q) < 2 ^ w := fun q hq => by
    have ha : base + BitPackedDoubleTabulation.offBot w c_tab d b_char + q =
        base + 1 + (tW + q) := by
      dsimp only [BitPackedDoubleTabulation.offBot, tW]; omega
    rw [ha, hmem ⟨tW + q, by omega⟩]; exact (ws _).isLt
  have hts : Tabulation.extractSlice (base + 1) w tW mem = fun q => ws (Fin.castAdd bW q) := by
    funext q
    apply Fin.ext
    change (wordOfNat w (mem (base + 1 + q.val))).val = (ws (Fin.castAdd bW q)).val
    rw [wordOfNat_val_of_lt (htop_lt q.val q.isLt)]
    simpa only [Fin.val_castAdd] using hmem (Fin.castAdd bW q)
  have hbs : Tabulation.extractSlice (base + BitPackedDoubleTabulation.offBot w c_tab d b_char)
      w bW mem = fun q => ws (Fin.natAdd tW q) := by
    funext q
    apply Fin.ext
    change (wordOfNat w (mem (base + BitPackedDoubleTabulation.offBot w c_tab d b_char +
      q.val))).val = (ws (Fin.natAdd tW q)).val
    rw [wordOfNat_val_of_lt (hbot_lt q.val q.isLt)]
    have ha : base + BitPackedDoubleTabulation.offBot w c_tab d b_char + q.val =
        base + 1 + (tW + q.val) := by
      dsimp only [BitPackedDoubleTabulation.offBot, tW]; omega
    rw [ha]
    simpa only [Fin.val_natAdd] using hmem (Fin.natAdd tW q)
  unfold BitPackedDoubleTabulation.extractSeed
  dsimp only [tW, bW, BitPackedDoubleTabulation.topWords, BitPackedDoubleTabulation.botWords]
    at hts hbs
  rw [BitPackedDoubleTabulation.extractPackedSlice_eq_packedSliceOfWords hw hbc htop_lt,
    BitPackedDoubleTabulation.extractPackedSlice_eq_packedSliceOfWords hw hm hbot_lt, hts, hbs]
  rfl

/-- Pushing `PMF.uniformOfFintype (SeedWords c w N)` forward along `seedsOfWords c U w N` yields
the exact uniform distribution `PMF.uniformOfFintype (EpochHashSeeds c U N)` for every large epoch
(`whpThreshold c ≤ N ≤ U < 2 ^ w`). -/
private theorem uniform_map_seedsOfWords {c U w N : ℕ}
    (hth : whpThreshold c ≤ N) (hnU : N ≤ U) (hUw : Fits w U) :
    (PMF.uniformOfFintype (SeedWords c w N)).map (seedsOfWords c U w N) =
      PMF.uniformOfFintype (EpochHashSeeds c U N) := by
  have hN_pos : 0 < N := (whpThreshold_pos c).trans_le hth
  obtain ⟨_, _, hlog_w, hbc_w, hb_w, hfp_w, _⟩ := largeEpoch_param_bounds hth hnU hUw
  have hw : 0 < w := lt_of_le_of_lt (Nat.zero_le _) hlog_w
  have hr_le : redWidthWhp U - 1 ≤ w := by
    have hrw : redWidthWhp U ≤ w :=
      max_le (by omega) (Nat.clog_le_of_le_pow hUw.le)
    omega
  set wB := BitPackedDoubleTabulation.topWords w (cTabWhp c) (dTabWhp c) (bCharWhp N) +
    BitPackedDoubleTabulation.botWords w (dTabWhp c) (bCharWhp N) (bWhp N)
  set wF := BitPackedDoubleTabulation.topWords w (cTabWhp c) (dTabWhp c) (bCharWhp N) +
    BitPackedDoubleTabulation.botWords w (dTabWhp c) (bCharWhp N) (fpBitsWhp N)
  have hlen : (if N = 0 then 0 else offBktMeta c w N - 32) = (1 + wB) + (1 + wF) := by
    rw [ite_eq_right hN_pos.ne']
    unfold offBktMeta offFpHash offBktHash BitPackedDoubleTabulation.space
    dsimp only [wB, wF]
    omega
  let e_len : SeedWords c w N ≃ (Fin ((1 + wB) + (1 + wF)) → Fin (2 ^ w)) :=
    Equiv.arrowCongr (finCongr hlen) (Equiv.refl _)
  let e_sum : (Fin ((1 + wB) + (1 + wF)) → Fin (2 ^ w)) ≃
      (Fin (1 + wB) → Fin (2 ^ w)) × (Fin (1 + wF) → Fin (2 ^ w)) :=
    (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl _)).trans
      (Equiv.sumArrowEquivProdArrow (Fin (1 + wB)) (Fin (1 + wF)) (Fin (2 ^ w)))
  let e_b : (Fin (1 + wB) → Fin (2 ^ w)) ≃ Fin (2 ^ w) × (Fin wB → Fin (2 ^ w)) :=
    (Equiv.arrowCongr (finCongr (Nat.add_comm 1 wB)) (Equiv.refl _)).trans
      (Fin.consEquiv (fun _ : Fin (wB + 1) => Fin (2 ^ w))).symm
  let e_f : (Fin (1 + wF) → Fin (2 ^ w)) ≃ Fin (2 ^ w) × (Fin wF → Fin (2 ^ w)) :=
    (Equiv.arrowCongr (finCongr (Nat.add_comm 1 wF)) (Equiv.refl _)).trans
      (Fin.consEquiv (fun _ : Fin (wF + 1) => Fin (2 ^ w))).symm
  let e_all : SeedWords c w N ≃
      (Fin (2 ^ w) × (Fin wB → Fin (2 ^ w))) × (Fin (2 ^ w) × (Fin wF → Fin (2 ^ w))) :=
    e_len.trans (e_sum.trans (Equiv.prodCongr e_b e_f))
  let combine :
      Fin (2 ^ (redWidthWhp U - 1)) → (Fin wB → Fin (2 ^ w)) →
      Fin (2 ^ (redWidthWhp U - 1)) → (Fin wF → Fin (2 ^ w)) → EpochHashSeeds c U N :=
    fun aB wsB aF wsF =>
      let pB := BitPackedDoubleTabulation.tablesOfWords w (cTabWhp c) (dTabWhp c) (bCharWhp N)
        (bWhp N) hw wsB
      let pF := BitPackedDoubleTabulation.tablesOfWords w (cTabWhp c) (dTabWhp c) (bCharWhp N)
        (fpBitsWhp N) hw wsF
      ⟨⟨aB, pB.1, pB.2⟩, ⟨aF, pF.1, pF.2⟩⟩
  have hval : ∀ p : (Fin (2 ^ w) × (Fin wB → Fin (2 ^ w))) ×
      (Fin (2 ^ w) × (Fin wF → Fin (2 ^ w))),
      seedsOfWords c U w N (e_all.symm p) =
        combine (maskTruncWord (redWidthWhp U - 1) w p.1.1) p.1.2
          (maskTruncWord (redWidthWhp U - 1) w p.2.1) p.2.2 := by
    rintro ⟨⟨xB, wsB⟩, ⟨xF, wsF⟩⟩
    unfold seedsOfWords
    rw [dite_eq_right hN_pos.ne']
    dsimp only
    set ws' : Fin (offBktMeta c w N - 32) → Fin (2 ^ w) :=
      fun i => e_all.symm ((xB, wsB), (xF, wsF)) (i.cast (ite_eq_right hN_pos.ne').symm)
    set m0 := writeWords (fun _ => 0) 32 ws'
    set mask := 2 ^ (redWidthWhp U - 1) - 1
    set m1 := Function.update (Function.update m0 32 (m0 32 &&& mask))
      (offFpHash c w N) (m0 (offFpHash c w N) &&& mask)
    have hspB : BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c) (bCharWhp N) (bWhp N) =
        1 + wB := by unfold BitPackedDoubleTabulation.space; dsimp only [wB]; omega
    have hspF :
        BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c) (bCharWhp N) (fpBitsWhp N) =
        1 + wF := by unfold BitPackedDoubleTabulation.space; dsimp only [wF]; omega
    have hfp_eq : offFpHash c w N = 32 + (1 + wB) := by
      unfold offFpHash offBktHash; rw [hspB]
    have hbm_eq : offBktMeta c w N = 32 + ((1 + wB) + (1 + wF)) := by
      unfold offBktMeta; rw [hfp_eq, hspF]; omega
    have hws_idx : ∀ k (hk : k < (1 + wB) + (1 + wF)),
        ws' ⟨k, by omega⟩ =
          if h1 : k < 1 + wB then
            (if hk0 : k = 0 then xB else wsB ⟨k - 1, by omega⟩)
          else
            (if hk0 : k - (1 + wB) = 0 then xF else wsF ⟨k - (1 + wB) - 1, by omega⟩) := by
      intro k hk
      change (Equiv.sumArrowEquivProdArrow (Fin (1 + wB)) (Fin (1 + wF)) (Fin (2 ^ w))).symm
        (e_b.symm (xB, wsB), e_f.symm (xF, wsF)) (finSumFinEquiv.symm ⟨k, hk⟩) = _
      by_cases h1 : k < 1 + wB
      · rw [dite_eq_left h1]
        have hsum_l : finSumFinEquiv.symm ⟨k, hk⟩ = Sum.inl ⟨k, h1⟩ := by
          apply finSumFinEquiv.injective
          rw [Equiv.apply_symm_apply, finSumFinEquiv_apply_left]
          ext; rfl
        rw [hsum_l]
        dsimp only [Equiv.sumArrowEquivProdArrow_symm_apply_inl]
        by_cases hk0 : k = 0
        · subst hk0
          rw [dite_eq_left rfl]
          exact @Fin.cons_zero wB (fun _ => Fin (2 ^ w)) xB wsB
        · rw [dite_eq_right hk0]
          have hk_b : k < wB + 1 := Nat.add_comm 1 wB ▸ h1
          have hkm1 : k - 1 < wB := by omega
          have hsucc : (⟨k, hk_b⟩ : Fin (wB + 1)) = (⟨k - 1, hkm1⟩ : Fin wB).succ := by
            apply Fin.ext; change k = (k - 1) + 1; omega
          change @Fin.cons wB (fun _ => Fin (2 ^ w)) xB wsB ⟨k, hk_b⟩ = _
          rw [hsucc, Fin.cons_succ]
      · rw [dite_eq_right h1]
        have hsum_r : finSumFinEquiv.symm ⟨k, hk⟩ = Sum.inr ⟨k - (1 + wB), by omega⟩ := by
          apply finSumFinEquiv.injective
          rw [Equiv.apply_symm_apply, finSumFinEquiv_apply_right]
          apply Fin.ext
          change k = (1 + wB) + (k - (1 + wB))
          omega
        rw [hsum_r]
        dsimp only [Equiv.sumArrowEquivProdArrow_symm_apply_inr]
        have hk_f : k - (1 + wB) < wF + 1 := by
          have hlt_f : k - (1 + wB) < 1 + wF :=
            Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp h1) hk
          exact Nat.add_comm 1 wF ▸ hlt_f
        by_cases hk0 : k - (1 + wB) = 0
        · rw [dite_eq_left hk0]
          change @Fin.cons wF (fun _ => Fin (2 ^ w)) xF wsF ⟨k - (1 + wB), hk_f⟩ = xF
          have hz : (⟨k - (1 + wB), hk_f⟩ : Fin (wF + 1)) = 0 := by
            apply Fin.ext; exact hk0
          rw [hz]
          exact @Fin.cons_zero wF (fun _ => Fin (2 ^ w)) xF wsF
        · rw [dite_eq_right hk0]
          have hkm1 : k - (1 + wB) - 1 < wF := by omega
          have hsucc : (⟨k - (1 + wB), hk_f⟩ : Fin (wF + 1)) =
              (⟨k - (1 + wB) - 1, hkm1⟩ : Fin wF).succ := by
            apply Fin.ext; change k - (1 + wB) = (k - (1 + wB) - 1) + 1; omega
          change @Fin.cons wF (fun _ => Fin (2 ^ w)) xF wsF ⟨k - (1 + wB), hk_f⟩ = _
          rw [hsucc, Fin.cons_succ]
    have hm1_32 : m1 32 = xB.val &&& mask := by
      dsimp only [m1]
      rw [Function.update_of_ne (by omega), Function.update_self]
      dsimp only [m0]
      have hw32 : writeWords (fun _ => 0) 32 ws' (32 + 0) = (ws' ⟨0, by omega⟩).val :=
        writeWords_apply_in (fun _ => 0) 32 ws' (by omega)
      rw [Nat.add_zero] at hw32
      rw [hw32, hws_idx 0 (by omega)]
      simp
    have hm1_fp : m1 (offFpHash c w N) = xF.val &&& mask := by
      dsimp only [m1]
      rw [Function.update_self]
      dsimp only [m0]
      rw [hfp_eq, writeWords_apply_in (fun _ => 0) 32 ws' (by omega),
        hws_idx (1 + wB) (by omega)]
      simp
    have hm1_b : ∀ q : Fin wB, m1 (32 + 1 + q.val) = (wsB q).val := fun q => by
      dsimp only [m1]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      dsimp only [m0]
      have ha : 32 + 1 + q.val = 32 + (1 + q.val) := by omega
      rw [ha, writeWords_apply_in (fun _ => 0) 32 ws' (by omega),
        hws_idx (1 + q.val) (by omega)]
      have hlt : 1 + q.val < 1 + wB := by omega
      rw [dite_eq_left hlt, dite_eq_right (by omega)]
      have hsub : (⟨1 + q.val - 1, by omega⟩ : Fin wB) = q := by ext; dsimp only; omega
      rw [hsub]
    have hm1_f : ∀ q : Fin wF, m1 (offFpHash c w N + 1 + q.val) = (wsF q).val := fun q => by
      dsimp only [m1]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      dsimp only [m0]
      have ha : offFpHash c w N + 1 + q.val = 32 + ((1 + wB) + 1 + q.val) := by omega
      rw [ha, writeWords_apply_in (fun _ => 0) 32 ws' (by omega),
        hws_idx ((1 + wB) + 1 + q.val) (by omega)]
      have hnlt : ¬((1 + wB) + 1 + q.val < 1 + wB) := by omega
      rw [dite_eq_right hnlt, dite_eq_right (by omega)]
      have hsub : (⟨(1 + wB) + 1 + q.val - (1 + wB) - 1, by omega⟩ : Fin wF) = q := by
        ext; dsimp only; omega
      rw [hsub]
    unfold extractEpochSeeds
    have hb_ext := extractSeed_eq_tablesOfWords (base := 0 + offBktHash)
      (w₀ := redWidthWhp U) hw hbc_w.le hb_w.le m1 wsB (fun q => hm1_b q)
    have hf_ext := extractSeed_eq_tablesOfWords (base := 0 + offFpHash c w N)
      (w₀ := redWidthWhp U) hw hbc_w.le hfp_w.le m1 wsF (fun q => by
        simpa only [Nat.zero_add] using hm1_f q)
    rw [hb_ext, hf_ext]
    simp only [Nat.zero_add, offBktHash, hm1_32, hm1_fp]
    rfl
  have heq_fn : seedsOfWords c U w N =
      (fun p : (Fin (2 ^ w) × (Fin wB → Fin (2 ^ w))) × (Fin (2 ^ w) × (Fin wF → Fin (2 ^ w))) =>
        combine (maskTruncWord (redWidthWhp U - 1) w p.1.1) p.1.2
          (maskTruncWord (redWidthWhp U - 1) w p.2.1) p.2.2) ∘ e_all := by
    funext ws
    rw [← e_all.symm_apply_apply ws, hval (e_all ws), Function.comp_apply, e_all.apply_symm_apply]
  rw [heq_fn, ← PMF.map_comp, PMF.uniformOfFintype_map_equiv e_all]
  rw [← PMF.uniformOfFintype_prod, ← PMF.uniformOfFintype_prod, ← PMF.uniformOfFintype_prod]
  simp only [PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have hm_trunc := uniformOfFintype_map_maskTruncWord hr_le
  have hstep1 :
      (PMF.uniformOfFintype (Fin (2 ^ w))).bind (fun xB =>
        (PMF.uniformOfFintype (Fin wB → Fin (2 ^ w))).bind fun wsB =>
          (PMF.uniformOfFintype (Fin (2 ^ w))).bind fun xF =>
            (PMF.uniformOfFintype (Fin wF → Fin (2 ^ w))).map fun wsF =>
              combine (maskTruncWord (redWidthWhp U - 1) w xB) wsB
                (maskTruncWord (redWidthWhp U - 1) w xF) wsF) =
      (PMF.uniformOfFintype (Fin (2 ^ (redWidthWhp U - 1)))).bind (fun aB =>
        (PMF.uniformOfFintype (Fin wB → Fin (2 ^ w))).bind fun wsB =>
          (PMF.uniformOfFintype (Fin (2 ^ (redWidthWhp U - 1)))).bind fun aF =>
            (PMF.uniformOfFintype (Fin wF → Fin (2 ^ w))).map fun wsF =>
              combine aB wsB aF wsF) := by
    rw [← hm_trunc, PMF.bind_map]
    congr 1; funext xB
    congr 1; funext wsB
    rw [PMF.bind_map]; rfl
  exact hstep1.trans (uniform_epochHashSeeds_of_words hw)

/-- Per-epoch bad-seed probability bound directly on `SeedWords c w N`. -/
theorem toOuterMeasure_seedWords_not_good_le {c U w N : ℕ}
    (hth : whpThreshold c ≤ N) (hnU : N ≤ U) (hUw : Fits w U)
    (win : EpochWindowSpec c U N) :
    (PMF.uniformOfFintype (SeedWords c w N)).toOuterMeasure
      {ws | ¬GoodEpochSeeds win (seedsOfWords c U w N ws)} ≤
      ((1 : ℝ≥0∞) / 2) * ((N : ℝ≥0∞)⁻¹ ^ c) := by
  have hunif := uniform_map_seedsOfWords hth hnU hUw
  have hmap : ((PMF.uniformOfFintype (SeedWords c w N)).map (seedsOfWords c U w N)).toOuterMeasure
      {s | ¬GoodEpochSeeds win s} =
      (PMF.uniformOfFintype (SeedWords c w N)).toOuterMeasure
        {ws | ¬GoodEpochSeeds win (seedsOfWords c U w N ws)} :=
    PMF.toOuterMeasure_map_apply _ _ _
  rw [← hmap, hunif]
  exact uniform_not_goodEpochSeeds_le hth hnU win

/-- Concatenates `ws₁ : Fin k₁ → α` and `ws₂ : Fin k₂ → α` into `Fin (k₁ + k₂) → α`. -/
@[expose] def finAppendWords {α : Type} {k₁ k₂ : ℕ} (ws₁ : Fin k₁ → α) (ws₂ : Fin k₂ → α) :
    Fin (k₁ + k₂) → α :=
  fun i => if h : i.val < k₁ then ws₁ ⟨i.val, h⟩ else ws₂ ⟨i.val - k₁, by omega⟩

private def finAppendEquiv (α : Type) (k₁ k₂ : ℕ) :
    (Fin k₁ → α) × (Fin k₂ → α) ≃ (Fin (k₁ + k₂) → α) :=
  (Equiv.sumArrowEquivProdArrow (Fin k₁) (Fin k₂) α).symm.trans
    (Equiv.arrowCongr finSumFinEquiv (Equiv.refl α))

private theorem finAppendEquiv_apply {α : Type} {k₁ k₂ : ℕ}
    (ws₁ : Fin k₁ → α) (ws₂ : Fin k₂ → α) :
    finAppendEquiv α k₁ k₂ (ws₁, ws₂) = finAppendWords ws₁ ws₂ := by
  funext i
  dsimp only [finAppendEquiv, finAppendWords, Equiv.trans_apply, Equiv.arrowCongr_apply,
    Equiv.refl_apply]
  by_cases h : i.val < k₁
  · rw [dite_eq_left h]
    have hl : finSumFinEquiv.symm i = Sum.inl ⟨i.val, h⟩ := by
      apply finSumFinEquiv.injective
      rw [Equiv.apply_symm_apply, finSumFinEquiv_apply_left]
      ext; rfl
    change ((Equiv.sumArrowEquivProdArrow (Fin k₁) (Fin k₂) α).symm (ws₁, ws₂))
      (finSumFinEquiv.symm i) = _
    rw [hl]; rfl
  · rw [dite_eq_right h]
    have hr : finSumFinEquiv.symm i = Sum.inr ⟨i.val - k₁, by omega⟩ := by
      apply finSumFinEquiv.injective
      rw [Equiv.apply_symm_apply, finSumFinEquiv_apply_right]
      apply Fin.ext
      change i.val = k₁ + (i.val - k₁)
      omega
    change ((Equiv.sumArrowEquivProdArrow (Fin k₁) (Fin k₂) α).symm (ws₁, ws₂))
      (finSumFinEquiv.symm i) = _
    rw [hr]; rfl

/-- Concatenating independent uniform word tuples `Fin k₁ → Fin (2 ^ w)` and `Fin k₂ → Fin (2 ^ w)`
via `finAppendWords` yields `PMF.uniformOfFintype (Fin (k₁ + k₂) → Fin (2 ^ w))`. -/
theorem uniform_bind_finAppendWords (w k₁ k₂ : ℕ) :
    (PMF.uniformOfFintype (Fin k₁ → Fin (2 ^ w))).bind (fun ws₁ =>
      (PMF.uniformOfFintype (Fin k₂ → Fin (2 ^ w))).map (fun ws₂ =>
        finAppendWords ws₁ ws₂)) =
      PMF.uniformOfFintype (Fin (k₁ + k₂) → Fin (2 ^ w)) := by
  symm
  rw [← PMF.uniformOfFintype_map_equiv (finAppendEquiv (Fin (2 ^ w)) k₁ k₂),
    ← PMF.uniformOfFintype_prod, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def, finAppendEquiv_apply]

/-- Sequential `writeWords` at `a` (`k₁` words) and `a + k₁` (`k₂` words) equals a single
`writeWords` of `finAppendWords ws₁ ws₂` at `a`. -/
private theorem writeWords_writeWords_eq_finAppendWords {w : ℕ} (m : ℕ → ℕ) (a k₁ k₂ : ℕ)
    (ws₁ : Fin k₁ → Fin (2 ^ w)) (ws₂ : Fin k₂ → Fin (2 ^ w)) :
    writeWords (writeWords m a ws₁) (a + k₁) ws₂ =
      writeWords m a (finAppendWords ws₁ ws₂) := by
  funext addr
  by_cases hin : a ≤ addr ∧ addr < a + (k₁ + k₂)
  · have h_rhs : addr = a + (addr - a) := by omega
    have hlt_tot : addr - a < k₁ + k₂ := by omega
    conv_rhs => rw [h_rhs, writeWords_apply_in m a (finAppendWords ws₁ ws₂) hlt_tot]
    dsimp only [finAppendWords]
    by_cases h1 : addr - a < k₁
    · rw [dite_eq_left h1, writeWords_apply_out _ (a + k₁) ws₂ (by omega)]
      conv_lhs => rw [h_rhs, writeWords_apply_in m a ws₁ h1]
    · rw [dite_eq_right h1]
      have h_lhs : addr = (a + k₁) + (addr - a - k₁) := by omega
      have hlt2 : addr - a - k₁ < k₂ := by omega
      conv_lhs => rw [h_lhs, writeWords_apply_in (writeWords m a ws₁) (a + k₁) ws₂ hlt2]
  · rw [writeWords_apply_out _ (a + k₁) ws₂ (by omega),
      writeWords_apply_out m a ws₁ (by omega),
      writeWords_apply_out m a (finAppendWords ws₁ ws₂) hin]

/-! ## Section 2: Phase-`5` Prefix Equivariance (`Ph5StateAt`) and `5 → 5` / `5 → 6` Steps -/

/-- Commutes `writeWords · a ws` across any `RWConfined R R s₁ p` program when `[a, a + k)` is
disjoint from `R`. -/
private theorem rwConfined_writeWords_comm {α : Type} {R : ℕ → Prop} {w a k : ℕ}
    {s₁ : Memory.State} {p : Memory.Prog α}
    (hp : RWConfined R R s₁ p)
    (hdisj : ∀ i < k, ¬R (a + i))
    (ws : Fin k → Fin (2 ^ w)) :
    let s₂ : Memory.State := { mem := writeWords s₁.mem a ws, frontier := s₁.frontier }
    (Memory.spec 0).clientResult s₁ p = (Memory.spec 0).clientResult s₂ p ∧
    (Memory.spec 0).clientState s₂ p =
      { mem := writeWords ((Memory.spec 0).clientState s₁ p).mem a ws
        frontier := ((Memory.spec 0).clientState s₁ p).frontier } := by
  dsimp only
  set s₂ : Memory.State := { mem := writeWords s₁.mem a ws, frontier := s₁.frontier }
  have hagree : ∀ addr, R addr → s₁.mem addr = s₂.mem addr := fun addr hr => by
    have hnot : ¬(a ≤ addr ∧ addr < a + k) := fun ⟨hlo, hhi⟩ => by
      have heq : a + (addr - a) = addr := by omega
      exact hdisj (addr - a) (by omega) (heq.symm ▸ hr)
    exact (writeWords_apply_out s₁.mem a ws hnot).symm
  obtain ⟨hfr₂, hout₂⟩ := hp.out₂ s₂ hagree
  refine ⟨hp.res_eq s₂ hagree, ?_⟩
  have hst_ext : ∀ {a b : Memory.State}, a.mem = b.mem → a.frontier = b.frontier → a = b := by
    rintro ⟨_, _⟩ ⟨_, _⟩ rfl rfl; rfl
  refine hst_ext (funext fun addr => ?_) (hfr₂.trans hp.fr₁.symm)
  change ((Memory.spec 0).clientState s₂ p).mem addr =
    writeWords ((Memory.spec 0).clientState s₁ p).mem a ws addr
  by_cases hin : a ≤ addr ∧ addr < a + k
  · have h_add : addr = a + (addr - a) := by omega
    have hlt : addr - a < k := by omega
    have hnr : ¬R addr := h_add ▸ hdisj (addr - a) hlt
    rw [hout₂ addr hnr]
    dsimp only [s₂]
    rw [h_add, writeWords_apply_in s₁.mem a ws hlt,
      writeWords_apply_in ((Memory.spec 0).clientState s₁ p).mem a ws hlt]
  · rw [writeWords_apply_out ((Memory.spec 0).clientState s₁ p).mem a ws hin]
    by_cases hr : R addr
    · exact (hp.mem_in s₂ hagree addr hr).symm
    · exact (hout₂ addr hr).trans
        ((writeWords_apply_out s₁.mem a ws hin).trans (hp.out₁ addr hr).symm)

private theorem update_writeWords_out {w : ℕ} (m : ℕ → ℕ) (a k b val : ℕ)
    (ws : Fin k → Fin (2 ^ w)) (hout : ¬(a ≤ b ∧ b < a + k)) :
    Function.update (writeWords m a ws) b val = writeWords (Function.update m b val) a ws := by
  funext addr
  by_cases heq : addr = b
  · subst heq
    rw [Function.update_self, writeWords_apply_out _ a ws hout, Function.update_self]
  · rw [Function.update_of_ne heq]
    by_cases hin : a ≤ addr ∧ addr < a + k
    · have ha : addr = a + (addr - a) := by omega
      have hlt : addr - a < k := by omega
      rw [ha, writeWords_apply_in m a ws hlt,
        writeWords_apply_in (Function.update m b val) a ws hlt]
    · rw [writeWords_apply_out m a ws hin, writeWords_apply_out (Function.update m b val) a ws hin,
        Function.update_of_ne heq]

private theorem clear_writeWords_above {w : ℕ} (m : ℕ → ℕ) (a k c_lo c_len : ℕ)
    (ws : Fin k → Fin (2 ^ w)) (habove : a + k ≤ c_lo) :
    clear (writeWords m a ws) c_lo c_len = writeWords (clear m c_lo c_len) a ws := by
  funext addr
  by_cases hin : a ≤ addr ∧ addr < a + k
  · have hno : ¬(Block.mk c_lo c_len).Owns addr := by simp only [Block.Owns]; omega
    have ha : addr = a + (addr - a) := by omega
    have hlt : addr - a < k := by omega
    rw [clear_of_not_owns hno, ha, writeWords_apply_in m a ws hlt,
      writeWords_apply_in (clear m c_lo c_len) a ws hlt]
  · rw [writeWords_apply_out (clear m c_lo c_len) a ws hin]
    by_cases hown : (Block.mk c_lo c_len).Owns addr
    · rw [clear_of_owns hown, clear_of_owns hown]
    · rw [clear_of_not_owns hown, clear_of_not_owns hown, writeWords_apply_out m a ws hin]

/-- `s` differs from the Phase-`5` anchor state `s_anc` exclusively by writing the accumulated
random seed prefix `ws_pre : Fin k_pre → Fin (2 ^ w)` at `[dualMbDst + 32, dualMbDst + 32 + k_pre)`.
-/
@[expose] def Ph5StateAt (c w base : ℕ) (s_anc : Memory.State) (k_pre : ℕ)
    (ws_pre : Fin k_pre → Fin (2 ^ w)) (s : Memory.State) : Prop :=
  s_anc.mem (base + hdrPhase) = 5 ∧
  32 + k_pre = s_anc.mem (base + hdrCur) ∧
  32 + k_pre ≤ offBktMeta c w (s_anc.mem (base + hdrNDst)) ∧
  s = { mem := writeWords s_anc.mem (dualMbDst base s_anc.mem + 32) ws_pre
        frontier := s_anc.frontier }

/-- Upon entering Phase `5` (`hdrCur = 32`), any resting `DualStateInv` state `s_anc` trivially
satisfies `Ph5StateAt` at `k_pre = 0`. -/
theorem Ph5StateAt.of_entry {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s_anc : Memory.State}
    (h_anc : DualStateInv c U V w base s_dict L s_anc)
    (hp5 : s_anc.mem (base + hdrPhase) = 5)
    (hcur32 : s_anc.mem (base + hdrCur) = 32)
    (ws₀ : Fin 0 → Fin (2 ^ w)) :
    Ph5StateAt c w base s_anc 0 ws₀ s_anc := by
  refine ⟨hp5, by omega, ?_, ?_⟩
  · rw [Nat.add_zero, ← hcur32]; exact (h_anc.ph5_inv hp5).2.2.1
  · rcases s_anc with ⟨m, fr⟩
    congr 1; funext addr
    exact (writeWords_apply_out m _ ws₀ (by omega)).symm

/-- Every `Ph5StateAt` state shares `SchedEq` with its anchor `s_anc`. -/
theorem Ph5StateAt.schedEq {c U V w base k_pre : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s_anc s : Memory.State}
    {ws_pre : Fin k_pre → Fin (2 ^ w)}
    (h_anc : DualStateInv c U V w base s_dict L s_anc)
    (hph5 : Ph5StateAt c w base s_anc k_pre ws_pre s) :
    SchedEq base s_anc s := by
  obtain ⟨hp5, _, _, hs_eq⟩ := hph5
  have hd_pos := (h_anc.ph5_inv hp5).1
  have hmd_192 : base + 192 ≤ dualMbDst base s_anc.mem := by
    unfold dualMbDst; rw [hp5, ite_eq_left (by decide : 5 < 10), ite_eq_right hd_pos.ne']
    split_ifs <;> omega
  subst hs_eq
  exact ⟨rfl, fun off hoff _ => (writeWords_apply_out _ _ ws_pre (by omega)).symm⟩

/-- Address predicate outside destination non-page metadata, shared host page metadata, and active
destination `[dualMbDst, dualMbDst + offPageDir)` words. -/
@[expose] def Coupled67Region (c w base : ℕ) (m : ℕ → ℕ) (addr : ℕ) : Prop :=
  ¬slotOwnsNonPageMeta c w (dualMbDst base m) (m (base + hdrNDst)) addr ∧
  ¬(dualPgHost c 1 w base 0 m).OwnsMetaAddr addr ∧
  ¬(m (base + hdrNDst) ≠ 0 ∧ dualMbDst base m ≤ addr ∧
    addr < dualMbDst base m + offPageDir c w (m (base + hdrNDst)))

/-- Phases `6..7` coupling: `SchedEq` plus bitwise memory equality everywhere outside
`slotOwnsNonPageMeta` of `slotDst` and `OwnsMetaAddr` of `dualPgHost`. -/
@[expose] def Coupled67 (c w base : ℕ) (s₁ s₂ : Memory.State) : Prop :=
  SchedEq base s₁ s₂ ∧
  ∀ addr, Coupled67Region c w base s₁.mem addr → s₁.mem addr = s₂.mem addr

/-- Reflexivity of `Coupled67` (used at `3 → 6` when `nDst = 0` and `SeedWords c w 0` is
`Subsingleton`). -/
theorem Coupled67.refl (c w base : ℕ) (s : Memory.State) : Coupled67 c w base s s :=
  ⟨SchedEq.refl base s, fun _ _ => rfl⟩

/-- Disjointness of the Phases-`4..7` direct-I/O source region `SlotDirectRegion` from destination
non-page metadata, shared host page metadata, and `[dualMbDst, dualMbDst + offPageDir)`. -/
theorem srcDirect_disj_dstMeta {c U V w base opTag : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s : Memory.State}
    (h : DualStateInv c U V w base s_dict L s)
    (hp47 : 4 ≤ s.mem (base + hdrPhase) ∧ s.mem (base + hdrPhase) ≤ 7) :
    let nDst := s.mem (base + hdrNDst)
    let ibHi := s.mem (base + hdrItemHi)
    let qHi := s.mem (base + hdrQHi)
    let nLive := (Dictionary.dom s_dict).card
    let nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
    let pSrc := dualPSrc base s.mem
    let mbSrc := dualMbSrc base s.mem
    let capSrc := dualCapSrc base s.mem
    let io_al := directSlotIo w (valBits V) base ibHi qHi nAlloc
    ∀ addr, SlotDirectRegion c w pSrc mbSrc capSrc io_al addr →
      ¬slotOwnsNonPageMeta c w (dualMbDst base s.mem) nDst addr ∧
      ¬(dualPgHost c 1 w base 0 s.mem).OwnsMetaAddr addr ∧
      ¬(nDst ≠ 0 ∧ dualMbDst base s.mem ≤ addr ∧
        addr < dualMbDst base s.mem + offPageDir c w nDst) :=
  by
  dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier]
  have hsched := h.sched; rw [ite_eq_right (by omega)] at hsched
  obtain ⟨hmD_e, hpad_e, _, _, hibHi_e, _⟩ := hsched.ge2 (by omega)
  have hdisj_pg := disjoint_pgHost_nonPageMeta (nc := 0) h (by omega) (by omega)
  have hpg_meta_eq : ∀ a,
      (dualPgHost c 1 w base 0 s.mem).OwnsMetaAddr a ↔
      (dualPgHost c V w base 0 s.mem).OwnsMetaAddr a := fun _ => Iff.rfl
  intro addr hsr
  have hlt10 : s.mem (base + hdrPhase) < 10 := by omega
  have hpS_rng : base + 64 ≤ dualPSrc base s.mem ∧ dualPSrc base s.mem + 64 ≤ base + 192 := by
    unfold dualPSrc; dsimp only [hdrPBase0, hdrPBase1]; split_ifs <;> exact ⟨by omega, by omega⟩
  rcases hsr with ⟨hp1, hp2⟩ | hmeta_s | hio
  · refine ⟨?_, fun hpg => by have := (hdisj_pg addr ((hpg_meta_eq addr).mp hpg)).1; omega, ?_⟩
    · unfold slotOwnsNonPageMeta dualMbDst; rw [ite_eq_left hlt10]
      by_cases hd0 : s.mem (base + hdrNDst) = 0
      · simp only [hd0, ↓reduceIte, ne_eq, not_true_eq_false, false_and, or_false, hdrSmallMeta1]
        omega
      · simp only [hd0, ↓reduceIte]
        rcases Decidable.em (s.mem (base + hdrStage) = 0) with hs | hs <;>
          simp only [hs, ↓reduceIte] <;> omega
    · rintro ⟨hd0, hlo, _⟩
      unfold dualMbDst at hlo; rw [ite_eq_left hlt10, ite_eq_right hd0] at hlo
      split_ifs at hlo <;> omega
  · have hn_pg : ¬(dualPgHost c 1 w base 0 s.mem).OwnsMetaAddr addr :=
      fun hpg => (hdisj_pg addr ((hpg_meta_eq addr).mp hpg)).2.2.1 hmeta_s
    have hnot_d : ¬(s.mem (base + hdrNDst) ≠ 0 ∧ dualMbDst base s.mem ≤ addr ∧
        addr < dualMbDst base s.mem + offPageDir c w (s.mem (base + hdrNDst))) := by
      rintro ⟨hd0, hlo, hhi⟩
      unfold dualMbDst at hlo hhi; rw [ite_eq_left hlt10, ite_eq_right hd0] at hlo hhi
      unfold slotOwnsNonPageMeta dualMbSrc dualCapSrc at hmeta_s
      by_cases hst0 : s.mem (base + hdrStage) = 0
      · simp only [hst0, ↓reduceIte] at hlo hhi hmeta_s
        by_cases hs0 : s.mem (base + hdrNSrc) = 0
        · simp only [hs0, ↓reduceIte, ne_eq, not_true_eq_false, false_and, or_false,
            hdrSmallMeta0] at hmeta_s; omega
        · have hth_s := (h.nSrc_bounds.resolve_left hs0).1
          have h32_s : 32 ≤ offBktMeta c w (s.mem (base + hdrNSrc)) :=
            (epochMeta_offsets_le (w := w) hth_s).1.trans
              (epochMeta_offsets_le (w := w) hth_s).2.1
          have hbm_s := (epochMeta_offsets_le (w := w) hth_s).2.2.1
          have hod_s := (epochMeta_offsets_le (w := w) hth_s).2.2.2
          have hmS_p : s.mem (base + hdrMSrc) ≤ s.mem (base + hdrPad) := by
            rw [hpad_e]; exact le_max_left _ _
          rw [← h.mSrc_eq] at hod_s
          simp only [hs0, ↓reduceIte] at hmeta_s
          rcases hmeta_s with ⟨_, g2⟩ | ⟨_, _, g2⟩ <;> omega
      · simp only [hst0, ↓reduceIte] at hlo hhi hmeta_s
        have hth_d := (hsched.nDst_bounds.resolve_left hd0).1
        have hod_d := (epochMeta_offsets_le (w := w) hth_d).2.2.2
        have hmD_p : s.mem (base + hdrMDst) ≤ s.mem (base + hdrPad) := by
          rw [hpad_e]; exact le_max_right _ _
        rw [← hmD_e] at hod_d
        simp only [hd0, ↓reduceIte] at hmeta_s
        rcases hmeta_s with ⟨g1, _⟩ | ⟨_, g1, _⟩ <;> omega
    refine ⟨?_, hn_pg, hnot_d⟩
    intro hmeta_d
    by_cases hd0 : s.mem (base + hdrNDst) = 0
    · obtain ⟨hs_pos, hst0, _⟩ := hsched.nDst_zero hd0
      unfold slotOwnsNonPageMeta dualMbDst at hmeta_d
      rw [ite_eq_left hlt10] at hmeta_d
      simp only [hd0, ↓reduceIte, ne_eq, not_true_eq_false, false_and, or_false,
        hdrSmallMeta1] at hmeta_d
      unfold slotOwnsNonPageMeta dualMbSrc dualCapSrc at hmeta_s
      simp only [hst0, hs_pos.ne', ↓reduceIte] at hmeta_s
      rcases hmeta_s with ⟨g1, _⟩ | ⟨_, g1, _⟩ <;> omega
    · unfold slotOwnsNonPageMeta at hmeta_d
      simp only [hd0, ↓reduceIte] at hmeta_d
      have h32_d : 32 ≤ offPageDir c w (s.mem (base + hdrNDst)) := by
        have hth_d := (hsched.nDst_bounds.resolve_left hd0).1
        exact (epochMeta_offsets_le (w := w) hth_d).1.trans
          ((epochMeta_offsets_le (w := w) hth_d).2.1.trans
            (epochMeta_offsets_le (w := w) hth_d).2.2.1)
      rcases hmeta_d with ⟨g1, g2⟩ | ⟨_, g1, g2⟩ <;> exact hnot_d ⟨hd0, by omega, by omega⟩
  · simp only [SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr, directSlotIo, ↓reduceIte] at hio
    have hi_lo : s.mem (base + hdrItemHi) ≤ addr := hio.1
    have hn_pg : ¬(dualPgHost c 1 w base 0 s.mem).OwnsMetaAddr addr := fun hpg =>
      absurd hi_lo (Nat.not_le_of_gt (hdisj_pg addr ((hpg_meta_eq addr).mp hpg)).2.1)
    have hnot_d : ¬(s.mem (base + hdrNDst) ≠ 0 ∧ dualMbDst base s.mem ≤ addr ∧
        addr < dualMbDst base s.mem + offPageDir c w (s.mem (base + hdrNDst))) := by
      rintro ⟨hd0, _, hhi⟩
      have hth_d := (hsched.nDst_bounds.resolve_left hd0).1
      have hod_d := (epochMeta_offsets_le (w := w) hth_d).2.2.2
      have hmD_p : s.mem (base + hdrMDst) ≤ s.mem (base + hdrPad) := by
        rw [hpad_e]; exact le_max_right _ _
      rw [← hmD_e] at hod_d
      unfold dualMbDst at hhi; rw [ite_eq_left hlt10, ite_eq_right hd0] at hhi
      rw [hibHi_e, ite_eq_right hd0] at hi_lo
      split_ifs at hhi <;> omega
    refine ⟨?_, hn_pg, hnot_d⟩
    intro hmeta_d
    by_cases hd0 : s.mem (base + hdrNDst) = 0
    · unfold slotOwnsNonPageMeta dualMbDst at hmeta_d
      rw [ite_eq_left hlt10] at hmeta_d
      simp only [hd0, ↓reduceIte, ne_eq, not_true_eq_false, false_and, or_false,
        hdrSmallMeta1] at hmeta_d
      rw [hibHi_e, ite_eq_left hd0] at hi_lo; omega
    · unfold slotOwnsNonPageMeta at hmeta_d
      simp only [hd0, ↓reduceIte] at hmeta_d
      have h32_d : 32 ≤ offPageDir c w (s.mem (base + hdrNDst)) := by
        have hth_d := (hsched.nDst_bounds.resolve_left hd0).1
        exact (epochMeta_offsets_le (w := w) hth_d).1.trans
          ((epochMeta_offsets_le (w := w) hth_d).2.1.trans
            (epochMeta_offsets_le (w := w) hth_d).2.2.1)
      rcases hmeta_d with ⟨g1, g2⟩ | ⟨_, g1, g2⟩ <;> exact hnot_d ⟨hd0, by omega, by omega⟩

/-- Direct-I/O `RWConfined` witness for `userMutateRawProg` during Phases `4..7`. -/
theorem fg_direct_rw_of_47 {c U V w base opTag v_val : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s : Memory.State}
    (h : DualStateInv c U V w base s_dict L s)
    (hop_nz : opTag ≠ 0) (u : Fin U) (v : Fin V)
    (hp47 : 4 ≤ s.mem (base + hdrPhase) ∧ s.mem (base + hdrPhase) ≤ 7) :
    let nLive := (Dictionary.dom s_dict).card
    let nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
    let s_prep := (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val))
    let k_grow := (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val))
    let s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
    let pSrc := dualPSrc base s.mem
    let mbSrc := dualMbSrc base s.mem
    let capSrc := dualCapSrc base s.mem
    let io_al := directSlotIo w (valBits V) base (s.mem (base + hdrItemHi))
      (s.mem (base + hdrQHi)) nAlloc
    let act : Memory.Prog Unit :=
      if opTag = 1 then epochInsertProg ((pSrc, u.val), v_val) else epochDeleteProg (pSrc, u.val)
    (Memory.spec 0).clientState s_grow (userMutateRawProg ((base, opTag), (u.val, v_val))) =
      (Memory.spec 0).clientState s_grow act ∧
    RWConfined (SlotDirectRegion c w pSrc mbSrc capSrc io_al)
      (SlotDirectRegion c w pSrc mbSrc capSrc io_al) s_grow act := by
  dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier]
  have hsetup := fgSetup_of_dualStateInv h hop_nz u v
  set s_prep := (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val))
  set k_grow := (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val))
  set s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
  have hs_ph : s_grow.mem (base + hdrPhase) = s.mem (base + hdrPhase) :=
    hsetup.grow_low hdrPhase (by decide)
  have hs_stg : s_grow.mem (base + hdrStage) = s.mem (base + hdrStage) :=
    hsetup.grow_low hdrStage (by decide)
  have hdisp := (userMutateRawProg_eval (opTag := opTag) (u_val := u.val) (v_val := v_val)
    s_grow hs_ph hs_stg).1
  have hact_eq :
      (if opTag = 1 then
         if s.mem (base + hdrPhase) = 8 then
           epochDeleteProg
             (if s.mem (base + hdrStage) = 0 then base + hdrPBase0 else base + hdrPBase1, u.val) >>=
             fun _ => epochInsertProg
               ((if s.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0, u.val),
                 v_val)
         else if s.mem (base + hdrPhase) = 9 then
           epochInsertProg
             ((if s.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0, u.val),
               v_val)
         else if 3 < s.mem (base + hdrPhase) then
           if s.mem (base + hdrPhase) < 8 then
             epochInsertProg
               ((if s.mem (base + hdrStage) = 0 then base + hdrPBase0 else base + hdrPBase1, u.val),
                 v_val)
           else epochInsertProg ((base + hdrPBase0, u.val), v_val)
         else epochInsertProg ((base + hdrPBase0, u.val), v_val)
       else
         if s.mem (base + hdrPhase) = 8 then
           epochDeleteProg
             (if s.mem (base + hdrStage) = 0 then base + hdrPBase0 else base + hdrPBase1, u.val) >>=
             fun _ => epochDeleteProg
               (if s.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0, u.val)
         else if s.mem (base + hdrPhase) = 9 then
           epochDeleteProg
             (if s.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0, u.val)
         else if 3 < s.mem (base + hdrPhase) then
           if s.mem (base + hdrPhase) < 8 then
             epochDeleteProg
               (if s.mem (base + hdrStage) = 0 then base + hdrPBase0 else base + hdrPBase1, u.val)
           else epochDeleteProg (base + hdrPBase0, u.val)
         else epochDeleteProg (base + hdrPBase0, u.val)) =
      (if opTag = 1 then epochInsertProg ((dualPSrc base s.mem, u.val), v_val)
       else epochDeleteProg (dualPSrc base s.mem, u.val)) := by
    have h1 : s.mem (base + hdrPhase) ≠ 8 := by omega
    have h2 : s.mem (base + hdrPhase) ≠ 9 := by omega
    have h3 : 3 < s.mem (base + hdrPhase) := by omega
    have h4 : s.mem (base + hdrPhase) < 8 := by omega
    unfold dualPSrc
    by_cases hop1 : opTag = 1 <;> simp [hop1, h1, h2, h3, h4]
  rw [hact_eq] at hdisp
  obtain ⟨hcap_s, _, hsl_s, _⟩ := h.sl_le7 hp47.2
  have hio_s : activeSrcIo c w (valBits V) base (s.mem (base + hdrStage))
      (s.mem (base + hdrPhase)) (s.mem (base + hdrNSrc)) (s.mem (base + hdrNDst))
      (s.mem (base + hdrPad)) (s.mem (base + hdrItemLo)) (s.mem (base + hdrQLo))
      (s.mem (base + hdrItemHi)) (s.mem (base + hdrQHi)) (Dictionary.dom s_dict).card =
      directSlotIo w (valBits V) base (s.mem (base + hdrItemHi)) (s.mem (base + hdrQHi))
        (Dictionary.dom s_dict).card := by
    unfold activeSrcIo
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
  rw [hio_s] at hsl_s
  have hlift := @FGSetup.lift_grow_slot c U V w base opTag u v s_dict L s hsetup
  dsimp only at hlift
  obtain ⟨_, hpos_s, _, hm_hi_s⟩ := hsetup.mbSrc_info (by omega)
  have hibHi_192 : base + 192 ≤ s.mem (base + hdrItemHi) :=
    hsetup.ibLo_ge.trans hsetup.ibHi_ge_ibLo.1
  have hpSrc_or : dualPSrc base s.mem = base + hdrPBase0 ∨
      dualPSrc base s.mem = base + hdrPBase1 := by
    unfold dualPSrc; split_ifs <;> simp
  have hsl_g : EpochSlotInv c U V w s_grow.frontier (dualPSrc base s.mem) (dualMbSrc base s.mem)
      (directSlotIo w (valBits V) base (s.mem (base + hdrItemHi)) (s.mem (base + hdrQHi))
        (if opTag = 1 then min ((Dictionary.dom s_dict).card + 1) U
         else (Dictionary.dom s_dict).card))
      0 false L.slotSrc s_grow.mem :=
    hlift hsl_s rfl hpSrc_or hpos_s
      ⟨fun _ hsb => absurd rfl hsb, fun hup => absurd rfl hup, hibHi_192⟩
      (fun _ _ => hsetup.fr_bounds.2.2.2.1 ⟨by omega, by omega⟩)
      (fun _ hsb => absurd rfl hsb)
      (fun hup => absurd rfl hup)
      ⟨hm_hi_s (by omega), fun _ hsb => absurd rfl hsb⟩
  refine ⟨hdisp, ?_⟩
  rw [← hcap_s]
  by_cases hop1 : opTag = 1
  · simp only [hop1, ↓reduceIte] at hsl_g ⊢
    exact epochInsert_direct_rw (u_val := u.val) (v_val := v_val) hsl_g rfl
  · simp only [hop1, ↓reduceIte] at hsl_g ⊢
    exact epochDelete_direct_rw (u_val := u.val) hsl_g rfl

private theorem syncLive_of_not_slide {base : ℕ} {s : Memory.State}
    (hnot_p : ¬(s.mem (base + hdrPhase) = 3 ∨ s.mem (base + hdrPhase) = 10)) :
    ∃ cnt, (Memory.spec 0).clientState s (syncLiveCountsProg base) =
      { mem := Function.update
          (Function.update (Function.update s.mem (base + hdrLive) cnt)
            (base + hdrPBase0 + 60) cnt)
          (base + hdrPBase1 + 60) cnt
        frontier := s.frontier } := by
  have hsync := (syncLiveCountsProg_eval (base := base) s).1
  dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hsync
  rw [ite_eq_right (fun hp => hnot_p hp.1)] at hsync
  exact ⟨_, hsync⟩

private theorem syncLive_mem_eq_aux {c U V w base opTag v_val k_grow : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V}
    {s s_prep s_raw s_mid : Memory.State}
    (h : DualStateInv c U V w base s_dict L s)
    (hop_nz : opTag ≠ 0) (u : Fin U) (v : Fin V) (hv_eq : opTag = 1 → v_val = v.val)
    (hne3 : s.mem (base + hdrPhase) ≠ 3) (hne10 : s.mem (base + hdrPhase) ≠ 10)
    (hs_prep_def :
      s_prep = (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val)))
    (hk_grow_def :
      k_grow = (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val)))
    (hs_raw_def :
      s_raw =
        (Memory.spec 0).clientState { mem := s_prep.mem, frontier := s.frontier + k_grow }
          (userMutateRawProg ((base, opTag), (u.val, v_val))))
    (hs_mid_def :
      s_mid =
        (Memory.spec 0).clientState { mem := s_prep.mem, frontier := s.frontier + k_grow }
          (userMutateProg ((base, opTag), (u.val, v_val))))
    (hraw_ph : s_raw.mem (base + hdrPhase) = s.mem (base + hdrPhase)) :
    let s_dict' :=
      if opTag = 1 then Function.update s_dict u (some v.val)
      else Function.update s_dict u none
    let nLive' := (Dictionary.dom s_dict').card
    s_mid =
      { mem := Function.update
          (Function.update (Function.update s_raw.mem (base + hdrLive) nLive')
            (base + hdrPBase0 + 60) nLive')
          (base + hdrPBase1 + 60) nLive'
        frontier := s_raw.frontier } := by
  intro s_dict' nLive'
  have hsetup := fgSetup_of_dualStateInv h hop_nz u v
  have hstep : FGStepOutAux c U V w base opTag v_val u v s_dict L s s_prep k_grow s_mid := by
    by_cases hle7 : s.mem (base + hdrPhase) ≤ 7
    · exact fgStep_le7_aux h u v hv_eq hsetup hs_prep_def hk_grow_def hs_mid_def hle7
    · by_cases h8 : s.mem (base + hdrPhase) = 8
      · exact fgStep_eq8_aux h u v hv_eq hsetup hs_prep_def hk_grow_def hs_mid_def h8
      · exact fgStep_ge9_aux h u v hv_eq hsetup hs_prep_def hk_grow_def hs_mid_def (by omega)
  have hs_mid_live : s_mid.mem (base + hdrLive) = nLive' := hstep.2.2.1
  have hs_mid_sync : s_mid = (Memory.spec 0).clientState s_raw (syncLiveCountsProg base) := by
    rw [hs_mid_def, hs_raw_def]
    exact (userMutateProg_eval base opTag u.val v_val _).1
  clear hs_prep_def hk_grow_def hs_raw_def hs_mid_def hsetup hstep
  have hnot_p : ¬(s_raw.mem (base + hdrPhase) = 3 ∨ s_raw.mem (base + hdrPhase) = 10) := by
    rintro (h3 | h10)
    · exact hne3 (hraw_ph.symm.trans h3)
    · exact hne10 (hraw_ph.symm.trans h10)
  obtain ⟨cnt, hsync⟩ := syncLive_of_not_slide hnot_p
  rw [hs_mid_sync, hsync] at hs_mid_live ⊢
  dsimp only [Memory.State.mem] at hs_mid_live
  rw [Function.update_of_ne (by dsimp only [hdrPBase1, hdrLive]; omega),
    Function.update_of_ne (by dsimp only [hdrPBase0, hdrLive]; omega),
    Function.update_self] at hs_mid_live
  rw [hs_mid_live]

/-- Explicit memory update characterization of `userMutateProg` outside Phases `3` and `10`. -/
theorem syncLive_mem_eq_of_ne3_10 {c U V w base opTag v_val : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s : Memory.State}
    (h : DualStateInv c U V w base s_dict L s)
    (hop_nz : opTag ≠ 0) (u : Fin U) (v : Fin V) (hv_eq : opTag = 1 → v_val = v.val)
    (hne3 : s.mem (base + hdrPhase) ≠ 3) (hne10 : s.mem (base + hdrPhase) ≠ 10) :
    let s_dict' :=
      if opTag = 1 then Function.update s_dict u (some v.val)
      else Function.update s_dict u none
    let nLive' := (Dictionary.dom s_dict').card
    let s_prep := (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val))
    let k_grow := (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val))
    let s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
    let s_raw := (Memory.spec 0).clientState s_grow
      (userMutateRawProg ((base, opTag), (u.val, v_val)))
    let s_mid := (Memory.spec 0).clientState s_grow
      (userMutateProg ((base, opTag), (u.val, v_val)))
    s_raw.mem (base + hdrPhase) = s.mem (base + hdrPhase) →
    s_mid =
      { mem := Function.update
          (Function.update (Function.update s_raw.mem (base + hdrLive) nLive')
            (base + hdrPBase0 + 60) nLive')
          (base + hdrPBase1 + 60) nLive'
        frontier := s_raw.frontier } := by
  intro _ _ _ _ _ _ _ hraw_ph
  exact syncLive_mem_eq_aux h hop_nz u v hv_eq hne3 hne10 rfl rfl rfl rfl hraw_ph

private theorem dualPh5MaskMem_of_lt48 (V w base pDst ibHi qHi nLive : ℕ) (mem : ℕ → ℕ)
    {k : ℕ} (hk : k < 48) :
    dualPh5MaskMem V w base pDst ibHi qHi nLive mem (pDst + k) = mem (pDst + k) := by
  unfold dualPh5MaskMem
  iterate 13 rw [Function.update_of_ne (by omega)]

private theorem finishRandFill_initZeroed_outside {c U V w base nDst metaDst : ℕ}
    {s_dict' : Dictionary.State U} {st : Memory.State} {L : DualLatent c U V}
    (hd_pos : 0 < nDst)
    (hm : DualMidInv c U V w base s_dict' L st)
    (hp5_st : st.mem (base + hdrPhase) = 5)
    (hnD_st : st.mem (base + hdrNDst) = nDst)
    (hmbD_st : dualMbDst base st.mem = metaDst)
    (hprf_st : FinishRandFillPre w base st) :
    let pD := if st.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0
    let md := if st.mem (base + hdrStage) = 0 then base + 192 + st.mem (base + hdrPad)
      else base + 192
    let msk := ((1 : ℕ) <<< (st.mem (base + hdrRedW) - 1)) - 1
    let st1 : Memory.State :=
      { mem := Function.update
          (Function.update st.mem (md + 32) (st.mem (md + 32) &&& msk))
          (md + st.mem (pD + 30)) (st.mem (md + st.mem (pD + 30)) &&& msk)
        frontier := st.frontier }
    let st2 := (Memory.spec 0).clientState st1
      (setDirectSlotIoProg ((base, pD),
        ((st.mem (base + hdrItemHi), st.mem (base + hdrQHi)),
          st.mem (base + hdrLive))))
    ∀ b, ¬(metaDst ≤ b ∧ b < metaDst + offPageDir c w nDst) →
      ((Memory.spec 0).clientState st2 (epochInitZeroedProg pD)).mem b = st2.mem b := by
  intro pD md msk st1 st2 b hnot_b
  obtain ⟨_, _, _, _, _, _, hepre⟩ := hprf_st
  change EpochProgPre w pD st2 at hepre
  have hmd_eq : md = metaDst := by
    dsimp only [md]; rw [← hmbD_st]; unfold dualMbDst
    rw [hp5_st, ite_eq_left (by decide : 5 < 10), hnD_st, ite_eq_right hd_pos.ne']
  have hpD_d : pD = dualPDst base st.mem := by
    dsimp only [pD]; unfold dualPDst; rw [hp5_st, ite_eq_left (by decide : 5 < 10)]
  have hpD_lt48 : ∀ k < 48, st2.mem (pD + k) = st.mem (dualPDst base st.mem + k) := by
    intro k hk
    dsimp only [st2]
    rw [(setDirectSlotIoProg_eval _ _ _ _ _ _).1,
      (setSlotIoProg_frame pD _).mem_outside _ (pD + k) (by omega)]
    dsimp only [st1]
    have hmd_192 : base + 192 ≤ metaDst := by
      rw [← hmd_eq]; dsimp only [md]; split_ifs <;> omega
    have hpD_hi : pD + k < base + 192 := by
      dsimp only [pD, hdrPBase0, hdrPBase1]; split_ifs <;> omega
    rw [hmd_eq,
      Function.update_of_ne (by omega),
      Function.update_of_ne (by omega),
      hpD_d]
  have hpD_0 : st2.mem pD = nDst := by
    have h0 := (hm.ph5_inv hp5_st).2.2.2.1 0 (by decide)
    dsimp only [FastEpochLayout.paramWord] at h0
    rw [dualPh5MaskMem_of_lt48 _ _ _ _ _ _ _ _ (by decide), Nat.add_zero] at h0
    have hk0 := hpD_lt48 0 (by decide)
    rw [Nat.add_zero, Nat.add_zero] at hk0
    exact hk0.trans (h0.trans hnD_st)
  unfold EpochProgPre at hepre
  rcases hepre with ⟨hz, _⟩ | ⟨_, fl_st, hpB_e, hr_st2⟩
  · exact absurd (hpD_0.symm.trans hz) hd_pos.ne'
  · have hmconf := epochInitZeroedProg_meta_confine hr_st2
    have hN_fl : fl_st.N = nDst := by
      have h0 := hr_st2.2.1 0 (by decide)
      dsimp only [FastEpochLayout.paramWord] at h0
      rw [hpB_e, Nat.add_zero, hpD_0] at h0
      exact h0.symm
    have hmb_fl : fl_st.metaBase = metaDst := by
      have h1 := hr_st2.2.1 1 (by decide)
      dsimp only [FastEpochLayout.paramWord] at h1
      rw [hpB_e, hpD_lt48 1 (by decide)] at h1
      have h1' := (hm.ph5_inv hp5_st).2.2.2.1 1 (by decide)
      dsimp only [FastEpochLayout.paramWord] at h1'
      rw [dualPh5MaskMem_of_lt48 _ _ _ _ _ _ _ _ (by decide)] at h1'
      exact h1.symm.trans (h1'.trans hmbD_st)
    have hod_fl : offPageDir fl_st.c fl_st.w fl_st.N = offPageDir c w nDst := by
      have h2 := hr_st2.2.1 2 (by decide)
      dsimp only [FastEpochLayout.paramWord] at h2
      rw [hpB_e, hpD_lt48 2 (by decide)] at h2
      have h2' := (hm.ph5_inv hp5_st).2.2.2.1 2 (by decide)
      dsimp only [FastEpochLayout.paramWord] at h2'
      rw [dualPh5MaskMem_of_lt48 _ _ _ _ _ _ _ _ (by decide)] at h2'
      have hw_fl : fl_st.w = w := h2.symm.trans h2'
      have h43 := hr_st2.2.1 43 (by decide)
      dsimp only [FastEpochLayout.paramWord] at h43
      rw [hpB_e, hpD_lt48 43 (by decide)] at h43
      have h43' := (hm.ph5_inv hp5_st).2.2.2.1 43 (by decide)
      dsimp only [FastEpochLayout.paramWord] at h43'
      rw [dualPh5MaskMem_of_lt48 _ _ _ _ _ _ _ _ (by decide), hnD_st] at h43'
      have hotn : offTrieNode fl_st.c fl_st.w fl_st.N 2 = offTrieNode c w nDst 2 := by
        have hti := h43.symm.trans h43'
        unfold offTrieItem at hti
        simpa only [zero_mul, add_zero] using hti
      unfold offPageDir offTrieItem
      rw [hotn, hw_fl, hN_fl]
    rw [← hpB_e]
    refine hmconf b ?_
    rw [hmb_fl, hod_fl]
    exact hnot_b

private theorem finishRandFill_agree_outside {c U V w base nDst metaDst : ℕ}
    {s_dict' : Dictionary.State U} {L_ra L_rs : DualLatent c U V}
    {s_r_anc s_r : Memory.State}
    (hd_pos : 0 < nDst) (hth_d : whpThreshold c ≤ nDst)
    (hmd_192 : base + 192 ≤ metaDst)
    (hmid_ra : DualMidInv c U V w base s_dict' L_ra s_r_anc)
    (hmid_rs : DualMidInv c U V w base s_dict' L_rs s_r)
    (hp5_ra : s_r_anc.mem (base + hdrPhase) = 5)
    (hp5_rs : s_r.mem (base + hdrPhase) = 5)
    (hnD_rs : s_r.mem (base + hdrNDst) = nDst)
    (hmbD_rs : dualMbDst base s_r.mem = metaDst)
    (hpre_rf_a : FinishRandFillPre w base s_r_anc)
    (hpre_rf_s : FinishRandFillPre w base s_r)
    (hsr_out : ∀ b, ¬(metaDst ≤ b ∧ b < metaDst + offPageDir c w nDst) →
      s_r_anc.mem b = s_r.mem b) :
    (∀ addr, ¬(metaDst ≤ addr ∧ addr < metaDst + offPageDir c w nDst) →
      ((Memory.spec 0).clientState s_r_anc (finishRandFillProg base)).mem addr =
        ((Memory.spec 0).clientState s_r (finishRandFillProg base)).mem addr) ∧
    (∀ off < 48, off ≠ hdrPhase → off ≠ hdrCur →
      ((Memory.spec 0).clientState s_r (finishRandFillProg base)).mem (base + off) =
        s_r.mem (base + off)) := by
  have hod_ge_bm : offBktMeta c w nDst ≤ offPageDir c w nDst :=
    (epochMeta_offsets_le (w := w) hth_d).2.2.1
  refine ⟨fun addr hnot_m => ?_, fun off hoff hne_p hne_c => ?_⟩
  · rw [(finishRandFillProg_eval base s_r_anc).1, (finishRandFillProg_eval base s_r).1]
    dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier]
    by_cases hp_o : addr = base + hdrPhase
    · subst hp_o; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hp_o, Function.update_of_ne hp_o]
      by_cases hc_o : addr = base + hdrCur
      · subst hc_o; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hc_o, Function.update_of_ne hc_o]
        have hnD_ra : s_r_anc.mem (base + hdrNDst) = nDst := by
          rw [hsr_out (base + hdrNDst) (by dsimp only [hdrNDst]; omega)]
          exact hnD_rs
        have hmbD_ra : dualMbDst base s_r_anc.mem = metaDst := by
          unfold dualMbDst
          rw [hp5_ra, hnD_ra,
            hsr_out (base + hdrStage) (by dsimp only [hdrStage]; omega),
            hsr_out (base + hdrPad) (by dsimp only [hdrPad]; omega)]
          rw [← hp5_rs, ← hnD_rs]; exact hmbD_rs
        rw [finishRandFill_initZeroed_outside hd_pos hmid_ra hp5_ra hnD_ra hmbD_ra hpre_rf_a
            addr hnot_m,
          finishRandFill_initZeroed_outside hd_pos hmid_rs hp5_rs hnD_rs hmbD_rs hpre_rf_s
            addr hnot_m]
        have hhdr_eq : ∀ off < 48, s_r_anc.mem (base + off) = s_r.mem (base + off) :=
          fun off hoff => hsr_out (base + off) (by omega)
        rw [← hhdr_eq hdrStage (by decide),
          ← hhdr_eq hdrPad (by decide),
          ← hhdr_eq hdrRedW (by decide),
          ← hhdr_eq hdrItemHi (by decide),
          ← hhdr_eq hdrQHi (by decide),
          ← hhdr_eq hdrLive (by decide)]
        set pD := if s_r_anc.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0
        set md := if s_r_anc.mem (base + hdrStage) = 0 then
            base + 192 + s_r_anc.mem (base + hdrPad)
          else base + 192
        have hmd_eq : md = metaDst := by
          dsimp only [md]; rw [← hmbD_ra]; unfold dualMbDst
          rw [hp5_ra, ite_eq_left (by decide : 5 < 10), hnD_ra, ite_eq_right hd_pos.ne']
        rw [(setDirectSlotIoProg_eval _ _ _ _ _ _).1, (setDirectSlotIoProg_eval _ _ _ _ _ _).1]
        have hwv_eq : ∀ st_m : Memory.State,
            (∀ b, ¬(metaDst ≤ b ∧ b < metaDst + offPageDir c w nDst) →
              st_m.mem b = s_r_anc.mem b) →
            directSlotIo (st_m.mem (base + hdrW)) (st_m.mem (base + hdrValBits)) base
              (s_r_anc.mem (base + hdrItemHi)) (s_r_anc.mem (base + hdrQHi))
              (s_r_anc.mem (base + hdrLive)) =
            directSlotIo (s_r_anc.mem (base + hdrW)) (s_r_anc.mem (base + hdrValBits)) base
              (s_r_anc.mem (base + hdrItemHi)) (s_r_anc.mem (base + hdrQHi))
              (s_r_anc.mem (base + hdrLive)) := fun st_m hm_st => by
          rw [hm_st (base + hdrW) (by dsimp only [hdrW]; omega),
            hm_st (base + hdrValBits) (by dsimp only [hdrValBits]; omega)]
        have hp30_ra : s_r_anc.mem (pD + 30) = offFpHash c w nDst := by
          have hpD_d : pD = dualPDst base s_r_anc.mem := by
            dsimp only [pD]; unfold dualPDst; rw [hp5_ra, ite_eq_left (by decide : 5 < 10)]
          rw [hpD_d]
          have h30 := (hmid_ra.ph5_inv hp5_ra).2.2.2.1 30 (by decide)
          dsimp only [FastEpochLayout.paramWord] at h30
          rw [dualPh5MaskMem_of_lt48 _ _ _ _ _ _ _ _ (by decide), hnD_ra] at h30
          exact h30
        have hp30_rs : s_r.mem (pD + 30) = offFpHash c w nDst := by
          have hp_hi : pD + 30 < base + 192 := by
            dsimp only [pD, hdrPBase0, hdrPBase1]; split_ifs <;> omega
          rw [← hsr_out (pD + 30) (by omega)]
          exact hp30_ra
        have hfp_in : metaDst ≤ metaDst + offFpHash c w nDst ∧
            metaDst + offFpHash c w nDst < metaDst + offPageDir c w nDst := by
          have hsp_fp := BitPackedDoubleTabulation.space_pos w (cTabWhp c) (dTabWhp c)
            (bCharWhp nDst) (fpBitsWhp nDst)
          have hlt_bm : offFpHash c w nDst < offBktMeta c w nDst := by unfold offBktMeta; omega
          exact ⟨Nat.le_add_right _ _, by omega⟩
        have h32_in : metaDst ≤ metaDst + 32 ∧ metaDst + 32 < metaDst + offPageDir c w nDst := by
          have hsp_b := BitPackedDoubleTabulation.space_pos w (cTabWhp c) (dTabWhp c)
            (bCharWhp nDst) (bWhp nDst)
          have hlt_fp : 32 < offFpHash c w nDst := by unfold offFpHash offBktHash; omega
          have hfp_le : offFpHash c w nDst ≤ offBktMeta c w nDst :=
            (epochMeta_offsets_le (w := w) hth_d).2.1
          exact ⟨Nat.le_add_right _ _, by omega⟩
        rw [hmd_eq, hp30_ra, hp30_rs]
        set msk := ((1 : ℕ) <<< (s_r_anc.mem (base + hdrRedW) - 1)) - 1
        set st1_a : Memory.State :=
          { mem := Function.update
              (Function.update s_r_anc.mem (metaDst + 32) (s_r_anc.mem (metaDst + 32) &&& msk))
              (metaDst + offFpHash c w nDst)
              (s_r_anc.mem (metaDst + offFpHash c w nDst) &&& msk)
            frontier := s_r_anc.frontier }
        set st1_s : Memory.State :=
          { mem := Function.update
              (Function.update s_r.mem (metaDst + 32) (s_r.mem (metaDst + 32) &&& msk))
              (metaDst + offFpHash c w nDst)
              (s_r.mem (metaDst + offFpHash c w nDst) &&& msk)
            frontier := s_r.frontier }
        set io_d := directSlotIo (s_r_anc.mem (base + hdrW)) (s_r_anc.mem (base + hdrValBits))
          base (s_r_anc.mem (base + hdrItemHi)) (s_r_anc.mem (base + hdrQHi))
          (s_r_anc.mem (base + hdrLive))
        have hst1_a_out : ∀ b, ¬(metaDst ≤ b ∧ b < metaDst + offPageDir c w nDst) →
            st1_a.mem b = s_r_anc.mem b := by
          intro b hnb; dsimp only [st1_a, Memory.State.mem]
          rw [Function.update_of_ne (by rintro rfl; exact hnb hfp_in),
            Function.update_of_ne (by rintro rfl; exact hnb h32_in)]
        have hst1_s_out : ∀ b, ¬(metaDst ≤ b ∧ b < metaDst + offPageDir c w nDst) →
            st1_s.mem b = s_r_anc.mem b := by
          intro b hnb; dsimp only [st1_s, Memory.State.mem]
          rw [Function.update_of_ne (by rintro rfl; exact hnb hfp_in),
            Function.update_of_ne (by rintro rfl; exact hnb h32_in), hsr_out b hnb]
        rw [hwv_eq st1_a hst1_a_out, hwv_eq st1_s hst1_s_out]
        by_cases h48 : pD + 48 ≤ addr ∧ addr < pD + 61
        · have hv1 := setSlotIoProg_mem_vals pD io_d st1_a
          have hv2 := setSlotIoProg_mem_vals pD io_d st1_s
          dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hv1 hv2
          have hj : addr - (pD + 48) < 13 := by omega
          have ha_off : addr = pD + (48 + (addr - (pD + 48))) := by omega
          rw [ha_off]
          interval_cases (addr - (pD + 48))
          · exact hv1.1.trans hv2.1.symm
          · exact hv1.2.1.trans hv2.2.1.symm
          · exact hv1.2.2.1.trans hv2.2.2.1.symm
          · exact hv1.2.2.2.1.trans hv2.2.2.2.1.symm
          · exact hv1.2.2.2.2.1.trans hv2.2.2.2.2.1.symm
          · exact hv1.2.2.2.2.2.1.trans hv2.2.2.2.2.2.1.symm
          · exact hv1.2.2.2.2.2.2.1.trans hv2.2.2.2.2.2.2.1.symm
          · exact hv1.2.2.2.2.2.2.2.1.trans hv2.2.2.2.2.2.2.2.1.symm
          · exact hv1.2.2.2.2.2.2.2.2.1.trans hv2.2.2.2.2.2.2.2.2.1.symm
          · exact hv1.2.2.2.2.2.2.2.2.2.1.trans hv2.2.2.2.2.2.2.2.2.2.1.symm
          · exact hv1.2.2.2.2.2.2.2.2.2.2.1.trans hv2.2.2.2.2.2.2.2.2.2.2.1.symm
          · exact hv1.2.2.2.2.2.2.2.2.2.2.2.1.trans hv2.2.2.2.2.2.2.2.2.2.2.2.1.symm
          · exact hv1.2.2.2.2.2.2.2.2.2.2.2.2.trans hv2.2.2.2.2.2.2.2.2.2.2.2.2.symm
        · rw [(setSlotIoProg_frame pD io_d.toCtx).mem_outside _ addr h48,
            (setSlotIoProg_frame pD io_d.toCtx).mem_outside _ addr h48,
            hst1_a_out addr hnot_m, hst1_s_out addr hnot_m]
  · rw [(finishRandFillProg_eval base s_r).1]
    dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier]
    rw [Function.update_of_ne (base_add_ne hne_p), Function.update_of_ne (base_add_ne hne_c),
      finishRandFill_initZeroed_outside hd_pos hmid_rs hp5_rs hnD_rs hmbD_rs hpre_rf_s
        (base + off) (by omega),
      (setDirectSlotIoProg_eval _ _ _ _ _ _).1,
      (setSlotIoProg_frame _ _).mem_outside _ (base + off) (by
        dsimp only [hdrPBase0, hdrPBase1]; split_ifs <;> omega)]
    dsimp only [Memory.State.mem]
    have hmd_s : (if s_r.mem (base + hdrStage) = 0 then base + 192 + s_r.mem (base + hdrPad)
        else base + 192) = metaDst := by
      rw [← hmbD_rs]; unfold dualMbDst
      rw [hp5_rs, ite_eq_left (by decide : 5 < 10), hnD_rs, ite_eq_right hd_pos.ne']
    rw [hmd_s, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

/-- Phase-`5` mutation equivariance (`5 → 5` stays in `Ph5StateAt` with `finAppendWords`;
`5 → 6` enters `Coupled67` with `seedsDst = seedsOfWords c U w nDst ws_seed`). -/
theorem ph5_mutate_step {c U V w base opTag v_val k_pre : ℕ}
    {s_dict : Dictionary.State U} {L_anc L_s : DualLatent c U V}
    {s_anc s : Memory.State} {ws_pre : Fin k_pre → Fin (2 ^ w)}
    (h_anc : DualStateInv c U V w base s_dict L_anc s_anc)
    (h_s : DualStateInv c U V w base s_dict L_s s)
    (hph5 : Ph5StateAt c w base s_anc k_pre ws_pre s)
    (hop_nz : opTag ≠ 0) (u : Fin U) (v : Fin V) (hv_eq : opTag = 1 → v_val = v.val)
    (hsucc_fits' :
      let s_dict' :=
        if opTag = 1 then Function.update s_dict u (some v.val)
        else Function.update s_dict u none
      base + Dynamic.succinctWords (whpResizableSpaceFactor c) whpResizableSpaceConst U V w
        (Dictionary.dom s_dict').card < 2 ^ w)
    (hpad_fits' :
      let s_dict' :=
        if opTag = 1 then Function.update s_dict u (some v.val)
        else Function.update s_dict u none
      base + dualPaddedWords c U V w (s_anc.mem (base + hdrNSrc))
        (if s_anc.mem (base + hdrPhase) = 0 then s_anc.mem (base + hdrNSrc)
         else s_anc.mem (base + hdrNDst)) (Dictionary.dom s_dict').card < 2 ^ w) :
    let s_dict' :=
      if opTag = 1 then Function.update s_dict u (some v.val)
      else Function.update s_dict u none
    let cur := s_anc.mem (base + hdrCur)
    let nDst := s_anc.mem (base + hdrNDst)
    let offBM := offBktMeta c w nDst
    let endOff := cur + min bulkBatchWhp (offBM - cur)
    let metaDst := dualMbDst base s_anc.mem
    let k_grow :=
      (Memory.spec 0).clientResult s_anc (prepGrowProg (((base, s_anc.frontier), opTag), u.val))
    let s_prep_anc :=
      (Memory.spec 0).clientState s_anc (prepGrowProg (((base, s_anc.frontier), opTag), u.val))
    let s_prep :=
      (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val))
    let s_grow_anc : Memory.State := { mem := s_prep_anc.mem, frontier := s_anc.frontier + k_grow }
    let s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
    let s_tick_anc :=
      (Memory.spec 0).clientState s_grow_anc (stepOpProg (((base, s_grow_anc.frontier), opTag),
        (u.val, v_val)))
    let s_tick :=
      (Memory.spec 0).clientState s_grow (stepOpProg (((base, s_grow.frontier), opTag),
        (u.val, v_val)))
    let ws_zero : Fin (endOff - cur) → Fin (2 ^ w) := fun _ => wordOfNat w 0
    let s_r_anc : Memory.State :=
      { mem := writeWords s_tick_anc.mem (metaDst + cur) ws_zero, frontier := s_tick_anc.frontier }
    let s_ps_anc := (Memory.spec 0).clientState s_r_anc
      (postRandShrinkProg ((base, s_r_anc.frontier), opTag))
    let k_sh_anc := (Memory.spec 0).clientResult s_r_anc
      (postRandShrinkProg ((base, s_r_anc.frontier), opTag))
    let s_post_anc : Memory.State :=
      { mem := clear s_ps_anc.mem (s_r_anc.frontier - k_sh_anc) k_sh_anc
        frontier := s_r_anc.frontier - k_sh_anc }
    0 < nDst ∧
    ∀ ws_batch : Fin (endOff - cur) → Fin (2 ^ w),
      let s_r : Memory.State :=
        { mem := writeWords s_tick.mem (metaDst + cur) ws_batch, frontier := s_tick.frontier }
      let s_ps := (Memory.spec 0).clientState s_r
        (postRandShrinkProg ((base, s_r.frontier), opTag))
      let k_sh := (Memory.spec 0).clientResult s_r
        (postRandShrinkProg ((base, s_r.frontier), opTag))
      let s_post : Memory.State :=
        { mem := clear s_ps.mem (s_r.frontier - k_sh) k_sh
          frontier := s_r.frontier - k_sh }
      (endOff < offBM →
        s_post_anc.mem (base + hdrPhase) = 5 ∧
        Ph5StateAt c w base s_post_anc (k_pre + (endOff - cur))
          (finAppendWords ws_pre ws_batch) s_post) ∧
      (∀ heq_bm : endOff = offBM,
        let hlen : k_pre + (endOff - cur) = (if nDst = 0 then 0 else offBM - 32) := by
          have hp := (h_anc.ph5_inv hph5.1).1
          rw [ite_eq_right hp.ne']
          have h32 := hph5.2.1
          omega
        let ws_seed : SeedWords c w nDst :=
          fun i => (finAppendWords ws_pre ws_batch) (i.cast hlen.symm)
        s_post_anc.mem (base + hdrPhase) = 6 ∧
        Coupled67 c w base s_post_anc s_post ∧
        DualStateInv c U V w base s_dict'
          { (L_s.applyFG 5 opTag u v) with
            slotDst := ⟨nDst, fun _ => none, seedsOfWords c U w nDst ws_seed, []⟩
            elapsed := L_s.elapsed + 1 }
          s_post) := by
  dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier]
  have hsch := hph5.schedEq h_anc
  obtain ⟨hp5, hcur_pre, hpre_le_bm, hs_eq_anc⟩ := hph5
  have hd_pos : 0 < s_anc.mem (base + hdrNDst) := (h_anc.ph5_inv hp5).1
  have hw_pos : 0 < w := by have := h_anc.hw11; omega
  have hpad_s :
      let s_dict' :=
        if opTag = 1 then Function.update s_dict u (some v.val)
        else Function.update s_dict u none
      base + dualPaddedWords c U V w (s.mem (base + hdrNSrc))
        (if s.mem (base + hdrPhase) = 0 then s.mem (base + hdrNSrc)
         else s.mem (base + hdrNDst)) (Dictionary.dom s_dict').card < 2 ^ w := by
    dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hpad_fits' ⊢
    rwa [← hsch.2 hdrNSrc (by decide) (by decide),
      ← hsch.2 hdrPhase (by decide) (by decide),
      ← hsch.2 hdrNDst (by decide) (by decide)]
  obtain ⟨hkg_eq, hres2_eq, hsch_tick, _, hpost_sch5⟩ :=
    schedEq_mutate_step h_anc h_s hsch hop_nz u v hv_eq hsucc_fits' hpad_fits'
  set cur := s_anc.mem (base + hdrCur)
  set nDst := s_anc.mem (base + hdrNDst)
  set offBM := offBktMeta c w nDst
  change 32 + k_pre ≤ offBM at hpre_le_bm
  set endOff := cur + min bulkBatchWhp (offBM - cur)
  set metaDst := dualMbDst base s_anc.mem
  have hmd_192 : base + 192 ≤ metaDst := by
    dsimp only [metaDst]; unfold dualMbDst
    rw [hp5, ite_eq_left (by decide : 5 < 10), ite_eq_right hd_pos.ne']
    split_ifs <;> omega
  set k_grow :=
    (Memory.spec 0).clientResult s_anc (prepGrowProg (((base, s_anc.frontier), opTag), u.val))
  set s_prep_anc :=
    (Memory.spec 0).clientState s_anc (prepGrowProg (((base, s_anc.frontier), opTag), u.val))
  set s_prep :=
    (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val))
  set s_grow_anc : Memory.State := { mem := s_prep_anc.mem, frontier := s_anc.frontier + k_grow }
  set s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
  -- Step 1: `s_grow` has `writeWords s_grow_anc.mem (metaDst + 32) ws_pre`
  have hu1_anc : s_anc.mem (base + hdrU1) + 1 ≤ 2 ^ w := by
    have := h_anc.hdr.1; have := h_anc.U_pos; have := h_anc.U_lt; omega
  have hnL_anc : s_anc.mem (base + hdrLive) ≤ s_anc.mem (base + hdrU1) + 1 := by
    rw [h_anc.live_eq, h_anc.hdr.1]; have := h_anc.U_pos; have := h_anc.live_le; omega
  have hu1_s : s.mem (base + hdrU1) + 1 ≤ 2 ^ w := by
    have := h_s.hdr.1; have := h_s.U_pos; have := h_s.U_lt; omega
  have hnL_s : s.mem (base + hdrLive) ≤ s.mem (base + hdrU1) + 1 := by
    rw [h_s.live_eq, h_s.hdr.1]; have := h_s.U_pos; have := h_s.live_le; omega
  have hp_anc := (prepGrowProg_eval (opTag := opTag) (u_val := u.val) hop_nz hw_pos
    h_anc.hdr.2.2.1 hu1_anc hnL_anc).1
  have hp_s := (prepGrowProg_eval (opTag := opTag) (u_val := u.val) hop_nz hw_pos
    h_s.hdr.2.2.1 hu1_s hnL_s).1
  dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hp_anc hp_s
  have hgrow_ww :
      s_grow = { mem := writeWords s_grow_anc.mem (metaDst + 32) ws_pre
                 frontier := s_grow_anc.frontier } := by
    dsimp only [s_grow, s_grow_anc]
    congr 1
    · dsimp only [s_prep, s_prep_anc]
      rw [hp_s, hp_anc]
      dsimp only [Memory.State.mem]
      rw [← hsch.2 hdrLive (by decide) (by decide), ← hsch.2 hdrU1 (by decide) (by decide)]
      by_cases hop1 : opTag = 1
      · simp only [hop1, ↓reduceIte, hs_eq_anc]
        rw [update_writeWords_out _ (metaDst + 32) k_pre (base + hdrPBase0 + 60) _ ws_pre
            (by dsimp only [hdrPBase0]; omega),
          update_writeWords_out _ (metaDst + 32) k_pre (base + hdrPBase1 + 60) _ ws_pre
            (by dsimp only [hdrPBase1]; omega)]
      · simp only [hop1, ↓reduceIte, hs_eq_anc]
    · exact hsch.1.symm ▸ rfl
  -- Step 2: `userMutateRawProg` commutes with `writeWords · (metaDst + 32) ws_pre`
  obtain ⟨hd_anc, hrw_anc⟩ := fg_direct_rw_of_47 (v_val := v_val) h_anc hop_nz u v
    ⟨by rw [hp5]; decide, by rw [hp5]; decide⟩
  obtain ⟨hd_s, _⟩ := fg_direct_rw_of_47 (v_val := v_val) h_s hop_nz u v
    ⟨by rw [← hsch.2 hdrPhase (by decide) (by decide), hp5]; decide,
     by rw [← hsch.2 hdrPhase (by decide) (by decide), hp5]; decide⟩
  dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hd_anc hrw_anc hd_s
  rw [← hkg_eq] at hd_s
  rw [← hsch.pSrc_eq] at hd_s
  change (Memory.spec 0).clientState s_grow_anc
      (userMutateRawProg ((base, opTag), (u.val, v_val))) =
    (Memory.spec 0).clientState s_grow_anc _ at hd_anc
  change (Memory.spec 0).clientState s_grow
      (userMutateRawProg ((base, opTag), (u.val, v_val))) =
    (Memory.spec 0).clientState s_grow _ at hd_s
  change RWConfined _ _ s_grow_anc _ at hrw_anc
  have hdisj_src := srcDirect_disj_dstMeta (opTag := opTag) h_anc
    ⟨by rw [hp5]; decide, by rw [hp5]; decide⟩
  dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hdisj_src
  have hod_bm : offBM ≤ offPageDir c w nDst := by
    have hsched_a := h_anc.sched; rw [ite_eq_right (by rw [hp5]; decide)] at hsched_a
    have hth_d := (hsched_a.nDst_bounds.resolve_left hd_pos.ne').1
    exact (epochMeta_offsets_le (w := w) hth_d).2.2.1
  have hdisj_ww : ∀ i < k_pre,
      ¬SlotDirectRegion c w (dualPSrc base s_anc.mem) (dualMbSrc base s_anc.mem)
        (dualCapSrc base s_anc.mem)
        (directSlotIo w (valBits V) base (s_anc.mem (base + hdrItemHi))
          (s_anc.mem (base + hdrQHi))
          (if opTag = 1 then min ((Dictionary.dom s_dict).card + 1) U
           else (Dictionary.dom s_dict).card))
        (metaDst + 32 + i) := fun i hi hsr => by
    refine (hdisj_src (metaDst + 32 + i) hsr).2.2 ⟨hd_pos.ne', ?_, ?_⟩
    · dsimp only [metaDst]; omega
    · dsimp only [metaDst, nDst, offBM] at hod_bm hpre_le_bm ⊢; omega
  have hraw_ww :
      (Memory.spec 0).clientState s_grow (userMutateRawProg ((base, opTag), (u.val, v_val))) =
        { mem := writeWords
            ((Memory.spec 0).clientState s_grow_anc
              (userMutateRawProg ((base, opTag), (u.val, v_val)))).mem
            (metaDst + 32) ws_pre
          frontier :=
            ((Memory.spec 0).clientState s_grow_anc
              (userMutateRawProg ((base, opTag), (u.val, v_val)))).frontier } := by
    rw [hd_s, hd_anc, hgrow_ww]
    exact (rwConfined_writeWords_comm hrw_anc hdisj_ww ws_pre).2
  -- Step 3: `syncLiveCountsProg` and `bgTickProg` (`tickRandPrepProg`) commute with `writeWords`
  have hraw_ph_anc :
      ((Memory.spec 0).clientState s_grow_anc
        (userMutateRawProg ((base, opTag), (u.val, v_val)))).mem (base + hdrPhase) = 5 := by
    rw [hd_anc]
    have hout := hrw_anc.out₁ (base + hdrPhase) fun hsr => by
      rcases hsr with ⟨h1, _⟩ | hm | hio
      · unfold dualPSrc at h1
        dsimp only [hdrPBase0, hdrPBase1, hdrPhase] at h1; split_ifs at h1 <;> omega
      · have hb := slotOwnsNonPageMeta_src_range rfl (fun _ => hd_pos.ne') hm
        dsimp only [hdrPhase] at hb ⊢; rcases hb with ⟨h1, _⟩ | h1 <;> omega
      · simp only [SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr, directSlotIo,
          ↓reduceIte] at hio
        have hib := (fgSetup_of_dualStateInv h_anc hop_nz u v).ibLo_ge.trans
          (fgSetup_of_dualStateInv h_anc hop_nz u v).ibHi_ge_ibLo.1
        dsimp only [hdrPhase] at hio; have h1 := hio.1; omega
    have hlow : s_grow_anc.mem (base + hdrPhase) = s_anc.mem (base + hdrPhase) :=
      (fgSetup_of_dualStateInv h_anc hop_nz u v).grow_low hdrPhase (by decide)
    exact hout.trans (hlow.trans hp5)
  have hraw_ph_s :
      ((Memory.spec 0).clientState s_grow
        (userMutateRawProg ((base, opTag), (u.val, v_val)))).mem (base + hdrPhase) =
      s.mem (base + hdrPhase) := by
    rw [hraw_ww]; dsimp only [Memory.State.mem]
    rw [writeWords_apply_out _ (metaDst + 32) ws_pre (by dsimp only [hdrPhase]; omega),
      hraw_ph_anc, ← hsch.2 hdrPhase (by decide) (by decide), hp5]
  have hmid_eq_anc := syncLive_mem_eq_of_ne3_10 (v_val := v_val) h_anc hop_nz u v hv_eq
    (by rw [hp5]; decide) (by rw [hp5]; decide) (hraw_ph_anc.trans hp5.symm)
  have hmid_eq_s := syncLive_mem_eq_of_ne3_10 (v_val := v_val) h_s hop_nz u v hv_eq
    (by rw [← hsch.2 hdrPhase (by decide) (by decide), hp5]; decide)
    (by rw [← hsch.2 hdrPhase (by decide) (by decide), hp5]; decide)
    (by rw [← hkg_eq]; exact hraw_ph_s)
  dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hmid_eq_anc hmid_eq_s
  rw [← hkg_eq] at hmid_eq_s
  set s_mid_anc :=
    (Memory.spec 0).clientState s_grow_anc (userMutateProg ((base, opTag), (u.val, v_val)))
  set s_mid :=
    (Memory.spec 0).clientState s_grow (userMutateProg ((base, opTag), (u.val, v_val)))
  change s_mid_anc = _ at hmid_eq_anc
  change s_mid = _ at hmid_eq_s
  have hmid_ww :
      s_mid = { mem := writeWords s_mid_anc.mem (metaDst + 32) ws_pre
                frontier := s_mid_anc.frontier } := by
    rw [hmid_eq_s, hmid_eq_anc, hraw_ww]
    dsimp only [Memory.State.mem, Memory.State.frontier]
    congr 1
    rw [update_writeWords_out _ (metaDst + 32) k_pre (base + hdrLive) _ ws_pre
        (by dsimp only [hdrLive]; omega),
      update_writeWords_out _ (metaDst + 32) k_pre (base + hdrPBase0 + 60) _ ws_pre
        (by dsimp only [hdrPBase0]; omega),
      update_writeWords_out _ (metaDst + 32) k_pre (base + hdrPBase1 + 60) _ ws_pre
        (by dsimp only [hdrPBase1]; omega)]
  have hm_sp_anc := stepOpProg_mutate_spec h_anc hop_nz u v hv_eq hsucc_fits' hpad_fits'
  have hm_sp_s := stepOpProg_mutate_spec h_s hop_nz u v hv_eq hsucc_fits' hpad_s
  dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hm_sp_anc hm_sp_s
  rw [← hkg_eq] at hm_sp_s
  have hmid_ph_anc : s_mid_anc.mem (base + hdrPhase) = 5 := by
    rw [hmid_eq_anc]; dsimp only [Memory.State.mem]
    rw [Function.update_of_ne (by dsimp only [hdrPBase1, hdrPhase]; omega),
      Function.update_of_ne (by dsimp only [hdrPBase0, hdrPhase]; omega),
      Function.update_of_ne (by dsimp only [hdrLive, hdrPhase]; omega)]
    exact hraw_ph_anc
  have hmid_ph_s : s_mid.mem (base + hdrPhase) = 5 := by
    rw [hmid_ww]; dsimp only [Memory.State.mem]
    rw [writeWords_apply_out _ (metaDst + 32) ws_pre (by dsimp only [hdrPhase]; omega)]
    exact hmid_ph_anc
  set s_tick_anc :=
    (Memory.spec 0).clientState s_grow_anc
      (stepOpProg (((base, s_grow_anc.frontier), opTag), (u.val, v_val)))
  set s_tick :=
    (Memory.spec 0).clientState s_grow
      (stepOpProg (((base, s_grow.frontier), opTag), (u.val, v_val)))
  have htick_ww :
      s_tick = { mem := writeWords s_tick_anc.mem (metaDst + 32) ws_pre
                 frontier := s_tick_anc.frontier } := by
    have hso_a := (stepOpProg_eval base s_grow_anc.frontier opTag u.val v_val s_grow_anc).1
    have hso_s := (stepOpProg_eval base s_grow.frontier opTag u.val v_val s_grow).1
    rw [ite_eq_right hop_nz] at hso_a hso_s
    have hbg_a := (bgTickProg_eval base s_grow_anc.frontier s_mid_anc).1
    have hbg_s := (bgTickProg_eval base s_grow.frontier s_mid).1
    dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hbg_a hbg_s
    simp only [hmid_ph_anc, hmid_ph_s, Nat.reduceEqDiff, ↓reduceIte] at hbg_a hbg_s
    have hrp_a := (tickRandPrepProg_eval base s_mid_anc).1
    have hrp_s := (tickRandPrepProg_eval base s_mid).1
    dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hrp_a hrp_s
    have hst_m_eq : s_mid.mem (base + hdrStage) = s_mid_anc.mem (base + hdrStage) := by
      rw [hmid_ww]
      exact writeWords_apply_out _ (metaDst + 32) ws_pre (by dsimp only [hdrStage]; omega)
    have hpD_eq :
        s_mid.mem ((if s_mid.mem (base + hdrStage) = 0 then base + hdrPBase1
          else base + hdrPBase0) + 31) =
        s_mid_anc.mem ((if s_mid_anc.mem (base + hdrStage) = 0 then base + hdrPBase1
          else base + hdrPBase0) + 31) := by
      rw [hst_m_eq, hmid_ww]
      exact writeWords_apply_out _ (metaDst + 32) ws_pre
        (by dsimp only [hdrPBase0, hdrPBase1]; split_ifs <;> omega)
    have hc_eq : s_mid.mem (base + hdrCur) = s_mid_anc.mem (base + hdrCur) := by
      rw [hmid_ww]
      exact writeWords_apply_out _ (metaDst + 32) ws_pre (by dsimp only [hdrCur]; omega)
    dsimp only [s_tick, s_tick_anc]
    rw [hso_s, hbg_s, hrp_s, hso_a, hbg_a, hrp_a, hpD_eq, hc_eq, hmid_ww]
    dsimp only [Memory.State.mem, Memory.State.frontier]
    congr 1
    exact update_writeWords_out s_mid_anc.mem (metaDst + 32) k_pre (base + hdrCur) _ ws_pre
      (by dsimp only [hdrCur]; omega)
  have htick_hdr : ∀ off < 48, off ≠ hdrCur →
      s_tick_anc.mem (base + off) = s_mid_anc.mem (base + off) := by
    intro off _ hne
    dsimp only [s_tick_anc]
    rw [(stepOpProg_eval base s_grow_anc.frontier opTag u.val v_val s_grow_anc).1,
      ite_eq_right hop_nz, (bgTickProg_eval base s_grow_anc.frontier s_mid_anc).1]
    simp only [hmid_ph_anc, Nat.reduceEqDiff, ↓reduceIte]
    rw [(tickRandPrepProg_eval base s_mid_anc).1]
    exact Function.update_of_ne (base_add_ne hne) _ _
  -- Extract `DualPostTickInv` on both `s_tick_anc` and `s_tick`
  have hpt_anc := hm_sp_anc.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2
  have hpt_s := hm_sp_s.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2
  change (if s_mid_anc.mem (base + hdrPhase) ≠ 5 then _ else _) at hpt_anc
  change (if s_mid.mem (base + hdrPhase) ≠ 5 then _ else _) at hpt_s
  rw [ite_eq_right (not_not.mpr hmid_ph_anc)] at hpt_anc
  rw [ite_eq_right (not_not.mpr hmid_ph_s)] at hpt_s
  dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hpt_anc hpt_s
  have hstep_anc := fgStep_le7_aux h_anc u v hv_eq
    (fgSetup_of_dualStateInv h_anc hop_nz u v) rfl rfl rfl (by rw [hp5]; decide)
  have hcur_m_anc : s_mid_anc.mem (base + hdrCur) = cur :=
    hstep_anc.2.2.2.1 (base + hdrCur) (by dsimp only [hdrCur]; omega)
      (base_add_ne (by decide)) (base_add_ne (by decide))
  have hnD_m_anc : s_mid_anc.mem (base + hdrNDst) = nDst :=
    hstep_anc.2.2.2.1 (base + hdrNDst) (by dsimp only [hdrNDst]; omega)
      (base_add_ne (by decide)) (base_add_ne (by decide))
  have hst_m_anc : s_mid_anc.mem (base + hdrStage) = s_anc.mem (base + hdrStage) :=
    hstep_anc.2.2.2.1 (base + hdrStage) (by dsimp only [hdrStage]; omega)
      (base_add_ne (by decide)) (base_add_ne (by decide))
  have hpad_m_anc : s_mid_anc.mem (base + hdrPad) = s_anc.mem (base + hdrPad) :=
    hstep_anc.2.2.2.1 (base + hdrPad) (by dsimp only [hdrPad]; omega)
      (base_add_ne (by decide)) (base_add_ne (by decide))
  have hmbD_m_anc : dualMbDst base s_mid_anc.mem = metaDst := by
    unfold dualMbDst; rw [hmid_ph_anc, hnD_m_anc, hst_m_anc, hpad_m_anc, ← hp5]
  have hpD_m_anc : dualPDst base s_mid_anc.mem = dualPDst base s_anc.mem := by
    unfold dualPDst; rw [hmid_ph_anc, hst_m_anc, ← hp5]
  have hcur_m_s : s_mid.mem (base + hdrCur) = cur := by
    rw [hmid_ww]
    exact (writeWords_apply_out _ (metaDst + 32) ws_pre
      (by dsimp only [hdrCur]; omega)).trans hcur_m_anc
  have hnD_m_s : s_mid.mem (base + hdrNDst) = nDst := by
    rw [hmid_ww]
    exact (writeWords_apply_out _ (metaDst + 32) ws_pre
      (by dsimp only [hdrNDst]; omega)).trans hnD_m_anc
  have hmbD_m_s : dualMbDst base s_mid.mem = metaDst := by
    unfold dualMbDst
    rw [hmid_ph_s, hnD_m_s]
    have hst_s : s_mid.mem (base + hdrStage) = s_mid_anc.mem (base + hdrStage) := by
      rw [hmid_ww]
      exact writeWords_apply_out _ (metaDst + 32) ws_pre (by dsimp only [hdrStage]; omega)
    have hpad_s2 : s_mid.mem (base + hdrPad) = s_mid_anc.mem (base + hdrPad) := by
      rw [hmid_ww]
      exact writeWords_apply_out _ (metaDst + 32) ws_pre (by dsimp only [hdrPad]; omega)
    rw [hst_s, hpad_s2, ← hmid_ph_anc, ← hnD_m_anc]
    exact hmbD_m_anc
  have hpD_m_s : dualPDst base s_mid.mem = dualPDst base s_anc.mem := by
    unfold dualPDst
    have hst_s : s_mid.mem (base + hdrStage) = s_mid_anc.mem (base + hdrStage) := by
      rw [hmid_ww]
      exact writeWords_apply_out _ (metaDst + 32) ws_pre (by dsimp only [hdrStage]; omega)
    rw [hmid_ph_s, hst_s, hst_m_anc, ← hp5]
  have hcur_ma' : ((Memory.spec 0).clientState
      { mem := ((Memory.spec 0).clientState s_anc
          (prepGrowProg (((base, s_anc.frontier), opTag), u.val))).mem
        frontier := s_anc.frontier +
          (Memory.spec 0).clientResult s_anc
            (prepGrowProg (((base, s_anc.frontier), opTag), u.val)) }
      (userMutateProg ((base, opTag), (u.val, v_val)))).mem (base + hdrCur) = cur := hcur_m_anc
  have hnD_ma' : ((Memory.spec 0).clientState
      { mem := ((Memory.spec 0).clientState s_anc
          (prepGrowProg (((base, s_anc.frontier), opTag), u.val))).mem
        frontier := s_anc.frontier +
          (Memory.spec 0).clientResult s_anc
            (prepGrowProg (((base, s_anc.frontier), opTag), u.val)) }
      (userMutateProg ((base, opTag), (u.val, v_val)))).mem (base + hdrNDst) = nDst := hnD_m_anc
  have hmbD_ma' : dualMbDst base ((Memory.spec 0).clientState
      { mem := ((Memory.spec 0).clientState s_anc
          (prepGrowProg (((base, s_anc.frontier), opTag), u.val))).mem
        frontier := s_anc.frontier +
          (Memory.spec 0).clientResult s_anc
            (prepGrowProg (((base, s_anc.frontier), opTag), u.val)) }
      (userMutateProg ((base, opTag), (u.val, v_val)))).mem = metaDst := hmbD_m_anc
  have hpD_ma' : dualPDst base ((Memory.spec 0).clientState
      { mem := ((Memory.spec 0).clientState s_anc
          (prepGrowProg (((base, s_anc.frontier), opTag), u.val))).mem
        frontier := s_anc.frontier +
          (Memory.spec 0).clientResult s_anc
            (prepGrowProg (((base, s_anc.frontier), opTag), u.val)) }
      (userMutateProg ((base, opTag), (u.val, v_val)))).mem = dualPDst base s_anc.mem := hpD_m_anc
  have hcur_ms' : ((Memory.spec 0).clientState
      { mem := ((Memory.spec 0).clientState s
          (prepGrowProg (((base, s.frontier), opTag), u.val))).mem
        frontier := s.frontier + k_grow }
      (userMutateProg ((base, opTag), (u.val, v_val)))).mem (base + hdrCur) = cur := hcur_m_s
  have hnD_ms' : ((Memory.spec 0).clientState
      { mem := ((Memory.spec 0).clientState s
          (prepGrowProg (((base, s.frontier), opTag), u.val))).mem
        frontier := s.frontier + k_grow }
      (userMutateProg ((base, opTag), (u.val, v_val)))).mem (base + hdrNDst) = nDst := hnD_m_s
  have hmbD_ms' : dualMbDst base ((Memory.spec 0).clientState
      { mem := ((Memory.spec 0).clientState s
          (prepGrowProg (((base, s.frontier), opTag), u.val))).mem
        frontier := s.frontier + k_grow }
      (userMutateProg ((base, opTag), (u.val, v_val)))).mem = metaDst := hmbD_m_s
  have hpD_ms' : dualPDst base ((Memory.spec 0).clientState
      { mem := ((Memory.spec 0).clientState s
          (prepGrowProg (((base, s.frontier), opTag), u.val))).mem
        frontier := s.frontier + k_grow }
      (userMutateProg ((base, opTag), (u.val, v_val)))).mem = dualPDst base s_anc.mem := hpD_m_s
  rw [hcur_ma', hnD_ma', hmbD_ma', hpD_ma'] at hpt_anc
  rw [hcur_ms', hnD_ms', hmbD_ms', hpD_ms'] at hpt_s
  have hw_of_pre_le10 : ∀ {st : Memory.State} {L : DualLatent c U V},
      DualPreShrinkInv c U V w base
        (if opTag = 1 then Function.update s_dict u (some v.val)
         else Function.update s_dict u none) L st →
      3 ≤ st.mem (base + hdrPhase) → st.mem (base + hdrPhase) ≤ 10 →
      st.mem (base + hdrW) = w := by
    intro st L hp h3 h10
    have hbr := hp.2.2.2
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h10] at hbr
    exact hbr.2.2.hdr.2.2.1
  refine ⟨hd_pos, fun ws_batch => ?_⟩
  let ws_zero : Fin (endOff - cur) → Fin (2 ^ w) := fun _ => wordOfNat w 0
  have hr_anc := hpt_anc.2.2.2.2.2.2.2.2.2 ws_zero
  have hr_s := hpt_s.2.2.2.2.2.2.2.2.2 ws_batch
  obtain ⟨hksh_eq, hsch_post⟩ := hpost_sch5 hp5 ws_zero ws_batch
  dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier] at hksh_eq hsch_post
  rw [← hkg_eq] at hksh_eq hsch_post
  set s_r_anc : Memory.State :=
    { mem := writeWords s_tick_anc.mem (metaDst + cur) ws_zero, frontier := s_tick_anc.frontier }
  set s_r : Memory.State :=
    { mem := writeWords s_tick.mem (metaDst + cur) ws_batch, frontier := s_tick.frontier }
  change (Memory.spec 0).clientResult s_r_anc
      (postRandShrinkProg ((base, s_r_anc.frontier), opTag)) =
    (Memory.spec 0).clientResult s_r (postRandShrinkProg ((base, s_r.frontier), opTag)) at hksh_eq
  -- Relate `s_r.mem` to `writeWords s_tick_anc.mem (metaDst + 32) (finAppendWords ws_pre ws_batch)`
  have hadd_cur : (metaDst + 32) + k_pre = metaDst + cur := by omega
  have hsr_mem_eq :
      writeWords s_tick.mem (metaDst + cur) ws_batch =
        writeWords s_tick_anc.mem (metaDst + 32) (finAppendWords ws_pre ws_batch) := by
    rw [htick_ww]; dsimp only [Memory.State.mem]
    rw [← hadd_cur, writeWords_writeWords_eq_finAppendWords]
  have hsr_mem_over_anc :
      writeWords s_tick.mem (metaDst + cur) ws_batch =
        writeWords (writeWords s_tick_anc.mem (metaDst + cur) ws_zero)
          (metaDst + 32) (finAppendWords ws_pre ws_batch) := by
    rw [hsr_mem_eq]
    funext addr
    by_cases hin : metaDst + 32 ≤ addr ∧ addr < (metaDst + 32) + (k_pre + (endOff - cur))
    · have ha : addr = (metaDst + 32) + (addr - (metaDst + 32)) := by omega
      have hlt : addr - (metaDst + 32) < k_pre + (endOff - cur) := by omega
      rw [ha, writeWords_apply_in _ _ _ hlt, writeWords_apply_in _ _ _ hlt]
    · rw [writeWords_apply_out _ _ _ hin, writeWords_apply_out _ _ _ hin,
        writeWords_apply_out s_tick_anc.mem (metaDst + cur) ws_zero (by omega)]
  refine ⟨fun hlt => ?_, fun heq_bm => ?_⟩
  · -- `5 → 5` (`endOff < offBM`): `postRandShrinkProg` is read-only (`s_ps = s_r`)
    have hpre_anc := hr_anc.2.2.2.2.2.2.1 hlt
    have hpre_s := hr_s.2.2.2.2.2.2.1 hlt
    obtain ⟨_, _, _, _, _, _, L_pa, _, hinv_pa⟩ := postRandShrinkProg_spec_pre hop_nz hpre_anc
    have hp5_ra : s_r_anc.mem (base + hdrPhase) = 5 := hr_anc.2.2.1
    have hp5_rs : s_r.mem (base + hdrPhase) = 5 := hr_s.2.2.1
    have hst_ra : s_r_anc.mem (base + hdrStage) = s_mid_anc.mem (base + hdrStage) := hr_anc.2.2.2.1
    have hst_rs : s_r.mem (base + hdrStage) = s_mid.mem (base + hdrStage) := hr_s.2.2.2.1
    have hpD_ra : (if s_r_anc.mem (base + hdrStage) = 0 then base + hdrPBase1
        else base + hdrPBase0) = dualPDst base s_anc.mem := by
      rw [hst_ra, hst_m_anc]; unfold dualPDst; rw [hp5, ite_eq_left (by decide : 5 < 10)]
    have hpD_rs : (if s_r.mem (base + hdrStage) = 0 then base + hdrPBase1
        else base + hdrPBase0) = dualPDst base s_anc.mem := by
      have hst_ms : s_mid.mem (base + hdrStage) = s_mid_anc.mem (base + hdrStage) := by
        rw [hmid_ww]
        exact writeWords_apply_out _ (metaDst + 32) ws_pre (by dsimp only [hdrStage]; omega)
      rw [hst_rs, hst_ms, hst_m_anc]; unfold dualPDst; rw [hp5, ite_eq_left (by decide : 5 < 10)]
    have h31_ra : s_r_anc.mem (dualPDst base s_anc.mem + 31) = offBM := hr_anc.2.2.2.2.2.1
    have hcur_ra : s_r_anc.mem (base + hdrCur) = endOff := hr_anc.2.2.2.2.1
    have h31_rs : s_r.mem (dualPDst base s_anc.mem + 31) = offBM := hr_s.2.2.2.2.2.1
    have hcur_rs : s_r.mem (base + hdrCur) = endOff := hr_s.2.2.2.2.1
    have hnd_ra : ¬(s_r_anc.mem (base + hdrPhase) = 5 ∧
        s_r_anc.mem ((if s_r_anc.mem (base + hdrStage) = 0 then base + hdrPBase1
          else base + hdrPBase0) + 31) ≤ s_r_anc.mem (base + hdrCur)) := by
      rw [hpD_ra, h31_ra, hcur_ra]; intro ⟨_, hle⟩; exact not_le_of_gt hlt hle
    have hnd_rs : ¬(s_r.mem (base + hdrPhase) = 5 ∧
        s_r.mem ((if s_r.mem (base + hdrStage) = 0 then base + hdrPBase1
          else base + hdrPBase0) + 31) ≤ s_r.mem (base + hdrCur)) := by
      rw [hpD_rs, h31_rs, hcur_rs]; intro ⟨_, hle⟩; exact not_le_of_gt hlt hle
    have hw_ra : s_r_anc.mem (base + hdrW) = w :=
      hw_of_pre_le10 hpre_anc (by rw [hp5_ra]; decide) (by rw [hp5_ra]; decide)
    have hw_rs : s_r.mem (base + hdrW) = w :=
      hw_of_pre_le10 hpre_s (by rw [hp5_rs]; decide) (by rw [hp5_rs]; decide)
    have hps_a_eq : (Memory.spec 0).clientState s_r_anc
        (postRandShrinkProg ((base, s_r_anc.frontier), opTag)) = s_r_anc := by
      rw [(postRandShrinkProg_eval base s_r_anc.frontier opTag s_r_anc).1]
      dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier]
      rw [ite_eq_right hop_nz, ite_eq_right hnd_ra]
      rw [(calcPostShrinkProg_eval (curFr := s_r_anc.frontier) (hw_ra ▸ hw_pos)).1]
      dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier]
      rw [hp5_ra, ite_eq_right (fun h => absurd h.1 (by decide))]
    have hps_s_eq : (Memory.spec 0).clientState s_r
        (postRandShrinkProg ((base, s_r.frontier), opTag)) = s_r := by
      rw [(postRandShrinkProg_eval base s_r.frontier opTag s_r).1]
      dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier]
      rw [ite_eq_right hop_nz, ite_eq_right hnd_rs]
      rw [(calcPostShrinkProg_eval (curFr := s_r.frontier) (hw_rs ▸ hw_pos)).1]
      dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier]
      rw [hp5_rs, ite_eq_right (fun h => absurd h.1 (by decide))]
    set k_sh_a := (Memory.spec 0).clientResult s_r_anc
      (postRandShrinkProg ((base, s_r_anc.frontier), opTag))
    set s_post_anc : Memory.State :=
      { mem := clear ((Memory.spec 0).clientState s_r_anc
          (postRandShrinkProg ((base, s_r_anc.frontier), opTag))).mem
          (s_r_anc.frontier - k_sh_a) k_sh_a
        frontier := s_r_anc.frontier - k_sh_a }
    have hlow_pa : ∀ off < 48, s_post_anc.mem (base + off) = s_r_anc.mem (base + off) := by
      intro off hoff
      have hb192 : base + 192 ≤ s_r_anc.frontier - k_sh_a := hinv_pa.base_fr
      dsimp only [s_post_anc]
      rw [hps_a_eq, clear_of_not_owns (by simp only [Block.Owns]; omega)]
    have hp5_pa : s_post_anc.mem (base + hdrPhase) = 5 :=
      (hlow_pa hdrPhase (by decide)).trans hp5_ra
    have hcur_pa : s_post_anc.mem (base + hdrCur) = endOff :=
      (hlow_pa hdrCur (by decide)).trans hcur_ra
    have hnD_pa : s_post_anc.mem (base + hdrNDst) = nDst := by
      rw [hlow_pa hdrNDst (by decide)]
      dsimp only [s_r_anc]; rw [writeWords_apply_out _ _ _ (by dsimp only [hdrNDst]; omega)]
      exact (htick_hdr hdrNDst (by decide) (by decide)).trans hnD_m_anc
    have hpad_ra : s_r_anc.mem (base + hdrPad) = s_anc.mem (base + hdrPad) := by
      dsimp only [s_r_anc]; rw [writeWords_apply_out _ _ _ (by dsimp only [hdrPad]; omega)]
      exact (htick_hdr hdrPad (by decide) (by decide)).trans hpad_m_anc
    have hmbD_pa : dualMbDst base s_post_anc.mem = metaDst := by
      unfold dualMbDst
      rw [hp5_pa, hnD_pa, hlow_pa hdrStage (by decide), hlow_pa hdrPad (by decide),
        hst_ra, hst_m_anc, hpad_ra]
      unfold metaDst dualMbDst; rw [hp5]
    -- Bound `metaDst + endOff ≤ s_r_anc.frontier - k_sh_a`
    have hfr_post_ge : (metaDst + 32) + (k_pre + (endOff - cur)) ≤ s_r_anc.frontier - k_sh_a := by
      have hsched_pa := hinv_pa.sched; rw [ite_eq_right (by rw [hp5_pa]; decide)] at hsched_pa
      obtain ⟨hfr_hi, _⟩ := hsched_pa.ph3_10 ⟨by rw [hp5_pa]; decide, by rw [hp5_pa]; decide⟩
      obtain ⟨hmD_pa, _, _, _, hibHi_pa, _⟩ := hsched_pa.ge2 (by rw [hp5_pa]; decide)
      have hd_pa := (hinv_pa.ph5_inv hp5_pa).1
      have hth_pa := (hsched_pa.nDst_bounds.resolve_left hd_pa.ne').1
      have hbm_mD : offBktMeta c w (s_post_anc.mem (base + hdrNDst)) ≤
          s_post_anc.mem (base + hdrMDst) := by
        rw [hmD_pa]
        exact (epochMeta_offsets_le (w := w) hth_pa).2.2.1.trans
          (epochMeta_offsets_le (w := w) hth_pa).2.2.2
      rw [hnD_pa] at hbm_mD
      have hib_ge_md : metaDst + offBM ≤ s_post_anc.mem (base + hdrItemHi) := by
        rw [hibHi_pa, ite_eq_right (hnD_pa.symm ▸ hd_pos.ne'), ← hmbD_pa]
        unfold dualMbDst; rw [hp5_pa, ite_eq_left (by decide : 5 < 10), ite_eq_right hd_pa.ne']
        split_ifs <;> omega
      have hfr_hi' : s_post_anc.mem (base + hdrItemHi) ≤ s_r_anc.frontier - k_sh_a :=
        le_trans (Nat.le_add_right _ _) hfr_hi
      have hmin_le : min bulkBatchWhp (offBM - cur) ≤ offBM - cur := min_le_right _ _
      omega
    refine ⟨hp5_pa, hp5_pa, ?_, ?_, ?_⟩
    · clear *- hcur_pa hcur_pre
      dsimp only [endOff, offBM, nDst, cur] at hcur_pa ⊢
      omega
    · rw [hnD_pa]
      have hmin_le : min bulkBatchWhp (offBM - cur) ≤ offBM - cur := min_le_right _ _
      dsimp only [endOff, offBM, nDst, cur] at hpre_le_bm hmin_le ⊢
      clear *- hcur_pre hpre_le_bm hmin_le
      omega
    · change ({
          mem := clear ((Memory.spec 0).clientState s_r
            (postRandShrinkProg ((base, s_r.frontier), opTag))).mem
            (s_r.frontier - (Memory.spec 0).clientResult s_r
              (postRandShrinkProg ((base, s_r.frontier), opTag)))
            ((Memory.spec 0).clientResult s_r
              (postRandShrinkProg ((base, s_r.frontier), opTag)))
          frontier := s_r.frontier - (Memory.spec 0).clientResult s_r
            (postRandShrinkProg ((base, s_r.frontier), opTag)) } : Memory.State) = _
      rw [hps_s_eq, ← hksh_eq]
      have hfr_r_eq : s_r.frontier = s_r_anc.frontier := by
        dsimp only [s_r, s_r_anc]; rw [htick_ww]
      rw [hfr_r_eq, hmbD_pa]
      dsimp only [s_post_anc]
      rw [hps_a_eq]
      congr 1
      dsimp only [s_r, s_r_anc]
      rw [hsr_mem_over_anc]
      exact clear_writeWords_above _ (metaDst + 32) (k_pre + (endOff - cur))
        (s_r_anc.frontier - k_sh_a) k_sh_a (finAppendWords ws_pre ws_batch) hfr_post_ge
  · -- `5 → 6` (`endOff = offBM`): runs `finishRandFillProg`, enters `Coupled67` with `seedsOfWords`
    have heq_bm' : endOff = offBM := heq_bm
    have hmid_ra := hr_anc.2.2.2.2.2.2.2 heq_bm
    have hmid_rs := hr_s.2.2.2.2.2.2.2 heq_bm
    have hp5_ra0 : s_r_anc.mem (base + hdrPhase) = 5 := hr_anc.2.2.1
    have hp5_rs0 : s_r.mem (base + hdrPhase) = 5 := hr_s.2.2.1
    have hst_ra0 : s_r_anc.mem (base + hdrStage) = s_mid_anc.mem (base + hdrStage) :=
      hr_anc.2.2.2.1
    have hst_rs0 : s_r.mem (base + hdrStage) = s_mid.mem (base + hdrStage) := hr_s.2.2.2.1
    have h31_ra0 : s_r_anc.mem (dualPDst base s_anc.mem + 31) = offBM := hr_anc.2.2.2.2.2.1
    have hcur_ra0 : s_r_anc.mem (base + hdrCur) = endOff := hr_anc.2.2.2.2.1
    have h31_rs0 : s_r.mem (dualPDst base s_anc.mem + 31) = offBM := hr_s.2.2.2.2.2.1
    have hcur_rs0 : s_r.mem (base + hdrCur) = endOff := hr_s.2.2.2.2.1
    have hpD_ra : dualPDst base s_r_anc.mem = dualPDst base s_mid_anc.mem := by
      unfold dualPDst
      rw [hp5_ra0, hmid_ph_anc, hst_ra0]
    have hpD_rs : dualPDst base s_r.mem = dualPDst base s_mid.mem := by
      unfold dualPDst
      rw [hp5_rs0, hmid_ph_s, hst_rs0]
    have hdone_ra : s_r_anc.mem (dualPDst base s_r_anc.mem + 31) ≤ s_r_anc.mem (base + hdrCur) := by
      rw [hpD_ra, hpD_m_anc, h31_ra0, hcur_ra0, heq_bm']
    have hdone_rs : s_r.mem (dualPDst base s_r.mem + 31) ≤ s_r.mem (base + hdrCur) := by
      rw [hpD_rs, hpD_m_s, h31_rs0, hcur_rs0, heq_bm']
    obtain ⟨_, _, _, _, _, _, hinv_pa⟩ :=
      postRandShrinkProg_spec hop_nz hmid_ra hp5_ra0 hdone_ra
    obtain ⟨_, _, _, _, _, _, hinv_ps⟩ := postRandShrinkProg_spec hop_nz hmid_rs hp5_rs0 hdone_rs
    -- Identify `nDst` and `metaDst` on `s_r`
    have hnD_rs : s_r.mem (base + hdrNDst) = nDst := by
      dsimp only [s_r]; rw [writeWords_apply_out _ _ _ (by dsimp only [hdrNDst]; omega)]
      rw [htick_ww]; dsimp only [Memory.State.mem]
      rw [writeWords_apply_out _ _ _ (by dsimp only [hdrNDst]; omega)]
      exact (htick_hdr hdrNDst (by decide) (by decide)).trans hnD_m_anc
    have hmbD_rs : dualMbDst base s_r.mem = metaDst := by
      unfold dualMbDst
      rw [hp5_rs0, hnD_rs, hst_rs0]
      have hst_ms : s_mid.mem (base + hdrStage) = s_anc.mem (base + hdrStage) := by
        rw [hmid_ww]
        exact (writeWords_apply_out _ _ _ (by dsimp only [hdrStage]; omega)).trans hst_m_anc
      have hpd_rs : s_r.mem (base + hdrPad) = s_anc.mem (base + hdrPad) := by
        dsimp only [s_r]; rw [writeWords_apply_out _ _ _ (by dsimp only [hdrPad]; omega)]
        rw [htick_ww]; dsimp only [Memory.State.mem]
        rw [writeWords_apply_out _ _ _ (by dsimp only [hdrPad]; omega)]
        exact (htick_hdr hdrPad (by decide) (by decide)).trans hpad_m_anc
      rw [hst_ms, hpd_rs]; unfold metaDst dualMbDst; rw [hp5]
    -- Rewrite `extractEpochSeeds` to `seedsOfWords` via `extractEpochSeeds_masked_writeWords_eq`
    have hsched_a := h_anc.sched; rw [ite_eq_right (by rw [hp5]; decide)] at hsched_a
    have hth_d : whpThreshold c ≤ nDst := (hsched_a.nDst_bounds.resolve_left hd_pos.ne').1
    have hlen_bm : k_pre + (endOff - cur) = offBM - 32 := by
      clear *- hcur_pre hpre_le_bm heq_bm'; omega
    let ws_bm : Fin (offBM - 32) → Fin (2 ^ w) :=
      fun i => (finAppendWords ws_pre ws_batch) (i.cast hlen_bm.symm)
    have hsr_ws_bm : s_r.mem = writeWords s_tick_anc.mem (metaDst + 32) ws_bm := by
      dsimp only [s_r]; rw [hsr_mem_eq]
      funext addr
      by_cases hin : metaDst + 32 ≤ addr ∧ addr < (metaDst + 32) + (offBM - 32)
      · have ha : addr = (metaDst + 32) + (addr - (metaDst + 32)) := by clear *- hin; omega
        have hlt1 : addr - (metaDst + 32) < k_pre + (endOff - cur) := by
          dsimp only [endOff, offBM, nDst, cur] at hin hlen_bm ⊢
          clear *- hin hlen_bm; omega
        have hlt2 : addr - (metaDst + 32) < offBM - 32 := by clear *- hin; omega
        rw [ha, writeWords_apply_in _ _ _ hlt1, writeWords_apply_in _ _ _ hlt2]
        rfl
      · have hout1 : ¬(metaDst + 32 ≤ addr ∧ addr < (metaDst + 32) + (k_pre + (endOff - cur))) := by
          dsimp only [endOff, offBM, nDst, cur] at hin hlen_bm ⊢
          clear *- hin hlen_bm; omega
        rw [writeWords_apply_out _ _ _ hout1, writeWords_apply_out _ _ _ hin]
    have hseeds_eq :
        extractEpochSeeds c U w nDst metaDst
          (Function.update
            (Function.update s_r.mem (metaDst + 32)
              (s_r.mem (metaDst + 32) &&& (2 ^ (redWidthWhp U - 1) - 1)))
            (metaDst + offFpHash c w nDst)
            (s_r.mem (metaDst + offFpHash c w nDst) &&& (2 ^ (redWidthWhp U - 1) - 1))) =
        seedsOfWords c U w nDst
          (fun i => (finAppendWords ws_pre ws_batch)
            (i.cast (by rw [ite_eq_right hd_pos.ne']; exact hlen_bm.symm))) := by
      rw [hsr_ws_bm]
      exact extractEpochSeeds_masked_writeWords_eq hw_pos hth_d s_tick_anc.mem ws_bm
    have hL_eq :
        ({ slotSrc := (L_s.applyFG (s.mem (base + hdrPhase)) opTag u v).slotSrc
           slotDst := ⟨s_r.mem (base + hdrNDst), fun _ => none,
             extractEpochSeeds c U w (s_r.mem (base + hdrNDst)) (dualMbDst base s_r.mem)
               (Function.update
                 (Function.update s_r.mem (dualMbDst base s_r.mem + 32)
                   (s_r.mem (dualMbDst base s_r.mem + 32) &&& (2 ^ (redWidthWhp U - 1) - 1)))
                 (dualMbDst base s_r.mem + offFpHash c w (s_r.mem (base + hdrNDst)))
                 (s_r.mem (dualMbDst base s_r.mem + offFpHash c w (s_r.mem (base + hdrNDst))) &&&
                   (2 ^ (redWidthWhp U - 1) - 1))), []⟩
           nTrig := (L_s.applyFG (s.mem (base + hdrPhase)) opTag u v).nTrig
           trigOps := (L_s.applyFG (s.mem (base + hdrPhase)) opTag u v).trigOps
           elapsed := (L_s.applyFG (s.mem (base + hdrPhase)) opTag u v).elapsed + 1
           unpermBound := (L_s.applyFG (s.mem (base + hdrPhase)) opTag u v).unpermBound } :
          DualLatent c U V) =
        { (L_s.applyFG 5 opTag u v) with
          slotDst := ⟨nDst, fun _ => none,
            seedsOfWords c U w nDst
              (fun i => (finAppendWords ws_pre ws_batch)
                (i.cast (by rw [ite_eq_right hd_pos.ne']; exact hlen_bm.symm))), []⟩
          elapsed := L_s.elapsed + 1 } := by
      have hph_s5 : s.mem (base + hdrPhase) = 5 :=
        (hsch.2 hdrPhase (by decide) (by decide)).symm.trans hp5
      rw [hph_s5, hmbD_rs]
      have hnD_eq : s_r.mem (base + hdrNDst) = nDst := hnD_rs
      generalize s_r.mem (base + hdrNDst) = nD_val at hnD_eq ⊢
      subst hnD_eq
      rw [hseeds_eq]
      rfl
    rw [hL_eq] at hinv_ps
    -- Prove `s_post_anc.mem (base + hdrPhase) = 6` and `Coupled67 c w base s_post_anc s_post`
    obtain ⟨hpre_rf_a, hfr_rf_a, _, _, _, hpre_sh_a⟩ :=
      finishRandFillProg_spec hmid_ra hp5_ra0 hdone_ra
    obtain ⟨hpre_rf_s, hfr_rf_s, _, _, _, hpre_sh_s⟩ :=
      finishRandFillProg_spec hmid_rs hp5_rs0 hdone_rs
    set s_rf_a := (Memory.spec 0).clientState s_r_anc (finishRandFillProg base)
    set s_rf_s := (Memory.spec 0).clientState s_r (finishRandFillProg base)
    have hph_rfa : s_rf_a.mem (base + hdrPhase) = 6 := by
      dsimp only [s_rf_a]
      rw [(finishRandFillProg_eval base s_r_anc).1]; exact Function.update_self ..
    have hph_rfs : s_rf_s.mem (base + hdrPhase) = 6 := by
      dsimp only [s_rf_s]
      rw [(finishRandFillProg_eval base s_r).1]; exact Function.update_self ..
    have hdone_if_a : s_r_anc.mem ((if s_r_anc.mem (base + hdrStage) = 0 then base + hdrPBase1
        else base + hdrPBase0) + 31) ≤ s_r_anc.mem (base + hdrCur) := by
      have hp5_ra : s_r_anc.mem (base + hdrPhase) = 5 := hr_anc.2.2.1
      have hpD :
          (if s_r_anc.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0) =
          dualPDst base s_r_anc.mem := by
        unfold dualPDst; rw [hp5_ra, ite_eq_left (by decide : 5 < 10)]
      rw [hpD]; exact hdone_ra
    have hdone_if_s : s_r.mem ((if s_r.mem (base + hdrStage) = 0 then base + hdrPBase1
        else base + hdrPBase0) + 31) ≤ s_r.mem (base + hdrCur) := by
      have hp5_rs : s_r.mem (base + hdrPhase) = 5 := hr_s.2.2.1
      have hpD : (if s_r.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0) =
          dualPDst base s_r.mem := by
        unfold dualPDst; rw [hp5_rs, ite_eq_left (by decide : 5 < 10)]
      rw [hpD]; exact hdone_rs
    have hps_a_rf : (Memory.spec 0).clientState s_r_anc
        (postRandShrinkProg ((base, s_r_anc.frontier), opTag)) = s_rf_a := by
      have hp5_ra : s_r_anc.mem (base + hdrPhase) = 5 := hr_anc.2.2.1
      have hw_rfa : s_rf_a.mem (base + hdrW) = w :=
        hw_of_pre_le10 hpre_sh_a (by rw [hph_rfa]; decide) (by rw [hph_rfa]; decide)
      rw [(postRandShrinkProg_eval base s_r_anc.frontier opTag s_r_anc).1]
      dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier]
      rw [ite_eq_right hop_nz, ite_eq_left ⟨hp5_ra, hdone_if_a⟩]
      rw [(calcPostShrinkProg_eval (curFr := s_r_anc.frontier) (hw_rfa ▸ hw_pos)).1]
      dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier]
      rw [hph_rfa, ite_eq_right (fun h => absurd h.1 (by decide))]
    have hps_s_rf : (Memory.spec 0).clientState s_r
        (postRandShrinkProg ((base, s_r.frontier), opTag)) = s_rf_s := by
      have hp5_rs : s_r.mem (base + hdrPhase) = 5 := hr_s.2.2.1
      have hw_rfs : s_rf_s.mem (base + hdrW) = w :=
        hw_of_pre_le10 hpre_sh_s (by rw [hph_rfs]; decide) (by rw [hph_rfs]; decide)
      rw [(postRandShrinkProg_eval base s_r.frontier opTag s_r).1]
      dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier]
      rw [ite_eq_right hop_nz, ite_eq_left ⟨hp5_rs, hdone_if_s⟩]
      rw [(calcPostShrinkProg_eval (curFr := s_r.frontier) (hw_rfs ▸ hw_pos)).1]
      dsimp -failIfUnchanged only [Memory.State.mem, Memory.State.frontier]
      rw [hph_rfs, ite_eq_right (fun h => absurd h.1 (by decide))]
    set k_sh_a := (Memory.spec 0).clientResult s_r_anc
      (postRandShrinkProg ((base, s_r_anc.frontier), opTag))
    set s_post_anc : Memory.State :=
      { mem := clear ((Memory.spec 0).clientState s_r_anc
          (postRandShrinkProg ((base, s_r_anc.frontier), opTag))).mem
          (s_r_anc.frontier - k_sh_a) k_sh_a
        frontier := s_r_anc.frontier - k_sh_a }
    have hp6_pa : s_post_anc.mem (base + hdrPhase) = 6 := by
      have hb192 : base + 192 ≤ s_r_anc.frontier - k_sh_a := hinv_pa.base_fr
      dsimp only [s_post_anc]
      rw [hps_a_rf, clear_of_not_owns (by simp only [Block.Owns]; dsimp only [hdrPhase]; omega)]
      exact hph_rfa
    -- Show `s_rf_a.mem` and `s_rf_s.mem` agree outside `[metaDst, metaDst + offPageDir c w nDst)`
    have hmd_192 : base + 192 ≤ metaDst := by
      unfold metaDst dualMbDst
      rw [hp5, ite_eq_left (by decide : 5 < 10), ite_eq_right hd_pos.ne']
      split_ifs <;> (clear *-; omega)
    have hod_ge_bm : offBktMeta c w nDst ≤ offPageDir c w nDst :=
      (epochMeta_offsets_le (w := w) hth_d).2.2.1
    obtain ⟨hrf_out, hrf_s_hdr⟩ :=
      finishRandFill_agree_outside hd_pos hth_d hmd_192 hmid_ra hmid_rs
        hr_anc.2.2.1 hr_s.2.2.1 hnD_rs hmbD_rs hpre_rf_a hpre_rf_s fun b hnb => by
          have hnot_bm : ¬(metaDst + 32 ≤ b ∧ b < (metaDst + 32) + (k_pre + (endOff - cur))) := by
            intro ⟨h1, h2⟩
            apply hnb
            dsimp only [endOff, offBM, nDst, cur] at hlen_bm hod_ge_bm h1 h2 ⊢
            clear *- hlen_bm hod_ge_bm h1 h2
            exact ⟨by omega, by omega⟩
          dsimp only [s_r_anc, s_r]
          rw [hsr_mem_over_anc, writeWords_apply_out _ _ _ hnot_bm]
    refine ⟨hp6_pa, ⟨hsch_post, fun addr hreg => ?_⟩, hinv_ps⟩
    have hlow_pa : ∀ off < 48, off ≠ hdrPhase → off ≠ hdrCur →
        s_post_anc.mem (base + off) = s_r.mem (base + off) := by
      intro off hoff hne_p hne_c
      have hb192 : base + 192 ≤ s_r_anc.frontier - k_sh_a := hinv_pa.base_fr
      dsimp only [s_post_anc]
      rw [hps_a_rf, clear_of_not_owns (by simp only [Block.Owns]; clear *- hoff hb192; omega),
        hrf_out (base + off) (by clear *- hoff hmd_192; omega),
        hrf_s_hdr off hoff hne_p hne_c]
    have hnD_pa : s_post_anc.mem (base + hdrNDst) = nDst :=
      (hlow_pa hdrNDst (by decide) (by decide) (by decide)).trans hnD_rs
    have hmbD_pa : dualMbDst base s_post_anc.mem = metaDst := by
      have hp5_rs : s_r.mem (base + hdrPhase) = 5 := hr_s.2.2.1
      have hmb5 := hmbD_rs
      unfold dualMbDst at hmb5 ⊢
      rw [hp5_rs, ite_eq_left (by decide : 5 < 10)] at hmb5
      rw [hp6_pa, ite_eq_left (by decide : 6 < 10), hnD_pa,
        hlow_pa hdrStage (by decide) (by decide) (by decide),
        hlow_pa hdrPad (by decide) (by decide) (by decide), ← hnD_rs]
      exact hmb5
    have hnot_m : ¬(metaDst ≤ addr ∧ addr < metaDst + offPageDir c w nDst) := by
      have h3 := hreg.2.2
      rw [hmbD_pa, hnD_pa] at h3
      exact fun h => h3 ⟨hd_pos.ne', h⟩
    change s_post_anc.mem addr =
      clear ((Memory.spec 0).clientState s_r
        (postRandShrinkProg ((base, s_r.frontier), opTag))).mem
        (s_r.frontier - (Memory.spec 0).clientResult s_r
          (postRandShrinkProg ((base, s_r.frontier), opTag)))
        ((Memory.spec 0).clientResult s_r
          (postRandShrinkProg ((base, s_r.frontier), opTag))) addr
    dsimp only [s_post_anc]
    rw [hps_a_rf, hps_s_rf, ← hksh_eq]
    have hfr_r_eq : s_r.frontier = s_r_anc.frontier := by
      dsimp only [s_r, s_r_anc]; rw [htick_ww]
    rw [hfr_r_eq]
    by_cases hown : (Block.mk (s_r_anc.frontier - k_sh_a) k_sh_a).Owns addr
    · rw [clear_of_owns hown, clear_of_owns hown]
    · rw [clear_of_not_owns hown, clear_of_not_owns hown]
      exact hrf_out addr hnot_m

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
