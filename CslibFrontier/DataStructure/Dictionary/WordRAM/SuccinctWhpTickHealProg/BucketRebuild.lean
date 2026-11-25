/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpTickHealProg.HealRt
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.Tactic.Realize

/-!
# Per-Bucket SWAR B+-Tree Slice Reconstruction for `csrToFastGenProg`

This internal module implements Phase E2 of `csrToFastGenProg`:
* **`readHealSlotQuotProg`**: reads the Feistel quotient of local coordinate `(b, loc)` from either
  front-yard `offQuotWhp[b * cf + loc]` or backyard `offQuotWhp[M * cf + offBackPtr[b * cb + k]]`.
* **`buildBktSliceLoopProg`**: inserts `cnt` fingerprinted coordinates `(fp, loc)` into live slice
  `3 * b` using candidate salt `offBktMeta[16 * b + 1]`.
* **`buildAllBucketsOuterLoopProg`**: reconstructs live slices `3 * b` across all `b < M` while
  leaving auxiliary slices `3 * b + 1, 3 * b + 2` at `zeroBTreeSlice`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.readHealSlotQuotProg`,
  `buildBktSliceLoopProg`, `buildAllBucketsOuterLoopProg`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_buildAllBucketsOuterLoop`,
  `buildAllBucketsOuterLoop_safe`, `buildAllBucketsOuterLoop_spec`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind clientResult_bind)
open Cslib.DataStructure.WordRAM
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

private theorem fpOfQuot_lt_two_pow {c U n_max : ℕ} (θ : SeedWhp c U n_max) (salt kv : ℕ) :
    (if hs : salt < sMaxWhp c n_max then
       if hu : kv < U then fpHash c U n_max θ.2 ⟨salt, hs⟩ ⟨kv, hu⟩ else 0
     else 0) < 2 ^ fpBitsWhp n_max := by
  split_ifs with hs hu
  · exact fpHash_lt c U n_max θ.2 ⟨salt, hs⟩ ⟨kv, hu⟩
  · exact Nat.two_pow_pos _
  · exact Nat.two_pow_pos _

/-! ## Slot Quotient Reader (`readHealSlotQuotProg`) -/

/-- Read the quotient stored at local coordinate `(b, loc)` during `csrToFastGenProg`. -/
@[irreducible] def readHealSlotQuotProg :
    (HealRt × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog ℕ
  | ((rt, (offQ_in, qBits_in)), (b_in, loc_in)) => do
    let offQ ← pure offQ_in
    let qBits ← pure qBits_in
    let b ← pure b_in
    let loc ← pure loc_in
    let zero_v ← pure 0
    if loc < hlCF rt then
      let p ← pure (b * hlCF rt + loc)
      readPackedGenProg (((hlBase rt, offQ), (qBits, hlW rt)), p)
    else
      let k ← pure (loc - hlCF rt)
      if k < hlCB rt then
        let idxBp ← pure (b * hlCB rt + k)
        let bpVal ← readPackedGenProg (((hlBase rt, hlOffBp rt), (hlGBits rt, hlW rt)), idxBp)
        if bpVal < hlPoolSize rt then
          let ft ← pure (hlM rt * hlCF rt)
          let p ← pure (ft + bpVal)
          readPackedGenProg (((hlBase rt, offQ), (qBits, hlW rt)), p)
        else
          pure zero_v
      else
        pure zero_v

private def ReadHealSlotQuotPre (w : ℕ)
    (d : (HealRt × (ℕ × ℕ)) × (ℕ × ℕ)) (_s : Memory.State) : Prop :=
  ∃ c U V w₀ n_max,
    WhpLargeEnv c U V w₀ n_max w (hlBase d.1.1) ∧
    d.1.1 = mkHealRt c U V w₀ n_max (hlBase d.1.1) ∧
    d.1.2.1 = offQuotWhp c w₀ n_max ∧
    d.1.2.2 = quotBitsWhp U n_max ∧
    d.2.1 < numBucketsWhp n_max

private theorem realizes_readHealSlotQuot :
    Realizes .exact readHealSlotQuotProg
      (WordEncoding.encode (α := (HealRt × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      ReadHealSlotQuotPre
      (fun _ _ => 0) := by
  unfold readHealSlotQuotProg
  have hrp := realizes_readPackedGen
  have hcs : ∀ y s', (Memory.spec 0).clientState s' (readPackedGenProg y) = s' := fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨⟨rt, offQ, qBits⟩, b, loc⟩
    dsimp only [ReadHealSlotQuotPre] at h
    obtain ⟨c, U, V, w₀, n_max, henv, heq_rt, rfl, rfl, hb_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize hlBase rt = base at henv heq_rt
    subst heq_rt
    obtain ⟨_, _, hMcb, _, _, _, _, hgk⟩ := hl_bounds henv
    have hseg := WhpLargeEnv.seg_end_le c U V w n_max
    have hMcf_le : numBucketsWhp n_max * capFrontWhp n_max ≤ n_max :=
      (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans (Nat.mul_div_le _ _)
    have hMcf_ps : numBucketsWhp n_max * capFrontWhp n_max + poolSizeWhp n_max ≤ n_max := by
      unfold poolSizeWhp; omega
    have hqk : quotBitsWhp U n_max ≤ w :=
      (Nat.sub_le _ _).trans (keyBits_le_w henv.2.2.2.2.2.1)
    dsimp only [mkHealRt, hlBase, hlW, hlM, hlCF, hlCB, hlPoolSize, hlGBits, hlOffBp] at *
    simp only [hcs] at *
    first
    | omega
    | exact henv.fits_of_le_n_max (by omega)
    | (refine henv.fits_of_le_n_max ?_
       exact (mul_add_lt_mul_bound hb_lt (by assumption)).le.trans hMcf_le)
    | (refine henv.fits_of_le_n_max ?_
       exact (mul_add_lt_mul_bound hb_lt (by assumption)).le.trans hMcb)
    | (refine to_true_exists (henv.packed_safe_of_le hqk ?_ hseg.1)
       exact (mul_add_lt_mul_bound hb_lt (by assumption)).trans_le hMcf_le)
    | (refine to_true_exists (henv.packed_safe_of_le hgk ?_ hseg.2.2.2.2.2.2.1)
       exact mul_add_lt_mul_bound hb_lt (by assumption))
    | exact to_true_exists (henv.packed_safe_of_le hqk (by omega) hseg.1)
  )

private theorem readHealSlotQuotProg_spec {c U V w n_max base b loc : ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) :
    let rt := mkHealRt c U V w n_max base
    let prog := readHealSlotQuotProg ((rt, (offQuotWhp c w n_max, quotBitsWhp U n_max)), (b, loc))
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog < 2 ^ quotBitsWhp U n_max ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hw := henv.2.1
  have hseg := WhpLargeEnv.seg_end_le c U V w n_max
  have hq_b : base + offQuotWhp c w n_max +
      packedWords n_max (quotBitsWhp U n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.1 _
  have hbp_b : base + offBackPtr c U V w n_max +
      packedWords (numBucketsWhp n_max * capBackWhp n_max) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.2.2.1 _
  have hMcf_le : numBucketsWhp n_max * capFrontWhp n_max ≤ n_max :=
    (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans (Nat.mul_div_le _ _)
  dsimp only
  unfold readHealSlotQuotProg
  dsimp only [mkHealRt, hlBase, hlW, hlM, hlCF, hlCB, hlPoolSize, hlGBits, hlOffBp]
  simp only [pure_bind]
  by_cases hcf : loc < capFrontWhp n_max
  · simp only [hcf, ↓reduceIte]
    have hp_lt : b * capFrontWhp n_max + loc < n_max :=
      (mul_add_lt_mul_bound hb hcf).trans_le hMcf_le
    have hst := StepSpec.readPackedGen (s := s) hw hp_lt hq_b
    exact ⟨hst.1, hst.2.1.symm ▸ readPacked_lt _ _ _ _ _, hst.2.2⟩
  · simp only [hcf, ↓reduceIte]
    by_cases hk : loc - capFrontWhp n_max < capBackWhp n_max
    · simp only [hk, ↓reduceIte]
      have hidx_bp := mul_add_lt_mul_bound hb hk
      let bpVal := readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s.mem
        (b * capBackWhp n_max + (loc - capFrontWhp n_max))
      have hbp_step : StepSpec w (base + largeSpaceWhp c U V w n_max) s _ s bpVal :=
        StepSpec.readPackedGen hw hidx_bp hbp_b
      by_cases hbp : bpVal < poolSizeWhp n_max
      · have hp_lt : numBucketsWhp n_max * capFrontWhp n_max + bpVal < n_max := by
          unfold poolSizeWhp at hbp; omega
        have hcomb := hbp_step.bind (g := fun v =>
            if v < poolSizeWhp n_max then
              readPackedGenProg
                (((base, offQuotWhp c w n_max), (quotBitsWhp U n_max, w)),
                 numBucketsWhp n_max * capFrontWhp n_max + v)
            else pure 0)
          (by simp only [hbp, ↓reduceIte]; exact StepSpec.readPackedGen hw hp_lt hq_b)
        exact ⟨hcomb.1, hcomb.2.1.symm ▸ readPacked_lt _ _ _ _ _, hcomb.2.2⟩
      · have hcomb := hbp_step.bind (g := fun v =>
            if v < poolSizeWhp n_max then
              readPackedGenProg
                (((base, offQuotWhp c w n_max), (quotBitsWhp U n_max, w)),
                 numBucketsWhp n_max * capFrontWhp n_max + v)
            else pure 0)
          (by simp only [hbp, ↓reduceIte]; exact StepSpec.pure _ _)
        exact ⟨hcomb.1, hcomb.2.1.symm ▸ Nat.two_pow_pos _, hcomb.2.2⟩
    · simp only [hk, ↓reduceIte]
      exact ⟨rfl, Nat.two_pow_pos _, validProg_pure _⟩

private theorem readHealSlotQuotProg_eq {c U V w n_max base b loc : ℕ}
    {qArr : ℕ → ℕ} {backPtr : ℕ → ℕ → ℕ} {s : Memory.State}
    (hb : b < numBucketsWhp n_max)
    (hq_mem : ∀ i < n_max,
      readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s.mem i = qArr i)
    (hbp_mem : ∀ k < capBackWhp n_max,
      readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s.mem
        (b * capBackWhp n_max + k) = backPtr b k)
    (hk_cb : loc - capFrontWhp n_max < capBackWhp n_max)
    (hbp_ps : capFrontWhp n_max ≤ loc → backPtr b (loc - capFrontWhp n_max) < poolSizeWhp n_max) :
    let rt := mkHealRt c U V w n_max base
    let prog := readHealSlotQuotProg ((rt, (offQuotWhp c w n_max, quotBitsWhp U n_max)), (b, loc))
    let cf := capFrontWhp n_max
    let p := if loc < cf then b * cf + loc else numBucketsWhp n_max * cf + backPtr b (loc - cf)
    (Memory.spec 0).clientResult s prog = qArr p := by
  have hMcf_le : numBucketsWhp n_max * capFrontWhp n_max ≤ n_max :=
    (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans (Nat.mul_div_le _ _)
  dsimp only
  unfold readHealSlotQuotProg
  dsimp only [mkHealRt, hlBase, hlW, hlM, hlCF, hlCB, hlPoolSize, hlGBits, hlOffBp,
    readPackedGenProg]
  simp only [pure_bind]
  by_cases hcf : loc < capFrontWhp n_max
  · simp only [hcf, ↓reduceIte, clientResult_readPackedProg]
    exact hq_mem _ ((mul_add_lt_mul_bound hb hcf).trans_le hMcf_le)
  · have hge : capFrontWhp n_max ≤ loc := Nat.le_of_not_lt hcf
    have hbp_lt := hbp_ps hge
    have hp_lt : numBucketsWhp n_max * capFrontWhp n_max + backPtr b (loc - capFrontWhp n_max) <
        n_max := by
      unfold poolSizeWhp at hbp_lt; omega
    simp only [hcf, hk_cb, ↓reduceIte]
    rw [clientResult_bind, clientState_readPackedProg,
      clientResult_readPackedProg, hbp_mem _ hk_cb]
    simp only [hbp_lt, ↓reduceIte, clientResult_readPackedProg]
    exact hq_mem _ hp_lt

/-! ## Per-Bucket & All-Bucket Slice Rebuild (`buildBktSliceLoopProg`) -/

/-- Single coordinate insertion step of `buildBktSliceLoopProg`. -/
@[irreducible] def buildBktSliceStepProg :
    (((WhpCoreParams × ℕ) × (HealRt × HashRt)) × (ℕ × ℕ)) × ℕ → Memory.Prog ℕ
  | ((((cp, base_in), (rt, hrt)), (b_in, salt_in)), loc_in) => do
    let base ← pure base_in
    let _ ← Memory.read base
    let b ← pure b_in
    let salt ← pure salt_in
    let loc ← pure loc_in
    let one_v ← pure 1
    let q ← readHealSlotQuotProg ((rt, (wpOffQuot cp, wpQuotBits cp)), (b, loc))
    let fp ← fpOfQuotRtProg (((hrt, salt), b), q)
    let sIdx ← pure (3 * b)
    btreeInsertGenProg ((((cp, base), sIdx), fp), loc)
    pure (loc + one_v)

private theorem memoryCost_buildBktSliceStep_pos
    (d : (((WhpCoreParams × ℕ) × (HealRt × HashRt)) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    0 < memoryCost (buildBktSliceStepProg d) s := by
  rcases d with ⟨⟨⟨⟨cp, base⟩, rt, hrt⟩, b, salt⟩, loc⟩
  unfold buildBktSliceStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 0 < 1 + _
  omega

/-- Precondition for `buildBktSliceStepProg`. -/
@[expose] def BuildBktSliceStepPre (w : ℕ) :
    (((WhpCoreParams × ℕ) × (HealRt × HashRt)) × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | ((((cp, base), (rt, hrt)), (b, _salt)), loc), s =>
    ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (sl : BTreeSlice) (mapFn : ℕ → Option ℕ),
      WhpLargeEnv c U V w₀ n_max w base ∧
      cp = mkWhpCoreParams c U V w₀ n_max ∧
      rt = mkHealRt c U V w₀ n_max base ∧
      hrt = mkHashRt c U w₀ n_max base ∧
      SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
      b < numBucketsWhp n_max ∧
      loc < totalLocalCoordsWhp n_max ∧
      BTreeSliceMemRep base c U V w₀ n_max (3 * b) sl s.mem ∧
      ValidWhpSlice n_max loc sl mapFn

private theorem realizes_buildBktSliceStep :
    Realizes .exact buildBktSliceStepProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × (HealRt × HashRt)) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ))
      BuildBktSliceStepPre
      (fun _ _ => 0) := by
  unfold buildBktSliceStepProg
  have hrq := realizes_readHealSlotQuot
  have hfp := realizes_fpOfQuotRt
  have hbi := realizes_btreeInsertGen
  have hcs_r : ∀ a s', (Memory.spec 0).clientState s' (Memory.read a) = s' := fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, rt, hrt⟩, b, salt⟩, loc⟩
    dsimp only [BuildBktSliceStepPre] at h
    obtain ⟨c, U, V, w₀, n_max, θ, sl, mapFn, henv, rfl, rfl, rfl, hseed, hb_lt, hloc_lt,
      hrep, hv⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h16M := sixteen_mul_numBuckets_le_n_max hth
    have htot_n := (large_bounds_lt_n_max hth).2.2.1
    have htot3 := @totalLocalCoordsWhp_le_three_mul n_max
    obtain ⟨hrq_st, hrq_lt, _⟩ := readHealSlotQuotProg_spec (b := b) (loc := loc) henv hb_lt
      (s := s)
    let qVal := (Memory.spec 0).clientResult s
      (readHealSlotQuotProg
        ((mkHealRt c U V w n_max base, (offQuotWhp c w n_max, quotBitsWhp U n_max)), (b, loc)))
    obtain ⟨hfp_st, hfp_res, _, _⟩ := fpOfQuotRtProg_spec (salt := salt) (b := b) (q := qVal)
      henv hseed (s := s)
    have hfp_lt : (Memory.spec 0).clientResult s
        (fpOfQuotRtProg (((mkHashRt c U w n_max base, salt), b), qVal)) < 2 ^ fpBitsWhp n_max :=
      hfp_res.symm ▸ fpOfQuot_lt_two_pow θ salt _
    have hloc_val : loc < 2 ^ valLaneBitsWhp n_max := by rw [two_pow_valLaneBitsWhp]; omega
    dsimp only [qVal] at hfp_st hfp_lt
    simp only [hcs_r, wp_large_offQuot hth, wp_large_quotBits hth, hrq_st, hfp_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl, rfl, rfl, hb_lt⟩
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed, hrq_lt⟩
    | exact ⟨c, U, V, w, n_max, loc, sl, mapFn, henv, rfl, by omega, by omega, hrep, hv,
        hfp_lt, hloc_val⟩
  )

/-- Inner loop inserting local coordinates into live slice `3 * b`. -/
@[irreducible] def buildBktSliceLoopProg :
    ((((WhpCoreParams × ℕ) × (HealRt × HashRt)) × (ℕ × ℕ)) × ℕ) × ℕ → Memory.Prog ℕ
  | ((cfg, l₀), rem) => iterate buildBktSliceStepProg cfg rem l₀

private theorem realizes_buildBktSliceLoop :
    Realizes .exact buildBktSliceLoopProg
      (WordEncoding.encode
        (α := ((((WhpCoreParams × ℕ) × (HealRt × HashRt)) × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cfg, l₀), rem) s =>
        iterationSafe buildBktSliceStepProg BuildBktSliceStepPre w cfg rem l₀ s)
      (fun _ _ => 0) := by
  unfold buildBktSliceLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × (HealRt × HashRt)) × (ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ))
    realizes_buildBktSliceStep
    memoryCost_buildBktSliceStep_pos

private theorem buildBktSliceStep_transition {c U V w n_max base b salt l : ℕ}
    {θ : SeedWhp c U n_max} {sl : BTreeSlice} {mapFn : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hl : l < totalLocalCoordsWhp n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : BTreeSliceMemRep base c U V w n_max (3 * b) sl s.mem)
    (hv : ValidWhpSlice n_max l sl mapFn) :
    let cp := mkWhpCoreParams c U V w n_max
    let rt := mkHealRt c U V w n_max base
    let hrt := mkHashRt c U w n_max base
    let p1 := buildBktSliceStepProg ((((cp, base), (rt, hrt)), (b, salt)), l)
    let s' := (Memory.spec 0).clientState s p1
    (Memory.spec 0).clientResult s p1 = l + 1 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s p1 ∧
    SeedWhpMemRep base c U w n_max θ s'.mem ∧
    (∃ sl' mapFn',
      BTreeSliceMemRep base c U V w n_max (3 * b) sl' s'.mem ∧
      ValidWhpSlice n_max (l + 1) sl' mapFn') ∧
    (∀ sIdx < 3 * numBucketsWhp n_max, sIdx ≠ 3 * b → ∀ sl₂,
      BTreeSliceMemRep base c U V w n_max sIdx sl₂ s.mem →
      BTreeSliceMemRep base c U V w n_max sIdx sl₂ s'.mem) := by
  have hw := henv.2.1
  have hth := henv.2.2.2.1
  have htot3 := @totalLocalCoordsWhp_le_three_mul n_max
  have hq_bm : offQuotWhp c w n_max ≤ offBktMeta c U V w n_max := by
    unfold offBktMeta offLocState offPermAct offValWhp; omega
  have hbase_lt : base < base + largeSpaceWhp c U V w n_max := by
    have : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    omega
  obtain ⟨hrq_st, _, hrq_vp⟩ := readHealSlotQuotProg_spec (b := b) (loc := l) henv hb (s := s)
  let qv := (Memory.spec 0).clientResult s
    (readHealSlotQuotProg
      ((mkHealRt c U V w n_max base, (offQuotWhp c w n_max, quotBitsWhp U n_max)), (b, l)))
  obtain ⟨hfp_st, hfp_res, _, hfp_vp⟩ := fpOfQuotRtProg_spec (salt := salt) (b := b) (q := qv)
    henv hseed (s := s)
  let fpv := (Memory.spec 0).clientResult s
    (fpOfQuotRtProg (((mkHashRt c U w n_max base, salt), b), qv))
  have hfp_lt : fpv < 2 ^ fpBitsWhp n_max := by
    dsimp only [fpv]; rw [hfp_res]; exact fpOfQuot_lt_two_pow θ salt _
  have hl_val : l < 2 ^ valLaneBitsWhp n_max := by rw [two_pow_valLaneBitsWhp]; omega
  obtain ⟨_, _, hbi_vp, hr', hv', hoth', _, hout'⟩ := btreeInsertGenProg_spec (sIdx := 3 * b)
    (insCount := l) (q := fpv) (val := l) henv (by omega) (by omega) hrep hv hfp_lt hl_val
  set s1 := (Memory.spec 0).clientState s
    (btreeInsertGenProg ((((mkWhpCoreParams c U V w n_max, base), 3 * b), fpv), l))
  have hstep : StepSpec w (base + largeSpaceWhp c U V w n_max) s
      (buildBktSliceStepProg
        ((((mkWhpCoreParams c U V w n_max, base),
           (mkHealRt c U V w n_max base, mkHashRt c U w n_max base)), (b, salt)), l))
      s1 (l + 1) := by
    unfold buildBktSliceStepProg
    simp only [pure_bind, wp_large_offQuot hth, wp_large_quotBits hth]
    refine (StepSpec.read hbase_lt).bind ?_
    refine StepSpec.bind ⟨hrq_st, rfl, hrq_vp⟩ ?_
    refine StepSpec.bind ⟨hfp_st, rfl, hfp_vp⟩ ?_
    exact StepSpec.bind ⟨rfl, rfl, hbi_vp⟩ (StepSpec.pure _ _)
  dsimp only
  rw [hstep.1, hstep.2.1]
  exact ⟨rfl, hstep.2.2,
    SeedWhpMemRep.congr_hash hw (fun a _ ha2 => (hout' a (Or.inl (by omega))).symm) hseed,
    ⟨_, _, hr', hv'⟩, hoth'⟩

private theorem buildBktSliceLoop_safe_and_frame {c U V w n_max base b salt : ℕ}
    {θ : SeedWhp c U n_max}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) :
    let cp := mkWhpCoreParams c U V w n_max
    let rt := mkHealRt c U V w n_max base
    let hrt := mkHashRt c U w n_max base
    ∀ rem (s : Memory.State),
      rem ≤ totalLocalCoordsWhp n_max →
      SeedWhpMemRep base c U w n_max θ s.mem →
      BTreeSliceMemRep base c U V w n_max (3 * b) zeroBTreeSlice s.mem →
      let s' := (Memory.spec 0).clientState s
        (buildBktSliceLoopProg (((((cp, base), (rt, hrt)), (b, salt)), 0), rem))
      iterationSafe buildBktSliceStepProg BuildBktSliceStepPre w
        (((cp, base), (rt, hrt)), (b, salt)) rem 0 s ∧
      SeedWhpMemRep base c U w n_max θ s'.mem ∧
      (∀ sIdx < 3 * numBucketsWhp n_max, sIdx ≠ 3 * b → ∀ sl₂,
        BTreeSliceMemRep base c U V w n_max sIdx sl₂ s.mem →
        BTreeSliceMemRep base c U V w n_max sIdx sl₂ s'.mem) := by
  intro cp rt hrt rem s hle hseed hrep
  unfold buildBktSliceLoopProg
  obtain ⟨hsafe, -, -, hseed', -, hoth'⟩ := validProg_iterate_of_inv (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (body := buildBktSliceStepProg)
    (d := (((cp, base), (rt, hrt)), (b, salt))) (n := rem) (safe := BuildBktSliceStepPre)
    (a := 0) (s := s)
    (fun k l t => l = k ∧ SeedWhpMemRep base c U w n_max θ t.mem ∧
      (∃ sl mf, BTreeSliceMemRep base c U V w n_max (3 * b) sl t.mem ∧
        ValidWhpSlice n_max l sl mf) ∧
      ∀ sIdx < 3 * numBucketsWhp n_max, sIdx ≠ 3 * b → ∀ sl₂,
        BTreeSliceMemRep base c U V w n_max sIdx sl₂ s.mem →
        BTreeSliceMemRep base c U V w n_max sIdx sl₂ t.mem)
    (fun k hk l t ⟨hl, hseed, ⟨sl, mf, hrep, hv⟩, hoth⟩ => by
      have hl_lt : l < totalLocalCoordsWhp n_max := by omega
      obtain ⟨hres1, hvp1, hseed1, hrep1, hoth1⟩ :=
        buildBktSliceStep_transition (salt := salt) henv hb hl_lt hseed hrep hv
      refine ⟨⟨c, U, V, w, n_max, θ, sl, mf, henv, rfl, rfl, rfl, hseed, hb, hl_lt, hrep, hv⟩,
        hvp1, ?_⟩
      rw [hres1]
      exact ⟨by omega, hseed1, hrep1, fun sIdx hsIdx hne sl₂ hr₂ =>
        hoth1 sIdx hsIdx hne sl₂ (hoth sIdx hsIdx hne sl₂ hr₂)⟩)
    ⟨rfl, hseed, ⟨_, _, hrep, validWhpSlice_zero _ 0 _⟩, fun _ _ _ _ hr => hr⟩
  exact ⟨hsafe, hseed', hoth'⟩

private theorem buildBktSliceLoop_spec {c U V w n_max base b salt cnt : ℕ}
    {θ : SeedWhp c U n_max} {qArr : ℕ → ℕ} {backPtr : ℕ → ℕ → ℕ} {s₀ : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hcnt_le : cnt ≤ totalLocalCoordsWhp n_max)
    (hback_cb : cnt - capFrontWhp n_max < capBackWhp n_max)
    (hbp_ps : ∀ k < cnt - capFrontWhp n_max, backPtr b k < poolSizeWhp n_max)
    (hseed₀ : SeedWhpMemRep base c U w n_max θ s₀.mem)
    (hq₀ : ∀ i < n_max,
      readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s₀.mem i = qArr i)
    (hbp₀ : ∀ k < capBackWhp n_max,
      readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s₀.mem
        (b * capBackWhp n_max + k) = backPtr b k)
    (s : Memory.State)
    (hrep : BTreeSliceMemRep base c U V w n_max (3 * b) zeroBTreeSlice s.mem)
    (hout : ∀ a, (a < base + offBktMeta c U V w n_max ∨
      (base + offFbStart c U V w n_max ≤ a ∧ a < base + offBtMeta c U V w n_max) ∨
      base + offTrieChild0 c U V w n_max ≤ a) → s.mem a = s₀.mem a) :
    let cp := mkWhpCoreParams c U V w n_max
    let rt := mkHealRt c U V w n_max base
    let hrt := mkHashRt c U w n_max base
    let prog := buildBktSliceLoopProg (((((cp, base), (rt, hrt)), (b, salt)), 0), cnt)
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = s.frontier ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BTreeSliceMemRep base c U V w n_max (3 * b)
      (buildBucketSlice c U n_max θ qArr backPtr b salt cnt) s'.mem ∧
    (∀ sIdx' < 3 * numBucketsWhp n_max, sIdx' ≠ 3 * b → ∀ sl₂,
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s.mem →
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s'.mem) ∧
    (∀ idx < 16 * numBucketsWhp n_max,
      idx ≠ 16 * b + 10 → idx ≠ 16 * b + 11 →
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem idx =
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem idx) ∧
    (∀ a, (a < base + offBktMeta c U V w n_max ∨
        (base + offFbStart c U V w n_max ≤ a ∧ a < base + offBtMeta c U V w n_max) ∨
        base + offTrieChild0 c U V w n_max ≤ a) → s'.mem a = s₀.mem a) := by
  intro cp rt hrt
  have hw := henv.2.1
  have hth := henv.2.2.2.1
  have htot3 := @totalLocalCoordsWhp_le_three_mul n_max
  have hbase_lt : base < base + largeSpaceWhp c U V w n_max := by
    have : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    omega
  have hq_bm : offQuotWhp c w n_max + packedWords n_max (quotBitsWhp U n_max) w ≤
      offBktMeta c U V w n_max := by
    have h1 : offValWhp c U w n_max =
      offQuotWhp c w n_max + packedWords n_max (quotBitsWhp U n_max) w := rfl
    unfold offBktMeta offLocState offPermAct; omega
  have hbp_bt : offFbStart c U V w n_max ≤ offBackPtr c U V w n_max ∧
      offBackPtr c U V w n_max +
        packedWords (numBucketsWhp n_max * capBackWhp n_max) (globalPtrBits n_max) w ≤
      offBtMeta c U V w n_max := by
    have h1 : offBackAux c U V w n_max = offBackPtr c U V w n_max +
        packedWords (numBucketsWhp n_max * capBackWhp n_max) (globalPtrBits n_max) w := rfl
    refine ⟨by unfold offBackPtr; omega, ?_⟩
    unfold offBtMeta offPoolOwner offPoolFreeStack; omega
  have hdiv3 : (3 * b) / 3 = b := by omega
  have hmod3 : (3 * b) % 3 = 0 := by omega
  unfold buildBktSliceLoopProg
  obtain ⟨-, hvp, hl_eq, hrep', -, hoth', hbm', hout', hfr'⟩ := validProg_iterate_of_inv (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (body := buildBktSliceStepProg)
    (d := (((cp, base), (rt, hrt)), (b, salt))) (n := cnt) (safe := fun _ _ _ => True)
    (a := 0) (s := s)
    (fun k l t => l = k ∧
      BTreeSliceMemRep base c U V w n_max (3 * b)
        (buildBucketSlice c U n_max θ qArr backPtr b salt l) t.mem ∧
      (∃ mf, ValidWhpSlice n_max l (buildBucketSlice c U n_max θ qArr backPtr b salt l) mf) ∧
      (∀ sIdx' < 3 * numBucketsWhp n_max, sIdx' ≠ 3 * b → ∀ sl₂,
        BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s.mem →
        BTreeSliceMemRep base c U V w n_max sIdx' sl₂ t.mem) ∧
      (∀ idx < 16 * numBucketsWhp n_max,
        idx ≠ 16 * b + 10 → idx ≠ 16 * b + 11 →
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w t.mem idx =
          readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem idx) ∧
      (∀ a, (a < base + offBktMeta c U V w n_max ∨
          (base + offFbStart c U V w n_max ≤ a ∧ a < base + offBtMeta c U V w n_max) ∨
          base + offTrieChild0 c U V w n_max ≤ a) → t.mem a = s₀.mem a) ∧
      t.frontier = s.frontier)
    (fun k hk l t ⟨hl, hrep, ⟨mapFn, hv⟩, hoth, hbm, hout, hfr⟩ => by
      have hl_cnt : l < cnt := by omega
      have hl_tot : l < totalLocalCoordsWhp n_max := hl_cnt.trans_le hcnt_le
      have hseed_s : SeedWhpMemRep base c U w n_max θ t.mem :=
        SeedWhpMemRep.congr_hash hw (fun a _ ha2 => (hout a (Or.inl (by omega))).symm) hseed₀
      have hq_s : ∀ i < n_max,
          readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w t.mem i = qArr i :=
        fun i hi => (readPacked_congr hw (hidx := hi)
          (fun a ⟨_, ha2⟩ => hout a (Or.inl (by omega)))).trans (hq₀ i hi)
      have hbp_s : ∀ j < capBackWhp n_max,
          readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w t.mem
            (b * capBackWhp n_max + j) = backPtr b j := fun j hj =>
        (readPacked_congr hw (hidx := mul_add_lt_mul_bound hb hj)
          (fun a ⟨ha1, ha2⟩ => hout a (Or.inr (Or.inl ⟨by omega, by omega⟩)))).trans (hbp₀ j hj)
      obtain ⟨hrq_st, _, hrq_vp⟩ := readHealSlotQuotProg_spec (b := b) (loc := l) henv hb (s := t)
      have hrq_eq := readHealSlotQuotProg_eq (loc := l) hb hq_s hbp_s (by omega)
        (fun hge => hbp_ps _ (by omega))
      set p_loc := if l < capFrontWhp n_max then b * capFrontWhp n_max + l
        else numBucketsWhp n_max * capFrontWhp n_max + backPtr b (l - capFrontWhp n_max)
      obtain ⟨hfp_st, hfp_res, _, hfp_vp⟩ := fpOfQuotRtProg_spec (salt := salt) (b := b)
        (q := qArr p_loc) henv hseed_s (s := t)
      set kv_loc := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1) b (qArr p_loc)
      set fp_loc :=
        if hs : salt < sMaxWhp c n_max then
          if hu : kv_loc < U then fpHash c U n_max θ.2 ⟨salt, hs⟩ ⟨kv_loc, hu⟩ else 0
        else 0
      have hfp_lt : fp_loc < 2 ^ fpBitsWhp n_max := fpOfQuot_lt_two_pow θ salt kv_loc
      have hl_val : l < 2 ^ valLaneBitsWhp n_max := by rw [two_pow_valLaneBitsWhp]; omega
      obtain ⟨hfr_bi, _, hvp_bi, hrep_bi, hv_bi, hoth_bi, hbm_bi, hout_bi⟩ :=
        btreeInsertGenProg_spec (sIdx := 3 * b) (insCount := l) (q := fp_loc) (val := l)
          henv (by omega) (by omega) hrep hv hfp_lt hl_val
      set s1 := (Memory.spec 0).clientState t
        (btreeInsertGenProg ((((cp, base), 3 * b), fp_loc), l))
      have hs1 : StepSpec w (base + largeSpaceWhp c U V w n_max) t
          (buildBktSliceStepProg ((((cp, base), (rt, hrt)), (b, salt)), l)) s1 (l + 1) := by
        unfold buildBktSliceStepProg
        dsimp only [cp, rt, hrt] at hrq_st hrq_eq hrq_vp hfp_st hfp_res hfp_vp hvp_bi s1 ⊢
        simp only [pure_bind, wp_large_offQuot hth, wp_large_quotBits hth]
        refine (StepSpec.read hbase_lt).bind ?_
        refine StepSpec.bind ⟨hrq_st, hrq_eq, hrq_vp⟩ ?_
        refine StepSpec.bind ⟨hfp_st, hfp_res, hfp_vp⟩ ?_
        exact StepSpec.bind ⟨rfl, rfl, hvp_bi⟩ (StepSpec.pure _ _)
      refine ⟨trivial, hs1.2.2, ?_⟩
      rw [hs1.1, hs1.2.1]
      exact ⟨by omega, hrep_bi, ⟨_, hv_bi⟩,
        fun sIdx' hsIdx' hne sl₂ hr₂ =>
          hoth_bi sIdx' hsIdx' hne sl₂ (hoth sIdx' hsIdx' hne sl₂ hr₂),
        fun idx hidx h10 h11 => (hbm_bi idx hidx (by rw [hdiv3, hmod3]; omega)
          (by rw [hdiv3, hmod3]; omega)).trans (hbm idx hidx h10 h11),
        fun a ha => (hout_bi a ha).trans (hout a ha), hfr_bi.trans hfr⟩)
    ⟨rfl, hrep, ⟨fun _ => none, validWhpSlice_zero _ 0 _⟩, fun _ _ _ _ hr => hr,
      fun _ _ _ _ => rfl, hout, rfl⟩
  rw [hl_eq] at hrep'
  exact ⟨hfr', hvp, hrep', hoth', hbm', hout'⟩

/-- Single bucket step of `buildAllBucketsOuterLoopProg`. -/
@[irreducible] def buildAllBucketsOuterStepProg :
    ((WhpCoreParams × ℕ) × (HealRt × HashRt)) × ℕ → Memory.Prog ℕ
  | (((cp, base_in), (rt, hrt)), b_in) => do
    let base ← pure base_in
    let b ← pure b_in
    let zero_v ← pure 0
    let one_v ← pure 1
    let b1 ← pure (b + one_v)
    let lo ← readPackedGenProg (((hlBase rt, hlOffFb rt), (hlGBits rt, hlW rt)), b)
    let hi ← readPackedGenProg (((hlBase rt, hlOffFb rt), (hlGBits rt, hlW rt)), b1)
    let idxSalt ← pure (16 * b + 1)
    let salt ← readPackedGenProg (((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), idxSalt)
    if lo ≤ hi then
      let cnt ← pure (hi - lo)
      if cnt ≤ hlTotalLoc rt then
        let _ ← buildBktSliceLoopProg (((((cp, base), (rt, hrt)), (b, salt)), zero_v), cnt)
        pure b1
      else
        pure b1
    else
      pure b1

private theorem memoryCost_buildAllBucketsOuterStep_pos
    (d : ((WhpCoreParams × ℕ) × (HealRt × HashRt)) × ℕ) (s : Memory.State) :
    0 < memoryCost (buildAllBucketsOuterStepProg d) s := by
  rcases d with ⟨⟨⟨cp, base⟩, rt, hrt⟩, b⟩
  unfold buildAllBucketsOuterStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 0 < 2 + _
  omega

/-- Precondition for `buildAllBucketsOuterStepProg`. -/
@[expose] def BuildAllBucketsOuterPre (w : ℕ) :
    ((WhpCoreParams × ℕ) × (HealRt × HashRt)) × ℕ → Memory.State → Prop
  | (((cp, base), (rt, hrt)), b), s =>
    ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max),
      WhpLargeEnv c U V w₀ n_max w base ∧
      cp = mkWhpCoreParams c U V w₀ n_max ∧
      rt = mkHealRt c U V w₀ n_max base ∧
      hrt = mkHashRt c U w₀ n_max base ∧
      SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
      b < numBucketsWhp n_max ∧
      (∀ sIdx < 3 * numBucketsWhp n_max, b ≤ sIdx / 3 →
        BTreeSliceMemRep base c U V w₀ n_max sIdx zeroBTreeSlice s.mem)

private theorem realizes_buildAllBucketsOuterStep :
    Realizes .exact buildAllBucketsOuterStepProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × (HealRt × HashRt)) × ℕ))
      (WordEncoding.encode (α := ℕ))
      BuildAllBucketsOuterPre
      (fun _ _ => 0) := by
  unfold buildAllBucketsOuterStepProg
  have hrp := realizes_readPackedGen
  have hbs := realizes_buildBktSliceLoop
  have hcs : ∀ y s', (Memory.spec 0).clientState s' (readPackedGenProg y) = s' := fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, rt, hrt⟩, b⟩
    dsimp only [BuildAllBucketsOuterPre] at h
    obtain ⟨c, U, V, w₀, n_max, θ, henv, rfl, rfl, rfl, hseed, hb_lt, hz_rem⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    obtain ⟨hM_lt, h16M, _, _, _, _, _, hgk⟩ := hl_bounds henv
    have hseg := WhpLargeEnv.seg_end_le c U V w n_max
    have hrep3b : BTreeSliceMemRep base c U V w n_max (3 * b) zeroBTreeSlice s.mem :=
      hz_rem (3 * b) (by omega) (by omega)
    dsimp only [mkHealRt, hlBase, hlW, hlM, hlTotalLoc, hlGBits, hlOffBm, hlOffFb] at *
    simp only [hcs] at *
    first
    | exact henv.fits_const (by decide)
    | omega
    | exact henv.fits_of_le_n_max (by omega)
    | exact to_true_exists (henv.packed_safe_of_le hgk (idx := b) (by omega) hseg.2.2.2.2.2.1)
    | exact to_true_exists (henv.packed_safe_of_le hgk (idx := b + 1) (by omega) hseg.2.2.2.2.2.1)
    | exact to_true_exists (henv.bktMeta_safe (idx := 16 * b + 1) (by omega))
    | exact (buildBktSliceLoop_safe_and_frame henv hb_lt _ s (by omega) hseed hrep3b).1
  )

/-- Outer bucket loop rebuilding all `M` live SWAR B+-tree slices `3 * b`. -/
@[irreducible] def buildAllBucketsOuterLoopProg :
    (((WhpCoreParams × ℕ) × (HealRt × HashRt)) × ℕ) × ℕ → Memory.Prog ℕ
  | ((cfg, b₀), rem) => iterate buildAllBucketsOuterStepProg cfg rem b₀

/-- `Realizes .exact` certificate for `buildAllBucketsOuterLoopProg`. -/
theorem realizes_buildAllBucketsOuterLoop :
    Realizes .exact buildAllBucketsOuterLoopProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × (HealRt × HashRt)) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cfg, b₀), rem) s =>
        iterationSafe buildAllBucketsOuterStepProg BuildAllBucketsOuterPre w cfg rem b₀ s)
      (fun _ _ => 0) := by
  unfold buildAllBucketsOuterLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := (WhpCoreParams × ℕ) × (HealRt × HashRt)))
    (WordEncoding.encode (α := ℕ))
    realizes_buildAllBucketsOuterStep
    memoryCost_buildAllBucketsOuterStep_pos

/-- Loop-safety invariant for `buildAllBucketsOuterLoopProg`. -/
theorem buildAllBucketsOuterLoop_safe {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let cp := mkWhpCoreParams c U V w n_max
    let rt := mkHealRt c U V w n_max base
    let hrt := mkHashRt c U w n_max base
    ∀ rem b₀ (s : Memory.State),
      b₀ + rem ≤ numBucketsWhp n_max →
      SeedWhpMemRep base c U w n_max θ s.mem →
      (∀ sIdx < 3 * numBucketsWhp n_max, b₀ ≤ sIdx / 3 →
        BTreeSliceMemRep base c U V w n_max sIdx zeroBTreeSlice s.mem) →
      iterationSafe buildAllBucketsOuterStepProg BuildAllBucketsOuterPre w
        ((cp, base), (rt, hrt)) rem b₀ s := by
  intro cp rt hrt rem b₀ s hle hseed hz_rem
  refine iterationSafe_of_stepInv _ _ w _
    (fun j b t => b + j ≤ numBucketsWhp n_max ∧ SeedWhpMemRep base c U w n_max θ t.mem ∧
      ∀ sIdx < 3 * numBucketsWhp n_max, b ≤ sIdx / 3 →
        BTreeSliceMemRep base c U V w n_max sIdx zeroBTreeSlice t.mem)
    (fun j b t h => ?_) ⟨hle, hseed, hz_rem⟩
  obtain ⟨hle, hseed, hz_rem⟩ := h
  have hb_lt : b < numBucketsWhp n_max := by omega
  refine ⟨⟨c, U, V, w, n_max, θ, henv, rfl, rfl, rfl, hseed, hb_lt, hz_rem⟩, ?_⟩
  set p1 := buildAllBucketsOuterStepProg (((cp, base), (rt, hrt)), b)
  set lo := readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w t.mem b
  set hi := readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w t.mem (b + 1)
  set salt := readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w t.mem
    (16 * b + 1)
  have hr1 : (Memory.spec 0).clientResult t p1 = b + 1 := by
    dsimp only [p1]; unfold buildAllBucketsOuterStepProg; dsimp only [readPackedGenProg]
    simp only [pure_bind]
    rw [clientResult_bind, clientState_readPackedProg,
      clientResult_bind, clientState_readPackedProg,
      clientResult_bind, clientState_readPackedProg]
    split_ifs
    · rw [clientResult_bind]; rfl
    · rfl
    · rfl
  rw [hr1]
  by_cases hcond : lo ≤ hi ∧ hi - lo ≤ totalLocalCoordsWhp n_max
  · have hs1_eq : (Memory.spec 0).clientState t p1 =
        (Memory.spec 0).clientState t
          (buildBktSliceLoopProg (((((cp, base), (rt, hrt)), (b, salt)), 0), hi - lo)) := by
      dsimp only [p1]; unfold buildAllBucketsOuterStepProg
      simp only [rt, mkHealRt, hlBase, hlW, hlTotalLoc, hlGBits, hlOffBm, hlOffFb,
        readPackedGenProg, pure_bind]
      rw [clientState_bind, clientState_readPackedProg, clientResult_readPackedProg,
        clientState_bind, clientState_readPackedProg, clientResult_readPackedProg,
        clientState_bind, clientState_readPackedProg, clientResult_readPackedProg,
        ite_eq_left hcond.1, ite_eq_left hcond.2, clientState_bind]
      rfl
    rw [hs1_eq]
    obtain ⟨_, hseed_f, hoth_f⟩ := buildBktSliceLoop_safe_and_frame (salt := salt) henv hb_lt
      (hi - lo) t hcond.2 hseed (hz_rem (3 * b) (by omega) (by omega))
    exact ⟨by omega, hseed_f, fun sIdx hsIdx hge =>
      hoth_f sIdx hsIdx (by omega) zeroBTreeSlice (hz_rem sIdx hsIdx (by omega))⟩
  · have hs1_eq : (Memory.spec 0).clientState t p1 = t := by
      dsimp only [p1]; unfold buildAllBucketsOuterStepProg
      simp only [rt, mkHealRt, hlBase, hlW, hlTotalLoc, hlGBits, hlOffBm, hlOffFb,
        readPackedGenProg, pure_bind]
      rw [clientState_bind, clientState_readPackedProg, clientResult_readPackedProg,
        clientState_bind, clientState_readPackedProg, clientResult_readPackedProg,
        clientState_bind, clientState_readPackedProg, clientResult_readPackedProg]
      by_cases h1 : lo ≤ hi
      · rw [ite_eq_left h1, ite_eq_right (fun h2 => hcond ⟨h1, h2⟩)]; rfl
      · rw [ite_eq_right h1]; rfl
    rw [hs1_eq]
    exact ⟨by omega, hseed, fun sIdx hsIdx hge => hz_rem sIdx hsIdx (by omega)⟩

/-- Exact memory specification of `buildAllBucketsOuterLoopProg`. -/
theorem buildAllBucketsOuterLoop_spec {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fbStart qArr : ℕ → ℕ} {backPtr : ℕ → ℕ → ℕ} {salts : ℕ → ℕ}
    {s₀ : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hfb_adj : ∀ b < numBucketsWhp n_max, fbStart b ≤ fbStart (b + 1))
    (hbnd : ∀ b < numBucketsWhp n_max,
      (fbStart (b + 1) - fbStart b) - capFrontWhp n_max < capBackWhp n_max ∧
      fbStart (b + 1) - fbStart b ≤ totalLocalCoordsWhp n_max)
    (hbp_ps : ∀ b < numBucketsWhp n_max,
      ∀ k < (fbStart (b + 1) - fbStart b) - capFrontWhp n_max,
        backPtr b k < poolSizeWhp n_max)
    (hseed₀ : SeedWhpMemRep base c U w n_max θ s₀.mem)
    (hfb₀ : ∀ x ≤ numBucketsWhp n_max,
      readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s₀.mem x = fbStart x)
    (hq₀ : ∀ i < n_max,
      readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s₀.mem i = qArr i)
    (hbp₀ : ∀ b < numBucketsWhp n_max, ∀ k < capBackWhp n_max,
      readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s₀.mem
        (b * capBackWhp n_max + k) = backPtr b k) :
    let cp := mkWhpCoreParams c U V w n_max
    let rt := mkHealRt c U V w n_max base
    let hrt := mkHashRt c U w n_max base
    let M := numBucketsWhp n_max
    let targetSlice : ℕ → BTreeSlice := fun sIdx =>
      let b := sIdx / 3
      let role := sIdx % 3
      if b < M ∧ role = 0 then
        buildBucketSlice c U n_max θ qArr backPtr b (salts b) (fbStart (b + 1) - fbStart b)
      else zeroBTreeSlice
    ∀ rem b₀ (s : Memory.State),
      b₀ + rem ≤ M →
      (∀ sIdx < 3 * M,
        BTreeSliceMemRep base c U V w n_max sIdx
          (if sIdx / 3 < b₀ then targetSlice sIdx else zeroBTreeSlice) s.mem) →
      (∀ b < M,
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem (16 * b + 1) =
          salts b) →
      (∀ a, (a < base + offBktMeta c U V w n_max ∨
          (base + offFbStart c U V w n_max ≤ a ∧ a < base + offBtMeta c U V w n_max) ∨
          base + offTrieChild0 c U V w n_max ≤ a) → s.mem a = s₀.mem a) →
      let prog := buildAllBucketsOuterLoopProg ((((cp, base), (rt, hrt)), b₀), rem)
      let s' := (Memory.spec 0).clientState s prog
      s'.frontier = s.frontier ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      (∀ sIdx < 3 * M,
        BTreeSliceMemRep base c U V w n_max sIdx
          (if sIdx / 3 < b₀ + rem then targetSlice sIdx else zeroBTreeSlice) s'.mem) ∧
      (∀ b < M,
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem (16 * b + 1) =
          salts b) ∧
      (∀ a, (a < base + offBktMeta c U V w n_max ∨
          (base + offFbStart c U V w n_max ≤ a ∧ a < base + offBtMeta c U V w n_max) ∨
          base + offTrieChild0 c U V w n_max ≤ a) → s'.mem a = s₀.mem a) := by
  intro cp rt hrt M targetSlice rem b₀ s hle hprev hsalt hout
  have hw := henv.2.1
  have hseg := WhpLargeEnv.seg_end_le c U V w n_max
  have hbm_b : base + offBktMeta c U V w n_max +
      packedWords (16 * M) (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.1 _
  have hfb_b : base + offFbStart c U V w n_max +
      packedWords (M + 1) (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.2.1 _
  have hfb_bt : offFbStart c U V w n_max +
      packedWords (M + 1) (globalPtrBits n_max) w ≤ offBtMeta c U V w n_max := by
    have h6 : offBackPtr c U V w n_max =
      offFbStart c U V w n_max + packedWords (M + 1) (globalPtrBits n_max) w := rfl
    unfold offBtMeta offPoolOwner offPoolFreeStack offBackAux; omega
  unfold buildAllBucketsOuterLoopProg
  obtain ⟨-, hvp, hj_eq, hrep', hsalt', hout', hfr'⟩ := validProg_iterate_of_inv (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (body := buildAllBucketsOuterStepProg)
    (d := ((cp, base), (rt, hrt))) (n := rem) (safe := fun _ _ _ => True) (a := b₀) (s := s)
    (fun k j t => j = b₀ + k ∧
      (∀ sIdx < 3 * M,
        BTreeSliceMemRep base c U V w n_max sIdx
          (if sIdx / 3 < j then targetSlice sIdx else zeroBTreeSlice) t.mem) ∧
      (∀ b < M,
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w t.mem (16 * b + 1) =
          salts b) ∧
      (∀ a, (a < base + offBktMeta c U V w n_max ∨
          (base + offFbStart c U V w n_max ≤ a ∧ a < base + offBtMeta c U V w n_max) ∨
          base + offTrieChild0 c U V w n_max ≤ a) → t.mem a = s₀.mem a) ∧
      t.frontier = s.frontier)
    (fun k hk j t ⟨hj, hprev, hsalt_s, hout, hfr⟩ => by
      have hb_lt : j < M := by omega
      have hfb_s : ∀ x ≤ M,
          readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w t.mem x =
            fbStart x :=
        fun x hx => (readPacked_congr hw (hidx := show x < M + 1 by omega)
          (fun a ⟨ha1, ha2⟩ => hout a (Or.inr (Or.inl ⟨ha1, by
            dsimp only [M] at hfb_bt ha2; omega⟩)))).trans (hfb₀ x hx)
      have hlo_hi := hfb_adj j hb_lt
      obtain ⟨hcb_b, hcnt_le⟩ := hbnd j hb_lt
      set cnt := fbStart (j + 1) - fbStart j
      have hrep3b : BTreeSliceMemRep base c U V w n_max (3 * j) zeroBTreeSlice t.mem := by
        have hp := hprev (3 * j) (by omega)
        have hnot : ¬((3 * j) / 3 < j) := by omega
        rwa [ite_eq_right hnot] at hp
      obtain ⟨hin_fr, hin_vp, hin_rep, hin_oth, hin_bm, hin_out⟩ :=
        buildBktSliceLoop_spec (b := j) (salt := salts j) (cnt := cnt)
          henv hb_lt hcnt_le hcb_b (hbp_ps j hb_lt) hseed₀ hq₀ (hbp₀ j hb_lt) t hrep3b hout
      set inProg := buildBktSliceLoopProg (((((cp, base), (rt, hrt)), (j, salts j)), 0), cnt)
      set s_in := (Memory.spec 0).clientState t inProg
      have hin_step : StepSpec w (base + largeSpaceWhp c U V w n_max) t inProg s_in
          ((Memory.spec 0).clientResult t inProg) := ⟨rfl, rfl, hin_vp⟩
      have h16b1 : 16 * j + 1 < 16 * M := by omega
      have hs1 : StepSpec w (base + largeSpaceWhp c U V w n_max) t
          (buildAllBucketsOuterStepProg (((cp, base), (rt, hrt)), j)) s_in (j + 1) := by
        unfold buildAllBucketsOuterStepProg
        dsimp only [rt, mkHealRt, hlBase, hlW, hlTotalLoc, hlGBits, hlOffBm, hlOffFb] at hin_step ⊢
        simp only [pure_bind]
        refine (StepSpec.readPackedGen_eq hw (by omega) hfb_b (hfb_s j hb_lt.le)).bind ?_
        refine (StepSpec.readPackedGen_eq hw (by omega) hfb_b (hfb_s (j + 1) hb_lt)).bind ?_
        refine (StepSpec.readPackedGen_eq hw h16b1 hbm_b (hsalt_s j hb_lt)).bind ?_
        simp only [hlo_hi,
          show fbStart (j + 1) - fbStart j ≤ totalLocalCoordsWhp n_max from hcnt_le, ↓reduceIte]
        exact hin_step.bind (StepSpec.pure _ _)
      refine ⟨trivial, hs1.2.2, ?_⟩
      rw [hs1.1, hs1.2.1]
      refine ⟨by omega, fun sIdx hsIdx => ?_, fun b hb =>
        (hin_bm (16 * b + 1) (by omega) (by omega) (by omega)).trans (hsalt_s b hb),
        hin_out, hin_fr.trans hfr⟩
      by_cases heq3 : sIdx = 3 * j
      · subst heq3
        have hlt1 : (3 * j) / 3 < j + 1 := by omega
        rw [ite_eq_left hlt1]
        dsimp only [targetSlice]
        have hd : (3 * j) / 3 = j := by omega
        have hm : (3 * j) % 3 = 0 := by omega
        rw [hd, hm, ite_eq_left ⟨hb_lt, rfl⟩]
        exact hin_rep
      · have hp := hin_oth sIdx hsIdx heq3 _ (hprev sIdx hsIdx)
        by_cases hlt0 : sIdx / 3 < j
        · have hlt1 : sIdx / 3 < j + 1 := by omega
          rw [ite_eq_left hlt0] at hp; rw [ite_eq_left hlt1]; exact hp
        · by_cases hlt1 : sIdx / 3 < j + 1
          · have hdb : sIdx / 3 = j := by omega
            have hmr : sIdx % 3 ≠ 0 := by omega
            rw [ite_eq_right hlt0] at hp
            rw [ite_eq_left hlt1]
            dsimp only [targetSlice]
            rw [hdb, ite_eq_right (fun h => hmr h.2)]
            exact hp
          · rw [ite_eq_right hlt0] at hp
            rw [ite_eq_right hlt1]
            exact hp)
    ⟨rfl, hprev, hsalt, hout, rfl⟩
  rw [hj_eq] at hrep'
  exact ⟨hfr', hvp, hrep', hsalt', hout'⟩

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
