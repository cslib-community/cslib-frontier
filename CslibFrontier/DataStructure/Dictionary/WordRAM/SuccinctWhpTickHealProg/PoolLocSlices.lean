/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpTickHealProg.HealRt
import CslibFrontier.Tactic.Realize

/-!
# Pool Ownership, Free-Stack, `locState`, and Slice-Reset Loops for `csrToFastGenProg`

This internal module implements Phases D1, D2, D3, and E1 of `csrToFastGenProg`:
* **`fillPoolOwnerLoopProg`** (Phase D1): populates `offPoolOwner[poolIdx]` via
  `scanBucketLoopProg` over `offBktMeta[2 * x]`.
* **`fillFreeStackLoopProg`** (Phase D2): populates `offPoolFreeStack[j]` with unallocated backyard
  indices `totalBack + j`.
* **`fillLocStateOuterLoopProg`** (Phase D3): initializes per-bucket 2-bit `offLocState` entries to
  `1` on `[0, cnt)` and `0` on `[cnt, totalLoc)`.
* **`resetAllSlicesLoopProg`** (Phase E1): resets all `3 * M` SWAR B+-tree slices to
  `zeroBTreeSlice` while preserving odd `offBktMeta` entries.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.fillPoolOwnerLoopProg`,
  `fillFreeStackLoopProg`, `fillLocStateOuterLoopProg`, `resetAllSlicesLoopProg`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_fillPoolOwnerLoop`,
  `fillPoolOwnerLoop_safe`, `fillPoolOwnerLoop_spec`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_fillFreeStackLoop`,
  `fillFreeStackLoop_safe`, `fillFreeStackLoop_spec`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_fillLocStateOuterLoop`,
  `fillLocStateOuterLoop_safe`, `fillLocStateOuterLoop_spec`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_resetAllSlicesLoop`,
  `resetAllSlicesLoop_safe`, `resetAllSlicesLoop_spec`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind clientResult_bind)
open Cslib.DataStructure.WordRAM
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

/-! ## Phase D1: `fillPoolOwnerLoopProg` (populate `offPoolOwner[poolIdx]`) -/

/-- Single pool-slot step of `fillPoolOwnerLoopProg`. -/
@[irreducible] def fillPoolOwnerStepProg : (HealRt × ℕ) × ℕ → Memory.Prog ℕ
  | ((rt, tb_in), pid_in) => do
    let totalBack ← pure tb_in
    let poolIdx ← pure pid_in
    let zero_v ← pure 0
    let one_v ← pure 1
    let two_v ← pure 2
    let p1 ← pure (poolIdx + one_v)
    if poolIdx < totalBack then
      let sb ← scanBucketLoopProg
        (((((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), (two_v, poolIdx)), (zero_v, zero_v)),
         hlM rt)
      let b ← pure sb.2
      if b < hlM rt then
        let idxBm ← pure (2 * b)
        let bp_b ← readPackedGenProg (((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), idxBm)
        if bp_b ≤ poolIdx then
          let k ← pure (poolIdx - bp_b)
          if k < hlCB rt then
            let enc ← pure (b * hlCB rt + k)
            writePackedGenProg ((((hlBase rt, hlOffPo rt), (hlGBits rt, hlW rt)), poolIdx), enc)
            pure p1
          else
            writePackedGenProg
              ((((hlBase rt, hlOffPo rt), (hlGBits rt, hlW rt)), poolIdx), zero_v)
            pure p1
        else
          writePackedGenProg ((((hlBase rt, hlOffPo rt), (hlGBits rt, hlW rt)), poolIdx), zero_v)
          pure p1
      else
        writePackedGenProg ((((hlBase rt, hlOffPo rt), (hlGBits rt, hlW rt)), poolIdx), zero_v)
        pure p1
    else
      writePackedGenProg ((((hlBase rt, hlOffPo rt), (hlGBits rt, hlW rt)), poolIdx), zero_v)
      pure p1

private theorem memoryCost_fillPoolOwnerStep_pos (d : (HealRt × ℕ) × ℕ) (s : Memory.State) :
    0 < memoryCost (fillPoolOwnerStepProg d) s := by
  rcases d with ⟨⟨rt, tb⟩, pid⟩
  have hwp : ∀ y s', memoryCost (writePackedGenProg y) s' = 4 := fun _ _ => rfl
  unfold fillPoolOwnerStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
  split_ifs
  · rw [memoryCost_bind]
    split_ifs
    · rw [memoryCost_bind]
      split_ifs <;> (rw [memoryCost_bind, hwp]; omega)
    · rw [memoryCost_bind, hwp]; omega
  · rw [memoryCost_bind, hwp]; omega

/-- Precondition for `fillPoolOwnerStepProg`. -/
@[expose] def FillPoolOwnerPre (w : ℕ) : (HealRt × ℕ) × ℕ → Memory.State → Prop
  | ((rt, _totalBack), p), _s => HealRtEnvGen w rt ∧ p < hlPoolSize rt

private theorem realizes_fillPoolOwnerStep :
    Realizes .exact fillPoolOwnerStepProg
      (WordEncoding.encode (α := (HealRt × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      FillPoolOwnerPre
      (fun _ _ => 0) := by
  unfold fillPoolOwnerStepProg
  have hsbl := realizes_scanBucketLoop
  have hrp := realizes_readPackedGen
  have hwp := realizes_writePackedGen
  have hcs : ∀ y s', (Memory.spec 0).clientState s' (readPackedGenProg y) = s' := fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨⟨rt, totalBack⟩, poolIdx⟩
    dsimp only [FillPoolOwnerPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_rt⟩, hp_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize hlBase rt = base at henv heq_rt
    subst heq_rt
    obtain ⟨_, h16M, hMcb, hps_le, _, _, _, hgk⟩ := hl_bounds henv
    have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.2.2.1
    obtain ⟨hsb_sf, hsb_st, _, _⟩ :=
      scanBucketLoop_invariant (target := poolIdx) henv (Or.inr ⟨rfl, rfl⟩) (s := s)
    dsimp only [mkHealRt, hlBase, hlW, hlM, hlCB, hlPoolSize, hlGBits, hlOffBm, hlOffPo] at *
    simp only [hsb_st, hcs] at *
    first
    | exact henv.fits_const (by decide)
    | omega
    | exact henv.fits_of_le_n_max (by omega)
    | (refine henv.fits_of_le_n_max ?_
       exact (mul_add_lt_mul_bound (by assumption) (by assumption)).le.trans hMcb)
    | exact to_true_exists (henv.bktMeta_safe (idx := 2 * _) (by omega))
    | exact to_true_exists (henv.packed_safe_of_le hgk hp_lt hseg)
  )

/-- Loop populating `offPoolOwner`. -/
@[irreducible] def fillPoolOwnerLoopProg :
    ((HealRt × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | ((cfg, p₀), rem) => iterate fillPoolOwnerStepProg cfg rem p₀

/-- `Realizes .exact` certificate for `fillPoolOwnerLoopProg`. -/
theorem realizes_fillPoolOwnerLoop :
    Realizes .exact fillPoolOwnerLoopProg
      (WordEncoding.encode (α := ((HealRt × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cfg, p₀), rem) s =>
        iterationSafe fillPoolOwnerStepProg FillPoolOwnerPre w cfg rem p₀ s)
      (fun _ _ => 0) := by
  unfold fillPoolOwnerLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := HealRt × ℕ))
    (WordEncoding.encode (α := ℕ))
    realizes_fillPoolOwnerStep
    memoryCost_fillPoolOwnerStep_pos

/-- Loop-safety invariant for `fillPoolOwnerLoopProg`. -/
theorem fillPoolOwnerLoop_safe {c U V w n_max base totalBack : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let rt := mkHealRt c U V w n_max base
    ∀ rem p₀ (s : Memory.State),
      p₀ + rem ≤ poolSizeWhp n_max →
      iterationSafe fillPoolOwnerStepProg FillPoolOwnerPre w (rt, totalBack) rem p₀ s :=
  iterationSafe_of_stateless_step fillPoolOwnerStepProg FillPoolOwnerPre
    (fun _ hp _ => ⟨⟨c, U, V, w, n_max, henv, rfl⟩, hp⟩)
    (fun _ _ _ => by
      unfold fillPoolOwnerStepProg; dsimp only; simp only [pure_bind]
      split_ifs with hlt
      · rw [clientResult_bind]
        split_ifs with hb
        · rw [clientResult_bind]
          split_ifs <;> (rw [clientResult_bind]; rfl)
        · rw [clientResult_bind]; rfl
      · rw [clientResult_bind]; rfl)

/-- Exact memory specification of `fillPoolOwnerLoopProg`. -/
theorem fillPoolOwnerLoop_spec {c U V w n_max base : ℕ} {fbStart : ℕ → ℕ}
    {s₀ : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hback_cb : ∀ b < numBucketsWhp n_max,
      (fbStart (b + 1) - fbStart b) - capFrontWhp n_max < capBackWhp n_max)
    (hbp_mem : ∀ x ≤ numBucketsWhp n_max,
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s₀.mem (2 * x) =
        buildBackPrefix (numBucketsWhp n_max) (capFrontWhp n_max) fbStart x) :
    let rt := mkHealRt c U V w n_max base
    let M := numBucketsWhp n_max
    let cf := capFrontWhp n_max
    let cb := capBackWhp n_max
    let bp := buildBackPrefix M cf fbStart
    let findOwner : ℕ → ℕ := fun poolIdx =>
      let b := csrBucketOfIdx bp poolIdx M
      let k := poolIdx - bp b
      if poolIdx < bp M then b * cb + k else 0
    ∀ rem p₀ (s : Memory.State),
      p₀ + rem ≤ poolSizeWhp n_max →
      (∀ idx < p₀,
        readPacked (base + offPoolOwner c U V w n_max) (globalPtrBits n_max) w s.mem idx =
          findOwner idx) →
      (∀ a, (a < base + offPoolOwner c U V w n_max ∨ base + offBtMeta c U V w n_max ≤ a) →
        s.mem a = s₀.mem a) →
      let prog := fillPoolOwnerLoopProg (((rt, bp M), p₀), rem)
      let s' := (Memory.spec 0).clientState s prog
      s'.frontier = s.frontier ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      (∀ idx < p₀ + rem,
        readPacked (base + offPoolOwner c U V w n_max) (globalPtrBits n_max) w s'.mem idx =
          findOwner idx) ∧
      (∀ a, (a < base + offPoolOwner c U V w n_max ∨ base + offBtMeta c U V w n_max ≤ a) →
        s'.mem a = s₀.mem a) := by
  intro rt M cf cb bp findOwner rem
  have hw := henv.2.1
  have hM_pos : 0 < M := Nat.two_pow_pos _
  obtain ⟨_, _, hMcb, _, _, _, _, hgk⟩ := hl_bounds henv
  have hseg := WhpLargeEnv.seg_end_le c U V w n_max
  have hbm_b : base + offBktMeta c U V w n_max +
      packedWords (16 * M) (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.1 _
  have hpo_b : base + offPoolOwner c U V w n_max +
      packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.2.2.2.2.1 _
  have hpo_end : offPoolOwner c U V w n_max +
      packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w = offBtMeta c U V w n_max := rfl
  have hbm_le_po : offBktMeta c U V w n_max +
      packedWords (16 * M) (globalPtrBits n_max) w ≤ offPoolOwner c U V w n_max := by
    have h1 : offFbStart c U V w n_max =
      offBktMeta c U V w n_max + packedWords (16 * M) (globalPtrBits n_max) w := rfl
    unfold offPoolOwner offPoolFreeStack offBackAux offBackPtr; omega
  obtain ⟨hbp0, hbp_adj, _, _⟩ := backPrefix_spec M cf fbStart
  have hbp_le_step : ∀ b < M, bp b ≤ bp (b + 1) := fun b hb => by
    have h1 : bp (b + 1) = bp b + ((fbStart (b + 1) - fbStart b) - cf) := hbp_adj b hb
    omega
  induction rem with
  | zero =>
    intro p₀ s _ hprev hout
    unfold fillPoolOwnerLoopProg iterate
    rw [Nat.add_zero]
    exact ⟨rfl, validProg_pure _, hprev, hout⟩
  | succ rem ih =>
    intro p₀ s hle hprev hout
    have hp_lt : p₀ < poolSizeWhp n_max := by omega
    have hbp_s : ∀ x ≤ M,
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem (2 * x) =
          bp x := fun x hx =>
      (readPacked_congr hw (hidx := show 2 * x < 16 * M by omega)
        (fun a ⟨_, ha2⟩ => hout a (Or.inl (by dsimp only [M] at hbm_le_po ha2; omega)))).trans
        (hbp_mem x hx)
    set p1 := fillPoolOwnerStepProg ((rt, bp M), p₀)
    set m1 := writePacked (base + offPoolOwner c U V w n_max) (globalPtrBits n_max) w s.mem
      p₀ (findOwner p₀)
    have hown_pow : findOwner p₀ < 2 ^ globalPtrBits n_max := by
      dsimp only [findOwner]
      by_cases hlt : p₀ < bp M
      · obtain ⟨hb_i, hlo_i, hhi_i⟩ := csrBucketOfIdx_spec hbp0 hbp_le_step M le_rfl p₀ hlt
        have hk_cb : p₀ - bp (csrBucketOfIdx bp p₀ M) < cb := by
          have h1 : bp (csrBucketOfIdx bp p₀ M + 1) =
              bp (csrBucketOfIdx bp p₀ M) +
                ((fbStart (csrBucketOfIdx bp p₀ M + 1) - fbStart (csrBucketOfIdx bp p₀ M)) - cf) :=
            hbp_adj _ hb_i
          have h2 : (fbStart (csrBucketOfIdx bp p₀ M + 1) - fbStart (csrBucketOfIdx bp p₀ M)) - cf <
              cb := hback_cb _ hb_i
          change buildBackPrefix M cf fbStart (csrBucketOfIdx bp p₀ M) ≤ p₀ at hlo_i
          dsimp only [bp, cf, cb] at h1 h2 hlo_i hhi_i ⊢
          omega
        rw [ite_eq_left hlt]
        exact lt_two_pow_globalPtrBits_of_le_n_max ((mul_add_lt_mul_bound hb_i hk_cb).le.trans hMcb)
      · rw [ite_eq_right hlt]; exact Nat.two_pow_pos _
    have hs1 : StepSpec w (base + largeSpaceWhp c U V w n_max) s p1
        { mem := m1, frontier := s.frontier } (p₀ + 1) := by
      dsimp only [p1]; unfold fillPoolOwnerStepProg
      dsimp only [rt, mkHealRt, hlBase, hlW, hlM, hlCB, hlGBits, hlOffBm, hlOffPo]
      simp only [pure_bind]
      by_cases hlt : p₀ < bp M
      · obtain ⟨_, hsb_st, hsb_res, hsb_vp⟩ :=
          scanBucketLoop_invariant (target := p₀) henv (Or.inr ⟨rfl, rfl⟩) (s := s)
        have hsb_b : csrBucketOfIdx (fun x => readPacked (base + offBktMeta c U V w n_max)
            (globalPtrBits n_max) w s.mem (2 * x)) p₀ M = csrBucketOfIdx bp p₀ M :=
          csrBucketOfIdx_congr hbp_s
        rw [hsb_b] at hsb_res
        set b_i := csrBucketOfIdx bp p₀ M
        obtain ⟨hb_i, hlo_i, hhi_i⟩ := csrBucketOfIdx_spec hbp0 hbp_le_step M le_rfl p₀ hlt
        have hk_cb : p₀ - bp b_i < cb := by
          have h1 : bp (b_i + 1) = bp b_i + ((fbStart (b_i + 1) - fbStart b_i) - cf) :=
            hbp_adj b_i hb_i
          have h2 : (fbStart (b_i + 1) - fbStart b_i) - cf < cb := hback_cb b_i hb_i
          have hlo' : bp b_i ≤ p₀ := hlo_i
          have hhi' : p₀ < bp (b_i + 1) := hhi_i
          dsimp only [b_i, bp, cf, cb] at h1 h2 hlo' hhi' ⊢
          omega
        have h2bi : 2 * b_i < 16 * M :=
          (Nat.mul_lt_mul_of_pos_left hb_i two_pos).trans_le (Nat.mul_le_mul_right _ (by decide))
        have hown_eq : findOwner p₀ = b_i * cb + (p₀ - bp b_i) := ite_eq_left hlt
        have hsb_step : StepSpec w (base + largeSpaceWhp c U V w n_max) s _ s
            (numBucketsWhp n_max, b_i) :=
          ⟨hsb_st, hsb_res, hsb_vp⟩
        simp only [hlt, ↓reduceIte]
        refine hsb_step.bind ?_
        simp only [show b_i < numBucketsWhp n_max from hb_i, ↓reduceIte]
        refine (StepSpec.readPackedGen_eq hw h2bi hbm_b (hbp_s b_i hb_i.le)).bind ?_
        simp only [show bp b_i ≤ p₀ from hlo_i,
          show p₀ - bp b_i < capBackWhp n_max from hk_cb, ↓reduceIte]
        dsimp only [m1]; rw [hown_eq]
        exact (StepSpec.writePackedGen hw hgk hp_lt hpo_b).bind (StepSpec.pure _ _)
      · have hown0 : findOwner p₀ = 0 := ite_eq_right hlt
        simp only [hlt, ↓reduceIte]
        dsimp only [m1]; rw [hown0]
        exact (StepSpec.writePackedGen hw hgk hp_lt hpo_b).bind (StepSpec.pure _ _)
    set s1 : Memory.State := { mem := m1, frontier := s.frontier }
    have hprev1 : ∀ idx < p₀ + 1,
        readPacked (base + offPoolOwner c U V w n_max) (globalPtrBits n_max) w s1.mem idx =
          findOwner idx := by
      intro idx hidx
      dsimp only [s1, m1]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hidx with hlt | rfl
      · rw [readPacked_writePacked_of_ne hw _ (by omega)]; exact hprev idx hlt
      · exact readPacked_writePacked_self _ _ _ _ _ hown_pow
    have hout1 : ∀ a, (a < base + offPoolOwner c U V w n_max ∨ base + offBtMeta c U V w n_max ≤ a) →
        s1.mem a = s₀.mem a := by
      intro a ha; dsimp only [s1, m1]
      rw [writePacked_outside hw _ hp_lt _ (by omega)]; exact hout a ha
    obtain ⟨hf_r, hvp_r, hp_r, hout_r⟩ := ih (p₀ + 1) s1 (by omega) hprev1 hout1
    have hadd : p₀ + 1 + rem = p₀ + (rem + 1) := by omega
    rw [hadd] at hp_r
    unfold fillPoolOwnerLoopProg at hf_r hvp_r hp_r hout_r ⊢
    dsimp only [iterate]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hs1.1, hs1.2.1]; exact hf_r
    · refine validProg_bind hs1.2.2 ?_; rw [hs1.1, hs1.2.1]; exact hvp_r
    · intro idx hidx; rw [clientState_bind, hs1.1, hs1.2.1]; exact hp_r idx hidx
    · intro a ha; rw [clientState_bind, hs1.1, hs1.2.1]; exact hout_r a ha

/-! ## Phase D2: `fillFreeStackLoopProg` (populate `offPoolFreeStack[j]`) -/

/-- Single stack-slot step of `fillFreeStackLoopProg`. -/
@[irreducible] def fillFreeStackStepProg :
    (HealRt × (ℕ × ℕ)) × ℕ → Memory.Prog ℕ
  | ((rt, (tb_in, ft_in)), j_in) => do
    let totalBack ← pure tb_in
    let freeTop ← pure ft_in
    let j ← pure j_in
    let zero_v ← pure 0
    let one_v ← pure 1
    let j1 ← pure (j + one_v)
    if j < freeTop then
      if totalBack ≤ hlNMax rt then
        let remN ← pure (hlNMax rt - totalBack)
        if j ≤ remN then
          let v ← pure (totalBack + j)
          writePackedGenProg ((((hlBase rt, hlOffPs rt), (hlGBits rt, hlW rt)), j), v)
          pure j1
        else
          writePackedGenProg ((((hlBase rt, hlOffPs rt), (hlGBits rt, hlW rt)), j), zero_v)
          pure j1
      else
        writePackedGenProg ((((hlBase rt, hlOffPs rt), (hlGBits rt, hlW rt)), j), zero_v)
        pure j1
    else
      writePackedGenProg ((((hlBase rt, hlOffPs rt), (hlGBits rt, hlW rt)), j), zero_v)
      pure j1

private theorem memoryCost_fillFreeStackStep_pos
    (d : (HealRt × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    0 < memoryCost (fillFreeStackStepProg d) s := by
  rcases d with ⟨⟨rt, tb, ft⟩, j⟩
  unfold fillFreeStackStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
  split_ifs <;> (rw [memoryCost_bind]; change 0 < 4 + _; omega)

/-- Precondition for `fillFreeStackStepProg`. -/
@[expose] def FillFreeStackPre (w : ℕ) : (HealRt × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | ((rt, _bounds), j), _s => HealRtEnvGen w rt ∧ j < hlPoolSize rt

private theorem realizes_fillFreeStackStep :
    Realizes .exact fillFreeStackStepProg
      (WordEncoding.encode (α := (HealRt × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ))
      FillFreeStackPre
      (fun _ _ => 0) := by
  unfold fillFreeStackStepProg
  have hwp := realizes_writePackedGen
  realize
  all_goals (
    rcases d with ⟨⟨rt, tb, ft⟩, j⟩
    dsimp only [FillFreeStackPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_rt⟩, hj_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize hlBase rt = base at henv heq_rt
    subst heq_rt
    obtain ⟨_, _, _, hps_le, _, _, _, hgk⟩ := hl_bounds henv
    have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.2.1
    dsimp only [mkHealRt, hlBase, hlW, hlNMax, hlPoolSize, hlGBits, hlOffPs] at *
    first
    | exact henv.fits_const (by decide)
    | omega
    | exact henv.fits_of_le_n_max (by omega)
    | exact henv.packed_safe_of_le hgk hj_lt hseg
  )

/-- Loop populating `offPoolFreeStack`. -/
@[irreducible] def fillFreeStackLoopProg :
    ((HealRt × (ℕ × ℕ)) × ℕ) × ℕ → Memory.Prog ℕ
  | ((cfg, j₀), rem) => iterate fillFreeStackStepProg cfg rem j₀

/-- `Realizes .exact` certificate for `fillFreeStackLoopProg`. -/
theorem realizes_fillFreeStackLoop :
    Realizes .exact fillFreeStackLoopProg
      (WordEncoding.encode (α := ((HealRt × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cfg, j₀), rem) s =>
        iterationSafe fillFreeStackStepProg FillFreeStackPre w cfg rem j₀ s)
      (fun _ _ => 0) := by
  unfold fillFreeStackLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := HealRt × (ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ))
    realizes_fillFreeStackStep
    memoryCost_fillFreeStackStep_pos

/-- Loop-safety invariant for `fillFreeStackLoopProg`. -/
theorem fillFreeStackLoop_safe {c U V w n_max base tb ft : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let rt := mkHealRt c U V w n_max base
    ∀ rem j₀ (s : Memory.State),
      j₀ + rem ≤ poolSizeWhp n_max →
      iterationSafe fillFreeStackStepProg FillFreeStackPre w (rt, (tb, ft)) rem j₀ s :=
  iterationSafe_of_stateless_step fillFreeStackStepProg FillFreeStackPre
    (fun _ hj _ => ⟨⟨c, U, V, w, n_max, henv, rfl⟩, hj⟩)
    (fun _ _ _ => by
      unfold fillFreeStackStepProg; dsimp only [writePackedGenProg]; simp only [pure_bind]
      split_ifs <;> (rw [clientResult_bind]; rfl))

/-- Exact memory specification of `fillFreeStackLoopProg`. -/
theorem fillFreeStackLoop_spec {c U V w n_max base totalBack : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base)
    (htb_le : totalBack ≤ poolSizeWhp n_max) :
    let rt := mkHealRt c U V w n_max base
    let ps := poolSizeWhp n_max
    let freeTop := ps - totalBack
    ∀ rem j₀ (s : Memory.State),
      j₀ + rem ≤ ps →
      (∀ idx < j₀,
        readPacked (base + offPoolFreeStack c U V w n_max) (globalPtrBits n_max) w s.mem idx =
          if idx < freeTop then totalBack + idx else 0) →
      let prog := fillFreeStackLoopProg (((rt, (totalBack, freeTop)), j₀), rem)
      let s' := (Memory.spec 0).clientState s prog
      s'.frontier = s.frontier ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      (∀ idx < j₀ + rem,
        readPacked (base + offPoolFreeStack c U V w n_max) (globalPtrBits n_max) w s'.mem idx =
          if idx < freeTop then totalBack + idx else 0) ∧
      (∀ a, (a < base + offPoolFreeStack c U V w n_max ∨
          base + offPoolOwner c U V w n_max ≤ a) → s'.mem a = s.mem a) := by
  intro rt ps freeTop rem
  have hw := henv.2.1
  obtain ⟨_, _, _, hps_le, _, _, _, hgk⟩ := hl_bounds henv
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.2.1
  have hps_b : base + offPoolFreeStack c U V w n_max +
      packedWords ps (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
  have hps_end : offPoolFreeStack c U V w n_max +
      packedWords ps (globalPtrBits n_max) w = offPoolOwner c U V w n_max := rfl
  induction rem with
  | zero =>
    intro j₀ s _ hprev
    unfold fillFreeStackLoopProg iterate
    rw [Nat.add_zero]
    exact ⟨rfl, validProg_pure _, hprev, fun _ _ => rfl⟩
  | succ rem ih =>
    intro j₀ s hle hprev
    have hj_lt : j₀ < ps := by omega
    set vVal := if j₀ < freeTop then totalBack + j₀ else 0
    have hv_pow : vVal < 2 ^ globalPtrBits n_max := by
      dsimp only [vVal, freeTop, ps] at *
      split_ifs <;> exact lt_two_pow_globalPtrBits_of_le_n_max (by omega)
    set p1 := fillFreeStackStepProg ((rt, (totalBack, freeTop)), j₀)
    set m1 := writePacked (base + offPoolFreeStack c U V w n_max) (globalPtrBits n_max) w s.mem
      j₀ vVal
    have hs1 : StepSpec w (base + largeSpaceWhp c U V w n_max) s p1
        { mem := m1, frontier := s.frontier } (j₀ + 1) := by
      dsimp only [p1]; unfold fillFreeStackStepProg
      dsimp only [rt, mkHealRt, hlBase, hlW, hlNMax, hlGBits, hlOffPs]
      simp only [pure_bind]
      by_cases hjf : j₀ < freeTop
      · have h1 : totalBack ≤ n_max := htb_le.trans hps_le
        have h2 : j₀ ≤ n_max - totalBack := by dsimp only [freeTop, ps] at hjf hps_le; omega
        simp only [hjf, h1, h2, ↓reduceIte]
        dsimp only [m1, vVal]; simp only [hjf, ↓reduceIte]
        exact (StepSpec.writePackedGen hw hgk hj_lt hps_b).bind (StepSpec.pure _ _)
      · simp only [hjf, ↓reduceIte]
        dsimp only [m1, vVal]; simp only [hjf, ↓reduceIte]
        exact (StepSpec.writePackedGen hw hgk hj_lt hps_b).bind (StepSpec.pure _ _)
    set s1 : Memory.State := { mem := m1, frontier := s.frontier }
    have hprev1 : ∀ idx < j₀ + 1,
        readPacked (base + offPoolFreeStack c U V w n_max) (globalPtrBits n_max) w s1.mem idx =
          if idx < freeTop then totalBack + idx else 0 := by
      intro idx hidx
      dsimp only [s1, m1]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hidx with hlt | rfl
      · rw [readPacked_writePacked_of_ne hw _ (by omega)]; exact hprev idx hlt
      · exact readPacked_writePacked_self _ _ _ _ _ hv_pow
    obtain ⟨hf_r, hvp_r, hp_r, hout_r⟩ := ih (j₀ + 1) s1 (by omega) hprev1
    have hadd : j₀ + 1 + rem = j₀ + (rem + 1) := by omega
    rw [hadd] at hp_r
    unfold fillFreeStackLoopProg at hf_r hvp_r hp_r hout_r ⊢
    dsimp only [iterate]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hs1.1, hs1.2.1]; exact hf_r
    · refine validProg_bind hs1.2.2 ?_; rw [hs1.1, hs1.2.1]; exact hvp_r
    · intro idx hidx; rw [clientState_bind, hs1.1, hs1.2.1]; exact hp_r idx hidx
    · intro a ha
      rw [clientState_bind, hs1.1, hs1.2.1, hout_r a ha]
      dsimp only [ps] at hj_lt hps_end
      exact writePacked_outside hw _ hj_lt _ (by omega)

/-! ## Phase D3: `fillLocStateOuterLoopProg` (populate `offLocState`) -/

@[irreducible] private def fillLocStateInnerStepProg :
    (HealRt × (ℕ × ℕ)) × ℕ → Memory.Prog ℕ
  | ((rt, (b_in, cnt_in)), loc_in) => do
    let _ ← Memory.read (hlBase rt)
    let b ← pure b_in
    let cnt ← pure cnt_in
    let loc ← pure loc_in
    let zero_v ← pure 0
    let one_v ← pure 1
    let loc1 ← pure (loc + one_v)
    if loc < cnt then
      writeLocStateGenProg
        ((((hlBase rt, hlOffLs rt), (hlTotalLoc rt, hlW rt)), (b, loc)), one_v)
      pure loc1
    else
      writeLocStateGenProg
        ((((hlBase rt, hlOffLs rt), (hlTotalLoc rt, hlW rt)), (b, loc)), zero_v)
      pure loc1

private theorem memoryCost_fillLocStateInnerStep_pos
    (d : (HealRt × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    0 < memoryCost (fillLocStateInnerStepProg d) s := by
  rcases d with ⟨⟨rt, b, cnt⟩, loc⟩
  unfold fillLocStateInnerStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 0 < 1 + _
  omega

private def FillLocStateInnerPre (w : ℕ)
    (d : (HealRt × (ℕ × ℕ)) × ℕ) (_s : Memory.State) : Prop :=
  HealRtEnvGen w d.1.1 ∧ d.1.2.1 < hlM d.1.1 ∧ d.2 < hlTotalLoc d.1.1

private theorem realizes_fillLocStateInnerStep :
    Realizes .exact fillLocStateInnerStepProg
      (WordEncoding.encode (α := (HealRt × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ))
      FillLocStateInnerPre
      (fun _ _ => 0) := by
  unfold fillLocStateInnerStepProg
  have hwl := realizes_writeLocStateGen
  have hcs_r : ∀ a s', (Memory.spec 0).clientState s' (Memory.read a) = s' := fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨⟨rt, b, cnt⟩, loc⟩
    dsimp only [FillLocStateInnerPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_rt⟩, hb_lt, hloc_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize hlBase rt = base at henv heq_rt
    subst heq_rt
    obtain ⟨_, _, _, _, h2T, _, hw3, _⟩ := hl_bounds henv
    have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.1
    have hn_fit := henv.fits_of_le_n_max le_rfl
    dsimp only [mkHealRt, hlBase, hlW, hlM, hlTotalLoc, hlOffLs] at *
    simp only [hcs_r] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | (refine ⟨numBucketsWhp n_max, rfl, hw3, h2T.trans hn_fit, hb_lt, hloc_lt, ?_⟩
       refine henv.fits_largeSpace.of_le ?_
       rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _)
  )

@[irreducible] private def fillLocStateInnerLoopProg :
    ((HealRt × (ℕ × ℕ)) × ℕ) × ℕ → Memory.Prog ℕ
  | ((cfg, l₀), rem) => iterate fillLocStateInnerStepProg cfg rem l₀

private theorem realizes_fillLocStateInnerLoop :
    Realizes .exact fillLocStateInnerLoopProg
      (WordEncoding.encode (α := ((HealRt × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cfg, l₀), rem) s =>
        iterationSafe fillLocStateInnerStepProg FillLocStateInnerPre w cfg rem l₀ s)
      (fun _ _ => 0) := by
  unfold fillLocStateInnerLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := HealRt × (ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ))
    realizes_fillLocStateInnerStep
    memoryCost_fillLocStateInnerStep_pos

private theorem fillLocStateInnerLoop_safe {c U V w n_max base b cnt : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) (hb : b < numBucketsWhp n_max) :
    let rt := mkHealRt c U V w n_max base
    ∀ rem l₀ (s : Memory.State),
      l₀ + rem ≤ totalLocalCoordsWhp n_max →
      iterationSafe fillLocStateInnerStepProg FillLocStateInnerPre w
        (rt, (b, cnt)) rem l₀ s :=
  iterationSafe_of_stateless_step fillLocStateInnerStepProg FillLocStateInnerPre
    (fun _ hl _ => ⟨⟨c, U, V, w, n_max, henv, rfl⟩, hb, hl⟩)
    (fun _ _ s => by
      unfold fillLocStateInnerStepProg; dsimp only; simp only [pure_bind]
      rw [clientResult_bind]
      have hcs_r : (Memory.spec 0).clientState s
          (Memory.read (hlBase (mkHealRt c U V w n_max base))) = s := rfl
      rw [hcs_r]
      split_ifs <;> (rw [clientResult_bind]; rfl))

private theorem fillLocStateInnerLoop_spec {c U V w n_max base b cnt : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) :
    let rt := mkHealRt c U V w n_max base
    let M := numBucketsWhp n_max
    let totalLoc := totalLocalCoordsWhp n_max
    ∀ rem l₀ (s : Memory.State),
      l₀ + rem ≤ totalLoc →
      (∀ loc < l₀,
        readPacked (base + offLocState c U V w n_max) 2 w s.mem (b * totalLoc + loc) =
          if loc < cnt then 1 else 0) →
      let prog := fillLocStateInnerLoopProg (((rt, (b, cnt)), l₀), rem)
      let s' := (Memory.spec 0).clientState s prog
      s'.frontier = s.frontier ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      (∀ loc < l₀ + rem,
        readPacked (base + offLocState c U V w n_max) 2 w s'.mem (b * totalLoc + loc) =
          if loc < cnt then 1 else 0) ∧
      (∀ b' < M, b' ≠ b → ∀ loc < totalLoc,
        readPacked (base + offLocState c U V w n_max) 2 w s'.mem (b' * totalLoc + loc) =
          readPacked (base + offLocState c U V w n_max) 2 w s.mem (b' * totalLoc + loc)) ∧
      (∀ a, (a < base + offLocState c U V w n_max ∨ base + offBktMeta c U V w n_max ≤ a) →
        s'.mem a = s.mem a) := by
  intro rt M totalLoc rem
  have hw := henv.2.1
  have hls_end : offLocState c U V w n_max +
      packedWords (M * totalLoc) 2 w = offBktMeta c U V w n_max := rfl
  induction rem with
  | zero =>
    intro l₀ s _ hprev
    unfold fillLocStateInnerLoopProg iterate
    rw [Nat.add_zero]
    exact ⟨rfl, validProg_pure _, hprev, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  | succ rem ih =>
    intro l₀ s hle hprev
    have hl_lt : l₀ < totalLoc := by omega
    have hidx := mul_add_lt_mul_bound hb hl_lt
    set vVal := if l₀ < cnt then 1 else 0
    have hv_pow : vVal < 2 ^ 2 := by dsimp only [vVal]; split_ifs <;> decide
    obtain ⟨hwl_st, _, hwl_vp⟩ := writeLocStateGenProg_spec (b := b) (loc := l₀) (val := vVal)
      henv hb hl_lt (s := s)
    set p1 := fillLocStateInnerStepProg ((rt, (b, cnt)), l₀)
    set m1 := writePacked (base + offLocState c U V w n_max) 2 w s.mem (b * totalLoc + l₀) vVal
    have hbase_lt : base < base + largeSpaceWhp c U V w n_max := by
      have : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
      omega
    have hwl_step : StepSpec w (base + largeSpaceWhp c U V w n_max) s
        (writeLocStateGenProg
          ((((base, offLocState c U V w n_max), (totalLoc, w)), (b, l₀)), vVal))
        { mem := m1, frontier := s.frontier } () := ⟨hwl_st, rfl, hwl_vp⟩
    have hs1 : StepSpec w (base + largeSpaceWhp c U V w n_max) s p1
        { mem := m1, frontier := s.frontier } (l₀ + 1) := by
      dsimp only [p1]; unfold fillLocStateInnerStepProg
      dsimp only [rt, mkHealRt, hlBase, hlW, hlTotalLoc, hlOffLs]
      simp only [pure_bind]
      refine (StepSpec.read hbase_lt).bind ?_
      by_cases hlc : l₀ < cnt <;> (
        simp only [hlc, ↓reduceIte]
        dsimp only [vVal] at hwl_step
        simp only [hlc, ↓reduceIte] at hwl_step
        exact hwl_step.bind (StepSpec.pure _ _))
    set s1 : Memory.State := { mem := m1, frontier := s.frontier }
    have hprev1 : ∀ loc < l₀ + 1,
        readPacked (base + offLocState c U V w n_max) 2 w s1.mem (b * totalLoc + loc) =
          if loc < cnt then 1 else 0 := by
      intro loc hloc
      dsimp only [s1, m1]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hloc with hlt | rfl
      · rw [readPacked_writePacked_of_ne hw _ (by omega)]; exact hprev loc hlt
      · exact readPacked_writePacked_self _ _ _ _ _ hv_pow
    obtain ⟨hf_r, hvp_r, hp_r, hoth_r, hout_r⟩ := ih (l₀ + 1) s1 (by omega) hprev1
    have hadd : l₀ + 1 + rem = l₀ + (rem + 1) := by omega
    rw [hadd] at hp_r
    unfold fillLocStateInnerLoopProg at hf_r hvp_r hp_r hoth_r hout_r ⊢
    dsimp only [iterate]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hs1.1, hs1.2.1]; exact hf_r
    · refine validProg_bind hs1.2.2 ?_; rw [hs1.1, hs1.2.1]; exact hvp_r
    · intro loc hloc
      rw [clientState_bind, hs1.1, hs1.2.1]; exact hp_r loc hloc
    · intro b' hb' hne loc hloc
      rw [clientState_bind, hs1.1, hs1.2.1, hoth_r b' hb' hne loc hloc]
      have hne_idx : b' * totalLoc + loc ≠ b * totalLoc + l₀ := by
        intro heq
        have htl_pos : 0 < totalLoc := by omega
        have hd1 : (b' * totalLoc + loc) / totalLoc = b' := by
          rw [mul_comm, Nat.mul_add_div htl_pos, Nat.div_eq_of_lt hloc, Nat.add_zero]
        have hd2 : (b * totalLoc + l₀) / totalLoc = b := by
          rw [mul_comm, Nat.mul_add_div htl_pos, Nat.div_eq_of_lt hl_lt, Nat.add_zero]
        exact hne (by rw [← hd1, heq, hd2])
      exact readPacked_writePacked_of_ne hw _ hne_idx _
    · intro a ha
      rw [clientState_bind, hs1.1, hs1.2.1, hout_r a ha]
      dsimp only [M, totalLoc] at hidx hls_end
      exact writePacked_outside hw _ hidx _ (by omega)

/-- Single bucket step of `fillLocStateOuterLoopProg`. -/
@[irreducible] def fillLocStateOuterStepProg : HealRt × ℕ → Memory.Prog ℕ
  | (rt, b_in) => do
    let b ← pure b_in
    let zero_v ← pure 0
    let one_v ← pure 1
    let b1 ← pure (b + one_v)
    let lo ← readPackedGenProg (((hlBase rt, hlOffFb rt), (hlGBits rt, hlW rt)), b)
    let hi ← readPackedGenProg (((hlBase rt, hlOffFb rt), (hlGBits rt, hlW rt)), b1)
    if lo ≤ hi then
      let cnt ← pure (hi - lo)
      let _ ← fillLocStateInnerLoopProg (((rt, (b, cnt)), zero_v), hlTotalLoc rt)
      pure b1
    else
      let _ ← fillLocStateInnerLoopProg (((rt, (b, zero_v)), zero_v), hlTotalLoc rt)
      pure b1

private theorem memoryCost_fillLocStateOuterStep_pos (d : HealRt × ℕ) (s : Memory.State) :
    0 < memoryCost (fillLocStateOuterStepProg d) s := by
  rcases d with ⟨rt, b⟩
  unfold fillLocStateOuterStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 0 < 2 + _
  omega

private theorem realizes_fillLocStateOuterStep :
    Realizes .exact fillLocStateOuterStepProg
      (WordEncoding.encode (α := HealRt × ℕ))
      (WordEncoding.encode (α := ℕ))
      HealBktStepPre
      (fun _ _ => 0) := by
  unfold fillLocStateOuterStepProg
  have hrp := realizes_readPackedGen
  have hil := realizes_fillLocStateInnerLoop
  have hcs : ∀ y s', (Memory.spec 0).clientState s' (readPackedGenProg y) = s' := fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨rt, b⟩
    dsimp only [HealBktStepPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_rt⟩, hb_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize hlBase rt = base at henv heq_rt
    subst heq_rt
    obtain ⟨hM_lt, _, _, _, h2T, _, _, hgk⟩ := hl_bounds henv
    have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.1
    dsimp only [mkHealRt, hlBase, hlW, hlM, hlTotalLoc, hlGBits, hlOffFb] at *
    simp only [hcs] at *
    first
    | exact henv.fits_const (by decide)
    | omega
    | exact henv.fits_of_le_n_max (by omega)
    | exact to_true_exists (henv.packed_safe_of_le hgk (idx := b) (by omega) hseg)
    | exact to_true_exists (henv.packed_safe_of_le hgk (idx := b + 1) (by omega) hseg)
    | exact fillLocStateInnerLoop_safe henv hb_lt (totalLocalCoordsWhp n_max) 0 s (by omega)
  )

/-- Outer bucket loop populating `offLocState`. -/
@[irreducible] def fillLocStateOuterLoopProg : (HealRt × ℕ) × ℕ → Memory.Prog ℕ
  | ((rt, b₀), rem) => iterate fillLocStateOuterStepProg rt rem b₀

/-- `Realizes .exact` certificate for `fillLocStateOuterLoopProg`. -/
theorem realizes_fillLocStateOuterLoop :
    Realizes .exact fillLocStateOuterLoopProg
      (WordEncoding.encode (α := (HealRt × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((rt, b₀), rem) s =>
        iterationSafe fillLocStateOuterStepProg HealBktStepPre w rt rem b₀ s)
      (fun _ _ => 0) := by
  unfold fillLocStateOuterLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := HealRt))
    (WordEncoding.encode (α := ℕ))
    realizes_fillLocStateOuterStep
    memoryCost_fillLocStateOuterStep_pos

/-- Loop-safety invariant for `fillLocStateOuterLoopProg`. -/
theorem fillLocStateOuterLoop_safe {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let rt := mkHealRt c U V w n_max base
    ∀ rem b₀ (s : Memory.State),
      b₀ + rem ≤ numBucketsWhp n_max →
      iterationSafe fillLocStateOuterStepProg HealBktStepPre w rt rem b₀ s :=
  iterationSafe_of_stateless_step fillLocStateOuterStepProg HealBktStepPre
    (fun _ hb _ => ⟨⟨c, U, V, w, n_max, henv, rfl⟩, hb⟩)
    (fun _ _ _ => by
      unfold fillLocStateOuterStepProg; dsimp only [readPackedGenProg]; simp only [pure_bind]
      rw [clientResult_bind, clientState_readPackedProg,
        clientResult_bind, clientState_readPackedProg]
      split_ifs <;> (rw [clientResult_bind]; rfl))

/-- Exact memory specification of `fillLocStateOuterLoopProg`. -/
theorem fillLocStateOuterLoop_spec {c U V w n_max base : ℕ} {fbStart : ℕ → ℕ}
    {s₀ : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hfb_adj : ∀ b < numBucketsWhp n_max, fbStart b ≤ fbStart (b + 1))
    (hfb_mem : ∀ x ≤ numBucketsWhp n_max,
      readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s₀.mem x = fbStart x) :
    let rt := mkHealRt c U V w n_max base
    let M := numBucketsWhp n_max
    let totalLoc := totalLocalCoordsWhp n_max
    ∀ rem b₀ (s : Memory.State),
      b₀ + rem ≤ M →
      (∀ b < b₀, ∀ loc < totalLoc,
        readPacked (base + offLocState c U V w n_max) 2 w s.mem (b * totalLoc + loc) =
          if loc < fbStart (b + 1) - fbStart b then 1 else 0) →
      (∀ a, (a < base + offLocState c U V w n_max ∨ base + offBktMeta c U V w n_max ≤ a) →
        s.mem a = s₀.mem a) →
      let prog := fillLocStateOuterLoopProg ((rt, b₀), rem)
      let s' := (Memory.spec 0).clientState s prog
      s'.frontier = s.frontier ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      (∀ b < b₀ + rem, ∀ loc < totalLoc,
        readPacked (base + offLocState c U V w n_max) 2 w s'.mem (b * totalLoc + loc) =
          if loc < fbStart (b + 1) - fbStart b then 1 else 0) ∧
      (∀ a, (a < base + offLocState c U V w n_max ∨ base + offBktMeta c U V w n_max ≤ a) →
        s'.mem a = s₀.mem a) := by
  intro rt M totalLoc rem
  have hw := henv.2.1
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.1
  have hfb_b : base + offFbStart c U V w n_max +
      packedWords (M + 1) (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
  have hbm_le_fb : offBktMeta c U V w n_max ≤ offFbStart c U V w n_max := by
    unfold offFbStart; exact Nat.le_add_right _ _
  induction rem with
  | zero =>
    intro b₀ s _ hprev hout
    unfold fillLocStateOuterLoopProg iterate
    rw [Nat.add_zero]
    exact ⟨rfl, validProg_pure _, hprev, hout⟩
  | succ rem ih =>
    intro b₀ s hle hprev hout
    have hb_lt : b₀ < M := by omega
    have hfb_s : ∀ x ≤ M,
        readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem x = fbStart x :=
      fun x hx => (readPacked_congr hw (fun a ⟨ha1, _⟩ => hout a (Or.inr (by omega)))
        (Nat.lt_succ_of_le hx)).trans (hfb_mem x hx)
    have hlo_hi := hfb_adj b₀ hb_lt
    set cnt := fbStart (b₀ + 1) - fbStart b₀
    obtain ⟨hin_f, hin_vp, hin_l, hin_oth, hin_out⟩ := fillLocStateInnerLoop_spec
      (b := b₀) (cnt := cnt) henv hb_lt totalLoc 0 s (by omega)
      (fun _ h => absurd h (Nat.not_lt_zero _))
    rw [Nat.zero_add] at hin_l
    set inProg := fillLocStateInnerLoopProg (((rt, (b₀, cnt)), 0), totalLoc)
    set s_in := (Memory.spec 0).clientState s inProg
    have hin_step : StepSpec w (base + largeSpaceWhp c U V w n_max) s inProg s_in
        ((Memory.spec 0).clientResult s inProg) := ⟨rfl, rfl, hin_vp⟩
    set p1 := fillLocStateOuterStepProg (rt, b₀)
    have hs1 : StepSpec w (base + largeSpaceWhp c U V w n_max) s p1 s_in (b₀ + 1) := by
      dsimp only [p1]; unfold fillLocStateOuterStepProg
      dsimp only [rt, mkHealRt, hlBase, hlW, hlTotalLoc, hlGBits, hlOffFb] at hin_step ⊢
      simp only [pure_bind]
      refine (StepSpec.readPackedGen_eq hw (by omega) hfb_b (hfb_s b₀ hb_lt.le)).bind ?_
      refine (StepSpec.readPackedGen_eq hw (by omega) hfb_b (hfb_s (b₀ + 1) hb_lt)).bind ?_
      simp only [hlo_hi, ↓reduceIte]
      exact hin_step.bind (StepSpec.pure _ _)
    have hprev1 : ∀ b < b₀ + 1, ∀ loc < totalLoc,
        readPacked (base + offLocState c U V w n_max) 2 w s_in.mem (b * totalLoc + loc) =
          if loc < fbStart (b + 1) - fbStart b then 1 else 0 := by
      intro b hb loc hloc
      rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hlt | rfl
      · rw [hin_oth b (hlt.trans hb_lt) (by omega) loc hloc]; exact hprev b hlt loc hloc
      · exact hin_l loc hloc
    have hout1 : ∀ a, (a < base + offLocState c U V w n_max ∨
        base + offBktMeta c U V w n_max ≤ a) → s_in.mem a = s₀.mem a :=
      fun a ha => (hin_out a ha).trans (hout a ha)
    obtain ⟨hf_r, hvp_r, hp_r, hout_r⟩ := ih (b₀ + 1) s_in (by omega) hprev1 hout1
    have hadd : b₀ + 1 + rem = b₀ + (rem + 1) := by omega
    rw [hadd] at hp_r
    unfold fillLocStateOuterLoopProg at hf_r hvp_r hp_r hout_r ⊢
    dsimp only [iterate]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hs1.1, hs1.2.1]; exact hf_r.trans hin_f
    · refine validProg_bind hs1.2.2 ?_; rw [hs1.1, hs1.2.1]; exact hvp_r
    · intro b hb loc hloc
      rw [clientState_bind, hs1.1, hs1.2.1]; exact hp_r b hb loc hloc
    · intro a ha; rw [clientState_bind, hs1.1, hs1.2.1]; exact hout_r a ha

/-! ## Phase E1: `resetAllSlicesLoopProg` (reset all `3 * M` slices to `zeroBTreeSlice`) -/

/-- Single slice step of `resetAllSlicesLoopProg`. -/
@[irreducible] def resetAllSlicesStepProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, base_in), sIdx_in) => do
    let base ← pure base_in
    let sIdx ← pure sIdx_in
    let one_v ← pure 1
    resetBTreeSliceGenProg ((cp, base), sIdx)
    pure (sIdx + one_v)

private theorem memoryCost_resetAllSlicesStep_pos
    (d : (WhpCoreParams × ℕ) × ℕ) (s : Memory.State) :
    0 < memoryCost (resetAllSlicesStepProg d) s := by
  rcases d with ⟨⟨cp, base⟩, sIdx⟩
  unfold resetAllSlicesStepProg resetBTreeSliceGenProg writePackedGenProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 0 < 4 + (4 + 0)
  omega

/-- Precondition for `resetAllSlicesStepProg`. -/
@[expose] def ResetAllSlicesPre (w : ℕ) : (WhpCoreParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, base), sIdx), _s => WhpLargeEnvGen w cp base ∧ sIdx < 3 * wpM cp

private theorem realizes_resetAllSlicesStep :
    Realizes .exact resetAllSlicesStepProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      ResetAllSlicesPre
      (fun _ _ => 0) := by
  unfold resetAllSlicesStepProg
  have hrs := realizes_resetBTreeSliceGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, sIdx⟩
    dsimp only [ResetAllSlicesPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hsIdx⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h16M := sixteen_mul_numBuckets_le_n_max hth
    simp only [wp_large_M hth] at hsIdx
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | (simp only [wp_large_M hth]; exact hsIdx)
    | exact henv.fits_of_le_n_max (by omega)
  )

/-- Loop resetting all `3 * M` slices to `zeroBTreeSlice`. -/
@[irreducible] def resetAllSlicesLoopProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | ((cfg, s₀), rem) => iterate resetAllSlicesStepProg cfg rem s₀

/-- `Realizes .exact` certificate for `resetAllSlicesLoopProg`. -/
theorem realizes_resetAllSlicesLoop :
    Realizes .exact resetAllSlicesLoopProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cfg, s₀), rem) s =>
        iterationSafe resetAllSlicesStepProg ResetAllSlicesPre w cfg rem s₀ s)
      (fun _ _ => 0) := by
  unfold resetAllSlicesLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := WhpCoreParams × ℕ))
    (WordEncoding.encode (α := ℕ))
    realizes_resetAllSlicesStep
    memoryCost_resetAllSlicesStep_pos

/-- Loop-safety invariant for `resetAllSlicesLoopProg`. -/
theorem resetAllSlicesLoop_safe {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let cp := mkWhpCoreParams c U V w n_max
    ∀ rem s₀ (s : Memory.State),
      s₀ + rem ≤ 3 * numBucketsWhp n_max →
      iterationSafe resetAllSlicesStepProg ResetAllSlicesPre w (cp, base) rem s₀ s := by
  have hth := henv.2.2.2.1
  exact iterationSafe_of_stateless_step resetAllSlicesStepProg ResetAllSlicesPre
    (fun _ hs _ => ⟨⟨c, U, V, w, n_max, henv, rfl⟩, by rw [wp_large_M hth]; exact hs⟩)
    (fun _ _ _ => by
      unfold resetAllSlicesStepProg; simp only [pure_bind]; rw [clientResult_bind]; rfl)

/-- Exact memory specification of `resetAllSlicesLoopProg`. -/
theorem resetAllSlicesLoop_spec {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let cp := mkWhpCoreParams c U V w n_max
    let M := numBucketsWhp n_max
    ∀ rem s₀ (s : Memory.State),
      s₀ + rem ≤ 3 * M →
      (∀ sIdx < s₀, BTreeSliceMemRep base c U V w n_max sIdx zeroBTreeSlice s.mem) →
      let prog := resetAllSlicesLoopProg (((cp, base), s₀), rem)
      let s' := (Memory.spec 0).clientState s prog
      s'.frontier = s.frontier ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      (∀ sIdx < s₀ + rem, BTreeSliceMemRep base c U V w n_max sIdx zeroBTreeSlice s'.mem) ∧
      (∀ idx < 16 * M, idx % 16 = 1 →
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem idx =
          readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem idx) ∧
      (∀ a, (a < base + offBktMeta c U V w n_max ∨ base + offFbStart c U V w n_max ≤ a) →
        s'.mem a = s.mem a) := by
  intro cp M rem
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hnU := henv.2.2.2.2.1
  have hU := henv.2.2.2.2.2.1
  induction rem with
  | zero =>
    intro s₀ s _ hprev
    unfold resetAllSlicesLoopProg iterate
    rw [Nat.add_zero]
    exact ⟨rfl, validProg_pure _, hprev, fun _ _ _ => rfl, fun _ _ => rfl⟩
  | succ rem ih =>
    intro s₀ s hle hprev
    have hs_lt : s₀ < 3 * M := by omega
    obtain ⟨hfr1, _, hvp1, hrep1, hoth1, hbm1, hout1⟩ :=
      resetBTreeSliceGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max)
        (base := base) hth hw hnU hU hs_lt (s := s)
    set s1 := (Memory.spec 0).clientState s (resetBTreeSliceGenProg ((cp, base), s₀))
    set p1 := resetAllSlicesStepProg ((cp, base), s₀)
    have hs1_eq : StepSpec w (base + largeSpaceWhp c U V w n_max) s p1 s1 (s₀ + 1) := by
      dsimp only [p1]; unfold resetAllSlicesStepProg; simp only [pure_bind]
      exact StepSpec.bind ⟨rfl, rfl, hvp1⟩ (StepSpec.pure _ _)
    have hprev1 : ∀ sIdx < s₀ + 1,
        BTreeSliceMemRep base c U V w n_max sIdx zeroBTreeSlice s1.mem := by
      intro sIdx hsIdx
      rcases Nat.lt_succ_iff_lt_or_eq.mp hsIdx with hlt | rfl
      · exact hoth1 sIdx (hlt.trans hs_lt) (by omega) zeroBTreeSlice (hprev sIdx hlt)
      · exact hrep1
    obtain ⟨hfr_r, hvp_r, hrep_r, hbm_r, hout_r⟩ := ih (s₀ + 1) s1 (by omega) hprev1
    have hadd : s₀ + 1 + rem = s₀ + (rem + 1) := by omega
    rw [hadd] at hrep_r
    unfold resetAllSlicesLoopProg at hfr_r hvp_r hrep_r hbm_r hout_r ⊢
    dsimp only [iterate]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hs1_eq.1, hs1_eq.2.1]; exact hfr_r.trans hfr1
    · refine validProg_bind hs1_eq.2.2 ?_; rw [hs1_eq.1, hs1_eq.2.1]; exact hvp_r
    · intro sIdx hsIdx
      rw [clientState_bind, hs1_eq.1, hs1_eq.2.1]; exact hrep_r sIdx hsIdx
    · intro idx hidx hmod
      rw [clientState_bind, hs1_eq.1, hs1_eq.2.1, hbm_r idx hidx hmod]
      have hrole : s₀ % 3 < 3 := Nat.mod_lt _ (by decide)
      exact hbm1 idx hidx (by omega) (by omega)
    · intro a ha
      rw [clientState_bind, hs1_eq.1, hs1_eq.2.1, hout_r a ha]
      exact hout1 a ha

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
