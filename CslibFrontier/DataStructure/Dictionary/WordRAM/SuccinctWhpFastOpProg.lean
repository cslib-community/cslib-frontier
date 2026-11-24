/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg
import CslibFrontier.Tactic.Realize

/-!
# Fast-Mode Deletion and Guarded Insertion `Memory.Prog` Subroutines

This module completes the fast-mode foreground operation `Memory.Prog` subroutines and
`Realizes .exact` certificates on top of `SuccinctWhpFastBaseProg`:

1. `fastDeleteGenProg`: worst-case `O_c(1)` dense-coordinate deletion (`fastDeleteRemove`,
   `fastDeleteMoveLast`, `fastDeleteShrink`, and `overmarsStep`) preserving `FastStateStep` across
   all epoch rebuild stages (`0 .. 5`).
2. `fastInsertGenProg`: worst-case `O_c(1)` guarded insertion and overwrite refining `fastInsert`,
   evaluating all capacity, backyard-pool, Stage-1 `rKey`, and epoch-buffer guards before mutating
   memory so `clientState s prog = s` whenever `fastInsert` returns `none`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.readRebSliceIdxGenProg`,
  `fastDeleteGenProg`, `fastInsertGenProg`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_fastDeleteGen`,
  `fastDeleteGenProg_fastStep`, `realizes_fastInsertGen`, `fastInsertGenProg_spec`.
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
open Cslib.DataStructure.Dictionary.Dynamic (logLogFactor one_le_logLogFactor)
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

attribute [local simp] clientResult_pure_whp clientState_pure_whp
/-! ## Section 6: Fast-Mode Deletion (`fastDeleteGenProg`) -/

/-- Read `(fs.rebRole b, fs.overmarsRole b)` from bucket `b` metadata fields `2` and `4`
(`d = ((cp, base), b)`). -/
@[irreducible] def readRebAndOmRoleGenProg : (WhpCoreParams × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cp, base), b) => do
    let z0 ← pure 0
    let z3 ← pure 3
    let lr ← readBktFieldGenProg (((cp, base), b), 2)
    let orl ← readBktFieldGenProg (((cp, base), b), 4)
    let rRole ←
      if lr ≤ z3 then do
        let rem ← pure (z3 - lr)
        if orl ≤ rem then pure (rem - orl) else pure z0
      else
        pure z0
    pure (rRole, orl)

theorem realizes_readRebAndOmRoleGen :
    Realizes .exact readRebAndOmRoleGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((cp, base), b) _ => WhpLargeEnvGen w cp base ∧ b < wpM cp)
      (fun _ _ => 0) := by
  unfold readRebAndOmRoleGenProg
  have hrb := realizes_readBktFieldGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    simp only [wp_large_M hth] at *
    first
    | decide
    | omega
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
  )

theorem readRebAndOmRoleGenProg_spec {c U V w n_max base b : ℕ} {fs : FastState}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := readRebAndOmRoleGenProg ((mkWhpCoreParams c U V w n_max, base), b)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (if fs.liveRole b ≤ 3 ∧ fs.overmarsRole b ≤ 3 - fs.liveRole b
       then fs.rebRole b else 0, fs.overmarsRole b) ∧
    memoryCost prog s = 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  obtain ⟨h2_st, h2_res, h2_mc, h2_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 2 < 10) hrep (s := s)
  obtain ⟨h4_st, h4_res, h4_mc, h4_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 4 < 10) hrep (s := s)
  simp only [getBktField] at h2_res h4_res
  unfold readRebAndOmRoleGenProg FastState.rebRole
  simp only [pure_bind]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, h2_st, h2_res, clientState_bind, h4_st, h4_res]
    by_cases hlr3 : fs.liveRole b ≤ 3
    · simp only [hlr3, ↓reduceIte]; split_ifs <;> rfl
    · simp only [hlr3, ↓reduceIte]; rfl
  · rw [clientResult_bind, h2_st, h2_res, clientResult_bind, h4_st, h4_res]
    by_cases hlr3 : fs.liveRole b ≤ 3
    · simp only [hlr3, ↓reduceIte, true_and]
      by_cases hor3 : fs.overmarsRole b ≤ 3 - fs.liveRole b <;>
        simp only [hor3, ↓reduceIte, clientResult_pure_whp]
    · simp only [hlr3, ↓reduceIte, false_and, clientResult_pure_whp]
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [h2_st, h2_res, h2_mc, h4_st, h4_res, h4_mc]
    by_cases hlr3 : fs.liveRole b ≤ 3
    · simp only [hlr3, ↓reduceIte]
      by_cases hor3 : fs.overmarsRole b ≤ 3 - fs.liveRole b <;>
        simp [hor3]
    · simp [hlr3]
  · refine validProg_bind h2_vp ?_; rw [h2_st, h2_res]
    refine validProg_bind h4_vp ?_; rw [h4_st, h4_res]
    by_cases hlr3 : fs.liveRole b ≤ 3
    · simp only [hlr3, ↓reduceIte]
      by_cases hor3 : fs.overmarsRole b ≤ 3 - fs.liveRole b <;>
        (simp only [hor3, ↓reduceIte]; exact validProg_pure _)
    · simp only [hlr3, ↓reduceIte]; exact validProg_pure _

private theorem readRebAndOmRoleGenProg_fst_le (cp : WhpCoreParams) (base b : ℕ)
    (s : Memory.State) :
    ((Memory.spec 0).clientResult s (readRebAndOmRoleGenProg ((cp, base), b))).1 ≤ 3 := by
  unfold readRebAndOmRoleGenProg
  simp only [pure_bind, clientResult_bind]
  split_ifs <;> simp only [clientResult_pure_whp] <;> omega

/-- Read `fs.rebSliceIdx b = 3 * b + (3 - fs.liveRole b - fs.overmarsRole b)`
(`d = ((cp, base), b)`). -/
@[irreducible] def readRebSliceIdxGenProg : (WhpCoreParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, base), b) => do
    let ro ← readRebAndOmRoleGenProg ((cp, base), b)
    pure (3 * b + ro.1)

theorem realizes_readRebSliceIdxGen :
    Realizes .exact readRebSliceIdxGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cp, base), b) _ => WhpLargeEnvGen w cp base ∧ b < wpM cp)
      (fun _ _ => 0) := by
  unfold readRebSliceIdxGenProg
  have hro := realizes_readRebAndOmRoleGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h3M := (large_index_bounds hth).2.2.2.2.1
    have hfst := readRebAndOmRoleGenProg_fst_le (mkWhpCoreParams c U V w n_max) base b s
    simp only [wp_large_M hth] at *
    first
    | exact hb
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
  )

theorem readRebSliceIdxGenProg_spec {c U V w n_max base b : ℕ} {fs : FastState}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := readRebSliceIdxGenProg ((mkWhpCoreParams c U V w n_max, base), b)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = fs.rebSliceIdx b ∧
    memoryCost prog s = 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  obtain ⟨hro_st, hro_res, hro_mc, hro_vp⟩ :=
    readRebAndOmRoleGenProg_spec henv hb hrep (s := s)
  unfold readRebSliceIdxGenProg FastState.rebSliceIdx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, hro_st]; rfl
  · rw [clientResult_bind, hro_st, hro_res, clientResult_pure_whp]
    dsimp only [FastState.rebRole]
    split_ifs <;> omega
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hro_st, hro_mc]; simp
  · refine validProg_bind hro_vp ?_; rw [hro_st]; exact validProg_pure _

/-- Extract buffer and slice invariants on bucket `b` from `ValidFastState`. -/
private theorem validFastState_delete_bounds {c U V n_max b : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U}
    (hv : ValidFastState c U V n_max θ fs dict) (hb : b < numBucketsWhp n_max) :
    (∀ loc < fs.bktCount b, fs.locState b loc = 2 →
      (fs.buf 0).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
      (fs.buf 0).itemAlloc < qEpochWhp n_max ∧
      ∃ m0, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf 0) m0) ∧
    (∀ loc < fs.bktCount b, fs.locState b loc = 3 →
      (fs.buf 1).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
      (fs.buf 1).itemAlloc < qEpochWhp n_max ∧
      ∃ m1, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf 1) m1) ∧
    fs.liveSliceIdx b < 3 * numBucketsWhp n_max ∧
    fs.overmarsSliceIdx b < 3 * numBucketsWhp n_max ∧
    fs.rebSliceIdx b < 3 * numBucketsWhp n_max ∧
    fs.liveSliceIdx b ≠ fs.overmarsSliceIdx b ∧
    fs.liveSliceIdx b ≠ fs.rebSliceIdx b ∧
    fs.overmarsSliceIdx b ≠ fs.rebSliceIdx b ∧
    (fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
      ∃ lm, ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) lm) ∧
    (fs.overmarsActive b = 1 →
      fs.overmarsInsCount b < 8 * (slabScale n_max) ^ 12 ∧
      ∃ om, ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices (fs.overmarsSliceIdx b)) om) ∧
    (decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
        fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
        fs.rebCollision = 0) = true →
      fs.rebInsCount < 8 * (slabScale n_max) ^ 12 ∧
      ∃ rm, ValidWhpSlice n_max fs.rebInsCount (fs.slices (fs.rebSliceIdx b)) rm) := by
  have hL2 := two_le_slabScale n_max
  have hL12 : 4096 ≤ (slabScale n_max) ^ 12 :=
    (by decide : 4096 ≤ 2 ^ 12).trans (Nat.pow_le_pow_left hL2 12)
  have hcnt3 : fs.bktCount b ≤ 3 * (slabScale n_max) ^ 12 :=
    (hv.bktCount_le b hb).trans totalLocalCoordsWhp_le_three_mul
  obtain ⟨hlr, hor, hne_ro⟩ := hv.roles_valid b hb
  have hrr_lt : fs.rebRole b < 3 := by unfold FastState.rebRole; omega
  have hbuf_of_tag : ∀ ep, (ep = 0 ∨ ep = 1) →
      ∀ loc < fs.bktCount b, fs.locState b loc = 2 + ep →
        (fs.buf ep).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
        (fs.buf ep).itemAlloc < qEpochWhp n_max ∧
        ∃ mp, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf ep) mp := by
    intro ep hep loc hloc htag
    by_cases hce : ep = fs.curEp
    · subst hce
      obtain ⟨hia, hna, mp, hvb, _⟩ := hv.bufCur_valid
      obtain ⟨hc1, hc2⟩ := bufTrie_caps_of_bounds hv.hth hia hna
      exact ⟨hc1, hc2, mp, hvb⟩
    · have hoe : ep = fs.oldEp := by
        rcases hep with rfl | rfl <;> rcases hv.curEp_or with hc | hc <;>
          simp_all [FastState.oldEp]
      subst hoe
      have hbo := hv.bufOld_valid
      by_cases hs3 : fs.rebStage ≤ 3
      · rw [ite_eq_left hs3] at hbo
        obtain ⟨hia, hna, mp, hvb, _⟩ := hbo
        obtain ⟨hc1, hc2⟩ := bufTrie_caps_of_bounds hv.hth hia hna
        exact ⟨hc1, hc2, mp, hvb⟩
      · rw [ite_eq_right hs3] at hbo
        by_cases hs4 : fs.rebStage = 4
        · rw [ite_eq_left hs4] at hbo; exact absurd htag (hbo.1 b hb loc hloc)
        · rw [ite_eq_right hs4] at hbo; exact absurd htag (hbo.1 b hb loc hloc)
  refine ⟨fun loc hloc h2 => hbuf_of_tag 0 (Or.inl rfl) loc hloc h2,
    fun loc hloc h3 => hbuf_of_tag 1 (Or.inr rfl) loc hloc h3,
    by unfold FastState.liveSliceIdx; omega,
    by unfold FastState.overmarsSliceIdx; omega,
    by unfold FastState.rebSliceIdx; omega,
    by unfold FastState.liveSliceIdx FastState.overmarsSliceIdx; omega,
    by unfold FastState.liveSliceIdx FastState.rebSliceIdx FastState.rebRole; omega,
    by unfold FastState.overmarsSliceIdx FastState.rebSliceIdx FastState.rebRole; omega,
    ⟨liveInsCount_le_eight hv.toCore hb (hv.overmars_valid b hb),
     let ⟨lm, hvl, _⟩ := hv.live_valid b hb; ⟨lm, hvl⟩⟩,
    fun ha1 => ?_, fun hreb_b => ?_⟩
  · rcases hv.overmars_valid b hb with ⟨h0, _⟩ | ⟨_, _, hcur_lt, _, hins, om, hv_om, _⟩
    · omega
    · exact ⟨by omega, om, hv_om⟩
  · obtain ⟨hs2, _, hdb, hcs, _⟩ := of_decide_eq_true hreb_b
    have hstg := hv.stage_valid
    dsimp only [ValidEpochStage] at hstg
    simp only [hs2, show ¬(2 = 0) by decide, show ¬(2 = 1) by decide, ↓reduceIte] at hstg
    obtain ⟨hcur_r, _, rm, hv_rm, _⟩ := hstg.2.2.2.2.2.2 hcs
    rw [hdb] at hcur_r hv_rm
    rcases hcur_r with ⟨_, hi0⟩ | ⟨_, hcur_lt, hins⟩
    · exact ⟨by omega, rm, hv_rm⟩
    · exact ⟨by omega, rm, hv_rm⟩

private theorem loc_lt_two_pow_valLaneBits {n_max loc : ℕ}
    (hloc : loc < totalLocalCoordsWhp n_max) : loc < 2 ^ valLaneBitsWhp n_max := by
  have h3 := hloc.trans_le totalLocalCoordsWhp_le_three_mul
  have h256 : 2 ^ valLaneBitsWhp n_max = 256 * (slabScale n_max) ^ 12 := by
    have hsc : slabScale n_max = 2 ^ logLogFactor n_max := rfl
    unfold valLaneBitsWhp
    rw [hsc, Nat.pow_add, ← Nat.pow_mul, Nat.mul_comm _ 12]; ring
  have hL_pos : 0 < (slabScale n_max) ^ 12 := Nat.pow_pos (Nat.two_pow_pos _)
  omega

/-- Sub-helper 6.1a: delete `rKey_u` from `buf 0` (`st_del = 2`) or `buf 1` (`st_del = 3`). -/
@[irreducible] private def delRemBufGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, base), st_del), rKey_u) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let z2 ← pure 2
    let z3 ← pure 3
    if st_del = z2 then
      bufDeleteGenProg (((cp, base), z0), rKey_u)
    else if st_del = z3 then
      bufDeleteGenProg (((cp, base), z1), rKey_u)
    else
      pure ()

private theorem realizes_delRemBufGen :
    Realizes .exact delRemBufGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), st_del), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (st_del = 2 → ∃ m0, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf 0) m0) ∧
          (st_del = 3 → ∃ m1, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf 1) m1))
      (fun _ _ => 0) := by
  unfold delRemBufGenProg
  have hbd := realizes_bufDeleteGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, st_del⟩, rKey_u⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, h2, h3⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    first
    | exact henv.fits_const (by decide)
    | (obtain ⟨m0, hv0⟩ := h2 (by assumption)
       exact ⟨c, U, V, w, n_max, fs.buf 0, m0, henv, rfl, Or.inl rfl,
         hrep.buf_rep (Or.inl rfl), hv0⟩)
    | (obtain ⟨m1, hv1⟩ := h3 (by assumption)
       exact ⟨c, U, V, w, n_max, fs.buf 1, m1, henv, rfl, Or.inr rfl,
         hrep.buf_rep (Or.inr rfl), hv1⟩)
  )

private theorem delRemBufGenProg_fastStep {c U V w n_max base st_del rKey_u : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (h2 : st_del = 2 → ∃ m0, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf 0) m0)
    (h3 : st_del = 3 → ∃ m1, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf 1) m1)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := delRemBufGenProg (((mkWhpCoreParams c U V w n_max, base), st_del), rKey_u)
    let s' := (Memory.spec 0).clientState s prog
    let buf1 :=
      if st_del = 2 then
        Function.update fs.buf 0 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 0) rKey_u)
      else if st_del = 3 then
        Function.update fs.buf 1 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 1) rKey_u)
      else fs.buf
    memoryCost prog s ≤ 2 * cTabWhp c + 8 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ { fs with buf := buf1 } s s' := by
  dsimp only
  unfold delRemBufGenProg
  simp only [pure_bind]
  by_cases hs2 : st_del = 2
  · simp only [hs2, ↓reduceIte]
    obtain ⟨m0, hv0⟩ := h2 hs2
    obtain ⟨hmc, hvp, hstep⟩ :=
      bufDeleteGenProg_fastStep henv (Or.inl rfl) hseed hrep hv0 (rKey := rKey_u) (s := s)
    exact ⟨hmc, hvp, hstep⟩
  · simp only [hs2, ↓reduceIte]
    by_cases hs3 : st_del = 3
    · simp only [hs3, ↓reduceIte]
      obtain ⟨m1, hv1⟩ := h3 hs3
      obtain ⟨hmc, hvp, hstep⟩ :=
        bufDeleteGenProg_fastStep henv (Or.inr rfl) hseed hrep hv1 (rKey := rKey_u) (s := s)
      exact ⟨hmc, hvp, hstep⟩
    · simp only [hs3, ↓reduceIte]
      exact ⟨Nat.zero_le _, validProg_pure _, FastStateStep.refl hseed hrep⟩

/-- Sub-helper 6.1b: delete `fp_live_u` from `liveSlice[b]` when `inLiveTree` holds. -/
@[irreducible] private def delRemLiveGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, base), b), (st_del, fp_live_u)) => do
    let z1 ← pure 1
    let stg ← readHdrProg (base, hdrRebStage)
    let oldEp ← readOldEpProg base
    let doneB ← readBktFieldGenProg (((cp, base), b), 8)
    let inL ← inLiveTreeProg ((stg, oldEp), (doneB, st_del))
    if inL = z1 then do
      let lr ← readBktFieldGenProg (((cp, base), b), 2)
      let lIdx ← pure (3 * b + lr)
      btreeDeleteGenProg (((cp, base), lIdx), fp_live_u)
    else
      pure ()

private theorem realizes_delRemLiveGen :
    Realizes .exact delRemLiveGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), b), (_, fp_live_u)) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState) (lm : ℕ → Option ℕ),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          b < numBucketsWhp n_max ∧
          fs.liveRole b < 3 ∧
          fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
          ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) lm ∧
          fp_live_u < 2 ^ fpBitsWhp n_max)
      (fun _ _ => 0) := by
  unfold delRemLiveGenProg
  have hrh := realizes_readHdr
  have hro := realizes_readOldEp
  have hrb := realizes_readBktFieldGen
  have hil := realizes_inLiveTree
  have hbd := realizes_btreeDeleteGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, b⟩, ⟨st_del, fp_live_u⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, lm, henv, rfl, hrep, hce, hb, hlr, hins, hv_l, hfp⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h2w := henv.two_le_w
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have h3M := (large_index_bounds hth).2.2.2.2.1
    obtain ⟨hst_s, hres_s, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebStage)
      (by dsimp [hdrRebStage]; omega) (s := s)
    obtain ⟨hst_o, hres_o, _, _⟩ := readOldEpProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce
      hrep.2.2.2.1 (s := s)
    obtain ⟨hst_8, hres_8, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 8 < 10)
      hrep (s := s)
    obtain ⟨hst_2, hres_2, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 2 < 10)
      hrep (s := s)
    simp only [getBktField] at hres_8 hres_2
    obtain ⟨hst_il, _, _, _⟩ := inLiveTreeProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (rebStage := s.mem (base + hdrRebStage))
      (oldEp := fs.oldEp) (rebDoneB := fs.rebDoneFlag b) (st := st_del) (s := s)
    have hlIdx : fs.liveSliceIdx b < 3 * numBucketsWhp n_max := by
      unfold FastState.liveSliceIdx; omega
    have hold : fs.oldEp ≤ 1 := by rcases hce with hc | hc <;> simp [FastState.oldEp, hc]
    simp only [hst_s, hres_s, hst_o, hres_o, hst_8, hres_8, hst_2, hres_2, hst_il,
      wp_large_M hth] at *
    first
    | decide
    | exact h2w
    | exact hold
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact ⟨c, U, V, w, n_max, fs.liveInsCount b, fs.slices (fs.liveSliceIdx b), lm,
        henv, rfl, hlIdx, hins, hrep.slice_rep hlIdx, hv_l, hfp⟩
  )

private theorem delRemLiveGenProg_fastStep {c U V w n_max base b st_del fp_live_u : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {lm : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1)
    (hb : b < numBucketsWhp n_max) (hlr : fs.liveRole b < 3)
    (hins : fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12)
    (hv_l : ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) lm)
    (hfp : fp_live_u < 2 ^ fpBitsWhp n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := delRemLiveGenProg (((mkWhpCoreParams c U V w n_max, base), b), (st_del, fp_live_u))
    let s' := (Memory.spec 0).clientState s prog
    let lIdx := fs.liveSliceIdx b
    let slices1 :=
      if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then
        Function.update fs.slices lIdx
          (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs.slices lIdx) fp_live_u)
      else fs.slices
    memoryCost prog s ≤ 280 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ { fs with slices := slices1 } s s' := by
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hst_s, hres_s, hmc_s, hvp_s⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebStage)
    (by dsimp [hdrRebStage]; omega) (s := s)
  rw [hrep.2.2.2.2.2.1] at hres_s
  obtain ⟨hst_o, hres_o, hmc_o, hvp_o⟩ := readOldEpProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce
    hrep.2.2.2.1 (s := s)
  obtain ⟨hst_8, hres_8, hmc_8, hvp_8⟩ := readBktFieldGenProg_spec henv hb (by decide : 8 < 10)
    hrep (s := s)
  simp only [getBktField] at hres_8
  obtain ⟨hst_il, hres_il, hmc_il, hvp_il⟩ := inLiveTreeProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (rebStage := fs.rebStage) (oldEp := fs.oldEp)
    (rebDoneB := fs.rebDoneFlag b) (st := st_del) (s := s)
  dsimp only
  unfold delRemLiveGenProg
  simp only [cp, pure_bind]
  by_cases hin : inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del = true
  · rw [ite_eq_left hin] at hres_il ⊢
    obtain ⟨hst_2, hres_2, hmc_2, hvp_2⟩ := readBktFieldGenProg_spec henv hb (by decide : 2 < 10)
      hrep (s := s)
    simp only [getBktField] at hres_2
    have hlIdx : fs.liveSliceIdx b < 3 * numBucketsWhp n_max := by
      unfold FastState.liveSliceIdx; omega
    obtain ⟨hbd_mc, hbd_vp, hbd_step⟩ :=
      btreeDeleteGenProg_fastStep henv hlIdx hins hseed hrep hv_l hfp (s := s)
    have hl_def : 3 * b + fs.liveRole b = fs.liveSliceIdx b := rfl
    have hs'_eq : (Memory.spec 0).clientState s
        (readHdrProg (base, hdrRebStage) >>= fun stg =>
          readOldEpProg base >>= fun oldEp =>
          readBktFieldGenProg (((cp, base), b), 8) >>= fun doneB =>
          inLiveTreeProg ((stg, oldEp), (doneB, st_del)) >>= fun inL =>
          if inL = 1 then
            readBktFieldGenProg (((cp, base), b), 2) >>= fun lr =>
            btreeDeleteGenProg (((cp, base), 3 * b + lr), fp_live_u)
          else pure ()) =
        (Memory.spec 0).clientState s
          (btreeDeleteGenProg (((cp, base), fs.liveSliceIdx b), fp_live_u)) := by
      rw [clientState_bind, hst_s, hres_s, clientState_bind, hst_o, hres_o,
        clientState_bind, hst_8, hres_8, clientState_bind, hst_il, hres_il,
        ite_eq_left rfl, clientState_bind, hst_2, hres_2, hl_def]
    rw [hs'_eq]
    refine ⟨?_, ?_, hbd_step⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hst_s, hres_s, hmc_s, hst_o, hres_o, hmc_o, hst_8, hres_8, hmc_8,
        hst_il, hres_il, hmc_il, ite_eq_left rfl]
      simp only [memoryCost_bind]
      rw [hst_2, hres_2, hmc_2, hl_def]
      omega
    · refine validProg_bind hvp_s ?_; rw [hst_s, hres_s]
      refine validProg_bind hvp_o ?_; rw [hst_o, hres_o]
      refine validProg_bind hvp_8 ?_; rw [hst_8, hres_8]
      refine validProg_bind hvp_il ?_; rw [hst_il, hres_il, ite_eq_left rfl]
      refine validProg_bind hvp_2 ?_; rw [hst_2, hres_2, hl_def]
      exact hbd_vp
  · rw [ite_eq_right hin] at hres_il ⊢
    have hs'_eq : (Memory.spec 0).clientState s
        (readHdrProg (base, hdrRebStage) >>= fun stg =>
          readOldEpProg base >>= fun oldEp =>
          readBktFieldGenProg (((cp, base), b), 8) >>= fun doneB =>
          inLiveTreeProg ((stg, oldEp), (doneB, st_del)) >>= fun inL =>
          if inL = 1 then
            readBktFieldGenProg (((cp, base), b), 2) >>= fun lr =>
            btreeDeleteGenProg (((cp, base), 3 * b + lr), fp_live_u)
          else pure ()) = s := by
      rw [clientState_bind, hst_s, hres_s, clientState_bind, hst_o, hres_o,
        clientState_bind, hst_8, hres_8, clientState_bind, hst_il, hres_il,
        ite_eq_right (by decide : ¬(0 = 1))]; rfl
    rw [hs'_eq]
    refine ⟨?_, ?_, FastStateStep.refl hseed hrep⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hst_s, hres_s, hmc_s, hst_o, hres_o, hmc_o, hst_8, hres_8, hmc_8,
        hst_il, hres_il, hmc_il, ite_eq_right (by decide : ¬(0 = 1))]
      simp only [memoryCost_pure]; omega
    · refine validProg_bind hvp_s ?_; rw [hst_s, hres_s]
      refine validProg_bind hvp_o ?_; rw [hst_o, hres_o]
      refine validProg_bind hvp_8 ?_; rw [hst_8, hres_8]
      refine validProg_bind hvp_il ?_; rw [hst_il, hres_il, ite_eq_right (by decide : ¬(0 = 1))]
      exact validProg_pure _

/-- Active deletion helper for `delRemOmGenProg`: read `overmarsRole b` and delete `fp_live_u`
from `overmarsSlice[b]`. -/
@[irreducible] private def delRemOmDeleteProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, base), b), fp_live_u) => do
    let orl ← readBktFieldGenProg (((cp, base), b), 4)
    let omIdx ← pure (3 * b + orl)
    btreeDeleteGenProg (((cp, base), omIdx), fp_live_u)

private theorem realizes_delRemOmDelete :
    Realizes .exact delRemOmDeleteProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), b), fp_live_u) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState) (om : ℕ → Option ℕ),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.overmarsRole b < 3 ∧
          fs.overmarsInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
          ValidWhpSlice n_max (fs.overmarsInsCount b)
            (fs.slices (fs.overmarsSliceIdx b)) om ∧
          fp_live_u < 2 ^ fpBitsWhp n_max)
      (fun _ _ => 0) := by
  unfold delRemOmDeleteProg
  have hrb := realizes_readBktFieldGen
  have hbd := realizes_btreeDeleteGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, b⟩, fp_live_u⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, om, henv, rfl, hrep, hb, hor, hins_om, hv_om, hfp⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h3M := (large_index_bounds hth).2.2.2.2.1
    obtain ⟨hst_4, hres_4, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 4 < 10)
      hrep (s := s)
    simp only [getBktField] at hres_4
    have homIdx : fs.overmarsSliceIdx b < 3 * numBucketsWhp n_max := by
      unfold FastState.overmarsSliceIdx; omega
    simp only [hst_4, hres_4, wp_large_M hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact ⟨c, U, V, w, n_max, fs.overmarsInsCount b, fs.slices (fs.overmarsSliceIdx b), om,
        henv, rfl, homIdx, hins_om, hrep.slice_rep homIdx, hv_om, hfp⟩
  )

/-- Read `if inLiveTree rebStage oldEp (rebDoneFlag b) st then 1 else 0` without mutating memory.
-/
@[irreducible] private def readInLiveTagGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((cp, base), b), st) => do
    let stg ← readHdrProg (base, hdrRebStage)
    let oldEp ← readOldEpProg base
    let doneB ← readBktFieldGenProg (((cp, base), b), 8)
    inLiveTreeProg ((stg, oldEp), (doneB, st))

private theorem realizes_readInLiveTagGen :
    Realizes .exact readInLiveTagGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (((cp, base), b), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          b < numBucketsWhp n_max)
      (fun _ _ => 0) := by
  unfold readInLiveTagGenProg
  have hrh := realizes_readHdr
  have hro := realizes_readOldEp
  have hrb := realizes_readBktFieldGen
  have hil := realizes_inLiveTree
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, b⟩, st⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hce, hb⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h2w := henv.two_le_w
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hold : fs.oldEp ≤ 1 := by rcases hce with hc | hc <;> simp [FastState.oldEp, hc]
    obtain ⟨hst_s, hres_s, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebStage)
      (by dsimp [hdrRebStage]; omega) (s := s)
    obtain ⟨hst_o, hres_o, _, _⟩ := readOldEpProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce
      hrep.2.2.2.1 (s := s)
    obtain ⟨hst_8, hres_8, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 8 < 10)
      hrep (s := s)
    simp only [getBktField] at hres_8
    simp only [hst_s, hres_s, hst_o, hres_o, hst_8, hres_8, wp_large_M hth] at *
    first
    | decide
    | exact h2w
    | exact hold
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
  )

private theorem readInLiveTagGenProg_spec {c U V w n_max base b st : ℕ}
    {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1)
    (hb : b < numBucketsWhp n_max)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := readInLiveTagGenProg (((mkWhpCoreParams c U V w n_max, base), b), st)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st then 1 else 0) ∧
    memoryCost prog s ≤ 5 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  obtain ⟨hst_s, hres_s, hmc_s, hvp_s⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebStage)
    (by dsimp [hdrRebStage]; omega) (s := s)
  rw [hrep.2.2.2.2.2.1] at hres_s
  obtain ⟨hst_o, hres_o, hmc_o, hvp_o⟩ := readOldEpProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce
    hrep.2.2.2.1 (s := s)
  obtain ⟨hst_8, hres_8, hmc_8, hvp_8⟩ := readBktFieldGenProg_spec henv hb (by decide : 8 < 10)
    hrep (s := s)
  simp only [getBktField] at hres_8
  obtain ⟨hst_il, hres_il, hmc_il, hvp_il⟩ := inLiveTreeProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (rebStage := fs.rebStage) (oldEp := fs.oldEp)
    (rebDoneB := fs.rebDoneFlag b) (st := st) (s := s)
  dsimp only
  unfold readInLiveTagGenProg
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, hst_s, hres_s, clientState_bind, hst_o, hres_o,
      clientState_bind, hst_8, hres_8, hst_il]
  · rw [clientResult_bind, hst_s, hres_s, clientResult_bind, hst_o, hres_o,
      clientResult_bind, hst_8, hres_8, hres_il]
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hst_s, hres_s, hmc_s, hst_o, hres_o, hmc_o, hst_8, hres_8, hmc_8]; omega
  · refine validProg_bind hvp_s ?_; rw [hst_s, hres_s]
    refine validProg_bind hvp_o ?_; rw [hst_o, hres_o]
    refine validProg_bind hvp_8 ?_; rw [hst_8, hres_8]
    exact hvp_il

/-- Sub-helper 6.1c: delete `fp_live_u` from `overmarsSlice[b]` when active and `< overmarsCursor`.
-/
@[irreducible] private def delRemOmGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((((cp, base), b), loc_del), (st_del, fp_live_u)) => do
    let z1 ← pure 1
    let omAct ← readBktFieldGenProg (((cp, base), b), 5)
    let omCur ← readBktFieldGenProg (((cp, base), b), 6)
    let inL ← readInLiveTagGenProg (((cp, base), b), st_del)
    if omAct = z1 ∧ loc_del < omCur ∧ inL = z1 then
      delRemOmDeleteProg (((cp, base), b), fp_live_u)
    else
      pure ()

private theorem realizes_delRemOmGen :
    Realizes .exact delRemOmGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), _), (_, fp_live_u)) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          b < numBucketsWhp n_max ∧
          fs.overmarsRole b < 3 ∧
          (fs.overmarsActive b = 1 →
            fs.overmarsInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
            ∃ om, ValidWhpSlice n_max (fs.overmarsInsCount b)
              (fs.slices (fs.overmarsSliceIdx b)) om) ∧
          fp_live_u < 2 ^ fpBitsWhp n_max)
      (fun _ _ => 0) := by
  unfold delRemOmGenProg
  have hrb := realizes_readBktFieldGen
  have hil := realizes_readInLiveTagGen
  have hdo := realizes_delRemOmDelete
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, loc_del⟩, ⟨st_del, fp_live_u⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hce, hb, hor, hom_fn, hfp⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    obtain ⟨hst_5, hres_5, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 5 < 10)
      hrep (s := s)
    obtain ⟨hst_6, hres_6, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 6 < 10)
      hrep (s := s)
    obtain ⟨hst_il, _, _, _⟩ := readInLiveTagGenProg_spec henv hce hb hrep (st := st_del) (s := s)
    simp only [getBktField] at hres_5 hres_6
    simp only [hst_5, hres_5, hst_6, hres_6, hst_il, wp_large_M hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hce, hb⟩
    | (obtain ⟨hins_om, om, hv_om⟩ := hom_fn (by omega)
       exact ⟨c, U, V, w, n_max, fs, om, henv, rfl, hrep, hb, hor, hins_om, hv_om, hfp⟩)
  )

private theorem delRemOmGenProg_fastStep {c U V w n_max base b loc_del st_del fp_live_u : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1)
    (hb : b < numBucketsWhp n_max) (hor : fs.overmarsRole b < 3)
    (hom_fn : fs.overmarsActive b = 1 →
      fs.overmarsInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
      ∃ om, ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices (fs.overmarsSliceIdx b)) om)
    (hfp : fp_live_u < 2 ^ fpBitsWhp n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := delRemOmGenProg
      ((((mkWhpCoreParams c U V w n_max, base), b), loc_del), (st_del, fp_live_u))
    let s' := (Memory.spec 0).clientState s prog
    let omIdx := fs.overmarsSliceIdx b
    let slices2 :=
      if fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
          inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then
        Function.update fs.slices omIdx
          (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs.slices omIdx) fp_live_u)
      else fs.slices
    memoryCost prog s ≤ 285 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ { fs with slices := slices2 } s s' := by
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hst_5, hres_5, hmc_5, hvp_5⟩ := readBktFieldGenProg_spec henv hb (by decide : 5 < 10)
    hrep (s := s)
  obtain ⟨hst_6, hres_6, hmc_6, hvp_6⟩ := readBktFieldGenProg_spec henv hb (by decide : 6 < 10)
    hrep (s := s)
  obtain ⟨hst_il, hres_il, hmc_il, hvp_il⟩ :=
    readInLiveTagGenProg_spec henv hce hb hrep (st := st_del) (s := s)
  simp only [getBktField] at hres_5 hres_6
  have hcond_iff :
      (fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
        (if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then 1 else 0) = 1) ↔
      (fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
        inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del = true) := by
    cases inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del <;> simp
  dsimp only
  unfold delRemOmGenProg
  simp only [cp, pure_bind]
  by_cases hcond : fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
      inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del = true
  · rw [ite_eq_left hcond]
    have hcond_n := hcond_iff.mpr hcond
    obtain ⟨hins_om, om, hv_om⟩ := hom_fn hcond.1
    obtain ⟨hst_4, hres_4, hmc_4, hvp_4⟩ := readBktFieldGenProg_spec henv hb (by decide : 4 < 10)
      hrep (s := s)
    simp only [getBktField] at hres_4
    have homIdx : fs.overmarsSliceIdx b < 3 * numBucketsWhp n_max := by
      unfold FastState.overmarsSliceIdx; omega
    obtain ⟨hbd_mc, hbd_vp, hbd_step⟩ :=
      btreeDeleteGenProg_fastStep henv homIdx hins_om hseed hrep hv_om hfp (s := s)
    have hom_def : 3 * b + fs.overmarsRole b = fs.overmarsSliceIdx b := rfl
    have hs'_eq : (Memory.spec 0).clientState s
        (readBktFieldGenProg (((cp, base), b), 5) >>= fun omAct =>
          readBktFieldGenProg (((cp, base), b), 6) >>= fun omCur =>
          readInLiveTagGenProg (((cp, base), b), st_del) >>= fun inL =>
          if omAct = 1 ∧ loc_del < omCur ∧ inL = 1 then
            delRemOmDeleteProg (((cp, base), b), fp_live_u)
          else pure ()) =
        (Memory.spec 0).clientState s
          (btreeDeleteGenProg (((cp, base), fs.overmarsSliceIdx b), fp_live_u)) := by
      rw [clientState_bind, hst_5, hres_5, clientState_bind, hst_6, hres_6,
        clientState_bind, hst_il, hres_il, ite_eq_left hcond_n]
      unfold delRemOmDeleteProg; dsimp only; simp only [pure_bind]
      rw [clientState_bind, hst_4, hres_4, hom_def]
    rw [hs'_eq]
    refine ⟨?_, ?_, hbd_step⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hst_5, hres_5, hmc_5, hst_6, hres_6, hmc_6, hst_il, hres_il, ite_eq_left hcond_n]
      unfold delRemOmDeleteProg; dsimp only
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hst_4, hres_4, hmc_4, hom_def]
      omega
    · refine validProg_bind hvp_5 ?_; rw [hst_5, hres_5]
      refine validProg_bind hvp_6 ?_; rw [hst_6, hres_6]
      refine validProg_bind hvp_il ?_; rw [hst_il, hres_il, ite_eq_left hcond_n]
      unfold delRemOmDeleteProg; dsimp only; simp only [pure_bind]
      refine validProg_bind hvp_4 ?_; rw [hst_4, hres_4, hom_def]
      exact hbd_vp
  · rw [ite_eq_right hcond]
    have hncond_n : ¬(fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
        (if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then 1 else 0) = 1) :=
      fun h => hcond (hcond_iff.mp h)
    have hs'_eq : (Memory.spec 0).clientState s
        (readBktFieldGenProg (((cp, base), b), 5) >>= fun omAct =>
          readBktFieldGenProg (((cp, base), b), 6) >>= fun omCur =>
          readInLiveTagGenProg (((cp, base), b), st_del) >>= fun inL =>
          if omAct = 1 ∧ loc_del < omCur ∧ inL = 1 then
            delRemOmDeleteProg (((cp, base), b), fp_live_u)
          else pure ()) = s := by
      rw [clientState_bind, hst_5, hres_5, clientState_bind, hst_6, hres_6,
        clientState_bind, hst_il, hres_il, ite_eq_right hncond_n]; rfl
    rw [hs'_eq]
    refine ⟨?_, ?_, FastStateStep.refl hseed hrep⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hst_5, hres_5, hmc_5, hst_6, hres_6, hmc_6, hst_il, hres_il,
        ite_eq_right hncond_n, memoryCost_pure]
      omega
    · refine validProg_bind hvp_5 ?_; rw [hst_5, hres_5]
      refine validProg_bind hvp_6 ?_; rw [hst_6, hres_6]
      refine validProg_bind hvp_il ?_; rw [hst_il, hres_il, ite_eq_right hncond_n]
      exact validProg_pure _

/-- Guard helper for `delRemRebGenProg`: return `1` iff Stage 2 is actively scanning bucket `b`
past `loc_del` and `st_del ∈ {1, 2 + oldEp}`. -/
@[irreducible] private def delRemRebCheckProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | ((((cp, base), b), loc_del), st_del) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let z2 ← pure 2
    let rebAct ← readRebActiveBGenProg ((cp, base), b)
    let rebCur ← readHdrProg (base, hdrRebScanCursor)
    let oldEp ← readOldEpProg base
    let tagOld ← pure (z2 + oldEp)
    if rebAct = z1 ∧ loc_del < rebCur ∧ (st_del = z1 ∨ st_del = tagOld) then
      pure z1
    else
      pure z0

private theorem realizes_delRemRebCheck :
    Realizes .exact delRemRebCheckProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((((cp, base), _), _), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1))
      (fun _ _ => 0) := by
  unfold delRemRebCheckProg
  have hrb := realizes_readRebActiveBGen
  have hrh := realizes_readHdr
  have hro := realizes_readOldEp
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, loc_del⟩, st_del⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hce⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h2w := henv.two_le_w
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    obtain ⟨hst_ra, hres_ra, _, _⟩ := readRebActiveBGenProg_spec henv hrep (b := b) (s := s)
    obtain ⟨hst_rc, hres_rc, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebScanCursor)
      (by dsimp [hdrRebScanCursor]; omega) (s := s)
    obtain ⟨hst_o, hres_o, _, _⟩ := readOldEpProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce
      hrep.2.2.2.1 (s := s)
    have hdc_mem : s.mem (base + hdrDirtyCount) ≤ qEpochWhp n_max :=
      hrep.2.2.2.2.2.2.2.1.trans_le hrep.1
    have hfit_old : Fits w (2 + fs.oldEp) := by
      have h4 : 4 ≤ 2 ^ w := (by decide : 4 ≤ 2 ^ 2).trans (Nat.pow_le_pow_right two_pos h2w)
      have hold : fs.oldEp ≤ 1 := by rcases hce with hc | hc <;> simp [FastState.oldEp, hc]
      change 2 + fs.oldEp < 2 ^ w; omega
    simp only [hst_ra, hres_ra, hst_rc, hres_rc, hst_o, hres_o, wp_large_qEpoch hth] at *
    first
    | exact h2w
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hdc_mem
    | exact hfit_old
  )

/-- Evaluate `fpOfSaltOpt` on `rebCandSalt` and `u_val` without mutating memory. -/
@[irreducible] private def readCandFpGenProg : (WhpParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((wp, base), u_val) => do
    let cand ← readHdrProg (base, hdrRebCandSalt)
    let hrt ← mkHashRtGenProg (wp, base)
    fpOfSaltOptRtProg ((hrt, cand), u_val)

private theorem realizes_readCandFpGen :
    Realizes .exact readCandFpGenProg
      (WordEncoding.encode (α := (WhpParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((wp, base), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem)
      (fun _ _ => 0) := by
  unfold readCandFpGenProg
  have hrh := realizes_readHdr
  have hmh := realizes_mkHashRtGen
  have hfp := realizes_fpOfSaltOptRt
  realize
  all_goals (
    rcases d with ⟨⟨wp, base⟩, u_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, henv, heq_wp, hseed⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    obtain ⟨hst_cs, _, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebCandSalt)
      (by dsimp [hdrRebCandSalt]; omega) (s := s)
    obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    simp only [hst_cs, hmh_st, hmh_res] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
  )

/-- Active deletion helper for `delRemRebGenProg`: evaluate `fpOfSalt rebCandSalt u` and delete it
from `rebSlice[b]`. -/
@[irreducible] private def delRemRebActiveProg :
    ((WhpParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((wp, base), b), u_val) => do
    let fp_c ← readCandFpGenProg ((wp, base), u_val)
    let rIdx ← readRebSliceIdxGenProg ((wp.1, base), b)
    btreeDeleteGenProg (((wp.1, base), rIdx), fp_c)

private theorem realizes_delRemRebActive :
    Realizes .exact delRemRebActiveProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((wp, base), b), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (rm : ℕ → Option ℕ),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.rebSliceIdx b < 3 * numBucketsWhp n_max ∧
          fs.rebInsCount ≤ 8 * (slabScale n_max) ^ 12 ∧
          ValidWhpSlice n_max fs.rebInsCount (fs.slices (fs.rebSliceIdx b)) rm)
      (fun _ _ => 0) := by
  unfold delRemRebActiveProg
  have hrc := realizes_readCandFpGen
  have hrs := realizes_readRebSliceIdxGen
  have hbd := realizes_btreeDeleteGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, b⟩, u_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, rm, henv, heq_wp, hseed, hrep, hb, hrIdx, hins_r, hv_r⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hst_cs, hres_cs, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebCandSalt)
      (by dsimp [hdrRebCandSalt]; omega) (s := s)
    obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    obtain ⟨hfp_st, hfp_res, _, _⟩ :=
      fpOfSaltOptRtProg_spec (salt := s.mem (base + hdrRebCandSalt)) (kv := u_val)
        henv hseed (s := s)
    have hrc_st : (Memory.spec 0).clientState s
        (readCandFpGenProg ((mkWhpParams c U V w n_max, base), u_val)) = s := by
      unfold readCandFpGenProg
      rw [clientState_bind, hst_cs, hres_cs, clientState_bind, hmh_st, hmh_res, hfp_st]
    have hrc_res : (Memory.spec 0).clientResult s
        (readCandFpGenProg ((mkWhpParams c U V w n_max, base), u_val)) =
        (if hs : s.mem (base + hdrRebCandSalt) < sMaxWhp c n_max then
          if hu : u_val < U then fpHash c U n_max θ.2 ⟨s.mem (base + hdrRebCandSalt), hs⟩
            ⟨u_val, hu⟩ else 0
         else 0) := by
      unfold readCandFpGenProg
      rw [clientResult_bind, hst_cs, hres_cs, clientResult_bind, hmh_st, hmh_res, hfp_res]
    obtain ⟨hrs_st, hrs_res, _, _⟩ := readRebSliceIdxGenProg_spec henv hb hrep (s := s)
    have hfp_lt := fpOfSaltOpt_lt c U n_max (s.mem (base + hdrRebCandSalt)) u_val θ.2
    simp only [hcp_eq] at *
    simp only [hrc_st, hrc_res, hrs_st, hrs_res, wp_large_M hth] at *
    first
    | exact hb
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
    | exact ⟨c, U, V, w, n_max, fs.rebInsCount, fs.slices (fs.rebSliceIdx b), rm,
        henv, rfl, hrIdx, hins_r, hrep.slice_rep hrIdx, hv_r, hfp_lt⟩
  )

/-- Sub-helper 6.1d: delete `fpOfSalt rebCandSalt u` from `rebSlice[b]` when Stage 2 is actively
scanning bucket `b` past `loc_del`. -/
@[irreducible] private def delRemRebGenProg :
    (((WhpParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((((wp, base), b), loc_del), (st_del, u_val)) => do
    let z1 ← pure 1
    let act ← delRemRebCheckProg ((((wp.1, base), b), loc_del), st_del)
    if act = z1 then
      delRemRebActiveProg (((wp, base), b), u_val)
    else
      pure ()

private theorem realizes_delRemRebGen :
    Realizes .exact delRemRebGenProg
      (WordEncoding.encode (α := (((WhpParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((((wp, base), b), _), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          b < numBucketsWhp n_max ∧
          fs.rebSliceIdx b < 3 * numBucketsWhp n_max ∧
          (decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
              fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
              fs.rebCollision = 0) = true →
            fs.rebInsCount ≤ 8 * (slabScale n_max) ^ 12 ∧
            ∃ rm, ValidWhpSlice n_max fs.rebInsCount (fs.slices (fs.rebSliceIdx b)) rm))
      (fun _ _ => 0) := by
  unfold delRemRebGenProg
  have hck := realizes_delRemRebCheck
  have hac := realizes_delRemRebActive
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨wp, base⟩, b⟩, loc_del⟩, ⟨st_del, u_val⟩⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, heq_wp, hseed, hrep, hce, hb, hrIdx, hreb_fn⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hst_ra, hres_ra, _, _⟩ := readRebActiveBGenProg_spec henv hrep (b := b) (s := s)
    obtain ⟨hst_rc, hres_rc, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebScanCursor)
      (by dsimp [hdrRebScanCursor]; omega) (s := s)
    obtain ⟨hst_o, hres_o, _, _⟩ := readOldEpProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce
      hrep.2.2.2.1 (s := s)
    have hck_st : (Memory.spec 0).clientState s
        (delRemRebCheckProg
          ((((mkWhpCoreParams c U V w n_max, base), b), loc_del), st_del)) = s := by
      unfold delRemRebCheckProg
      simp only [pure_bind]
      rw [clientState_bind, hst_ra, hres_ra, clientState_bind, hst_rc, hres_rc,
        clientState_bind, hst_o, hres_o]
      split_ifs <;> rfl
    have hck_res : (Memory.spec 0).clientResult s
        (delRemRebCheckProg ((((mkWhpCoreParams c U V w n_max, base), b), loc_del), st_del)) = 1 →
        decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
          fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
          fs.rebCollision = 0) = true := by
      unfold delRemRebCheckProg
      simp only [pure_bind]
      rw [clientResult_bind, hst_ra, hres_ra, clientResult_bind, hst_rc, hres_rc,
        clientResult_bind, hst_o, hres_o]
      intro h1
      by_cases hcond : (if decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
            fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
            fs.rebCollision = 0) then 1 else 0) = 1 ∧
          loc_del < s.mem (base + hdrRebScanCursor) ∧ (st_del = 1 ∨ st_del = 2 + fs.oldEp)
      · cases hd : decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
            fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
            fs.rebCollision = 0)
        · have h01 : (0 : ℕ) = 1 := by simpa [hd] using hcond.1
          cases h01
        · rfl
      · rw [ite_eq_right hcond, clientResult_pure_whp] at h1
        cases h1
    simp only [hcp_eq] at *
    simp only [hck_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hce⟩
    | (obtain ⟨hins_r, rm, hv_r⟩ := hreb_fn (hck_res (by assumption))
       exact ⟨c, U, V, w, n_max, θ, fs, rm, henv, rfl, hseed, hrep, hb, hrIdx, hins_r, hv_r⟩)
  )

private theorem delRemRebGenProg_fastStep {c U V w n_max base b loc_del st_del : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State} (u : Fin U)
    (henv : WhpLargeEnv c U V w n_max w base)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1)
    (hb : b < numBucketsWhp n_max)
    (hrIdx : fs.rebSliceIdx b < 3 * numBucketsWhp n_max)
    (hreb_fn : decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
        fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
        fs.rebCollision = 0) = true →
      fs.rebInsCount ≤ 8 * (slabScale n_max) ^ 12 ∧
      ∃ rm, ValidWhpSlice n_max fs.rebInsCount (fs.slices (fs.rebSliceIdx b)) rm)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := delRemRebGenProg
      ((((mkWhpParams c U V w n_max, base), b), loc_del), (st_del, u.val))
    let s' := (Memory.spec 0).clientState s prog
    let rebActiveB : Bool :=
      decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
        fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
        fs.rebCollision = 0)
    let rIdx := fs.rebSliceIdx b
    let slices3 :=
      if rebActiveB && decide (loc_del < fs.rebScanCursor ∧
          (st_del = 1 ∨ st_del = 2 + fs.oldEp)) then
        Function.update fs.slices rIdx
          (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs.slices rIdx) (fpOfSalt c U n_max θ.2 fs.rebCandSalt u))
      else fs.slices
    memoryCost prog s ≤ hashEvalCostWhp c + 290 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ { fs with slices := slices3 } s s' := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hst_ra, hres_ra, hmc_ra, hvp_ra⟩ := readRebActiveBGenProg_spec henv hrep (b := b) (s := s)
  obtain ⟨hst_rc, hres_rc, hmc_rc, hvp_rc⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebScanCursor)
    (by dsimp [hdrRebScanCursor]; omega) (s := s)
  rw [hrep.2.2.2.2.2.2.2.2.2.2.1] at hres_rc
  obtain ⟨hst_o, hres_o, hmc_o, hvp_o⟩ := readOldEpProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce
    hrep.2.2.2.1 (s := s)
  set rebActiveB : Bool :=
    decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
      fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
      fs.rebCollision = 0)
  have hcond_iff :
      ((if rebActiveB then 1 else 0) = 1 ∧ loc_del < fs.rebScanCursor ∧
        (st_del = 1 ∨ st_del = 2 + fs.oldEp)) ↔
      (rebActiveB && decide (loc_del < fs.rebScanCursor ∧
        (st_del = 1 ∨ st_del = 2 + fs.oldEp))) = true := by
    cases rebActiveB <;> simp
  have hck_st : (Memory.spec 0).clientState s
      (delRemRebCheckProg ((((cp, base), b), loc_del), st_del)) = s := by
    unfold delRemRebCheckProg; simp only [pure_bind]
    rw [clientState_bind, hst_ra, hres_ra, clientState_bind, hst_rc, hres_rc,
      clientState_bind, hst_o, hres_o]
    split_ifs <;> rfl
  have hck_mc : memoryCost (delRemRebCheckProg ((((cp, base), b), loc_del), st_del)) s ≤ 10 := by
    unfold delRemRebCheckProg
    simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hst_ra, hres_ra, hst_rc, hres_rc, hmc_rc, hst_o, hres_o, hmc_o]
    have hra_mc' : memoryCost (readRebActiveBGenProg ((cp, base), b)) s ≤ 7 := hmc_ra
    split_ifs <;> (simp only [memoryCost_pure]; omega)
  have hck_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
      (delRemRebCheckProg ((((cp, base), b), loc_del), st_del)) := by
    unfold delRemRebCheckProg; simp only [pure_bind]
    refine validProg_bind hvp_ra ?_; rw [hst_ra, hres_ra]
    refine validProg_bind hvp_rc ?_; rw [hst_rc, hres_rc]
    refine validProg_bind hvp_o ?_; rw [hst_o, hres_o]
    split_ifs <;> exact validProg_pure _
  dsimp only
  unfold delRemRebGenProg
  dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
  simp only [pure_bind]
  by_cases hcond : (rebActiveB && decide (loc_del < fs.rebScanCursor ∧
      (st_del = 1 ∨ st_del = 2 + fs.oldEp))) = true
  · rw [ite_eq_left hcond]
    have hcond_n := hcond_iff.mpr hcond
    have hck_res : (Memory.spec 0).clientResult s
        (delRemRebCheckProg ((((cp, base), b), loc_del), st_del)) = 1 := by
      unfold delRemRebCheckProg; simp only [pure_bind]
      rw [clientResult_bind, hst_ra, hres_ra, clientResult_bind, hst_rc, hres_rc,
        clientResult_bind, hst_o, hres_o, ite_eq_left hcond_n]; rfl
    have hrbt : rebActiveB = true := (Bool.and_eq_true _ _).mp hcond |>.1
    obtain ⟨hins_r, rm, hv_r⟩ := hreb_fn hrbt
    obtain ⟨hst_cs, hres_cs, hmc_cs, hvp_cs⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebCandSalt)
      (by dsimp [hdrRebCandSalt]; omega) (s := s)
    rw [hrep.2.2.2.2.2.2.2.2.2.1] at hres_cs
    obtain ⟨hmh_st, hmh_res, hmh_mc, hmh_vp⟩ :=
      mkHashRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base) hth s
    obtain ⟨hfp_st, hfp_res, hfp_mc, hfp_vp⟩ :=
      fpOfSaltOptRtProg_spec (salt := fs.rebCandSalt) (kv := u.val) henv hseed (s := s)
    have hfp_eq : (if hs : fs.rebCandSalt < sMaxWhp c n_max then
        if hu : u.val < U then fpHash c U n_max θ.2 ⟨fs.rebCandSalt, hs⟩ ⟨u.val, hu⟩ else 0
       else 0) = fpOfSalt c U n_max θ.2 fs.rebCandSalt u := by
      unfold fpOfSalt
      split_ifs with hs hu <;> first | rfl | exact absurd u.isLt hu
    rw [hfp_eq] at hfp_res
    obtain ⟨hrs_st, hrs_res, hrs_mc, hrs_vp⟩ := readRebSliceIdxGenProg_spec henv hb hrep (s := s)
    have hfp_lt : fpOfSalt c U n_max θ.2 fs.rebCandSalt u < 2 ^ fpBitsWhp n_max := by
      rw [← hfp_eq]; exact fpOfSaltOpt_lt c U n_max _ _ θ.2
    obtain ⟨hbd_mc, hbd_vp, hbd_step⟩ :=
      btreeDeleteGenProg_fastStep henv hrIdx hins_r hseed hrep hv_r hfp_lt (s := s)
    have hrc_st : (Memory.spec 0).clientState s
        (readCandFpGenProg ((mkWhpParams c U V w n_max, base), u.val)) = s := by
      unfold readCandFpGenProg
      rw [clientState_bind, hst_cs, hres_cs, clientState_bind, hmh_st, hmh_res, hfp_st]
    have hrc_res : (Memory.spec 0).clientResult s
        (readCandFpGenProg ((mkWhpParams c U V w n_max, base), u.val)) =
        fpOfSalt c U n_max θ.2 fs.rebCandSalt u := by
      unfold readCandFpGenProg
      rw [clientResult_bind, hst_cs, hres_cs, clientResult_bind, hmh_st, hmh_res, hfp_res]
    have hs'_eq : (Memory.spec 0).clientState s
        (delRemRebCheckProg ((((cp, base), b), loc_del), st_del) >>= fun act =>
          if act = 1 then
            delRemRebActiveProg (((mkWhpParams c U V w n_max, base), b), u.val)
          else pure ()) =
        (Memory.spec 0).clientState s
          (btreeDeleteGenProg
            (((cp, base), fs.rebSliceIdx b), fpOfSalt c U n_max θ.2 fs.rebCandSalt u)) := by
      rw [clientState_bind, hck_st, hck_res, ite_eq_left rfl]
      unfold delRemRebActiveProg; dsimp only
      rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
      rw [clientState_bind, hrc_st, hrc_res, clientState_bind, hrs_st, hrs_res]
    rw [hs'_eq]
    refine ⟨?_, ?_, hbd_step⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hck_st, hck_res, ite_eq_left rfl]
      unfold delRemRebActiveProg; dsimp only
      rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
      simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hrc_st, hrc_res, hrs_st, hrs_res, hrs_mc]
      have hrc_mc : memoryCost (readCandFpGenProg ((mkWhpParams c U V w n_max, base), u.val)) s ≤
          hashEvalCostWhp c + 1 := by
        unfold readCandFpGenProg
        simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hst_cs, hres_cs, hmc_cs, hmh_st, hmh_res, hmh_mc]
        have hfp_mc' : memoryCost (fpOfSaltOptRtProg ((mkHashRt c U w n_max base, fs.rebCandSalt),
            u.val)) s ≤ hashEvalCostWhp c := hfp_mc
        omega
      dsimp only [cp] at hck_mc hbd_mc ⊢
      omega
    · refine validProg_bind hck_vp ?_; rw [hck_st, hck_res, ite_eq_left rfl]
      unfold delRemRebActiveProg; dsimp only
      rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
      have hrc_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
          (readCandFpGenProg ((mkWhpParams c U V w n_max, base), u.val)) := by
        unfold readCandFpGenProg
        refine validProg_bind hvp_cs ?_; rw [hst_cs, hres_cs]
        refine validProg_bind hmh_vp ?_; rw [hmh_st, hmh_res]
        exact hfp_vp
      refine validProg_bind hrc_vp ?_; rw [hrc_st, hrc_res]
      refine validProg_bind hrs_vp ?_; rw [hrs_st, hrs_res]
      exact hbd_vp
  · rw [ite_eq_right hcond]
    have hncond_n : ¬((if rebActiveB then 1 else 0) = 1 ∧ loc_del < fs.rebScanCursor ∧
        (st_del = 1 ∨ st_del = 2 + fs.oldEp)) :=
      fun h => hcond (hcond_iff.mp h)
    have hck_res : (Memory.spec 0).clientResult s
        (delRemRebCheckProg ((((cp, base), b), loc_del), st_del)) = 0 := by
      unfold delRemRebCheckProg; simp only [pure_bind]
      rw [clientResult_bind, hst_ra, hres_ra, clientResult_bind, hst_rc, hres_rc,
        clientResult_bind, hst_o, hres_o, ite_eq_right hncond_n]; rfl
    have hs'_eq : (Memory.spec 0).clientState s
        (delRemRebCheckProg ((((cp, base), b), loc_del), st_del) >>= fun act =>
          if act = 1 then
            delRemRebActiveProg (((mkWhpParams c U V w n_max, base), b), u.val)
          else pure ()) = s := by
      rw [clientState_bind, hck_st, hck_res, ite_eq_right (by decide : ¬(0 = 1))]; rfl
    rw [hs'_eq]
    refine ⟨?_, ?_, FastStateStep.refl hseed hrep⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hck_st, hck_res, ite_eq_right (by decide : ¬(0 = 1)), memoryCost_pure]
      omega
    · refine validProg_bind hck_vp ?_
      rw [hck_st, hck_res, ite_eq_right (by decide : ¬(0 = 1))]
      exact validProg_pure _

/-- Read `(st_del, (rKey_u, fp_live_u))` for `fastDeleteRemoveGenProg` without mutating memory. -/
@[irreducible] private def delRemReadInfoGenProg :
    (((WhpParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((((wp, base), b), loc_del), u_val) => do
    let st_del ← readFastLocGenProg (((wp.1, base), b), loc_del)
    let hrt ← mkHashRtGenProg (wp, base)
    let rKey_u ← fpReducedKeyOptRtProg (hrt, u_val)
    let salt_b ← readBktFieldGenProg (((wp.1, base), b), 1)
    let fp_live_u ← fpOfSaltOptRtProg ((hrt, salt_b), u_val)
    pure (st_del, (rKey_u, fp_live_u))

private theorem realizes_delRemReadInfoGen :
    Realizes .exact delRemReadInfoGenProg
      (WordEncoding.encode (α := (((WhpParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ((((wp, base), b), loc_del), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          loc_del < totalLocalCoordsWhp n_max)
      (fun _ _ => 0) := by
  unfold delRemReadInfoGenProg
  have hrl := realizes_readFastLocGen
  have hmh := realizes_mkHashRtGen
  have hrk := realizes_fpReducedKeyOptRt
  have hrb := realizes_readBktFieldGen
  have hfp := realizes_fpOfSaltOptRt
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨wp, base⟩, b⟩, loc_del⟩, u_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, heq_wp, hseed, hrep, hb, hld_tl⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hst_l, _, _, _⟩ := readFastLocGenProg_spec henv hb hld_tl hrep (s := s)
    obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    obtain ⟨hrk_st, _, _, _⟩ := fpReducedKeyOptRtProg_spec (kv := u_val) henv hseed (s := s)
    obtain ⟨hs1_st, hs1_res, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 1 < 10)
      hrep (s := s)
    simp only [getBktField] at hs1_res
    obtain ⟨hfp_st, _, _, _⟩ :=
      fpOfSaltOptRtProg_spec (salt := fs.bktSalt b) (kv := u_val) henv hseed (s := s)
    simp only [hcp_eq] at *
    simp only [hst_l, hmh_st, hmh_res, hrk_st, hs1_st, hs1_res, hfp_st,
      wp_large_M hth, wp_large_totalLoc hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact hld_tl
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
  )

private theorem delRemReadInfoGenProg_spec {c U V w n_max base b loc_del : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State} (u : Fin U)
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hb : b < numBucketsWhp n_max)
    (hld_tl : loc_del < totalLocalCoordsWhp n_max) :
    let prog := delRemReadInfoGenProg ((((mkWhpParams c U V w n_max, base), b), loc_del), u.val)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (fs.locState b loc_del,
       (fpReducedKey c U n_max θ.2 u, fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)) ∧
    memoryCost prog s ≤ hashEvalCostWhp c + 5 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hst_l, hres_l, hmc_l, hvp_l⟩ := readFastLocGenProg_spec henv hb hld_tl hrep (s := s)
  obtain ⟨hmh_st, hmh_res, hmh_mc, hmh_vp⟩ :=
    mkHashRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base) hth s
  obtain ⟨hrk_st, hrk_res, hrk_mc, hrk_vp⟩ :=
    fpReducedKeyOptRtProg_spec (kv := u.val) henv hseed (s := s)
  obtain ⟨hs1_st, hs1_res, hs1_mc, hs1_vp⟩ := readBktFieldGenProg_spec henv hb (by decide : 1 < 10)
    hrep (s := s)
  simp only [getBktField] at hs1_res
  obtain ⟨hfp_st, hfp_res, hfp_mc, hfp_vp⟩ :=
    fpOfSaltOptRtProg_spec (salt := fs.bktSalt b) (kv := u.val) henv hseed (s := s)
  have hrk_eq : (if hu' : u.val < U then fpReducedKey c U n_max θ.2 ⟨u.val, hu'⟩ else 0) =
      fpReducedKey c U n_max θ.2 u := dite_eq_left u.isLt
  have hfp_eq : (if hs : fs.bktSalt b < sMaxWhp c n_max then
      if hu' : u.val < U then fpHash c U n_max θ.2 ⟨fs.bktSalt b, hs⟩ ⟨u.val, hu'⟩ else 0
     else 0) = fpOfSalt c U n_max θ.2 (fs.bktSalt b) u := by
    unfold fpOfSalt
    split_ifs with hs hu' <;> first | rfl | exact absurd u.isLt hu'
  rw [hrk_eq] at hrk_res
  rw [hfp_eq] at hfp_res
  dsimp only
  unfold delRemReadInfoGenProg
  dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, hst_l, hres_l, clientState_bind, hmh_st, hmh_res,
      clientState_bind, hrk_st, hrk_res, clientState_bind, hs1_st, hs1_res,
      clientState_bind, hfp_st, hfp_res]; rfl
  · rw [clientResult_bind, hst_l, hres_l, clientResult_bind, hmh_st, hmh_res,
      clientResult_bind, hrk_st, hrk_res, clientResult_bind, hs1_st, hs1_res,
      clientResult_bind, hfp_st, hfp_res]; rfl
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hst_l, hres_l, hmc_l, hmh_st, hmh_res, hmh_mc, hrk_st, hrk_res,
      hs1_st, hs1_res, hs1_mc, hfp_st, hfp_res, memoryCost_pure]
    have hrk_mc' : memoryCost (fpReducedKeyOptRtProg (mkHashRt c U w n_max base, u.val)) s ≤ 1 :=
      hrk_mc
    have hfp_mc' : memoryCost (fpOfSaltOptRtProg ((mkHashRt c U w n_max base, fs.bktSalt b),
        u.val)) s ≤ hashEvalCostWhp c := hfp_mc
    omega
  · refine validProg_bind hvp_l ?_; rw [hst_l, hres_l]
    refine validProg_bind hmh_vp ?_; rw [hmh_st, hmh_res]
    refine validProg_bind hrk_vp ?_; rw [hrk_st, hrk_res]
    refine validProg_bind hs1_vp ?_; rw [hs1_st, hs1_res]
    refine validProg_bind hfp_vp ?_; rw [hfp_st, hfp_res]
    exact validProg_pure _

/-- Core `WhpCoreParams` removal sequence (`buf`, `liveSlice`, `overmarsSlice`) for
`fastDeleteRemoveGenProg`. -/
@[irreducible] private def delRemCoreGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | ((((cp, base), b), loc_del), (st_del, (rKey_u, fp_live_u))) => do
    delRemBufGenProg (((cp, base), st_del), rKey_u)
    delRemLiveGenProg (((cp, base), b), (st_del, fp_live_u))
    delRemOmGenProg ((((cp, base), b), loc_del), (st_del, fp_live_u))

private theorem realizes_delRemCoreGen :
    Realizes .exact delRemCoreGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), loc_del), (st_del, (_, fp_live_u))) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          b < numBucketsWhp n_max ∧
          loc_del < fs.bktCount b ∧
          st_del = fs.locState b loc_del ∧
          fp_live_u < 2 ^ fpBitsWhp n_max)
      (fun _ _ => 0) := by
  unfold delRemCoreGenProg
  have db1 := realizes_delRemBufGen
  have db2 := realizes_delRemLiveGen
  have db3 := realizes_delRemOmGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, loc_del⟩, ⟨st_del, ⟨rKey_u, fp_live_u⟩⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv, hb, hld,
      rfl, hfp_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    obtain ⟨hb0, hb1, _, _, _, hne_lo, _, _, ⟨hlic_le, lm, hv_l⟩, hom_fn, _⟩ :=
      validFastState_delete_bounds hv hb
    set st_del := fs.locState b loc_del
    obtain ⟨_, _, hst1⟩ := delRemBufGenProg_fastStep henv
      (fun h2 => (hb0 loc_del hld h2).2.2) (fun h3 => (hb1 loc_del hld h3).2.2)
      hseed hrep (st_del := st_del) (rKey_u := rKey_u) (s := s)
    set s1 := (Memory.spec 0).clientState s
      (delRemBufGenProg (((mkWhpCoreParams c U V w n_max, base), st_del), rKey_u))
    set buf1 :=
      if st_del = 2 then
        Function.update fs.buf 0 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 0) rKey_u)
      else if st_del = 3 then
        Function.update fs.buf 1 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 1) rKey_u)
      else fs.buf
    set fs_b : FastState := { fs with buf := buf1 }
    obtain ⟨_, _, hst2⟩ := delRemLiveGenProg_fastStep (fs := fs_b) henv hv.curEp_or hb
      (hv.roles_valid b hb).1 hlic_le hv_l hfp_lt hst1.2.1 hst1.2.2.1 (st_del := st_del) (s := s1)
    set slices1 :=
      if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then
        Function.update fs.slices (fs.liveSliceIdx b)
          (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs.slices (fs.liveSliceIdx b)) fp_live_u)
      else fs.slices
    set fs_l : FastState := { fs_b with slices := slices1 }
    have hom_fn2 : fs_l.overmarsActive b = 1 →
        fs_l.overmarsInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
        ∃ om, ValidWhpSlice n_max (fs_l.overmarsInsCount b)
          (fs_l.slices (fs_l.overmarsSliceIdx b)) om := by
      intro ha1
      obtain ⟨hins_o, om, hv_o⟩ := hom_fn ha1
      refine ⟨hins_o.le, om, ?_⟩
      change ValidWhpSlice n_max (fs.overmarsInsCount b) (slices1 (fs.overmarsSliceIdx b)) om
      dsimp only [slices1]
      by_cases hin : inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del = true
      · rw [ite_eq_left hin, Function.update_of_ne hne_lo.symm]; exact hv_o
      · rw [ite_eq_right hin]; exact hv_o
    first
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep,
        fun h2 => (hb0 loc_del hld h2).2.2, fun h3 => (hb1 loc_del hld h3).2.2⟩
    | exact ⟨c, U, V, w, n_max, fs_b, lm, henv, rfl, hst1.2.2.1, hv.curEp_or, hb,
        (hv.roles_valid b hb).1, hlic_le, hv_l, hfp_lt⟩
    | exact ⟨c, U, V, w, n_max, fs_l, henv, rfl, hst2.2.2.1, hv.curEp_or, hb,
        (hv.roles_valid b hb).2.1, hom_fn2, hfp_lt⟩
  )

/-- Complete Substep 1 (`fastDeleteRemove`): remove `(u, loc_del)` from epoch buffers and slices
(`d = ((((wp, base), b), loc_del), u_val)`). -/
@[irreducible] private def fastDeleteRemoveGenProg :
    (((WhpParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | ((((wp, base), b), loc_del), u_val) => do
    let info ← delRemReadInfoGenProg ((((wp, base), b), loc_del), u_val)
    delRemCoreGenProg ((((wp.1, base), b), loc_del), info)
    delRemRebGenProg ((((wp, base), b), loc_del), (info.1, u_val))

private theorem realizes_fastDeleteRemoveGen :
    Realizes .exact fastDeleteRemoveGenProg
      (WordEncoding.encode (α := (((WhpParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((((wp, base), b), loc_del), u_val) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          b < numBucketsWhp n_max ∧
          loc_del < fs.bktCount b ∧
          u_val < U)
      (fun _ _ => 0) := by
  unfold fastDeleteRemoveGenProg
  have hri := realizes_delRemReadInfoGen
  have hdc := realizes_delRemCoreGen
  have db4 := realizes_delRemRebGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨wp, base⟩, b⟩, loc_del⟩, u_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hv, hb, hld, hu⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    set u : Fin U := ⟨u_val, hu⟩
    have hld_tl : loc_del < totalLocalCoordsWhp n_max := hld.trans_le (hv.bktCount_le b hb)
    obtain ⟨hb0, hb1, _, _, hr_lt, hne_lo, hne_lr, hne_or,
      ⟨hlic_le, lm, hv_l⟩, hom_fn, hreb_fn⟩ := validFastState_delete_bounds hv hb
    obtain ⟨hri_st, hri_res, _, _⟩ :=
      delRemReadInfoGenProg_spec u henv hseed hrep hb hld_tl (s := s)
    dsimp only [u] at hri_st hri_res
    have hfp_lt : fpOfSalt c U n_max θ.2 (fs.bktSalt b) u < 2 ^ fpBitsWhp n_max := by
      unfold fpOfSalt
      by_cases hs : fs.bktSalt b < sMaxWhp c n_max
      · simp only [hs, ↓reduceDIte]; exact fpHash_lt c U n_max θ.2 ⟨_, hs⟩ u
      · simp only [hs, ↓reduceDIte]; exact Nat.two_pow_pos _
    set st_del := fs.locState b loc_del
    set rKey_u := fpReducedKey c U n_max θ.2 u
    set fp_live_u := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
    obtain ⟨_, _, hst1⟩ := delRemBufGenProg_fastStep henv
      (fun h2 => (hb0 loc_del hld h2).2.2) (fun h3 => (hb1 loc_del hld h3).2.2)
      hseed hrep (st_del := st_del) (rKey_u := rKey_u) (s := s)
    set s1 := (Memory.spec 0).clientState s
      (delRemBufGenProg (((mkWhpCoreParams c U V w n_max, base), st_del), rKey_u))
    set buf1 :=
      if st_del = 2 then
        Function.update fs.buf 0 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 0) rKey_u)
      else if st_del = 3 then
        Function.update fs.buf 1 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 1) rKey_u)
      else fs.buf
    set fs_b : FastState := { fs with buf := buf1 }
    obtain ⟨_, _, hst2⟩ := delRemLiveGenProg_fastStep (fs := fs_b) henv hv.curEp_or hb
      (hv.roles_valid b hb).1 hlic_le hv_l hfp_lt hst1.2.1 hst1.2.2.1 (st_del := st_del) (s := s1)
    set s2 := (Memory.spec 0).clientState s1
      (delRemLiveGenProg (((mkWhpCoreParams c U V w n_max, base), b), (st_del, fp_live_u)))
    set slices1 :=
      if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then
        Function.update fs.slices (fs.liveSliceIdx b)
          (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs.slices (fs.liveSliceIdx b)) fp_live_u)
      else fs.slices
    set fs_l : FastState := { fs_b with slices := slices1 }
    have hom_fn2 : fs_l.overmarsActive b = 1 →
        fs_l.overmarsInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
        ∃ om, ValidWhpSlice n_max (fs_l.overmarsInsCount b)
          (fs_l.slices (fs_l.overmarsSliceIdx b)) om := by
      intro ha1
      obtain ⟨hins_o, om, hv_o⟩ := hom_fn ha1
      refine ⟨hins_o.le, om, ?_⟩
      change ValidWhpSlice n_max (fs.overmarsInsCount b) (slices1 (fs.overmarsSliceIdx b)) om
      dsimp only [slices1]
      by_cases hin : inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del = true
      · rw [ite_eq_left hin, Function.update_of_ne hne_lo.symm]; exact hv_o
      · rw [ite_eq_right hin]; exact hv_o
    obtain ⟨_, _, hst3⟩ := delRemOmGenProg_fastStep (fs := fs_l) henv hv.curEp_or hb
      (hv.roles_valid b hb).2.1 hom_fn2 hfp_lt hst2.2.1 hst2.2.2.1
      (loc_del := loc_del) (st_del := st_del) (s := s2)
    set slices2 :=
      if fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
          inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then
        Function.update slices1 (fs.overmarsSliceIdx b)
          (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (slices1 (fs.overmarsSliceIdx b)) fp_live_u)
      else slices1
    set fs_o : FastState := { fs_l with slices := slices2 }
    have hcore_st : (Memory.spec 0).clientState s
        (delRemCoreGenProg ((((mkWhpCoreParams c U V w n_max, base), b), loc_del),
          (st_del, (rKey_u, fp_live_u)))) =
        (Memory.spec 0).clientState s2
          (delRemOmGenProg ((((mkWhpCoreParams c U V w n_max, base), b), loc_del),
            (st_del, fp_live_u))) := by
      unfold delRemCoreGenProg; dsimp only
      rw [clientState_bind, clientState_bind]
    rw [hcp_eq] at *
    rw [hri_st] at *
    rw [hri_res] at *
    rw [hcore_st] at *
    dsimp only at *
    first
    | exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, hb, hld_tl⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv, hb, hld, rfl, hfp_lt⟩
    | (refine ⟨c, U, V, w, n_max, θ, fs_o, henv, rfl, hst3.2.1, hst3.2.2.1, hv.curEp_or, hb, hr_lt,
         fun hrbt => ?_⟩
       obtain ⟨hins_r, rm, hv_r⟩ := hreb_fn hrbt
       refine ⟨hins_r.le, rm, ?_⟩
       have hsl2 : slices2 (fs.rebSliceIdx b) = slices1 (fs.rebSliceIdx b) := by
         dsimp only [slices2]
         by_cases ho : fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
             inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del = true
         · rw [ite_eq_left ho]; exact Function.update_of_ne hne_or.symm _ _
         · rw [ite_eq_right ho]
       have hsl1 : slices1 (fs.rebSliceIdx b) = fs.slices (fs.rebSliceIdx b) := by
         dsimp only [slices1]
         by_cases hl : inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del = true
         · rw [ite_eq_left hl]; exact Function.update_of_ne hne_lr.symm _ _
         · rw [ite_eq_right hl]
       change ValidWhpSlice n_max fs.rebInsCount (slices2 (fs.rebSliceIdx b)) rm
       rwa [hsl2, hsl1])
  )

private theorem fastDeleteRemoveGenProg_fastStep {c U V w n_max base b loc_del : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (u : Fin U)
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidFastState c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max)
    (hld : loc_del < fs.bktCount b) :
    let prog := fastDeleteRemoveGenProg
      ((((mkWhpParams c U V w n_max, base), b), loc_del), u.val)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 2 * cTabWhp c + 2 * hashEvalCostWhp c + 870 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (fastDeleteRemove c U n_max θ fs u b loc_del) s s' := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  set cp := mkWhpCoreParams c U V w n_max
  have hld_tl : loc_del < totalLocalCoordsWhp n_max := hld.trans_le (hv.bktCount_le b hb)
  obtain ⟨hb0, hb1, _, _, hr_lt, hne_lo, hne_lr, hne_or,
    ⟨hlic_le, lm, hv_l⟩, hom_fn, hreb_fn⟩ := validFastState_delete_bounds hv hb
  obtain ⟨hri_st, hri_res, hri_mc, hri_vp⟩ :=
    delRemReadInfoGenProg_spec u henv hseed hrep hb hld_tl (s := s)
  have hfp_lt : fpOfSalt c U n_max θ.2 (fs.bktSalt b) u < 2 ^ fpBitsWhp n_max := by
    unfold fpOfSalt
    by_cases hs : fs.bktSalt b < sMaxWhp c n_max
    · simp only [hs, ↓reduceDIte]; exact fpHash_lt c U n_max θ.2 ⟨_, hs⟩ u
    · simp only [hs, ↓reduceDIte]; exact Nat.two_pow_pos _
  set st_del := fs.locState b loc_del
  set rKey_u := fpReducedKey c U n_max θ.2 u
  set fp_live_u := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
  obtain ⟨hmc1, hvp1, hst1⟩ := delRemBufGenProg_fastStep henv
    (fun h2 => (hb0 loc_del hld h2).2.2) (fun h3 => (hb1 loc_del hld h3).2.2)
    hseed hrep (st_del := st_del) (rKey_u := rKey_u) (s := s)
  set s1 := (Memory.spec 0).clientState s (delRemBufGenProg (((cp, base), st_del), rKey_u))
  set buf1 :=
    if st_del = 2 then
      Function.update fs.buf 0 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 0) rKey_u)
    else if st_del = 3 then
      Function.update fs.buf 1 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 1) rKey_u)
    else fs.buf
  set fs_b : FastState := { fs with buf := buf1 }
  obtain ⟨hmc2, hvp2, hst2⟩ := delRemLiveGenProg_fastStep (fs := fs_b) henv hv.curEp_or hb
    (hv.roles_valid b hb).1 hlic_le hv_l hfp_lt hst1.2.1 hst1.2.2.1
    (st_del := st_del) (s := s1)
  set s2 := (Memory.spec 0).clientState s1
    (delRemLiveGenProg (((cp, base), b), (st_del, fp_live_u)))
  set slices1 :=
    if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then
      Function.update fs.slices (fs.liveSliceIdx b)
        (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.liveSliceIdx b)) fp_live_u)
    else fs.slices
  set fs_l : FastState := { fs_b with slices := slices1 }
  have hom_fn2 : fs_l.overmarsActive b = 1 →
      fs_l.overmarsInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
      ∃ om, ValidWhpSlice n_max (fs_l.overmarsInsCount b)
        (fs_l.slices (fs_l.overmarsSliceIdx b)) om := by
    intro ha1
    obtain ⟨hins_o, om, hv_o⟩ := hom_fn ha1
    refine ⟨hins_o.le, om, ?_⟩
    change ValidWhpSlice n_max (fs.overmarsInsCount b) (slices1 (fs.overmarsSliceIdx b)) om
    dsimp only [slices1]
    by_cases hin : inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del = true
    · rw [ite_eq_left hin, Function.update_of_ne hne_lo.symm]; exact hv_o
    · rw [ite_eq_right hin]; exact hv_o
  obtain ⟨hmc3, hvp3, hst3⟩ := delRemOmGenProg_fastStep (fs := fs_l) henv hv.curEp_or hb
    (hv.roles_valid b hb).2.1 hom_fn2 hfp_lt hst2.2.1 hst2.2.2.1
    (loc_del := loc_del) (st_del := st_del) (s := s2)
  set s3 := (Memory.spec 0).clientState s2
    (delRemOmGenProg ((((cp, base), b), loc_del), (st_del, fp_live_u)))
  set slices2 :=
    if fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
        inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then
      Function.update slices1 (fs.overmarsSliceIdx b)
        (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (slices1 (fs.overmarsSliceIdx b)) fp_live_u)
    else slices1
  set fs_o : FastState := { fs_l with slices := slices2 }
  have hreb_fn3 : decide (fs_o.rebStage = 2 ∧ fs_o.dirtyIdx < fs_o.dirtyCount ∧
      fs_o.dirtyBuckets fs_o.dirtyIdx = b ∧ fs_o.rebCandSalt < sMaxWhp c n_max ∧
      fs_o.rebCollision = 0) = true →
      fs_o.rebInsCount ≤ 8 * (slabScale n_max) ^ 12 ∧
      ∃ rm, ValidWhpSlice n_max fs_o.rebInsCount (fs_o.slices (fs_o.rebSliceIdx b)) rm := by
    intro hrbt
    obtain ⟨hins_r, rm, hv_r⟩ := hreb_fn hrbt
    refine ⟨hins_r.le, rm, ?_⟩
    have hsl2 : slices2 (fs.rebSliceIdx b) = slices1 (fs.rebSliceIdx b) := by
      dsimp only [slices2]
      by_cases ho : fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
          inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del = true
      · rw [ite_eq_left ho]; exact Function.update_of_ne hne_or.symm _ _
      · rw [ite_eq_right ho]
    have hsl1 : slices1 (fs.rebSliceIdx b) = fs.slices (fs.rebSliceIdx b) := by
      dsimp only [slices1]
      by_cases hl : inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del = true
      · rw [ite_eq_left hl]; exact Function.update_of_ne hne_lr.symm _ _
      · rw [ite_eq_right hl]
    change ValidWhpSlice n_max fs.rebInsCount (slices2 (fs.rebSliceIdx b)) rm
    rwa [hsl2, hsl1]
  obtain ⟨hmc4, hvp4, hst4⟩ := delRemRebGenProg_fastStep (fs := fs_o) u henv hv.curEp_or hb
    hr_lt hreb_fn3 hst3.2.1 hst3.2.2.1 (loc_del := loc_del) (st_del := st_del) (s := s3)
  have hcore_st : (Memory.spec 0).clientState s
      (delRemCoreGenProg ((((cp, base), b), loc_del), (st_del, (rKey_u, fp_live_u)))) = s3 := by
    unfold delRemCoreGenProg; dsimp only
    rw [clientState_bind, clientState_bind]
  dsimp only
  unfold fastDeleteRemoveGenProg
  dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
  have hs'_eq : (Memory.spec 0).clientState s
      (delRemReadInfoGenProg ((((mkWhpParams c U V w n_max, base), b), loc_del), u.val) >>=
        fun info =>
        delRemCoreGenProg ((((cp, base), b), loc_del), info) >>= fun _ =>
        delRemRebGenProg ((((mkWhpParams c U V w n_max, base), b), loc_del), (info.1, u.val))) =
      (Memory.spec 0).clientState s3
        (delRemRebGenProg
          ((((mkWhpParams c U V w n_max, base), b), loc_del), (st_del, u.val))) := by
    rw [clientState_bind, hri_st, hri_res]; dsimp only
    rw [clientState_bind, hcore_st]
  rw [hs'_eq]
  refine ⟨?_, ?_, ((hst1.trans hst2).trans hst3).trans hst4⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hri_st, hri_res]; dsimp only
    rw [hcore_st]
    unfold delRemCoreGenProg; dsimp only
    simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    have hri_mc' : memoryCost (delRemReadInfoGenProg
        ((((mkWhpParams c U V w n_max, base), b), loc_del), u.val)) s ≤
        hashEvalCostWhp c + 5 := hri_mc
    dsimp only [s1, s2, s3, cp, st_del, rKey_u, fp_live_u] at hmc1 hmc2 hmc3 hmc4 ⊢
    omega
  · refine validProg_bind hri_vp ?_; rw [hri_st, hri_res]; dsimp only
    have hcore_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
        (delRemCoreGenProg ((((cp, base), b), loc_del), (st_del, (rKey_u, fp_live_u)))) := by
      unfold delRemCoreGenProg; dsimp only
      exact validProg_bind hvp1 (validProg_bind hvp2 hvp3)
    refine validProg_bind hcore_vp ?_; rw [hcore_st]
    exact hvp4

/-- Sub-helper 6.2a: relocate `(b, loc_last) → (b, loc_del)` in `buf 0` or `buf 1`. -/
@[irreducible] private def delMoveBufGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((((cp, base), b), loc_del), (st_last, rKey_last)) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let z2 ← pure 2
    let z3 ← pure 3
    if st_last = z2 then
      bufInsertGenProg ((((cp, base), z0), rKey_last), (b, loc_del))
    else if st_last = z3 then
      bufInsertGenProg ((((cp, base), z1), rKey_last), (b, loc_del))
    else
      pure ()

private theorem realizes_delMoveBufGen :
    Realizes .exact delMoveBufGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), loc_del), (st_last, _)) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          loc_del < totalLocalCoordsWhp n_max ∧
          (st_last = 2 →
            (fs.buf 0).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
            (fs.buf 0).itemAlloc < qEpochWhp n_max ∧
            ∃ m0, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf 0) m0) ∧
          (st_last = 3 →
            (fs.buf 1).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
            (fs.buf 1).itemAlloc < qEpochWhp n_max ∧
            ∃ m1, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf 1) m1))
      (fun _ _ => 0) := by
  unfold delMoveBufGenProg
  have hbi := realizes_bufInsertGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, loc_del⟩, ⟨st_last, rKey_last⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hb, hld, h2, h3⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    first
    | exact henv.fits_const (by decide)
    | (obtain ⟨hna0, hia0, m0, hv0⟩ := h2 (by assumption)
       exact ⟨c, U, V, w, n_max, fs.buf 0, m0, henv, rfl, Or.inl rfl,
         hrep.buf_rep (Or.inl rfl), hv0, hna0, hia0, hb, hld⟩)
    | (obtain ⟨hna1, hia1, m1, hv1⟩ := h3 (by assumption)
       exact ⟨c, U, V, w, n_max, fs.buf 1, m1, henv, rfl, Or.inr rfl,
         hrep.buf_rep (Or.inr rfl), hv1, hna1, hia1, hb, hld⟩)
  )

private theorem delMoveBufGenProg_fastStep {c U V w n_max base b loc_del st_last rKey_last : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hld : loc_del < totalLocalCoordsWhp n_max)
    (h2 : st_last = 2 →
      (fs.buf 0).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
      (fs.buf 0).itemAlloc < qEpochWhp n_max ∧
      ∃ m0, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf 0) m0)
    (h3 : st_last = 3 →
      (fs.buf 1).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
      (fs.buf 1).itemAlloc < qEpochWhp n_max ∧
      ∃ m1, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf 1) m1)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := delMoveBufGenProg
      ((((mkWhpCoreParams c U V w n_max, base), b), loc_del), (st_last, rKey_last))
    let s' := (Memory.spec 0).clientState s prog
    let buf2 :=
      if st_last = 2 then
        Function.update fs.buf 0
          (bufInsert (cTabWhp c) (bCharWhp n_max) (fs.buf 0) rKey_last b loc_del)
      else if st_last = 3 then
        Function.update fs.buf 1
          (bufInsert (cTabWhp c) (bCharWhp n_max) (fs.buf 1) rKey_last b loc_del)
      else fs.buf
    memoryCost prog s ≤ 20 * cTabWhp c + 24 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ { fs with buf := buf2 } s s' := by
  dsimp only
  unfold delMoveBufGenProg
  simp only [pure_bind]
  by_cases hs2 : st_last = 2
  · simp only [hs2, ↓reduceIte]
    obtain ⟨hna0, hia0, m0, hv0⟩ := h2 hs2
    obtain ⟨hmc, hvp, hstep⟩ :=
      bufInsertGenProg_fastStep henv (Or.inl rfl) hseed hrep hv0 hna0 hia0 hb hld
        (rKey := rKey_last) (s := s)
    exact ⟨hmc, hvp, hstep⟩
  · simp only [hs2, ↓reduceIte]
    by_cases hs3 : st_last = 3
    · simp only [hs3, ↓reduceIte]
      obtain ⟨hna1, hia1, m1, hv1⟩ := h3 hs3
      obtain ⟨hmc, hvp, hstep⟩ :=
        bufInsertGenProg_fastStep henv (Or.inr rfl) hseed hrep hv1 hna1 hia1 hb hld
          (rKey := rKey_last) (s := s)
      exact ⟨hmc, hvp, hstep⟩
    · simp only [hs3, ↓reduceIte]
      exact ⟨Nat.zero_le _, validProg_pure _, FastStateStep.refl hseed hrep⟩

/-- Sub-helper 6.2b (Overmars insert+inc): insert `(fp_live_last, loc_del)` into `omIdx` and
increment `overmarsInsCount b`. -/
@[irreducible] private def delMoveOmInsertIncProg :
    ((WhpCoreParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, base), (b, omIdx)), (fp_live_last, loc_del)) => do
    let z1 ← pure 1
    btreeInsertGenProg ((((cp, base), omIdx), fp_live_last), loc_del)
    let omIns ← readBktFieldGenProg (((cp, base), b), 7)
    let omIns1 ← pure (omIns + z1)
    writeBktFieldGenProg ((((cp, base), b), 7), omIns1)

private theorem realizes_delMoveOmInsertInc :
    Realizes .exact delMoveOmInsertIncProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), (b, omIdx)), (fp_live_last, loc_del)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (om : ℕ → Option ℕ),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          omIdx = fs.overmarsSliceIdx b ∧
          omIdx < 3 * numBucketsWhp n_max ∧
          loc_del < totalLocalCoordsWhp n_max ∧
          fp_live_last < 2 ^ fpBitsWhp n_max ∧
          fs.overmarsInsCount b < 8 * (slabScale n_max) ^ 12 ∧
          ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices omIdx) om)
      (fun _ _ => 0) := by
  unfold delMoveOmInsertIncProg
  have hbi := realizes_btreeInsertGen
  have hrb := realizes_readBktFieldGen
  have hwb := realizes_writeBktFieldGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, ⟨b, omIdx⟩⟩, ⟨fp_live_last, loc_del⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, om, henv, rfl, hseed, hrep, hb, rfl, homIdx,
      hld, hfp, hins_lt, hv_om⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hML12 := numBucketsWhp_mul_scale_pow12_le hth
    have h8L12 : 8 * (slabScale n_max) ^ 12 ≤ n_max :=
      (Nat.mul_le_mul_right _ (by have := (large_bounds_lt_n_max hth).1; omega)).trans hML12
    have hval_ld := loc_lt_two_pow_valLaneBits hld
    obtain ⟨_, _, hbi_step⟩ :=
      btreeInsertGenProg_fastStep henv homIdx hins_lt.le hseed hrep hv_om hfp hval_ld (s := s)
    set s_bi := (Memory.spec 0).clientState s
      (btreeInsertGenProg
        ((((mkWhpCoreParams c U V w n_max, base), fs.overmarsSliceIdx b), fp_live_last), loc_del))
    obtain ⟨hst_7, hres_7, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 7 < 10) hbi_step.2.2.1 (s := s_bi)
    simp only [getBktField] at hres_7
    have hfit7 : Fits w ((Memory.spec 0).clientResult s_bi
        (readBktFieldGenProg (((mkWhpCoreParams c U V w n_max, base), b), 7)) + 1) := by
      rw [hres_7]; exact henv.fits_of_le_n_max (by omega)
    dsimp only [s_bi] at hst_7 hres_7 hfit7
    simp only [hst_7, wp_large_M hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact hfit7
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact ⟨c, U, V, w, n_max, fs.overmarsInsCount b, fs.slices (fs.overmarsSliceIdx b), om,
        henv, rfl, homIdx, hins_lt.le, hrep.slice_rep homIdx, hv_om, hfp, hval_ld⟩
  )

private theorem delMoveOmInsertIncProg_fastStep {c U V w n_max base b loc_del fp_live_last : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {om : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hor : fs.overmarsRole b < 3)
    (hld : loc_del < totalLocalCoordsWhp n_max)
    (hfp : fp_live_last < 2 ^ fpBitsWhp n_max)
    (hins_lt : fs.overmarsInsCount b < 8 * (slabScale n_max) ^ 12)
    (hv_om : ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices (fs.overmarsSliceIdx b)) om)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let omIdx := fs.overmarsSliceIdx b
    let prog := delMoveOmInsertIncProg
      (((mkWhpCoreParams c U V w n_max, base), (b, omIdx)), (fp_live_last, loc_del))
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 2432 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        slices := Function.update fs.slices omIdx
          (btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs.slices omIdx) fp_live_last loc_del)
        overmarsInsCount := Function.update fs.overmarsInsCount b (fs.overmarsInsCount b + 1) }
      s s' := by
  have hth := henv.2.2.2.1
  have hML12 := numBucketsWhp_mul_scale_pow12_le hth
  have h8L12 : 8 * (slabScale n_max) ^ 12 ≤ n_max :=
    (Nat.mul_le_mul_right _ (by have := (large_bounds_lt_n_max hth).1; omega)).trans hML12
  have hval_ld := loc_lt_two_pow_valLaneBits hld
  have homIdx : fs.overmarsSliceIdx b < 3 * numBucketsWhp n_max := by
    unfold FastState.overmarsSliceIdx; omega
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hbi_mc, hbi_vp, hbi_step⟩ :=
    btreeInsertGenProg_fastStep henv homIdx hins_lt.le hseed hrep hv_om hfp hval_ld (s := s)
  set s_bi := (Memory.spec 0).clientState s
    (btreeInsertGenProg ((((cp, base), fs.overmarsSliceIdx b), fp_live_last), loc_del))
  obtain ⟨hst_7, hres_7, hmc_7, hvp_7⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 7 < 10) hbi_step.2.2.1 (s := s_bi)
  simp only [getBktField] at hres_7
  obtain ⟨hwb_mc, hwb_vp, hwb_step⟩ :=
    writeBktFieldGenProg_fastStep henv hb (by decide : 7 < 10) (by omega)
      hbi_step.2.1 hbi_step.2.2.1 (val := fs.overmarsInsCount b + 1) (s := s_bi)
  dsimp only
  unfold delMoveOmInsertIncProg
  simp only [cp, pure_bind]
  have hs'_eq : (Memory.spec 0).clientState s
      (btreeInsertGenProg ((((cp, base), fs.overmarsSliceIdx b), fp_live_last), loc_del) >>=
        fun _ =>
        readBktFieldGenProg (((cp, base), b), 7) >>= fun omIns =>
        writeBktFieldGenProg ((((cp, base), b), 7), omIns + 1)) =
      (Memory.spec 0).clientState s_bi
        (writeBktFieldGenProg ((((cp, base), b), 7), fs.overmarsInsCount b + 1)) := by
    rw [clientState_bind, clientState_bind]
    dsimp only [s_bi, cp] at hst_7 hres_7 ⊢
    rw [hst_7, hres_7]
  rw [hs'_eq]
  refine ⟨?_, ?_, hbi_step.trans hwb_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    dsimp only [s_bi, cp] at hbi_mc hst_7 hres_7 hmc_7 hwb_mc ⊢
    rw [hst_7, hres_7, hmc_7]; omega
  · refine validProg_bind hbi_vp ?_
    dsimp only [s_bi, cp] at hst_7 hres_7 hvp_7 hwb_vp ⊢
    refine validProg_bind hvp_7 ?_; rw [hst_7, hres_7]; exact hwb_vp

/-- Active Overmars helper for `delMoveOmSubProg` once `overmarsActive b = 1`. -/
@[irreducible] private def delMoveOmActiveProg :
    ((WhpCoreParams × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ) → Memory.Prog Unit
  | (((cp, base), b), ((loc_del, loc_last), fp_live_last)) => do
    let omCur ← readBktFieldGenProg (((cp, base), b), 6)
    let orl ← readBktFieldGenProg (((cp, base), b), 4)
    let omIdx ← pure (3 * b + orl)
    if loc_last < omCur then
      btreeUpdateGenProg ((((cp, base), omIdx), fp_live_last), loc_del)
    else if loc_del < omCur then
      delMoveOmInsertIncProg (((cp, base), (b, omIdx)), (fp_live_last, loc_del))
    else
      pure ()

private theorem realizes_delMoveOmActive :
    Realizes .exact delMoveOmActiveProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), b), ((loc_del, _), fp_live_last)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (om : ℕ → Option ℕ),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.overmarsRole b < 3 ∧
          loc_del < totalLocalCoordsWhp n_max ∧
          fp_live_last < 2 ^ fpBitsWhp n_max ∧
          fs.overmarsInsCount b < 8 * (slabScale n_max) ^ 12 ∧
          ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices (fs.overmarsSliceIdx b)) om)
      (fun _ _ => 0) := by
  unfold delMoveOmActiveProg
  have hrb := realizes_readBktFieldGen
  have hbu := realizes_btreeUpdateGen
  have hmi := realizes_delMoveOmInsertInc
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, b⟩, ⟨⟨loc_del, loc_last⟩, fp_live_last⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, om, henv, rfl, hseed, hrep, hb, hor, hld, hfp,
      hins_lt, hv_om⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h3M := (large_index_bounds hth).2.2.2.2.1
    have hval_ld := loc_lt_two_pow_valLaneBits hld
    have homIdx : fs.overmarsSliceIdx b < 3 * numBucketsWhp n_max := by
      unfold FastState.overmarsSliceIdx; omega
    obtain ⟨hst_6, hres_6, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 6 < 10)
      hrep (s := s)
    obtain ⟨hst_4, hres_4, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 4 < 10)
      hrep (s := s)
    simp only [getBktField] at hres_6 hres_4
    simp only [hst_6, hres_6, hst_4, hres_4, wp_large_M hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact ⟨c, U, V, w, n_max, fs.overmarsInsCount b, fs.slices (fs.overmarsSliceIdx b), om,
        henv, rfl, homIdx, hins_lt.le, hrep.slice_rep homIdx, hv_om, hfp, hval_ld⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, om, henv, rfl, hseed, hrep, hb, rfl, homIdx,
        hld, hfp, hins_lt, hv_om⟩
  )

/-- Sub-helper 6.2b (Overmars part): relocate `loc_last → loc_del` in `overmarsSlice[b]` when
`inLiveTree` already holds (`d = (((cp, base), b), ((loc_del, loc_last), fp_live_last))`). -/
@[irreducible] private def delMoveOmSubProg :
    ((WhpCoreParams × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ) → Memory.Prog Unit
  | (((cp, base), b), ((loc_del, loc_last), fp_live_last)) => do
    let z1 ← pure 1
    let omAct ← readBktFieldGenProg (((cp, base), b), 5)
    if omAct = z1 then
      delMoveOmActiveProg (((cp, base), b), ((loc_del, loc_last), fp_live_last))
    else
      pure ()

private theorem realizes_delMoveOmSub :
    Realizes .exact delMoveOmSubProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), b), ((loc_del, _), fp_live_last)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.overmarsRole b < 3 ∧
          loc_del < totalLocalCoordsWhp n_max ∧
          fp_live_last < 2 ^ fpBitsWhp n_max ∧
          (fs.overmarsActive b = 1 →
            fs.overmarsInsCount b < 8 * (slabScale n_max) ^ 12 ∧
            ∃ om, ValidWhpSlice n_max (fs.overmarsInsCount b)
              (fs.slices (fs.overmarsSliceIdx b)) om))
      (fun _ _ => 0) := by
  unfold delMoveOmSubProg
  have hrb := realizes_readBktFieldGen
  have hma := realizes_delMoveOmActive
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, b⟩, ⟨⟨loc_del, loc_last⟩, fp_live_last⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, rfl, hseed, hrep, hb, hor, hld, hfp, hom_fn⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    obtain ⟨hst_5, hres_5, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 5 < 10)
      hrep (s := s)
    simp only [getBktField] at hres_5
    simp only [hst_5, hres_5, wp_large_M hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | (obtain ⟨hins_lt, om, hv_om⟩ := hom_fn (by assumption)
       exact ⟨c, U, V, w, n_max, θ, fs, om, henv, rfl, hseed, hrep, hb, hor, hld, hfp,
         hins_lt, hv_om⟩)
  )

private theorem delMoveOmSubProg_fastStep {c U V w n_max base b loc_del loc_last fp_live_last : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hor : fs.overmarsRole b < 3)
    (hld : loc_del < totalLocalCoordsWhp n_max)
    (hfp : fp_live_last < 2 ^ fpBitsWhp n_max)
    (hom_fn : fs.overmarsActive b = 1 →
      fs.overmarsInsCount b < 8 * (slabScale n_max) ^ 12 ∧
      ∃ om, ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices (fs.overmarsSliceIdx b)) om)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := delMoveOmSubProg
      (((mkWhpCoreParams c U V w n_max, base), b), ((loc_del, loc_last), fp_live_last))
    let s' := (Memory.spec 0).clientState s prog
    let omIdx := fs.overmarsSliceIdx b
    let omPair :=
      if fs.overmarsActive b = 1 then
        if loc_last < fs.overmarsCursor b then
          (Function.update fs.slices omIdx
            (btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              (fs.slices omIdx) fp_live_last loc_del),
           fs.overmarsInsCount)
        else if loc_del < fs.overmarsCursor b then
          (Function.update fs.slices omIdx
            (btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              (fs.slices omIdx) fp_live_last loc_del),
           Function.update fs.overmarsInsCount b (fs.overmarsInsCount b + 1))
        else (fs.slices, fs.overmarsInsCount)
      else (fs.slices, fs.overmarsInsCount)
    memoryCost prog s ≤ 2438 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with slices := omPair.1, overmarsInsCount := omPair.2 } s s' := by
  have hval_ld := loc_lt_two_pow_valLaneBits hld
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hst_5, hres_5, hmc_5, hvp_5⟩ := readBktFieldGenProg_spec henv hb (by decide : 5 < 10)
    hrep (s := s)
  simp only [getBktField] at hres_5
  dsimp only
  unfold delMoveOmSubProg
  simp only [cp, pure_bind]
  by_cases ha1 : fs.overmarsActive b = 1
  · rw [ite_eq_left ha1]
    obtain ⟨hins_lt, om, hv_om⟩ := hom_fn ha1
    obtain ⟨hst_6, hres_6, hmc_6, hvp_6⟩ := readBktFieldGenProg_spec henv hb (by decide : 6 < 10)
      hrep (s := s)
    obtain ⟨hst_4, hres_4, hmc_4, hvp_4⟩ := readBktFieldGenProg_spec henv hb (by decide : 4 < 10)
      hrep (s := s)
    simp only [getBktField] at hres_6 hres_4
    have homIdx : fs.overmarsSliceIdx b < 3 * numBucketsWhp n_max := by
      unfold FastState.overmarsSliceIdx; omega
    have hom_def : 3 * b + fs.overmarsRole b = fs.overmarsSliceIdx b := rfl
    by_cases hll_c : loc_last < fs.overmarsCursor b
    · rw [ite_eq_left hll_c]
      obtain ⟨hbu_mc, hbu_vp, hbu_step⟩ :=
        btreeUpdateGenProg_fastStep henv homIdx hins_lt.le hseed hrep hv_om hfp hval_ld (s := s)
      have hs'_eq : (Memory.spec 0).clientState s
          (readBktFieldGenProg (((cp, base), b), 5) >>= fun omAct =>
            if omAct = 1 then
              delMoveOmActiveProg (((cp, base), b), ((loc_del, loc_last), fp_live_last))
            else pure ()) =
          (Memory.spec 0).clientState s
            (btreeUpdateGenProg
              ((((cp, base), fs.overmarsSliceIdx b), fp_live_last), loc_del)) := by
        rw [clientState_bind, hst_5, hres_5, ite_eq_left ha1]
        unfold delMoveOmActiveProg; simp only [pure_bind]
        rw [clientState_bind, hst_6, hres_6, clientState_bind, hst_4, hres_4,
          ite_eq_left hll_c, hom_def]
      rw [hs'_eq]
      refine ⟨?_, ?_, hbu_step⟩
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hst_5, hres_5, hmc_5, ite_eq_left ha1]
        unfold delMoveOmActiveProg
        simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hst_6, hres_6, hmc_6, hst_4, hres_4, hmc_4, ite_eq_left hll_c, hom_def]
        omega
      · refine validProg_bind hvp_5 ?_; rw [hst_5, hres_5, ite_eq_left ha1]
        unfold delMoveOmActiveProg; simp only [pure_bind]
        refine validProg_bind hvp_6 ?_; rw [hst_6, hres_6]
        refine validProg_bind hvp_4 ?_; rw [hst_4, hres_4, ite_eq_left hll_c, hom_def]
        exact hbu_vp
    · rw [ite_eq_right hll_c]
      by_cases hld_c : loc_del < fs.overmarsCursor b
      · rw [ite_eq_left hld_c]
        obtain ⟨hmi_mc, hmi_vp, hmi_step⟩ :=
          delMoveOmInsertIncProg_fastStep henv hb hor hld hfp hins_lt hv_om hseed hrep (s := s)
        have hs'_eq : (Memory.spec 0).clientState s
            (readBktFieldGenProg (((cp, base), b), 5) >>= fun omAct =>
              if omAct = 1 then
                delMoveOmActiveProg (((cp, base), b), ((loc_del, loc_last), fp_live_last))
              else pure ()) =
            (Memory.spec 0).clientState s
              (delMoveOmInsertIncProg
                (((cp, base), (b, fs.overmarsSliceIdx b)), (fp_live_last, loc_del))) := by
          rw [clientState_bind, hst_5, hres_5, ite_eq_left ha1]
          unfold delMoveOmActiveProg; simp only [pure_bind]
          rw [clientState_bind, hst_6, hres_6, clientState_bind, hst_4, hres_4,
            ite_eq_right hll_c, ite_eq_left hld_c, hom_def]
        rw [hs'_eq]
        refine ⟨?_, ?_, hmi_step⟩
        · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
          rw [hst_5, hres_5, hmc_5, ite_eq_left ha1]
          unfold delMoveOmActiveProg
          simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
          rw [hst_6, hres_6, hmc_6, hst_4, hres_4, hmc_4, ite_eq_right hll_c, ite_eq_left hld_c,
            hom_def]
          omega
        · refine validProg_bind hvp_5 ?_; rw [hst_5, hres_5, ite_eq_left ha1]
          unfold delMoveOmActiveProg; simp only [pure_bind]
          refine validProg_bind hvp_6 ?_; rw [hst_6, hres_6]
          refine validProg_bind hvp_4 ?_; rw [hst_4, hres_4, ite_eq_right hll_c,
            ite_eq_left hld_c, hom_def]
          exact hmi_vp
      · rw [ite_eq_right hld_c]
        have hs'_eq : (Memory.spec 0).clientState s
            (readBktFieldGenProg (((cp, base), b), 5) >>= fun omAct =>
              if omAct = 1 then
                delMoveOmActiveProg (((cp, base), b), ((loc_del, loc_last), fp_live_last))
              else pure ()) = s := by
          rw [clientState_bind, hst_5, hres_5, ite_eq_left ha1]
          unfold delMoveOmActiveProg; simp only [pure_bind]
          rw [clientState_bind, hst_6, hres_6, clientState_bind, hst_4, hres_4,
            ite_eq_right hll_c, ite_eq_right hld_c]; rfl
        rw [hs'_eq]
        refine ⟨?_, ?_, FastStateStep.refl hseed hrep⟩
        · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
          rw [hst_5, hres_5, hmc_5, ite_eq_left ha1]
          unfold delMoveOmActiveProg
          simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
          rw [hst_6, hres_6, hmc_6, hst_4, hres_4, hmc_4, ite_eq_right hll_c, ite_eq_right hld_c]
          simp only [memoryCost_pure]; omega
        · refine validProg_bind hvp_5 ?_; rw [hst_5, hres_5, ite_eq_left ha1]
          unfold delMoveOmActiveProg; simp only [pure_bind]
          refine validProg_bind hvp_6 ?_; rw [hst_6, hres_6]
          refine validProg_bind hvp_4 ?_; rw [hst_4, hres_4, ite_eq_right hll_c,
            ite_eq_right hld_c]
          exact validProg_pure _
  · rw [ite_eq_right ha1]
    have hs'_eq : (Memory.spec 0).clientState s
        (readBktFieldGenProg (((cp, base), b), 5) >>= fun omAct =>
          if omAct = 1 then
            delMoveOmActiveProg (((cp, base), b), ((loc_del, loc_last), fp_live_last))
          else pure ()) = s := by
      rw [clientState_bind, hst_5, hres_5, ite_eq_right ha1]; rfl
    rw [hs'_eq]
    refine ⟨?_, ?_, FastStateStep.refl hseed hrep⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hst_5, hres_5, hmc_5, ite_eq_right ha1, memoryCost_pure]; omega
    · refine validProg_bind hvp_5 ?_; rw [hst_5, hres_5, ite_eq_right ha1]
      exact validProg_pure _

/-- Active helper for `delMoveLiveOmGenProg` once `inLiveTree` holds. -/
@[irreducible] private def delMoveLiveOmActiveProg :
    (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((((cp, base), b), (loc_del, loc_last)), fp_live_last) => do
    let lr ← readBktFieldGenProg (((cp, base), b), 2)
    let lIdx ← pure (3 * b + lr)
    btreeUpdateGenProg ((((cp, base), lIdx), fp_live_last), loc_del)
    delMoveOmSubProg (((cp, base), b), ((loc_del, loc_last), fp_live_last))

private theorem realizes_delMoveLiveOmActive :
    Realizes .exact delMoveLiveOmActiveProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), (loc_del, _)), fp_live_last) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (lm : ℕ → Option ℕ),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.liveRole b < 3 ∧
          fs.overmarsRole b < 3 ∧
          fs.liveSliceIdx b ≠ fs.overmarsSliceIdx b ∧
          loc_del < totalLocalCoordsWhp n_max ∧
          fp_live_last < 2 ^ fpBitsWhp n_max ∧
          fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
          ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) lm ∧
          (fs.overmarsActive b = 1 →
            fs.overmarsInsCount b < 8 * (slabScale n_max) ^ 12 ∧
            ∃ om, ValidWhpSlice n_max (fs.overmarsInsCount b)
              (fs.slices (fs.overmarsSliceIdx b)) om))
      (fun _ _ => 0) := by
  unfold delMoveLiveOmActiveProg
  have hrb := realizes_readBktFieldGen
  have hbu := realizes_btreeUpdateGen
  have hmo := realizes_delMoveOmSub
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, ⟨loc_del, loc_last⟩⟩, fp_live_last⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, lm, henv, rfl, hseed, hrep, hb, hlr, hor, hne_lo,
      hld, hfp, hlic, hv_l, hom_fn⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h3M := (large_index_bounds hth).2.2.2.2.1
    have hval_ld := loc_lt_two_pow_valLaneBits hld
    have hlIdx : fs.liveSliceIdx b < 3 * numBucketsWhp n_max := by
      unfold FastState.liveSliceIdx; omega
    obtain ⟨hst_2, hres_2, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 2 < 10)
      hrep (s := s)
    simp only [getBktField] at hres_2
    simp only [hst_2, hres_2, wp_large_M hth] at *
    first
    | decide
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact ⟨c, U, V, w, n_max, fs.liveInsCount b, fs.slices (fs.liveSliceIdx b), lm,
        henv, rfl, hlIdx, hlic, hrep.slice_rep hlIdx, hv_l, hfp, hval_ld⟩
    | (obtain ⟨_, _, hbu_step⟩ :=
         btreeUpdateGenProg_fastStep henv hlIdx hlic hseed hrep hv_l hfp hval_ld (s := s)
       refine ⟨c, U, V, w, n_max, θ, _, henv, rfl, hbu_step.2.1, hbu_step.2.2.1, hb, hor,
         hld, hfp, fun ha1 => ?_⟩
       obtain ⟨hins_lt, om, hv_om⟩ := hom_fn ha1
       refine ⟨hins_lt, om, ?_⟩
       change ValidWhpSlice n_max (fs.overmarsInsCount b)
         (Function.update fs.slices (fs.liveSliceIdx b)
           (btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
             (fs.slices (fs.liveSliceIdx b)) fp_live_last loc_del)
           (fs.overmarsSliceIdx b)) om
       rwa [Function.update_of_ne hne_lo.symm])
  )

/-- Sub-helper 6.2b: relocate `loc_last → loc_del` in `liveSlice[b]` and `overmarsSlice[b]`
(`fastDeleteMoveSlices`). -/
@[irreducible] private def delMoveLiveOmGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog Unit
  | ((((cp, base), b), (loc_del, loc_last)), (st_last, fp_live_last)) => do
    let z1 ← pure 1
    let stg ← readHdrProg (base, hdrRebStage)
    let oldEp ← readOldEpProg base
    let doneB ← readBktFieldGenProg (((cp, base), b), 8)
    let inL ← inLiveTreeProg ((stg, oldEp), (doneB, st_last))
    if inL = z1 then
      delMoveLiveOmActiveProg ((((cp, base), b), (loc_del, loc_last)), fp_live_last)
    else
      pure ()

private theorem realizes_delMoveLiveOmGen :
    Realizes .exact delMoveLiveOmGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), (loc_del, _)), (_, fp_live_last)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (lm : ℕ → Option ℕ),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          b < numBucketsWhp n_max ∧
          fs.liveRole b < 3 ∧
          fs.overmarsRole b < 3 ∧
          fs.liveSliceIdx b ≠ fs.overmarsSliceIdx b ∧
          loc_del < totalLocalCoordsWhp n_max ∧
          fp_live_last < 2 ^ fpBitsWhp n_max ∧
          fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
          ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) lm ∧
          (fs.overmarsActive b = 1 →
            fs.overmarsInsCount b < 8 * (slabScale n_max) ^ 12 ∧
            ∃ om, ValidWhpSlice n_max (fs.overmarsInsCount b)
              (fs.slices (fs.overmarsSliceIdx b)) om))
      (fun _ _ => 0) := by
  unfold delMoveLiveOmGenProg
  have hrh := realizes_readHdr
  have hro := realizes_readOldEp
  have hrb := realizes_readBktFieldGen
  have hil := realizes_inLiveTree
  have hma := realizes_delMoveLiveOmActive
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, ⟨loc_del, loc_last⟩⟩, ⟨st_last, fp_live_last⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, lm, henv, rfl, hseed, hrep, hce, hb, hlr, hor, hne_lo,
      hld, hfp, hlic, hv_l, hom_fn⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h2w := henv.two_le_w
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hold : fs.oldEp ≤ 1 := by rcases hce with hc | hc <;> simp [FastState.oldEp, hc]
    obtain ⟨hst_s, hres_s, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebStage)
      (by dsimp [hdrRebStage]; omega) (s := s)
    obtain ⟨hst_o, hres_o, _, _⟩ := readOldEpProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce
      hrep.2.2.2.1 (s := s)
    obtain ⟨hst_8, hres_8, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 8 < 10)
      hrep (s := s)
    simp only [getBktField] at hres_8
    obtain ⟨hst_il, _, _, _⟩ := inLiveTreeProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (rebStage := s.mem (base + hdrRebStage))
      (oldEp := fs.oldEp) (rebDoneB := fs.rebDoneFlag b) (st := st_last) (s := s)
    simp only [hst_s, hres_s, hst_o, hres_o, hst_8, hres_8, hst_il, wp_large_M hth] at *
    first
    | decide
    | exact h2w
    | exact hold
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact ⟨c, U, V, w, n_max, θ, fs, lm, henv, rfl, hseed, hrep, hb, hlr, hor, hne_lo,
        hld, hfp, hlic, hv_l, hom_fn⟩
  )

private theorem delMoveLiveOmGenProg_fastStep
    {c U V w n_max base b loc_del loc_last st_last fp_live_last : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {lm : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1)
    (hb : b < numBucketsWhp n_max)
    (hlr : fs.liveRole b < 3) (hor : fs.overmarsRole b < 3)
    (hne_lo : fs.liveSliceIdx b ≠ fs.overmarsSliceIdx b)
    (hld : loc_del < totalLocalCoordsWhp n_max)
    (hfp : fp_live_last < 2 ^ fpBitsWhp n_max)
    (hlic : fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12)
    (hv_l : ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) lm)
    (hom_fn : fs.overmarsActive b = 1 →
      fs.overmarsInsCount b < 8 * (slabScale n_max) ^ 12 ∧
      ∃ om, ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices (fs.overmarsSliceIdx b)) om)
    (hst_eq : st_last = fs.locState b loc_last)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := delMoveLiveOmGenProg
      ((((mkWhpCoreParams c U V w n_max, base), b), (loc_del, loc_last)), (st_last, fp_live_last))
    let s' := (Memory.spec 0).clientState s prog
    let omPair := fastDeleteMoveSlices n_max b loc_del loc_last fp_live_last fs
    memoryCost prog s ≤ 2718 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with slices := omPair.1, overmarsInsCount := omPair.2 } s s' := by
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have hval_ld := loc_lt_two_pow_valLaneBits hld
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hst_s, hres_s, hmc_s, hvp_s⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebStage)
    (by dsimp [hdrRebStage]; omega) (s := s)
  rw [hrep.2.2.2.2.2.1] at hres_s
  obtain ⟨hst_o, hres_o, hmc_o, hvp_o⟩ := readOldEpProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce
    hrep.2.2.2.1 (s := s)
  obtain ⟨hst_8, hres_8, hmc_8, hvp_8⟩ := readBktFieldGenProg_spec henv hb (by decide : 8 < 10)
    hrep (s := s)
  simp only [getBktField] at hres_8
  obtain ⟨hst_il, hres_il, hmc_il, hvp_il⟩ := inLiveTreeProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (rebStage := fs.rebStage) (oldEp := fs.oldEp)
    (rebDoneB := fs.rebDoneFlag b) (st := st_last) (s := s)
  dsimp only
  unfold delMoveLiveOmGenProg fastDeleteMoveSlices
  simp only [cp, pure_bind, ← hst_eq]
  by_cases hin : inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_last = true
  · rw [ite_eq_left hin] at hres_il ⊢
    obtain ⟨hst_2, hres_2, hmc_2, hvp_2⟩ := readBktFieldGenProg_spec henv hb (by decide : 2 < 10)
      hrep (s := s)
    simp only [getBktField] at hres_2
    have hlIdx : fs.liveSliceIdx b < 3 * numBucketsWhp n_max := by
      unfold FastState.liveSliceIdx; omega
    obtain ⟨hbu_mc, hbu_vp, hbu_step⟩ :=
      btreeUpdateGenProg_fastStep henv hlIdx hlic hseed hrep hv_l hfp hval_ld (s := s)
    set s_bu := (Memory.spec 0).clientState s
      (btreeUpdateGenProg ((((cp, base), fs.liveSliceIdx b), fp_live_last), loc_del))
    set sl_live' := Function.update fs.slices (fs.liveSliceIdx b)
      (btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        (fs.slices (fs.liveSliceIdx b)) fp_live_last loc_del)
    set fs_bu : FastState := { fs with slices := sl_live' }
    have hom_fn' : fs_bu.overmarsActive b = 1 →
        fs_bu.overmarsInsCount b < 8 * (slabScale n_max) ^ 12 ∧
        ∃ om, ValidWhpSlice n_max (fs_bu.overmarsInsCount b)
          (fs_bu.slices (fs_bu.overmarsSliceIdx b)) om := by
      intro ha1
      obtain ⟨hins_lt, om, hv_om⟩ := hom_fn ha1
      refine ⟨hins_lt, om, ?_⟩
      dsimp only [fs_bu, sl_live']
      have hne' : fs_bu.overmarsSliceIdx b ≠ fs.liveSliceIdx b := hne_lo.symm
      rwa [Function.update_of_ne hne']
    obtain ⟨hom_mc, hom_vp, hom_step⟩ :=
      delMoveOmSubProg_fastStep (fs := fs_bu) henv hb hor hld hfp hom_fn'
        hbu_step.2.1 hbu_step.2.2.1 (loc_last := loc_last) (s := s_bu)
    have hl_def : 3 * b + fs.liveRole b = fs.liveSliceIdx b := rfl
    have hs'_eq : (Memory.spec 0).clientState s
        (readHdrProg (base, hdrRebStage) >>= fun stg =>
          readOldEpProg base >>= fun oldEp =>
          readBktFieldGenProg (((cp, base), b), 8) >>= fun doneB =>
          inLiveTreeProg ((stg, oldEp), (doneB, st_last)) >>= fun inL =>
          if inL = 1 then
            delMoveLiveOmActiveProg ((((cp, base), b), (loc_del, loc_last)), fp_live_last)
          else pure ()) =
        (Memory.spec 0).clientState s_bu
          (delMoveOmSubProg (((cp, base), b), ((loc_del, loc_last), fp_live_last))) := by
      rw [clientState_bind, hst_s, hres_s, clientState_bind, hst_o, hres_o,
        clientState_bind, hst_8, hres_8, clientState_bind, hst_il, hres_il,
        ite_eq_left rfl]
      unfold delMoveLiveOmActiveProg; simp only [pure_bind]
      rw [clientState_bind, hst_2, hres_2, hl_def, clientState_bind]
    simp only [hin, and_true]
    rw [hs'_eq]
    refine ⟨?_, ?_, hbu_step.trans hom_step⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hst_s, hres_s, hmc_s, hst_o, hres_o, hmc_o, hst_8, hres_8, hmc_8,
        hst_il, hres_il, hmc_il, ite_eq_left rfl]
      unfold delMoveLiveOmActiveProg
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hst_2, hres_2, hmc_2, hl_def]
      dsimp only [s_bu, cp] at hbu_mc hom_mc ⊢; omega
    · refine validProg_bind hvp_s ?_; rw [hst_s, hres_s]
      refine validProg_bind hvp_o ?_; rw [hst_o, hres_o]
      refine validProg_bind hvp_8 ?_; rw [hst_8, hres_8]
      refine validProg_bind hvp_il ?_; rw [hst_il, hres_il, ite_eq_left rfl]
      unfold delMoveLiveOmActiveProg; simp only [pure_bind]
      refine validProg_bind hvp_2 ?_; rw [hst_2, hres_2, hl_def]
      exact validProg_bind hbu_vp hom_vp
  · rw [ite_eq_right hin] at hres_il ⊢
    have hfls : ¬(fs.overmarsActive b = 1 ∧
        inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_last = true) :=
      fun ⟨_, h⟩ => hin h
    rw [ite_eq_right hfls]
    have hs'_eq : (Memory.spec 0).clientState s
        (readHdrProg (base, hdrRebStage) >>= fun stg =>
          readOldEpProg base >>= fun oldEp =>
          readBktFieldGenProg (((cp, base), b), 8) >>= fun doneB =>
          inLiveTreeProg ((stg, oldEp), (doneB, st_last)) >>= fun inL =>
          if inL = 1 then
            delMoveLiveOmActiveProg ((((cp, base), b), (loc_del, loc_last)), fp_live_last)
          else pure ()) = s := by
      rw [clientState_bind, hst_s, hres_s, clientState_bind, hst_o, hres_o,
        clientState_bind, hst_8, hres_8, clientState_bind, hst_il, hres_il,
        ite_eq_right (by decide : ¬(0 = 1))]; rfl
    rw [hs'_eq]
    refine ⟨?_, ?_, FastStateStep.refl hseed hrep⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hst_s, hres_s, hmc_s, hst_o, hres_o, hmc_o, hst_8, hres_8, hmc_8,
        hst_il, hres_il, hmc_il, ite_eq_right (by decide : ¬(0 = 1))]
      simp only [memoryCost_pure]; omega
    · refine validProg_bind hvp_s ?_; rw [hst_s, hres_s]
      refine validProg_bind hvp_o ?_; rw [hst_o, hres_o]
      refine validProg_bind hvp_8 ?_; rw [hst_8, hres_8]
      refine validProg_bind hvp_il ?_; rw [hst_il, hres_il, ite_eq_right (by decide : ¬(0 = 1))]
      exact validProg_pure _

/-- Sub-helper 6.2c (collision reset): reset `rebSlice`, advance `rebCandSalt`, and zero cursors
(`d = ((cp, base), rIdx)`). -/
@[irreducible] private def delMoveRebCollisionProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, base), rIdx) => do
    let z0 ← pure 0
    let z1 ← pure 1
    resetBTreeSliceGenProg ((cp, base), rIdx)
    let cand ← readHdrProg (base, hdrRebCandSalt)
    let cand1 ← pure (cand + z1)
    writeHdrProg ((base, hdrRebCandSalt), cand1)
    writeHdrProg ((base, hdrRebScanCursor), z0)
    writeHdrProg ((base, hdrRebInsCount), z0)

private theorem realizes_delMoveRebCollision :
    Realizes .exact delMoveRebCollisionProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((cp, base), rIdx) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          rIdx < 3 * numBucketsWhp n_max ∧
          fs.rebCandSalt < sMaxWhp c n_max)
      (fun _ _ => 0) := by
  unfold delMoveRebCollisionProg
  have hrs := realizes_resetBTreeSliceGen
  have hrh := realizes_readHdr
  have hwh := realizes_writeHdr
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, rIdx⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, rfl, hseed, hrep, hrIdx, hcs_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hsmax_n := (large_bounds_lt_n_max hth).2.2.2.2.1
    obtain ⟨_, _, hrs_step⟩ := resetBTreeSliceGenProg_fastStep henv hrIdx hseed hrep (s := s)
    set s1 := (Memory.spec 0).clientState s
      (resetBTreeSliceGenProg ((mkWhpCoreParams c U V w n_max, base), rIdx))
    obtain ⟨hst_c, hres_c, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebCandSalt)
      (by dsimp [hdrRebCandSalt]; omega) (s := s1)
    have hmem_c : s1.mem (base + hdrRebCandSalt) = fs.rebCandSalt :=
      hrs_step.2.2.1.2.2.2.2.2.2.2.2.2.1
    simp only [wp_large_M hth] at *
    first
    | trivial
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | (dsimp only [s1] at hst_c hres_c hmem_c
       rw [hres_c, hmem_c]
       exact henv.fits_of_le_n_max (by omega))
  )

private theorem delMoveRebCollisionProg_fastStep {c U V w n_max base rIdx : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hrIdx : rIdx < 3 * numBucketsWhp n_max)
    (hcs_lt : fs.rebCandSalt < sMaxWhp c n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := delMoveRebCollisionProg ((mkWhpCoreParams c U V w n_max, base), rIdx)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s = 12 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        slices := Function.update fs.slices rIdx (resetBTreeSlice (fs.slices rIdx))
        rebCandSalt := fs.rebCandSalt + 1
        rebScanCursor := 0
        rebInsCount := 0 } s s' := by
  have hth := henv.2.2.2.1
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have hsmax_n := (large_bounds_lt_n_max hth).2.2.2.2.1
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hrs_mc, hrs_vp, hrs_step⟩ :=
    resetBTreeSliceGenProg_fastStep henv hrIdx hseed hrep (s := s)
  set s1 := (Memory.spec 0).clientState s (resetBTreeSliceGenProg ((cp, base), rIdx))
  obtain ⟨hst_c, hres_c, hmc_c, hvp_c⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebCandSalt)
    (by dsimp [hdrRebCandSalt]; omega) (s := s1)
  rw [hrs_step.2.2.1.2.2.2.2.2.2.2.2.2.1] at hres_c
  obtain ⟨hw1_mc, hw1_vp, hw1_step⟩ := writeHdrProg_fastStep (hdrOff := hdrRebCandSalt) henv
    (by decide) (henv.fits_of_le_n_max (by omega))
    (by intro h; cases h) hrs_step.2.1 hrs_step.2.2.1
    (val := fs.rebCandSalt + 1) (s := s1)
  set s2 :=
    (Memory.spec 0).clientState s1 (writeHdrProg ((base, hdrRebCandSalt), fs.rebCandSalt + 1))
  obtain ⟨hw2_mc, hw2_vp, hw2_step⟩ := writeHdrProg_fastStep (hdrOff := hdrRebScanCursor) henv
    (by decide) (henv.fits_const (by decide))
    (by intro h; cases h) hw1_step.2.1 hw1_step.2.2.1
    (val := 0) (s := s2)
  set s3 := (Memory.spec 0).clientState s2 (writeHdrProg ((base, hdrRebScanCursor), 0))
  obtain ⟨hw3_mc, hw3_vp, hw3_step⟩ := writeHdrProg_fastStep (hdrOff := hdrRebInsCount) henv
    (by decide) (henv.fits_const (by decide))
    (by intro h; cases h) hw2_step.2.1 hw2_step.2.2.1
    (val := 0) (s := s3)
  dsimp only
  unfold delMoveRebCollisionProg
  simp only [cp, pure_bind]
  have hs'_eq : (Memory.spec 0).clientState s
      (resetBTreeSliceGenProg ((cp, base), rIdx) >>= fun _ =>
        readHdrProg (base, hdrRebCandSalt) >>= fun cand =>
        writeHdrProg ((base, hdrRebCandSalt), cand + 1) >>= fun _ =>
        writeHdrProg ((base, hdrRebScanCursor), 0) >>= fun _ =>
        writeHdrProg ((base, hdrRebInsCount), 0)) =
      (Memory.spec 0).clientState s3 (writeHdrProg ((base, hdrRebInsCount), 0)) := by
    rw [clientState_bind, clientState_bind, hst_c, hres_c, clientState_bind,
      clientState_bind]
  rw [hs'_eq]
  refine ⟨?_, ?_, ((hrs_step.trans hw1_step).trans hw2_step).trans hw3_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    dsimp only [s1, s2, s3, cp] at hrs_mc hst_c hres_c hmc_c hw1_mc hw2_mc hw3_mc ⊢
    rw [hst_c, hres_c, hmc_c]; omega
  · refine validProg_bind hrs_vp ?_
    refine validProg_bind hvp_c ?_; rw [hst_c, hres_c]
    exact validProg_bind hw1_vp (validProg_bind hw2_vp hw3_vp)

/-- Sub-helper 6.2c (insert+inc): insert `(fp_cand_last, loc_del)` into `rIdx` and increment
`rebInsCount`. -/
@[irreducible] private def delMoveRebInsertIncProg :
    ((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, base), rIdx), (fp_cand_last, loc_del)) => do
    let z1 ← pure 1
    btreeInsertGenProg ((((cp, base), rIdx), fp_cand_last), loc_del)
    let ins ← readHdrProg (base, hdrRebInsCount)
    let ins1 ← pure (ins + z1)
    writeHdrProg ((base, hdrRebInsCount), ins1)

private theorem realizes_delMoveRebInsertInc :
    Realizes .exact delMoveRebInsertIncProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), rIdx), (fp_cand_last, loc_del)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (rm : ℕ → Option ℕ),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          rIdx < 3 * numBucketsWhp n_max ∧
          loc_del < totalLocalCoordsWhp n_max ∧
          fp_cand_last < 2 ^ fpBitsWhp n_max ∧
          fs.rebInsCount < 8 * (slabScale n_max) ^ 12 ∧
          ValidWhpSlice n_max fs.rebInsCount (fs.slices rIdx) rm)
      (fun _ _ => 0) := by
  unfold delMoveRebInsertIncProg
  have hbi := realizes_btreeInsertGen
  have hrh := realizes_readHdr
  have hwh := realizes_writeHdr
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, rIdx⟩, ⟨fp_cand_last, loc_del⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, rm, henv, rfl, hseed, hrep, hrIdx,
      hld, hfp, hins_lt, hv_r⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hML12 := numBucketsWhp_mul_scale_pow12_le hth
    have h8L12 : 8 * (slabScale n_max) ^ 12 ≤ n_max :=
      (Nat.mul_le_mul_right _ (by have := (large_bounds_lt_n_max hth).1; omega)).trans hML12
    have hval_ld := loc_lt_two_pow_valLaneBits hld
    obtain ⟨_, _, hbi_step⟩ :=
      btreeInsertGenProg_fastStep henv hrIdx hins_lt.le hseed hrep hv_r hfp hval_ld (s := s)
    set s_bi := (Memory.spec 0).clientState s
      (btreeInsertGenProg
        ((((mkWhpCoreParams c U V w n_max, base), rIdx), fp_cand_last), loc_del))
    obtain ⟨hst_i, hres_i, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebInsCount)
      (by dsimp [hdrRebInsCount]; omega) (s := s_bi)
    have hmem_i : s_bi.mem (base + hdrRebInsCount) = fs.rebInsCount :=
      hbi_step.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1
    have hfit_i : Fits w
        ((Memory.spec 0).clientResult s_bi (readHdrProg (base, hdrRebInsCount)) + 1) := by
      rw [hres_i, hmem_i]; exact henv.fits_of_le_n_max (by omega)
    dsimp only [s_bi] at hst_i hfit_i
    simp only [hst_i] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact hfit_i
    | exact ⟨c, U, V, w, n_max, fs.rebInsCount, fs.slices rIdx, rm,
        henv, rfl, hrIdx, hins_lt.le, hrep.slice_rep hrIdx, hv_r, hfp, hval_ld⟩
  )

private theorem delMoveRebInsertIncProg_fastStep {c U V w n_max base rIdx loc_del fp_cand_last : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {rm : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hrIdx : rIdx < 3 * numBucketsWhp n_max)
    (hld : loc_del < totalLocalCoordsWhp n_max)
    (hfp : fp_cand_last < 2 ^ fpBitsWhp n_max)
    (hins_lt : fs.rebInsCount < 8 * (slabScale n_max) ^ 12)
    (hv_r : ValidWhpSlice n_max fs.rebInsCount (fs.slices rIdx) rm)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := delMoveRebInsertIncProg
      (((mkWhpCoreParams c U V w n_max, base), rIdx), (fp_cand_last, loc_del))
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 2428 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        slices := Function.update fs.slices rIdx
          (btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs.slices rIdx) fp_cand_last loc_del)
        rebInsCount := fs.rebInsCount + 1 } s s' := by
  have hth := henv.2.2.2.1
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have hML12 := numBucketsWhp_mul_scale_pow12_le hth
  have h8L12 : 8 * (slabScale n_max) ^ 12 ≤ n_max :=
    (Nat.mul_le_mul_right _ (by have := (large_bounds_lt_n_max hth).1; omega)).trans hML12
  have hval_ld := loc_lt_two_pow_valLaneBits hld
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hbi_mc, hbi_vp, hbi_step⟩ :=
    btreeInsertGenProg_fastStep henv hrIdx hins_lt.le hseed hrep hv_r hfp hval_ld (s := s)
  set s_bi := (Memory.spec 0).clientState s
    (btreeInsertGenProg ((((cp, base), rIdx), fp_cand_last), loc_del))
  obtain ⟨hst_i, hres_i, hmc_i, hvp_i⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebInsCount)
    (by dsimp [hdrRebInsCount]; omega) (s := s_bi)
  rw [hbi_step.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1] at hres_i
  obtain ⟨hwh_mc, hwh_vp, hwh_step⟩ := writeHdrProg_fastStep (hdrOff := hdrRebInsCount) henv
    (by decide) (henv.fits_of_le_n_max (by omega))
    (by intro h; cases h) hbi_step.2.1 hbi_step.2.2.1
    (val := fs.rebInsCount + 1) (s := s_bi)
  dsimp only
  unfold delMoveRebInsertIncProg
  simp only [cp, pure_bind]
  have hs'_eq : (Memory.spec 0).clientState s
      (btreeInsertGenProg ((((cp, base), rIdx), fp_cand_last), loc_del) >>= fun _ =>
        readHdrProg (base, hdrRebInsCount) >>= fun ins =>
        writeHdrProg ((base, hdrRebInsCount), ins + 1)) =
      (Memory.spec 0).clientState s_bi
        (writeHdrProg ((base, hdrRebInsCount), fs.rebInsCount + 1)) := by
    rw [clientState_bind, clientState_bind]
    dsimp only [s_bi, cp] at hst_i hres_i ⊢
    rw [hst_i, hres_i]
  rw [hs'_eq]
  refine ⟨?_, ?_, hbi_step.trans hwh_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    dsimp only [s_bi, cp] at hbi_mc hst_i hres_i hmc_i hwh_mc ⊢
    rw [hst_i, hres_i, hmc_i]; omega
  · refine validProg_bind hbi_vp ?_
    dsimp only [s_bi, cp] at hst_i hres_i hvp_i hwh_vp ⊢
    refine validProg_bind hvp_i ?_; rw [hst_i, hres_i]; exact hwh_vp

/-- Sub-helper 6.2c (active branch): relocate `loc_last → loc_del` in `rebSlice[b]` once
`rebAct = 1` and `st_last ∈ {1, 2 + oldEp}` hold. -/
@[irreducible] private def delMoveRebActiveProg :
    (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((((cp, base), b), (loc_del, loc_last)), fp_cand_last) => do
    let z1 ← pure 1
    let rebCur ← readHdrProg (base, hdrRebScanCursor)
    let rIdx ← readRebSliceIdxGenProg ((cp, base), b)
    if loc_last < rebCur then
      btreeUpdateGenProg ((((cp, base), rIdx), fp_cand_last), loc_del)
    else if loc_del < rebCur then do
      let lk ← btreeLookupGenProg (((cp, base), rIdx), fp_cand_last)
      if lk.1 = z1 then
        delMoveRebCollisionProg ((cp, base), rIdx)
      else
        delMoveRebInsertIncProg (((cp, base), rIdx), (fp_cand_last, loc_del))
    else
      pure ()

private theorem realizes_delMoveRebActive :
    Realizes .exact delMoveRebActiveProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), (loc_del, _)), fp_cand_last) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (rm : ℕ → Option ℕ),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.rebSliceIdx b < 3 * numBucketsWhp n_max ∧
          loc_del < totalLocalCoordsWhp n_max ∧
          fp_cand_last < 2 ^ fpBitsWhp n_max ∧
          fs.rebCandSalt < sMaxWhp c n_max ∧
          fs.rebInsCount < 8 * (slabScale n_max) ^ 12 ∧
          ValidWhpSlice n_max fs.rebInsCount (fs.slices (fs.rebSliceIdx b)) rm)
      (fun _ _ => 0) := by
  unfold delMoveRebActiveProg
  have hrh := realizes_readHdr
  have hrs := realizes_readRebSliceIdxGen
  have hbu := realizes_btreeUpdateGen
  have hbl := realizes_btreeLookupGen
  have hrc := realizes_delMoveRebCollision
  have hri := realizes_delMoveRebInsertInc
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, ⟨loc_del, loc_last⟩⟩, fp_cand_last⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, rm, henv, rfl, hseed, hrep, hb, hrIdx,
      hld, hfp, hcs_lt, hins_lt, hv_r⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hval_ld := loc_lt_two_pow_valLaneBits hld
    obtain ⟨hst_rc, hres_rc, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebScanCursor)
      (by dsimp [hdrRebScanCursor]; omega) (s := s)
    obtain ⟨hrs_st, hrs_res, _, _⟩ := readRebSliceIdxGenProg_spec henv hb hrep (s := s)
    obtain ⟨hbl_st, _, _, _⟩ := btreeLookupGenProg_spec henv hrIdx hins_lt.le
      (hrep.slice_rep hrIdx) hv_r hfp (s := s)
    simp only [hst_rc, hres_rc, hrs_st, hrs_res, hbl_st, wp_large_M hth] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact hb
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact ⟨c, U, V, w, n_max, fs.rebInsCount, fs.slices (fs.rebSliceIdx b), rm,
        henv, rfl, hrIdx, hins_lt.le, hrep.slice_rep hrIdx, hv_r, hfp, hval_ld⟩
    | exact ⟨c, U, V, w, n_max, fs.rebInsCount, fs.slices (fs.rebSliceIdx b), rm,
        henv, rfl, hrIdx, hins_lt.le, hrep.slice_rep hrIdx, hv_r, hfp⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, hrIdx, hcs_lt⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, rm, henv, rfl, hseed, hrep, hrIdx, hld, hfp, hins_lt, hv_r⟩
  )

/-- Sub-helper 6.2c: relocate `loc_last → loc_del` in `rebSlice[b]` (`rebQuad`). -/
@[irreducible] private def delMoveRebGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ) → Memory.Prog Unit
  | ((((cp, base), b), (loc_del, loc_last)), ((rebAct, st_last), fp_cand_last)) => do
    let z1 ← pure 1
    let z2 ← pure 2
    let oldEp ← readOldEpProg base
    let tagOld ← pure (z2 + oldEp)
    if rebAct = z1 ∧ (st_last = z1 ∨ st_last = tagOld) then
      delMoveRebActiveProg ((((cp, base), b), (loc_del, loc_last)), fp_cand_last)
    else
      pure ()

private theorem realizes_delMoveRebGen :
    Realizes .exact delMoveRebGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), (loc_del, _)), ((rebAct, _), fp_cand_last)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          b < numBucketsWhp n_max ∧
          fs.rebSliceIdx b < 3 * numBucketsWhp n_max ∧
          loc_del < totalLocalCoordsWhp n_max ∧
          fp_cand_last < 2 ^ fpBitsWhp n_max ∧
          (rebAct = 1 →
            fs.rebCandSalt < sMaxWhp c n_max ∧
            fs.rebInsCount < 8 * (slabScale n_max) ^ 12 ∧
            ∃ rm, ValidWhpSlice n_max fs.rebInsCount (fs.slices (fs.rebSliceIdx b)) rm))
      (fun _ _ => 0) := by
  unfold delMoveRebGenProg
  have hro := realizes_readOldEp
  have hra := realizes_delMoveRebActive
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, ⟨loc_del, loc_last⟩⟩, ⟨⟨rebAct, st_last⟩, fp_cand_last⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, rfl, hseed, hrep, hce, hb, hrIdx,
      hld, hfp, hreb_fn⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have h2w := henv.two_le_w
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    obtain ⟨hst_o, hres_o, _, _⟩ := readOldEpProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce
      hrep.2.2.2.1 (s := s)
    simp only [hst_o, hres_o] at *
    first
    | exact h2w
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | (have h4 : 4 ≤ 2 ^ w := (by decide : 4 ≤ 2 ^ 2).trans (Nat.pow_le_pow_right two_pos h2w)
       have hold : fs.oldEp ≤ 1 := by rcases hce with hc | hc <;> simp [FastState.oldEp, hc]
       change 2 + fs.oldEp < 2 ^ w; omega)
    | (obtain ⟨hcs_lt, hins_lt, rm, hv_r⟩ := hreb_fn (by omega)
       exact ⟨c, U, V, w, n_max, θ, fs, rm, henv, rfl, hseed, hrep, hb, hrIdx,
         hld, hfp, hcs_lt, hins_lt, hv_r⟩)
  )

private theorem delMoveRebGenProg_fastStep
    {c U V w n_max base b loc_del loc_last st_last fp_cand_last : ℕ}
    {rebActiveB : Bool} {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1)
    (hb : b < numBucketsWhp n_max)
    (hrIdx : fs.rebSliceIdx b < 3 * numBucketsWhp n_max)
    (hld : loc_del < totalLocalCoordsWhp n_max)
    (hfp : fp_cand_last < 2 ^ fpBitsWhp n_max)
    (hreb_fn : rebActiveB = true →
      fs.rebCandSalt < sMaxWhp c n_max ∧
      fs.rebInsCount < 8 * (slabScale n_max) ^ 12 ∧
      ∃ rm, ValidWhpSlice n_max fs.rebInsCount (fs.slices (fs.rebSliceIdx b)) rm)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let rebAct := if rebActiveB then 1 else 0
    let prog := delMoveRebGenProg
      ((((mkWhpCoreParams c U V w n_max, base), b), (loc_del, loc_last)),
        ((rebAct, st_last), fp_cand_last))
    let s' := (Memory.spec 0).clientState s prog
    let rIdx := fs.rebSliceIdx b
    let rebQuad :=
      if rebActiveB && decide (st_last = 1 ∨ st_last = 2 + fs.oldEp) then
        if loc_last < fs.rebScanCursor then
          (Function.update fs.slices rIdx
            (btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              (fs.slices rIdx) fp_cand_last loc_del),
           (fs.rebCandSalt, (fs.rebScanCursor, fs.rebInsCount)))
        else if loc_del < fs.rebScanCursor then
          match btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              (fs.slices rIdx) fp_cand_last with
          | some _ =>
            (Function.update fs.slices rIdx (resetBTreeSlice (fs.slices rIdx)),
             (fs.rebCandSalt + 1, (0, 0)))
          | none =>
            (Function.update fs.slices rIdx
              (btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
                (fs.slices rIdx) fp_cand_last loc_del),
             (fs.rebCandSalt, (fs.rebScanCursor, fs.rebInsCount + 1)))
        else (fs.slices, (fs.rebCandSalt, (fs.rebScanCursor, fs.rebInsCount)))
      else (fs.slices, (fs.rebCandSalt, (fs.rebScanCursor, fs.rebInsCount)))
    memoryCost prog s ≤ 2696 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        slices := rebQuad.1
        rebCandSalt := rebQuad.2.1
        rebScanCursor := rebQuad.2.2.1
        rebInsCount := rebQuad.2.2.2 } s s' := by
  have hth := henv.2.2.2.1
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have hval_ld := loc_lt_two_pow_valLaneBits hld
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hst_o, hres_o, hmc_o, hvp_o⟩ := readOldEpProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce
    hrep.2.2.2.1 (s := s)
  have hcond_iff :
      ((if rebActiveB then 1 else 0) = 1 ∧ (st_last = 1 ∨ st_last = 2 + fs.oldEp)) ↔
      (rebActiveB && decide (st_last = 1 ∨ st_last = 2 + fs.oldEp)) = true := by
    cases rebActiveB <;> simp
  dsimp only
  unfold delMoveRebGenProg
  simp only [cp, pure_bind]
  by_cases hcond : (rebActiveB && decide (st_last = 1 ∨ st_last = 2 + fs.oldEp)) = true
  · rw [ite_eq_left hcond]
    have hcond_n := hcond_iff.mpr hcond
    have hrbt : rebActiveB = true := (Bool.and_eq_true _ _).mp hcond |>.1
    obtain ⟨hcs_lt, hins_lt, rm, hv_r⟩ := hreb_fn hrbt
    obtain ⟨hst_rc, hres_rc, hmc_rc, hvp_rc⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebScanCursor)
      (by dsimp [hdrRebScanCursor]; omega) (s := s)
    rw [hrep.2.2.2.2.2.2.2.2.2.2.1] at hres_rc
    obtain ⟨hrs_st, hrs_res, hrs_mc, hrs_vp⟩ := readRebSliceIdxGenProg_spec henv hb hrep (s := s)
    unfold delMoveRebActiveProg
    simp only [pure_bind]
    by_cases hll_r : loc_last < fs.rebScanCursor
    · rw [ite_eq_left hll_r]
      obtain ⟨hbu_mc, hbu_vp, hbu_step⟩ :=
        btreeUpdateGenProg_fastStep henv hrIdx hins_lt.le hseed hrep hv_r hfp hval_ld (s := s)
      have hs'_eq : (Memory.spec 0).clientState s
          (readOldEpProg base >>= fun oldEp =>
            if (if rebActiveB = true then 1 else 0) = 1 ∧ (st_last = 1 ∨ st_last = 2 + oldEp) then
              readHdrProg (base, hdrRebScanCursor) >>= fun rebCur =>
              readRebSliceIdxGenProg ((cp, base), b) >>= fun rIdx =>
              if loc_last < rebCur then
                btreeUpdateGenProg ((((cp, base), rIdx), fp_cand_last), loc_del)
              else if loc_del < rebCur then
                btreeLookupGenProg (((cp, base), rIdx), fp_cand_last) >>= fun lk =>
                if lk.1 = 1 then delMoveRebCollisionProg ((cp, base), rIdx)
                else delMoveRebInsertIncProg (((cp, base), rIdx), (fp_cand_last, loc_del))
              else pure ()
            else pure ()) =
          (Memory.spec 0).clientState s
            (btreeUpdateGenProg ((((cp, base), fs.rebSliceIdx b), fp_cand_last), loc_del)) := by
        rw [clientState_bind, hst_o, hres_o, ite_eq_left hcond_n,
          clientState_bind, hst_rc, hres_rc, clientState_bind, hrs_st, hrs_res,
          ite_eq_left hll_r]
      rw [hs'_eq]
      refine ⟨?_, ?_, hbu_step⟩
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hst_o, hres_o, hmc_o, ite_eq_left hcond_n]
        simp only [memoryCost_bind]
        rw [hst_rc, hres_rc, hmc_rc, hrs_st, hrs_res, hrs_mc, ite_eq_left hll_r]
        omega
      · refine validProg_bind hvp_o ?_; rw [hst_o, hres_o, ite_eq_left hcond_n]
        refine validProg_bind hvp_rc ?_; rw [hst_rc, hres_rc]
        refine validProg_bind hrs_vp ?_; rw [hrs_st, hrs_res, ite_eq_left hll_r]
        exact hbu_vp
    · rw [ite_eq_right hll_r]
      by_cases hld_r : loc_del < fs.rebScanCursor
      · rw [ite_eq_left hld_r]
        obtain ⟨hbl_st, hbl_res, hbl_mc, hbl_vp⟩ :=
          btreeLookupGenProg_spec henv hrIdx hins_lt.le (hrep.slice_rep hrIdx) hv_r hfp (s := s)
        rw [← hv_r.lookup_eq hth hins_lt.le hfp] at hbl_res
        cases hlk : btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs.slices (fs.rebSliceIdx b)) fp_cand_last with
        | some v_hit =>
          rw [hlk] at hbl_res
          obtain ⟨hrc_mc, hrc_vp, hrc_step⟩ :=
            delMoveRebCollisionProg_fastStep henv hrIdx hcs_lt hseed hrep (s := s)
          have hs'_eq : (Memory.spec 0).clientState s
              (readOldEpProg base >>= fun oldEp =>
                if (if rebActiveB = true then 1 else 0) = 1 ∧
                    (st_last = 1 ∨ st_last = 2 + oldEp) then
                  readHdrProg (base, hdrRebScanCursor) >>= fun rebCur =>
                  readRebSliceIdxGenProg ((cp, base), b) >>= fun rIdx =>
                  if loc_last < rebCur then
                    btreeUpdateGenProg ((((cp, base), rIdx), fp_cand_last), loc_del)
                  else if loc_del < rebCur then
                    btreeLookupGenProg (((cp, base), rIdx), fp_cand_last) >>= fun lk =>
                    if lk.1 = 1 then delMoveRebCollisionProg ((cp, base), rIdx)
                    else delMoveRebInsertIncProg (((cp, base), rIdx), (fp_cand_last, loc_del))
                  else pure ()
                else pure ()) =
              (Memory.spec 0).clientState s
                (delMoveRebCollisionProg ((cp, base), fs.rebSliceIdx b)) := by
            rw [clientState_bind, hst_o, hres_o, ite_eq_left hcond_n,
              clientState_bind, hst_rc, hres_rc, clientState_bind, hrs_st, hrs_res,
              ite_eq_right hll_r, ite_eq_left hld_r, clientState_bind, hbl_st, hbl_res,
              ite_eq_left rfl]
          rw [hs'_eq]
          refine ⟨?_, ?_, hrc_step⟩
          · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
            rw [hst_o, hres_o, hmc_o, ite_eq_left hcond_n]
            simp only [memoryCost_bind]
            rw [hst_rc, hres_rc, hmc_rc, hrs_st, hrs_res, hrs_mc, ite_eq_right hll_r,
              ite_eq_left hld_r]
            simp only [memoryCost_bind]
            dsimp only [cp] at hbl_st hbl_res hbl_mc hrc_mc ⊢
            rw [hbl_st, hbl_res, ite_eq_left rfl]; omega
          · refine validProg_bind hvp_o ?_; rw [hst_o, hres_o, ite_eq_left hcond_n]
            refine validProg_bind hvp_rc ?_; rw [hst_rc, hres_rc]
            refine validProg_bind hrs_vp ?_; rw [hrs_st, hrs_res, ite_eq_right hll_r,
              ite_eq_left hld_r]
            refine validProg_bind hbl_vp ?_
            dsimp only [cp] at hbl_st hbl_res hrc_vp ⊢
            rw [hbl_st, hbl_res, ite_eq_left rfl]; exact hrc_vp
        | none =>
          rw [hlk] at hbl_res
          obtain ⟨hri_mc, hri_vp, hri_step⟩ :=
            delMoveRebInsertIncProg_fastStep henv hrIdx hld hfp hins_lt hv_r hseed hrep (s := s)
          have hs'_eq : (Memory.spec 0).clientState s
              (readOldEpProg base >>= fun oldEp =>
                if (if rebActiveB = true then 1 else 0) = 1 ∧
                    (st_last = 1 ∨ st_last = 2 + oldEp) then
                  readHdrProg (base, hdrRebScanCursor) >>= fun rebCur =>
                  readRebSliceIdxGenProg ((cp, base), b) >>= fun rIdx =>
                  if loc_last < rebCur then
                    btreeUpdateGenProg ((((cp, base), rIdx), fp_cand_last), loc_del)
                  else if loc_del < rebCur then
                    btreeLookupGenProg (((cp, base), rIdx), fp_cand_last) >>= fun lk =>
                    if lk.1 = 1 then delMoveRebCollisionProg ((cp, base), rIdx)
                    else delMoveRebInsertIncProg (((cp, base), rIdx), (fp_cand_last, loc_del))
                  else pure ()
                else pure ()) =
              (Memory.spec 0).clientState s
                (delMoveRebInsertIncProg
                  (((cp, base), fs.rebSliceIdx b), (fp_cand_last, loc_del))) := by
            rw [clientState_bind, hst_o, hres_o, ite_eq_left hcond_n,
              clientState_bind, hst_rc, hres_rc, clientState_bind, hrs_st, hrs_res,
              ite_eq_right hll_r, ite_eq_left hld_r, clientState_bind, hbl_st, hbl_res,
              ite_eq_right (by decide : ¬(0 = 1))]
          rw [hs'_eq]
          refine ⟨?_, ?_, hri_step⟩
          · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
            rw [hst_o, hres_o, hmc_o, ite_eq_left hcond_n]
            simp only [memoryCost_bind]
            rw [hst_rc, hres_rc, hmc_rc, hrs_st, hrs_res, hrs_mc, ite_eq_right hll_r,
              ite_eq_left hld_r]
            simp only [memoryCost_bind]
            dsimp only [cp] at hbl_st hbl_res hbl_mc hri_mc ⊢
            rw [hbl_st, hbl_res, ite_eq_right (by decide : ¬(0 = 1))]; omega
          · refine validProg_bind hvp_o ?_; rw [hst_o, hres_o, ite_eq_left hcond_n]
            refine validProg_bind hvp_rc ?_; rw [hst_rc, hres_rc]
            refine validProg_bind hrs_vp ?_; rw [hrs_st, hrs_res, ite_eq_right hll_r,
              ite_eq_left hld_r]
            refine validProg_bind hbl_vp ?_
            dsimp only [cp] at hbl_st hbl_res hri_vp ⊢
            rw [hbl_st, hbl_res, ite_eq_right (by decide : ¬(0 = 1))]; exact hri_vp
      · rw [ite_eq_right hld_r]
        have hs'_eq : (Memory.spec 0).clientState s
            (readOldEpProg base >>= fun oldEp =>
              if (if rebActiveB = true then 1 else 0) = 1 ∧
                  (st_last = 1 ∨ st_last = 2 + oldEp) then
                readHdrProg (base, hdrRebScanCursor) >>= fun rebCur =>
                readRebSliceIdxGenProg ((cp, base), b) >>= fun rIdx =>
                if loc_last < rebCur then
                  btreeUpdateGenProg ((((cp, base), rIdx), fp_cand_last), loc_del)
                else if loc_del < rebCur then
                  btreeLookupGenProg (((cp, base), rIdx), fp_cand_last) >>= fun lk =>
                  if lk.1 = 1 then delMoveRebCollisionProg ((cp, base), rIdx)
                  else delMoveRebInsertIncProg (((cp, base), rIdx), (fp_cand_last, loc_del))
                else pure ()
              else pure ()) = s := by
          rw [clientState_bind, hst_o, hres_o, ite_eq_left hcond_n,
            clientState_bind, hst_rc, hres_rc, clientState_bind, hrs_st, hrs_res,
            ite_eq_right hll_r, ite_eq_right hld_r]; rfl
        rw [hs'_eq]
        refine ⟨?_, ?_, FastStateStep.refl hseed hrep⟩
        · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
          rw [hst_o, hres_o, hmc_o, ite_eq_left hcond_n]
          simp only [memoryCost_bind]
          rw [hst_rc, hres_rc, hmc_rc, hrs_st, hrs_res, hrs_mc, ite_eq_right hll_r,
            ite_eq_right hld_r, memoryCost_pure]; omega
        · refine validProg_bind hvp_o ?_; rw [hst_o, hres_o, ite_eq_left hcond_n]
          refine validProg_bind hvp_rc ?_; rw [hst_rc, hres_rc]
          refine validProg_bind hrs_vp ?_; rw [hrs_st, hrs_res, ite_eq_right hll_r,
            ite_eq_right hld_r]
          exact validProg_pure _
  · rw [ite_eq_right hcond]
    have hncond_n : ¬((if rebActiveB then 1 else 0) = 1 ∧
        (st_last = 1 ∨ st_last = 2 + fs.oldEp)) :=
      fun h => hcond (hcond_iff.mp h)
    have hs'_eq : (Memory.spec 0).clientState s
        (readOldEpProg base >>= fun oldEp =>
          if (if rebActiveB = true then 1 else 0) = 1 ∧
              (st_last = 1 ∨ st_last = 2 + oldEp) then
            delMoveRebActiveProg ((((cp, base), b), (loc_del, loc_last)), fp_cand_last)
          else pure ()) = s := by
      rw [clientState_bind, hst_o, hres_o, ite_eq_right hncond_n]; rfl
    rw [hs'_eq]
    refine ⟨?_, ?_, FastStateStep.refl hseed hrep⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hst_o, hres_o, hmc_o, ite_eq_right hncond_n, memoryCost_pure]; omega
    · refine validProg_bind hvp_o ?_; rw [hst_o, hres_o, ite_eq_right hncond_n]
      exact validProg_pure _

/-- Sub-helper 6.2d: copy `(quotArr[p_last], valArr[p_last], st_last)` into `(p_del, loc_del)`
(`d = ((((cp, base), b), (loc_del, loc_last)), st_last)`). -/
@[irreducible] private def delCopySlotGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((((cp, base), b), (loc_del, loc_last)), st_last) => do
    let p_last ← physSlotGenProg (((cp, base), b), loc_last)
    let p_del ← physSlotGenProg (((cp, base), b), loc_del)
    let q_last ← readQuotGenProg ((cp, base), p_last)
    let v_last ← readValGenProg ((cp, base), p_last)
    writeQuotGenProg (((cp, base), p_del), q_last)
    writeValGenProg (((cp, base), p_del), v_last)
    writeFastLocGenProg ((((cp, base), b), loc_del), st_last)

private theorem realizes_delCopySlotGen :
    Realizes .exact delCopySlotGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), (loc_del, loc_last)), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          loc_del < loc_last ∧
          loc_last < totalLocalCoordsWhp n_max ∧
          (∀ k < loc_last + 1 - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max) ∧
          fs.quotArr (fs.physSlot n_max b loc_last) < 2 ^ quotBitsWhp U n_max ∧
          fs.valArr (fs.physSlot n_max b loc_last) < 2 ^ valBits V)
      (fun _ _ => 0) := by
  unfold delCopySlotGenProg
  have hps := realizes_physSlotGen
  have hrq := realizes_readQuotGen
  have hrv := realizes_readValGen
  have hwq := realizes_writeQuotGen
  have hwv := realizes_writeValGen
  have hwl := realizes_writeFastLocGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, ⟨loc_del, loc_last⟩⟩, st_last⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, rfl, hseed, hrep, hb, hlt, hll, hbp, hq_lt,
      hv_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hld : loc_del < totalLocalCoordsWhp n_max := hlt.trans hll
    have hbp_l : capFrontWhp n_max ≤ loc_last →
        fs.backPtr b (loc_last - capFrontWhp n_max) < poolSizeWhp n_max :=
      fun hcf => hbp _ (by omega)
    have hbp_d : capFrontWhp n_max ≤ loc_del →
        fs.backPtr b (loc_del - capFrontWhp n_max) < poolSizeWhp n_max :=
      fun hcf => hbp _ (by omega)
    obtain ⟨hps1_st, hps1_res, hps1_lt, _, _⟩ :=
      physSlotGenProg_spec henv hb hll hbp_l hrep (s := s)
    obtain ⟨hps2_st, hps2_res, hps2_lt, _, _⟩ :=
      physSlotGenProg_spec henv hb hld hbp_d hrep (s := s)
    obtain ⟨hrq_st, hrq_res, _, _⟩ := readQuotGenProg_spec henv hps1_lt hrep (s := s)
    obtain ⟨hrv_st, hrv_res, _, _⟩ := readValGenProg_spec henv hps1_lt hrep (s := s)
    simp only [hps1_st, hps1_res, hps2_st, hps2_res, hrq_st, hrq_res, hrv_st, hrv_res,
      wp_large_M hth, wp_large_nMax hth, wp_large_totalLoc hth] at *
    first
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hll, hbp_l⟩
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hld, hbp_d⟩
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hps1_lt
    | exact hps2_lt
    | exact hb
    | exact hld
  )

private theorem delCopySlotGenProg_fastStep
    {c U V w n_max base b loc_del loc_last st_last : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hlt : loc_del < loc_last) (hll : loc_last < totalLocalCoordsWhp n_max)
    (hbp : ∀ k < loc_last + 1 - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max)
    (hq_lt : fs.quotArr (fs.physSlot n_max b loc_last) < 2 ^ quotBitsWhp U n_max)
    (hv_lt : fs.valArr (fs.physSlot n_max b loc_last) < 2 ^ valBits V)
    (hst_lt : st_last < 4)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := delCopySlotGenProg
      ((((mkWhpCoreParams c U V w n_max, base), b), (loc_del, loc_last)), st_last)
    let s' := (Memory.spec 0).clientState s prog
    let p_last := fs.physSlot n_max b loc_last
    let p_del := fs.physSlot n_max b loc_del
    memoryCost prog s ≤ 20 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        quotArr := Function.update fs.quotArr p_del (fs.quotArr p_last)
        valArr := Function.update fs.valArr p_del (fs.valArr p_last)
        locState := Function.update fs.locState b
          (Function.update (fs.locState b) loc_del st_last) } s s' := by
  set cp := mkWhpCoreParams c U V w n_max
  have hld : loc_del < totalLocalCoordsWhp n_max := hlt.trans hll
  obtain ⟨hps1_st, hps1_res, hps1_lt, hps1_mc, hps1_vp⟩ :=
    physSlotGenProg_spec henv hb hll (fun hcf => hbp _ (by omega)) hrep (s := s)
  obtain ⟨hps2_st, hps2_res, hps2_lt, hps2_mc, hps2_vp⟩ :=
    physSlotGenProg_spec henv hb hld (fun hcf => hbp _ (by omega)) hrep (s := s)
  obtain ⟨hrq_st, hrq_res, hrq_mc, hrq_vp⟩ := readQuotGenProg_spec henv hps1_lt hrep (s := s)
  obtain ⟨hrv_st, hrv_res, hrv_mc, hrv_vp⟩ := readValGenProg_spec henv hps1_lt hrep (s := s)
  obtain ⟨hwq_mc, hwq_vp, hwq_step⟩ :=
    writeQuotGenProg_fastStep henv hps2_lt hq_lt hseed hrep (s := s)
  set s1 := (Memory.spec 0).clientState s
    (writeQuotGenProg (((cp, base), fs.physSlot n_max b loc_del),
      fs.quotArr (fs.physSlot n_max b loc_last)))
  obtain ⟨hwv_mc, hwv_vp, hwv_step⟩ :=
    writeValGenProg_fastStep henv hps2_lt hv_lt hwq_step.2.1 hwq_step.2.2.1 (s := s1)
  set s2 := (Memory.spec 0).clientState s1
    (writeValGenProg (((cp, base), fs.physSlot n_max b loc_del),
      fs.valArr (fs.physSlot n_max b loc_last)))
  obtain ⟨hwl_mc, hwl_vp, hwl_step⟩ :=
    writeFastLocGenProg_fastStep henv hb hld hst_lt hwv_step.2.1 hwv_step.2.2.1 (s := s2)
  dsimp only
  unfold delCopySlotGenProg
  have hs'_eq : (Memory.spec 0).clientState s
      (physSlotGenProg (((cp, base), b), loc_last) >>= fun p_last =>
        physSlotGenProg (((cp, base), b), loc_del) >>= fun p_del =>
        readQuotGenProg ((cp, base), p_last) >>= fun q_last =>
        readValGenProg ((cp, base), p_last) >>= fun v_last =>
        writeQuotGenProg (((cp, base), p_del), q_last) >>= fun _ =>
        writeValGenProg (((cp, base), p_del), v_last) >>= fun _ =>
        writeFastLocGenProg ((((cp, base), b), loc_del), st_last)) =
      (Memory.spec 0).clientState s2
        (writeFastLocGenProg ((((cp, base), b), loc_del), st_last)) := by
    rw [clientState_bind, hps1_st, hps1_res, clientState_bind, hps2_st, hps2_res,
      clientState_bind, hrq_st, hrq_res, clientState_bind, hrv_st, hrv_res,
      clientState_bind, clientState_bind]
  rw [hs'_eq]
  refine ⟨?_, ?_, (hwq_step.trans hwv_step).trans hwl_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hps1_st, hps1_res, hps2_st, hps2_res, hrq_st, hrq_res, hrq_mc, hrv_st, hrv_res, hrv_mc]
    dsimp only [s1, s2, cp] at hps1_mc hps2_mc hwq_mc hwv_mc hwl_mc ⊢
    omega
  · refine validProg_bind hps1_vp ?_; rw [hps1_st, hps1_res]
    refine validProg_bind hps2_vp ?_; rw [hps2_st, hps2_res]
    refine validProg_bind hrq_vp ?_; rw [hrq_st, hrq_res]
    refine validProg_bind hrv_vp ?_; rw [hrv_st, hrv_res]
    exact validProg_bind hwq_vp (validProg_bind hwv_vp hwl_vp)

/-- Read `(st_last, rKey_last)` at `(b, loc_last)` without mutating memory. -/
@[irreducible] private def delMoveReadStRkGenProg :
    ((WhpParams × ℕ) × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | (((wp, base), b), loc_last) => do
    let st_last ← readFastLocGenProg (((wp.1, base), b), loc_last)
    let rKey_last ← rKeyAtGenProg (((wp, base), b), loc_last)
    pure (st_last, rKey_last)

private theorem realizes_delMoveReadStRkGen :
    Realizes .exact delMoveReadStRkGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      CoordHashPre
      (fun _ _ => 0) := by
  unfold delMoveReadStRkGenProg
  have hrl := realizes_readFastLocGen
  have hrk := realizes_rKeyAtGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, b⟩, loc_last⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, heq_wp, hseed, hrep, hq_all, hb, hll, hbp_ll⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hst_l, _, _, _⟩ := readFastLocGenProg_spec henv hb hll hrep (s := s)
    obtain ⟨hrk_st, _, _, _⟩ := rKeyAtGenProg_spec henv hseed hrep hb hll hbp_ll (s := s)
    simp only [hcp_eq] at *
    simp only [hst_l, hrk_st, wp_large_M hth, wp_large_totalLoc hth] at *
    first
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact hll
    | exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, hq_all, hb, hll, hbp_ll⟩
  )

/-- Read `fpAt (bktSalt b) b loc_last` without mutating memory. -/
@[irreducible] private def readLiveFpAtGenProg :
    ((WhpParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((wp, base), b), loc_last) => do
    let salt_b ← readBktFieldGenProg (((wp.1, base), b), 1)
    fpAtGenProg ((((wp, base), salt_b), b), loc_last)

private theorem realizes_readLiveFpAtGen :
    Realizes .exact readLiveFpAtGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      CoordHashPre
      (fun _ _ => 0) := by
  unfold readLiveFpAtGenProg
  have hrb := realizes_readBktFieldGen
  have hfp := realizes_fpAtGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, b⟩, loc_last⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, heq_wp, hseed, hrep, hq_all, hb, hll, hbp_ll⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hs1_st, _, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 1 < 10)
      hrep (s := s)
    simp only [hcp_eq] at *
    simp only [hs1_st, wp_large_M hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, hq_all, hb, hll, hbp_ll⟩
  )

/-- Read `fpAt rebCandSalt b loc_last` without mutating memory. -/
@[irreducible] private def readCandFpAtGenProg :
    ((WhpParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((wp, base), b), loc_last) => do
    let cand ← readHdrProg (base, hdrRebCandSalt)
    fpAtGenProg ((((wp, base), cand), b), loc_last)

private theorem realizes_readCandFpAtGen :
    Realizes .exact readCandFpAtGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      CoordHashPre
      (fun _ _ => 0) := by
  unfold readCandFpAtGenProg
  have hrh := realizes_readHdr
  have hfp := realizes_fpAtGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, b⟩, loc_last⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, heq_wp, hseed, hrep, hq_all, hb, hll, hbp_ll⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    obtain ⟨hcs_st, _, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebCandSalt)
      (by dsimp [hdrRebCandSalt]; omega) (s := s)
    simp only [hcs_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, hq_all, hb, hll, hbp_ll⟩
  )

/-- Read `(st_last, (rKey_last, (fp_live_last, fp_cand_last)))` for `fastDeleteMoveLastGenProg`
without mutating memory. -/
@[irreducible] private def delMoveReadInfoGenProg :
    ((WhpParams × ℕ) × ℕ) × ℕ → Memory.Prog (ℕ × (ℕ × (ℕ × ℕ)))
  | d => do
    let sr ← delMoveReadStRkGenProg d
    let fp_l ← readLiveFpAtGenProg d
    let fp_c ← readCandFpAtGenProg d
    pure (sr.1, (sr.2, (fp_l, fp_c)))

private theorem delMoveReadInfoGenProg_spec {c U V w n_max base b loc_last : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hb : b < numBucketsWhp n_max)
    (hll : loc_last < totalLocalCoordsWhp n_max)
    (hbp_ll : capFrontWhp n_max ≤ loc_last →
      fs.backPtr b (loc_last - capFrontWhp n_max) < poolSizeWhp n_max) :
    let prog := delMoveReadInfoGenProg (((mkWhpParams c U V w n_max, base), b), loc_last)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (fs.locState b loc_last,
       (fs.rKeyAt c U n_max θ b loc_last,
        (fs.fpAt c U n_max θ (fs.bktSalt b) b loc_last,
         fs.fpAt c U n_max θ fs.rebCandSalt b loc_last))) ∧
    memoryCost prog s ≤ 5 * hashEvalCostWhp c + 18 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  set cp := mkWhpCoreParams c U V w n_max
  set wp := mkWhpParams c U V w n_max
  obtain ⟨hst_l, hres_l, hmc_l, hvp_l⟩ := readFastLocGenProg_spec henv hb hll hrep (s := s)
  obtain ⟨hrk_st, hrk_res, hrk_mc, hrk_vp⟩ :=
    rKeyAtGenProg_spec henv hseed hrep hb hll hbp_ll (s := s)
  obtain ⟨hs1_st, hs1_res, hs1_mc, hs1_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 1 < 10) hrep (s := s)
  simp only [getBktField] at hs1_res
  obtain ⟨hfp1_st, hfp1_res, hfp1_mc, hfp1_vp⟩ :=
    fpAtGenProg_spec henv hseed hrep hb hll hbp_ll (salt := fs.bktSalt b) (s := s)
  obtain ⟨hcs_st, hcs_res, hcs_mc, hcs_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebCandSalt)
    (by dsimp [hdrRebCandSalt]; omega) (s := s)
  rw [hrep.2.2.2.2.2.2.2.2.2.1] at hcs_res
  obtain ⟨hfp2_st, hfp2_res, hfp2_mc, hfp2_vp⟩ :=
    fpAtGenProg_spec henv hseed hrep hb hll hbp_ll (salt := fs.rebCandSalt) (s := s)
  have hsr_st : (Memory.spec 0).clientState s
      (delMoveReadStRkGenProg (((wp, base), b), loc_last)) = s := by
    unfold delMoveReadStRkGenProg; dsimp only; rw [show wp.1 = cp from hwp1]
    rw [clientState_bind, hst_l, hres_l, clientState_bind, hrk_st, hrk_res]; rfl
  have hsr_res : (Memory.spec 0).clientResult s
      (delMoveReadStRkGenProg (((wp, base), b), loc_last)) =
      (fs.locState b loc_last, fs.rKeyAt c U n_max θ b loc_last) := by
    unfold delMoveReadStRkGenProg; dsimp only; rw [show wp.1 = cp from hwp1]
    rw [clientResult_bind, hst_l, hres_l, clientResult_bind, hrk_st, hrk_res]; rfl
  have hsr_mc : memoryCost (delMoveReadStRkGenProg (((wp, base), b), loc_last)) s ≤
      hashEvalCostWhp c + 7 := by
    unfold delMoveReadStRkGenProg; dsimp only; rw [show wp.1 = cp from hwp1]
    simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hst_l, hres_l, hmc_l, hrk_st, hrk_res, memoryCost_pure]
    have hrk_mc' : memoryCost (rKeyAtGenProg (((wp, base), b), loc_last)) s ≤
        hashEvalCostWhp c + 5 := hrk_mc
    omega
  have hsr_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
      (delMoveReadStRkGenProg (((wp, base), b), loc_last)) := by
    unfold delMoveReadStRkGenProg; dsimp only; rw [show wp.1 = cp from hwp1]
    refine validProg_bind hvp_l ?_; rw [hst_l, hres_l]
    refine validProg_bind hrk_vp ?_; rw [hrk_st, hrk_res]
    exact validProg_pure _
  have hfl_st : (Memory.spec 0).clientState s
      (readLiveFpAtGenProg (((wp, base), b), loc_last)) = s := by
    unfold readLiveFpAtGenProg; dsimp only; rw [show wp.1 = cp from hwp1]
    rw [clientState_bind, hs1_st, hs1_res, hfp1_st]
  have hfl_res : (Memory.spec 0).clientResult s
      (readLiveFpAtGenProg (((wp, base), b), loc_last)) =
      fs.fpAt c U n_max θ (fs.bktSalt b) b loc_last := by
    unfold readLiveFpAtGenProg; dsimp only; rw [show wp.1 = cp from hwp1]
    rw [clientResult_bind, hs1_st, hs1_res, hfp1_res]
  have hfl_mc : memoryCost (readLiveFpAtGenProg (((wp, base), b), loc_last)) s ≤
      2 * hashEvalCostWhp c + 6 := by
    unfold readLiveFpAtGenProg; dsimp only; rw [show wp.1 = cp from hwp1]
    simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hs1_st, hs1_res, hs1_mc]
    have hfp1_mc' : memoryCost (fpAtGenProg ((((wp, base), fs.bktSalt b), b), loc_last)) s ≤
        2 * hashEvalCostWhp c + 4 := hfp1_mc
    omega
  have hfl_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
      (readLiveFpAtGenProg (((wp, base), b), loc_last)) := by
    unfold readLiveFpAtGenProg; dsimp only; rw [show wp.1 = cp from hwp1]
    refine validProg_bind hs1_vp ?_; rw [hs1_st, hs1_res]; exact hfp1_vp
  have hfc_st : (Memory.spec 0).clientState s
      (readCandFpAtGenProg (((wp, base), b), loc_last)) = s := by
    unfold readCandFpAtGenProg
    rw [clientState_bind, hcs_st, hcs_res, hfp2_st]
  have hfc_res : (Memory.spec 0).clientResult s
      (readCandFpAtGenProg (((wp, base), b), loc_last)) =
      fs.fpAt c U n_max θ fs.rebCandSalt b loc_last := by
    unfold readCandFpAtGenProg
    rw [clientResult_bind, hcs_st, hcs_res, hfp2_res]
  have hfc_mc : memoryCost (readCandFpAtGenProg (((wp, base), b), loc_last)) s ≤
      2 * hashEvalCostWhp c + 5 := by
    unfold readCandFpAtGenProg
    simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hcs_st, hcs_res, hcs_mc]
    have hfp2_mc' : memoryCost (fpAtGenProg ((((wp, base), fs.rebCandSalt), b), loc_last)) s ≤
        2 * hashEvalCostWhp c + 4 := hfp2_mc
    omega
  have hfc_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
      (readCandFpAtGenProg (((wp, base), b), loc_last)) := by
    unfold readCandFpAtGenProg
    refine validProg_bind hcs_vp ?_; rw [hcs_st, hcs_res]; exact hfp2_vp
  dsimp only
  unfold delMoveReadInfoGenProg
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, hsr_st, hsr_res, clientState_bind, hfl_st, hfl_res,
      clientState_bind, hfc_st, hfc_res]; rfl
  · rw [clientResult_bind, hsr_st, hsr_res, clientResult_bind, hfl_st, hfl_res,
      clientResult_bind, hfc_st, hfc_res]; rfl
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hsr_st, hsr_res, hfl_st, hfl_res, hfc_st, hfc_res, memoryCost_pure]
    dsimp only [wp] at hsr_mc hfl_mc hfc_mc ⊢
    omega
  · refine validProg_bind hsr_vp ?_; rw [hsr_st, hsr_res]
    refine validProg_bind hfl_vp ?_; rw [hfl_st, hfl_res]
    refine validProg_bind hfc_vp ?_; rw [hfc_st, hfc_res]
    exact validProg_pure _

private theorem realizes_delMoveReadInfoGen :
    Realizes .exact delMoveReadInfoGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × (ℕ × ℕ))))
      CoordHashPre
      (fun _ _ => 0) := by
  unfold delMoveReadInfoGenProg
  have hsr := realizes_delMoveReadStRkGen
  have hfl := realizes_readLiveFpAtGen
  have hfc := realizes_readCandFpAtGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, b⟩, loc_last⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, heq_wp, hseed, hrep, hq_all, hb, hll, hbp_ll⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hst_l, hres_l, _, _⟩ := readFastLocGenProg_spec henv hb hll hrep (s := s)
    obtain ⟨hrk_st, hrk_res, _, _⟩ := rKeyAtGenProg_spec henv hseed hrep hb hll hbp_ll (s := s)
    obtain ⟨hs1_st, hs1_res, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 1 < 10) hrep (s := s)
    simp only [getBktField] at hs1_res
    obtain ⟨hfp1_st, _, _, _⟩ :=
      fpAtGenProg_spec henv hseed hrep hb hll hbp_ll (salt := fs.bktSalt b) (s := s)
    have hsr_st : (Memory.spec 0).clientState s
        (delMoveReadStRkGenProg (((mkWhpParams c U V w n_max, base), b), loc_last)) = s := by
      unfold delMoveReadStRkGenProg; dsimp only; rw [hcp_eq]
      rw [clientState_bind, hst_l, hres_l, clientState_bind, hrk_st, hrk_res]; rfl
    have hfl_st : (Memory.spec 0).clientState s
        (readLiveFpAtGenProg (((mkWhpParams c U V w n_max, base), b), loc_last)) = s := by
      unfold readLiveFpAtGenProg; dsimp only; rw [hcp_eq]
      rw [clientState_bind, hs1_st, hs1_res, hfp1_st]
    rw [hsr_st] at *
    rw [hfl_st] at *
    exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, hq_all, hb, hll, hbp_ll⟩
  )

/-- `WhpCoreParams`-only write phase of `fastDeleteMoveLastGenProg` once `info` has been read. -/
@[irreducible] private def delMoveApplyCoreGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × (ℕ × ℕ)))) → Memory.Prog Unit
  | ((((cp, base), b), (loc_del, loc_last)),
     (rebAct, (st_last, (rKey_last, (fp_live_last, fp_cand_last))))) => do
    delMoveBufGenProg ((((cp, base), b), loc_del), (st_last, rKey_last))
    delMoveLiveOmGenProg ((((cp, base), b), (loc_del, loc_last)), (st_last, fp_live_last))
    delMoveRebGenProg ((((cp, base), b), (loc_del, loc_last)), ((rebAct, st_last), fp_cand_last))
    delCopySlotGenProg ((((cp, base), b), (loc_del, loc_last)), st_last)

/-- Complete Substep 2 (`fastDeleteMoveLast`, when `loc_del < loc_last`): relocate `loc_last` into
`loc_del` (`d = ((((wp, base), b), (loc_del, loc_last)), rebAct)`). -/
@[irreducible] private def fastDeleteMoveLastGenProg :
    (((WhpParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((((wp, base), b), (loc_del, loc_last)), rebAct) => do
    let info ← delMoveReadInfoGenProg (((wp, base), b), loc_last)
    delMoveApplyCoreGenProg ((((wp.1, base), b), (loc_del, loc_last)), (rebAct, info))

/-- Precondition for `fastDeleteMoveLastGenProg` on `fs1 = fastDeleteRemove c U n_max θ fs u b
loc_del` under `ValidFastState ... fs dict`. -/
private def FastDelMoveLastPre (w : ℕ) :
    (((WhpParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | ((((wp, base), b), (loc_del, loc_last)), rebAct), s =>
    ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U) (u : Fin U),
      WhpLargeEnv c U V w₀ n_max w base ∧
      wp = mkWhpParams c U V w₀ n_max ∧
      ValidFastState c U V n_max θ fs dict ∧
      b < numBucketsWhp n_max ∧
      fs.bktCount b = loc_last + 1 ∧
      loc_del < loc_last ∧
      rebAct = (if decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
          fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
          fs.rebCollision = 0) then 1 else 0) ∧
      SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
      FastMemRep base c U V w₀ n_max (fastDeleteRemove c U n_max θ fs u b loc_del) s.mem

private theorem fs1_moveLast_invs {c U V n_max b loc_del loc_last : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} (u : Fin U)
    (hv : ValidFastState c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max)
    (hcnt : fs.bktCount b = loc_last + 1)
    (_hlt : loc_del < loc_last) :
    let fs1 := fastDeleteRemove c U n_max θ fs u b loc_del
    let st_last := fs1.locState b loc_last
    let rebActiveB := decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
      fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
      fs.rebCollision = 0)
    loc_last < totalLocalCoordsWhp n_max ∧
    (∀ k < loc_last + 1 - capFrontWhp n_max, fs1.backPtr b k < poolSizeWhp n_max) ∧
    (∀ i < n_max, fs1.quotArr i < 2 ^ quotBitsWhp U n_max) ∧
    fs1.valArr (fs1.physSlot n_max b loc_last) < 2 ^ valBits V ∧
    st_last < 4 ∧
    (st_last = 2 →
      (fs1.buf 0).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
      (fs1.buf 0).itemAlloc < qEpochWhp n_max ∧
      ∃ m0, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs1.buf 0) m0) ∧
    (st_last = 3 →
      (fs1.buf 1).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
      (fs1.buf 1).itemAlloc < qEpochWhp n_max ∧
      ∃ m1, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs1.buf 1) m1) ∧
    (∃ lm1, ValidWhpSlice n_max (fs1.liveInsCount b) (fs1.slices (fs1.liveSliceIdx b)) lm1) ∧
    (fs1.overmarsActive b = 1 →
      fs1.overmarsInsCount b < 8 * (slabScale n_max) ^ 12 ∧
      ∃ om1, ValidWhpSlice n_max (fs1.overmarsInsCount b)
        (fs1.slices (fs1.overmarsSliceIdx b)) om1) ∧
    (rebActiveB = true →
      fs1.rebCandSalt < sMaxWhp c n_max ∧
      fs1.rebInsCount < 8 * (slabScale n_max) ^ 12 ∧
      ∃ rm1, ValidWhpSlice n_max fs1.rebInsCount (fs1.slices (fs1.rebSliceIdx b)) rm1) := by
  intro fs1 st_last rebActiveB
  have hll_b : loc_last < fs.bktCount b := by omega
  have hll_tl : loc_last < totalLocalCoordsWhp n_max := hll_b.trans_le (hv.bktCount_le b hb)
  obtain ⟨hb0, hb1, _, _, _, hne_lo, hne_lr, hne_or,
    ⟨hlic_le, lm, hv_l⟩, hom_fn, hreb_fn⟩ := validFastState_delete_bounds hv hb
  have hv_last : fs.valArr (fs.physSlot n_max b loc_last) < 2 ^ valBits V :=
    val_lt_two_pow_valBits (hv.active_item b hb loc_last hll_b).2.2.2
  have hst_lt : st_last < 4 := by
    have := (hv.locState_active b hb loc_last hll_b).2
    dsimp [st_last, fs1, fastDeleteRemove]; omega
  have hrk_u_lt : fpReducedKey c U n_max θ.2 u < 2 ^ (cTabWhp c * bCharWhp n_max) :=
    fpReducedKey_lt c U n_max θ.2 u
  have hfp_u_lt : fpOfSalt c U n_max θ.2 (fs.bktSalt b) u < 2 ^ fpBitsWhp n_max := by
    unfold fpOfSalt
    by_cases hs : fs.bktSalt b < sMaxWhp c n_max <;> simp only [hs, ↓reduceDIte]
    · exact fpHash_lt c U n_max θ.2 ⟨_, hs⟩ u
    · exact Nat.two_pow_pos _
  have hfpc_u_lt : fpOfSalt c U n_max θ.2 fs.rebCandSalt u < 2 ^ fpBitsWhp n_max := by
    unfold fpOfSalt
    by_cases hs : fs.rebCandSalt < sMaxWhp c n_max <;> simp only [hs, ↓reduceDIte]
    · exact fpHash_lt c U n_max θ.2 ⟨_, hs⟩ u
    · exact Nat.two_pow_pos _
  refine ⟨hll_tl,
    fun k hk => (hv.backPtr_valid b hb k (by omega)).1,
    fun i _ => (hv.qv_global i).1,
    hv_last, hst_lt,
    fun h2 => ?_, fun h3 => ?_, ?_, fun ha1 => ?_, fun hrbt => ?_⟩
  · obtain ⟨hna0, hia0, m0, hv0⟩ := hb0 loc_last hll_b h2
    dsimp only [fs1, fastDeleteRemove]
    by_cases hd2 : fs.locState b loc_del = 2
    · rw [ite_eq_left hd2, Function.update_self]
      obtain ⟨hv0', hna_e, hia_e, _, _⟩ := hv0.delete_spec hrk_u_lt
      exact ⟨hna_e ▸ hna0, hia_e ▸ hia0, _, hv0'⟩
    · rw [ite_eq_right hd2]
      split_ifs with hd3
      · rw [Function.update_of_ne (by decide : (0 : ℕ) ≠ 1)]
        exact ⟨hna0, hia0, m0, hv0⟩
      · exact ⟨hna0, hia0, m0, hv0⟩
  · obtain ⟨hna1, hia1, m1, hv1⟩ := hb1 loc_last hll_b h3
    dsimp only [fs1, fastDeleteRemove]
    by_cases hd2 : fs.locState b loc_del = 2
    · rw [ite_eq_left hd2, Function.update_of_ne (by decide : (1 : ℕ) ≠ 0)]
      exact ⟨hna1, hia1, m1, hv1⟩
    · rw [ite_eq_right hd2]
      by_cases hd3 : fs.locState b loc_del = 3
      · rw [ite_eq_left hd3, Function.update_self]
        obtain ⟨hv1', hna_e, hia_e, _, _⟩ := hv1.delete_spec hrk_u_lt
        exact ⟨hna_e ▸ hna1, hia_e ▸ hia1, _, hv1'⟩
      · rw [ite_eq_right hd3]
        exact ⟨hna1, hia1, m1, hv1⟩
  · -- `liveSlice` in `fs1`
    have hsl_l : fs1.slices (fs.liveSliceIdx b) =
        if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_del) then
          btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs.slices (fs.liveSliceIdx b)) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)
        else fs.slices (fs.liveSliceIdx b) := by
      dsimp only [fs1, fastDeleteRemove]
      by_cases hr : (decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
          fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
          fs.rebCollision = 0) && decide (loc_del < fs.rebScanCursor ∧
          (fs.locState b loc_del = 1 ∨ fs.locState b loc_del = 2 + fs.oldEp))) = true
      · rw [ite_eq_left hr, Function.update_of_ne hne_lr]
        by_cases ho : fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
            inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_del) = true
        · rw [ite_eq_left ho, Function.update_of_ne hne_lo, ite_eq_left ho.2.2,
            ite_eq_left ho.2.2, Function.update_self]
        · rw [ite_eq_right ho]
          by_cases hin :
              inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_del) = true
          · rw [ite_eq_left hin, ite_eq_left hin, Function.update_self]
          · rw [ite_eq_right hin, ite_eq_right hin]
      · rw [ite_eq_right hr]
        by_cases ho : fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
            inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_del) = true
        · rw [ite_eq_left ho, Function.update_of_ne hne_lo, ite_eq_left ho.2.2,
            ite_eq_left ho.2.2, Function.update_self]
        · rw [ite_eq_right ho]
          by_cases hin :
              inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_del) = true
          · rw [ite_eq_left hin, ite_eq_left hin, Function.update_self]
          · rw [ite_eq_right hin, ite_eq_right hin]
    change ∃ lm1, ValidWhpSlice n_max (fs.liveInsCount b) (fs1.slices (fs.liveSliceIdx b)) lm1
    rw [hsl_l]
    split_ifs
    · exact ⟨_, hv_l.delete_spec hv.hth hlic_le hfp_u_lt⟩
    · exact ⟨lm, hv_l⟩
  · -- `overmarsSlice` in `fs1`
    obtain ⟨hins_om, om, hv_om⟩ := hom_fn ha1
    refine ⟨hins_om, ?_⟩
    have hsl_o : fs1.slices (fs.overmarsSliceIdx b) =
        if fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
            inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_del) then
          btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs.slices (fs.overmarsSliceIdx b)) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)
        else fs.slices (fs.overmarsSliceIdx b) := by
      dsimp only [fs1, fastDeleteRemove]
      by_cases hr : (decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
          fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
          fs.rebCollision = 0) && decide (loc_del < fs.rebScanCursor ∧
          (fs.locState b loc_del = 1 ∨ fs.locState b loc_del = 2 + fs.oldEp))) = true
      · rw [ite_eq_left hr, Function.update_of_ne hne_or]
        by_cases ho : fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
            inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_del) = true
        · rw [ite_eq_left ho, Function.update_self, ite_eq_left ho, ite_eq_left ho.2.2,
            Function.update_of_ne hne_lo.symm]
        · rw [ite_eq_right ho, ite_eq_right ho]
          by_cases hin :
              inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_del) = true
          · rw [ite_eq_left hin, Function.update_of_ne hne_lo.symm]
          · rw [ite_eq_right hin]
      · rw [ite_eq_right hr]
        by_cases ho : fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
            inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_del) = true
        · rw [ite_eq_left ho, Function.update_self, ite_eq_left ho, ite_eq_left ho.2.2,
            Function.update_of_ne hne_lo.symm]
        · rw [ite_eq_right ho, ite_eq_right ho]
          by_cases hin :
              inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_del) = true
          · rw [ite_eq_left hin, Function.update_of_ne hne_lo.symm]
          · rw [ite_eq_right hin]
    change ∃ om1, ValidWhpSlice n_max (fs.overmarsInsCount b)
      (fs1.slices (fs.overmarsSliceIdx b)) om1
    rw [hsl_o]
    split_ifs
    · exact ⟨_, hv_om.delete_spec hv.hth hins_om.le hfp_u_lt⟩
    · exact ⟨om, hv_om⟩
  · -- `rebSlice` in `fs1`
    have hcs_lt : fs.rebCandSalt < sMaxWhp c n_max := (of_decide_eq_true hrbt).2.2.2.1
    obtain ⟨hins_r, rm, hv_r⟩ := hreb_fn hrbt
    refine ⟨hcs_lt, hins_r, ?_⟩
    have hsl_r : fs1.slices (fs.rebSliceIdx b) =
        if rebActiveB && decide (loc_del < fs.rebScanCursor ∧
            (fs.locState b loc_del = 1 ∨ fs.locState b loc_del = 2 + fs.oldEp)) then
          btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs.slices (fs.rebSliceIdx b)) (fpOfSalt c U n_max θ.2 fs.rebCandSalt u)
        else fs.slices (fs.rebSliceIdx b) := by
      dsimp only [fs1, fastDeleteRemove, rebActiveB]
      have h_sub : (if fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
            inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_del) then
          Function.update
            (if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_del) then
              Function.update fs.slices (fs.liveSliceIdx b)
                (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
                  (fs.slices (fs.liveSliceIdx b)) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u))
             else fs.slices)
            (fs.overmarsSliceIdx b)
            (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              ((if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_del) then
                  Function.update fs.slices (fs.liveSliceIdx b)
                    (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
                      (fs.slices (fs.liveSliceIdx b)) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u))
                else fs.slices) (fs.overmarsSliceIdx b))
              (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u))
        else if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_del) then
          Function.update fs.slices (fs.liveSliceIdx b)
            (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              (fs.slices (fs.liveSliceIdx b)) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u))
        else fs.slices) (fs.rebSliceIdx b) = fs.slices (fs.rebSliceIdx b) := by
        by_cases ho : fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
            inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_del) = true
        · rw [ite_eq_left ho, Function.update_of_ne hne_or.symm, ite_eq_left ho.2.2,
            Function.update_of_ne hne_lr.symm]
        · rw [ite_eq_right ho]
          by_cases hin :
              inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc_del) = true
          · rw [ite_eq_left hin, Function.update_of_ne hne_lr.symm]
          · rw [ite_eq_right hin]
      by_cases h_reb : (decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
          fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
          fs.rebCollision = 0) && decide (loc_del < fs.rebScanCursor ∧
          (fs.locState b loc_del = 1 ∨ fs.locState b loc_del = 2 + fs.oldEp))) = true
      · rw [ite_eq_left h_reb, Function.update_self, ite_eq_left h_reb, h_sub]
      · rw [ite_eq_right h_reb, ite_eq_right h_reb, h_sub]
    change ∃ rm1, ValidWhpSlice n_max fs.rebInsCount (fs1.slices (fs.rebSliceIdx b)) rm1
    rw [hsl_r]
    split_ifs
    · exact ⟨_, hv_r.delete_spec hv.hth hins_r.le hfpc_u_lt⟩
    · exact ⟨rm, hv_r⟩

/-- Precondition for `delMoveApplyCoreGenProg`. -/
private def DelMoveApplyCorePre (w : ℕ) :
    (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × (ℕ × ℕ)))) → Memory.State → Prop
  | ((((cp, base), b), (loc_del, loc_last)), (rebAct, info)), s =>
    ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U) (u : Fin U),
      let fs1 := fastDeleteRemove c U n_max θ fs u b loc_del
      WhpLargeEnv c U V w₀ n_max w base ∧
      cp = mkWhpCoreParams c U V w₀ n_max ∧
      ValidFastState c U V n_max θ fs dict ∧
      b < numBucketsWhp n_max ∧
      fs.bktCount b = loc_last + 1 ∧
      loc_del < loc_last ∧
      rebAct = (if decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
          fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
          fs.rebCollision = 0) then 1 else 0) ∧
      info = (fs1.locState b loc_last,
        (fs1.rKeyAt c U n_max θ b loc_last,
         (fs1.fpAt c U n_max θ (fs1.bktSalt b) b loc_last,
          fs1.fpAt c U n_max θ fs1.rebCandSalt b loc_last))) ∧
      SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
      FastMemRep base c U V w₀ n_max fs1 s.mem

private theorem realizes_delMoveApplyCoreGen :
    Realizes .exact delMoveApplyCoreGenProg
      (WordEncoding.encode
        (α := (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × (ℕ × ℕ))))))
      (WordEncoding.encode (α := Unit))
      DelMoveApplyCorePre
      (fun _ _ => 0) := by
  unfold delMoveApplyCoreGenProg
  have mb1 := realizes_delMoveBufGen
  have mb2 := realizes_delMoveLiveOmGen
  have mb3 := realizes_delMoveRebGen
  have mb4 := realizes_delCopySlotGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, ⟨loc_del, loc_last⟩⟩,
      ⟨rebAct, ⟨st_l, ⟨rk_l, ⟨fpl_l, fpc_l⟩⟩⟩⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, u, henv, rfl, hv, hb, hcnt, hlt, rfl,
      hinfo, hseed, hrep1⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    rcases Prod.mk.inj hinfo with ⟨rfl, hinfo2⟩
    rcases Prod.mk.inj hinfo2 with ⟨rfl, hinfo3⟩
    rcases Prod.mk.inj hinfo3 with ⟨rfl, rfl⟩
    set fs1 := fastDeleteRemove c U n_max θ fs u b loc_del
    obtain ⟨hll_tl, hbp1, hq1, hv1_lt, _, hbuf0_1, hbuf1_1, ⟨lm1, hv_l1⟩, hom1_fn,
      hreb1_fn⟩ := fs1_moveLast_invs u hv hb hcnt hlt
    obtain ⟨_, _, _, _, hr_lt, hne_lo, hne_lr, hne_or, ⟨hlic_le, _⟩, _, _⟩ :=
      validFastState_delete_bounds hv hb
    have hld_tl : loc_del < totalLocalCoordsWhp n_max := hlt.trans hll_tl
    have hbp_ll : capFrontWhp n_max ≤ loc_last →
        fs1.backPtr b (loc_last - capFrontWhp n_max) < poolSizeWhp n_max :=
      fun hcf => hbp1 _ (by omega)
    have hfp_live_lt := fpAt_lt θ fs1 (fs1.bktSalt b) b loc_last
    have hfp_cand_lt := fpAt_lt θ fs1 fs1.rebCandSalt b loc_last
    set st_last := fs1.locState b loc_last
    set rKey_last := fs1.rKeyAt c U n_max θ b loc_last
    set fp_live_last := fs1.fpAt c U n_max θ (fs1.bktSalt b) b loc_last
    set fp_cand_last := fs1.fpAt c U n_max θ fs1.rebCandSalt b loc_last
    obtain ⟨_, _, hstep_b⟩ := delMoveBufGenProg_fastStep (fs := fs1) henv hb hld_tl
      hbuf0_1 hbuf1_1 hseed hrep1 (st_last := st_last) (rKey_last := rKey_last) (s := s)
    set sb := (Memory.spec 0).clientState s
      (delMoveBufGenProg ((((mkWhpCoreParams c U V w n_max, base), b), loc_del),
        (st_last, rKey_last)))
    set fs1b : FastState :=
      { fs1 with
        buf :=
          if st_last = 2 then
            Function.update fs1.buf 0
              (bufInsert (cTabWhp c) (bCharWhp n_max) (fs1.buf 0) rKey_last b loc_del)
          else if st_last = 3 then
            Function.update fs1.buf 1
              (bufInsert (cTabWhp c) (bCharWhp n_max) (fs1.buf 1) rKey_last b loc_del)
          else fs1.buf }
    obtain ⟨_, _, hstep_lo⟩ := delMoveLiveOmGenProg_fastStep (fs := fs1b) henv hv.curEp_or hb
      (hv.roles_valid b hb).1 (hv.roles_valid b hb).2.1 hne_lo hld_tl hfp_live_lt
      hlic_le hv_l1 hom1_fn rfl hstep_b.2.1 hstep_b.2.2.1 (loc_last := loc_last) (s := sb)
    set slo := (Memory.spec 0).clientState sb
      (delMoveLiveOmGenProg ((((mkWhpCoreParams c U V w n_max, base), b), (loc_del, loc_last)),
        (st_last, fp_live_last)))
    set omPair := fastDeleteMoveSlices n_max b loc_del loc_last fp_live_last fs1b
    set fs1lo : FastState :=
      { fs1b with slices := omPair.1, overmarsInsCount := omPair.2 }
    have hreb_slo : decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
        fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
        fs.rebCollision = 0) = true →
        fs1lo.rebCandSalt < sMaxWhp c n_max ∧
        fs1lo.rebInsCount < 8 * (slabScale n_max) ^ 12 ∧
        ∃ rm1, ValidWhpSlice n_max fs1lo.rebInsCount
          (fs1lo.slices (fs1lo.rebSliceIdx b)) rm1 := by
      intro hrbt
      obtain ⟨hcs, hins_r, rm1, hv_r1⟩ := hreb1_fn hrbt
      refine ⟨hcs, hins_r, rm1, ?_⟩
      have hne_lr1 : fs1b.liveSliceIdx b ≠ fs1.rebSliceIdx b := hne_lr
      have hne_or1 : fs1b.overmarsSliceIdx b ≠ fs1.rebSliceIdx b := hne_or
      have hsl_r_eq : omPair.1 (fs1.rebSliceIdx b) = fs1.slices (fs1.rebSliceIdx b) := by
        dsimp only [omPair, fastDeleteMoveSlices]
        split_ifs <;>
          simp only [Function.update_of_ne hne_or1.symm, Function.update_of_ne hne_lr1.symm] <;>
          rfl
      dsimp only [fs1lo, fs1b, FastState.rebSliceIdx, FastState.rebRole] at hv_r1 hsl_r_eq ⊢
      rwa [hsl_r_eq]
    obtain ⟨_, _, hstep_r⟩ := delMoveRebGenProg_fastStep (fs := fs1lo) henv hv.curEp_or hb
      hr_lt hld_tl hfp_cand_lt hreb_slo hstep_lo.2.1 hstep_lo.2.2.1 (loc_last := loc_last)
      (st_last := st_last) (s := slo)
    first
    | exact ⟨c, U, V, w, n_max, fs1, henv, rfl, hrep1, hb, hld_tl, hbuf0_1, hbuf1_1⟩
    | exact ⟨c, U, V, w, n_max, θ, fs1b, lm1, henv, rfl, hstep_b.2.1, hstep_b.2.2.1,
        hv.curEp_or, hb, (hv.roles_valid b hb).1, (hv.roles_valid b hb).2.1, hne_lo,
        hld_tl, hfp_live_lt, hlic_le, hv_l1, hom1_fn⟩
    | (refine ⟨c, U, V, w, n_max, θ, fs1lo, henv, rfl, hstep_lo.2.1, hstep_lo.2.2.1,
         hv.curEp_or, hb, hr_lt, hld_tl, hfp_cand_lt, fun hra1 => ?_⟩
       have hrbt : decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
           fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
           fs.rebCollision = 0) = true := by
         cases hd : decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
           fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
           fs.rebCollision = 0)
         · rw [hd] at hra1; cases hra1
         · rfl
       exact hreb_slo hrbt)
    | exact ⟨c, U, V, w, n_max, θ, _, henv, rfl, hstep_r.2.1, hstep_r.2.2.1,
        hb, hlt, hll_tl, hbp1, hq1 _ (physSlotGenProg_spec henv hb hll_tl hbp_ll hrep1).2.2.1,
        hv1_lt⟩
  )

private theorem realizes_fastDeleteMoveLastGen :
    Realizes .exact fastDeleteMoveLastGenProg
      (WordEncoding.encode (α := (((WhpParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      FastDelMoveLastPre
      (fun _ _ => 0) := by
  unfold fastDeleteMoveLastGenProg
  have hri := realizes_delMoveReadInfoGen
  have hac := realizes_delMoveApplyCoreGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨wp, base⟩, b⟩, ⟨loc_del, loc_last⟩⟩, rebAct⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, u, henv, heq_wp, hv, hb, hcnt, hlt, rfl,
      hseed, hrep1⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    set fs1 := fastDeleteRemove c U n_max θ fs u b loc_del
    obtain ⟨hll_tl, hbp1, hq1, _, _, _, _, _, _, _⟩ := fs1_moveLast_invs u hv hb hcnt hlt
    have hbp_ll : capFrontWhp n_max ≤ loc_last →
        fs1.backPtr b (loc_last - capFrontWhp n_max) < poolSizeWhp n_max :=
      fun hcf => hbp1 _ (by omega)
    obtain ⟨hri_st, hri_res, _, _⟩ :=
      delMoveReadInfoGenProg_spec henv hseed hrep1 hb hll_tl hbp_ll (s := s)
    rw [hcp_eq] at *
    rw [hri_st] at *
    rw [hri_res] at *
    first
    | exact ⟨c, U, V, w, n_max, θ, fs1, henv, rfl, hseed, hrep1, hq1, hb, hll_tl, hbp_ll⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, u, henv, rfl, hv, hb, hcnt, hlt, rfl, rfl,
        hseed, hrep1⟩
  )

private theorem fastDeleteMoveLastGenProg_fastStep {c U V w n_max base b loc_del loc_last : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (u : Fin U)
    (henv : WhpLargeEnv c U V w n_max w base)
    (hv : ValidFastState c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max)
    (hcnt : fs.bktCount b = loc_last + 1)
    (hlt : loc_del < loc_last)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep1 : FastMemRep base c U V w n_max (fastDeleteRemove c U n_max θ fs u b loc_del) s.mem) :
    let rebActiveB : Bool :=
      decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
        fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
        fs.rebCollision = 0)
    let rebAct := if rebActiveB then 1 else 0
    let fs1 := fastDeleteRemove c U n_max θ fs u b loc_del
    let prog := fastDeleteMoveLastGenProg
      ((((mkWhpParams c U V w n_max, base), b), (loc_del, loc_last)), rebAct)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 20 * cTabWhp c + 5 * hashEvalCostWhp c + 5476 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      (fastDeleteMoveLast c U n_max θ b loc_del loc_last rebActiveB fs1) s s' := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  set cp := mkWhpCoreParams c U V w n_max
  set fs1 := fastDeleteRemove c U n_max θ fs u b loc_del
  set rebActiveB : Bool :=
    decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
      fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
      fs.rebCollision = 0)
  set rebAct := if rebActiveB then 1 else 0
  obtain ⟨hll_tl, hbp1, hq1, hv1_lt, hst_lt, hbuf0_1, hbuf1_1, ⟨lm1, hv_l1⟩, hom1_fn,
    hreb1_fn⟩ := fs1_moveLast_invs u hv hb hcnt hlt
  obtain ⟨_, _, _, _, hr_lt, hne_lo, hne_lr, hne_or, ⟨hlic_le, _⟩, _, _⟩ :=
    validFastState_delete_bounds hv hb
  have hld_tl : loc_del < totalLocalCoordsWhp n_max := hlt.trans hll_tl
  have hbp_ll : capFrontWhp n_max ≤ loc_last →
      fs1.backPtr b (loc_last - capFrontWhp n_max) < poolSizeWhp n_max :=
    fun hcf => hbp1 _ (by omega)
  obtain ⟨hri_st, hri_res, hri_mc, hri_vp⟩ :=
    delMoveReadInfoGenProg_spec henv hseed hrep1 hb hll_tl hbp_ll (s := s)
  set st_last := fs1.locState b loc_last
  set rKey_last := fs1.rKeyAt c U n_max θ b loc_last
  set fp_live_last := fs1.fpAt c U n_max θ (fs1.bktSalt b) b loc_last
  set fp_cand_last := fs1.fpAt c U n_max θ fs1.rebCandSalt b loc_last
  have hfp_live_lt := fpAt_lt θ fs1 (fs1.bktSalt b) b loc_last
  have hfp_cand_lt := fpAt_lt θ fs1 fs1.rebCandSalt b loc_last
  obtain ⟨hmc_b, hvp_b, hstep_b⟩ :=
    delMoveBufGenProg_fastStep (fs := fs1) henv hb hld_tl hbuf0_1 hbuf1_1 hseed hrep1
      (st_last := st_last) (rKey_last := rKey_last) (s := s)
  set sb := (Memory.spec 0).clientState s
    (delMoveBufGenProg ((((cp, base), b), loc_del), (st_last, rKey_last)))
  set fs1b : FastState :=
    { fs1 with
      buf :=
        if st_last = 2 then
          Function.update fs1.buf 0
            (bufInsert (cTabWhp c) (bCharWhp n_max) (fs1.buf 0) rKey_last b loc_del)
        else if st_last = 3 then
          Function.update fs1.buf 1
            (bufInsert (cTabWhp c) (bCharWhp n_max) (fs1.buf 1) rKey_last b loc_del)
        else fs1.buf }
  obtain ⟨hmc_lo, hvp_lo, hstep_lo⟩ :=
    delMoveLiveOmGenProg_fastStep (fs := fs1b) henv hv.curEp_or hb (hv.roles_valid b hb).1
      (hv.roles_valid b hb).2.1 hne_lo hld_tl hfp_live_lt hlic_le hv_l1 hom1_fn rfl
      hstep_b.2.1 hstep_b.2.2.1 (loc_last := loc_last) (s := sb)
  set slo := (Memory.spec 0).clientState sb
    (delMoveLiveOmGenProg ((((cp, base), b), (loc_del, loc_last)), (st_last, fp_live_last)))
  set omPair := fastDeleteMoveSlices n_max b loc_del loc_last fp_live_last fs1b
  set fs1lo : FastState :=
    { fs1b with slices := omPair.1, overmarsInsCount := omPair.2 }
  have hreb_slo : rebActiveB = true →
      fs1lo.rebCandSalt < sMaxWhp c n_max ∧
      fs1lo.rebInsCount < 8 * (slabScale n_max) ^ 12 ∧
      ∃ rm1, ValidWhpSlice n_max fs1lo.rebInsCount
        (fs1lo.slices (fs1lo.rebSliceIdx b)) rm1 := by
    intro hrbt
    obtain ⟨hcs, hins_r, rm1, hv_r1⟩ := hreb1_fn hrbt
    refine ⟨hcs, hins_r, rm1, ?_⟩
    have hne_lr1 : fs1b.liveSliceIdx b ≠ fs1.rebSliceIdx b := hne_lr
    have hne_or1 : fs1b.overmarsSliceIdx b ≠ fs1.rebSliceIdx b := hne_or
    have hsl_r_eq : omPair.1 (fs1.rebSliceIdx b) = fs1.slices (fs1.rebSliceIdx b) := by
      dsimp only [omPair, fastDeleteMoveSlices]
      split_ifs <;>
        simp only [Function.update_of_ne hne_or1.symm, Function.update_of_ne hne_lr1.symm] <;>
        rfl
    dsimp only [fs1lo, fs1b, FastState.rebSliceIdx, FastState.rebRole] at hv_r1 hsl_r_eq ⊢
    rwa [hsl_r_eq]
  obtain ⟨hmc_r, hvp_r, hstep_r⟩ :=
    delMoveRebGenProg_fastStep (fs := fs1lo) henv hv.curEp_or hb hr_lt hld_tl
      hfp_cand_lt hreb_slo hstep_lo.2.1 hstep_lo.2.2.1 (loc_last := loc_last)
      (st_last := st_last) (s := slo)
  set sr := (Memory.spec 0).clientState slo
    (delMoveRebGenProg ((((cp, base), b), (loc_del, loc_last)), ((rebAct, st_last), fp_cand_last)))
  set rebQuad :=
    if rebActiveB && decide (st_last = 1 ∨ st_last = 2 + fs1lo.oldEp) then
      if loc_last < fs1lo.rebScanCursor then
        (Function.update fs1lo.slices (fs1lo.rebSliceIdx b)
          (btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs1lo.slices (fs1lo.rebSliceIdx b)) fp_cand_last loc_del),
         (fs1lo.rebCandSalt, (fs1lo.rebScanCursor, fs1lo.rebInsCount)))
      else if loc_del < fs1lo.rebScanCursor then
        match btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs1lo.slices (fs1lo.rebSliceIdx b)) fp_cand_last with
        | some _ =>
          (Function.update fs1lo.slices (fs1lo.rebSliceIdx b)
            (resetBTreeSlice (fs1lo.slices (fs1lo.rebSliceIdx b))),
           (fs1lo.rebCandSalt + 1, (0, 0)))
        | none =>
          (Function.update fs1lo.slices (fs1lo.rebSliceIdx b)
            (btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              (fs1lo.slices (fs1lo.rebSliceIdx b)) fp_cand_last loc_del),
           (fs1lo.rebCandSalt, (fs1lo.rebScanCursor, fs1lo.rebInsCount + 1)))
      else (fs1lo.slices, (fs1lo.rebCandSalt, (fs1lo.rebScanCursor, fs1lo.rebInsCount)))
    else (fs1lo.slices, (fs1lo.rebCandSalt, (fs1lo.rebScanCursor, fs1lo.rebInsCount)))
  set fs1r : FastState :=
    { fs1lo with
      slices := rebQuad.1
      rebCandSalt := rebQuad.2.1
      rebScanCursor := rebQuad.2.2.1
      rebInsCount := rebQuad.2.2.2 }
  have hps_lt1 := (physSlotGenProg_spec henv hb hll_tl hbp_ll hrep1 (s := s)).2.2.1
  obtain ⟨hmc_c, hvp_c, hstep_c⟩ :=
    delCopySlotGenProg_fastStep (fs := fs1r) henv hb hlt hll_tl hbp1 (hq1 _ hps_lt1) hv1_lt
      hst_lt hstep_r.2.1 hstep_r.2.2.1 (s := sr)
  dsimp only
  unfold fastDeleteMoveLastGenProg
  dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
  have hs'_eq : (Memory.spec 0).clientState s
      (delMoveReadInfoGenProg (((mkWhpParams c U V w n_max, base), b), loc_last) >>= fun info =>
        delMoveApplyCoreGenProg ((((cp, base), b), (loc_del, loc_last)), (rebAct, info))) =
      (Memory.spec 0).clientState sr
        (delCopySlotGenProg ((((cp, base), b), (loc_del, loc_last)), st_last)) := by
    rw [clientState_bind, hri_st, hri_res]
    unfold delMoveApplyCoreGenProg; dsimp only
    rw [clientState_bind, clientState_bind, clientState_bind]
  rw [hs'_eq]
  have hfs_eq : { fs1r with
      quotArr := Function.update fs1r.quotArr (fs1r.physSlot n_max b loc_del)
        (fs1r.quotArr (fs1r.physSlot n_max b loc_last))
      valArr := Function.update fs1r.valArr (fs1r.physSlot n_max b loc_del)
        (fs1r.valArr (fs1r.physSlot n_max b loc_last))
      locState := Function.update fs1r.locState b
        (Function.update (fs1r.locState b) loc_del st_last) } =
      fastDeleteMoveLast c U n_max θ b loc_del loc_last rebActiveB fs1 := by
    unfold fastDeleteMoveLast; rfl
  rw [← hfs_eq]
  refine ⟨?_, ?_, ((hstep_b.trans hstep_lo).trans hstep_r).trans hstep_c⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hri_st, hri_res]
    unfold delMoveApplyCoreGenProg; dsimp only
    simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    have hri_mc' : memoryCost (delMoveReadInfoGenProg
        (((mkWhpParams c U V w n_max, base), b), loc_last)) s ≤
        5 * hashEvalCostWhp c + 18 := hri_mc
    dsimp only [sb, slo, sr, cp, fs1, fs1b, st_last, rKey_last, fp_live_last, fp_cand_last, rebAct]
      at hmc_b hmc_lo hmc_r hmc_c ⊢
    omega
  · refine validProg_bind hri_vp ?_; rw [hri_st, hri_res]
    unfold delMoveApplyCoreGenProg; dsimp only
    exact validProg_bind hvp_b (validProg_bind hvp_lo (validProg_bind hvp_r hvp_c))

/-- Backyard slot release helper for `fastDeleteShrinkGenProg` when `capFrontWhp ≤ loc_last`
(`d = (((cp, base), b), loc_last)`). -/
@[irreducible] private def delShrinkBackyardProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, base), b), loc_last) => do
    let z1 ← pure 1
    let k ← pure (loc_last - wpCapFront cp)
    let pSlot ← readBackPtrGenProg (((cp, base), b), k)
    let top ← readHdrProg (base, hdrPoolFreeTop)
    writePoolFreeStackGenProg (((cp, base), top), pSlot)
    let top1 ← pure (top + z1)
    writeHdrProg ((base, hdrPoolFreeTop), top1)

private theorem realizes_delShrinkBackyard :
    Realizes .exact delShrinkBackyardProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), b), loc_last) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs2 : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs2 s.mem ∧
          b < numBucketsWhp n_max ∧
          capFrontWhp n_max ≤ loc_last ∧
          loc_last < totalLocalCoordsWhp n_max ∧
          fs2.poolFreeTop < poolSizeWhp n_max)
      (fun _ _ => 0) := by
  unfold delShrinkBackyardProg
  have hrb := realizes_readBackPtrGen
  have hrh := realizes_readHdr
  have hws := realizes_writePoolFreeStackGen
  have hwh := realizes_writeHdr
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, b⟩, loc_last⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs2, henv, rfl, hrep2, hb, hcf, hll, htop_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have h2tl := (large_index_bounds hth).2.2.1
    have hps_le := (large_index_bounds hth).2.1
    have hk : loc_last - capFrontWhp n_max < capBackWhp n_max := by
      unfold totalLocalCoordsWhp at hll; omega
    obtain ⟨hrb_st, hrb_res, _, _⟩ := readBackPtrGenProg_spec henv hb hk hrep2 (s := s)
    obtain ⟨hrh_st, hrh_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrPoolFreeTop)
      (by dsimp [hdrPoolFreeTop]; omega) (s := s)
    have hmem_top : s.mem (base + hdrPoolFreeTop) = fs2.poolFreeTop := hrep2.2.2.1
    simp only [wp_large_M hth, wp_large_capFront hth, wp_large_capBack hth,
      wp_large_poolSize hth] at *
    simp only [hrb_st, hrb_res, hrh_st, hrh_res, hmem_top] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact hk
    | exact htop_lt
    | omega
  )

/-- Substep 3 (`fastDeleteShrink`): clear `locState b loc_last := 0`, set `bktCount b := loc_last`,
and return any backyard slot to `poolFreeStack` (`d = (((cp, base), b), loc_last)`). -/
@[irreducible] private def fastDeleteShrinkGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, base), b), loc_last) => do
    let z0 ← pure 0
    writeFastLocGenProg ((((cp, base), b), loc_last), z0)
    writeBktFieldGenProg ((((cp, base), b), z0), loc_last)
    let cf ← pure (wpCapFront cp)
    if cf ≤ loc_last then
      delShrinkBackyardProg (((cp, base), b), loc_last)
    else
      pure ()

private theorem realizes_fastDeleteShrinkGen :
    Realizes .exact fastDeleteShrinkGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), b), loc_last) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs2 : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs2 s.mem ∧
          b < numBucketsWhp n_max ∧
          loc_last < totalLocalCoordsWhp n_max ∧
          (capFrontWhp n_max ≤ loc_last →
            fs2.backPtr b (loc_last - capFrontWhp n_max) < poolSizeWhp n_max ∧
            fs2.poolFreeTop < poolSizeWhp n_max))
      (fun _ _ => 0) := by
  unfold fastDeleteShrinkGenProg
  have hwl := realizes_writeFastLocGen
  have hwb := realizes_writeBktFieldGen
  have hsb := realizes_delShrinkBackyard
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, b⟩, loc_last⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs2, henv, rfl, hseed, hrep2, hb, hll, hcf_fn⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h2tl := (large_index_bounds hth).2.2.1
    obtain ⟨_, _, hwl_step⟩ := writeFastLocGenProg_fastStep henv hb hll (by decide : 0 < 4)
      hseed hrep2 (s := s)
    set s1 := (Memory.spec 0).clientState s
      (writeFastLocGenProg ((((mkWhpCoreParams c U V w n_max, base), b), loc_last), 0))
    obtain ⟨_, _, hwb_step⟩ := writeBktFieldGenProg_fastStep henv hb (by decide : 0 < 10)
      (by omega : loc_last ≤ n_max) hwl_step.2.1 hwl_step.2.2.1 (s := s1)
    simp only [setBktField] at hwb_step
    try simp only [wp_large_M hth, wp_large_totalLoc hth, wp_large_capFront hth] at *
    first
    | decide
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact hll
    | (have hcf : capFrontWhp n_max ≤ loc_last := by omega
       exact ⟨c, U, V, w, n_max, _, henv, rfl, hwb_step.2.2.1, hb, hcf, hll, (hcf_fn hcf).2⟩)
  )

private theorem fastDeleteShrinkGenProg_fastStep {c U V w n_max base b loc_last : ℕ}
    {θ : SeedWhp c U n_max} {fs2 : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hll : loc_last < totalLocalCoordsWhp n_max)
    (hcf_fn : capFrontWhp n_max ≤ loc_last →
      fs2.backPtr b (loc_last - capFrontWhp n_max) < poolSizeWhp n_max ∧
      fs2.poolFreeTop < poolSizeWhp n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep2 : FastMemRep base c U V w n_max fs2 s.mem) :
    let prog := fastDeleteShrinkGenProg (((mkWhpCoreParams c U V w n_max, base), b), loc_last)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 16 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (fastDeleteShrink n_max b loc_last fs2) s s' := by
  have hth := henv.2.2.2.1
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have h2tl := (large_index_bounds hth).2.2.1
  have hps_le := (large_index_bounds hth).2.1
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hwl_mc, hwl_vp, hwl_step⟩ := writeFastLocGenProg_fastStep henv hb hll (by decide : 0 < 4)
    hseed hrep2 (s := s)
  set s1 := (Memory.spec 0).clientState s (writeFastLocGenProg ((((cp, base), b), loc_last), 0))
  obtain ⟨hwb_mc, hwb_vp, hwb_step⟩ := writeBktFieldGenProg_fastStep henv hb (by decide : 0 < 10)
    (by omega : loc_last ≤ n_max) hwl_step.2.1 hwl_step.2.2.1 (s := s1)
  set s2 := (Memory.spec 0).clientState s1 (writeBktFieldGenProg ((((cp, base), b), 0), loc_last))
  simp only [setBktField] at hwb_step
  dsimp only
  unfold fastDeleteShrinkGenProg fastDeleteShrink
  dsimp only
  simp only [cp, wp_large_capFront hth, pure_bind]
  by_cases hcf : capFrontWhp n_max ≤ loc_last
  · simp only [hcf, ↓reduceIte]
    have hk : loc_last - capFrontWhp n_max < capBackWhp n_max := by
      unfold totalLocalCoordsWhp at hll; omega
    obtain ⟨hbp_lt, htop_lt⟩ := hcf_fn hcf
    obtain ⟨hrb_st, hrb_res, hrb_mc, hrb_vp⟩ :=
      readBackPtrGenProg_spec henv hb hk hwb_step.2.2.1 (s := s2)
    obtain ⟨hrh_st, hrh_res, hrh_mc, hrh_vp⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrPoolFreeTop)
      (by dsimp [hdrPoolFreeTop]; omega) (s := s2)
    rw [hwb_step.2.2.1.2.2.1] at hrh_res
    obtain ⟨hws_mc, hws_vp, hws_step⟩ := writePoolFreeStackGenProg_fastStep henv htop_lt
      (by omega : fs2.backPtr b (loc_last - capFrontWhp n_max) ≤ n_max)
      hwb_step.2.1 hwb_step.2.2.1 (s := s2)
    set s3 := (Memory.spec 0).clientState s2
      (writePoolFreeStackGenProg
        (((cp, base), fs2.poolFreeTop), fs2.backPtr b (loc_last - capFrontWhp n_max)))
    obtain ⟨hwh_mc, hwh_vp, hwh_step⟩ := writeHdrProg_fastStep (hdrOff := hdrPoolFreeTop) henv
      (by decide) (henv.fits_of_le_n_max (by omega))
      (by intro h; cases h) hws_step.2.1 hws_step.2.2.1
      (val := fs2.poolFreeTop + 1) (s := s3)
    dsimp only [updateFastHdr] at hwh_step
    have hs'_eq : (Memory.spec 0).clientState s
        (writeFastLocGenProg ((((cp, base), b), loc_last), 0) >>= fun _ =>
          writeBktFieldGenProg ((((cp, base), b), 0), loc_last) >>= fun _ =>
          delShrinkBackyardProg (((cp, base), b), loc_last)) =
        (Memory.spec 0).clientState s3
          (writeHdrProg ((base, hdrPoolFreeTop), fs2.poolFreeTop + 1)) := by
      rw [clientState_bind, clientState_bind]
      unfold delShrinkBackyardProg; dsimp only
      simp only [cp, wp_large_capFront hth, pure_bind]
      rw [clientState_bind, hrb_st, hrb_res, clientState_bind, hrh_st, hrh_res,
        clientState_bind]
    rw [hs'_eq]
    refine ⟨?_, ?_, ((hwl_step.trans hwb_step).trans hws_step).trans hwh_step⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      unfold delShrinkBackyardProg; dsimp only
      simp only [wp_large_capFront hth, pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      dsimp only [s1, s2, s3, cp]
        at hwl_mc hwb_mc hrb_st hrb_res hrb_mc hrh_st hrh_res hrh_mc hws_mc hwh_mc ⊢
      rw [hrb_st, hrb_res, hrb_mc, hrh_st, hrh_res, hrh_mc]; omega
    · refine validProg_bind hwl_vp ?_
      refine validProg_bind hwb_vp ?_
      unfold delShrinkBackyardProg; dsimp only
      simp only [wp_large_capFront hth, pure_bind]
      refine validProg_bind hrb_vp ?_; rw [hrb_st, hrb_res]
      refine validProg_bind hrh_vp ?_; rw [hrh_st, hrh_res]
      exact validProg_bind hws_vp hwh_vp
  · simp only [hcf, ↓reduceIte]
    have hs'_eq : (Memory.spec 0).clientState s
        (writeFastLocGenProg ((((cp, base), b), loc_last), 0) >>= fun _ =>
          writeBktFieldGenProg ((((cp, base), b), 0), loc_last) >>= fun _ =>
          pure ()) = s2 := by
      rw [clientState_bind, clientState_bind]; rfl
    rw [hs'_eq]
    refine ⟨?_, ?_, hwl_step.trans hwb_step⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_pure]
      dsimp only [s1, cp] at hwl_mc hwb_mc ⊢
      omega
    · refine validProg_bind hwl_vp ?_
      exact validProg_bind hwb_vp (validProg_pure _)

private theorem poolFreeTop_lt_of_backyard_active {c U V n_max b loc_last : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U}
    (hv : ValidFastState c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max)
    (hcnt : fs.bktCount b = loc_last + 1)
    (hcf : capFrontWhp n_max ≤ loc_last) :
    fs.backPtr b (loc_last - capFrontWhp n_max) < poolSizeWhp n_max ∧
    fs.poolFreeTop < poolSizeWhp n_max := by
  have hbp := (hv.backPtr_valid b hb (loc_last - capFrontWhp n_max) (by omega)).1
  have hpc := hv.pool_conservation
  have hle_sum : fs.bktCount b - capFrontWhp n_max ≤
      ∑ b' ∈ Finset.range (numBucketsWhp n_max), (fs.bktCount b' - capFrontWhp n_max) :=
    Finset.single_le_sum (f := fun b' => fs.bktCount b' - capFrontWhp n_max)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hb)
  exact ⟨hbp, by omega⟩

/-- Optional `fastDeleteMoveLast` wrapper (`if loc_del < loc_last`). -/
@[irreducible] private def fastDeleteOptMoveGenProg :
    (((WhpParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((((wp, base), b), (loc_del, loc_last)), rebAct) =>
    if loc_del < loc_last then
      fastDeleteMoveLastGenProg ((((wp, base), b), (loc_del, loc_last)), rebAct)
    else
      pure ()

private theorem realizes_fastDeleteOptMoveGen :
    Realizes .exact fastDeleteOptMoveGenProg
      (WordEncoding.encode (α := (((WhpParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((((wp, base), b), (loc_del, loc_last)), rebAct) s =>
        loc_del < loc_last →
          FastDelMoveLastPre w ((((wp, base), b), (loc_del, loc_last)), rebAct) s)
      (fun _ _ => 0) := by
  unfold fastDeleteOptMoveGenProg
  have hdm := realizes_fastDeleteMoveLastGen
  realize
  rcases d with ⟨⟨⟨⟨wp, base⟩, b⟩, ⟨loc_del, loc_last⟩⟩, rebAct⟩
  exact h (by assumption)

/-- Read `(bktCount b - 1, rebActiveB)` for `fastDeleteHitGenProg` (`d = ((cp, base), b)`). -/
@[irreducible] private def delHitPrepGenProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cp, base), b) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let cnt ← readBktFieldGenProg (((cp, base), b), z0)
    let loc_last ← pure (cnt - z1)
    let rebAct ← readRebActiveBGenProg ((cp, base), b)
    pure (loc_last, rebAct)

private theorem realizes_delHitPrepGen :
    Realizes .exact delHitPrepGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((cp, base), b) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          1 ≤ fs.bktCount b)
      (fun _ _ => 0) := by
  unfold delHitPrepGenProg
  have hrb := realizes_readBktFieldGen
  have hra := realizes_readRebActiveBGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hb, hcnt1⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hdc_mem : s.mem (base + hdrDirtyCount) ≤ qEpochWhp n_max :=
      hrep.2.2.2.2.2.2.2.1.trans_le hrep.1
    obtain ⟨hc0_st, hc0_res, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 0 < 10) hrep (s := s)
    simp only [getBktField] at hc0_res
    obtain ⟨hra_st, _, _, _⟩ := readRebActiveBGenProg_spec henv hrep (b := b) (s := s)
    simp only [hc0_st, hc0_res, hra_st, wp_large_M hth, wp_large_qEpoch hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | omega
  )

/-- Hit branch of `fastDeleteBodyGenProg` once `fastFindLoc = some loc_del`
(`d = ((((wp, base), b), loc_del), u_val)`). -/
@[irreducible] private def fastDeleteHitGenProg :
    (((WhpParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | ((((wp, base), b), loc_del), u_val) => do
    let prep ← delHitPrepGenProg ((wp.1, base), b)
    fastDeleteRemoveGenProg ((((wp, base), b), loc_del), u_val)
    fastDeleteOptMoveGenProg ((((wp, base), b), (loc_del, prep.1)), prep.2)
    fastDeleteShrinkGenProg (((wp.1, base), b), prep.1)

private theorem realizes_fastDeleteHitGen :
    Realizes .exact fastDeleteHitGenProg
      (WordEncoding.encode (α := (((WhpParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((((wp, base), b), loc_del), u_val) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          b < numBucketsWhp n_max ∧
          loc_del < fs.bktCount b ∧
          u_val < U)
      (fun _ _ => 0) := by
  unfold fastDeleteHitGenProg
  have hdp := realizes_delHitPrepGen
  have hdr := realizes_fastDeleteRemoveGen
  have hdm := realizes_fastDeleteOptMoveGen
  have hds := realizes_fastDeleteShrinkGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨wp, base⟩, b⟩, loc_del⟩, u_val⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hv, hb, hld, hu⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    set u : Fin U := ⟨u_val, hu⟩
    set loc_last := fs.bktCount b - 1
    have hcnt : fs.bktCount b = loc_last + 1 := by omega
    have hll_tl : loc_last < totalLocalCoordsWhp n_max :=
      (by omega : loc_last < fs.bktCount b).trans_le (hv.bktCount_le b hb)
    obtain ⟨hc0_st, hc0_res, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 0 < 10) hrep (s := s)
    simp only [getBktField] at hc0_res
    obtain ⟨hra_st, hra_res, _, _⟩ := readRebActiveBGenProg_spec henv hrep (b := b) (s := s)
    have hprep_st : (Memory.spec 0).clientState s
        (delHitPrepGenProg ((mkWhpCoreParams c U V w n_max, base), b)) = s := by
      unfold delHitPrepGenProg; simp only [pure_bind]
      rw [clientState_bind, hc0_st, hc0_res, clientState_bind, hra_st, hra_res]; rfl
    have hprep_res : (Memory.spec 0).clientResult s
        (delHitPrepGenProg ((mkWhpCoreParams c U V w n_max, base), b)) =
        (loc_last,
         if decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
           fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
           fs.rebCollision = 0) then 1 else 0) := by
      unfold delHitPrepGenProg; simp only [pure_bind]
      rw [clientResult_bind, hc0_st, hc0_res, clientResult_bind, hra_st, hra_res]; rfl
    obtain ⟨_, _, hdr_step⟩ :=
      fastDeleteRemoveGenProg_fastStep u henv hseed hrep hv hb hld (s := s)
    set s1 := (Memory.spec 0).clientState s
      (fastDeleteRemoveGenProg ((((mkWhpParams c U V w n_max, base), b), loc_del), u_val))
    rw [hcp_eq] at *
    try rw [hprep_st]
    try rw [hprep_res]
    first
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, by omega⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv, hb, hld, hu⟩
    | (dsimp only
       intro hlt_ll
       exact ⟨c, U, V, w, n_max, θ, fs, dict, u, henv, rfl, hv, hb, hcnt, hlt_ll, rfl,
         hdr_step.2.1, hdr_step.2.2.1⟩)
    | (dsimp only
       unfold fastDeleteOptMoveGenProg; dsimp only
       by_cases hlt_ll : loc_del < loc_last
       · rw [ite_eq_left hlt_ll]
         obtain ⟨_, _, hdm_step⟩ :=
           fastDeleteMoveLastGenProg_fastStep u henv hv hb hcnt hlt_ll
             hdr_step.2.1 hdr_step.2.2.1 (s := s1)
         exact ⟨c, U, V, w, n_max, θ, _, henv, rfl, hdm_step.2.1, hdm_step.2.2.1, hb, hll_tl,
           fun hcf => poolFreeTop_lt_of_backyard_active (fs := fs) hv hb hcnt hcf⟩
       · rw [ite_eq_right hlt_ll, clientState_pure_whp]
         exact ⟨c, U, V, w, n_max, θ, _, henv, rfl, hdr_step.2.1, hdr_step.2.2.1, hb, hll_tl,
           fun hcf => poolFreeTop_lt_of_backyard_active (fs := fs) hv hb hcnt hcf⟩)
  )

private theorem fastDeleteHitGenProg_fastStep {c U V w n_max base loc_del : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (u : Fin U)
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidFastState c U V n_max θ fs dict)
    (hld : loc_del < fs.bktCount (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val))
    (hq_del : fs.quotArr (fs.physSlot n_max
      (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val) loc_del) =
      keyQuotient (bWhp n_max) u.val) :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let loc_last := fs.bktCount b - 1
    let rebActiveB : Bool :=
      decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
        fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
        fs.rebCollision = 0)
    let fs1 := fastDeleteRemove c U n_max θ fs u b loc_del
    let fs2 :=
      if loc_del < loc_last then
        fastDeleteMoveLast c U n_max θ b loc_del loc_last rebActiveB fs1
      else fs1
    let fsAfterDel := fastDeleteShrink n_max b loc_last fs2
    let prog := fastDeleteHitGenProg ((((mkWhpParams c U V w n_max, base), b), loc_del), u.val)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 22 * cTabWhp c + 7 * hashEvalCostWhp c + 6371 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ fsAfterDel s s' ∧
    OvermarsBucketStepBounds U n_max b fsAfterDel := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  set cp := mkWhpCoreParams c U V w n_max
  set b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
  have hb : b < numBucketsWhp n_max := feistelBucket_lt _ _ _
  set loc_last := fs.bktCount b - 1
  have hcnt : fs.bktCount b = loc_last + 1 := by omega
  have hll_tl : loc_last < totalLocalCoordsWhp n_max :=
    (by omega : loc_last < fs.bktCount b).trans_le (hv.bktCount_le b hb)
  obtain ⟨hc0_st, hc0_res, hc0_mc, hc0_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 0 < 10) hrep (s := s)
  simp only [getBktField] at hc0_res
  obtain ⟨hra_st, hra_res, hra_mc, hra_vp⟩ :=
    readRebActiveBGenProg_spec henv hrep (b := b) (s := s)
  set rebActiveB : Bool := decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
      fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
      fs.rebCollision = 0)
  set rebAct := if rebActiveB then 1 else 0
  have hprep_st : (Memory.spec 0).clientState s (delHitPrepGenProg ((cp, base), b)) = s := by
    unfold delHitPrepGenProg; simp only [pure_bind]
    rw [clientState_bind, hc0_st, hc0_res, clientState_bind, hra_st, hra_res]; rfl
  have hprep_res : (Memory.spec 0).clientResult s (delHitPrepGenProg ((cp, base), b)) =
      (loc_last, rebAct) := by
    unfold delHitPrepGenProg; simp only [pure_bind]
    rw [clientResult_bind, hc0_st, hc0_res, clientResult_bind, hra_st, hra_res]; rfl
  have hprep_mc : memoryCost (delHitPrepGenProg ((cp, base), b)) s ≤ 9 := by
    unfold delHitPrepGenProg
    simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hc0_st, hc0_res, hc0_mc, hra_st, hra_res, memoryCost_pure]
    have hra_mc' : memoryCost (readRebActiveBGenProg ((cp, base), b)) s ≤ 7 := hra_mc
    omega
  have hprep_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
      (delHitPrepGenProg ((cp, base), b)) := by
    unfold delHitPrepGenProg; simp only [pure_bind]
    refine validProg_bind hc0_vp ?_; rw [hc0_st, hc0_res]
    refine validProg_bind hra_vp ?_; rw [hra_st, hra_res]
    exact validProg_pure _
  obtain ⟨hdr_mc, hdr_vp, hdr_step⟩ :=
    fastDeleteRemoveGenProg_fastStep u henv hseed hrep hv hb hld (s := s)
  set fs1 := fastDeleteRemove c U n_max θ fs u b loc_del
  set s1 := (Memory.spec 0).clientState s
    (fastDeleteRemoveGenProg ((((mkWhpParams c U V w n_max, base), b), loc_del), u.val))
  dsimp only
  unfold fastDeleteHitGenProg
  dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
  by_cases hlt_ll : loc_del < fs.bktCount b - 1
  · rw [ite_eq_left hlt_ll]
    have hlt_ll' : loc_del < loc_last := hlt_ll
    obtain ⟨hdm_mc, hdm_vp, hdm_step⟩ :=
      fastDeleteMoveLastGenProg_fastStep u henv hv hb hcnt hlt_ll' hdr_step.2.1 hdr_step.2.2.1
        (s := s1)
    set s2 := (Memory.spec 0).clientState s1
      (fastDeleteMoveLastGenProg
        ((((mkWhpParams c U V w n_max, base), b), (loc_del, loc_last)), rebAct))
    set fs2_rel := fastDeleteMoveLast c U n_max θ b loc_del loc_last rebActiveB fs1
    obtain ⟨hds_mc, hds_vp, hds_step⟩ :=
      fastDeleteShrinkGenProg_fastStep (fs2 := fs2_rel) henv hb hll_tl
        (fun hcf => poolFreeTop_lt_of_backyard_active (fs := fs) hv hb hcnt hcf)
        hdm_step.2.1 hdm_step.2.2.1 (s := s2)
    obtain ⟨hc_rel, _, hom_rel, _⟩ := fastDelete_afterDel_reloc_spec hv u hld hq_del hlt_ll
    have hs'_eq : (Memory.spec 0).clientState s
        (delHitPrepGenProg ((cp, base), b) >>= fun prep =>
          fastDeleteRemoveGenProg ((((mkWhpParams c U V w n_max, base), b), loc_del), u.val) >>=
            fun _ =>
          fastDeleteOptMoveGenProg
            ((((mkWhpParams c U V w n_max, base), b), (loc_del, prep.1)), prep.2) >>= fun _ =>
          fastDeleteShrinkGenProg (((cp, base), b), prep.1)) =
        (Memory.spec 0).clientState s2
          (fastDeleteShrinkGenProg (((cp, base), b), loc_last)) := by
      rw [clientState_bind, hprep_st, hprep_res, clientState_bind, clientState_bind]
      dsimp only
      unfold fastDeleteOptMoveGenProg; dsimp only
      rw [ite_eq_left hlt_ll']
    rw [hs'_eq]
    refine ⟨?_, ?_, (hdr_step.trans hdm_step).trans hds_step,
      OvermarsBucketStepBounds.of_core_and_pre hc_rel hb hom_rel⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hprep_st, hprep_res]; dsimp only
      unfold fastDeleteOptMoveGenProg; dsimp only
      rw [ite_eq_left hlt_ll']
      dsimp only [s1, s2, cp, loc_last, rebAct, rebActiveB, b] at hprep_mc hdr_mc hdm_mc hds_mc ⊢
      omega
    · refine validProg_bind hprep_vp ?_; rw [hprep_st, hprep_res]; dsimp only
      refine validProg_bind hdr_vp ?_
      unfold fastDeleteOptMoveGenProg; dsimp only
      rw [ite_eq_left hlt_ll']
      exact validProg_bind hdm_vp hds_vp
  · rw [ite_eq_right hlt_ll]
    have hlt_ll' : ¬(loc_del < loc_last) := hlt_ll
    obtain ⟨hds_mc, hds_vp, hds_step⟩ :=
      fastDeleteShrinkGenProg_fastStep (fs2 := fs1) henv hb hll_tl
        (fun hcf => poolFreeTop_lt_of_backyard_active (fs := fs) hv hb hcnt hcf)
        hdr_step.2.1 hdr_step.2.2.1 (s := s1)
    obtain ⟨hc_last, _, hom_last, _⟩ := fastDelete_afterDel_last_spec hv u hld hq_del hlt_ll
    have hs'_eq : (Memory.spec 0).clientState s
        (delHitPrepGenProg ((cp, base), b) >>= fun prep =>
          fastDeleteRemoveGenProg ((((mkWhpParams c U V w n_max, base), b), loc_del), u.val) >>=
            fun _ =>
          fastDeleteOptMoveGenProg
            ((((mkWhpParams c U V w n_max, base), b), (loc_del, prep.1)), prep.2) >>= fun _ =>
          fastDeleteShrinkGenProg (((cp, base), b), prep.1)) =
        (Memory.spec 0).clientState s1
          (fastDeleteShrinkGenProg (((cp, base), b), loc_last)) := by
      rw [clientState_bind, hprep_st, hprep_res, clientState_bind, clientState_bind]
      dsimp only
      unfold fastDeleteOptMoveGenProg; dsimp only
      rw [ite_eq_right hlt_ll', clientState_pure_whp]
    rw [hs'_eq]
    refine ⟨?_, ?_, hdr_step.trans hds_step,
      OvermarsBucketStepBounds.of_core_and_pre hc_last hb hom_last⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hprep_st, hprep_res]; dsimp only
      unfold fastDeleteOptMoveGenProg; dsimp only
      rw [ite_eq_right hlt_ll', clientState_pure_whp, memoryCost_pure]
      dsimp only [s1, cp, loc_last, b] at hprep_mc hdr_mc hds_mc ⊢
      omega
    · refine validProg_bind hprep_vp ?_; rw [hprep_st, hprep_res]; dsimp only
      refine validProg_bind hdr_vp ?_
      unfold fastDeleteOptMoveGenProg; dsimp only
      rw [ite_eq_right hlt_ll']
      exact validProg_bind (validProg_pure _) hds_vp

/-- Foreground body of `fastDelete` prior to `overmarsStep`
(`d = (((wp, base), bq), u_val)`). -/
@[irreducible] private def fastDeleteBodyGenProg :
    ((WhpParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | (((wp, base), bq), u_val) => do
    let z1 ← pure 1
    let fl ← fastFindLocBqGenProg (((wp, base), bq), u_val)
    if fl.1 = z1 then
      fastDeleteHitGenProg ((((wp, base), bq.1), fl.2), u_val)
    else
      pure ()

private theorem realizes_fastDeleteBodyGen :
    Realizes .exact fastDeleteBodyGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((wp, base), bq), u_val) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          u_val < U ∧
          bq = (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u_val,
                keyQuotient (bWhp n_max) u_val))
      (fun _ _ => 0) := by
  unfold fastDeleteBodyGenProg
  have hfl := realizes_fastFindLocBqGen
  have hhit := realizes_fastDeleteHitGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, ⟨b, q_val⟩⟩, u_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hv, hu, hbq⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    rcases Prod.mk.inj hbq with ⟨rfl, rfl⟩
    set u : Fin U := ⟨u_val, hu⟩
    have hb : feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u_val < numBucketsWhp n_max :=
      feistelBucket_lt _ _ _
    obtain ⟨hfl_st, hfl_res, _, _⟩ := fastFindLocBqGenProg_spec henv hseed hrep hv u (s := s)
    dsimp only [u] at hfl_st hfl_res
    rw [hfl_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv⟩
    | (rw [hcp_eq, wp_large_M hth]; exact hb)
    | (have hspec := hv.fastFindLoc_spec u
       cases hfind : fastFindLoc c U n_max θ fs u with
       | none =>
         have hhit : ((Memory.spec 0).clientResult s
           (fastFindLocBqGenProg (((mkWhpParams c U V w n_max, base),
             (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u_val,
              keyQuotient (bWhp n_max) u_val)), u_val))).1 = 1 := by assumption
         rw [hfind] at hfl_res; rw [hfl_res] at hhit; cases hhit
       | some loc_del =>
         rw [hfind] at hfl_res hspec
         rw [hfl_res]; dsimp only
         exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv, hb, hspec.1, hu⟩)
  )

private theorem fastDeleteBodyGenProg_fastStep {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (u : Fin U)
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidFastState c U V n_max θ fs dict) :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let q_val := keyQuotient (bWhp n_max) u.val
    let fsAfterDel : FastState :=
      match fastFindLoc c U n_max θ fs u with
      | none => fs
      | some loc_del =>
        let loc_last := fs.bktCount b - 1
        let rebActiveB : Bool :=
          decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
            fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
            fs.rebCollision = 0)
        let fs1 := fastDeleteRemove c U n_max θ fs u b loc_del
        let fs2 :=
          if loc_del < loc_last then
            fastDeleteMoveLast c U n_max θ b loc_del loc_last rebActiveB fs1
          else fs1
        fastDeleteShrink n_max b loc_last fs2
    let prog := fastDeleteBodyGenProg (((mkWhpParams c U V w n_max, base), (b, q_val)), u.val)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 26 * cTabWhp c + 8 * hashEvalCostWhp c + 6675 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ fsAfterDel s s' ∧
    OvermarsBucketStepBounds U n_max b fsAfterDel := by
  set b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
  set q_val := keyQuotient (bWhp n_max) u.val
  have hb : b < numBucketsWhp n_max := feistelBucket_lt _ _ _
  obtain ⟨hfl_st, hfl_res, hfl_mc, hfl_vp⟩ :=
    fastFindLocBqGenProg_spec henv hseed hrep hv u (s := s)
  have hspec := hv.fastFindLoc_spec u
  dsimp only
  unfold fastDeleteBodyGenProg
  simp only [pure_bind]
  cases hfind : fastFindLoc c U n_max θ fs u with
  | none =>
    rw [hfind] at hfl_res
    dsimp only at hfl_res ⊢
    have hs'_eq : (Memory.spec 0).clientState s
        (fastFindLocBqGenProg (((mkWhpParams c U V w n_max, base), (b, q_val)), u.val) >>= fun fl =>
          if fl.1 = 1 then
            fastDeleteHitGenProg ((((mkWhpParams c U V w n_max, base), b), fl.2), u.val)
          else pure ()) = s := by
      rw [clientState_bind, hfl_st, hfl_res]; rfl
    rw [hs'_eq]
    refine ⟨?_, ?_, FastStateStep.refl hseed hrep,
      OvermarsBucketStepBounds.of_core_and_pre hv.toCore hb
        (OvermarsBucketInv.toPre (hv.overmars_valid b hb))⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hfl_st, hfl_res]; dsimp only; simp only [zero_ne_one, ↓reduceIte, memoryCost_pure]
      dsimp only [b, q_val] at hfl_mc ⊢; omega
    · refine validProg_bind hfl_vp ?_
      rw [hfl_st, hfl_res]; exact validProg_pure _
  | some loc_del =>
    rw [hfind] at hfl_res hspec
    dsimp only at hfl_res ⊢
    obtain ⟨hld, hq_del⟩ := hspec
    obtain ⟨hhit_mc, hhit_vp, hhit_step, hhit_bnds⟩ :=
      fastDeleteHitGenProg_fastStep u henv hseed hrep hv hld hq_del (s := s)
    have hs'_eq : (Memory.spec 0).clientState s
        (fastFindLocBqGenProg (((mkWhpParams c U V w n_max, base), (b, q_val)), u.val) >>= fun fl =>
          if fl.1 = 1 then
            fastDeleteHitGenProg ((((mkWhpParams c U V w n_max, base), b), fl.2), u.val)
          else pure ()) =
        (Memory.spec 0).clientState s
          (fastDeleteHitGenProg ((((mkWhpParams c U V w n_max, base), b), loc_del), u.val)) := by
      rw [clientState_bind, hfl_st, hfl_res]; rfl
    rw [hs'_eq]
    refine ⟨?_, ?_, hhit_step, hhit_bnds⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hfl_st, hfl_res]; dsimp only; simp only [↓reduceIte]
      dsimp only [b, q_val] at hfl_mc hhit_mc ⊢; omega
    · refine validProg_bind hfl_vp ?_
      rw [hfl_st, hfl_res]; dsimp only; simp only [↓reduceIte]
      exact hhit_vp

/-- Fast-mode deletion `fastDeleteGenProg` (`d = ((wp, base), u_val)`), refining `fastDelete` in
`O_c(1)` worst-case memory operations. -/
@[irreducible] def fastDeleteGenProg : (WhpParams × ℕ) × ℕ → Memory.Prog Unit
  | ((wp, base), u_val) => do
    let hrt ← mkHashRtGenProg (wp, base)
    let bq ← feistelSplitRtProg (hrt, u_val)
    fastDeleteBodyGenProg (((wp, base), bq), u_val)
    overmarsStepGenProg ((wp, base), bq.1)

theorem realizes_fastDeleteGen :
    Realizes .exact fastDeleteGenProg
      (WordEncoding.encode (α := (WhpParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((wp, base), u_val) s => ValidFastMemPre w wp base s ∧ u_val < wpU wp.1)
      (fun _ _ => 0) := by
  unfold fastDeleteGenProg
  have hmh := realizes_mkHashRtGen
  have hfs := realizes_feistelSplitRt
  have hdb := realizes_fastDeleteBodyGen
  have hom := realizes_overmarsStepGen
  realize
  all_goals (
    rcases d with ⟨⟨wp, base⟩, u_val⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hv⟩, hu_wp⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    have hu : u_val < U := by rw [hcp_eq, wp_large_U hth] at hu_wp; exact hu_wp
    set u : Fin U := ⟨u_val, hu⟩
    obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    obtain ⟨hfs_st, hfs_res, _, _⟩ :=
      feistelSplitRtProg_spec (u_val := u_val) henv hseed (s := s)
    obtain ⟨_, _, hdb_step, hdb_bnds⟩ :=
      fastDeleteBodyGenProg_fastStep u henv hseed hrep hv (s := s)
    dsimp only [u] at hdb_step hdb_bnds
    simp only [hmh_st, hmh_res, hfs_st, hfs_res] at *
    first
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv, hu, rfl⟩
    | exact ⟨c, U, V, w, n_max, θ, _, henv, rfl, hdb_step.2.1, hdb_step.2.2.1, hdb_bnds⟩
  )

theorem fastDeleteGenProg_fastStep {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidFastState c U V n_max θ fs dict)
    (u : Fin U) :
    let prog := fastDeleteGenProg ((mkWhpParams c U V w n_max, base), u.val)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 26 * cTabWhp c + 41 * hashEvalCostWhp c + 46001 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (fastDelete c U n_max θ fs u) s s' := by
  have hth := henv.2.2.2.1
  obtain ⟨hmh_st, hmh_res, hmh_mc, hmh_vp⟩ :=
    mkHashRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base) hth s
  obtain ⟨hfs_st, hfs_res, hfs_mc, hfs_vp⟩ :=
    feistelSplitRtProg_spec (u_val := u.val) henv hseed (s := s)
  obtain ⟨hdb_mc, hdb_vp, hdb_step, hdb_bnds⟩ :=
    fastDeleteBodyGenProg_fastStep u henv hseed hrep hv (s := s)
  set bq := (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val,
             keyQuotient (bWhp n_max) u.val)
  set s1 := (Memory.spec 0).clientState s
    (fastDeleteBodyGenProg (((mkWhpParams c U V w n_max, base), bq), u.val))
  obtain ⟨hom_mc, hom_vp, hom_step⟩ :=
    overmarsStepGenProg_fastStep henv hdb_bnds hdb_step.2.1 hdb_step.2.2.1 (s := s1)
  dsimp only
  unfold fastDeleteGenProg fastDelete
  have hs'_eq : (Memory.spec 0).clientState s
      (mkHashRtGenProg (mkWhpParams c U V w n_max, base) >>= fun hrt =>
        feistelSplitRtProg (hrt, u.val) >>= fun bq' =>
        fastDeleteBodyGenProg (((mkWhpParams c U V w n_max, base), bq'), u.val) >>= fun _ =>
        overmarsStepGenProg ((mkWhpParams c U V w n_max, base), bq'.1)) =
      (Memory.spec 0).clientState s1
        (overmarsStepGenProg ((mkWhpParams c U V w n_max, base), bq.1)) := by
    rw [clientState_bind, hmh_st, hmh_res, clientState_bind, hfs_st, hfs_res,
      clientState_bind]
  rw [hs'_eq]
  refine ⟨?_, ?_, hdb_step.trans hom_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hmh_st, hmh_res, hmh_mc, hfs_st, hfs_res]
    have hfs_mc' : memoryCost (feistelSplitRtProg (mkHashRt c U w n_max base, u.val)) s ≤
        hashEvalCostWhp c := hfs_mc
    dsimp only [s1, bq] at hdb_mc hom_mc ⊢
    omega
  · refine validProg_bind hmh_vp ?_; rw [hmh_st, hmh_res]
    refine validProg_bind hfs_vp ?_; rw [hfs_st, hfs_res]
    exact validProg_bind hdb_vp hom_vp

/-! ## Section 7: Fast-Mode Guarded Insertion / Overwrite (`fastInsertGenProg`) -/

private theorem keyQuotient_lt_pow_quotBits {U n_max : ℕ} (u : Fin U) :
    keyQuotient (bWhp n_max) u.val < 2 ^ quotBitsWhp U n_max := by
  have hu_pow : u.val < 2 ^ keyBits U := u.isLt.trans_le (Nat.le_pow_clog Nat.one_lt_two U)
  unfold keyQuotient quotBitsWhp
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
  exact hu_pow.trans_le (Nat.pow_le_pow_right two_pos (by omega))

private theorem overmarsBucketStepBounds_update_valArr {U n_max b : ℕ}
    {fs : FastState} (vArr' : ℕ → ℕ)
    (hbnds : OvermarsBucketStepBounds U n_max b fs) :
    OvermarsBucketStepBounds U n_max b { fs with valArr := vArr' } := by
  rcases hbnds with ⟨hb, hce, hlr, hor, hcnt, hq, hbp, hact⟩
  refine ⟨hb, hce, hlr, hor, hcnt, hq, hbp, ?_⟩
  unfold overmarsAfterActivate at hact ⊢
  by_cases hc : fs.overmarsActive b = 0 ∧ 5 * (slabScale n_max) ^ 12 ≤ fs.liveInsCount b
  · dsimp only; rw [ite_eq_left hc] at hact ⊢; exact hact
  · dsimp only; rw [ite_eq_right hc] at hact ⊢; exact hact

/-- Overwrite value `v_val` at physical slot `(b, loc)` (`d = (((cp, base), (b, loc)), v_val)`). -/
@[irreducible] private def fastInsertWriteOvGenProg :
    ((WhpCoreParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | (((cp, base), (b, loc)), v_val) => do
    let p ← physSlotGenProg (((cp, base), b), loc)
    writeValGenProg (((cp, base), p), v_val)

private theorem realizes_fastInsertWriteOvGen :
    Realizes .exact fastInsertWriteOvGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), (b, loc)), _) s =>
        PhysSlotPre w (((cp, base), b), loc) s)
      (fun _ _ => 0) := by
  unfold fastInsertWriteOvGenProg
  have hps := realizes_physSlotGen
  have hwv := realizes_writeValGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, ⟨b, loc⟩⟩, v_val⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hb, hloc, hbp⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    obtain ⟨hps_st, hps_res, hps_lt, _, _⟩ := physSlotGenProg_spec henv hb hloc hbp hrep (s := s)
    simp only [hps_st, hps_res, wp_large_nMax hth] at *
    first
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hloc, hbp⟩
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hps_lt
  )

private theorem fastInsertWriteOvGenProg_fastStep {c U V w n_max base b loc v_val : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hloc : loc < totalLocalCoordsWhp n_max)
    (hbp : capFrontWhp n_max ≤ loc → fs.backPtr b (loc - capFrontWhp n_max) < poolSizeWhp n_max)
    (hv_lt : v_val < 2 ^ valBits V)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := fastInsertWriteOvGenProg (((mkWhpCoreParams c U V w n_max, base), (b, loc)), v_val)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 6 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with valArr := Function.update fs.valArr (fs.physSlot n_max b loc) v_val } s s' := by
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hps_st, hps_res, hps_lt, hps_mc, hps_vp⟩ :=
    physSlotGenProg_spec henv hb hloc hbp hrep (s := s)
  obtain ⟨hwv_mc, hwv_vp, hwv_step⟩ :=
    writeValGenProg_fastStep henv hps_lt hv_lt hseed hrep (v_val := v_val) (s := s)
  dsimp only
  unfold fastInsertWriteOvGenProg; dsimp only
  have hs'_eq : (Memory.spec 0).clientState s
      (physSlotGenProg (((cp, base), b), loc) >>= fun p =>
        writeValGenProg (((cp, base), p), v_val)) =
      (Memory.spec 0).clientState s
        (writeValGenProg (((cp, base), fs.physSlot n_max b loc), v_val)) := by
    rw [clientState_bind, hps_st, hps_res]
  rw [hs'_eq]
  refine ⟨?_, ?_, hwv_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hps_st, hps_res]; dsimp only [cp] at hps_mc hwv_mc ⊢; omega
  · refine validProg_bind hps_vp ?_; rw [hps_st, hps_res]; exact hwv_vp

/-- Hit branch of `fastInsert`: overwrite `valArr[physSlot b loc] := v_val` and run `overmarsStep`,
returning `1` (`d = (((wp, base), (b, loc)), v_val)`). -/
@[irreducible] private def fastInsertOverwriteGenProg :
    ((WhpParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog ℕ
  | (((wp, base), (b, loc)), v_val) => do
    fastInsertWriteOvGenProg (((wp.1, base), (b, loc)), v_val)
    overmarsStepGenProg ((wp, base), b)
    pure 1

private theorem realizes_fastInsertOverwriteGen :
    Realizes .exact fastInsertOverwriteGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (((wp, base), (b, loc)), v_val) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          b < numBucketsWhp n_max ∧
          loc < fs.bktCount b ∧
          v_val < V)
      (fun _ _ => 0) := by
  unfold fastInsertOverwriteGenProg
  have hwv := realizes_fastInsertWriteOvGen
  have hom := realizes_overmarsStepGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, ⟨b, loc⟩⟩, v_val⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hv, hb, hloc_b, hv_v⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    have hloc : loc < totalLocalCoordsWhp n_max := hloc_b.trans_le (hv.bktCount_le b hb)
    have hbp : capFrontWhp n_max ≤ loc →
        fs.backPtr b (loc - capFrontWhp n_max) < poolSizeWhp n_max :=
      fun hcf => (hv.backPtr_valid b hb _ (by omega)).1
    have hv_pow := val_lt_two_pow_valBits hv_v
    obtain ⟨_, _, hwv_step⟩ :=
      fastInsertWriteOvGenProg_fastStep henv hb hloc hbp hv_pow hseed hrep (s := s)
    have hbnds0 : OvermarsBucketStepBounds U n_max b fs :=
      OvermarsBucketStepBounds.of_core_and_pre hv.toCore hb
        (OvermarsBucketInv.toPre (hv.overmars_valid b hb))
    have hbnds_ov := overmarsBucketStepBounds_update_valArr
      (Function.update fs.valArr (fs.physSlot n_max b loc) v_val) hbnds0
    rw [hcp_eq] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hloc, hbp⟩
    | exact ⟨c, U, V, w, n_max, θ, _, henv, rfl, hwv_step.2.1, hwv_step.2.2.1, hbnds_ov⟩
  )

private theorem fastInsertOverwriteGenProg_spec {c U V w n_max base b loc v_val : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidFastState c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max) (hloc_b : loc < fs.bktCount b) (hv_v : v_val < V) :
    let prog := fastInsertOverwriteGenProg (((mkWhpParams c U V w n_max, base), (b, loc)), v_val)
    let s' := (Memory.spec 0).clientState s prog
    let fs_ov : FastState :=
      { fs with valArr := Function.update fs.valArr (fs.physSlot n_max b loc) v_val }
    (Memory.spec 0).clientResult s prog = 1 ∧
    memoryCost prog s ≤ 32 * hashEvalCostWhp c + 39332 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (overmarsStep c U n_max θ b fs_ov) s s' := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  set cp := mkWhpCoreParams c U V w n_max
  have hloc : loc < totalLocalCoordsWhp n_max := hloc_b.trans_le (hv.bktCount_le b hb)
  have hbp : capFrontWhp n_max ≤ loc → fs.backPtr b (loc - capFrontWhp n_max) < poolSizeWhp n_max :=
    fun hcf => (hv.backPtr_valid b hb _ (by omega)).1
  have hv_pow := val_lt_two_pow_valBits hv_v
  obtain ⟨hwv_mc, hwv_vp, hwv_step⟩ :=
    fastInsertWriteOvGenProg_fastStep henv hb hloc hbp hv_pow hseed hrep (s := s)
  set s1 := (Memory.spec 0).clientState s
    (fastInsertWriteOvGenProg (((cp, base), (b, loc)), v_val))
  set fs_ov : FastState :=
    { fs with valArr := Function.update fs.valArr (fs.physSlot n_max b loc) v_val }
  have hbnds_ov : OvermarsBucketStepBounds U n_max b fs_ov :=
    overmarsBucketStepBounds_update_valArr _
      (OvermarsBucketStepBounds.of_core_and_pre hv.toCore hb
        (OvermarsBucketInv.toPre (hv.overmars_valid b hb)))
  obtain ⟨hom_mc, hom_vp, hom_step⟩ :=
    overmarsStepGenProg_fastStep (fs := fs_ov) henv hbnds_ov hwv_step.2.1 hwv_step.2.2.1 (s := s1)
  dsimp only
  unfold fastInsertOverwriteGenProg; dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
  have hs'_eq : (Memory.spec 0).clientState s
      (fastInsertWriteOvGenProg (((cp, base), (b, loc)), v_val) >>= fun _ =>
        overmarsStepGenProg ((mkWhpParams c U V w n_max, base), b) >>= fun _ => pure 1) =
      (Memory.spec 0).clientState s1
        (overmarsStepGenProg ((mkWhpParams c U V w n_max, base), b)) := by
    rw [clientState_bind, clientState_bind, clientState_pure_whp]
  rw [hs'_eq]
  refine ⟨?_, ?_, ?_, hwv_step.trans hom_step⟩
  · rw [clientResult_bind, clientResult_bind, clientResult_pure_whp]
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_pure]
    dsimp only [s1, cp] at hwv_mc hom_mc ⊢; omega
  · exact validProg_bind hwv_vp (validProg_bind hom_vp (validProg_pure _))

/-- Guard 1 (`insCheckCapPoolGenProg`): check `totalLocalCoordsWhp ≤ X ∨ (cf ≤ X ∧ poolFreeTop = 0)`
without mutating memory, returning `(0, 0)` if rejected or `(1, X)` if accepted. -/
@[irreducible] private def insCheckCapPoolGenProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cp, base), b) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let X ← readBktFieldGenProg (((cp, base), b), z0)
    let top ← readHdrProg (base, hdrPoolFreeTop)
    let tl ← pure (wpTotalLoc cp)
    let cf ← pure (wpCapFront cp)
    if tl ≤ X ∨ (cf ≤ X ∧ top = z0) then
      pure (z0, z0)
    else
      pure (z1, X)

private theorem realizes_insCheckCapPoolGen :
    Realizes .exact insCheckCapPoolGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((cp, base), b) _ => WhpLargeEnvGen w cp base ∧ b < wpM cp)
      (fun _ _ => 0) := by
  unfold insCheckCapPoolGenProg
  have hrb := realizes_readBktFieldGen
  have hrh := realizes_readHdr
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    rw [wp_large_M hth] at hb
    try simp only [wp_large_M hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
  )

private theorem insCheckCapPoolGenProg_spec {c U V w n_max base b : ℕ}
    {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := insCheckCapPoolGenProg ((mkWhpCoreParams c U V w n_max, base), b)
    let X := fs.bktCount b
    let cf := capFrontWhp n_max
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (if totalLocalCoordsWhp n_max ≤ X ∨ (cf ≤ X ∧ fs.poolFreeTop = 0) then (0, 0) else (1, X)) ∧
    memoryCost prog s ≤ 3 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  obtain ⟨hc0_st, hc0_res, hc0_mc, hc0_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 0 < 10) hrep (s := s)
  simp only [getBktField] at hc0_res
  obtain ⟨ht_st, ht_res, ht_mc, ht_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrPoolFreeTop)
    (by dsimp [hdrPoolFreeTop]; omega) (s := s)
  rw [hrep.2.2.1] at ht_res
  dsimp only
  unfold insCheckCapPoolGenProg; dsimp only
  simp only [wp_large_totalLoc hth, wp_large_capFront hth, pure_bind]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, hc0_st, hc0_res, clientState_bind, ht_st, ht_res]
    split_ifs <;> rfl
  · rw [clientResult_bind, hc0_st, hc0_res, clientResult_bind, ht_st, ht_res]
    split_ifs <;> rfl
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hc0_st, hc0_res, hc0_mc, ht_st, ht_res, ht_mc]
    split_ifs <;> (simp only [memoryCost_pure]; omega)
  · refine validProg_bind hc0_vp ?_; rw [hc0_st, hc0_res]
    refine validProg_bind ht_vp ?_; rw [ht_st, ht_res]
    split_ifs <;> exact validProg_pure _

/-- Return `1` iff `(bufLookup (fs.buf ep) rKey).isSome`, else `0` (`d = (((cp, base), ep), rKey)`).
-/
@[irreducible] private def insBufIsSomeGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | d => do
    let lk ← bufLookupGenProg d
    pure lk.1

private theorem realizes_insBufIsSomeGen :
    Realizes .exact insBufIsSomeGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      BufReadGenPre
      (fun _ _ => 0) := by
  unfold insBufIsSomeGenProg
  have hbl := realizes_bufLookupGen
  realize
  exact h

private theorem insBufIsSomeGenProg_spec {c U V w n_max base ep rKey : ℕ}
    {fs : FastState} {mapFn : ℕ → Option (ℕ × ℕ)} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf ep) mapFn) :
    let prog := insBufIsSomeGenProg (((mkWhpCoreParams c U V w n_max, base), ep), rKey)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (if (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf ep) rKey).isSome then 1 else 0) ∧
    memoryCost prog s ≤ 2 * cTabWhp c + 8 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  obtain ⟨hl_st, hl_res, hl_mc, hl_vp⟩ :=
    bufLookupGenProg_spec henv hep (hrep.buf_rep hep) hv (rKey := rKey) (s := s)
  dsimp only
  unfold insBufIsSomeGenProg
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, hl_st]; rfl
  · rw [clientResult_bind, hl_st, hl_res, clientResult_pure_whp]
    rcases bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf ep) rKey with _ | ⟨_, _⟩ <;> rfl
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hl_st, memoryCost_pure]; omega
  · refine validProg_bind hl_vp ?_; rw [hl_st]; exact validProg_pure _

/-- Return `1` iff `fs.rebStage ≤ 3 ∧ (bufLookup (fs.buf fs.oldEp) rKey).isSome`
(`d = ((cp, base), rKey)`). -/
@[irreducible] private def insOldBufSomeGenProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, base), rKey) => do
    let z0 ← pure 0
    let z3 ← pure 3
    let stg ← readHdrProg (base, hdrRebStage)
    let oldEp ← readOldEpProg base
    if stg ≤ z3 then
      insBufIsSomeGenProg (((cp, base), oldEp), rKey)
    else
      pure z0

private theorem realizes_insOldBufSomeGen :
    Realizes .exact insOldBufSomeGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cp, base), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          (fs.rebStage ≤ 3 →
            ∃ oldMap, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) oldMap))
      (fun _ _ => 0) := by
  unfold insOldBufSomeGenProg
  have hrh := realizes_readHdr
  have hro := realizes_readOldEp
  have hib := realizes_insBufIsSomeGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, rKey⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hce, hbo_fn⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have h2w := henv.two_le_w
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1 := by
      rcases hce with hc | hc <;> simp [FastState.oldEp, hc]
    obtain ⟨hst_st, hst_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebStage)
      (by dsimp [hdrRebStage]; omega) (s := s)
    rw [hrep.2.2.2.2.2.1] at hst_res
    obtain ⟨hro_st, hro_res, _, _⟩ := readOldEpProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce
      hrep.2.2.2.1 (s := s)
    simp only [hst_st, hst_res, hro_st, hro_res] at *
    first
    | exact h2w
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | (obtain ⟨oldMap, hv_old⟩ := hbo_fn (by omega)
       exact ⟨c, U, V, w, n_max, fs.buf fs.oldEp, oldMap, henv, rfl, hold_or,
         hrep.buf_rep hold_or, hv_old⟩)
  )

private theorem insOldBufSomeGenProg_spec {c U V w n_max base rKey : ℕ}
    {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1)
    (hbo_fn : fs.rebStage ≤ 3 →
      ∃ oldMap, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) oldMap)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := insOldBufSomeGenProg ((mkWhpCoreParams c U V w n_max, base), rKey)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (if fs.rebStage ≤ 3 ∧
          (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey).isSome
       then 1 else 0) ∧
    memoryCost prog s ≤ 2 * cTabWhp c + 10 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1 := by
    rcases hce with hc | hc <;> simp [FastState.oldEp, hc]
  obtain ⟨hst_st, hst_res, hst_mc, hst_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebStage)
    (by dsimp [hdrRebStage]; omega) (s := s)
  rw [hrep.2.2.2.2.2.1] at hst_res
  obtain ⟨hro_st, hro_res, hro_mc, hro_vp⟩ := readOldEpProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce
    hrep.2.2.2.1 (s := s)
  dsimp only
  unfold insOldBufSomeGenProg; dsimp only; simp only [pure_bind]
  by_cases hle3 : fs.rebStage ≤ 3
  · obtain ⟨oldMap, hv_old⟩ := hbo_fn hle3
    obtain ⟨hib_st, hib_res, hib_mc, hib_vp⟩ :=
      insBufIsSomeGenProg_spec henv hold_or hrep hv_old (rKey := rKey) (s := s)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hst_st, hst_res, clientState_bind, hro_st, hro_res,
        ite_eq_left hle3, hib_st]
    · rw [clientResult_bind, hst_st, hst_res, clientResult_bind, hro_st, hro_res,
        ite_eq_left hle3, hib_res]
      by_cases hs : (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey).isSome = true
      · simp [hle3, hs]
      · simp [hle3, hs]
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hst_st, hst_res, hst_mc, hro_st, hro_res, hro_mc, ite_eq_left hle3]; omega
    · refine validProg_bind hst_vp ?_; rw [hst_st, hst_res]
      refine validProg_bind hro_vp ?_; rw [hro_st, hro_res, ite_eq_left hle3]
      exact hib_vp
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hst_st, hst_res, clientState_bind, hro_st, hro_res,
        ite_eq_right hle3]; rfl
    · rw [clientResult_bind, hst_st, hst_res, clientResult_bind, hro_st, hro_res,
        ite_eq_right hle3, clientResult_pure_whp]; simp [hle3]
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hst_st, hst_res, hst_mc, hro_st, hro_res, hro_mc, ite_eq_right hle3,
        memoryCost_pure]; omega
    · refine validProg_bind hst_vp ?_; rw [hst_st, hst_res]
      refine validProg_bind hro_vp ?_; rw [hro_st, hro_res, ite_eq_right hle3]
      exact validProg_pure _

/-- Guard 2 (`insCheckRKeyGuardsGenProg`): return `0` if `rKey` collides in `buf curEp` or active
`buf oldEp`, else `1` (`d = ((cp, base), rKey)`). -/
@[irreducible] private def insCheckRKeyGuardsGenProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, base), rKey) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let curEp ← readHdrProg (base, hdrCurEp)
    let cHit ← insBufIsSomeGenProg (((cp, base), curEp), rKey)
    let oHit ← insOldBufSomeGenProg ((cp, base), rKey)
    if cHit = z1 ∨ oHit = z1 then
      pure z0
    else
      pure z1

private theorem realizes_insCheckRKeyGuardsGen :
    Realizes .exact insCheckRKeyGuardsGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cp, base), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState) (curMap : ℕ → Option (ℕ × ℕ)),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) curMap ∧
          (fs.rebStage ≤ 3 →
            ∃ oldMap, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) oldMap))
      (fun _ _ => 0) := by
  unfold insCheckRKeyGuardsGenProg
  have hrh := realizes_readHdr
  have hib := realizes_insBufIsSomeGen
  have hob := realizes_insOldBufSomeGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, rKey⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, curMap, henv, rfl, hrep, hce, hv_cur, hbo_fn⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    obtain ⟨hce_st, hce_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrCurEp)
      (by dsimp [hdrCurEp]; omega) (s := s)
    rw [hrep.2.2.2.1] at hce_res
    obtain ⟨hc_st, _, _, _⟩ :=
      insBufIsSomeGenProg_spec henv hce hrep hv_cur (rKey := rKey) (s := s)
    obtain ⟨ho_st, _, _, _⟩ :=
      insOldBufSomeGenProg_spec henv hce hbo_fn hrep (rKey := rKey) (s := s)
    simp only [hce_st, hce_res, hc_st, ho_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact ⟨c, U, V, w, n_max, fs.buf fs.curEp, curMap, henv, rfl, hce, hrep.buf_rep hce, hv_cur⟩
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hce, hbo_fn⟩
  )

private theorem insCheckRKeyGuardsGenProg_spec {c U V w n_max base rKey : ℕ}
    {fs : FastState} {curMap : ℕ → Option (ℕ × ℕ)} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1)
    (hv_cur : ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) curMap)
    (hbo_fn : fs.rebStage ≤ 3 →
      ∃ oldMap, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) oldMap)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := insCheckRKeyGuardsGenProg ((mkWhpCoreParams c U V w n_max, base), rKey)
    let bad : Prop :=
      (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey).isSome ∨
        (fs.rebStage ≤ 3 ∧
          (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey).isSome)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (if bad then 0 else 1) ∧
    memoryCost prog s ≤ 4 * cTabWhp c + 19 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  obtain ⟨hce_st, hce_res, hce_mc, hce_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrCurEp)
    (by dsimp [hdrCurEp]; omega) (s := s)
  rw [hrep.2.2.2.1] at hce_res
  obtain ⟨hc_st, hc_res, hc_mc, hc_vp⟩ :=
    insBufIsSomeGenProg_spec henv hce hrep hv_cur (rKey := rKey) (s := s)
  obtain ⟨ho_st, ho_res, ho_mc, ho_vp⟩ :=
    insOldBufSomeGenProg_spec henv hce hbo_fn hrep (rKey := rKey) (s := s)
  dsimp only
  unfold insCheckRKeyGuardsGenProg; dsimp only; simp only [pure_bind]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, hce_st, hce_res, clientState_bind, hc_st, hc_res,
      clientState_bind, ho_st, ho_res]
    split_ifs <;> rfl
  · rw [clientResult_bind, hce_st, hce_res, clientResult_bind, hc_st, hc_res,
      clientResult_bind, ho_st, ho_res]
    by_cases h1 : (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey).isSome = true <;>
      by_cases h2 : fs.rebStage ≤ 3 ∧
          (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey).isSome = true <;>
      simp [h1, h2]
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hce_st, hce_res, hce_mc, hc_st, hc_res, ho_st, ho_res]
    split_ifs <;> (simp only [memoryCost_pure]; omega)
  · refine validProg_bind hce_vp ?_; rw [hce_st, hce_res]
    refine validProg_bind hc_vp ?_; rw [hc_st, hc_res]
    refine validProg_bind ho_vp ?_; rw [ho_st, ho_res]
    split_ifs <;> exact validProg_pure _

/-- Read `(fpOfSaltOpt (bktSalt b) u_val, liveSliceIdx b)` without mutating memory. -/
@[irreducible] private def insEvalLiveFpGenProg :
    (WhpParams × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | ((wp, base), (b, u_val)) => do
    let si ← readLiveSaltIdxGenProg ((wp.1, base), b)
    let hrt ← mkHashRtGenProg (wp, base)
    let fp ← fpOfSaltOptRtProg ((hrt, si.1), u_val)
    pure (fp, si.2)

private theorem realizes_insEvalLiveFpGen :
    Realizes .exact insEvalLiveFpGenProg
      (WordEncoding.encode (α := (WhpParams × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((wp, base), (b, _)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.liveRole b < 3)
      (fun _ _ => 0) := by
  unfold insEvalLiveFpGenProg
  have hrs := realizes_readLiveSaltIdxGen
  have hmh := realizes_mkHashRtGen
  have hfp := realizes_fpOfSaltOptRt
  realize
  all_goals (
    rcases d with ⟨⟨wp, base⟩, ⟨b, u_val⟩⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, heq_wp, hseed, hrep, hb, hlr⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hrs_st, hrs_res, _, _⟩ := readLiveSaltIdxGenProg_spec henv hb hrep (s := s)
    obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    obtain ⟨hfp_st, _, _, _⟩ :=
      fpOfSaltOptRtProg_spec (salt := fs.bktSalt b) (kv := u_val) henv hseed (s := s)
    simp only [hcp_eq] at *
    simp only [hrs_st, hrs_res, hmh_st, hmh_res, hfp_st] at *
    first
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hlr⟩
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
  )

/-- Read `(hasFpCollision, (fp, liveSliceIdx b))` for key `u` without mutating memory. -/
@[irreducible] private def insReadFpLiveGenProg :
    (WhpParams × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((wp, base), (b, u_val)) => do
    let fl ← insEvalLiveFpGenProg ((wp, base), (b, u_val))
    let lk ← btreeLookupGenProg (((wp.1, base), fl.2), fl.1)
    pure (lk.1, fl)

private theorem realizes_insReadFpLiveGen :
    Realizes .exact insReadFpLiveGenProg
      (WordEncoding.encode (α := (WhpParams × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ((wp, base), (b, _)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (lm : ℕ → Option ℕ),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.liveRole b < 3 ∧
          fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
          ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) lm)
      (fun _ _ => 0) := by
  unfold insReadFpLiveGenProg
  have hev := realizes_insEvalLiveFpGen
  have hbt := realizes_btreeLookupGen
  realize
  all_goals (
    rcases d with ⟨⟨wp, base⟩, ⟨b, u_val⟩⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, lm, henv, heq_wp, hseed, hrep, hb, hlr, hins, hv_sl⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hrs_st, hrs_res, _, _⟩ := readLiveSaltIdxGenProg_spec henv hb hrep (s := s)
    obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    obtain ⟨hfp_st, hfp_res, _, _⟩ :=
      fpOfSaltOptRtProg_spec (salt := fs.bktSalt b) (kv := u_val) henv hseed (s := s)
    have hev_st : (Memory.spec 0).clientState s
        (insEvalLiveFpGenProg ((mkWhpParams c U V w n_max, base), (b, u_val))) = s := by
      unfold insEvalLiveFpGenProg; dsimp only; rw [hcp_eq]
      rw [clientState_bind, hrs_st, hrs_res, clientState_bind, hmh_st, hmh_res,
        clientState_bind, hfp_st]; rfl
    have hev_res : (Memory.spec 0).clientResult s
        (insEvalLiveFpGenProg ((mkWhpParams c U V w n_max, base), (b, u_val))) =
        (if hs : fs.bktSalt b < sMaxWhp c n_max then
          if hu : u_val < U then fpHash c U n_max θ.2 ⟨fs.bktSalt b, hs⟩ ⟨u_val, hu⟩ else 0
         else 0, fs.liveSliceIdx b) := by
      unfold insEvalLiveFpGenProg; dsimp only; rw [hcp_eq]
      rw [clientResult_bind, hrs_st, hrs_res, clientResult_bind, hmh_st, hmh_res,
        clientResult_bind, hfp_st, hfp_res]; rfl
    have hlIdx : fs.liveSliceIdx b < 3 * numBucketsWhp n_max := by
      unfold FastState.liveSliceIdx; omega
    have hfp_lt := fpOfSaltOpt_lt c U n_max (fs.bktSalt b) u_val θ.2
    obtain ⟨hbt_st, _, _, _⟩ :=
      btreeLookupGenProg_spec henv hlIdx hins (hrep.slice_rep hlIdx) hv_sl hfp_lt (s := s)
    simp only [hcp_eq] at *
    simp only [hev_st, hev_res, hbt_st] at *
    first
    | exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, hb, hlr⟩
    | exact ⟨c, U, V, w, n_max, fs.liveInsCount b, fs.slices (fs.liveSliceIdx b), lm,
        henv, rfl, hlIdx, hins, hrep.slice_rep hlIdx, hv_sl, hfp_lt⟩
  )

private theorem insReadFpLiveGenProg_spec {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {lm : ℕ → Option ℕ} {s : Memory.State} (u : Fin U)
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hb : b < numBucketsWhp n_max) (hlr : fs.liveRole b < 3)
    (hins : fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12)
    (hv_sl : ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) lm) :
    let prog := insReadFpLiveGenProg ((mkWhpParams c U V w n_max, base), (b, u.val))
    let fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
    let lIdx := fs.liveSliceIdx b
    let hasCol := (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      (fs.slices lIdx) fp).isSome
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (if hasCol then 1 else 0, (fp, lIdx)) ∧
    memoryCost prog s ≤ hashEvalCostWhp c + 266 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hrs_st, hrs_res, hrs_mc, hrs_vp⟩ := readLiveSaltIdxGenProg_spec henv hb hrep (s := s)
  obtain ⟨hmh_st, hmh_res, hmh_mc, hmh_vp⟩ :=
    mkHashRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base) hth s
  obtain ⟨hfp_st, hfp_res, hfp_mc, hfp_vp⟩ :=
    fpOfSaltOptRtProg_spec (salt := fs.bktSalt b) (kv := u.val) henv hseed (s := s)
  set fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
  have hfp_eq : (if hs : fs.bktSalt b < sMaxWhp c n_max then
      if hu : u.val < U then fpHash c U n_max θ.2 ⟨fs.bktSalt b, hs⟩ ⟨u.val, hu⟩ else 0
     else 0) = fp := by
    dsimp only [fp, fpOfSalt]
    split_ifs with hs hu <;> first | rfl | exact absurd u.isLt hu
  rw [hfp_eq] at hfp_res
  have hfp_lt : fp < 2 ^ fpBitsWhp n_max := by
    rw [← hfp_eq]; exact fpOfSaltOpt_lt c U n_max _ _ θ.2
  have hlIdx : fs.liveSliceIdx b < 3 * numBucketsWhp n_max := by
    unfold FastState.liveSliceIdx; omega
  obtain ⟨hbt_st, hbt_res, hbt_mc, hbt_vp⟩ :=
    btreeLookupGenProg_spec henv hlIdx hins (hrep.slice_rep hlIdx) hv_sl hfp_lt (s := s)
  rw [← hv_sl.lookup_eq hth hins hfp_lt] at hbt_res
  have hev_st : (Memory.spec 0).clientState s
      (insEvalLiveFpGenProg ((mkWhpParams c U V w n_max, base), (b, u.val))) = s := by
    unfold insEvalLiveFpGenProg; dsimp only; rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
    rw [clientState_bind, hrs_st, hrs_res, clientState_bind, hmh_st, hmh_res,
      clientState_bind, hfp_st]; rfl
  have hev_res : (Memory.spec 0).clientResult s
      (insEvalLiveFpGenProg ((mkWhpParams c U V w n_max, base), (b, u.val))) =
      (fp, fs.liveSliceIdx b) := by
    unfold insEvalLiveFpGenProg; dsimp only; rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
    rw [clientResult_bind, hrs_st, hrs_res, clientResult_bind, hmh_st, hmh_res,
      clientResult_bind, hfp_st, hfp_res]; rfl
  have hev_mc : memoryCost
      (insEvalLiveFpGenProg ((mkWhpParams c U V w n_max, base), (b, u.val))) s ≤
      hashEvalCostWhp c + 4 := by
    unfold insEvalLiveFpGenProg; dsimp only; rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
    simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hrs_st, hrs_res, hrs_mc, hmh_st, hmh_res, hmh_mc, hfp_st, hfp_res, memoryCost_pure]
    have hfp_mc' : memoryCost (fpOfSaltOptRtProg ((mkHashRt c U w n_max base, fs.bktSalt b),
        u.val)) s ≤ hashEvalCostWhp c := hfp_mc
    dsimp only; omega
  have hev_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
      (insEvalLiveFpGenProg ((mkWhpParams c U V w n_max, base), (b, u.val))) := by
    unfold insEvalLiveFpGenProg; dsimp only; rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
    refine validProg_bind hrs_vp ?_; rw [hrs_st, hrs_res]
    refine validProg_bind hmh_vp ?_; rw [hmh_st, hmh_res]
    refine validProg_bind hfp_vp ?_; rw [hfp_st, hfp_res]
    exact validProg_pure _
  dsimp only
  unfold insReadFpLiveGenProg; dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, hev_st, hev_res, clientState_bind, hbt_st]; rfl
  · rw [clientResult_bind, hev_st, hev_res, clientResult_bind, hbt_st, hbt_res,
      clientResult_pure_whp]
    cases btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      (fs.slices (fs.liveSliceIdx b)) fp <;> rfl
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hev_st, hev_res, hbt_st, memoryCost_pure]
    dsimp only [cp, fp] at hbt_mc ⊢; omega
  · refine validProg_bind hev_vp ?_; rw [hev_st, hev_res]
    refine validProg_bind hbt_vp ?_; rw [hbt_st]; exact validProg_pure _

/-- Read `(fs.buf fs.curEp).itemAlloc` from headers `hdrBuf0ItemAlloc` / `hdrBuf1ItemAlloc`. -/
@[irreducible] private def insReadCurBufItemAllocProg (base : ℕ) : Memory.Prog ℕ := do
  let z0 ← pure 0
  let curEp ← readHdrProg (base, hdrCurEp)
  if curEp = z0 then
    readHdrProg (base, hdrBuf0ItemAlloc)
  else
    readHdrProg (base, hdrBuf1ItemAlloc)

private theorem realizes_insReadCurBufItemAlloc :
    Realizes .exact insReadCurBufItemAllocProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w base _ => 2 ≤ w ∧ Fits w (base + 32))
      (fun _ _ => 0) := by
  unfold insReadCurBufItemAllocProg
  have hrh := realizes_readHdr
  realize
  all_goals (
    obtain ⟨_, hfit32⟩ := h
    exact hfit32.of_le (by dsimp [hdrCurEp, hdrBuf0ItemAlloc, hdrBuf1ItemAlloc]; omega)
  )

private theorem insReadCurBufItemAllocProg_spec {c U V w n_max base : ℕ}
    {fs : FastState} {s : Memory.State}
    (_henv : WhpLargeEnv c U V w n_max w base)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := insReadCurBufItemAllocProg base
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (fs.buf fs.curEp).itemAlloc ∧
    memoryCost prog s ≤ 2 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  obtain ⟨hce_st, hce_res, hce_mc, hce_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrCurEp)
    (by dsimp [hdrCurEp]; omega) (s := s)
  rw [hrep.2.2.2.1] at hce_res
  obtain ⟨hi0_st, hi0_res, hi0_mc, hi0_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrBuf0ItemAlloc)
    (by dsimp [hdrBuf0ItemAlloc]; omega) (s := s)
  obtain ⟨hi1_st, hi1_res, hi1_mc, hi1_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrBuf1ItemAlloc)
    (by dsimp [hdrBuf1ItemAlloc]; omega) (s := s)
  have hia0 : s.mem (base + hdrBuf0ItemAlloc) = (fs.buf 0).itemAlloc :=
    (hrep.buf_rep (Or.inl rfl)).2.2.2.1
  have hia1 : s.mem (base + hdrBuf1ItemAlloc) = (fs.buf 1).itemAlloc :=
    (hrep.buf_rep (Or.inr rfl)).2.2.2.1
  rw [hia0] at hi0_res
  rw [hia1] at hi1_res
  dsimp only
  unfold insReadCurBufItemAllocProg; simp only [pure_bind]
  rcases hce with hc0 | hc1
  · rw [hc0] at hce_res ⊢
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hce_st, hce_res, ite_eq_left rfl, hi0_st]
    · rw [clientResult_bind, hce_st, hce_res, ite_eq_left rfl, hi0_res]
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hce_st, hce_res, hce_mc, ite_eq_left rfl, hi0_mc]
    · refine validProg_bind hce_vp ?_; rw [hce_st, hce_res, ite_eq_left rfl]; exact hi0_vp
  · rw [hc1] at hce_res ⊢
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hce_st, hce_res, ite_eq_right (by decide : ¬(1 = 0)), hi1_st]
    · rw [clientResult_bind, hce_st, hce_res, ite_eq_right (by decide : ¬(1 = 0)), hi1_res]
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hce_st, hce_res, hce_mc, ite_eq_right (by decide : ¬(1 = 0)), hi1_mc]
    · refine validProg_bind hce_vp ?_; rw [hce_st, hce_res, ite_eq_right (by decide : ¬(1 = 0))]
      exact hi1_vp

/-- Guard 3 active helper (`hasFpCollision = true`): return `0` iff
`!bufEverPresent (buf curEp) rKey ∧ 2 * sMaxWhp ≤ (buf curEp).itemAlloc`, else `1`. -/
@[irreducible] private def insCheckFpCapActiveGenProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, base), rKey) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let curEp ← readHdrProg (base, hdrCurEp)
    let ev ← bufEverPresentGenProg (((cp, base), curEp), rKey)
    let ia ← insReadCurBufItemAllocProg base
    let cap ← pure (wpBufItemCap cp)
    if ev = z0 ∧ cap ≤ ia then
      pure z0
    else
      pure z1

private theorem realizes_insCheckFpCapActiveGen :
    Realizes .exact insCheckFpCapActiveGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cp, base), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState) (curMap : ℕ → Option (ℕ × ℕ)),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) curMap)
      (fun _ _ => 0) := by
  unfold insCheckFpCapActiveGenProg
  have hrh := realizes_readHdr
  have hev := realizes_bufEverPresentGen
  have hia := realizes_insReadCurBufItemAlloc
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, rKey⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, curMap, henv, rfl, hrep, hce, hv_cur⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have h2w := henv.two_le_w
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    obtain ⟨hce_st, hce_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrCurEp)
      (by dsimp [hdrCurEp]; omega) (s := s)
    rw [hrep.2.2.2.1] at hce_res
    obtain ⟨hev_st, _, _, _⟩ :=
      bufEverPresentGenProg_spec henv hce (hrep.buf_rep hce) hv_cur (rKey := rKey) (s := s)
    obtain ⟨hia_st, _, _, _⟩ := insReadCurBufItemAllocProg_spec henv hce hrep (s := s)
    simp only [hce_st, hce_res, hev_st, hia_st] at *
    first
    | exact h2w
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact henv.fits_largeSpace.of_le (by omega)
    | exact ⟨c, U, V, w, n_max, fs.buf fs.curEp, curMap, henv, rfl, hce, hrep.buf_rep hce, hv_cur⟩
  )

/-- Guard 3 wrapper (`d = (((cp, base), hasCol), rKey)`). -/
@[irreducible] private def insCheckFpCapOptGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((cp, base), hasCol), rKey) => do
    let z1 ← pure 1
    if hasCol = z1 then
      insCheckFpCapActiveGenProg ((cp, base), rKey)
    else
      pure z1

private theorem realizes_insCheckFpCapOptGen :
    Realizes .exact insCheckFpCapOptGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (((cp, base), _), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState) (curMap : ℕ → Option (ℕ × ℕ)),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) curMap)
      (fun _ _ => 0) := by
  unfold insCheckFpCapOptGenProg
  have hca := realizes_insCheckFpCapActiveGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, hasCol⟩, rKey⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, curMap, henv, rfl, hrep, hce, hv_cur⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, fs, curMap, henv, rfl, hrep, hce, hv_cur⟩
  )

private theorem insCheckFpCapOptGenProg_spec {c U V w n_max base rKey : ℕ}
    {fs : FastState} {curMap : ℕ → Option (ℕ × ℕ)} {s : Memory.State} (hasFpCollision : Bool)
    (henv : WhpLargeEnv c U V w n_max w base)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1)
    (hv_cur : ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) curMap)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let hasCol := if hasFpCollision then 1 else 0
    let prog := insCheckFpCapOptGenProg (((mkWhpCoreParams c U V w n_max, base), hasCol), rKey)
    let bad3 : Prop :=
      hasFpCollision ∧
        !bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey ∧
        2 * sMaxWhp c n_max ≤ (fs.buf fs.curEp).itemAlloc
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (if bad3 then 0 else 1) ∧
    memoryCost prog s ≤ 2 * cTabWhp c + 5 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  dsimp only
  unfold insCheckFpCapOptGenProg; dsimp only; simp only [pure_bind]
  cases hasFpCollision with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, zero_ne_one, false_and, memoryCost_pure]
    exact ⟨rfl, rfl, Nat.zero_le _, validProg_pure _⟩
  | true =>
    simp only [↓reduceIte, true_and]
    obtain ⟨hce_st, hce_res, hce_mc, hce_vp⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrCurEp)
      (by dsimp [hdrCurEp]; omega) (s := s)
    rw [hrep.2.2.2.1] at hce_res
    obtain ⟨hev_st, hev_res, hev_mc, hev_vp⟩ :=
      bufEverPresentGenProg_spec henv hce (hrep.buf_rep hce) hv_cur (rKey := rKey) (s := s)
    obtain ⟨hia_st, hia_res, hia_mc, hia_vp⟩ :=
      insReadCurBufItemAllocProg_spec henv hce hrep (s := s)
    unfold insCheckFpCapActiveGenProg; dsimp only
    simp only [wp_large_bufItemCap hth, pure_bind]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hce_st, hce_res, clientState_bind, hev_st, hev_res,
        clientState_bind, hia_st, hia_res]
      split_ifs <;> rfl
    · rw [clientResult_bind, hce_st, hce_res, clientResult_bind, hev_st, hev_res,
        clientResult_bind, hia_st, hia_res]
      cases bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey <;>
        by_cases hle : 2 * sMaxWhp c n_max ≤ (fs.buf fs.curEp).itemAlloc <;>
        simp [hle]
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hce_st, hce_res, hce_mc, hev_st, hev_res, hia_st, hia_res]
      split_ifs <;> (simp only [memoryCost_pure]; omega)
    · refine validProg_bind hce_vp ?_; rw [hce_st, hce_res]
      refine validProg_bind hev_vp ?_; rw [hev_st, hev_res]
      refine validProg_bind hia_vp ?_; rw [hia_st, hia_res]
      split_ifs <;> exact validProg_pure _

/-- Pop one free slot from `poolFreeStack[poolFreeTop - 1]` and decrement `poolFreeTop`. -/
@[irreducible] private def insPopFreeSlotGenProg :
    WhpCoreParams × ℕ → Memory.Prog ℕ
  | (cp, base) => do
    let z1 ← pure 1
    let top ← readHdrProg (base, hdrPoolFreeTop)
    let top' ← pure (top - z1)
    let pSlot ← readPoolFreeStackGenProg ((cp, base), top')
    writeHdrProg ((base, hdrPoolFreeTop), top')
    pure pSlot

private theorem realizes_insPopFreeSlotGen :
    Realizes .exact insPopFreeSlotGenProg
      (WordEncoding.encode (α := WhpCoreParams × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (cp, base) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          0 < fs.poolFreeTop ∧
          fs.poolFreeTop ≤ poolSizeWhp n_max)
      (fun _ _ => 0) := by
  unfold insPopFreeSlotGenProg
  have hrh := realizes_readHdr
  have hrs := realizes_readPoolFreeStackGen
  have hwh := realizes_writeHdr
  realize
  all_goals (
    rcases d with ⟨cp, base⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hpos, hle_ps⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hps_le := (large_index_bounds hth).2.2.2.1
    obtain ⟨ht_st, ht_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrPoolFreeTop)
      (by dsimp [hdrPoolFreeTop]; omega) (s := s)
    rw [hrep.2.2.1] at ht_res
    obtain ⟨hp_st, _, _, _⟩ :=
      readPoolFreeStackGenProg_spec henv (by omega : fs.poolFreeTop - 1 < poolSizeWhp n_max)
        hrep (s := s)
    simp only [ht_st, ht_res, hp_st, wp_large_poolSize hth] at *
    first
    | omega
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
  )

/-- Bind backyard slot `pSlot` to `(b, k)` in `backPtr` and `poolOwner`. -/
@[irreducible] private def insBindBackSlotGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | ((((cp, base), b), k), pSlot) => do
    writeBackPtrGenProg ((((cp, base), b), k), pSlot)
    let enc ← pure (b * wpCapBack cp + k)
    writePoolOwnerGenProg (((cp, base), pSlot), enc)

private theorem realizes_insBindBackSlotGen :
    Realizes .exact insBindBackSlotGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), k), pSlot) _ =>
        WhpLargeEnvGen w cp base ∧ b < wpM cp ∧ k < wpCapBack cp ∧ pSlot < wpPoolSize cp)
      (fun _ _ => 0) := by
  unfold insBindBackSlotGenProg
  have hwb := realizes_writeBackPtrGen
  have hwo := realizes_writePoolOwnerGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, k⟩, pSlot⟩
    dsimp only at *
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb, hk, hpSlot⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hmcb := (large_index_bounds hth).1
    simp only [wp_large_M hth, wp_large_capBack hth, wp_large_poolSize hth] at hb hk hpSlot ⊢
    have hidx := mul_add_lt_mul_bound hb hk
    first
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact hk
    | exact hpSlot
  )

/-- Backyard allocation sequence for `fastInsertAllocGenProg` when `capFrontWhp ≤ X`. -/
@[irreducible] private def insAllocBackyardProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, base), b), X) => do
    let k ← pure (X - wpCapFront cp)
    let pSlot ← insPopFreeSlotGenProg (cp, base)
    insBindBackSlotGenProg ((((cp, base), b), k), pSlot)

private theorem realizes_insAllocBackyard :
    Realizes .exact insAllocBackyardProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), b), X) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          capFrontWhp n_max ≤ X ∧
          X < totalLocalCoordsWhp n_max ∧
          0 < fs.poolFreeTop ∧
          fs.poolFreeTop ≤ poolSizeWhp n_max ∧
          fs.poolFreeStack (fs.poolFreeTop - 1) < poolSizeWhp n_max)
      (fun _ _ => 0) := by
  unfold insAllocBackyardProg
  have hpop := realizes_insPopFreeSlotGen
  have hbnd := realizes_insBindBackSlotGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, b⟩, X⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hb, hcf, hX_tl, hpos, hle_ps, hp_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have h2tl := (large_index_bounds hth).2.2.1
    have hk : X - capFrontWhp n_max < capBackWhp n_max := by
      unfold totalLocalCoordsWhp at hX_tl; omega
    obtain ⟨ht_st, ht_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrPoolFreeTop)
      (by dsimp [hdrPoolFreeTop]; omega) (s := s)
    rw [hrep.2.2.1] at ht_res
    obtain ⟨hp_st, hp_res, _, _⟩ :=
      readPoolFreeStackGenProg_spec henv (by omega : fs.poolFreeTop - 1 < poolSizeWhp n_max)
        hrep (s := s)
    have hpop_res : (Memory.spec 0).clientResult s
        (insPopFreeSlotGenProg (mkWhpCoreParams c U V w n_max, base)) =
        fs.poolFreeStack (fs.poolFreeTop - 1) := by
      unfold insPopFreeSlotGenProg; dsimp only; simp only [pure_bind]
      rw [clientResult_bind, ht_st, ht_res, clientResult_bind, hp_st, hp_res,
        clientResult_bind, clientResult_pure_whp]
    simp only [hpop_res, wp_large_M hth, wp_large_capFront hth, wp_large_capBack hth,
      wp_large_poolSize hth] at *
    first
    | omega
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hpos, hle_ps⟩
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
  )

/-- Allocate backyard slot at `(b, X)` when `capFrontWhp ≤ X` (`d = (((cp, base), b), X)`). -/
@[irreducible] private def fastInsertAllocGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, base), b), X) => do
    let cf ← pure (wpCapFront cp)
    if cf ≤ X then
      insAllocBackyardProg (((cp, base), b), X)
    else
      pure ()

private theorem realizes_fastInsertAllocGen :
    Realizes .exact fastInsertAllocGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), b), X) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          X < totalLocalCoordsWhp n_max ∧
          (capFrontWhp n_max ≤ X →
            0 < fs.poolFreeTop ∧
            fs.poolFreeTop ≤ poolSizeWhp n_max ∧
            fs.poolFreeStack (fs.poolFreeTop - 1) < poolSizeWhp n_max))
      (fun _ _ => 0) := by
  unfold fastInsertAllocGenProg
  have hab := realizes_insAllocBackyard
  realize
  rcases d with ⟨⟨⟨cp, base⟩, b⟩, X⟩
  obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hb, hX_tl, hcf_fn⟩ := h
  have hw_eq := henv.2.2.1; subst hw_eq
  have hth := henv.2.2.2.1
  simp only [wp_large_capFront hth] at *
  have hcf : capFrontWhp n_max ≤ X := by omega
  obtain ⟨hpos, hle_ps, hp_lt⟩ := hcf_fn hcf
  exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hcf, hX_tl, hpos, hle_ps, hp_lt⟩

private theorem fastInsertAllocGenProg_fastStep {c U V w n_max base b X : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hX_tl : X < totalLocalCoordsWhp n_max)
    (hcf_fn : capFrontWhp n_max ≤ X →
      0 < fs.poolFreeTop ∧
      fs.poolFreeTop ≤ poolSizeWhp n_max ∧
      fs.poolFreeStack (fs.poolFreeTop - 1) < poolSizeWhp n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := fastInsertAllocGenProg (((mkWhpCoreParams c U V w n_max, base), b), X)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 12 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (fastInsertAlloc n_max b X fs) s s' := by
  have hth := henv.2.2.2.1
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have hmcb := (large_index_bounds hth).1
  have hps_le := (large_index_bounds hth).2.2.2.1
  set cp := mkWhpCoreParams c U V w n_max
  dsimp only
  unfold fastInsertAllocGenProg fastInsertAlloc; dsimp only
  simp only [cp, wp_large_capFront hth, pure_bind]
  by_cases hcf : capFrontWhp n_max ≤ X
  · simp only [hcf, ↓reduceIte]
    obtain ⟨hpos, hle_ps, hp_lt⟩ := hcf_fn hcf
    have hk : X - capFrontWhp n_max < capBackWhp n_max := by
      unfold totalLocalCoordsWhp at hX_tl; omega
    set k := X - capFrontWhp n_max
    set top' := fs.poolFreeTop - 1
    set pSlot := fs.poolFreeStack top'
    obtain ⟨ht_st, ht_res, ht_mc, ht_vp⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrPoolFreeTop)
      (by dsimp [hdrPoolFreeTop]; omega) (s := s)
    rw [hrep.2.2.1] at ht_res
    obtain ⟨hp_st, hp_res, hp_mc, hp_vp⟩ :=
      readPoolFreeStackGenProg_spec henv (by omega : top' < poolSizeWhp n_max) hrep (s := s)
    obtain ⟨hwh_mc, hwh_vp, hwh_step⟩ := writeHdrProg_fastStep (hdrOff := hdrPoolFreeTop) henv
      (by decide) (henv.fits_of_le_n_max (by omega)) (by intro h; cases h) hseed hrep
      (val := top') (s := s)
    dsimp only [updateFastHdr] at hwh_step
    set s1 := (Memory.spec 0).clientState s (writeHdrProg ((base, hdrPoolFreeTop), top'))
    obtain ⟨hwb_mc, hwb_vp, hwb_step⟩ := writeBackPtrGenProg_fastStep henv hb hk
      (by omega : pSlot ≤ n_max) hwh_step.2.1 hwh_step.2.2.1 (s := s1)
    set s2 := (Memory.spec 0).clientState s1 (writeBackPtrGenProg ((((cp, base), b), k), pSlot))
    have hidx_enc : b * capBackWhp n_max + k < numBucketsWhp n_max * capBackWhp n_max :=
      mul_add_lt_mul_bound hb hk
    obtain ⟨hwo_mc, hwo_vp, hwo_step⟩ := writePoolOwnerGenProg_fastStep henv hp_lt
      (by omega : b * capBackWhp n_max + k ≤ n_max) hwb_step.2.1 hwb_step.2.2.1 (s := s2)
    have hpop_st : (Memory.spec 0).clientState s (insPopFreeSlotGenProg (cp, base)) = s1 := by
      unfold insPopFreeSlotGenProg; dsimp only; simp only [pure_bind]
      rw [clientState_bind, ht_st, ht_res, clientState_bind, hp_st, hp_res,
        clientState_bind, clientState_pure_whp]
    have hpop_res : (Memory.spec 0).clientResult s (insPopFreeSlotGenProg (cp, base)) = pSlot := by
      unfold insPopFreeSlotGenProg; dsimp only; simp only [pure_bind]
      rw [clientResult_bind, ht_st, ht_res, clientResult_bind, hp_st, hp_res,
        clientResult_bind, clientResult_pure_whp]
    have hpop_mc : memoryCost (insPopFreeSlotGenProg (cp, base)) s ≤ 4 := by
      unfold insPopFreeSlotGenProg; dsimp only
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      dsimp only [cp, top'] at hp_st hp_res hp_mc hwh_mc ⊢
      rw [ht_st, ht_res, ht_mc, hp_st, hp_res, hp_mc, memoryCost_pure]; omega
    have hpop_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
        (insPopFreeSlotGenProg (cp, base)) := by
      unfold insPopFreeSlotGenProg; dsimp only; simp only [pure_bind]
      refine validProg_bind ht_vp ?_; rw [ht_st, ht_res]
      refine validProg_bind hp_vp ?_; rw [hp_st, hp_res]
      exact validProg_bind hwh_vp (validProg_pure _)
    unfold insAllocBackyardProg; dsimp only
    simp only [wp_large_capFront hth, pure_bind]
    have hs'_eq : (Memory.spec 0).clientState s
        (insPopFreeSlotGenProg (cp, base) >>= fun p =>
          insBindBackSlotGenProg ((((cp, base), b), k), p)) =
        (Memory.spec 0).clientState s2
          (writePoolOwnerGenProg (((cp, base), pSlot), b * capBackWhp n_max + k)) := by
      rw [clientState_bind, hpop_st, hpop_res]
      unfold insBindBackSlotGenProg; dsimp only
      simp only [cp, wp_large_capBack hth, pure_bind]
      rw [clientState_bind]
    rw [hs'_eq]
    refine ⟨?_, ?_, (hwh_step.trans hwb_step).trans hwo_step⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hpop_st, hpop_res]
      unfold insBindBackSlotGenProg; dsimp only
      simp only [wp_large_capBack hth, pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      dsimp only [s1, s2, cp, k, pSlot] at hpop_mc hwb_mc hwo_mc ⊢; omega
    · refine validProg_bind hpop_vp ?_; rw [hpop_st, hpop_res]
      unfold insBindBackSlotGenProg; dsimp only
      simp only [wp_large_capBack hth, pure_bind]
      exact validProg_bind hwb_vp hwo_vp
  · simp only [hcf, ↓reduceIte, memoryCost_pure]
    exact ⟨Nat.zero_le _, validProg_pure _, FastStateStep.refl hseed hrep⟩

/-- Write `(q_val, v_val)` at `physSlot b X` (`d = ((((cp, base), b), X), (q_val, v_val))`). -/
@[irreducible] private def insWriteQVAtGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((((cp, base), b), X), (q_val, v_val)) => do
    let p_new ← physSlotGenProg (((cp, base), b), X)
    writeQuotGenProg (((cp, base), p_new), q_val)
    writeValGenProg (((cp, base), p_new), v_val)

private theorem realizes_insWriteQVAtGen :
    Realizes .exact insWriteQVAtGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), X), (q_val, _)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          X < totalLocalCoordsWhp n_max ∧
          (capFrontWhp n_max ≤ X → fs.backPtr b (X - capFrontWhp n_max) < poolSizeWhp n_max) ∧
          q_val < 2 ^ quotBitsWhp U n_max)
      (fun _ _ => 0) := by
  unfold insWriteQVAtGenProg
  have hps := realizes_physSlotGen
  have hwq := realizes_writeQuotGen
  have hwv := realizes_writeValGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, X⟩, ⟨q_val, v_val⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, rfl, hseed, hrep, hb, hX_tl, hbp, hq_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    obtain ⟨hps_st, hps_res, hps_lt, _, _⟩ := physSlotGenProg_spec henv hb hX_tl hbp hrep (s := s)
    obtain ⟨_, _, hwq_step⟩ := writeQuotGenProg_fastStep henv hps_lt hq_lt hseed hrep (s := s)
    simp only [hps_st, hps_res, wp_large_nMax hth] at *
    first
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hX_tl, hbp⟩
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hps_lt
  )

private theorem insWriteQVAtGenProg_fastStep {c U V w n_max base b X q_val v_val : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hX_tl : X < totalLocalCoordsWhp n_max)
    (hbp : capFrontWhp n_max ≤ X → fs.backPtr b (X - capFrontWhp n_max) < poolSizeWhp n_max)
    (hq_lt : q_val < 2 ^ quotBitsWhp U n_max)
    (hv_lt : v_val < 2 ^ valBits V)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := insWriteQVAtGenProg
      ((((mkWhpCoreParams c U V w n_max, base), b), X), (q_val, v_val))
    let s' := (Memory.spec 0).clientState s prog
    let p_new := fs.physSlot n_max b X
    memoryCost prog s ≤ 10 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        quotArr := Function.update fs.quotArr p_new q_val
        valArr := Function.update fs.valArr p_new v_val } s s' := by
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hps_st, hps_res, hps_lt, hps_mc, hps_vp⟩ :=
    physSlotGenProg_spec henv hb hX_tl hbp hrep (s := s)
  obtain ⟨hwq_mc, hwq_vp, hwq_step⟩ :=
    writeQuotGenProg_fastStep henv hps_lt hq_lt hseed hrep (s := s)
  set s1 := (Memory.spec 0).clientState s
    (writeQuotGenProg (((cp, base), fs.physSlot n_max b X), q_val))
  obtain ⟨hwv_mc, hwv_vp, hwv_step⟩ :=
    writeValGenProg_fastStep henv hps_lt hv_lt hwq_step.2.1 hwq_step.2.2.1 (s := s1)
  dsimp only
  unfold insWriteQVAtGenProg; dsimp only
  have hs'_eq : (Memory.spec 0).clientState s
      (physSlotGenProg (((cp, base), b), X) >>= fun p =>
        writeQuotGenProg (((cp, base), p), q_val) >>= fun _ =>
        writeValGenProg (((cp, base), p), v_val)) =
      (Memory.spec 0).clientState s1
        (writeValGenProg (((cp, base), fs.physSlot n_max b X), v_val)) := by
    rw [clientState_bind, hps_st, hps_res, clientState_bind]
  rw [hs'_eq]
  refine ⟨?_, ?_, hwq_step.trans hwv_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hps_st, hps_res]; dsimp only [s1, cp] at hps_mc hwq_mc hwv_mc ⊢; omega
  · refine validProg_bind hps_vp ?_; rw [hps_st, hps_res]
    exact validProg_bind hwq_vp hwv_vp

/-- Set `bktCount b := X + 1` and `locState b X := tag` (`d = ((((cp, base), b), X), tag)`). -/
@[irreducible] private def insWriteCntLocGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | ((((cp, base), b), X), tag) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let X1 ← pure (X + z1)
    writeBktFieldGenProg ((((cp, base), b), z0), X1)
    writeFastLocGenProg ((((cp, base), b), X), tag)

private theorem realizes_insWriteCntLocGen :
    Realizes .exact insWriteCntLocGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), X), _) _ =>
        WhpLargeEnvGen w cp base ∧ b < wpM cp ∧ X < wpTotalLoc cp)
      (fun _ _ => 0) := by
  unfold insWriteCntLocGenProg
  have hwb := realizes_writeBktFieldGen
  have hwl := realizes_writeFastLocGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, X⟩, tag⟩
    dsimp only at *
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb, hX_tl⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h2tl := (large_index_bounds hth).2.2.1
    simp only [wp_large_M hth, wp_large_totalLoc hth] at hb hX_tl ⊢
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact hX_tl
  )

private theorem insWriteCntLocGenProg_fastStep {c U V w n_max base b X tag : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hX_tl : X < totalLocalCoordsWhp n_max)
    (htag : tag < 4)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := insWriteCntLocGenProg ((((mkWhpCoreParams c U V w n_max, base), b), X), tag)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 8 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        bktCount := Function.update fs.bktCount b (X + 1)
        locState := Function.update fs.locState b
          (Function.update (fs.locState b) X tag) } s s' := by
  have h2tl := (large_index_bounds henv.2.2.2.1).2.2.1
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hwb_mc, hwb_vp, hwb_step⟩ := writeBktFieldGenProg_fastStep henv hb (by decide : 0 < 10)
    (by omega : X + 1 ≤ n_max) hseed hrep (s := s)
  simp only [setBktField] at hwb_step
  set s1 := (Memory.spec 0).clientState s (writeBktFieldGenProg ((((cp, base), b), 0), X + 1))
  obtain ⟨hwl_mc, hwl_vp, hwl_step⟩ := writeFastLocGenProg_fastStep henv hb hX_tl htag
    hwb_step.2.1 hwb_step.2.2.1 (s := s1)
  dsimp only
  unfold insWriteCntLocGenProg; dsimp only; simp only [pure_bind]
  have hs'_eq : (Memory.spec 0).clientState s
      (writeBktFieldGenProg ((((cp, base), b), 0), X + 1) >>= fun _ =>
        writeFastLocGenProg ((((cp, base), b), X), tag)) =
      (Memory.spec 0).clientState s1
        (writeFastLocGenProg ((((cp, base), b), X), tag)) := by
    rw [clientState_bind]
  rw [hs'_eq]
  refine ⟨?_, ?_, hwb_step.trans hwl_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    dsimp only [s1, cp] at hwb_mc hwl_mc ⊢; omega
  · exact validProg_bind hwb_vp hwl_vp

/-- Increment `liveInsCount b` by `1` (`d = ((cp, base), b)`). -/
@[irreducible] private def insIncLiveInsGenProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, base), b) => do
    let z1 ← pure 1
    let f3 ← pure 3
    let lic ← readBktFieldGenProg (((cp, base), b), f3)
    let lic1 ← pure (lic + z1)
    writeBktFieldGenProg ((((cp, base), b), f3), lic1)

private theorem realizes_insIncLiveInsGen :
    Realizes .exact insIncLiveInsGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((cp, base), b) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12)
      (fun _ _ => 0) := by
  unfold insIncLiveInsGenProg
  have hrb := realizes_readBktFieldGen
  have hwb := realizes_writeBktFieldGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hb, hlic⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hML12 := numBucketsWhp_mul_scale_pow12_le hth
    have hM_ge := (large_bounds_lt_n_max hth).1
    have h9L12_n : 9 * (slabScale n_max) ^ 12 ≤ n_max :=
      (Nat.mul_le_mul_right _ (by omega : 9 ≤ numBucketsWhp n_max)).trans hML12
    have hL12_pos : 1 ≤ (slabScale n_max) ^ 12 := Nat.one_le_pow 12 _ (slabScale_pos n_max)
    obtain ⟨h3_st, h3_res, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 3 < 10) hrep (s := s)
    simp only [getBktField] at h3_res
    simp only [h3_st, h3_res, wp_large_M hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
  )

private theorem insIncLiveInsGenProg_fastStep {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hlic : fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := insIncLiveInsGenProg ((mkWhpCoreParams c U V w n_max, base), b)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 6 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        liveInsCount := Function.update fs.liveInsCount b (fs.liveInsCount b + 1) } s s' := by
  have hth := henv.2.2.2.1
  have hML12 := numBucketsWhp_mul_scale_pow12_le hth
  have hM_ge := (large_bounds_lt_n_max hth).1
  have h9L12_n : 9 * (slabScale n_max) ^ 12 ≤ n_max :=
    (Nat.mul_le_mul_right _ (by omega : 9 ≤ numBucketsWhp n_max)).trans hML12
  have hL12_pos : 1 ≤ (slabScale n_max) ^ 12 := Nat.one_le_pow 12 _ (slabScale_pos n_max)
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨h3_st, h3_res, h3_mc, h3_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 3 < 10) hrep (s := s)
  simp only [getBktField] at h3_res
  obtain ⟨hwb_mc, hwb_vp, hwb_step⟩ := writeBktFieldGenProg_fastStep henv hb (by decide : 3 < 10)
    (by omega : fs.liveInsCount b + 1 ≤ n_max) hseed hrep (s := s)
  simp only [setBktField] at hwb_step
  dsimp only
  unfold insIncLiveInsGenProg; dsimp only; simp only [pure_bind]
  have hs'_eq : (Memory.spec 0).clientState s
      (readBktFieldGenProg (((cp, base), b), 3) >>= fun lic =>
        writeBktFieldGenProg ((((cp, base), b), 3), lic + 1)) =
      (Memory.spec 0).clientState s
        (writeBktFieldGenProg ((((cp, base), b), 3), fs.liveInsCount b + 1)) := by
    rw [clientState_bind, h3_st, h3_res]
  rw [hs'_eq]
  refine ⟨?_, ?_, hwb_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [h3_st, h3_res, h3_mc]; dsimp only [cp] at hwb_mc ⊢; omega
  · refine validProg_bind h3_vp ?_; rw [h3_st, h3_res]; exact hwb_vp

/-- Finish collision insertion (`hasFpCollision = true`): write `bktCount`, `locState := 2 + curEp`,
and insert `(b, X)` into `buf curEp` (`d = ((((cp, base), b), X), rKey)`). -/
@[irreducible] private def insFinishCollisionGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | ((((cp, base), b), X), rKey) => do
    let z2 ← pure 2
    let ep ← readHdrProg (base, hdrCurEp)
    let tag ← pure (z2 + ep)
    insWriteCntLocGenProg ((((cp, base), b), X), tag)
    bufInsertGenProg ((((cp, base), ep), rKey), (b, X))

private theorem realizes_insFinishCollisionGen :
    Realizes .exact insFinishCollisionGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), X), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState)
            (curMap : ℕ → Option (ℕ × ℕ)),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          b < numBucketsWhp n_max ∧
          X < totalLocalCoordsWhp n_max ∧
          (fs.buf fs.curEp).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
          (fs.buf fs.curEp).itemAlloc < qEpochWhp n_max ∧
          ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) curMap)
      (fun _ _ => 0) := by
  unfold insFinishCollisionGenProg
  have hrh := realizes_readHdr
  have hwc := realizes_insWriteCntLocGen
  have hbi := realizes_bufInsertGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, X⟩, rKey⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, curMap, henv, rfl, hseed, hrep, hce, hb, hX_tl,
      hna_cap, hia_cap, hv_cur⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h2w := henv.two_le_w
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have htag_lt : 2 + fs.curEp < 4 := by rcases hce with hc | hc <;> omega
    have hfit_tag : Fits w (2 + fs.curEp) := by
      have h4 : 4 ≤ 2 ^ w := (by decide : 4 ≤ 2 ^ 2).trans (Nat.pow_le_pow_right two_pos h2w)
      change 2 + fs.curEp < 2 ^ w; omega
    obtain ⟨hep_st, hep_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrCurEp)
      (by dsimp [hdrCurEp]; omega) (s := s)
    rw [hrep.2.2.2.1] at hep_res
    obtain ⟨_, _, hwc_step⟩ :=
      insWriteCntLocGenProg_fastStep henv hb hX_tl htag_lt hseed hrep (s := s)
    simp only [hep_st, hep_res, wp_large_M hth, wp_large_totalLoc hth] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact hfit_tag
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact hX_tl
    | exact ⟨c, U, V, w, n_max, _, curMap, henv, rfl, hce,
        FastMemRep.buf_rep hce hwc_step.2.2.1, hv_cur, hna_cap, hia_cap, hb, hX_tl⟩
  )

/-- Finish direct insertion (`hasFpCollision = false`): write `bktCount`, `locState := 1`, insert
`(fp, X)` into `slices lIdx`, and increment `liveInsCount b`. -/
@[irreducible] private def insFinishDirectGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((((cp, base), b), X), (fp, lIdx)) => do
    let z1 ← pure 1
    insWriteCntLocGenProg ((((cp, base), b), X), z1)
    btreeInsertGenProg ((((cp, base), lIdx), fp), X)
    insIncLiveInsGenProg ((cp, base), b)

private theorem realizes_insFinishDirectGen :
    Realizes .exact insFinishDirectGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), X), (fp, lIdx)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (lm : ℕ → Option ℕ),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          X < totalLocalCoordsWhp n_max ∧
          lIdx = fs.liveSliceIdx b ∧
          lIdx < 3 * numBucketsWhp n_max ∧
          fp < 2 ^ fpBitsWhp n_max ∧
          fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
          ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices lIdx) lm)
      (fun _ _ => 0) := by
  unfold insFinishDirectGenProg
  have hwc := realizes_insWriteCntLocGen
  have hbi := realizes_btreeInsertGen
  have hic := realizes_insIncLiveInsGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, X⟩, ⟨fp, lIdx⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, lm, henv, rfl, hseed, hrep, hb, hX_tl, rfl,
      hlIdx, hfp_lt, hlic, hv_l⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hval_X := loc_lt_two_pow_valLaneBits hX_tl
    obtain ⟨_, _, hwc_step⟩ :=
      insWriteCntLocGenProg_fastStep henv hb hX_tl (by decide : 1 < 4) hseed hrep (s := s)
    set fs1 : FastState :=
      { fs with
        bktCount := Function.update fs.bktCount b (X + 1)
        locState := Function.update fs.locState b (Function.update (fs.locState b) X 1) }
    set s1 := (Memory.spec 0).clientState s
      (insWriteCntLocGenProg ((((mkWhpCoreParams c U V w n_max, base), b), X), 1))
    obtain ⟨_, _, hbi_step⟩ :=
      btreeInsertGenProg_fastStep (fs := fs1) henv hlIdx hlic
        hwc_step.2.1 hwc_step.2.2.1 hv_l hfp_lt hval_X (s := s1)
    try simp only [wp_large_M hth, wp_large_totalLoc hth] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact hX_tl
    | exact ⟨c, U, V, w, n_max, fs.liveInsCount b, _, lm,
        henv, rfl, hlIdx, hlic, FastMemRep.slice_rep hlIdx hwc_step.2.2.1, hv_l, hfp_lt, hval_X⟩
    | exact ⟨c, U, V, w, n_max, _, henv, rfl, hbi_step.2.2.1, hb, hlic⟩
  )

private theorem insFinishCollisionGenProg_fastStep {c U V w n_max base b X rKey : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {curMap : ℕ → Option (ℕ × ℕ)} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1)
    (hb : b < numBucketsWhp n_max) (hX_tl : X < totalLocalCoordsWhp n_max)
    (hna_cap : (fs.buf fs.curEp).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max)
    (hia_cap : (fs.buf fs.curEp).itemAlloc < qEpochWhp n_max)
    (hv_cur : ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) curMap)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := insFinishCollisionGenProg
      ((((mkWhpCoreParams c U V w n_max, base), b), X), rKey)
    let s' := (Memory.spec 0).clientState s prog
    let ep := fs.curEp
    let tr' := bufInsert (cTabWhp c) (bCharWhp n_max) (fs.buf ep) rKey b X
    memoryCost prog s ≤ 20 * cTabWhp c + 33 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        bktCount := Function.update fs.bktCount b (X + 1)
        locState := Function.update fs.locState b
          (Function.update (fs.locState b) X (2 + ep))
        buf := Function.update fs.buf ep tr' } s s' := by
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have htag_lt : 2 + fs.curEp < 4 := by rcases hce with hc | hc <;> omega
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hep_st, hep_res, hep_mc, hep_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrCurEp)
    (by dsimp [hdrCurEp]; omega) (s := s)
  rw [hrep.2.2.2.1] at hep_res
  obtain ⟨hwc_mc, hwc_vp, hwc_step⟩ :=
    insWriteCntLocGenProg_fastStep henv hb hX_tl htag_lt hseed hrep (s := s)
  set fs1 : FastState :=
    { fs with
      bktCount := Function.update fs.bktCount b (X + 1)
      locState := Function.update fs.locState b
        (Function.update (fs.locState b) X (2 + fs.curEp)) }
  set s1 := (Memory.spec 0).clientState s
    (insWriteCntLocGenProg ((((cp, base), b), X), 2 + fs.curEp))
  obtain ⟨hbi_mc, hbi_vp, hbi_step⟩ :=
    bufInsertGenProg_fastStep (fs := fs1) henv hce hwc_step.2.1 hwc_step.2.2.1 hv_cur
      hna_cap hia_cap hb hX_tl (rKey := rKey) (s := s1)
  dsimp only
  unfold insFinishCollisionGenProg; dsimp only; simp only [pure_bind]
  have hs'_eq : (Memory.spec 0).clientState s
      (readHdrProg (base, hdrCurEp) >>= fun ep =>
        insWriteCntLocGenProg ((((cp, base), b), X), 2 + ep) >>= fun _ =>
        bufInsertGenProg ((((cp, base), ep), rKey), (b, X))) =
      (Memory.spec 0).clientState s1
        (bufInsertGenProg ((((cp, base), fs.curEp), rKey), (b, X))) := by
    rw [clientState_bind, hep_st, hep_res, clientState_bind]
  rw [hs'_eq]
  refine ⟨?_, ?_, hwc_step.trans hbi_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hep_st, hep_res, hep_mc]
    dsimp only [s1, cp] at hwc_mc hbi_mc ⊢; omega
  · refine validProg_bind hep_vp ?_; rw [hep_st, hep_res]
    exact validProg_bind hwc_vp hbi_vp

private theorem insFinishDirectGenProg_fastStep {c U V w n_max base b X fp lIdx : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {lm : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hX_tl : X < totalLocalCoordsWhp n_max)
    (hlIdx_eq : lIdx = fs.liveSliceIdx b)
    (hlIdx : lIdx < 3 * numBucketsWhp n_max)
    (hfp_lt : fp < 2 ^ fpBitsWhp n_max)
    (hlic : fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12)
    (hv_l : ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices lIdx) lm)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := insFinishDirectGenProg
      ((((mkWhpCoreParams c U V w n_max, base), b), X), (fp, lIdx))
    let s' := (Memory.spec 0).clientState s prog
    let sl' := btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      (fs.slices lIdx) fp X
    memoryCost prog s ≤ 2440 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        bktCount := Function.update fs.bktCount b (X + 1)
        locState := Function.update fs.locState b (Function.update (fs.locState b) X 1)
        slices := Function.update fs.slices lIdx sl'
        liveInsCount := Function.update fs.liveInsCount b (fs.liveInsCount b + 1) } s s' := by
  subst hlIdx_eq
  have hval_X := loc_lt_two_pow_valLaneBits hX_tl
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hwc_mc, hwc_vp, hwc_step⟩ :=
    insWriteCntLocGenProg_fastStep henv hb hX_tl (by decide : 1 < 4) hseed hrep (s := s)
  set fs1 : FastState :=
    { fs with
      bktCount := Function.update fs.bktCount b (X + 1)
      locState := Function.update fs.locState b (Function.update (fs.locState b) X 1) }
  set s1 := (Memory.spec 0).clientState s
    (insWriteCntLocGenProg ((((cp, base), b), X), 1))
  obtain ⟨hbi_mc, hbi_vp, hbi_step⟩ :=
    btreeInsertGenProg_fastStep (fs := fs1) henv hlIdx hlic
      hwc_step.2.1 hwc_step.2.2.1 hv_l hfp_lt hval_X (s := s1)
  set fs2 : FastState :=
    { fs1 with
      slices := Function.update fs1.slices (fs.liveSliceIdx b)
        (btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.liveSliceIdx b)) fp X) }
  set s2 := (Memory.spec 0).clientState s1
    (btreeInsertGenProg ((((cp, base), fs.liveSliceIdx b), fp), X))
  obtain ⟨hic_mc, hic_vp, hic_step⟩ :=
    insIncLiveInsGenProg_fastStep (fs := fs2) henv hb hlic hbi_step.2.1 hbi_step.2.2.1 (s := s2)
  dsimp only
  unfold insFinishDirectGenProg; dsimp only; simp only [pure_bind]
  have hs'_eq : (Memory.spec 0).clientState s
      (insWriteCntLocGenProg ((((cp, base), b), X), 1) >>= fun _ =>
        btreeInsertGenProg ((((cp, base), fs.liveSliceIdx b), fp), X) >>= fun _ =>
        insIncLiveInsGenProg ((cp, base), b)) =
      (Memory.spec 0).clientState s2
        (insIncLiveInsGenProg ((cp, base), b)) := by
    rw [clientState_bind, clientState_bind]
  rw [hs'_eq]
  refine ⟨?_, ?_, (hwc_step.trans hbi_step).trans hic_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    dsimp only [s1, s2, cp] at hwc_mc hbi_mc hic_mc ⊢; omega
  · exact validProg_bind hwc_vp (validProg_bind hbi_vp hic_vp)

/-- Allocate slot, write `(q_val, v_val)`, and insert into `buf curEp` or `slices lIdx`
(`d = ((((cp, base), (b, X)), (q_val, v_val)), (hasCol, (rKey, (fp, lIdx))))`). -/
@[irreducible] private def fastInsertFreshGenProg :
    (((WhpCoreParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × ℕ))) → Memory.Prog Unit
  | ((((cp, base), (b, X)), (q_val, v_val)), (hasCol, (rKey, (fp, lIdx)))) => do
    let z1 ← pure 1
    fastInsertAllocGenProg (((cp, base), b), X)
    insWriteQVAtGenProg ((((cp, base), b), X), (q_val, v_val))
    if hasCol = z1 then
      insFinishCollisionGenProg ((((cp, base), b), X), rKey)
    else
      insFinishDirectGenProg ((((cp, base), b), X), (fp, lIdx))

private theorem realizes_fastInsertFreshGen :
    Realizes .exact fastInsertFreshGenProg
      (WordEncoding.encode
        (α := (((WhpCoreParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × ℕ)))))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), (b, X)), (q_val, v_val)), (hasCol, (_, (fp, lIdx)))) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          b < numBucketsWhp n_max ∧
          X < totalLocalCoordsWhp n_max ∧
          (capFrontWhp n_max ≤ X →
            0 < fs.poolFreeTop ∧
            fs.poolFreeTop ≤ poolSizeWhp n_max ∧
            fs.poolFreeStack (fs.poolFreeTop - 1) < poolSizeWhp n_max) ∧
          q_val < 2 ^ quotBitsWhp U n_max ∧
          v_val < 2 ^ valBits V ∧
          (hasCol = 1 →
            (fs.buf fs.curEp).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
            (fs.buf fs.curEp).itemAlloc < qEpochWhp n_max ∧
            ∃ curMap, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) curMap) ∧
          (hasCol ≠ 1 →
            lIdx = fs.liveSliceIdx b ∧
            lIdx < 3 * numBucketsWhp n_max ∧
            fp < 2 ^ fpBitsWhp n_max ∧
            fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
            ∃ lm, ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices lIdx) lm))
      (fun _ _ => 0) := by
  unfold fastInsertFreshGenProg
  have hal := realizes_fastInsertAllocGen
  have hwq := realizes_insWriteQVAtGen
  have hfc := realizes_insFinishCollisionGen
  have hfd := realizes_insFinishDirectGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, ⟨b, X⟩⟩, ⟨q_val, v_val⟩⟩, ⟨hasCol, ⟨rKey, ⟨fp, lIdx⟩⟩⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, rfl, hseed, hrep, hce, hb, hX_tl, hcf_fn,
      hq_lt, hv_lt, hcol1, hcol0⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hbp_alloc : capFrontWhp n_max ≤ X →
        (fastInsertAlloc n_max b X fs).backPtr b (X - capFrontWhp n_max) < poolSizeWhp n_max := by
      intro hcf
      unfold fastInsertAlloc; dsimp only
      rw [ite_eq_left hcf]; dsimp only
      simp only [Function.update_self]
      exact (hcf_fn hcf).2.2
    obtain ⟨_, _, hal_step⟩ :=
      fastInsertAllocGenProg_fastStep henv hb hX_tl hcf_fn hseed hrep (s := s)
    set fsAlloc := fastInsertAlloc n_max b X fs
    set s1 := (Memory.spec 0).clientState s
      (fastInsertAllocGenProg (((mkWhpCoreParams c U V w n_max, base), b), X))
    obtain ⟨_, _, hwq_step⟩ :=
      insWriteQVAtGenProg_fastStep (fs := fsAlloc) henv hb hX_tl hbp_alloc hq_lt hv_lt
        hal_step.2.1 hal_step.2.2.1 (s := s1)
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hX_tl, hcf_fn⟩
    | exact ⟨c, U, V, w, n_max, θ, fsAlloc, henv, rfl,
        hal_step.2.1, hal_step.2.2.1, hb, hX_tl, hbp_alloc, hq_lt⟩
    | (obtain ⟨hna_cap, hia_cap, curMap, hv_cur⟩ := hcol1 (by assumption)
       exact ⟨c, U, V, w, n_max, θ, _, curMap, henv, rfl, hwq_step.2.1, hwq_step.2.2.1,
         hce, hb, hX_tl, hna_cap, hia_cap, hv_cur⟩)
    | (obtain ⟨hlIdx_eq, hlIdx, hfp_lt, hlic, lm, hv_l⟩ := hcol0 (by assumption)
       exact ⟨c, U, V, w, n_max, θ, _, lm, henv, rfl, hwq_step.2.1, hwq_step.2.2.1,
         hb, hX_tl, hlIdx_eq, hlIdx, hfp_lt, hlic, hv_l⟩)
  )

private theorem fastInsertFreshGenProg_fastStep
    {c U V w n_max base b X q_val v_val rKey fp lIdx : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State} (hasFpCollision : Bool)
    (henv : WhpLargeEnv c U V w n_max w base)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1)
    (hb : b < numBucketsWhp n_max) (hX_tl : X < totalLocalCoordsWhp n_max)
    (hcf_fn : capFrontWhp n_max ≤ X →
      0 < fs.poolFreeTop ∧
      fs.poolFreeTop ≤ poolSizeWhp n_max ∧
      fs.poolFreeStack (fs.poolFreeTop - 1) < poolSizeWhp n_max)
    (hq_lt : q_val < 2 ^ quotBitsWhp U n_max)
    (hv_lt : v_val < 2 ^ valBits V)
    (hcol_t : hasFpCollision = true →
      (fs.buf fs.curEp).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
      (fs.buf fs.curEp).itemAlloc < qEpochWhp n_max ∧
      ∃ curMap, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) curMap)
    (hcol_f : hasFpCollision = false →
      lIdx = fs.liveSliceIdx b ∧
      lIdx < 3 * numBucketsWhp n_max ∧
      fp < 2 ^ fpBitsWhp n_max ∧
      fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
      ∃ lm, ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices lIdx) lm)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let hasCol := if hasFpCollision then 1 else 0
    let prog := fastInsertFreshGenProg
      ((((mkWhpCoreParams c U V w n_max, base), (b, X)), (q_val, v_val)),
       (hasCol, (rKey, (fp, lIdx))))
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 20 * cTabWhp c + 2462 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      (fastInsertFresh c n_max b X q_val v_val rKey fp lIdx hasFpCollision
        (fastInsertAlloc n_max b X fs)) s s' := by
  set cp := mkWhpCoreParams c U V w n_max
  have hbp_alloc : capFrontWhp n_max ≤ X →
      (fastInsertAlloc n_max b X fs).backPtr b (X - capFrontWhp n_max) < poolSizeWhp n_max := by
    intro hcf
    unfold fastInsertAlloc; dsimp only
    rw [ite_eq_left hcf]; dsimp only
    simp only [Function.update_self]
    exact (hcf_fn hcf).2.2
  obtain ⟨hal_mc, hal_vp, hal_step⟩ :=
    fastInsertAllocGenProg_fastStep henv hb hX_tl hcf_fn hseed hrep (s := s)
  set fsAlloc := fastInsertAlloc n_max b X fs
  set s1 := (Memory.spec 0).clientState s (fastInsertAllocGenProg (((cp, base), b), X))
  obtain ⟨hwq_mc, hwq_vp, hwq_step⟩ :=
    insWriteQVAtGenProg_fastStep (fs := fsAlloc) henv hb hX_tl hbp_alloc hq_lt hv_lt
      hal_step.2.1 hal_step.2.2.1 (s := s1)
  set fsQV : FastState :=
    { fsAlloc with
      quotArr := Function.update fsAlloc.quotArr (fsAlloc.physSlot n_max b X) q_val
      valArr := Function.update fsAlloc.valArr (fsAlloc.physSlot n_max b X) v_val }
  set s2 := (Memory.spec 0).clientState s1
    (insWriteQVAtGenProg ((((cp, base), b), X), (q_val, v_val)))
  dsimp only
  unfold fastInsertFreshGenProg fastInsertFresh; dsimp only; simp only [pure_bind]
  cases hasFpCollision with
  | true =>
    simp only [↓reduceIte]
    obtain ⟨hna_cap, hia_cap, curMap, hv_cur⟩ := hcol_t rfl
    obtain ⟨hfc_mc, hfc_vp, hfc_step⟩ :=
      insFinishCollisionGenProg_fastStep (fs := fsQV) henv hce hb hX_tl hna_cap hia_cap hv_cur
        hwq_step.2.1 hwq_step.2.2.1 (rKey := rKey) (s := s2)
    have hs'_eq : (Memory.spec 0).clientState s
        (fastInsertAllocGenProg (((cp, base), b), X) >>= fun _ =>
          insWriteQVAtGenProg ((((cp, base), b), X), (q_val, v_val)) >>= fun _ =>
          insFinishCollisionGenProg ((((cp, base), b), X), rKey)) =
        (Memory.spec 0).clientState s2
          (insFinishCollisionGenProg ((((cp, base), b), X), rKey)) := by
      rw [clientState_bind, clientState_bind]
    rw [hs'_eq]
    refine ⟨?_, ?_, (hal_step.trans hwq_step).trans hfc_step⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      dsimp only [s1, s2, cp] at hal_mc hwq_mc hfc_mc ⊢; omega
    · exact validProg_bind hal_vp (validProg_bind hwq_vp hfc_vp)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, zero_ne_one]
    obtain ⟨hlIdx_eq, hlIdx, hfp_lt, hlic, lm, hv_l⟩ := hcol_f rfl
    obtain ⟨hfd_mc, hfd_vp, hfd_step⟩ :=
      insFinishDirectGenProg_fastStep (fs := fsQV) henv hb hX_tl hlIdx_eq hlIdx hfp_lt hlic hv_l
        hwq_step.2.1 hwq_step.2.2.1 (s := s2)
    have hs'_eq : (Memory.spec 0).clientState s
        (fastInsertAllocGenProg (((cp, base), b), X) >>= fun _ =>
          insWriteQVAtGenProg ((((cp, base), b), X), (q_val, v_val)) >>= fun _ =>
          insFinishDirectGenProg ((((cp, base), b), X), (fp, lIdx))) =
        (Memory.spec 0).clientState s2
          (insFinishDirectGenProg ((((cp, base), b), X), (fp, lIdx))) := by
      rw [clientState_bind, clientState_bind]
    rw [hs'_eq]
    refine ⟨?_, ?_, (hal_step.trans hwq_step).trans hfd_step⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      dsimp only [s1, s2, cp] at hal_mc hwq_mc hfd_mc ⊢; omega
    · exact validProg_bind hal_vp (validProg_bind hwq_vp hfd_vp)

private theorem overmarsBucketStepBounds_insFresh {c U V n_max b q_val v_val rKey fp : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} (hasFpCollision : Bool)
    (hv : ValidFastState c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max)
    (hX_tl : fs.bktCount b < totalLocalCoordsWhp n_max)
    (hcf_fn : capFrontWhp n_max ≤ fs.bktCount b →
      0 < fs.poolFreeTop ∧
      fs.poolFreeTop ≤ poolSizeWhp n_max ∧
      fs.poolFreeStack (fs.poolFreeTop - 1) < poolSizeWhp n_max)
    (hq_lt : q_val < 2 ^ quotBitsWhp U n_max) :
    OvermarsBucketStepBounds U n_max b
      (fastInsertFresh c n_max b (fs.bktCount b) q_val v_val rKey fp (fs.liveSliceIdx b)
        hasFpCollision (fastInsertAlloc n_max b (fs.bktCount b) fs)) := by
  set X := fs.bktCount b
  set fsIns := fastInsertFresh c n_max b X q_val v_val rKey fp (fs.liveSliceIdx b) hasFpCollision
    (fastInsertAlloc n_max b X fs)
  have h2tl := (large_index_bounds hv.hth).2.2.1
  have hL2 := two_le_slabScale n_max
  have hL12 : 4096 ≤ (slabScale n_max) ^ 12 := by
    calc 4096 = 2 ^ 12 := by decide
      _ ≤ (slabScale n_max) ^ 12 := Nat.pow_le_pow_left hL2 12
  have hX_3L : X < 3 * (slabScale n_max) ^ 12 :=
    hX_tl.trans_le totalLocalCoordsWhp_le_three_mul
  have hce_ins : fsIns.curEp = fs.curEp := by cases hasFpCollision <;> rfl
  have hlr_ins : fsIns.liveRole = fs.liveRole := by cases hasFpCollision <;> rfl
  have hor_ins : fsIns.overmarsRole = fs.overmarsRole := by cases hasFpCollision <;> rfl
  have hoa_ins : fsIns.overmarsActive = fs.overmarsActive := by cases hasFpCollision <;> rfl
  have hoc_ins : fsIns.overmarsCursor = fs.overmarsCursor := by cases hasFpCollision <;> rfl
  have hoi_ins : fsIns.overmarsInsCount = fs.overmarsInsCount := by cases hasFpCollision <;> rfl
  have hcnt_ins : fsIns.bktCount b = X + 1 := by
    cases hasFpCollision <;> simp [fsIns, fastInsertFresh, fastInsertAlloc]
  have hq_ins : ∀ i < n_max, fsIns.quotArr i < 2 ^ quotBitsWhp U n_max := by
    intro i _
    have hqa : fsIns.quotArr =
        Function.update fs.quotArr ((fastInsertAlloc n_max b X fs).physSlot n_max b X) q_val := by
      cases hasFpCollision <;> rfl
    rw [hqa]
    by_cases hi : i = (fastInsertAlloc n_max b X fs).physSlot n_max b X
    · subst hi; simp only [Function.update_self]; exact hq_lt
    · rw [Function.update_of_ne hi]; exact (hv.qv_global i).1
  have hbp_ins : ∀ k < fsIns.bktCount b - capFrontWhp n_max,
      fsIns.backPtr b k < poolSizeWhp n_max := by
    rw [hcnt_ins]
    intro k hk
    have hbp_eq : fsIns.backPtr = (fastInsertAlloc n_max b X fs).backPtr := by
      cases hasFpCollision <;> rfl
    rw [hbp_eq]
    by_cases hcf : capFrontWhp n_max ≤ X
    · unfold fastInsertAlloc; dsimp only; rw [ite_eq_left hcf]; dsimp only
      rw [Function.update_self]
      by_cases hk_eq : k = X - capFrontWhp n_max
      · subst hk_eq; rw [Function.update_self]; exact (hcf_fn hcf).2.2
      · rw [Function.update_of_ne hk_eq]; exact (hv.backPtr_valid b hb k (by omega)).1
    · omega
  have hom_idx : fsIns.overmarsSliceIdx b = fs.overmarsSliceIdx b := by
    unfold FastState.overmarsSliceIdx; rw [hor_ins]
  have hom_sl : fsIns.slices (fs.overmarsSliceIdx b) = fs.slices (fs.overmarsSliceIdx b) := by
    cases hasFpCollision with
    | true => rfl
    | false =>
      have hne_role := (hv.roles_valid b hb).2.2
      have hne_idx : fs.overmarsSliceIdx b ≠ fs.liveSliceIdx b := by
        unfold FastState.overmarsSliceIdx FastState.liveSliceIdx; omega
      dsimp only [fsIns, fastInsertFresh, fastInsertAlloc]
      exact Function.update_of_ne hne_idx _ _
  refine ⟨hb, hce_ins ▸ hv.curEp_or, hlr_ins ▸ (hv.roles_valid b hb).1,
    hor_ins ▸ (hv.roles_valid b hb).2.1, by omega, hq_ins, hbp_ins, ?_⟩
  unfold overmarsAfterActivate
  rw [hoa_ins]
  intro ha1
  rcases hv.overmars_valid b hb with ⟨ha0, _⟩ | ⟨ha_act, _, hcur_lt, _, hins_le, omMap0, hv0, _⟩
  · by_cases htrig : 5 * (slabScale n_max) ^ 12 ≤ fsIns.liveInsCount b
    · have hc0 : fs.overmarsActive b = 0 ∧ 5 * (slabScale n_max) ^ 12 ≤ fsIns.liveInsCount b :=
        ⟨ha0, htrig⟩
      rw [ite_eq_left hc0]
      dsimp only [FastState.overmarsSliceIdx]
      simp only [Function.update_self]
      exact ⟨by omega, by omega, ⟨fun _ => none, validWhpSlice_zero _ 0 _⟩⟩
    · have hnc0 : ¬(fs.overmarsActive b = 0 ∧ 5 * (slabScale n_max) ^ 12 ≤ fsIns.liveInsCount b) :=
        fun ⟨_, h⟩ => htrig h
      rw [ite_eq_right hnc0] at ha1; rw [hoa_ins] at ha1; omega
  · have hnc0 : ¬(fs.overmarsActive b = 0 ∧ 5 * (slabScale n_max) ^ 12 ≤ fsIns.liveInsCount b) :=
      by omega
    rw [ite_eq_right hnc0, hoc_ins, hoi_ins, hom_idx, hom_sl]
    exact ⟨by omega, by omega, ⟨omMap0, hv0⟩⟩

/-- Commit fresh insertion and run `overmarsStepGenProg`, returning `1`. -/
@[irreducible] private def insCommitFreshGenProg :
    (((WhpParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × ℕ))) → Memory.Prog ℕ
  | ((((wp, base), (b, X)), (q_val, v_val)), (hasCol, (rKey, (fp, lIdx)))) => do
    fastInsertFreshGenProg
      ((((wp.1, base), (b, X)), (q_val, v_val)), (hasCol, (rKey, (fp, lIdx))))
    overmarsStepGenProg ((wp, base), b)
    pure 1

private theorem realizes_insCommitFreshGen :
    Realizes .exact insCommitFreshGenProg
      (WordEncoding.encode
        (α := (((WhpParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × ℕ)))))
      (WordEncoding.encode (α := ℕ))
      (fun w ((((wp, base), (b, X)), (q_val, v_val)), (hasCol, (_, (fp, lIdx)))) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U)
            (hasFpCollision : Bool),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          b < numBucketsWhp n_max ∧
          X = fs.bktCount b ∧
          X < totalLocalCoordsWhp n_max ∧
          (capFrontWhp n_max ≤ X → 0 < fs.poolFreeTop) ∧
          q_val < 2 ^ quotBitsWhp U n_max ∧
          v_val < V ∧
          hasCol = (if hasFpCollision then 1 else 0) ∧
          lIdx = fs.liveSliceIdx b ∧
          fp < 2 ^ fpBitsWhp n_max)
      (fun _ _ => 0) := by
  unfold insCommitFreshGenProg
  have hfr := realizes_fastInsertFreshGen
  have hom := realizes_overmarsStepGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨wp, base⟩, ⟨b, X⟩⟩, ⟨q_val, v_val⟩⟩, ⟨hasCol, ⟨rKey, ⟨fp, lIdx⟩⟩⟩⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, hasFpCollision, henv, heq_wp, hseed, hrep, hv,
      hb, rfl, hX_tl, hpos_fn, hq_lt, hv_v, rfl, rfl, hfp_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    have hv_pow := val_lt_two_pow_valBits hv_v
    have hcf_fn : capFrontWhp n_max ≤ fs.bktCount b →
        0 < fs.poolFreeTop ∧
        fs.poolFreeTop ≤ poolSizeWhp n_max ∧
        fs.poolFreeStack (fs.poolFreeTop - 1) < poolSizeWhp n_max := fun hcf =>
      ⟨hpos_fn hcf, hv.poolFreeTop_le, hv.freeStack_lt _ (by have := hpos_fn hcf; omega)⟩
    obtain ⟨hia_le, hna_le, curMap, hv_cur, _⟩ := hv.bufCur_valid
    obtain ⟨hna_cap, hia_cap⟩ := bufTrie_caps_of_bounds hth hia_le hna_le
    obtain ⟨liveMap, hv_live, _⟩ := hv.live_valid b hb
    have hlic := liveInsCount_le_eight hv.toCore hb (hv.overmars_valid b hb)
    have hlr_lt := (hv.roles_valid b hb).1
    have hlIdx : fs.liveSliceIdx b < 3 * numBucketsWhp n_max := by
      unfold FastState.liveSliceIdx; omega
    have hcol_t : hasFpCollision = true →
        (fs.buf fs.curEp).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
        (fs.buf fs.curEp).itemAlloc < qEpochWhp n_max ∧
        ∃ cm, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) cm :=
      fun _ => ⟨hna_cap, hia_cap, curMap, hv_cur⟩
    have hcol_f : hasFpCollision = false →
        fs.liveSliceIdx b = fs.liveSliceIdx b ∧
        fs.liveSliceIdx b < 3 * numBucketsWhp n_max ∧
        fp < 2 ^ fpBitsWhp n_max ∧
        fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
        ∃ lm, ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) lm :=
      fun _ => ⟨rfl, hlIdx, hfp_lt, hlic, liveMap, hv_live⟩
    obtain ⟨_, _, hfr_step⟩ :=
      fastInsertFreshGenProg_fastStep hasFpCollision henv hv.curEp_or hb hX_tl hcf_fn
        hq_lt hv_pow hcol_t hcol_f hseed hrep (rKey := rKey) (s := s)
    have hbnds_ins :=
      overmarsBucketStepBounds_insFresh hasFpCollision hv hb hX_tl hcf_fn hq_lt
        (v_val := v_val) (rKey := rKey) (fp := fp)
    rw [hcp_eq] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, hv.curEp_or, hb, hX_tl, hcf_fn,
        hq_lt, hv_pow,
        fun _ => ⟨hna_cap, hia_cap, curMap, hv_cur⟩,
        fun _ => ⟨rfl, hlIdx, hfp_lt, hlic, liveMap, hv_live⟩⟩
    | exact ⟨c, U, V, w, n_max, θ, _, henv, rfl, hfr_step.2.1, hfr_step.2.2.1, hbnds_ins⟩
  )

private theorem insCommitFreshGenProg_spec {c U V w n_max base b q_val v_val rKey fp : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (hasFpCollision : Bool)
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidFastState c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max)
    (hX_tl : fs.bktCount b < totalLocalCoordsWhp n_max)
    (hpos_fn : capFrontWhp n_max ≤ fs.bktCount b → 0 < fs.poolFreeTop)
    (hq_lt : q_val < 2 ^ quotBitsWhp U n_max)
    (hv_v : v_val < V)
    (hfp_lt : fp < 2 ^ fpBitsWhp n_max) :
    let X := fs.bktCount b
    let lIdx := fs.liveSliceIdx b
    let hasCol := if hasFpCollision then 1 else 0
    let prog := insCommitFreshGenProg
      ((((mkWhpParams c U V w n_max, base), (b, X)), (q_val, v_val)),
       (hasCol, (rKey, (fp, lIdx))))
    let s' := (Memory.spec 0).clientState s prog
    let fsIns := fastInsertFresh c n_max b X q_val v_val rKey fp lIdx hasFpCollision
      (fastInsertAlloc n_max b X fs)
    (Memory.spec 0).clientResult s prog = 1 ∧
    memoryCost prog s ≤ 20 * cTabWhp c + 32 * hashEvalCostWhp c + 41788 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (overmarsStep c U n_max θ b fsIns) s s' := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  set cp := mkWhpCoreParams c U V w n_max
  set X := fs.bktCount b
  set lIdx := fs.liveSliceIdx b
  set hasCol := if hasFpCollision then 1 else 0
  have hv_pow := val_lt_two_pow_valBits hv_v
  have hcf_fn : capFrontWhp n_max ≤ X →
      0 < fs.poolFreeTop ∧
      fs.poolFreeTop ≤ poolSizeWhp n_max ∧
      fs.poolFreeStack (fs.poolFreeTop - 1) < poolSizeWhp n_max := fun hcf =>
    ⟨hpos_fn hcf, hv.poolFreeTop_le, hv.freeStack_lt _ (by have := hpos_fn hcf; omega)⟩
  obtain ⟨hia_le, hna_le, curMap, hv_cur, _⟩ := hv.bufCur_valid
  obtain ⟨hna_cap, hia_cap⟩ := bufTrie_caps_of_bounds hth hia_le hna_le
  obtain ⟨liveMap, hv_live, _⟩ := hv.live_valid b hb
  have hlic := liveInsCount_le_eight hv.toCore hb (hv.overmars_valid b hb)
  have hlr_lt := (hv.roles_valid b hb).1
  have hlIdx : lIdx < 3 * numBucketsWhp n_max := by
    dsimp only [lIdx]; unfold FastState.liveSliceIdx; omega
  have hcol_t : hasFpCollision = true →
      (fs.buf fs.curEp).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
      (fs.buf fs.curEp).itemAlloc < qEpochWhp n_max ∧
      ∃ cm, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) cm :=
    fun _ => ⟨hna_cap, hia_cap, curMap, hv_cur⟩
  have hcol_f : hasFpCollision = false →
      lIdx = fs.liveSliceIdx b ∧
      lIdx < 3 * numBucketsWhp n_max ∧
      fp < 2 ^ fpBitsWhp n_max ∧
      fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
      ∃ lm, ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices lIdx) lm :=
    fun _ => ⟨rfl, hlIdx, hfp_lt, hlic, liveMap, hv_live⟩
  obtain ⟨hfr_mc, hfr_vp, hfr_step⟩ :=
    fastInsertFreshGenProg_fastStep hasFpCollision henv hv.curEp_or hb hX_tl hcf_fn
      hq_lt hv_pow hcol_t hcol_f hseed hrep (rKey := rKey) (s := s)
  set s1 := (Memory.spec 0).clientState s
    (fastInsertFreshGenProg
      ((((cp, base), (b, X)), (q_val, v_val)), (hasCol, (rKey, (fp, lIdx)))))
  have hbnds_ins :=
    overmarsBucketStepBounds_insFresh hasFpCollision hv hb hX_tl hcf_fn hq_lt
      (v_val := v_val) (rKey := rKey) (fp := fp)
  obtain ⟨hom_mc, hom_vp, hom_step⟩ :=
    overmarsStepGenProg_fastStep henv hbnds_ins hfr_step.2.1 hfr_step.2.2.1 (s := s1)
  dsimp only
  unfold insCommitFreshGenProg; dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
  have hs'_eq : (Memory.spec 0).clientState s
      (fastInsertFreshGenProg
          ((((cp, base), (b, X)), (q_val, v_val)), (hasCol, (rKey, (fp, lIdx)))) >>= fun _ =>
        overmarsStepGenProg ((mkWhpParams c U V w n_max, base), b) >>= fun _ => pure 1) =
      (Memory.spec 0).clientState s1
        (overmarsStepGenProg ((mkWhpParams c U V w n_max, base), b)) := by
    rw [clientState_bind, clientState_bind, clientState_pure_whp]
  rw [hs'_eq]
  refine ⟨?_, ?_, ?_, hfr_step.trans hom_step⟩
  · rw [clientResult_bind, clientResult_bind, clientResult_pure_whp]
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_pure]
    dsimp only [s1, cp, X, lIdx, hasCol] at hfr_mc hom_mc ⊢; omega
  · exact validProg_bind hfr_vp (validProg_bind hom_vp (validProg_pure _))

/-- Post-`rKey`-guard step: compute `(hasFpCollision, (fp, lIdx))`, check Guard 3, and commit. -/
@[irreducible] private def insAfterRKeyGenProg :
    (((WhpParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog ℕ
  | ((((wp, base), (b, X)), (q_val, v_val)), (u_val, rKey)) => do
    let z1 ← pure 1
    let cfp ← insReadFpLiveGenProg ((wp, base), (b, u_val))
    let ok3 ← insCheckFpCapOptGenProg (((wp.1, base), cfp.1), rKey)
    if ok3 = z1 then
      insCommitFreshGenProg ((((wp, base), (b, X)), (q_val, v_val)), (cfp.1, (rKey, cfp.2)))
    else
      pure 0

private theorem realizes_insAfterRKeyGen :
    Realizes .exact insAfterRKeyGenProg
      (WordEncoding.encode (α := (((WhpParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w ((((wp, base), (b, X)), (q_val, v_val)), (u_val, _)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          u_val < U ∧
          b < numBucketsWhp n_max ∧
          X = fs.bktCount b ∧
          X < totalLocalCoordsWhp n_max ∧
          (capFrontWhp n_max ≤ X → 0 < fs.poolFreeTop) ∧
          q_val < 2 ^ quotBitsWhp U n_max ∧
          v_val < V)
      (fun _ _ => 0) := by
  unfold insAfterRKeyGenProg
  have hrf := realizes_insReadFpLiveGen
  have hck := realizes_insCheckFpCapOptGen
  have hcm := realizes_insCommitFreshGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨wp, base⟩, ⟨b, X⟩⟩, ⟨q_val, v_val⟩⟩, ⟨u_val, rKey⟩⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hv, hu,
      hb, rfl, hX_tl, hpos_fn, hq_lt, hv_v⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    set u : Fin U := ⟨u_val, hu⟩
    obtain ⟨_, _, curMap, hv_cur, _⟩ := hv.bufCur_valid
    obtain ⟨liveMap, hv_live, _⟩ := hv.live_valid b hb
    have hlic := liveInsCount_le_eight hv.toCore hb (hv.overmars_valid b hb)
    have hlr_lt := (hv.roles_valid b hb).1
    obtain ⟨hrf_st, hrf_res, _, _⟩ :=
      insReadFpLiveGenProg_spec u henv hseed hrep hb hlr_lt hlic hv_live (s := s)
    dsimp only [u] at hrf_st hrf_res
    set fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) ⟨u_val, hu⟩
    set hasFpCollision :=
      (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        (fs.slices (fs.liveSliceIdx b)) fp).isSome
    have hfp_lt : fp < 2 ^ fpBitsWhp n_max := by
      dsimp only [fp, fpOfSalt]
      split_ifs with hs
      · exact fpHash_lt c U n_max θ.2 ⟨fs.bktSalt b, hs⟩ ⟨u_val, hu⟩
      · exact Nat.two_pow_pos _
    obtain ⟨hck_st, _, _, _⟩ :=
      insCheckFpCapOptGenProg_spec hasFpCollision henv hv.curEp_or hv_cur hrep (rKey := rKey)
        (s := s)
    simp only [hcp_eq] at *
    simp only [hrf_st, hrf_res, hck_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, θ, fs, liveMap, henv, rfl, hseed, hrep, hb, hlr_lt, hlic, hv_live⟩
    | exact ⟨c, U, V, w, n_max, fs, curMap, henv, rfl, hrep, hv.curEp_or, hv_cur⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, hasFpCollision, henv, rfl, hseed, hrep, hv,
        hb, rfl, hX_tl, hpos_fn, hq_lt, hv_v, rfl, rfl, hfp_lt⟩
  )

/-- Evaluate `fpReducedKeyOpt` from `(wp, base, u_val)`. -/
@[irreducible] private def insEvalRKeyGenProg :
    (WhpParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((wp, base), u_val) => do
    let hrt ← mkHashRtGenProg (wp, base)
    fpReducedKeyOptRtProg (hrt, u_val)

private theorem realizes_insEvalRKeyGen :
    Realizes .exact insEvalRKeyGenProg
      (WordEncoding.encode (α := (WhpParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((wp, base), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem)
      (fun _ _ => 0) := by
  unfold insEvalRKeyGenProg
  have hmh := realizes_mkHashRtGen
  have hrk := realizes_fpReducedKeyOptRt
  realize
  rcases d with ⟨⟨wp, base⟩, u_val⟩
  obtain ⟨c, U, V, w₀, n_max, θ, henv, heq_wp, hseed⟩ := h
  have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
  have hth := henv.2.2.2.1
  obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
    (w := w) (n_max := n_max) (base := base) hth s
  simp only [Prod.mk.eta, hmh_st, hmh_res] at *
  exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩

private theorem insEvalRKeyGenProg_spec {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {s : Memory.State} (u : Fin U)
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem) :
    let prog := insEvalRKeyGenProg ((mkWhpParams c U V w n_max, base), u.val)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = fpReducedKey c U n_max θ.2 u ∧
    memoryCost prog s ≤ 1 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  obtain ⟨hmh_st, hmh_res, hmh_mc, hmh_vp⟩ :=
    mkHashRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base) hth s
  obtain ⟨hrk_st, hrk_res, hrk_mc, hrk_vp⟩ :=
    fpReducedKeyOptRtProg_spec (kv := u.val) henv hseed (s := s)
  have hrk_eq : (if h : u.val < U then fpReducedKey c U n_max θ.2 ⟨u.val, h⟩ else 0) =
      fpReducedKey c U n_max θ.2 u := by simp [u.isLt]
  rw [hrk_eq] at hrk_res
  dsimp only
  unfold insEvalRKeyGenProg
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, hmh_st, hmh_res, hrk_st]
  · rw [clientResult_bind, hmh_st, hmh_res, hrk_res]
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hmh_st, hmh_res, hmh_mc, Nat.zero_add]; exact hrk_mc
  · refine validProg_bind hmh_vp ?_; rw [hmh_st, hmh_res]; exact hrk_vp

/-- Post-cap-guard step: compute `rKey`, check Guard 2, and delegate to `insAfterRKeyGenProg`. -/
@[irreducible] private def insAfterCapGenProg :
    (((WhpParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ → Memory.Prog ℕ
  | ((((wp, base), (b, X)), (q_val, v_val)), u_val) => do
    let z1 ← pure 1
    let rKey ← insEvalRKeyGenProg ((wp, base), u_val)
    let ok2 ← insCheckRKeyGuardsGenProg ((wp.1, base), rKey)
    if ok2 = z1 then
      insAfterRKeyGenProg ((((wp, base), (b, X)), (q_val, v_val)), (u_val, rKey))
    else
      pure 0

private theorem realizes_insAfterCapGen :
    Realizes .exact insAfterCapGenProg
      (WordEncoding.encode (α := (((WhpParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((((wp, base), (b, X)), (q_val, v_val)), u_val) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          u_val < U ∧
          b < numBucketsWhp n_max ∧
          X = fs.bktCount b ∧
          X < totalLocalCoordsWhp n_max ∧
          (capFrontWhp n_max ≤ X → 0 < fs.poolFreeTop) ∧
          q_val < 2 ^ quotBitsWhp U n_max ∧
          v_val < V)
      (fun _ _ => 0) := by
  unfold insAfterCapGenProg
  have her := realizes_insEvalRKeyGen
  have hcg := realizes_insCheckRKeyGuardsGen
  have har := realizes_insAfterRKeyGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨wp, base⟩, ⟨b, X⟩⟩, ⟨q_val, v_val⟩⟩, u_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hv, hu,
      hb, rfl, hX_tl, hpos_fn, hq_lt, hv_v⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    set u : Fin U := ⟨u_val, hu⟩
    obtain ⟨_, _, curMap, hv_cur, _⟩ := hv.bufCur_valid
    have hbo_fn : fs.rebStage ≤ 3 →
        ∃ oldMap, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) oldMap := by
      intro hle3
      have hbo := hv.bufOld_valid; rw [ite_eq_left hle3] at hbo
      obtain ⟨_, _, oldMap, hv_old, _⟩ := hbo; exact ⟨oldMap, hv_old⟩
    obtain ⟨her_st, her_res, _, _⟩ := insEvalRKeyGenProg_spec u henv hseed (s := s)
    dsimp only [u] at her_st her_res
    obtain ⟨hcg_st, _, _, _⟩ :=
      insCheckRKeyGuardsGenProg_spec henv hv.curEp_or hv_cur hbo_fn hrep
        (rKey := fpReducedKey c U n_max θ.2 ⟨u_val, hu⟩) (s := s)
    simp only [hcp_eq] at *
    simp only [her_st, her_res, hcg_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
    | exact ⟨c, U, V, w, n_max, fs, curMap, henv, rfl, hrep, hv.curEp_or, hv_cur, hbo_fn⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv, hu,
        hb, rfl, hX_tl, hpos_fn, hq_lt, hv_v⟩
  )

/-- Miss branch of `fastInsert`: check Guard 1 and delegate to `insAfterCapGenProg`. -/
@[irreducible] private def fastInsertMissGenProg :
    (((WhpParams × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ → Memory.Prog ℕ
  | ((((wp, base), (b, q_val)), u_val), v_val) => do
    let z1 ← pure 1
    let cpRes ← insCheckCapPoolGenProg ((wp.1, base), b)
    if cpRes.1 = z1 then
      insAfterCapGenProg ((((wp, base), (b, cpRes.2)), (q_val, v_val)), u_val)
    else
      pure 0

private theorem realizes_fastInsertMissGen :
    Realizes .exact fastInsertMissGenProg
      (WordEncoding.encode (α := (((WhpParams × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((((wp, base), (b, q_val)), u_val), v_val) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          u_val < U ∧
          b < numBucketsWhp n_max ∧
          q_val < 2 ^ quotBitsWhp U n_max ∧
          v_val < V)
      (fun _ _ => 0) := by
  unfold fastInsertMissGenProg
  have hcp := realizes_insCheckCapPoolGen
  have hac := realizes_insAfterCapGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨wp, base⟩, ⟨b, q_val⟩⟩, u_val⟩, v_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hv, hu,
      hb, hq_lt, hv_v⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hcp_st, hcp_res, _, _⟩ := insCheckCapPoolGenProg_spec henv hb hrep (s := s)
    simp only [hcp_eq] at *
    rw [hcp_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | (rw [wp_large_M hth]; exact hb)
    | (have hhit : ((Memory.spec 0).clientResult s
          (insCheckCapPoolGenProg ((mkWhpCoreParams c U V w n_max, base), b))).1 = 1 := by
          assumption
       rw [hcp_res] at hhit ⊢
       by_cases hbad1 : totalLocalCoordsWhp n_max ≤ fs.bktCount b ∨
           (capFrontWhp n_max ≤ fs.bktCount b ∧ fs.poolFreeTop = 0)
       · rw [ite_eq_left hbad1] at hhit; cases hhit
       · rw [ite_eq_right hbad1]; dsimp only
         exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv, hu, hb,
           rfl, by omega, fun hcf => by omega, hq_lt, hv_v⟩)
  )

private theorem fastInsertMissGenProg_spec {c U V w n_max base b q_val v_val : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State} (u : Fin U)
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidFastState c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max)
    (hq_lt : q_val < 2 ^ quotBitsWhp U n_max)
    (hv_v : v_val < V) :
    let prog := fastInsertMissGenProg
      ((((mkWhpParams c U V w n_max, base), (b, q_val)), u.val), v_val)
    let s' := (Memory.spec 0).clientState s prog
    let X := fs.bktCount b
    let cf := capFrontWhp n_max
    let rKey := fpReducedKey c U n_max θ.2 u
    let fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
    let lIdx := fs.liveSliceIdx b
    let hasFpCollision :=
      (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        (fs.slices lIdx) fp).isSome
    let missOpt : Option FastState :=
      if totalLocalCoordsWhp n_max ≤ X ∨ (cf ≤ X ∧ fs.poolFreeTop = 0) then
        none
      else if (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey).isSome ∨
          (fs.rebStage ≤ 3 ∧
            (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey).isSome) then
        none
      else if hasFpCollision ∧
          !bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey ∧
          2 * sMaxWhp c n_max ≤ (fs.buf fs.curEp).itemAlloc then
        none
      else
        some (overmarsStep c U n_max θ b
          (fastInsertFresh c n_max b X q_val v_val rKey fp lIdx hasFpCollision
        (fastInsertAlloc n_max b X fs)))
    memoryCost prog s ≤ 26 * cTabWhp c + 33 * hashEvalCostWhp c + 42082 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    match missOpt with
    | some fs' =>
      (Memory.spec 0).clientResult s prog = 1 ∧
      FastStateStep base c U V w n_max θ fs' s s'
    | none =>
      (Memory.spec 0).clientResult s prog = 0 ∧ s' = s := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  set cp := mkWhpCoreParams c U V w n_max
  set X := fs.bktCount b
  set cf := capFrontWhp n_max
  set rKey := fpReducedKey c U n_max θ.2 u
  set fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
  set lIdx := fs.liveSliceIdx b
  set hasFpCollision :=
    (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      (fs.slices lIdx) fp).isSome
  obtain ⟨hcp_st, hcp_res, hcp_mc, hcp_vp⟩ :=
    insCheckCapPoolGenProg_spec henv hb hrep (s := s)
  dsimp only
  unfold fastInsertMissGenProg; dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
  simp only [pure_bind]
  by_cases hbad1 : totalLocalCoordsWhp n_max ≤ X ∨ (cf ≤ X ∧ fs.poolFreeTop = 0)
  · rw [ite_eq_left hbad1] at hcp_res ⊢
    dsimp only
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hcp_st, hcp_res]; dsimp only
      simp only [zero_ne_one, ↓reduceIte, memoryCost_pure]
      dsimp only [cp] at hcp_mc ⊢; omega
    · refine validProg_bind hcp_vp ?_; rw [hcp_st, hcp_res]; exact validProg_pure _
    · rw [clientResult_bind, hcp_st, hcp_res]; rfl
    · rw [clientState_bind, hcp_st, hcp_res]; rfl
  · rw [ite_eq_right hbad1] at hcp_res ⊢
    have hX_tl : X < totalLocalCoordsWhp n_max := by omega
    have hpos_fn : cf ≤ X → 0 < fs.poolFreeTop := fun _ => by omega
    obtain ⟨_, _, curMap, hv_cur, _⟩ := hv.bufCur_valid
    have hbo_fn : fs.rebStage ≤ 3 →
        ∃ oldMap, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) oldMap := by
      intro hle3
      have hbo := hv.bufOld_valid; rw [ite_eq_left hle3] at hbo
      obtain ⟨_, _, oldMap, hv_old, _⟩ := hbo; exact ⟨oldMap, hv_old⟩
    obtain ⟨her_st, her_res, her_mc, her_vp⟩ := insEvalRKeyGenProg_spec u henv hseed (s := s)
    obtain ⟨hcg_st, hcg_res, hcg_mc, hcg_vp⟩ :=
      insCheckRKeyGuardsGenProg_spec henv hv.curEp_or hv_cur hbo_fn hrep (rKey := rKey) (s := s)
    set progCap := insAfterCapGenProg
      ((((mkWhpParams c U V w n_max, base), (b, X)), (q_val, v_val)), u.val)
    have hstep1_st : (Memory.spec 0).clientState s
        (insCheckCapPoolGenProg ((cp, base), b) >>= fun cpRes =>
          if cpRes.1 = 1 then
            insAfterCapGenProg
              ((((mkWhpParams c U V w n_max, base), (b, cpRes.2)), (q_val, v_val)), u.val)
          else pure 0) =
        (Memory.spec 0).clientState s progCap := by
      rw [clientState_bind, hcp_st, hcp_res]; rfl
    have hstep1_res : (Memory.spec 0).clientResult s
        (insCheckCapPoolGenProg ((cp, base), b) >>= fun cpRes =>
          if cpRes.1 = 1 then
            insAfterCapGenProg
              ((((mkWhpParams c U V w n_max, base), (b, cpRes.2)), (q_val, v_val)), u.val)
          else pure 0) =
        (Memory.spec 0).clientResult s progCap := by
      rw [clientResult_bind, hcp_st, hcp_res]; rfl
    have hstep1_mc : memoryCost
        (insCheckCapPoolGenProg ((cp, base), b) >>= fun cpRes =>
          if cpRes.1 = 1 then
            insAfterCapGenProg
              ((((mkWhpParams c U V w n_max, base), (b, cpRes.2)), (q_val, v_val)), u.val)
          else pure 0) s =
        memoryCost (insCheckCapPoolGenProg ((cp, base), b)) s + memoryCost progCap s := by
      simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hcp_st, hcp_res]; rfl
    have hstep1_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s progCap →
        ValidProg w (base + largeSpaceWhp c U V w n_max) s
          (insCheckCapPoolGenProg ((cp, base), b) >>= fun cpRes =>
            if cpRes.1 = 1 then
              insAfterCapGenProg
                ((((mkWhpParams c U V w n_max, base), (b, cpRes.2)), (q_val, v_val)), u.val)
            else pure 0) := by
      intro hvp_c; refine validProg_bind hcp_vp ?_; rw [hcp_st, hcp_res]; exact hvp_c
    rw [hstep1_st, hstep1_res, hstep1_mc]
    have hcap_all :
        memoryCost (insCheckCapPoolGenProg ((cp, base), b)) s + memoryCost progCap s ≤
          26 * cTabWhp c + 33 * hashEvalCostWhp c + 42082 ∧
        ValidProg w (base + largeSpaceWhp c U V w n_max) s progCap ∧
        match
          if (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey).isSome ∨
              (fs.rebStage ≤ 3 ∧
                (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey).isSome) then
            none
          else if hasFpCollision ∧
              !bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey ∧
              2 * sMaxWhp c n_max ≤ (fs.buf fs.curEp).itemAlloc then
            none
          else
            some (overmarsStep c U n_max θ b
              (fastInsertFresh c n_max b X q_val v_val rKey fp lIdx hasFpCollision
        (fastInsertAlloc n_max b X fs)))
        with
        | some fs' =>
          (Memory.spec 0).clientResult s progCap = 1 ∧
          FastStateStep base c U V w n_max θ fs' s ((Memory.spec 0).clientState s progCap)
        | none =>
          (Memory.spec 0).clientResult s progCap = 0 ∧
          (Memory.spec 0).clientState s progCap = s := by
      dsimp only [progCap]
      unfold insAfterCapGenProg; dsimp only
      rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
      simp only [pure_bind]
      by_cases hbad2 : (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey).isSome ∨
          (fs.rebStage ≤ 3 ∧
            (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey).isSome)
      · rw [ite_eq_left hbad2] at hcg_res ⊢
        dsimp only
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
          rw [her_st, her_res, hcg_st, hcg_res]
          simp only [zero_ne_one, ↓reduceIte, memoryCost_pure]
          dsimp only [cp, rKey] at hcp_mc her_mc hcg_mc ⊢; omega
        · refine validProg_bind her_vp ?_; rw [her_st, her_res]
          refine validProg_bind hcg_vp ?_; rw [hcg_st, hcg_res]; exact validProg_pure _
        · rw [clientResult_bind, her_st, her_res, clientResult_bind, hcg_st, hcg_res]; rfl
        · rw [clientState_bind, her_st, her_res, clientState_bind, hcg_st, hcg_res]; rfl
      · rw [ite_eq_right hbad2] at hcg_res ⊢
        obtain ⟨liveMap, hv_live, _⟩ := hv.live_valid b hb
        have hlic := liveInsCount_le_eight hv.toCore hb (hv.overmars_valid b hb)
        have hlr_lt := (hv.roles_valid b hb).1
        obtain ⟨hrf_st, hrf_res, hrf_mc, hrf_vp⟩ :=
          insReadFpLiveGenProg_spec u henv hseed hrep hb hlr_lt hlic hv_live (s := s)
        obtain ⟨hck_st, hck_res, hck_mc, hck_vp⟩ :=
          insCheckFpCapOptGenProg_spec hasFpCollision henv hv.curEp_or hv_cur hrep
            (rKey := rKey) (s := s)
        set progRK := insAfterRKeyGenProg
          ((((mkWhpParams c U V w n_max, base), (b, X)), (q_val, v_val)), (u.val, rKey))
        have hstep2_st : (Memory.spec 0).clientState s
            (insEvalRKeyGenProg ((mkWhpParams c U V w n_max, base), u.val) >>= fun rk =>
              insCheckRKeyGuardsGenProg ((cp, base), rk) >>= fun ok2 =>
              if ok2 = 1 then
                insAfterRKeyGenProg
                  ((((mkWhpParams c U V w n_max, base), (b, X)), (q_val, v_val)), (u.val, rk))
              else pure 0) =
            (Memory.spec 0).clientState s progRK := by
          rw [clientState_bind, her_st, her_res, clientState_bind, hcg_st, hcg_res]; rfl
        have hstep2_res : (Memory.spec 0).clientResult s
            (insEvalRKeyGenProg ((mkWhpParams c U V w n_max, base), u.val) >>= fun rk =>
              insCheckRKeyGuardsGenProg ((cp, base), rk) >>= fun ok2 =>
              if ok2 = 1 then
                insAfterRKeyGenProg
                  ((((mkWhpParams c U V w n_max, base), (b, X)), (q_val, v_val)), (u.val, rk))
              else pure 0) =
            (Memory.spec 0).clientResult s progRK := by
          rw [clientResult_bind, her_st, her_res, clientResult_bind, hcg_st, hcg_res]; rfl
        have hstep2_mc : memoryCost
            (insEvalRKeyGenProg ((mkWhpParams c U V w n_max, base), u.val) >>= fun rk =>
              insCheckRKeyGuardsGenProg ((cp, base), rk) >>= fun ok2 =>
              if ok2 = 1 then
                insAfterRKeyGenProg
                  ((((mkWhpParams c U V w n_max, base), (b, X)), (q_val, v_val)), (u.val, rk))
              else pure 0) s =
            memoryCost (insEvalRKeyGenProg ((mkWhpParams c U V w n_max, base), u.val)) s +
            memoryCost (insCheckRKeyGuardsGenProg ((cp, base), rKey)) s +
            memoryCost progRK s := by
          simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
          rw [her_st, her_res, hcg_st, hcg_res]; simp only [↓reduceIte, Nat.add_assoc]; rfl
        have hstep2_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s progRK →
            ValidProg w (base + largeSpaceWhp c U V w n_max) s
              (insEvalRKeyGenProg ((mkWhpParams c U V w n_max, base), u.val) >>= fun rk =>
                insCheckRKeyGuardsGenProg ((cp, base), rk) >>= fun ok2 =>
                if ok2 = 1 then
                  insAfterRKeyGenProg
                    ((((mkWhpParams c U V w n_max, base), (b, X)), (q_val, v_val)), (u.val, rk))
                else pure 0) := by
          intro hvp_r
          refine validProg_bind her_vp ?_; rw [her_st, her_res]
          refine validProg_bind hcg_vp ?_; rw [hcg_st, hcg_res]; exact hvp_r
        rw [hstep2_st, hstep2_res, hstep2_mc]
        have hrk_all :
            memoryCost (insCheckCapPoolGenProg ((cp, base), b)) s +
              (memoryCost (insEvalRKeyGenProg ((mkWhpParams c U V w n_max, base), u.val)) s +
               memoryCost (insCheckRKeyGuardsGenProg ((cp, base), rKey)) s +
               memoryCost progRK s) ≤
              26 * cTabWhp c + 33 * hashEvalCostWhp c + 42082 ∧
            ValidProg w (base + largeSpaceWhp c U V w n_max) s progRK ∧
            match
              if hasFpCollision ∧
                  !bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey ∧
                  2 * sMaxWhp c n_max ≤ (fs.buf fs.curEp).itemAlloc then
                none
              else
                some (overmarsStep c U n_max θ b
                  (fastInsertFresh c n_max b X q_val v_val rKey fp lIdx hasFpCollision
        (fastInsertAlloc n_max b X fs)))
            with
            | some fs' =>
              (Memory.spec 0).clientResult s progRK = 1 ∧
              FastStateStep base c U V w n_max θ fs' s ((Memory.spec 0).clientState s progRK)
            | none =>
              (Memory.spec 0).clientResult s progRK = 0 ∧
              (Memory.spec 0).clientState s progRK = s := by
          dsimp only [progRK]
          unfold insAfterRKeyGenProg; dsimp only
          rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
          simp only [pure_bind]
          by_cases hbad3 : hasFpCollision ∧
              !bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey ∧
              2 * sMaxWhp c n_max ≤ (fs.buf fs.curEp).itemAlloc
          · rw [ite_eq_left hbad3] at hck_res ⊢
            dsimp only
            refine ⟨?_, ?_, ?_, ?_⟩
            · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
              rw [hrf_st, hrf_res]; dsimp only; rw [hck_st, hck_res]
              simp only [zero_ne_one, ↓reduceIte, memoryCost_pure]
              dsimp only [cp, rKey, fp, lIdx, hasFpCollision] at hcp_mc her_mc hcg_mc
              dsimp only [cp, rKey, fp, lIdx, hasFpCollision] at hrf_mc hck_mc ⊢
              omega
            · refine validProg_bind hrf_vp ?_; rw [hrf_st, hrf_res]; dsimp only
              refine validProg_bind hck_vp ?_; rw [hck_st, hck_res]; exact validProg_pure _
            · rw [clientResult_bind, hrf_st, hrf_res]; dsimp only
              rw [clientResult_bind, hck_st, hck_res]; rfl
            · rw [clientState_bind, hrf_st, hrf_res]; dsimp only
              rw [clientState_bind, hck_st, hck_res]; rfl
          · rw [ite_eq_right hbad3] at hck_res ⊢
            dsimp only
            have hfp_lt : fp < 2 ^ fpBitsWhp n_max := by
              dsimp only [fp, fpOfSalt]
              split_ifs with hs
              · exact fpHash_lt c U n_max θ.2 ⟨fs.bktSalt b, hs⟩ u
              · exact Nat.two_pow_pos _
            obtain ⟨hcm_res, hcm_mc, hcm_vp, hcm_step⟩ :=
              insCommitFreshGenProg_spec hasFpCollision henv hseed hrep hv hb hX_tl hpos_fn
                hq_lt hv_v hfp_lt (rKey := rKey) (s := s)
            refine ⟨?_, ?_, ?_, ?_⟩
            · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
              rw [hrf_st, hrf_res]; dsimp only; rw [hck_st, hck_res]; simp only [↓reduceIte]
              dsimp only [cp, X, rKey, fp, lIdx, hasFpCollision] at hcp_mc her_mc hcg_mc
              dsimp only [cp, X, rKey, fp, lIdx, hasFpCollision] at hrf_mc hck_mc hcm_mc ⊢
              omega
            · refine validProg_bind hrf_vp ?_; rw [hrf_st, hrf_res]; dsimp only
              refine validProg_bind hck_vp ?_; rw [hck_st, hck_res]; exact hcm_vp
            · rw [clientResult_bind, hrf_st, hrf_res]; dsimp only
              rw [clientResult_bind, hck_st, hck_res]; exact hcm_res
            · rw [clientState_bind, hrf_st, hrf_res]; dsimp only
              rw [clientState_bind, hck_st, hck_res]; exact hcm_step
        exact ⟨hrk_all.1, hstep2_vp hrk_all.2.1, hrk_all.2.2⟩
    exact ⟨hcap_all.1, hstep1_vp hcap_all.2.1, hcap_all.2.2⟩

/-- Body of `fastInsertGenProg` after Feistel split (`d = ((((wp, base), bq), u_val), v_val)`). -/
@[irreducible] private def fastInsertBodyGenProg :
    (((WhpParams × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ → Memory.Prog ℕ
  | ((((wp, base), bq), u_val), v_val) => do
    let z1 ← pure 1
    let fl ← fastFindLocBqGenProg (((wp, base), bq), u_val)
    if fl.1 = z1 then
      fastInsertOverwriteGenProg (((wp, base), (bq.1, fl.2)), v_val)
    else
      fastInsertMissGenProg ((((wp, base), bq), u_val), v_val)

private theorem realizes_fastInsertBodyGen :
    Realizes .exact fastInsertBodyGenProg
      (WordEncoding.encode (α := (((WhpParams × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((((wp, base), bq), u_val), v_val) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          u_val < U ∧
          v_val < V ∧
          bq = (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u_val,
                keyQuotient (bWhp n_max) u_val))
      (fun _ _ => 0) := by
  unfold fastInsertBodyGenProg
  have hfl := realizes_fastFindLocBqGen
  have hov := realizes_fastInsertOverwriteGen
  have hms := realizes_fastInsertMissGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨wp, base⟩, ⟨b, q_val⟩⟩, u_val⟩, v_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hv, hu, hv_v, hbq⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    rcases Prod.mk.inj hbq with ⟨rfl, rfl⟩
    set u : Fin U := ⟨u_val, hu⟩
    have hb : feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u_val < numBucketsWhp n_max :=
      feistelBucket_lt _ _ _
    have hq_lt : keyQuotient (bWhp n_max) u_val < 2 ^ quotBitsWhp U n_max :=
      keyQuotient_lt_pow_quotBits u
    obtain ⟨hfl_st, hfl_res, _, _⟩ := fastFindLocBqGenProg_spec henv hseed hrep hv u (s := s)
    dsimp only [u] at hfl_st hfl_res
    rw [hfl_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv⟩
    | (rw [hcp_eq, wp_large_M hth]; exact hb)
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv, hu, hb, hq_lt, hv_v⟩
    | (have hspec := hv.fastFindLoc_spec u
       cases hfind : fastFindLoc c U n_max θ fs u with
       | none =>
         have hhit : ((Memory.spec 0).clientResult s
           (fastFindLocBqGenProg (((mkWhpParams c U V w n_max, base),
             (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u_val,
              keyQuotient (bWhp n_max) u_val)), u_val))).1 = 1 := by assumption
         rw [hfind] at hfl_res; rw [hfl_res] at hhit; cases hhit
       | some loc =>
         rw [hfind] at hfl_res hspec
         rw [hfl_res]; dsimp only
         exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv, hb, hspec.1, hv_v⟩)
  )

/-- Fast-mode guarded insertion / overwrite `fastInsertGenProg`
(`d = (((wp, base), u_val), v_val)`), returning `1` when `fastInsert` succeeds (`FastStateStep`)
and `0` without mutating memory when any fast-mode guard fires. -/
@[irreducible] def fastInsertGenProg : ((WhpParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((wp, base), u_val), v_val) => do
    let hrt ← mkHashRtGenProg (wp, base)
    let bq ← feistelSplitRtProg (hrt, u_val)
    fastInsertBodyGenProg ((((wp, base), bq), u_val), v_val)

theorem realizes_fastInsertGen :
    Realizes .exact fastInsertGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (((wp, base), u_val), v_val) s =>
        ValidFastMemPre w wp base s ∧ u_val < wpU wp.1 ∧ v_val < wpV wp.1)
      (fun _ _ => 0) := by
  unfold fastInsertGenProg
  have hmh := realizes_mkHashRtGen
  have hfs := realizes_feistelSplitRt
  have hib := realizes_fastInsertBodyGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, u_val⟩, v_val⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hv⟩, hu_wp, hv_wp⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    have hu : u_val < U := by rw [hcp_eq, wp_large_U hth] at hu_wp; exact hu_wp
    have hv_v : v_val < V := by rw [hcp_eq, wp_large_V hth] at hv_wp; exact hv_wp
    obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    obtain ⟨hfs_st, hfs_res, _, _⟩ :=
      feistelSplitRtProg_spec (u_val := u_val) henv hseed (s := s)
    simp only [hmh_st, hmh_res, hfs_st, hfs_res] at *
    first
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv, hu, hv_v, rfl⟩
  )

theorem fastInsertGenProg_spec {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidFastState c U V n_max θ fs dict)
    (u : Fin U) {v_val : ℕ} (hv_v : v_val < V) :
    let prog := fastInsertGenProg (((mkWhpParams c U V w n_max, base), u.val), v_val)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 30 * cTabWhp c + 35 * hashEvalCostWhp c + 42386 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    match fastInsert c U n_max θ fs u v_val with
    | some fs' =>
      (Memory.spec 0).clientResult s prog = 1 ∧
      FastStateStep base c U V w n_max θ fs' s s'
    | none =>
      (Memory.spec 0).clientResult s prog = 0 ∧ s' = s := by
  have hth := henv.2.2.2.1
  set b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
  set q_val := keyQuotient (bWhp n_max) u.val
  have hb : b < numBucketsWhp n_max := feistelBucket_lt _ _ _
  have hq_lt : q_val < 2 ^ quotBitsWhp U n_max := keyQuotient_lt_pow_quotBits u
  obtain ⟨hmh_st, hmh_res, hmh_mc, hmh_vp⟩ :=
    mkHashRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base) hth s
  obtain ⟨hfs_st, hfs_res, hfs_mc, hfs_vp⟩ :=
    feistelSplitRtProg_spec (u_val := u.val) henv hseed (s := s)
  obtain ⟨hfl_st, hfl_res, hfl_mc, hfl_vp⟩ :=
    fastFindLocBqGenProg_spec henv hseed hrep hv u (s := s)
  have hspec := hv.fastFindLoc_spec u
  dsimp only
  unfold fastInsertGenProg
  set progBody := fastInsertBodyGenProg
    ((((mkWhpParams c U V w n_max, base), (b, q_val)), u.val), v_val)
  have houter_st : (Memory.spec 0).clientState s
      (mkHashRtGenProg (mkWhpParams c U V w n_max, base) >>= fun hrt =>
        feistelSplitRtProg (hrt, u.val) >>= fun bq =>
        fastInsertBodyGenProg ((((mkWhpParams c U V w n_max, base), bq), u.val), v_val)) =
      (Memory.spec 0).clientState s progBody := by
    rw [clientState_bind, hmh_st, hmh_res, clientState_bind, hfs_st, hfs_res]
  have houter_res : (Memory.spec 0).clientResult s
      (mkHashRtGenProg (mkWhpParams c U V w n_max, base) >>= fun hrt =>
        feistelSplitRtProg (hrt, u.val) >>= fun bq =>
        fastInsertBodyGenProg ((((mkWhpParams c U V w n_max, base), bq), u.val), v_val)) =
      (Memory.spec 0).clientResult s progBody := by
    rw [clientResult_bind, hmh_st, hmh_res, clientResult_bind, hfs_st, hfs_res]
  have houter_mc : memoryCost
      (mkHashRtGenProg (mkWhpParams c U V w n_max, base) >>= fun hrt =>
        feistelSplitRtProg (hrt, u.val) >>= fun bq =>
        fastInsertBodyGenProg ((((mkWhpParams c U V w n_max, base), bq), u.val), v_val)) s =
      memoryCost (feistelSplitRtProg (mkHashRt c U w n_max base, u.val)) s +
      memoryCost progBody s := by
    simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hmh_st, hmh_res, hmh_mc, hfs_st, hfs_res, Nat.zero_add]
  have houter_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s progBody →
      ValidProg w (base + largeSpaceWhp c U V w n_max) s
        (mkHashRtGenProg (mkWhpParams c U V w n_max, base) >>= fun hrt =>
          feistelSplitRtProg (hrt, u.val) >>= fun bq =>
          fastInsertBodyGenProg ((((mkWhpParams c U V w n_max, base), bq), u.val), v_val)) := by
    intro hvp_b
    refine validProg_bind hmh_vp ?_; rw [hmh_st, hmh_res]
    refine validProg_bind hfs_vp ?_; rw [hfs_st, hfs_res]; exact hvp_b
  rw [houter_st, houter_res, houter_mc]
  have hfs_mc' : memoryCost (feistelSplitRtProg (mkHashRt c U w n_max base, u.val)) s ≤
      hashEvalCostWhp c := hfs_mc
  have hbody_all :
      memoryCost (feistelSplitRtProg (mkHashRt c U w n_max base, u.val)) s +
        memoryCost progBody s ≤
        30 * cTabWhp c + 35 * hashEvalCostWhp c + 42386 ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s progBody ∧
      match fastInsert c U n_max θ fs u v_val with
      | some fs' =>
        (Memory.spec 0).clientResult s progBody = 1 ∧
        FastStateStep base c U V w n_max θ fs' s ((Memory.spec 0).clientState s progBody)
      | none =>
        (Memory.spec 0).clientResult s progBody = 0 ∧
        (Memory.spec 0).clientState s progBody = s := by
    dsimp only [progBody]
    unfold fastInsertBodyGenProg fastInsert; dsimp only; simp only [pure_bind]
    cases hfind : fastFindLoc c U n_max θ fs u with
    | some loc =>
      rw [hfind] at hfl_res hspec
      dsimp only at hfl_res ⊢
      obtain ⟨hov_res, hov_mc, hov_vp, hov_step⟩ :=
        fastInsertOverwriteGenProg_spec henv hseed hrep hv hb hspec.1 hv_v (v_val := v_val) (s := s)
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hfl_st, hfl_res]; dsimp only; simp only [↓reduceIte]
        dsimp only [b, q_val] at hfl_mc hov_mc ⊢; omega
      · refine validProg_bind hfl_vp ?_; rw [hfl_st, hfl_res]; exact hov_vp
      · rw [clientResult_bind, hfl_st, hfl_res]; exact hov_res
      · rw [clientState_bind, hfl_st, hfl_res]; exact hov_step
    | none =>
      rw [hfind] at hfl_res
      dsimp only at hfl_res ⊢
      obtain ⟨hms_mc, hms_vp, hms_match⟩ :=
        fastInsertMissGenProg_spec u henv hseed hrep hv hb hq_lt hv_v (v_val := v_val) (s := s)
      refine ⟨?_, ?_, ?_⟩
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hfl_st, hfl_res]; dsimp only; simp only [zero_ne_one, ↓reduceIte]
        dsimp only [b, q_val] at hfl_mc hms_mc ⊢; omega
      · refine validProg_bind hfl_vp ?_; rw [hfl_st, hfl_res]; exact hms_vp
      · rw [clientResult_bind, hfl_st, hfl_res, clientState_bind, hfl_st, hfl_res]
        exact hms_match
  exact ⟨hbody_all.1, houter_vp hbody_all.2.1, hbody_all.2.2⟩

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
