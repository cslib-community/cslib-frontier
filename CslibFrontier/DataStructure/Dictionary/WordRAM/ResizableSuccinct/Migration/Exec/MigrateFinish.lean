/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.Exec.MigrateCompactBack
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.Exec.Resample
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Post-Resample Streaming Rebuild and Compaction (`migrateFinishCode`)

Internal deterministic finish half of `migrateActiveCode` after `resampleHashCode`: clears resample
scratch registers, initializes the new epoch's tables/metadata at `mNewMeta`, streams all `n`
entries from the right-aligned old item suffix (`streamAllItemsProg`), and compacts back to `base`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.Dynamic
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise
open Cslib.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise
open Cslib.Probability
open scoped BigOperators ENNReal

/-- First half of `migrateFinishCleanCode`: initializes new-epoch table/metadata and streams all
`n` entries from the right-aligned old item suffix into `(mNewMeta, mArena)`. -/
private noncomputable def migrateStreamBuildCode : RCode .exact rResize :=
  .seq (.op (.copy mTmpA mNewMeta)) <|
  .seq (RCode.ofCode (wInitNewMeta.code mFr srcInitNewMeta tmpInitNewMeta)) <|
  .seq (.op (.const mZero 0))
       (RCode.ofCode (wStreamAll.code mFr srcStreamAll tmpStreamAll))

/-- Deterministic finish body after `zeroResampleRegsCode`. -/
noncomputable def migrateFinishCleanCode : RCode .exact rResize :=
  .seq migrateStreamBuildCode migrateCompactBackCode

/-- Deterministic finish half of `migrateActiveCode` after `resampleHashCode`. -/
@[expose] noncomputable def migrateFinishCode : RCode .exact rResize :=
  .seq zeroResampleRegsCode migrateFinishCleanCode

theorem not_readsWidth_migrateFinishCode : ¬migrateFinishCode.ReadsWidth := by
  simp [migrateFinishCode, migrateFinishCleanCode, migrateStreamBuildCode,
    RCode.ReadsWidth, Op.ReadsWidth, not_readsWidth_migrateCompactBackCode]

theorem migrateFinishCode_exec {U V w N_old n base : ℕ}
    {θ_old : QuotHashSeed U N_old} {θ_new : QuotHashSeed U (targetCap U n)}
    {s_abs : Dictionary.State U} {x y_set y_rs : RData rResize}
    (hn : 1 ≤ n) (hev : EpochValid U n N_old)
    (hcard : (Dictionary.dom s_abs).card = n)
    (hvals : Dictionary.ValuesBounded V s_abs)
    (hfit_peak : Fits w (base + migratePeakWords U V w N_old n))
    (hy_set_b : y_set.Bounded w)
    (hy_set_fr : y_set.frontier = base + migratePeakWords U V w N_old n)
    (habi_set : abiPreserved x y_set)
    (hbelow_set : ∀ addr < base, y_set.mem addr = x.mem addr)
    (hhdr_set : RootHeaderValid U V w (targetCap U n) n n (base + offCompItems U w N_old)
      y_set.mem)
    (hpar_set : EpochParamsStored U V w (targetCap U n) (base + offCompItems U w N_old) y_set.mem)
    (hrep_old : ReducedKWise.Rep (base + epochHdrWords) w (qBits U N_old) (hashB N_old)
      (totalMicroBits N_old) 3 θ_old y_set.mem)
    (hcpl_old : ∃ s_fix_old : Memory.State,
      DictStateInv U V (ghostW w) N_old 0 θ_old s_abs s_fix_old ∧
      totalSlots N_old (compGmAt base U w N_old y_set.mem) = n ∧
      FixedCoupled base
        ((base + offCompItems U w N_old + offCompItems U w (targetCap U n)) +
          (migrateArenaWords U V w N_old (targetCap U n) n - compactedItemWords U V w N_old n))
        U V w N_old s_fix_old ⟨y_set.mem, y_set.frontier⟩)
    (hr_base : y_set.regs mBase = base)
    (hr_cnt : y_set.regs mCnt = n)
    (hr_fr : y_set.regs mFr = base + migratePeakWords U V w N_old n)
    (hr_nm : y_set.regs mNewMeta = base + offCompItems U w N_old)
    (hr_off : y_set.regs mOffNew = offCompItems U w (targetCap U n))
    (hr_iwn : y_set.regs mIwNew = compactedItemWords U V w (targetCap U n) n)
    (hr_ar : y_set.regs mArena = base + offCompItems U w N_old + offCompItems U w (targetCap U n))
    (hr_pf : y_set.regs mPeakFront = base + migratePeakWords U V w N_old n)
    (hr_oid : y_set.regs mOldItemDst =
      (base + offCompItems U w N_old + offCompItems U w (targetCap U n)) +
        (migrateArenaWords U V w N_old (targetCap U n) n - compactedItemWords U V w N_old n))
    (hr_ohp : ∀ i : Fin 19, y_set.regs (mOldHp i) =
      mkHashParams w (epochQBits U N_old) (epochHashB N_old) (totalMicroBits N_old) 3 i)
    (hr_ocp : ∀ i : Fin 36, y_set.regs (mOldCp i) = mkCompParams U V w N_old i)
    (hr_nhp : ∀ i : Fin 19, y_set.regs (mNewHp i) =
      mkHashParams w (epochQBits U (targetCap U n)) (epochHashB (targetCap U n))
        (totalMicroBits (targetCap U n)) 3 i)
    (hr_ncp : ∀ i : Fin 36, y_set.regs (mNewCp i) = mkCompParams U V w (targetCap U n) i)
    (hrs_fr : y_rs.frontier = y_set.frontier)
    (hrs_seed : ReducedKWise.SeedRep (base + offCompItems U w N_old + epochHdrWords)
      (qBits U (targetCap U n)) (hashB (targetCap U n)) (totalMicroBits (targetCap U n)) 3
      θ_new y_rs.mem)
    (hrs_mem : ∀ a,
      (a < base + offCompItems U w N_old + epochHdrWords ∨
        base + offCompItems U w N_old + epochHdrWords +
          ReducedKWise.seedWords (qBits U (targetCap U n)) (hashB (targetCap U n))
            (totalMicroBits (targetCap U n)) 3 ≤ a) →
      y_rs.mem a = y_set.mem a)
    (hrs_reg : ∀ j, j ∉ ([mCur, mIdx, mK, mOne, mRes] : List (Fin rResize)) →
      y_rs.regs j = y_set.regs j) :
    let N_new := targetCap U n
    let peakF := base + migratePeakWords U V w N_old n
    ∃ (z : RData rResize) (steps_clean : ℕ),
      RDemonicExec w peakF migrateFinishCleanCode
        (((((y_rs.set mCur 0).set mIdx 0).set mK 0).set mOne 0).set mRes 0)
        steps_clean (· = z) ∧
      z.Bounded w ∧
      z.frontier = base + compactedEpochWords U V w N_new n ∧
      CompactedSplitRep base (base + offCompItems U w N_new) U V w N_new n n θ_new s_abs
        ⟨z.mem, z.frontier⟩ ∧
      abiPreserved x z ∧
      (∀ addr < base, z.mem addr = x.mem addr) ∧
      (5 + steps_clean) + inEpochPotential U w N_new base z ≤
        (93500 * migFactor + 10000) * n := by
  intro N_new peakF
  obtain ⟨hw, hU, hV⟩ := rootHeaderValid_bounds hy_set_b hhdr_set
  have ⟨hNU_old, hn_old⟩ : N_old ≤ U ∧ n ≤ N_old := by
    rcases hev with ⟨rfl, _⟩ | ⟨_, _, _, _⟩ <;> omega
  have hnU : n ≤ U := hn_old.trans hNU_old
  obtain ⟨hN_new_pos, hn_new, hN_new_2n, hNU_new⟩ := targetCap_bounds_of_pos hn hnU
  set newMeta := base + offCompItems U w N_old
  set offNew := offCompItems U w N_new
  set iwOld := compactedItemWords U V w N_old n
  set iwNew := compactedItemWords U V w N_new n
  set arenaW := migrateArenaWords U V w N_old N_new n
  set arenaB := newMeta + offNew
  set oldItemDst := arenaB + (arenaW - iwOld)
  have hpeak_raw : base + migratePeakWords U V w N_old n = arenaB + arenaW := by
    dsimp only [migratePeakWords, arenaB, arenaW, newMeta, offNew, N_new, iwOld, iwNew]; ring
  have hfit_ar : Fits w (arenaB + arenaW) := hpeak_raw ▸ hfit_peak
  have hfit_nm : Fits w (newMeta + offNew) := hfit_ar.of_le (Nat.le_add_right _ _)
  obtain ⟨z₁, z₂, hex_c1, hex_im, hc_im, hfr_im, hz₂b, hz₂f_eq, hz₂_fr_reg, hz₂_mem_eq,
      hrep_new_im, _, hpot_im, h_empty_im, hkeep_set_2, hz₂_not_im⟩ :=
    exec_postResample_initMeta mNewMeta (by simp)
      hw hU hN_new_pos hNU_new hhdr_set.fits_U hV hy_set_b hy_set_fr
      ((Nat.le_add_right _ _).trans hpeak_raw.symm.le) hfit_nm
      hr_nm hr_fr hr_nhp hr_ncp hrs_fr hrs_seed hrs_mem hrs_reg
  set z₃ := z₂.set mZero 0
  have hex_z3 := RDemonicExec.const (B := .exact) (d := mZero) (v := 0) (x := z₂) hz₂f_eq.le
    (fits_zero w)
  have hz₃b : z₃.Bounded w := hz₂b.set (fits_zero w)
  have hms₃ : memoryState mFr z₃.toData = ⟨z₂.mem, peakF⟩ := Memory.State.ext rfl
    (by simp [memoryState, z₃, RData.set, RData.toData, hz₂_fr_reg, peakF])
  have hreg3 {reg : Fin rResize} (h160 : reg.val < 160)
      (hnot : reg ∉ ([mFr, mTmpA, mZero, mCur, mIdx, mK, mOne, mRes] : List (Fin rResize)) := by
        simp) : z₃.regs reg = y_set.regs reg := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot
    rw [← hkeep_set_2 reg h160 (by simp [hnot])]
    exact Function.update_of_ne hnot.2.2.1 _ _
  have hk3 {reg : Fin rResize} (h : 13 ≤ reg.val ∧ reg.val < 156) :
      z₃.regs reg = y_set.regs reg :=
    hreg3 (h.2.trans (Nat.lt_add_of_pos_right (Nat.succ_pos 3))) <| by
      simp [Fin.ext_iff]
      omega
  let d_sa := (((((mkHashParams w (qBits U N_old) (hashB N_old) (totalMicroBits N_old) 3,
      mkCompParams U V w N_old), (base, oldItemDst)),
    ((mkHashParams w (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3,
      mkCompParams U V w N_new), (newMeta, arenaB))), 0), n)
  have hin_sa : z₃.regs ∘ srcStreamAll = WordEncoding.encode d_sa := by
    refine (regs_pairSrc
      (regs_pairSrc
        (regs_pairSrc
          (regs_pairSrc
            (regs_pairSrc (regs_hp_eq fun i => ?_) (regs_cp_eq fun i => ?_))
            (regs_pairSrc (regs_reg1_eq mBase ((hreg3 (mReg_lt_160 _)).trans hr_base))
              (regs_reg1_eq mOldItemDst ((hreg3 (mReg_lt_160 _)).trans hr_oid))))
          (regs_pairSrc
            (regs_pairSrc (regs_hp_eq fun i => ?_) (regs_cp_eq fun i => ?_))
            (regs_pairSrc (regs_reg1_eq mNewMeta ((hreg3 (mReg_lt_160 _)).trans hr_nm))
              (regs_reg1_eq mArena ((hreg3 (mReg_lt_160 _)).trans hr_ar)))))
        (regs_reg1_eq mZero (by simp [z₃, RData.set])))
      (regs_reg1_eq mCnt ((hreg3 (mReg_lt_160 _)).trans hr_cnt))).eq
    · exact (hk3 (by simp only [val_mOldHp]; omega)).trans (hr_ohp i)
    · exact (hk3 (by simp only [val_mOldCp]; omega)).trans (hr_ocp i)
    · exact (hk3 (by simp only [val_mNewHp]; omega)).trans (hr_nhp i)
    · exact (hk3 (by simp only [val_mNewCp]; omega)).trans (hr_ncp i)
  have heh_val : epochHdrWords = 225 := rfl
  obtain ⟨s_fix_old, hinv_old, htot_old, hcpl_old_set⟩ := hcpl_old
  have hsp_le_old : 225 + ReducedKWise.space w (qBits U N_old) (hashB N_old)
      (totalMicroBits N_old) 3 ≤ offCompItems U w N_old := by
    unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM
    dsimp only [epochHdrWords, epochHashSpace, epochQBits, epochHashB, qBits, hashB]; omega
  have hz₂_below {a : ℕ} (ha : a < base + offCompItems U w N_old + 225) : z₂.mem a = y_set.mem a :=
    hz₂_not_im a (fun h => absurd ha (not_lt.mpr h.1))
  have hsw_old : ReducedKWise.seedWords (qBits U N_old) (hashB N_old) (totalMicroBits N_old) 3 ≤
      ReducedKWise.space w (qBits U N_old) (hashB N_old) (totalMicroBits N_old) 3 :=
    Nat.le_add_right _ _
  have hrep_old_z₂ : ReducedKWise.Rep (base + epochHdrWords) w (qBits U N_old) (hashB N_old)
      (totalMicroBits N_old) 3 θ_old z₂.mem :=
    ⟨ReducedKWise.tableRep_congr hrep_old.1 (fun _ _ h2 =>
       (hz₂_below (by linarith only [h2, hsp_le_old, heh_val])).symm),
     ReducedKWise.seedRep_congr (w := w) hrep_old.2 (fun _ _ h2 =>
       (hz₂_below (by linarith only [h2, hsw_old, hsp_le_old, heh_val])).symm)⟩
  obtain ⟨hcpl_old_z₂, hgm_old_z₂⟩ := fixedCoupled_of_shift (s₀ := ⟨y_set.mem, y_set.frontier⟩)
    (s₁ := ⟨z₂.mem, peakF⟩) (dstItemBase := oldItemDst) hw hcpl_old_set htot_old
    (fun _ ha => hz₂_below (Nat.lt_of_lt_of_le ha.2 (Nat.le_add_right _ _)))
    (fun j _ => hz₂_not_im (oldItemDst + j) (fun h => by
      dsimp only [oldItemDst, arenaB] at h; linarith only [h.2]))
  have henv_sa : StreamRebuildEnv U V w N_old N_new n base newMeta arenaB θ_old θ_new s_abs
      ⟨z₂.mem, peakF⟩ :=
    ⟨hw, hn, hn_old, hNU_old, hn_new, hNU_new, hhdr_set.fits_U, hV, hvals,
      le_rfl, le_rfl, hpeak_raw.ge, hfit_nm, hrep_old_z₂,
      ⟨s_fix_old, hinv_old, (congrArg (totalSlots N_old) hgm_old_z₂).trans htot_old, hcpl_old_z₂⟩,
      hrep_new_im,
      hpot_im,
      h_empty_im⟩
  obtain ⟨hpre_sa, hvp_sa, hc_sa, hfr_sa, hrep_sa, _, hcpl_sa, hlo_sa, hmid_sa⟩ :=
    streamAllItemsProg_spec henv_sa
  have hv_sa : (Memory.spec w).ValidHistory (memoryState mFr z₃.toData)
      ((Memory.spec w).clientHistory (memoryState mFr z₃.toData) (streamAllItemsProg d_sa)) :=
    hms₃ ▸ hvp_sa ⟨hms₃ ▸ wellFormed_memoryState hz₃b.1, Nat.zero_le _⟩
  obtain ⟨z₄, hex_sa, hz₄b, hz₄f, hm_sa, _, hframe_reg_sa⟩ :=
    execWitness wStreamAll factor_wStreamAll_le mFr srcStreamAll tmpStreamAll
      tmpStreamAll_inj srcStreamAll_ne_tmp tmpStreamAll_ne_mFr srcStreamAll_ne_mFr
      d_sa hz₃b hz₂f_eq.le hin_sa (hms₃ ▸ hpre_sa) hv_sa
      (by rw [hms₃, hfr_sa]; exact hz₂f_eq.symm.le)
  rw [hms₃] at hm_sa hex_sa
  have hz₄_mem_eq : z₄.mem = ((Memory.spec 0).clientState ⟨z₂.mem, peakF⟩
      (streamAllItemsProg d_sa)).mem :=
    congrArg Memory.State.mem hm_sa
  have hz₄_set {reg : Fin rResize} (h160 : reg.val < 160)
      (hnot : reg ∉ ([mFr, mTmpA, mZero, mCur, mIdx, mK, mOne, mRes] : List (Fin rResize)) := by
        simp) : z₄.regs reg = y_set.regs reg :=
    (hframe_reg_sa reg (fun h => hnot (by simp [h]))
      (mkTmp_ne_reg _ h160 fun a => by
        fin_cases a
        exact fun h => hnot (by simp [← h]))).trans (hreg3 h160 hnot)
  have hlow_z₄ : ∀ a, newMeta ≤ a ∧ a < newMeta + 63 → z₄.mem a = y_set.mem a := fun a ha => by
    rw [hz₄_mem_eq, hmid_sa a ha]
    exact hz₂_not_im a (fun h => by linarith only [ha.2, h.1, heh_val])
  have hhdr_z₄ : RootHeaderValid U V w N_new n n newMeta z₄.mem :=
    rootHeaderValid_congr hhdr_set fun a ha => hlow_z₄ a ⟨ha.1, by linarith only [ha.2]⟩
  have hpar_z₄ : EpochParamsStored U V w N_new newMeta z₄.mem :=
    epochParamsStored_congr hpar_set hlow_z₄
  have hs_z₄_eq : ({ mem := z₄.mem, frontier := peakF } : Memory.State) = _ :=
    Memory.State.ext hz₄_mem_eq hfr_sa.symm
  obtain ⟨z, steps_back, hex_back, hc_back, hzb, hzf, hsplit_z, hgm_z, habi_4z, hbelow_4z⟩ :=
    migrateCompactBackCode_exec hw hn hev hNU_new hN_new_2n hcard hvals hfit_peak hpeak_raw
      hz₄b (hz₄f.trans hz₂f_eq) ((congrArg Memory.State.frontier hm_sa).trans hfr_sa)
      ((hz₄_set (mReg_lt_160 _)).trans hr_nm) ((hz₄_set (mReg_lt_160 _)).trans hr_base)
      ((hz₄_set (mReg_lt_160 _)).trans hr_off) ((hz₄_set (mReg_lt_160 _)).trans hr_ar)
      ((hz₄_set (mReg_lt_160 _)).trans hr_iwn) ((hz₄_set (mReg_lt_160 _)).trans hr_pf)
      hhdr_z₄ hpar_z₄ (hz₄_mem_eq ▸ hrep_sa)
      (hcpl_sa.imp fun _ ⟨hi', hc'⟩ => ⟨hi', hs_z₄_eq ▸ hc'⟩)
  have habi_set_4 : abiPreserved y_set z₄ := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> exact hz₄_set (mReg_lt_160 _)
  have hc_im_mul := Nat.mul_le_mul_left migFactor
    ((Nat.add_le_add_right hc_im 1).trans (by linarith only [hN_new_2n] : _ ≤ 512 * n + 476))
  have hpot_le : inEpochPotential U w N_new base z ≤
      (98 * migFactor) * slotPotential N_new (compGmAt newMeta U w N_new z₄.mem) := by
    rw [inEpochPotential, hgm_z]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 98 inEpochFactor_le_migFactor)
  have hsa_pot : migFactor * (memoryCost (streamAllItemsProg d_sa) ⟨z₂.mem, peakF⟩ + 1) +
      inEpochPotential U w N_new base z ≤ (90540 * migFactor) * n + migFactor := by
    linarith only [hz₄_mem_eq ▸ Nat.mul_le_mul_left migFactor hc_sa, hpot_le]
  have hex_clean :=
    (hex_c1.seq_eq ((hex_im.mono hc_im_mul fun _ h => h).seq_eq (hex_z3.seq_eq hex_sa))).seq_eq
      hex_back
  refine ⟨z, _, hex_clean, hzb, hzf, hsplit_z,
    abiPreserved_trans habi_set (abiPreserved_trans habi_set_4 habi_4z),
    fun addr haddr => ?_, by nlinarith only [hsa_pot, hc_back, hn, one_le_migFactor]⟩
  exact (hbelow_4z addr haddr).trans <| (congrFun hz₄_mem_eq addr).trans <|
    (hlo_sa addr (by linarith only [haddr])).trans <|
    (hz₂_below (by linarith only [haddr])).trans <| hbelow_set addr haddr


end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
