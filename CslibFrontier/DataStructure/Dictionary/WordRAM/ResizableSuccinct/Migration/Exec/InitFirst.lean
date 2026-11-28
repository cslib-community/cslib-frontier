/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.Exec.Registers
public import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.Exec.InitFirstSetup
import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.Exec.Resample
import Mathlib.Tactic.Linarith

/-!
# Empty-to-Active First-Epoch Initialization (`initFirstEpochCode`)

Compiles the empty-to-active transition (`n = 0 → n' = 1`, `N₁ = targetCap U 1`) on `insert u v`
into the parameter-free (`¬ReadsWidth`) native `RCode .exact rResize` subroutine
`initFirstEpochCode`, proving its distributional `O(1)` execution bound
`initFirstEpochCode_execRCodeDist`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.initFirstCharge`: parameter-free `O(1)`
  expected amortized instruction charge for `0 → 1` first-epoch creation.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.initFirstEpochCode`: parameter-free
  `RCode .exact rResize` empty-to-active transition (`n = 0 → n' = 1`).

## Main results

* `not_readsWidth_initFirstEpochCode`: `initFirstEpochCode` does not inspect the ambient word width.
* `initFirstEpochCode_execRCodeDist`: distributional `ExecRCodeDist` specification within
  `base + compactedEpochWords U V w (targetCap U 1) 1`, bounding expected instructions plus
  post-step `inEpochPotential` by `initFirstCharge`.
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

/-- Parameter-free $O(1)$ expected amortized instruction charge for `0 → 1` first-epoch creation
(`initFirstEpochCode`). -/
noncomputable def initFirstCharge : ℕ :=
  50000 * migFactor + 10000

private noncomputable def initFirstFinishCleanCode : RCode .exact rResize :=
  .seq (.op (.copy mTmpA mBase)) <|
  .seq (RCode.ofCode (wInitNewMeta.code mFr srcInitNewMeta tmpInitNewMeta))
       (RCode.ofCode (wStreamIns.code mFr srcStreamIns tmpStreamIns))

private noncomputable def initFirstFinishCode : RCode .exact rResize :=
  .seq zeroResampleRegsCode initFirstFinishCleanCode

/-- Empty-to-active epoch transition (`n = 0 → n' = 1`, `N₁ = targetCap U 1`) on `insert u v`:
grows `[base + 8, base + compactedEpochWords U V w N₁ 1)`, writes epoch parameters, samples a
uniform `QuotHashSeed U N₁`, initializes metadata, and inserts `(u, v)` (`¬ReadsWidth`). -/
noncomputable def initFirstEpochCode : RCode .exact rResize :=
  .seq initFirstSetupCode <|
  .seq (resampleHashCode mHashBase (mNewHp ⟨3, by decide⟩) (mNewHp ⟨2, by decide⟩)
        (mNewHp ⟨10, by decide⟩) mCur mIdx mK mOne mRes)
       initFirstFinishCode

private theorem not_readsWidth_initFirstFinishCode : ¬initFirstFinishCode.ReadsWidth := by
  simp [initFirstFinishCode, initFirstFinishCleanCode, RCode.ReadsWidth, Op.ReadsWidth]

/-- `initFirstEpochCode` does not inspect the ambient word width `w` (`¬ReadsWidth`). -/
theorem not_readsWidth_initFirstEpochCode : ¬initFirstEpochCode.ReadsWidth := by
  simp [initFirstEpochCode, RCode.ReadsWidth, not_readsWidth_initFirstSetupCode,
    not_readsWidth_resampleHashCode, not_readsWidth_initFirstFinishCode]

private theorem initFirstFinishCode_exec {U V w base : ℕ} (u : Fin U) (v : ℕ)
    {θ : QuotHashSeed U (targetCap U 1)} {x y_set y_rs : RData rResize}
    (hv_lt : v < V)
    (hfit_peak : Fits w (base + compactedEpochWords U V w (targetCap U 1) 1))
    (hy_set_b : y_set.Bounded w)
    (hy_set_fr : y_set.frontier = base + compactedEpochWords U V w (targetCap U 1) 1)
    (habi_set : abiPreserved x y_set)
    (hbelow_set : ∀ addr < base, y_set.mem addr = x.mem addr)
    (hhdr_set : RootHeaderValid U V w (targetCap U 1) 1 1 base y_set.mem)
    (hpar_set : EpochParamsStored U V w (targetCap U 1) base y_set.mem)
    (hr_base : y_set.regs mBase = base)
    (hr_fr : y_set.regs mFr = base + compactedEpochWords U V w (targetCap U 1) 1)
    (hr_ib : y_set.regs mItemBase = base + offCompItems U w (targetCap U 1))
    (hr_u : x.regs mArgU = u.val)
    (hr_v : x.regs mArgV = v)
    (hr_nhp : ∀ i : Fin 19, y_set.regs (mNewHp i) =
      mkHashParams w (epochQBits U (targetCap U 1)) (epochHashB (targetCap U 1))
        (totalMicroBits (targetCap U 1)) 3 i)
    (hr_ncp : ∀ i : Fin 36, y_set.regs (mNewCp i) = mkCompParams U V w (targetCap U 1) i)
    (hrs_fr : y_rs.frontier = y_set.frontier)
    (hrs_seed : ReducedKWise.SeedRep (base + epochHdrWords) (qBits U (targetCap U 1))
      (hashB (targetCap U 1)) (totalMicroBits (targetCap U 1)) 3 θ y_rs.mem)
    (hrs_mem : ∀ a,
      a < base + epochHdrWords ∨
        base + epochHdrWords +
          ReducedKWise.seedWords (qBits U (targetCap U 1)) (hashB (targetCap U 1))
            (totalMicroBits (targetCap U 1)) 3 ≤ a →
      y_rs.mem a = y_set.mem a)
    (hrs_reg : ∀ reg, reg ∉ ([mCur, mIdx, mK, mOne, mRes] : List (Fin rResize)) →
      y_rs.regs reg = y_set.regs reg) :
    let N₁ := targetCap U 1
    let fr₁ := base + compactedEpochWords U V w N₁ 1
    let z₀ := (((((y_rs.set mCur 0).set mIdx 0).set mK 0).set mOne 0).set mRes 0)
    ∃ (z : RData rResize) (steps_clean : ℕ),
      RDemonicExec w fr₁ initFirstFinishCleanCode z₀ steps_clean (· = z) ∧
      z.Bounded w ∧
      z.frontier = fr₁ ∧
      CompactedSplitRep base (base + offCompItems U w N₁) U V w N₁ 1 1 θ
        (Function.update (Dictionary.empty U) u (some v)) ⟨z.mem, z.frontier⟩ ∧
      abiPreserved x z ∧
      (∀ addr < base, z.mem addr = x.mem addr) ∧
      (5 + steps_clean) + inEpochPotential U w N₁ base z ≤ 46350 * migFactor + 6 := by
  intro N₁ fr₁ z₀
  obtain ⟨hw, hU, hV⟩ := rootHeaderValid_bounds hy_set_b hhdr_set
  obtain ⟨hN₁_pos, _, hN₁_le2, hN₁U⟩ := targetCap_bounds_of_pos (le_rfl : 1 ≤ 1) hhdr_set.pos_U
  set off₁ := offCompItems U w N₁
  set iw₁ := compactedItemWords U V w N₁ 1
  have hfr₁_eq : fr₁ = base + off₁ + iw₁ := by
    simp only [fr₁, compactedEpochWords, Nat.one_ne_zero, ↓reduceIte, off₁, iw₁, Nat.add_assoc]
  have hnm_le_fr₁ : base + off₁ ≤ fr₁ := hfr₁_eq ▸ Nat.le_add_right _ _
  have hfit_off : Fits w (base + off₁) := hfit_peak.of_le hnm_le_fr₁
  obtain ⟨z₁, z₂, hex_c1, hex_im, hc_im, _, hz₂b, hz₂f_eq, hz₂_fr_reg, hz₂_mem_eq,
      hrep_im, htot_im, hpot_im, ⟨s_fix₀, hinv₀, hcpl₀⟩, hkeep_set_2, hz₂_not_im⟩ :=
    exec_postResample_initMeta mBase (by simp)
      hw hU hN₁_pos hN₁U hhdr_set.fits_U hV hy_set_b hy_set_fr hnm_le_fr₁ hfit_off
      hr_base hr_fr hr_nhp hr_ncp hrs_fr hrs_seed hrs_mem hrs_reg
  have hms₂ : memoryState mFr z₂.toData = ⟨z₂.mem, fr₁⟩ := Memory.State.ext rfl hz₂_fr_reg
  let d_si := (((mkHashParams w (qBits U N₁) (hashB N₁) (totalMicroBits N₁) 3,
    mkCompParams U V w N₁), (base, base + off₁)), (u.val, v))
  have hin_si : z₂.regs ∘ srcStreamIns = WordEncoding.encode d_si := by
    refine (regs_pairSrc
      (regs_pairSrc
        (regs_pairSrc
          (regs_hp_eq fun i => (hkeep_set_2 (mNewHp i) (mNewHp_lt_160 i) ?_).trans (hr_nhp i))
          (regs_cp_eq fun i => (hkeep_set_2 (mNewCp i) (mNewCp_lt_160 i) ?_).trans (hr_ncp i)))
        (regs_pairSrc
          (regs_reg1_eq mBase ((hkeep_set_2 mBase (mReg_lt_160 _) (by simp)).trans hr_base))
          (regs_reg1_eq mItemBase ((hkeep_set_2 mItemBase (mReg_lt_160 _) (by simp)).trans
            hr_ib))))
      (regs_pairSrc
        (regs_reg1_eq mArgU ((hkeep_set_2 mArgU (mReg_lt_160 _) (by simp)).trans
          (habi_set.2.2.1.trans hr_u)))
        (regs_reg1_eq mArgV ((hkeep_set_2 mArgV (mReg_lt_160 _) (by simp)).trans
          (habi_set.2.2.2.trans hr_v))))).eq
    all_goals clear * -; simp [Fin.ext_iff]; omega
  have henv_si : CompEpochEnv U V w N₁ base (base + off₁) 1 ⟨z₂.mem, fr₁⟩ :=
    ⟨hw, hN₁_pos, hN₁U, hhdr_set.fits_U, hV, le_rfl,
      by change base + off₁ + iw₁ ≤ fr₁; rw [hfr₁_eq]⟩
  obtain ⟨hpre_si, hvp_si, hc_si, hfr_si, hrep_si, ⟨s_fix₁, hinv₁, hcpl₁⟩, hout_si⟩ :=
    streamInsertFreshGenProg_spec (s₀ := ⟨z₂.mem, fr₁⟩) u.isLt henv_si hfit_off
      hrep_im hinv₀ hcpl₀ (htot_im.symm ▸ hN₁_pos) (htot_im.symm ▸ le_rfl) hv_lt
      (by simp [Dictionary.empty])
  obtain ⟨z, hex_si, hzb, hzf, hm_si, _, hframe_reg_si⟩ :=
    execWitness wStreamIns factor_wStreamIns_le mFr srcStreamIns tmpStreamIns
      tmpStreamIns_inj srcStreamIns_ne_tmp tmpStreamIns_ne_mFr srcStreamIns_ne_mFr
      d_si hz₂b hz₂f_eq.le hin_si (hms₂ ▸ hpre_si)
      (hms₂.symm ▸ hvp_si ⟨hms₂ ▸ wellFormed_memoryState hz₂b.1, Nat.zero_le _⟩)
      (by rw [hms₂, hfr_si]; exact hz₂f_eq.symm.le)
  rw [hms₂] at hm_si hex_si
  have hzf_eq : z.frontier = fr₁ := hzf.trans hz₂f_eq
  have hz_mem_eq : z.mem = ((Memory.spec 0).clientState ⟨z₂.mem, fr₁⟩
      (streamInsertFreshGenProg d_si)).mem :=
    congrArg Memory.State.mem hm_si
  have hs_z_eq : ({ mem := z.mem, frontier := z.frontier } : Memory.State) =
      (Memory.spec 0).clientState ⟨z₂.mem, fr₁⟩ (streamInsertFreshGenProg d_si) :=
    Memory.State.ext hz_mem_eq (hzf_eq.trans hfr_si.symm)
  have hlow_z : ∀ a < base + 63, z.mem a = y_set.mem a := fun a ha => by
    have heh : epochHdrWords = 225 := rfl
    have h0_lm : epochHdrWords ≤ offCompLM U w N₁ := Nat.le_add_right _ _
    have h225_off : 225 ≤ off₁ := le_offCompItems_225 U w N₁
    rw [hz_mem_eq,
      hout_si a (fun h => by linarith only [ha, h.1])
        (fun h => by linarith only [ha, h.1, heh, h0_lm])
        (fun h => by linarith only [ha, h.1, h225_off])]
    exact hz₂_not_im a (fun h => by linarith only [ha, h.1, heh])
  have hhdr_z : RootHeaderValid U V w N₁ 1 1 base z.mem :=
    rootHeaderValid_congr hhdr_set fun a ha => hlow_z a (by linarith only [ha.2])
  have hpar_z : EpochParamsStored U V w N₁ base z.mem :=
    epochParamsStored_congr hpar_set fun a ha => hlow_z a ha.2
  have hcard₁ : (Dictionary.dom (Function.update (Dictionary.empty U) u (some v))).card = 1 := by
    rw [Dictionary.dom_insert, Dictionary.dom_empty]; rfl
  have hvals₁ : Dictionary.ValuesBounded V (Function.update (Dictionary.empty U) u (some v)) :=
    fun k val hk => by
      simp only [Function.update_apply, Dictionary.empty] at hk
      split_ifs at hk
      exact Option.some.inj hk ▸ hv_lt
  have hcpl_z : FixedCoupled base (base + off₁) U V w N₁ s_fix₁ ⟨z.mem, z.frontier⟩ :=
    hs_z_eq ▸ hcpl₁
  have htot_z : totalSlots N₁ (compGmAt base U w N₁ z.mem) = 1 :=
    (congrArg (totalSlots N₁) hcpl_z.gm_eq).trans (hinv₁.htot.trans hcard₁)
  have habi_set_z : abiPreserved y_set z := abiPreserved_of_lt_five fun reg h5 hfr =>
    (hframe_reg_si reg hfr (mkTmp_ne_reg _ (by omega) (fun a => Fin.elim0 a))).trans <|
      hkeep_set_2 reg (by omega) (by simp [Fin.ext_iff] at hfr ⊢; omega)
  have hf1 := one_le_migFactor
  have hpot_le : inEpochPotential U w N₁ base z ≤
      (98 * migFactor) * slotPotential N₁ (compGmAt base U w N₁ z.mem) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 98 inEpochFactor_le_migFactor)
  have hsi_pot : migFactor * (memoryCost (streamInsertFreshGenProg d_si) ⟨z₂.mem, fr₁⟩ + 1) +
      inEpochPotential U w N₁ base z ≤ 45361 * migFactor := by
    dsimp only at hc_si
    rw [hpot_im, Nat.mul_zero, Nat.zero_add] at hc_si
    have hmul := Nat.mul_le_mul_left migFactor (Nat.add_le_add_right hc_si 1)
    rw [← hz_mem_eq] at hmul
    nlinarith only [hmul, hpot_le, hf1]
  refine ⟨z, _, hex_c1.seq_eq
      ((hex_im.mono (Nat.mul_le_mul_left migFactor (by linarith only [hc_im, hN₁_le2] : _ ≤ 988))
        (fun _ h => h)).seq_eq hex_si),
    hzb, hzf_eq, ⟨hhdr_z, hpar_z, hz_mem_eq ▸ hrep_si, hcard₁, hvals₁, s_fix₁, hinv₁, htot_z,
      hcpl_z⟩, abiPreserved_trans habi_set habi_set_z,
    fun addr haddr => (hlow_z addr (by linarith only [haddr])).trans (hbelow_set addr haddr),
    by linarith only [hsi_pot]⟩

/-- **Distributional `0 → 1` Epoch Creation (`initFirstEpochCode_execRCodeDist`):**
From the 8-word empty dictionary state (`n = 0`, `N = 0`) at `base`, `initFirstEpochCode` creates
the first active epoch `(N₁, 1, 1)` (`N₁ = targetCap U 1`) containing `(u, v)` under a fresh
uniform `QuotHashSeed U N₁`, never exceeding `base + compactedEpochWords U V w N₁ 1` and bounding
expected instructions plus post-step `inEpochPotential` by `initFirstCharge`. -/
theorem initFirstEpochCode_execRCodeDist {U V w base : ℕ} (u : Fin U) (v : ℕ) {x : RData rResize}
    (hx : x.Bounded w)
    (hfr : x.frontier = base + 8)
    (hhdr : RootHeaderValid U V w 0 0 0 base x.mem)
    (hv_lt : v < V)
    (hfit_peak : Fits w (base + compactedEpochWords U V w (targetCap U 1) 1))
    (hbase : x.regs mBase = base)
    (hu_reg : x.regs mArgU = u.val)
    (hv_reg : x.regs mArgV = v) :
    let N₁ := targetCap U 1
    let fr₁ := base + compactedEpochWords U V w N₁ 1
    ∃ (zOf : QuotHashSeed U N₁ → RData rResize) (T_init : ℝ≥0∞),
      ExecRCodeDist w initFirstEpochCode x
        ((PMF.uniformOfFintype (QuotHashSeed U N₁)).map zOf) T_init fr₁ ∧
      (∀ θ,
        (zOf θ).Bounded w ∧
        (zOf θ).frontier = fr₁ ∧
        CompactedSplitRep base (base + offCompItems U w N₁) U V w N₁ 1 1 θ
          (Function.update (Dictionary.empty U) u (some v))
          ⟨(zOf θ).mem, (zOf θ).frontier⟩ ∧
        (zOf θ).regs mBase = base ∧
        (∀ addr < base, (zOf θ).mem addr = x.mem addr)) ∧
      T_init + (∑' θ, (PMF.uniformOfFintype (QuotHashSeed U N₁)) θ *
          (inEpochPotential U w N₁ base (zOf θ) : ℝ≥0∞)) ≤
        (initFirstCharge : ℝ≥0∞) := by
  intro N₁ fr₁
  obtain ⟨hw, hU, _⟩ := rootHeaderValid_bounds hx hhdr
  obtain ⟨_, _, _, hN₁U⟩ := targetCap_bounds_of_pos (le_rfl : 1 ≤ 1) hhdr.pos_U
  obtain ⟨y_set, steps_set, hex_set, hc_set, hy_set_b, hy_set_fr, habi_set, hbelow_set,
      hhdr_set, hpar_set, hr_base, hr_fr, hr_ib, hr_hb, hr_nhp, hr_ncp⟩ :=
    initFirstSetupCode_exec hx hfr hhdr hfit_peak hbase
  have hnm_le : base + offCompItems U w N₁ ≤ fr₁ := by
    simp only [fr₁, compactedEpochWords, Nat.one_ne_zero, ↓reduceIte]; omega
  obtain ⟨zOf, T_init, hex_full, hpost, hcost⟩ :=
    exec_setup_resample_finish (metaBase := base) (base := base)
      (finBound := 46350 * migFactor + 6)
      (finishCleanCode := initFirstFinishCleanCode)
      (P := fun θ z =>
        z.Bounded w ∧
        z.frontier = fr₁ ∧
        CompactedSplitRep base (base + offCompItems U w N₁) U V w N₁ 1 1 θ
          (Function.update (Dictionary.empty U) u (some v))
          ⟨z.mem, z.frontier⟩ ∧
        z.regs mBase = base ∧
        (∀ addr < base, z.mem addr = x.mem addr))
      hw hU hN₁U hex_set hy_set_b hy_set_fr (hfit_peak.of_le hnm_le) hnm_le hr_hb hr_nhp
      (fun θ y_rs hfr_y hseed_y hmem_y hreg_y => by
        obtain ⟨z, stepsClean, hex_cl, hzb, hzf, hsp, habi, hbel, hbd⟩ :=
          initFirstFinishCode_exec u v hv_lt hfit_peak hy_set_b hy_set_fr habi_set hbelow_set
            hhdr_set hpar_set hr_base hr_fr hr_ib hu_reg hv_reg hr_nhp hr_ncp
            hfr_y hseed_y hmem_y hreg_y
        exact ⟨z, stepsClean, hex_cl, ⟨hzb, hzf, hsp, habi.1.trans hbase, hbel⟩, hbd⟩)
  refine ⟨zOf, T_init, hex_full, hpost, hcost.trans ((Nat.cast_le (α := ℝ≥0∞)).mpr ?_)⟩
  unfold initFirstCharge
  linarith only [hc_set, one_le_migFactor]

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
