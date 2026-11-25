/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.Exec.Registers
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.ParamsCompute
public import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.Exec.MigrateFinish
import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.Exec.MigrateSetupParams
import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.Exec.MigrateSetupShift

/-!
# Single-Tape `1 · OPT` Active Epoch Migration (`migrateActiveCode`)

Assembles `migrateSetupParamsCode`, `migrateSetupShiftCode`, `resampleHashCode`, and
`migrateFinishCode` into the parameter-free (`¬ReadsWidth`) native `RCode .exact rResize`
single-tape `1 · OPT` streaming rebuild `migrateActiveCode`, proving its distributional execution
and expected potential-amortized instruction bound `migrateActiveCode_execRCodeDist`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.migrateActiveCode`: parameter-free
  `RCode .exact rResize` single-tape `1 · OPT` streaming rebuild from `(N_old, n, n_init_old)` to
  `(targetCap U n, n, n)`.

## Main results

* `not_readsWidth_migrateActiveCode`: `migrateActiveCode` does not inspect the ambient word width.
* `migrateActiveCode_execRCodeDist`: distributional `ExecRCodeDist` specification within hardware
  frontier `base + migratePeakWords U V w N_old n`
  (`≤ base + Dynamic.succinctWords 2699 888 U V w n`), bounding expected instructions plus
  post-migration `inEpochPotential` by `migLinearFactor * n`.
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

/-- Deterministic setup half of `migrateActiveCode` before `resampleHashCode`. -/
private noncomputable def migrateSetupCode : RCode .exact rResize :=
  .seq migrateSetupParamsCode migrateSetupShiftCode

/-- Parameter-free (`¬ReadsWidth`) native `RCode .exact rResize` single-tape `1 · OPT` streaming
rebuild from `(N_old, n, n_init_old)` to `(targetCap U n, n, n)`. -/
noncomputable def migrateActiveCode : RCode .exact rResize :=
  .seq migrateSetupCode <|
  .seq (resampleHashCode mHashBase (mNewHp ⟨3, by decide⟩) (mNewHp ⟨2, by decide⟩)
         (mNewHp ⟨10, by decide⟩) mCur mIdx mK mOne mRes)
       migrateFinishCode


private theorem not_readsWidth_migrateSetupCode : ¬migrateSetupCode.ReadsWidth := by
  simp [migrateSetupCode, RCode.ReadsWidth,
    not_readsWidth_migrateSetupParamsCode, not_readsWidth_migrateSetupShiftCode]

/-- `migrateActiveCode` does not inspect the ambient word width `w` (`¬ReadsWidth`). -/
theorem not_readsWidth_migrateActiveCode : ¬migrateActiveCode.ReadsWidth := by
  simp [migrateActiveCode, RCode.ReadsWidth, not_readsWidth_migrateSetupCode,
    not_readsWidth_resampleHashCode, not_readsWidth_migrateFinishCode]

private theorem migrateSetupCode_exec {U V w N_old n n_init base : ℕ}
    {θ_old : QuotHashSeed U N_old} {s_abs : Dictionary.State U} {x : RData rResize}
    (hx : x.Bounded w) (hn : 1 ≤ n) (hev : EpochValid U n N_old)
    (hfr : x.frontier = base + compactedEpochWords U V w N_old n)
    (hfit_peak : Fits w (base + migratePeakWords U V w N_old n))
    (hsplit : CompactedSplitRep base (base + offCompItems U w N_old) U V w N_old n n_init θ_old
      s_abs ⟨x.mem, x.frontier⟩)
    (hbase : x.regs mBase = base) :
    let N_new := targetCap U n
    let newMeta := base + offCompItems U w N_old
    let offNew := offCompItems U w N_new
    let iwOld := compactedItemWords U V w N_old n
    let iwNew := compactedItemWords U V w N_new n
    let arenaW := migrateArenaWords U V w N_old N_new n
    let arenaB := newMeta + offNew
    let peakF := base + migratePeakWords U V w N_old n
    ∃ (y : RData rResize) (steps_setup : ℕ),
      RDemonicExec w peakF migrateSetupCode x steps_setup (· = y) ∧
      steps_setup ≤ (265 * migFactor + 12400) * n ∧
      y.Bounded w ∧
      y.frontier = peakF ∧
      abiPreserved x y ∧
      (∀ addr < base, y.mem addr = x.mem addr) ∧
      RootHeaderValid U V w N_new n n newMeta y.mem ∧
      EpochParamsStored U V w N_new newMeta y.mem ∧
      ReducedKWise.Rep (base + epochHdrWords) w (qBits U N_old) (hashB N_old)
        (totalMicroBits N_old) 3 θ_old y.mem ∧
      (∃ s_fix_old : Memory.State,
        DictStateInv U V (ghostW w) N_old 0 θ_old s_abs s_fix_old ∧
        totalSlots N_old (compGmAt base U w N_old y.mem) = n ∧
        FixedCoupled base (arenaB + (arenaW - iwOld)) U V w N_old s_fix_old ⟨y.mem, y.frontier⟩) ∧
      y.regs mBase = base ∧
      y.regs mCnt = n ∧
      y.regs mFr = peakF ∧
      y.regs mNewMeta = newMeta ∧
      y.regs mOffNew = offNew ∧
      y.regs mIwNew = iwNew ∧
      y.regs mArena = arenaB ∧
      y.regs mPeakFront = peakF ∧
      y.regs mOldItemDst = arenaB + (arenaW - iwOld) ∧
      y.regs mHashBase = newMeta + epochHdrWords ∧
      (∀ i : Fin 19, y.regs (mOldHp i) =
        mkHashParams w (epochQBits U N_old) (epochHashB N_old) (totalMicroBits N_old) 3 i) ∧
      (∀ i : Fin 36, y.regs (mOldCp i) = mkCompParams U V w N_old i) ∧
      (∀ i : Fin 19, y.regs (mNewHp i) =
        mkHashParams w (epochQBits U N_new) (epochHashB N_new) (totalMicroBits N_new) 3 i) ∧
      (∀ i : Fin 36, y.regs (mNewCp i) = mkCompParams U V w N_new i) := by
  intro N_new newMeta offNew iwOld iwNew arenaW arenaB peakF
  obtain ⟨s₈, steps_p, hex_p, hc_p, hs₈b, hs₈f, habi₈, hbelow₈, hsplit₈,
      hs₈_base, hs₈_cnt, hs₈_nn, hs₈_nm, hs₈_off, hs₈_iwo, hs₈_iwn, hs₈_ar, hs₈_pf, hs₈_k, hs₈_oid,
      hs₈_ohp, hs₈_ocp, hs₈_nhp, hs₈_ncp⟩ :=
    migrateSetupParamsCode_exec hx hn hev hfr hfit_peak hsplit hbase
  obtain ⟨y, steps_s, hex_s, hc_s, hrest⟩ :=
    migrateSetupShiftCode_exec hn hev hfr hfit_peak hs₈b hs₈f habi₈ hbelow₈ hsplit₈
      hs₈_base hs₈_cnt hs₈_nn hs₈_nm hs₈_off hs₈_iwo hs₈_iwn hs₈_ar hs₈_pf hs₈_k hs₈_oid
      hs₈_ohp hs₈_ocp hs₈_nhp hs₈_ncp
  refine ⟨y, steps_p + steps_s, hex_p.seq_eq hex_s, (Nat.add_le_add hc_p hc_s).trans ?_, hrest⟩
  rw [← Nat.add_mul]
  exact Nat.mul_le_mul_right n (by generalize migFactor = F; omega)


/-- **Distributional Single-Tape `1 · OPT` Rebuild (`migrateActiveCode_execRCodeDist`):**
From any active compacted epoch `(N_old, n, n_init_old)` (`1 ≤ n`, `EpochValid U n N_old`),
`migrateActiveCode` resamples a fresh uniform `QuotHashSeed U (targetCap U n)` and streams all `n`
entries into `(targetCap U n, n, n)` at `base` without ever exceeding hardware frontier
`base + migratePeakWords U V w N_old n` (`≤ base + Dynamic.succinctWords 2699 888 U V w n`),
bounding expected instructions plus post-migration `inEpochPotential` by `migLinearFactor * n`. -/
theorem migrateActiveCode_execRCodeDist {U V w N_old n n_init base : ℕ}
    {θ_old : QuotHashSeed U N_old} {s_abs : Dictionary.State U} {x : RData rResize}
    (hx : x.Bounded w) (hn : 1 ≤ n) (hev : EpochValid U n N_old)
    (hfr : x.frontier = base + compactedEpochWords U V w N_old n)
    (hfit_peak : Fits w (base + migratePeakWords U V w N_old n))
    (hsplit : CompactedSplitRep base (base + offCompItems U w N_old) U V w N_old n n_init θ_old
      s_abs ⟨x.mem, x.frontier⟩)
    (hbase : x.regs mBase = base) :
    let N_new := targetCap U n
    let peakF := base + migratePeakWords U V w N_old n
    ∃ (zOf : QuotHashSeed U N_new → RData rResize) (T_mig : ℝ≥0∞),
      ExecRCodeDist w migrateActiveCode x
        ((PMF.uniformOfFintype (QuotHashSeed U N_new)).map zOf) T_mig peakF ∧
      (∀ θ_new,
        (zOf θ_new).Bounded w ∧
        (zOf θ_new).frontier = base + compactedEpochWords U V w N_new n ∧
        CompactedSplitRep base (base + offCompItems U w N_new) U V w N_new n n θ_new s_abs
          ⟨(zOf θ_new).mem, (zOf θ_new).frontier⟩ ∧
        (zOf θ_new).regs mBase = base ∧
        (zOf θ_new).regs mTag = x.regs mTag ∧
        (zOf θ_new).regs mArgU = x.regs mArgU ∧
        (zOf θ_new).regs mArgV = x.regs mArgV ∧
        (∀ addr < base, (zOf θ_new).mem addr = x.mem addr)) ∧
      T_mig + (∑' θ_new, (PMF.uniformOfFintype (QuotHashSeed U N_new)) θ_new *
          (inEpochPotential U w N_new base (zOf θ_new) : ℝ≥0∞)) ≤
        ((migLinearFactor * n : ℕ) : ℝ≥0∞) := by
  intro N_new peakF
  obtain ⟨hw, hU, _⟩ := rootHeaderValid_bounds hx hsplit.root_hdr
  have hNU_old : N_old ≤ U := by rcases hev with ⟨rfl, _⟩ | ⟨_, _, _, hNU⟩ <;> omega
  have hn_old : n ≤ N_old := by rcases hev with ⟨rfl, _⟩ | ⟨_, hnN, _, _⟩ <;> omega
  have hnU : n ≤ U := hn_old.trans hNU_old
  obtain ⟨_, _, _, hNU_new⟩ := targetCap_bounds_of_pos hn hnU
  obtain ⟨y_set, steps_set, hex_set, hc_set, hy_set_b, hy_set_fr, habi_set, hbelow_set,
      hhdr_set, hpar_set, hrep_old, hcpl_old,
      hr_base, hr_cnt, hr_fr, hr_nm, hr_off, hr_iwn, hr_ar, hr_pf, hr_oid, hr_hb,
      hr_ohp, hr_ocp, hr_nhp, hr_ncp⟩ :=
    migrateSetupCode_exec hx hn hev hfr hfit_peak hsplit hbase
  set newMeta := base + offCompItems U w N_old
  have hpeak_def : peakF =
      newMeta + offCompItems U w N_new + migrateArenaWords U V w N_old N_new n := by
    dsimp only [peakF, newMeta, N_new]; unfold migratePeakWords; omega
  have hnm_le : newMeta + offCompItems U w N_new ≤ peakF := by rw [hpeak_def]; omega
  obtain ⟨zOf, T_mig, hex_full, hpost, hcost⟩ :=
    exec_setup_resample_finish (metaBase := newMeta) (base := base)
      (finBound := (93500 * migFactor + 10000) * n)
      (finishCleanCode := migrateFinishCleanCode)
      (P := fun θ_new z =>
        z.Bounded w ∧
        z.frontier = base + compactedEpochWords U V w N_new n ∧
        CompactedSplitRep base (base + offCompItems U w N_new) U V w N_new n n θ_new s_abs
          ⟨z.mem, z.frontier⟩ ∧
        z.regs mBase = base ∧
        z.regs mTag = x.regs mTag ∧
        z.regs mArgU = x.regs mArgU ∧
        z.regs mArgV = x.regs mArgV ∧
        (∀ addr < base, z.mem addr = x.mem addr))
      hw hU hNU_new hex_set hy_set_b hy_set_fr (hfit_peak.of_le hnm_le) hnm_le hr_hb hr_nhp
      (fun θ_new y_rs hfr_y hseed_y hmem_y hreg_y => by
        obtain ⟨z, stepsClean, hex_cl, hzb, hzf, hsp, habi, hbel, hbd⟩ :=
          migrateFinishCode_exec hn hev hsplit.card_eq hsplit.vals_lt hfit_peak
            hy_set_b hy_set_fr habi_set hbelow_set hhdr_set hpar_set hrep_old hcpl_old
            hr_base hr_cnt hr_fr hr_nm hr_off hr_iwn hr_ar hr_pf hr_oid hr_ohp hr_ocp hr_nhp hr_ncp
            hfr_y hseed_y hmem_y hreg_y
        exact ⟨z, stepsClean, hex_cl,
          ⟨hzb, hzf, hsp, habi.1.trans hbase, habi.2.1, habi.2.2.1, habi.2.2.2, hbel⟩, hbd⟩)
  refine ⟨zOf, T_mig, hex_full, hpost, hcost.trans ((Nat.cast_le (α := ℝ≥0∞)).mpr ?_)⟩
  have hf1 := one_le_migFactor
  unfold migLinearFactor
  refine (Nat.add_le_add_right (Nat.add_le_add hc_set (Nat.le_mul_of_pos_right 826 hn)) _).trans ?_
  simp only [← Nat.add_mul]
  exact Nat.mul_le_mul_right n (by generalize migFactor = F at hf1 ⊢; omega)


end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
