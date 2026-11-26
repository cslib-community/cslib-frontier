/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.Exec.Witness
public import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Hash-Seed Resampling Wrapper and Post-Resample Metadata Initialization

Internal distributional combinator `exec_setup_resample_finish`, scratch-clearing stub
`zeroResampleRegsCode`, and shared post-resample `initNewEpochMetaProg` execution helper
`exec_postResample_initMeta` shared by `MigrateFinish`, `MigrateActive`, and `InitFirst`.
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

/-- Zero the 5 scratch registers written by `resampleHashCode` (`5` instructions). -/
noncomputable def zeroResampleRegsCode : RCode .exact rResize :=
  .seq (.op (.const mCur 0)) <|
  .seq (.op (.const mIdx 0)) <|
  .seq (.op (.const mK 0)) <|
  .seq (.op (.const mOne 0))
       (.op (.const mRes 0))

@[simp] theorem not_readsWidth_zeroResampleRegsCode : ¬zeroResampleRegsCode.ReadsWidth := by
  simp [zeroResampleRegsCode, RCode.ReadsWidth, Op.ReadsWidth]

/-- Every address of the seed window `[base, base + seedWords w₀ b b' 3)` is the leading word
`base` or a limb address `base + 1 + (m + L * j)` of `ReducedKWise.SeedRep`. -/
private theorem seedWindow_cases {base w₀ b b' a : ℕ} (h₁ : base ≤ a)
    (h₂ : a < base + ReducedKWise.seedWords w₀ b b' 3) :
    a = base ∨ ∃ (j : Fin 3) (m : Fin (reducedLimbCount (reducedTrinomialStep w₀ b b'))),
      a = base + 1 + (m.val + reducedLimbCount (reducedTrinomialStep w₀ b b') * j.val) := by
  rcases eq_or_lt_of_le h₁ with rfl | h_gt
  · exact Or.inl rfl
  set L := reducedLimbCount (reducedTrinomialStep w₀ b b')
  have hsw : ReducedKWise.seedWords w₀ b b' 3 = 1 + 3 * L := rfl
  have hoff_lt : a - (base + 1) < 3 * L := by omega
  have hmod := Nat.mod_add_div (a - (base + 1)) L
  exact Or.inr ⟨⟨(a - (base + 1)) / L, Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])⟩,
    ⟨(a - (base + 1)) % L, Nat.mod_lt _ (by omega)⟩, by dsimp only; omega⟩

private theorem zeroResampleRegs_regs (y : RData rResize) (j : Fin rResize) :
    (((((y.set mCur 0).set mIdx 0).set mK 0).set mOne 0).set mRes 0).regs j =
      if j ∈ ([mCur, mIdx, mK, mOne, mRes] : List (Fin rResize)) then 0 else y.regs j := by
  simp only [RData.set, Function.update_apply, List.mem_cons, List.not_mem_nil, or_false]
  grind

theorem zeroResampleRegsCode_exec {w L_peak w₀ b b' hashBase : ℕ}
    {θ : ReducedPolySeed w₀ b b' 3} {x y : RData rResize}
    (hx : x.Bounded w) (hy_fr : y.frontier = x.frontier) (hL : x.frontier ≤ L_peak)
    (hw₀ : w₀ ≤ w)
    (hc_lt : 2 * reducedChunkBits (reducedTrinomialStep w₀ b b') < w)
    (hfr_h : hashBase + ReducedKWise.seedWords w₀ b b' 3 ≤ x.frontier)
    (hseed : ReducedKWise.SeedRep hashBase w₀ b b' 3 θ y.mem)
    (hframe_mem : ∀ a, (a < hashBase ∨ hashBase + ReducedKWise.seedWords w₀ b b' 3 ≤ a) →
      y.mem a = x.mem a)
    (hframe_reg : ∀ j, j ∉ ([mCur, mIdx, mK, mOne, mRes] : List (Fin rResize)) →
      y.regs j = x.regs j) :
    ∃ z : RData rResize,
      z = (((((y.set mCur 0).set mIdx 0).set mK 0).set mOne 0).set mRes 0) ∧
      RDemonicExec w L_peak zeroResampleRegsCode y 5 (· = z) ∧
      z.Bounded w ∧ z.mem = y.mem ∧ z.frontier = x.frontier ∧
      ∀ j, j ∉ ([mCur, mIdx, mK, mOne, mRes] : List (Fin rResize)) → z.regs j = x.regs j := by
  have hyL : y.frontier ≤ L_peak := hy_fr.le.trans hL
  have hfz : Fits w 0 := fits_zero w
  set z₁ := y.set mCur 0
  have s1 := RDemonicExec.const (B := .exact) (d := mCur) (v := 0) (x := y) hyL hfz
  set z₂ := z₁.set mIdx 0
  have s2 := RDemonicExec.const (B := .exact) (d := mIdx) (v := 0) (x := z₁) hyL hfz
  set z₃ := z₂.set mK 0
  have s3 := RDemonicExec.const (B := .exact) (d := mK) (v := 0) (x := z₂) hyL hfz
  set z₄ := z₃.set mOne 0
  have s4 := RDemonicExec.const (B := .exact) (d := mOne) (v := 0) (x := z₃) hyL hfz
  set z := z₄.set mRes 0
  have s5 := RDemonicExec.const (B := .exact) (d := mRes) (v := 0) (x := z₄) hyL hfz
  refine ⟨z, rfl,
    (s1.seq_eq (s2.seq_eq (s3.seq_eq (s4.seq_eq s5)))).mono (by omega) (fun _ h => h),
    ⟨⟨fun j => ?_, fun a => ?_⟩, hy_fr ▸ hx.frontier_fits, fun a ha => ?_⟩,
    rfl, hy_fr, fun j hj => ?_⟩
  · dsimp only [z, z₄, z₃, z₂, z₁, RData.toData]
    rw [zeroResampleRegs_regs]
    split_ifs with hj
    · exact hfz
    · exact hframe_reg j hj ▸ hx.regs_fits j
  · dsimp only [z, z₄, z₃, z₂, z₁, RData.set, RData.toData]
    by_cases ha_out : a < hashBase ∨ hashBase + ReducedKWise.seedWords w₀ b b' 3 ≤ a
    · rw [hframe_mem a ha_out]; exact hx.mem_fits a
    rw [not_or, not_lt, not_le] at ha_out
    rcases seedWindow_cases ha_out.1 ha_out.2 with rfl | ⟨j, m, rfl⟩
    · rw [hseed.1]; exact θ.1.isLt.trans_le (Nat.pow_le_pow_right two_pos (by omega))
    · rw [hseed.2 j m]
      exact (getLimb_lt _ _ _).trans_le (Nat.pow_le_pow_right two_pos (by omega))
  · dsimp only [z, z₄, z₃, z₂, z₁, RData.set] at ha ⊢
    rw [hframe_mem a (Or.inr (by omega))]
    exact hx.zero_above (hy_fr ▸ ha)
  · dsimp only [z, z₄, z₃, z₂, z₁]
    rw [zeroResampleRegs_regs, ite_eq_right hj, hframe_reg j hj]


/-- Shared post-resample step executing `.op (.copy mTmpA rMeta)` followed by `wInitNewMeta.code`
from the scratch-zeroed state after `resampleHashCode`, used by both `migrateFinishCode_exec`
(`rMeta = mNewMeta`) and `initFirstFinishCode_exec` (`rMeta = mBase`). -/
theorem exec_postResample_initMeta {U V w N metaBase peakF : ℕ}
    {θ : QuotHashSeed U N} {y_set y_rs : RData rResize} (rMeta : Fin rResize)
    (hr_not : rMeta ∉ ([mCur, mIdx, mK, mOne, mRes] : List (Fin rResize)))
    (hw : 0 < w) (hU : U < 2 ^ w) (hN_pos : 1 ≤ N) (hNU : N ≤ U)
    (hfits_U : Fits w U) (hV : V ≤ 2 ^ w)
    (hy_set_b : y_set.Bounded w) (hy_set_fr : y_set.frontier = peakF)
    (hnm_le_peak : metaBase + offCompItems U w N ≤ peakF)
    (hfit_nm : Fits w (metaBase + offCompItems U w N))
    (hr_meta : y_set.regs rMeta = metaBase)
    (hr_fr : y_set.regs mFr = peakF)
    (hr_nhp : ∀ i : Fin 19, y_set.regs (mNewHp i) =
      mkHashParams w (epochQBits U N) (epochHashB N) (totalMicroBits N) 3 i)
    (hr_ncp : ∀ i : Fin 36, y_set.regs (mNewCp i) = mkCompParams U V w N i)
    (hrs_fr : y_rs.frontier = y_set.frontier)
    (hrs_seed : ReducedKWise.SeedRep (metaBase + epochHdrWords) (qBits U N) (hashB N)
      (totalMicroBits N) 3 θ y_rs.mem)
    (hrs_mem : ∀ a,
      a < metaBase + epochHdrWords ∨
        metaBase + epochHdrWords +
          ReducedKWise.seedWords (qBits U N) (hashB N) (totalMicroBits N) 3 ≤ a →
      y_rs.mem a = y_set.mem a)
    (hrs_reg : ∀ reg, reg ∉ ([mCur, mIdx, mK, mOne, mRes] : List (Fin rResize)) →
      y_rs.regs reg = y_set.regs reg) :
    let z₀ := (((((y_rs.set mCur 0).set mIdx 0).set mK 0).set mOne 0).set mRes 0)
    let d_im := ((mkHashParams w (qBits U N) (hashB N) (totalMicroBits N) 3,
      mkCompParams U V w N), metaBase)
    ∃ z₁ z₂ : RData rResize,
      RDemonicExec (B := .exact) w peakF (.op (.copy mTmpA rMeta)) z₀ 1 (· = z₁) ∧
      RDemonicExec w peakF (RCode.ofCode (wInitNewMeta.code mFr srcInitNewMeta tmpInitNewMeta)) z₁
        (migFactor * (memoryCost (initNewEpochMetaProg d_im) ⟨y_rs.mem, peakF⟩ + 1)) (· = z₂) ∧
      memoryCost (initNewEpochMetaProg d_im) ⟨y_rs.mem, peakF⟩ ≤ 256 * N + 475 ∧
      ((Memory.spec 0).clientState ⟨y_rs.mem, peakF⟩ (initNewEpochMetaProg d_im)).frontier =
        peakF ∧
      z₂.Bounded w ∧
      z₂.frontier = peakF ∧
      z₂.regs mFr = peakF ∧
      z₂.mem = ((Memory.spec 0).clientState ⟨y_rs.mem, peakF⟩ (initNewEpochMetaProg d_im)).mem ∧
      ReducedKWise.Rep (metaBase + epochHdrWords) w (qBits U N) (hashB N) (totalMicroBits N) 3
        θ z₂.mem ∧
      totalSlots N (compGmAt metaBase U w N z₂.mem) = 0 ∧
      slotPotential N (compGmAt metaBase U w N z₂.mem) = 0 ∧
      (∃ s_fix₀ : Memory.State,
        DictStateInv U V (ghostW w) N 0 θ (Dictionary.empty U) s_fix₀ ∧
        FixedCoupled metaBase (metaBase + offCompItems U w N) U V w N s_fix₀ ⟨z₂.mem, peakF⟩) ∧
      (∀ reg : Fin rResize, reg.val < 160 →
        reg ∉ ([mFr, mTmpA, mCur, mIdx, mK, mOne, mRes] : List (Fin rResize)) →
        z₂.regs reg = y_set.regs reg) ∧
      (∀ a, ¬(metaBase + epochHdrWords ≤ a ∧ a < metaBase + offCompItems U w N) →
        z₂.mem a = y_set.mem a) := by
  intro z₀ d_im
  obtain ⟨hsp_le, hsw_le_sp, _, hc_lt⟩ :=
    hashSpace_bounds_of_fits_offCompItems hU hNU hfit_nm
  have heh_val : epochHdrWords = 225 := rfl
  obtain ⟨z₀', hz₀'_def, _hex_zr, hz₀b, hz₀m, hz₀f_set, hz₀_reg⟩ :=
    zeroResampleRegsCode_exec hy_set_b hrs_fr hy_set_fr.le
      (qBits_le_of_le_pow hw hU.le) hc_lt
      (by rw [hy_set_fr]; linarith only [hnm_le_peak, hsw_le_sp, hsp_le, heh_val])
      hrs_seed hrs_mem hrs_reg
  have hz₀_eq : z₀' = z₀ := hz₀'_def
  subst hz₀_eq
  have hz₀f : z₀.frontier = peakF := hz₀f_set.trans hy_set_fr
  set z₁ := z₀.set mTmpA metaBase
  have hz₀_meta : z₀.regs rMeta = metaBase := (hz₀_reg rMeta hr_not).trans hr_meta
  have hex_c1 := RDemonicExec.copy (B := .exact) (w := w) (L_peak := peakF)
    (d := mTmpA) (s := rMeta) (x := z₀) hz₀f.le
  rw [hz₀_meta] at hex_c1
  have hz₁b : z₁.Bounded w := hz₀b.set (hfit_nm.of_le (Nat.le_add_right _ _))
  have hz₀_fr_reg : z₀.regs mFr = peakF := (hz₀_reg mFr (by simp)).trans hr_fr
  have hms₁ : memoryState mFr z₁.toData = ⟨y_rs.mem, peakF⟩ := by
    simp [memoryState, z₁, RData.set, RData.toData, hz₀m, hz₀_fr_reg]
  have hz₁_nhp : ∀ i : Fin 19, z₁.regs (mNewHp i) =
      mkHashParams w (qBits U N) (hashB N) (totalMicroBits N) 3 i := fun i =>
    (Function.update_of_ne (mNewHp_ne_mReg i (c := 156) (Or.inr (by decide))) _ _).trans <|
      (hz₀_reg _ (by clear * -; simp [Fin.ext_iff]; omega)).trans (hr_nhp i)
  have hz₁_ncp : ∀ i : Fin 36, z₁.regs (mNewCp i) = mkCompParams U V w N i := fun i =>
    (Function.update_of_ne (mNewCp_ne_mReg i (c := 156) (Or.inr (by decide))) _ _).trans <|
      (hz₀_reg _ (by clear * -; simp [Fin.ext_iff]; omega)).trans (hr_ncp i)
  have hin_im : z₁.regs ∘ srcInitNewMeta = WordEncoding.encode d_im :=
    (regs_pairSrc (regs_pairSrc (regs_hp_eq hz₁_nhp) (regs_cp_eq hz₁_ncp))
      (regs_reg1_eq mTmpA (by simp [z₁, RData.set]))).eq
  obtain ⟨hpre_im, hv_im, hc_im, hfr_im, hrep_im, htot_im, hpot_im, h_empty_im, hframe_im⟩ :=
    initNewEpochMetaProg_spec (w := w) (U := U) (V := V) (N := N) (newMetaBase := metaBase)
      (arenaBase := metaBase + offCompItems U w N) (θ_new := θ) (s₀ := ⟨y_rs.mem, peakF⟩)
      hw hN_pos hNU hfits_U hV hnm_le_peak hfit_nm hrs_seed
  obtain ⟨z₂, hex_im, hz₂b, hz₂f, hm_im, _, hframe_reg_im⟩ :=
    execWitness wInitNewMeta factor_wInitNewMeta_le mFr srcInitNewMeta tmpInitNewMeta
      tmpInitNewMeta_inj srcInitNewMeta_ne_tmp tmpInitNewMeta_ne_mFr srcInitNewMeta_ne_mFr
      d_im hz₁b hz₀f.le hin_im (hms₁ ▸ hpre_im) (hms₁ ▸ hv_im)
      (by rw [hms₁, hfr_im]; exact hz₀f.symm.le)
  rw [hms₁] at hm_im hex_im
  have hz₂f_eq : z₂.frontier = peakF := hz₂f.trans hz₀f
  have hz₂_fr_reg : z₂.regs mFr = peakF := (congrArg Memory.State.frontier hm_im).trans hfr_im
  have hz₂_mem_eq : z₂.mem = ((Memory.spec 0).clientState ⟨y_rs.mem, peakF⟩
      (initNewEpochMetaProg d_im)).mem :=
    congrArg Memory.State.mem hm_im
  have hkeep_set_2 : ∀ reg : Fin rResize, reg.val < 160 →
      reg ∉ ([mFr, mTmpA, mCur, mIdx, mK, mOne, mRes] : List (Fin rResize)) →
      z₂.regs reg = y_set.regs reg := fun reg h160 hnot => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot
    obtain ⟨hfr', hta, hj⟩ := hnot
    rw [hframe_reg_im reg hfr' (mkTmp_ne_reg _ h160 (fun a => Fin.elim0 a)),
      ← hz₀_reg reg (by simpa using hj)]
    exact Function.update_of_ne hta _ _
  have hz₂_not_im : ∀ a, ¬(metaBase + epochHdrWords ≤ a ∧ a < metaBase + offCompItems U w N) →
      z₂.mem a = y_set.mem a := fun a ha => by
    rw [hz₂_mem_eq, hframe_im a ha]
    exact hrs_mem a (by omega)
  have hs₂_st_eq : ({ mem := z₂.mem, frontier := peakF } : Memory.State) =
      (Memory.spec 0).clientState ⟨y_rs.mem, peakF⟩ (initNewEpochMetaProg d_im) :=
    Memory.State.ext hz₂_mem_eq hfr_im.symm
  exact ⟨z₁, z₂, hex_c1, hex_im, hc_im, hfr_im, hz₂b, hz₂f_eq, hz₂_fr_reg, hz₂_mem_eq,
    hz₂_mem_eq ▸ hrep_im, hz₂_mem_eq ▸ htot_im, hz₂_mem_eq ▸ hpot_im,
    h_empty_im.imp (fun _ ⟨hi₀, hc₀⟩ => ⟨hi₀, hs₂_st_eq ▸ hc₀⟩),
    hkeep_set_2, hz₂_not_im⟩

theorem exec_setup_resample_finish
    {U w N_new metaBase base peakF steps_set finBound : ℕ}
    {setupCode finishCleanCode : RCode .exact rResize} {x y_set : RData rResize}
    {P : QuotHashSeed U N_new → RData rResize → Prop}
    (hw : 0 < w) (hU : U < 2 ^ w) (hNU : N_new ≤ U)
    (hex_set : RDemonicExec w peakF setupCode x steps_set (· = y_set))
    (hy_set_b : y_set.Bounded w) (hy_set_fr : y_set.frontier = peakF)
    (hfit_nm : Fits w (metaBase + offCompItems U w N_new))
    (hnm_le_peak : metaBase + offCompItems U w N_new ≤ peakF)
    (hr_hb : y_set.regs mHashBase = metaBase + epochHdrWords)
    (hr_nhp : ∀ j : Fin 19, y_set.regs (mNewHp j) =
      mkHashParams w (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3 j)
    (hfin_spec : ∀ (θ : QuotHashSeed U N_new) (y_rs : RData rResize),
      y_rs.frontier = y_set.frontier →
      ReducedKWise.SeedRep (metaBase + epochHdrWords) (qBits U N_new) (hashB N_new)
        (totalMicroBits N_new) 3 θ y_rs.mem →
      (∀ a, a < metaBase + epochHdrWords ∨
          metaBase + epochHdrWords +
            ReducedKWise.seedWords (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3 ≤ a →
          y_rs.mem a = y_set.mem a) →
      (∀ j : Fin rResize, j ∉ ([mCur, mIdx, mK, mOne, mRes] : List (Fin rResize)) →
          y_rs.regs j = y_set.regs j) →
      ∃ (z : RData rResize) (stepsClean : ℕ),
        RDemonicExec w peakF finishCleanCode
          (((((y_rs.set mCur 0).set mIdx 0).set mK 0).set mOne 0).set mRes 0)
          stepsClean (· = z) ∧
        P θ z ∧
        (5 + stepsClean) + inEpochPotential U w N_new base z ≤ finBound) :
    ∃ (zOf : QuotHashSeed U N_new → RData rResize) (T_all : ℝ≥0∞),
      ExecRCodeDist w
        (.seq setupCode <|
          .seq (resampleHashCode mHashBase (mNewHp ⟨3, by decide⟩) (mNewHp ⟨2, by decide⟩)
                 (mNewHp ⟨10, by decide⟩) mCur mIdx mK mOne mRes)
               (.seq zeroResampleRegsCode finishCleanCode))
        x ((PMF.uniformOfFintype (QuotHashSeed U N_new)).map zOf) T_all peakF ∧
      (∀ θ, P θ (zOf θ)) ∧
      T_all + (∑' θ, (PMF.uniformOfFintype (QuotHashSeed U N_new)) θ *
          (inEpochPotential U w N_new base (zOf θ) : ℝ≥0∞)) ≤
        ((steps_set + 826 + finBound : ℕ) : ℝ≥0∞) := by
  obtain ⟨hsp_le, hsw_le_sp, hfit_h, hc_lt⟩ :=
    hashSpace_bounds_of_fits_offCompItems hU hNU hfit_nm
  have hsw_le_fr : metaBase + epochHdrWords +
      ReducedKWise.seedWords (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3 ≤
      y_set.frontier := by
    rw [hy_set_fr]; unfold epochHdrWords; omega
  obtain ⟨μ_rs, hex_rs, hmap_unif, hrs_supp⟩ :=
    resampleHashCode_execRCodeDist (w := w) (L_peak := peakF)
      (w₀ := qBits U N_new) (b := hashB N_new) (b' := totalMicroBits N_new) (k := 3)
      (hashBase := metaBase + epochHdrWords) (x := y_set)
      mResample_nodup (qBits_le_of_le_pow hw hU.le) hc_lt hy_set_fr.le hsw_le_fr
      (hfit_h.of_le (by omega)) hr_hb
      (by rw [hr_nhp ⟨3, by decide⟩]; rfl)
      (by rw [hr_nhp ⟨2, by decide⟩]; rfl)
      (by rw [hr_nhp ⟨10, by decide⟩]; rfl)
  let extSeed (y : RData rResize) : QuotHashSeed U N_new :=
    ReducedKWise.extractSeed (metaBase + epochHdrWords) (qBits U N_new) (hashB N_new)
      (totalMicroBits N_new) 3 y.mem
  have hcanon_z₀ : ∀ {y₁ y₂ : RData rResize}, y₁ ∈ μ_rs.support → y₂ ∈ μ_rs.support →
      extSeed y₁ = extSeed y₂ →
      (((((y₁.set mCur 0).set mIdx 0).set mK 0).set mOne 0).set mRes 0) =
      (((((y₂.set mCur 0).set mIdx 0).set mK 0).set mOne 0).set mRes 0) := by
    intro y₁ y₂ hy₁ hy₂ heq_seed
    obtain ⟨hfr₁, hseed₁, hmem₁, hreg₁⟩ := hrs_supp y₁ hy₁
    obtain ⟨hfr₂, hseed₂, hmem₂, hreg₂⟩ := hrs_supp y₂ hy₂
    change ReducedKWise.SeedRep _ _ _ _ _ (extSeed y₁) y₁.mem at hseed₁
    change ReducedKWise.SeedRep _ _ _ _ _ (extSeed y₂) y₂.mem at hseed₂
    rw [heq_seed] at hseed₁
    apply RData.ext
    · funext j
      rw [zeroResampleRegs_regs, zeroResampleRegs_regs]
      split_ifs with hj
      · rfl
      · exact (hreg₁ j hj).trans (hreg₂ j hj).symm
    · funext a
      dsimp only [RData.set]
      by_cases ha_out :
          a < metaBase + epochHdrWords ∨
            metaBase + epochHdrWords +
              ReducedKWise.seedWords (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3 ≤ a
      · exact (hmem₁ a ha_out).trans (hmem₂ a ha_out).symm
      rw [not_or, not_lt, not_le] at ha_out
      rcases seedWindow_cases ha_out.1 ha_out.2 with rfl | ⟨j, m, rfl⟩
      · exact hseed₁.1.trans hseed₂.1.symm
      · exact (hseed₁.2 j m).trans (hseed₂.2 j m).symm
    · exact hfr₁.trans hfr₂.symm
  have hex_rep (θ : QuotHashSeed U N_new) : ∃ y_rs ∈ μ_rs.support, extSeed y_rs = θ :=
    (PMF.mem_support_map_iff _ _ _).mp (hmap_unif.symm ▸
      Cslib.Probability.PMF.mem_support_uniformOfFintype θ)
  choose yRep hyRep_supp hyRep_seed using hex_rep
  have hfin_rep := fun θ =>
    hfin_spec θ (yRep θ) (hrs_supp _ (hyRep_supp θ)).1
      (by convert (hrs_supp _ (hyRep_supp θ)).2.1; exact (hyRep_seed θ).symm)
      (hrs_supp _ (hyRep_supp θ)).2.2.1
      (hrs_supp _ (hyRep_supp θ)).2.2.2
  choose zOf stepsClean hfin_res using hfin_rep
  have hfin_any : ∀ y_rs ∈ μ_rs.support,
      ExecRCodeDist w (.seq zeroResampleRegsCode finishCleanCode) y_rs
        (PMF.pure (zOf (extSeed y_rs))) ((5 + stepsClean (extSeed y_rs) : ℕ) : ℝ≥0∞) peakF := by
    intro y_rs hy_rs
    obtain ⟨hfr_y, hseed_y, hmem_y, hreg_y⟩ := hrs_supp y_rs hy_rs
    obtain ⟨z₀, hz₀_def, hex_zr, _, _, _, _⟩ :=
      zeroResampleRegsCode_exec hy_set_b hfr_y hy_set_fr.le
        (qBits_le_of_le_pow hw hU.le) hc_lt hsw_le_fr hseed_y hmem_y hreg_y
    exact ExecRCodeDist.of_demonicExec (hex_zr.seq_eq
      ((hz₀_def.trans (hcanon_z₀ hy_rs (hyRep_supp _) (hyRep_seed _).symm)).symm ▸
        (hfin_res (extSeed y_rs)).1))
  have hex_tail := hex_rs.seq hfin_any
  have hmu_eq : μ_rs.bind (fun y_rs => PMF.pure (zOf (extSeed y_rs))) =
      (PMF.uniformOfFintype (QuotHashSeed U N_new)).map zOf := by
    change μ_rs.map (zOf ∘ extSeed) = _
    rw [← PMF.map_comp, hmap_unif]
  have hex_full := (ExecRCodeDist.of_demonicExec hex_set).seq_pure (hmu_eq ▸ hex_tail)
  set μ_u := PMF.uniformOfFintype (QuotHashSeed U N_new)
  have htsum_fin : (∑' y_rs, μ_rs y_rs * ((5 + stepsClean (extSeed y_rs) : ℕ) : ℝ≥0∞)) =
      ∑' θ, μ_u θ * ((5 + stepsClean θ : ℕ) : ℝ≥0∞) := by
    rw [← Cslib.Probability.PMF.tsum_map_mul μ_rs extSeed
      (fun θ => ((5 + stepsClean θ : ℕ) : ℝ≥0∞)), hmap_unif]
  have hsw_le_163 :
      ReducedKWise.seedWords (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3 ≤ 163 :=
    (ReducedKWise.seedWords_le _ _ _ 3).trans (by decide)
  have hsum_fin_pot :
      (∑' θ, μ_u θ * ((5 + stepsClean θ : ℕ) : ℝ≥0∞)) +
        (∑' θ, μ_u θ * (inEpochPotential U w N_new base (zOf θ) : ℝ≥0∞)) ≤
        (finBound : ℝ≥0∞) := by
    rw [← CompleteLattice.summable.tsum_add CompleteLattice.summable]
    calc _ ≤ ∑' θ, μ_u θ * (finBound : ℝ≥0∞) := tsum_le_tsum fun θ => by
            rw [← mul_add]; exact mul_le_mul_right (by exact_mod_cast (hfin_res θ).2.2) _
      _ = (finBound : ℝ≥0∞) := by rw [ENNReal.tsum_mul_right, μ_u.tsum_coe, one_mul]
  refine ⟨zOf, _, hex_full, fun θ => (hfin_res θ).2.1, ?_⟩
  rw [htsum_fin, add_assoc, add_assoc]
  have hsw_b : ((5 * ReducedKWise.seedWords (qBits U N_new) (hashB N_new)
      (totalMicroBits N_new) 3 + 11 : ℕ) : ℝ≥0∞) ≤ ((826 : ℕ) : ℝ≥0∞) :=
    (Nat.cast_le (α := ℝ≥0∞)).mpr (by omega)
  calc (steps_set : ℝ≥0∞) +
        (((5 * ReducedKWise.seedWords (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3 +
            11 : ℕ) : ℝ≥0∞) +
          ((∑' θ, μ_u θ * ((5 + stepsClean θ : ℕ) : ℝ≥0∞)) +
            (∑' θ, μ_u θ * (inEpochPotential U w N_new base (zOf θ) : ℝ≥0∞))))
      ≤ (steps_set : ℝ≥0∞) + (((826 : ℕ) : ℝ≥0∞) + (finBound : ℝ≥0∞)) := by gcongr
    _ = ((steps_set + 826 + finBound : ℕ) : ℝ≥0∞) := by push_cast; ring


end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
