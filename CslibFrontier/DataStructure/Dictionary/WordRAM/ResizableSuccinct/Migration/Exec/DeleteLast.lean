/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.Exec.Registers
import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.Exec.Witness
import Mathlib.Tactic.Linarith

/-!
# Deterministic Singleton Deletion and Empty-Epoch Collapse (`deleteLastOneCode`)

Compiles singleton deletion (`n = 1 → 1` or `1 → 0`) on `delete u` into the parameter-free
(`¬ReadsWidth`) native `RCode .exact rResize` subroutine `deleteLastOneCode`, proving its `O(1)`
deterministic `RDemonicExec` specification `deleteLastOneCode_demonicExec`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.deleteLastOneCharge`: parameter-free
  `O(1)` deterministic instruction charge for `n = 1` deletion and empty-epoch collapse.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.deleteLastOneCode`: parameter-free
  `RCode .exact rResize` singleton-epoch deletion and empty-header collapse subroutine.

## Main results

* `not_readsWidth_deleteLastOneCode`: `deleteLastOneCode` does not inspect the ambient word width.
* `deleteLastOneCode_demonicExec`: deterministic `RDemonicExec` specification collapsing to the
  8-word empty `CompactedRep` on key match and preserving `CompactedSplitRep` and `inEpochPotential`
  on key miss within `deleteLastOneCharge` instructions.
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

/-- Parameter-free $O(1)$ deterministic instruction charge for `n = 1` deletion and empty-epoch
collapse (`deleteLastOneCode`). -/
noncomputable def deleteLastOneCharge : ℕ :=
  46000 * migFactor + 6500

private noncomputable def deleteLastReadCode : RCode .exact rResize :=
  .seq (loadBlockUpTo mBase mCur mOldHp offHashParams 18 (by decide)) <|
  .seq (loadBlockUpTo mBase mCur mOldCp offCompParams 35 (by decide)) <|
  .seq (.op (.const mCnt 1)) <|
  .seq (.op (.const mFr 0)) <|
  .seq (RCode.ofCode (wItemWords.code mFr srcOldIw tmpOldIw)) <|
  .seq (.op (.exactBin .add mItemBase mBase (mOldCp ⟨34, by decide⟩))) <|
  .seq (.op (.exactBin .add mFr mItemBase mIwOld)) <|
  .seq (.op (.const mZero 0))
       (RCode.ofCode (wReadOldKV.code mFr srcReadOldKV tmpReadOldKV))

private noncomputable def deleteLastHitTailCode : RCode .exact rResize :=
  .seq (.op (.const mZero 0)) <|
  .seq (storeAtOffCode mBase mZero mCur 5) <|
  .seq (storeAtOffCode mBase mZero mCur 6) <|
  .seq (storeAtOffCode mBase mZero mCur 7) <|
  .seq (.op (.const mCur 8)) <|
  .seq (.op (.exactBin .add mCur mBase mCur)) <|
  .seq (.op (.exactBin .sub mK mFr mCur))
       (shrinkCode mK mIdx mZero mOne)

/-- Singleton deletion (`n = 1 → 1` or `1 → 0`) on `delete u`: reconstructs the sole live key
`u₀` at dense slot `0`, and on `u₀ = u` zeros `(N, n, n_init)` at `base + 5..7` and shrinks back
to the 8-word empty header (`¬ReadsWidth`). -/
noncomputable def deleteLastOneCode : RCode .exact rResize :=
  .seq deleteLastReadCode
       (.branch (.eq mU0 mArgU)
         deleteLastHitTailCode
         (.op (.copy mZero mZero)))

private theorem not_readsWidth_deleteLastReadCode : ¬deleteLastReadCode.ReadsWidth := by
  have hb1 := not_readsWidth_loadBlockUpTo mBase mCur mOldHp offHashParams 18 (by decide)
  have hb2 := not_readsWidth_loadBlockUpTo mBase mCur mOldCp offCompParams 35 (by decide)
  simp [deleteLastReadCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin, hb1, hb2]

/-- `deleteLastOneCode` does not inspect the ambient word width `w` (`¬ReadsWidth`). -/
theorem not_readsWidth_deleteLastOneCode : ¬deleteLastOneCode.ReadsWidth := by
  simp [deleteLastOneCode, deleteLastHitTailCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin,
    not_readsWidth_deleteLastReadCode, not_readsWidth_storeAtOffCode,
    shrinkCode_not_readsWidth]

private theorem deleteLastReadCode_exec {U V w N n_init base : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} {x : RData rResize}
    (hx : x.Bounded w) (hev : EpochValid U 1 N)
    (hfr : x.frontier = base + compactedEpochWords U V w N 1)
    (hsplit : CompactedSplitRep base (base + offCompItems U w N) U V w N 1 n_init θ s_abs
      ⟨x.mem, x.frontier⟩)
    (hbase : x.regs mBase = base) :
    let u₀ := reconstructKeyAt base (base + offCompItems U w N) U V w N 1 θ x.mem 0
    ∃ (y : RData rResize) (steps_r : ℕ),
      RDemonicExec w x.frontier deleteLastReadCode x steps_r (· = y) ∧
      steps_r ≤ 45182 * migFactor + 170 ∧
      y.Bounded w ∧
      y.frontier = x.frontier ∧
      y.regs mFr = x.frontier ∧
      y.regs mBase = base ∧
      y.regs mArgU = x.regs mArgU ∧
      y.regs mU0 = u₀ ∧
      (∀ a, ¬(base + 63 ≤ a ∧ a < base + 225) → y.mem a = x.mem a) := by
  intro u₀
  obtain ⟨hw, hU, hV⟩ := rootHeaderValid_bounds hx hsplit.root_hdr
  obtain ⟨_, h1N, _, hNU⟩ := hev.resolve_left (by simp)
  set off := offCompItems U w N
  set iw := compactedItemWords U V w N 1
  have hfr_eq : x.frontier = base + off + iw := by
    simp [hfr, compactedEpochWords, off, iw, Nat.add_assoc]
  have h225 : 225 ≤ off := le_offCompItems_225 U w N
  have hfit_fr : Fits w x.frontier := hx.frontier_fits
  have hfit_off : Fits w (base + off) := hfit_fr.of_le (by rw [hfr_eq]; linarith only)
  have hfit1 : Fits w 1 := hfit_off.of_le (by linarith only [h225])
  obtain ⟨x₁, hex_hp, hx₁b, hx₁m, hx₁f, hx₁_hp, hx₁_r⟩ :=
    loadBlockUpTo_exec mBase mCur (mReg_ne (by decide)) mOldHp mOldHp_inj
      (fun i => mOldHp_ne_mReg i (Or.inl (by decide)))
      (fun i => mOldHp_ne_mReg i (Or.inl (by decide)))
      offHashParams 18 (by decide) hx le_rfl hbase
      (by change base + 8 + 19 ≤ x.frontier; rw [hfr_eq]; omega)
  have hx₁_base : x₁.regs mBase = base :=
    (hx₁_r mBase (mReg_ne (by decide)) (fun i => mOldHp_ne_mReg i (Or.inl (by decide)))).trans hbase
  obtain ⟨x₂, hex_cp, hx₂b, hx₂m, hx₂f, hx₂_cp, hx₂_r⟩ :=
    loadBlockUpTo_exec mBase mCur (mReg_ne (by decide)) mOldCp mOldCp_inj
      (fun i => mOldCp_ne_mReg i (Or.inl (by decide)))
      (fun i => mOldCp_ne_mReg i (Or.inl (by decide)))
      offCompParams 35 (by decide) hx₁b hx₁f.le hx₁_base
      (by change base + 27 + 36 ≤ x₁.frontier; rw [hx₁f, hfr_eq]; omega)
  have hx₂m_eq : x₂.mem = x.mem := hx₂m.trans hx₁m
  have hx₂f_eq : x₂.frontier = x.frontier := hx₂f.trans hx₁f
  have hx₂_hp_all : ∀ i : Fin 19, x₂.regs (mOldHp i) =
      mkHashParams w (epochQBits U N) (epochHashB N) (totalMicroBits N) 3 i := fun i => by
    rw [hx₂_r (mOldHp i) (mOldHp_ne_mReg i (Or.inl (by decide)))
      (fun j => by intro h; have hv := congrArg Fin.val h; simp at hv; omega),
      hx₁_hp i (by omega)]
    exact hsplit.params_stored.hp_eq i
  have hx₂_cp_all : ∀ i : Fin 36, x₂.regs (mOldCp i) = mkCompParams U V w N i := fun i => by
    rw [hx₂_cp i (by omega), hx₁m]; exact hsplit.params_stored.cp_eq i
  set x₃ := (x₂.set mCnt 1).set mFr 0
  have hex_c1 := RDemonicExec.const (B := .exact) (d := mCnt) (v := 1) (x := x₂) hx₂f_eq.le hfit1
  have hex_zfr := RDemonicExec.const (B := .exact) (d := mFr) (v := 0) (x := x₂.set mCnt 1)
    hx₂f_eq.le (fits_zero w)
  have hx₃b : x₃.Bounded w := (hx₂b.set hfit1).set (fits_zero w)
  have hin_iw : x₃.regs ∘ srcOldIw = WordEncoding.encode (mkCompParams U V w N, 1) := by
    refine (regs_pairSrc (regs_cp_eq fun i => ?_) (regs_reg1_eq mCnt ?_)).eq
    · dsimp only [x₃, RData.set]
      rw [Function.update_of_ne (mOldCp_ne_mReg i (c := 1) (Or.inl (by decide))),
        Function.update_of_ne (mOldCp_ne_mReg i (c := 13) (Or.inl (by decide)))]
      exact hx₂_cp_all i
    · simp [x₃, RData.set]
  have hfit_iw4 : Fits w (4 + iw) := hfit_fr.of_le (by rw [hfr_eq]; linarith only [h225])
  have hsafe_iw : CompItemWordsPre w (mkCompParams U V w N, 1) (memoryState mFr x₃.toData) :=
    ⟨U, V, N, hw, hNU, hU, hV, rfl, fits_wOffQ_add_three_of_itemWords hw hfit_iw4⟩
  have hv_iw := validProg_compItemWordsGen (mkCompParams U V w N, 1)
    (memoryState mFr x₃.toData) ⟨wellFormed_memoryState hx₃b.1, Nat.zero_le _⟩
  obtain ⟨x₄, hex_iw, hx₄b, hx₄f, hm_iw, hout_iw, hframe_iw⟩ :=
    execWitness wItemWords factor_mItemWords_le mFr srcOldIw tmpOldIw
      tmpOldIw_inj srcOldIw_ne_tmp tmpOldIw_ne_mFr srcOldIw_ne_mFr
      (mkCompParams U V w N, 1) hx₃b hx₂f_eq.le hin_iw hsafe_iw hv_iw
      (by rw [clientState_compItemWordsGenProg]; change 0 ≤ x₃.frontier; omega)
  rw [memoryCost_compItemWordsGenProg, zero_add, mul_one] at hex_iw
  rw [clientState_compItemWordsGenProg] at hm_iw
  have hx₄m : x₄.mem = x.mem := (congrArg Memory.State.mem hm_iw).trans hx₂m_eq
  have hx₄f_eq : x₄.frontier = x.frontier := hx₄f.trans hx₂f_eq
  have hx₄_iw : x₄.regs mIwOld = iw := by
    have h0 := hout_iw 0; rwa [tmpOldIw_out, clientResult_compItemWordsGenProg hw] at h0
  have hx₄_keep3 : ∀ reg, reg ≠ mFr → reg.val < 160 → reg ≠ mIwOld → x₄.regs reg = x₃.regs reg :=
    fun reg h1 h160 hiw => hframe_iw reg h1
      (mkTmp_ne_reg _ h160 (fun a => by fin_cases a; exact hiw.symm))
  have hx₄_base : x₄.regs mBase = base :=
    (hx₄_keep3 mBase (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))).trans <|
    (by simp [x₃, RData.set] : x₃.regs mBase = x₂.regs mBase).trans <|
    (hx₂_r mBase (mReg_ne (by decide)) (fun i => mOldCp_ne_mReg i (Or.inl (by decide)))).trans
      hx₁_base
  have hx₄_cp34 : x₄.regs (mOldCp ⟨34, by decide⟩) = off :=
    (hx₄_keep3 _ (by simp [Fin.ext_iff]) (mOldCp_lt_160 _)
      (by simp [Fin.ext_iff])).trans <|
    (by simp [x₃, RData.set, Fin.ext_iff] : x₃.regs _ = x₂.regs _).trans <|
    (hx₂_cp_all _).trans (cpOffItems_mk U V w N)
  set x₅ := x₄.set mItemBase (base + off)
  have hex_ib := RDemonicExec.exactBin (f := .add) (d := mItemBase) (i := mBase)
    (j := mOldCp ⟨34, by decide⟩) (w := w) (L_peak := x.frontier) (x := x₄) hx₄f_eq.le
    (v := base + off)
    (by change some (x₄.regs mBase + x₄.regs (mOldCp ⟨34, by decide⟩)) = some (base + off)
        rw [hx₄_base, hx₄_cp34])
    hfit_off
  set x₆ := x₅.set mFr x.frontier
  have hex_fr := RDemonicExec.exactBin (f := .add) (d := mFr) (i := mItemBase) (j := mIwOld)
    (w := w) (L_peak := x.frontier) (x := x₅) hx₄f_eq.le (v := x.frontier)
    (by simp [BinOp.evalExact, x₅, RData.set, hx₄_iw, hfr_eq]) hfit_fr
  set x₇ := x₆.set mZero 0
  have hex_z := RDemonicExec.const (B := .exact) (d := mZero) (v := 0) (x := x₆) hx₄f_eq.le
    (fits_zero w)
  have hx₇b : x₇.Bounded w := ((hx₄b.set hfit_off).set hfit_fr).set (fits_zero w)
  have hms₇ : memoryState mFr x₇.toData = ⟨x.mem, x.frontier⟩ :=
    Memory.State.ext hx₄m (by simp [memoryState, x₇, x₆, RData.set, RData.toData])
  let d_ro := (((mkHashParams w (qBits U N) (hashB N) (totalMicroBits N) 3,
    mkCompParams U V w N), (base, base + off)), 0)
  have hx₇_x₂ : ∀ reg, reg.val < 160 →
      reg ∉ ([mZero, mFr, mItemBase, mIwOld, mCnt] : List (Fin rResize)) →
      x₇.regs reg = x₂.regs reg := fun reg h160 h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    obtain ⟨hz, hfr', hib, hiw, hcnt⟩ := h
    simp [x₇, x₆, x₅, x₃, RData.set, hz, hfr', hib, hx₄_keep3 reg hfr' h160 hiw, hcnt]
  have hin_ro : x₇.regs ∘ srcReadOldKV = WordEncoding.encode d_ro := by
    refine (regs_pairSrc
      (regs_pairSrc
        (regs_pairSrc (regs_hp_eq fun i => ?_) (regs_cp_eq fun i => ?_))
        (regs_pairSrc (regs_reg1_eq mBase (by simp [x₇, x₆, x₅, RData.set, hx₄_base]))
          (regs_reg1_eq mItemBase (by simp [x₇, x₆, x₅, RData.set]))))
      (regs_reg1_eq mZero (by simp [x₇, RData.set]))).eq
    · exact (hx₇_x₂ _ (mOldHp_lt_160 i) (by clear * -; simp [Fin.ext_iff]; omega)).trans
        (hx₂_hp_all i)
    · exact (hx₇_x₂ _ (mOldCp_lt_160 i) (by clear * -; simp [Fin.ext_iff]; omega)).trans
        (hx₂_cp_all i)
  obtain ⟨s_fix, hinv, htot, hcpl⟩ := hsplit.coupled
  obtain ⟨L_b, hb_inv⟩ := hinv.hbucket
  have hslot : SlotStoreInv N (compGmAt base U w N x.mem) := hcpl.gm_eq ▸ hb_inv.hslot
  obtain ⟨hrec_val, _, _⟩ := reconstructKeyAt_spec hsplit.vals_lt hNU hinv hcpl htot
  obtain ⟨hu₀_lt, _, _⟩ := hrec_val 0 zero_lt_one
  obtain ⟨hpre_ro, hvp_ro, hc_ro, hres_ro, hfr_ro, hout_ro⟩ :=
    readOldItemKeyValGenProg_spec (s₀ := ⟨x.mem, x.frontier⟩) hw h1N hNU hsplit.root_hdr.fits_U hV
      le_rfl (by change base + off + iw ≤ x.frontier; rw [hfr_eq]) hfit_off hsplit.hash_rep
      hslot hcpl.tailDenseInv htot zero_lt_one hu₀_lt
  have hv_ro : (Memory.spec w).ValidHistory (memoryState mFr x₇.toData)
      ((Memory.spec w).clientHistory (memoryState mFr x₇.toData)
        (readOldItemKeyValGenProg d_ro)) :=
    hms₇.symm ▸ hvp_ro ⟨hms₇ ▸ wellFormed_memoryState hx₇b.1, Nat.zero_le _⟩
  obtain ⟨y, hex_ro, hyb, hyf, hm_ro, hout_reg_ro, hframe_ro⟩ :=
    execWitness wReadOldKV factor_wReadOldKV_le mFr srcReadOldKV tmpReadOldKV
      tmpReadOldKV_inj srcReadOldKV_ne_tmp tmpReadOldKV_ne_mFr srcReadOldKV_ne_mFr
      d_ro hx₇b hx₄f_eq.le hin_ro (hms₇ ▸ hpre_ro) hv_ro
      (by rw [hms₇, hfr_ro]; exact hx₄f_eq.symm.le)
  rw [hms₇] at hm_ro hout_reg_ro hex_ro
  rw [hres_ro] at hout_reg_ro
  have hyf_eq : y.frontier = x.frontier := hyf.trans hx₄f_eq
  have hy_fr_reg : y.regs mFr = x.frontier := (congrArg Memory.State.frontier hm_ro).trans hfr_ro
  have hy_u0 : y.regs mU0 = u₀ := by
    have h0 := hout_reg_ro 0; rwa [tmpReadOldKV_out_0] at h0
  have hy_keep7 : ∀ reg, reg ≠ mFr → reg.val < 160 → reg ≠ mU0 → reg ≠ mV0 →
      y.regs reg = x₇.regs reg := fun reg h1 h160 hu0 hv0 =>
    hframe_ro reg h1
      (mkTmp_ne_reg _ h160 (fun a => by fin_cases a <;> [exact hu0.symm; exact hv0.symm]))
  have hy_argu : y.regs mArgU = x.regs mArgU :=
    (hy_keep7 mArgU (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))
      (mReg_ne (by decide))).trans <| (hx₇_x₂ mArgU (mReg_lt_160 _) (by simp)).trans <|
    (hx₂_r mArgU (mReg_ne (by decide)) (fun i => mOldCp_ne_mReg i (Or.inl (by decide)))).trans
      (hx₁_r mArgU (mReg_ne (by decide)) (fun i => mOldHp_ne_mReg i (Or.inl (by decide))))
  have hc_ro_mul :
      migFactor * (memoryCost (readOldItemKeyValGenProg d_ro) ⟨x.mem, x.frontier⟩ + 1) ≤
        migFactor * 45181 :=
    Nat.mul_le_mul_left migFactor (Nat.add_le_add_right hc_ro 1)
  have hf1 := one_le_migFactor
  have hex_all :=
    hex_hp.seq_eq (hex_cp.seq_eq (hex_c1.seq_eq (hex_zfr.seq_eq (hex_iw.seq_eq
      (hex_ib.seq_eq (hex_fr.seq_eq (hex_z.seq_eq
        (hex_ro.mono hc_ro_mul (fun _ h => h)))))))))
  refine ⟨y, _, hex_all, by linarith only [hf1], hyb, hyf_eq, hy_fr_reg,
    (hy_keep7 mBase (mReg_ne (by decide)) (mReg_lt_160 _) (mReg_ne (by decide))
      (mReg_ne (by decide))).trans (by simp [x₇, x₆, x₅, RData.set, hx₄_base]),
    hy_argu, hy_u0,
    fun a ha => (congrArg (fun s => s.mem a) hm_ro).trans (hout_ro a ha)⟩

private theorem deleteLastHitTailCode_exec {U V w N n_init base : ℕ} {x y : RData rResize}
    (hev : EpochValid U 1 N)
    (hfr : x.frontier = base + compactedEpochWords U V w N 1)
    (hhdr : RootHeaderValid U V w N 1 n_init base x.mem)
    (hyb : y.Bounded w)
    (hyf : y.frontier = x.frontier)
    (hy_fr_reg : y.regs mFr = x.frontier)
    (hy_base : y.regs mBase = base)
    (hy_mem : ∀ a, ¬(base + 63 ≤ a ∧ a < base + 225) → y.mem a = x.mem a) :
    ∃ (z : RData rResize) (steps_h : ℕ),
      RDemonicExec w x.frontier deleteLastHitTailCode y steps_h (· = z) ∧
      steps_h ≤ 5830 ∧
      CompactedRep U V w 0 0 0 base (Dictionary.empty U) z ∧
      z.regs mBase = base ∧
      (∀ addr < base, z.mem addr = x.mem addr) := by
  obtain ⟨hw, hU, hV⟩ := rootHeaderValid_bounds hyb
    (rootHeaderValid_congr hhdr fun a ha => hy_mem a (fun h => by linarith only [ha.2, h.1]))
  obtain ⟨_, _, hN4, hNU⟩ := hev.resolve_left (by simp)
  set off := offCompItems U w N
  set iw := compactedItemWords U V w N 1
  have hfr_eq : x.frontier = base + off + iw := by
    simp [hfr, compactedEpochWords, off, iw, Nat.add_assoc]
  have h225 : 225 ≤ off := le_offCompItems_225 U w N
  have hfit_fr : Fits w x.frontier := hyf ▸ hyb.frontier_fits
  have hfit8 : Fits w 8 := hfit_fr.of_le (by rw [hfr_eq]; linarith only [h225])
  have hfit1 : Fits w 1 := hfit8.of_le (by decide)
  set y₁ := y.set mZero 0
  have hex_z0 := RDemonicExec.const (B := .exact) (d := mZero) (v := 0) (x := y) hyf.le
    (fits_zero w)
  have hy₁b : y₁.Bounded w := hyb.set (fits_zero w)
  obtain ⟨hex_st5, hy₂b⟩ := storeAtOffCode_exec (rAddr := mBase) (rSrc := mZero) (rTmp := mCur)
    (base := base) (off := 5) (val := 0) hy₁b hyf.le (mReg_ne (by decide)) (mReg_ne (by decide))
    (by simp [y₁, RData.set, hy_base]) (by simp [y₁, RData.set]) (hfit8.of_le (by decide))
    (by change base + 5 < y.frontier; rw [hyf, hfr_eq]; omega)
  set y₂ := (y₁.set mCur (base + 5)).write (base + 5) 0
  obtain ⟨hex_st6, hy₃b⟩ := storeAtOffCode_exec (rAddr := mBase) (rSrc := mZero) (rTmp := mCur)
    (base := base) (off := 6) (val := 0) hy₂b hyf.le (mReg_ne (by decide)) (mReg_ne (by decide))
    (by simp [y₂, y₁, RData.set, RData.write, hy_base])
    (by simp [y₂, y₁, RData.set, RData.write])
    (hfit8.of_le (by decide)) (by change base + 6 < y.frontier; rw [hyf, hfr_eq]; omega)
  set y₃ := (y₂.set mCur (base + 6)).write (base + 6) 0
  obtain ⟨hex_st7, hy₄b⟩ := storeAtOffCode_exec (rAddr := mBase) (rSrc := mZero) (rTmp := mCur)
    (base := base) (off := 7) (val := 0) hy₃b hyf.le (mReg_ne (by decide)) (mReg_ne (by decide))
    (by simp [y₃, y₂, y₁, RData.set, RData.write, hy_base])
    (by simp [y₃, y₂, y₁, RData.set, RData.write])
    (hfit8.of_le (by decide)) (by change base + 7 < y.frontier; rw [hyf, hfr_eq]; omega)
  set y₄ := (y₃.set mCur (base + 7)).write (base + 7) 0
  set y₅ := y₄.set mCur 8
  have hex_c8 := RDemonicExec.const (B := .exact) (d := mCur) (v := 8) (x := y₄) hyf.le hfit8
  have hy₄_base : y₄.regs mBase = base := by
    simp [y₄, y₃, y₂, y₁, RData.set, RData.write, hy_base]
  have hy₄_fr : y₄.regs mFr = x.frontier := by
    simp [y₄, y₃, y₂, y₁, RData.set, RData.write, hy_fr_reg]
  have hfit_b8 : Fits w (base + 8) := hfit_fr.of_le (by rw [hfr_eq]; linarith only [h225])
  have hex_add := RDemonicExec.exactBin (f := .add) (d := mCur) (i := mBase) (j := mCur)
    (w := w) (L_peak := x.frontier) (x := y₅) hyf.le (v := base + 8)
    (by simp [BinOp.evalExact, y₅, RData.set, hy₄_base]) hfit_b8
  have hy₆_eq : (y₅.set mCur (base + 8)) = y₄.set mCur (base + 8) := by
    ext j <;> simp [y₅, RData.set]
  have hb8_le : base + 8 ≤ x.frontier := by rw [hfr_eq]; linarith only [h225]
  set y₇ := (y₄.set mCur (base + 8)).set mK (x.frontier - (base + 8))
  have hex_sub := RDemonicExec.exactBin (f := .sub) (d := mK) (i := mFr) (j := mCur)
    (w := w) (L_peak := x.frontier) (x := y₄.set mCur (base + 8)) hyf.le
    (v := x.frontier - (base + 8))
    (by simp [BinOp.evalExact, RData.set, hy₄_fr, hb8_le])
    (hfit_fr.of_le (Nat.sub_le _ _))
  rw [hy₆_eq] at hex_add
  have hy₇b : y₇.Bounded w := (hy₄b.set hfit_b8).set (hfit_fr.of_le (Nat.sub_le _ _))
  have hy₇_k : y₇.regs mK = x.frontier - (base + 8) := by simp [y₇, RData.set]
  have hk_le_fr : y₇.regs mK ≤ y₇.frontier := hyf ▸ hy₇_k ▸ Nat.sub_le _ _
  have hfr_sub : y₇.frontier - y₇.regs mK = base + 8 := by
    change y.frontier - y₇.regs mK = base + 8
    simpa only [hyf, hy₇_k] using Nat.sub_sub_self hb8_le
  have hex_sh := shrinkCode_exec (w := w) (L_peak := x.frontier)
    (count := mK) (idx := mIdx) (zero := mZero) (one := mOne)
    hy₇b mShrink_nodup hfit1 hyf.le hk_le_fr
  rw [hy₇_k] at hex_sh
  set z := shrinkPost mK mIdx mZero mOne y₇
  have hzb : z.Bounded w := shrinkPost_bounded hy₇b hfit1 hk_le_fr
  have hz_lt8 : ∀ a < base + 8, z.mem a = y₄.mem a := fun a ha => by
    change clear y₄.mem (y₇.frontier - y₇.regs mK) (y₇.regs mK) a = y₄.mem a
    rw [hfr_sub]
    exact clear_of_not_owns (by simp only [Block.Owns, not_and_or, not_le]; exact Or.inl ha)
  have hy₄_lt5 : ∀ a < base + 5, y₄.mem a = x.mem a := fun a ha => by
    dsimp only [y₄, y₃, y₂, y₁, RData.write, RData.set]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    exact hy_mem a (fun h => by linarith only [ha, h.1])
  have hhdr_z : RootHeaderValid U V w 0 0 0 base z.mem :=
    ⟨hhdr.fits_U, hhdr.pos_U, hhdr.pos_V,
      (hz_lt8 base (by omega)).trans ((hy₄_lt5 base (by omega)).trans hhdr.hdr_U),
      (hz_lt8 (base + 1) (by omega)).trans ((hy₄_lt5 (base + 1) (by omega)).trans hhdr.hdr_V),
      (hz_lt8 (base + 2) (by omega)).trans ((hy₄_lt5 (base + 2) (by omega)).trans hhdr.hdr_w),
      (hz_lt8 (base + 3) (by omega)).trans ((hy₄_lt5 (base + 3) (by omega)).trans hhdr.hdr_keyBits),
      (hz_lt8 (base + 4) (by omega)).trans ((hy₄_lt5 (base + 4) (by omega)).trans hhdr.hdr_valBits),
      (hz_lt8 (base + 5) (by omega)).trans (by simp [y₄, y₃, y₂, RData.write, RData.set]),
      (hz_lt8 (base + 6) (by omega)).trans (by simp [y₄, y₃, RData.write, RData.set]),
      (hz_lt8 (base + 7) (by omega)).trans (by simp [y₄, RData.write, RData.set])⟩
  have hoff_lin : off ≤ 1447 :=
    (offCompItems_le_linear hw hNU hhdr.fits_U).trans (by linarith only [hN4])
  have hiw_lin : iw ≤ 4 :=
    (compactedItemWords_le_linear (U := U) (V := V) (w := w) (N := N) (n := 1) hw hU.le hV).trans
      (by decide)
  have hc_sh : 4 * (x.frontier - (base + 8)) + 5 ≤ 5810 := by
    clear * - hfr_eq hoff_lin hiw_lin; omega
  have hex_tail :=
    hex_z0.seq_eq (hex_st5.seq_eq (hex_st6.seq_eq (hex_st7.seq_eq
      (hex_c8.seq_eq (hex_add.seq_eq (hex_sub.seq_eq
        (hex_sh.mono hc_sh (fun _ h => h))))))))
  exact ⟨z, _, hex_tail, by linarith only, compactedRep_empty hzb hfr_sub hhdr_z,
    by simp [z, shrinkPost, y₇, RData.set, hy₄_base],
    fun addr haddr => (hz_lt8 addr (by omega)).trans (hy₄_lt5 addr (by omega))⟩

/-- **Deterministic Singleton Delete (`deleteLastOneCode_demonicExec`):**
From an active singleton epoch (`n = 1`, `EpochValid U 1 N`) at `base` with seed `θ`:
* when `(s_abs u).isSome` (`Function.update s_abs u none = Dictionary.empty U`), `deleteLastOneCode`
  collapses to the 8-word empty `CompactedRep U V w 0 0 0` in `≤ deleteLastOneCharge` steps;
* when `¬(s_abs u).isSome` (`Function.update s_abs u none = s_abs`), `deleteLastOneCode` preserves
  `CompactedSplitRep` with the **same** seed `θ` and unchanged `inEpochPotential` in
  `≤ deleteLastOneCharge` steps. -/
theorem deleteLastOneCode_demonicExec {U V w N n_init base : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} (u : Fin U) {x : RData rResize}
    (hx : x.Bounded w) (hev : EpochValid U 1 N)
    (hfr : x.frontier = base + compactedEpochWords U V w N 1)
    (hsplit : CompactedSplitRep base (base + offCompItems U w N) U V w N 1 n_init θ s_abs
      ⟨x.mem, x.frontier⟩)
    (hbase : x.regs mBase = base)
    (hu_reg : x.regs mArgU = u.val) :
    ∃ (z : RData rResize) (steps : ℕ),
      RDemonicExec w x.frontier deleteLastOneCode x steps (· = z) ∧
      z.Bounded w ∧
      z.regs mBase = base ∧
      (∀ addr < base, z.mem addr = x.mem addr) ∧
      (if (s_abs u).isSome then
        Function.update s_abs u none = Dictionary.empty U ∧
        CompactedRep U V w 0 0 0 base (Dictionary.empty U) z ∧
        steps ≤ deleteLastOneCharge
      else
        Function.update s_abs u none = s_abs ∧
        z.frontier = base + compactedEpochWords U V w N 1 ∧
        CompactedSplitRep base (base + offCompItems U w N) U V w N 1 n_init θ s_abs
          ⟨z.mem, z.frontier⟩ ∧
        inEpochPotential U w N base z = inEpochPotential U w N base x ∧
        steps ≤ deleteLastOneCharge) := by
  obtain ⟨hw, _, _⟩ := rootHeaderValid_bounds hx hsplit.root_hdr
  obtain ⟨_, _, _, hNU⟩ := hev.resolve_left (by simp)
  obtain ⟨s_fix, hinv, htot, hcpl⟩ := hsplit.coupled
  obtain ⟨hrec_val, _, hrec_surj⟩ := reconstructKeyAt_spec hsplit.vals_lt hNU hinv hcpl htot
  obtain ⟨hu₀_lt, hs₀, _⟩ := hrec_val 0 zero_lt_one
  set u₀ := reconstructKeyAt base (base + offCompItems U w N) U V w N 1 θ x.mem 0
  obtain ⟨y, steps_r, hex_r, hc_r, hyb, hyf, hy_fr_reg, hy_base, hy_argu, hy_u0, hy_mem⟩ :=
    deleteLastReadCode_exec hx hev hfr hsplit hbase
  have hf1 := one_le_migFactor
  by_cases hsome : (s_abs u).isSome
  · obtain ⟨d, hd, hd_eq⟩ := hrec_surj u hsome
    obtain rfl : d = 0 := Nat.lt_one_iff.mp hd
    change u₀ = u.val at hd_eq
    have hc_eq : (Cond.eq mU0 mArgU).Holds y.toData := by
      simpa only [Cond.Holds, RData.toData, hy_u0, hy_argu, hu_reg] using hd_eq
    obtain ⟨z, steps_h, hex_h, hc_h, hrep_z, hz_base, hbelow_z⟩ :=
      deleteLastHitTailCode_exec hev hfr hsplit.root_hdr hyb hyf hy_fr_reg hy_base hy_mem
    have hs_empty : Function.update s_abs u none = Dictionary.empty U := funext fun k => by
      by_cases hku : k = u
      · simp [hku, Dictionary.empty]
      · rw [Function.update_of_ne hku]
        exact Option.not_isSome_iff_eq_none.mp fun hk => by
          obtain ⟨d', hd', hd'_eq⟩ := hrec_surj k hk
          rw [Nat.lt_one_iff.mp hd'] at hd'_eq
          exact hku (Fin.ext (hd'_eq.symm.trans hd_eq))
    refine ⟨z, _, hex_r.seq_eq (RDemonicExec.branch_pos hc_eq hex_h),
      hrep_z.bounded, hz_base, hbelow_z, ?_⟩
    rw [ite_eq_left hsome]
    refine ⟨hs_empty, hrep_z, ?_⟩
    unfold deleteLastOneCharge
    linarith only [hc_r, hc_h, hf1]
  · have hnc_eq : ¬(Cond.eq mU0 mArgU).Holds y.toData := fun h =>
      hsome ((Fin.ext (hy_u0.symm.trans (h.trans (hy_argu.trans hu_reg))) :
        (⟨u₀, hu₀_lt⟩ : Fin U) = u) ▸ hs₀ ▸ rfl)
    have hex_nop := RDemonicExec.copy (B := .exact) (w := w) (L_peak := x.frontier)
      (d := mZero) (s := mZero) (x := y) hyf.le
    set z := y.set mZero (y.regs mZero)
    have hs_same : Function.update s_abs u none = s_abs :=
      Function.update_eq_self_iff.mpr (Option.not_isSome_iff_eq_none.mp hsome).symm
    have hout_scr : ∀ a, (a < base + offScratch ∨ base + epochHdrWords ≤ a) → z.mem a = x.mem a :=
      fun a ha => hy_mem a (by unfold offScratch epochHdrWords at ha; omega)
    refine ⟨z, _, hex_r.seq_eq (RDemonicExec.branch_neg hnc_eq hex_nop),
      hyb.set (hyb.regs_fits mZero), by simp [z, RData.set, hy_base],
      fun addr haddr => hy_mem addr (fun h => by linarith only [haddr, h.1]), ?_⟩
    rw [ite_eq_right hsome]
    refine ⟨hs_same, hyf.trans hfr, compactedSplitRep_of_scratch_mod hw hsplit hyf hout_scr,
      by simp only [inEpochPotential, compGmAt_eq_of_scratch_mod hw hout_scr], ?_⟩
    unfold deleteLastOneCharge
    linarith only [hc_r, hf1]

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
