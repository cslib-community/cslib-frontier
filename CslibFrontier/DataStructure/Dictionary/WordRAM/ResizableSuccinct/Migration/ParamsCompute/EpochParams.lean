/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.InEpoch
import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.ParamsCompute.Primitives
import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.ParamsCompute.HashParams
import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.ParamsCompute.Scales
import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.ParamsCompute.CompParams

/-!
# Top-Level 63-Word Active Epoch Parameter Writer (`writeEpochParamsGenProg`)

Assembles `writeRootHdrSubProg`, `computeLogScalesProg`, `writeHashParamsSubProg`, and
`writeCompParamsSubProg` into the parameter-free (`¬ReadsWidth`) `Memory.Prog` subroutine
`writeEpochParamsGenProg` populating `[dstMetaBase, dstMetaBase + 63)` in `O(N)` (`≤ 11 * N + 100`)
operations via `RealizesBounded .exact`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.writeEpochParamsGenProg`,
  `WriteEpochParamsPre`: parameter-free `Memory.Prog` writer for the 63-word active epoch parameter
  header `[dstMetaBase, dstMetaBase + 63)` and its entry precondition.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.writeEpochParamsGenProg_spec`,
  `realizesBounded_writeEpochParamsGen`: functional specification (`≤ 11 * N + 100` cost bound) and
  `RealizesBounded .exact` compilation certificate.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.ParamsComputeAux

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure

/-- Populate the 8-word root header, 19-word `HashParams`, and 36-word `CompParams` at
`[dstMetaBase, dstMetaBase + 63)` from `[srcHdrBase, srcHdrBase + 5)` and `(N, n_cur, n_init_new)`,
returning `(offCompItems U w N, epochHashSpace U w N)` (`¬ReadsWidth`). -/
def writeEpochParamsGenProg : (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.Prog (ℕ × ℕ)
  | ((srcHdrBase, dstMetaBase), (N, (n_cur, n_init_new))) => do
    let (wVal, (kBits, vBits)) ←
      writeRootHdrSubProg ((srcHdrBase, dstMetaBase), (N, (n_cur, n_init_new)))
    let (logN, (qBitsVal, llf)) ← computeLogScalesProg (dstMetaBase, (N, kBits))
    let hSpace ← writeHashParamsSubProg ((dstMetaBase, dstMetaBase), (wVal, (qBitsVal, logN)))
    let offItemsVal ← writeCompParamsSubProg
      ((dstMetaBase, (wVal, N)), ((qBitsVal, vBits), (logN, (llf, hSpace))))
    pure (offItemsVal, hSpace)

/-- Entry precondition for `writeEpochParamsGenProg`. -/
@[expose] def WriteEpochParamsPre (w : ℕ) :
    (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.State → Prop
  | ((srcHdrBase, dstMetaBase), (N, (n_cur, n_init_new))), s =>
    ∃ U V N_old n_old n_init_old,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ V ≤ 2 ^ w ∧
      Fits w n_cur ∧ Fits w n_init_new ∧
      RootHeaderValid U V w N_old n_old n_init_old srcHdrBase s.mem ∧
      srcHdrBase + 5 ≤ s.frontier ∧
      dstMetaBase + 63 ≤ s.frontier ∧
      Fits w (dstMetaBase + offCompItems U w N)

/-- Functional specification and `≤ 11 * N + 100` cost bound for `writeEpochParamsGenProg`. -/
theorem writeEpochParamsGenProg_spec
    {w U V N_old n_old n_init_old srcHdrBase dstMetaBase N n_cur n_init_new : ℕ}
    {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hV : V ≤ 2 ^ w)
    (hfit_ncur : Fits w n_cur) (hfit_ninit : Fits w n_init_new)
    (hhdr : RootHeaderValid U V w N_old n_old n_init_old srcHdrBase s.mem)
    (hsrc_fr : srcHdrBase + 5 ≤ s.frontier)
    (hdst_fr : dstMetaBase + 63 ≤ s.frontier)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let d := ((srcHdrBase, dstMetaBase), (N, (n_cur, n_init_new)))
    let prog := writeEpochParamsGenProg d
    let s' := (Memory.spec 0).clientState s prog
    WriteEpochParamsPre w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    (Memory.spec 0).clientResult s prog = (offCompItems U w N, epochHashSpace U w N) ∧
    s'.frontier = s.frontier ∧
    RootHeaderValid U V w N n_cur n_init_new dstMetaBase s'.mem ∧
    EpochParamsStored U V w N dstMetaBase s'.mem ∧
    (∀ a, ¬(dstMetaBase ≤ a ∧ a < dstMetaBase + offScratch) → s'.mem a = s.mem a) ∧
    memoryCost prog s ≤ 11 * N + 100 := by
  intro d prog s'
  have hU := hhdr.fits_U
  have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
  have hdst8 : dstMetaBase + 8 ≤ s.frontier := by omega
  obtain ⟨_, hv_r, hres_r, hfr_r, hhdr_r, hframe_r, hc_r⟩ :=
    writeRootHdrSubProg_spec hhdr hV (hU.of_le hNU) hfit_ncur hfit_ninit (h225.of_le (by decide))
      hsrc_fr hdst8
  set s1 := (Memory.spec 0).clientState s
    (writeRootHdrSubProg ((srcHdrBase, dstMetaBase), (N, (n_cur, n_init_new))))
  have hdst_fr1 : dstMetaBase + 63 ≤ s1.frontier := hfr_r.symm ▸ hdst_fr
  have hdst_lt1 : dstMetaBase < s1.frontier := by omega
  obtain ⟨hv_ls, hst_ls, hres_ls, hc_ls⟩ :=
    computeLogScalesProg_exec (s := s1) hw hN hNU hU hdst_lt1 h225
  obtain ⟨hv_hp, hres_hp, hfr_hp, hmem_hp, hframe_hp, hc_hp⟩ :=
    writeHashParamsSubProg_props (s := s1) hw hN hNU hU hdst_lt1 (by omega) hfit_dst
  set s2 := (Memory.spec 0).clientState s1
    (writeHashParamsSubProg ((dstMetaBase, dstMetaBase), (w, (quotientBits U N, Nat.log 2 N))))
  have hdst_fr2 : dstMetaBase + 63 ≤ s2.frontier := hfr_hp.symm ▸ hdst_fr1
  obtain ⟨hv_cp, hres_cp, hfr_cp, hmem_cp, hframe_cp, hc_cp⟩ :=
    writeCompParamsSubProg_props (s := s2) hw hN hNU hU hV hdst_fr2 hfit_dst
  set s3 := (Memory.spec 0).clientState s2
    (writeCompParamsSubProg ((dstMetaBase, (w, N)),
      ((quotientBits U N, valBits V),
        (Nat.log 2 N, (Dynamic.logLogFactor N, epochHashSpace U w N)))))
  have hs'_eq : s' = s3 := by
    dsimp only [s', prog, d, writeEpochParamsGenProg]
    rw [StateTransitionSpec.clientState_bind, hres_r]
    dsimp only
    rw [StateTransitionSpec.clientState_bind, hst_ls, hres_ls]
    dsimp only
    rw [StateTransitionSpec.clientState_bind, hres_hp, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_pure]
  refine ⟨⟨U, V, N_old, n_old, n_init_old, hw, hN, hNU, hV, hfit_ncur, hfit_ninit, hhdr,
      hsrc_fr, hdst_fr, hfit_dst⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [prog, d, writeEpochParamsGenProg]
    rw [validHistory_bind']; refine ⟨hv_r, ?_⟩
    rw [hres_r]; dsimp only
    rw [validHistory_bind']; refine ⟨hv_ls, ?_⟩
    rw [hst_ls, hres_ls]; dsimp only
    rw [validHistory_bind']; refine ⟨hv_hp, ?_⟩
    rw [hres_hp, validHistory_bind']; exact ⟨hv_cp, trivial⟩
  · dsimp only [prog, d, writeEpochParamsGenProg]
    rw [prog_clientResult_bind, hres_r]
    change (Memory.spec 0).clientResult s1 _ = _
    dsimp only
    rw [prog_clientResult_bind, hst_ls, hres_ls]
    dsimp only
    rw [prog_clientResult_bind, hres_hp]
    change (Memory.spec 0).clientResult s2 _ = _
    rw [prog_clientResult_bind, hres_cp, prog_clientResult_pure]
  · rw [hs'_eq, hfr_cp, hfr_hp, hfr_r]
  · rw [hs'_eq]
    have h0_7 : ∀ j < 8, s3.mem (dstMetaBase + j) = s1.mem (dstMetaBase + j) := fun j hj => by
      rw [hframe_cp _ (by unfold offCompParams offScratch; omega),
        hframe_hp _ (by unfold offHashParams offCompParams; omega)]
    exact ⟨hhdr_r.fits_U, hhdr_r.pos_U, hhdr_r.pos_V,
      by simpa using (h0_7 0 (by decide)).trans hhdr_r.hdr_U,
      (h0_7 1 (by decide)).trans hhdr_r.hdr_V,
      (h0_7 2 (by decide)).trans hhdr_r.hdr_w,
      (h0_7 3 (by decide)).trans hhdr_r.hdr_keyBits,
      (h0_7 4 (by decide)).trans hhdr_r.hdr_valBits,
      (h0_7 5 (by decide)).trans hhdr_r.hdr_N,
      (h0_7 6 (by decide)).trans hhdr_r.hdr_n,
      (h0_7 7 (by decide)).trans hhdr_r.hdr_n_init⟩
  · rw [hs'_eq]
    refine ⟨fun i => ?_, hmem_cp⟩
    rw [hframe_cp _ (by have := i.isLt; unfold offHashParams offCompParams offScratch; omega)]
    exact hmem_hp i
  · intro a ha
    rw [hs'_eq, hframe_cp a (by unfold offCompParams offScratch at *; omega),
      hframe_hp a (by unfold offHashParams offCompParams offScratch at *; omega),
      hframe_r a (by unfold offScratch at ha; omega)]
  · dsimp only [prog, d, writeEpochParamsGenProg]
    rw [Realization.memoryCost_bind', hres_r, Realization.memoryCost_bind', hst_ls, hres_ls]
    dsimp only
    rw [Realization.memoryCost_bind', hres_hp, Realization.memoryCost_bind', memoryCost_pure]
    change memoryCost (writeRootHdrSubProg _) s +
      (memoryCost (computeLogScalesProg _) s1 +
        (memoryCost (writeHashParamsSubProg _) s1 +
          (memoryCost (writeCompParamsSubProg _) s2 + 0))) ≤ _
    omega

/-- `writeEpochParamsGenProg` compiles via `RealizesBounded .exact`. -/
theorem realizesBounded_writeEpochParamsGen :
    RealizesBounded .exact writeEpochParamsGenProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ × ℕ))
      WriteEpochParamsPre (fun _ _ => 0) := by
  have hr := realizesBounded_writeRootHdrSub
  have hls := realizesBounded_computeLogScales
  have hhp := realizesBounded_writeHashParamsSub
  have hcp := realizesBounded_writeCompParamsSub
  realize
  all_goals (
    rcases d with ⟨⟨srcHdrBase, dstMetaBase⟩, ⟨N, ⟨n_cur, n_init_new⟩⟩⟩
    obtain ⟨U, V, N_old, n_old, n_init_old, hw, hN, hNU, hV, hnc, hni, hhdr,
      hsrc_fr, hdst_fr, hfit_dst⟩ := h
    dsimp only at *
    have hU := hhdr.fits_U
    have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
    have hdst8 : dstMetaBase + 8 ≤ s.frontier := by omega
    obtain ⟨hpre_r, _, hres_r, hfr_r, _, _, _⟩ :=
      writeRootHdrSubProg_spec hhdr hV (hU.of_le hNU) hnc hni (h225.of_le (by decide))
        hsrc_fr hdst8)
  · exact hpre_r
  · rw [hres_r]
    exact ⟨U, hw, hN, hNU, hU, rfl, by rw [hfr_r]; omega, h225⟩
  · rw [hres_r]
    set s1 := (Memory.spec 0).clientState s
      (writeRootHdrSubProg ((srcHdrBase, dstMetaBase), (N, (n_cur, n_init_new))))
    have hdst_lt1 : dstMetaBase < s1.frontier := by rw [hfr_r]; omega
    obtain ⟨_, hst_ls, hres_ls, _⟩ :=
      computeLogScalesProg_exec (s := s1) hw hN hNU hU hdst_lt1 h225
    rw [hst_ls, hres_ls]
    exact ⟨U, N, hw, hN, hNU, hU, rfl, rfl, rfl, hdst_lt1, by rw [hfr_r]; omega, hfit_dst⟩
  · rw [hres_r]
    set s1 := (Memory.spec 0).clientState s
      (writeRootHdrSubProg ((srcHdrBase, dstMetaBase), (N, (n_cur, n_init_new))))
    have hdst_lt1 : dstMetaBase < s1.frontier := by rw [hfr_r]; omega
    obtain ⟨_, hst_ls, hres_ls, _⟩ :=
      computeLogScalesProg_exec (s := s1) hw hN hNU hU hdst_lt1 h225
    rw [hst_ls, hres_ls]
    obtain ⟨_, hres_hp, hfr_hp, _, _, _⟩ :=
      writeHashParamsSubProg_props (s := s1) hw hN hNU hU hdst_lt1 (by rw [hfr_r]; omega) hfit_dst
    rw [hres_hp]
    exact ⟨U, V, hw, hN, hNU, hU, hV, rfl, rfl, rfl, rfl, rfl, rfl,
      hfr_hp.symm ▸ hfr_r.symm ▸ hdst_fr, hfit_dst⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
