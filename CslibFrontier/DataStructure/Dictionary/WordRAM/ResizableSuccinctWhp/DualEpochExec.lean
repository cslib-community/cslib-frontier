/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochDist
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map

/-!
# 5-Regime Mutation Preservation and End-to-End WHP Execution (`DualEpochExec`)

Proves 5-regime mutation preservation (`dualDistInv_step_mutate`) across all 12 phases (`0..11`) of
the deamortized dual-epoch resizable succinct dynamic dictionary of
[Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 3–6][BenderFarachColtonKuszmaulKuszmaul2024], instantiates
`Resizable.Randomized.HighProbStateTransitionImpl` and `HighProbObliviousImpl`, and proves the
end-to-end sequence-level worst-case `O_c(1)` time with high probability
(`1 - ∑_t max(n_t, T)^(-c)`) and strict `1 · OPT` succinct space theorems over both `Basis.exact`
and `Basis.standard`.

## Main definitions

* `highProbStateImpl`: `HighProbStateTransitionImpl` package over `Basis.exact`.
* `highProbImpl`, `highProbImplStandard`: `HighProbObliviousImpl` packages over `Basis.exact` and
  `Basis.standard`.

## Main results

* `dualDistInv_step_mutate`
* `w_mul_spaceBoundWhp_le_bits`, `w_mul_stepSuccinctPeakWordsWhp_le_bits`,
  `obliviousPeakFits_of_succinctWords`
* `seq_whp_succinct`, `seq_whp_succinct_standard`

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–6][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.WordRAM.Resizable
open Cslib.DataStructure.WordRAM.Resizable.Randomized
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.Dynamic
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.Probability
open EpochUpdate
open scoped ENNReal

/-! ## Section 1: 5-Regime Mutation Preservation of `DualDistInv` -/

private theorem applyFG_false_evs {c U V : ℕ} (opTag : ℕ) (u : Fin U) (v : Fin V)
    (sl : SlotLatent c U V) :
    (sl.applyFG false opTag u v).evs =
      sl.evs ++ [if opTag = 1 then .insert u v else .delete u] := by
  unfold SlotLatent.applyFG
  simp only [Bool.false_eq_true, ↓reduceIte]
  split_ifs <;> rfl

private theorem applyFG_seeds_heq {c U V : ℕ} (draining : Bool) (opTag : ℕ)
    (u : Fin U) (v : Fin V) (sl : SlotLatent c U V) :
    HEq (sl.applyFG draining opTag u v).seeds sl.seeds := by
  suffices ∃ s' e', sl.applyFG draining opTag u v = ⟨sl.nCap, s', sl.seeds, e'⟩ by
    obtain ⟨_, _, h⟩ := this; rw [h]
  unfold SlotLatent.applyFG; split_ifs <;> exact ⟨_, _, rfl⟩

private theorem seedsOfWords_heq {c U w n₁ n₂ : ℕ} (hn : n₁ = n₂)
    (f₁ : SeedWords c w n₁) (f₂ : SeedWords c w n₂)
    (hf : ∀ (i₁ : Fin (if n₁ = 0 then 0 else offBktMeta c w n₁ - 32))
            (i₂ : Fin (if n₂ = 0 then 0 else offBktMeta c w n₂ - 32)),
          i₁.val = i₂.val → f₁ i₁ = f₂ i₂) :
    HEq (seedsOfWords c U w n₁ f₁) (seedsOfWords c U w n₂ f₂) := by
  subst hn
  exact heq_of_eq (congrArg (seedsOfWords c U w n₁) (funext fun i => hf i i rfl))

private theorem preShrink_congr_st {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s₁ s₂ : Memory.State}
    (h : DualPreShrinkInv c U V w base s_dict L s₁) (heq : s₁ = s₂) :
    DualPreShrinkInv c U V w base s_dict L s₂ :=
  heq ▸ h

private theorem stateInv_congr_st {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s₁ s₂ : Memory.State}
    (h : DualStateInv c U V w base s_dict L s₁) (heq : s₁ = s₂) :
    DualStateInv c U V w base s_dict L s₂ :=
  heq ▸ h

private theorem stateInv_congr_dict {c U V w base : ℕ} {d₁ d₂ : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualStateInv c U V w base d₁ L s) (heq : d₁ = d₂) :
    DualStateInv c U V w base d₂ L s :=
  heq ▸ h

private abbrev MutateStepPost (c U V w base : ℕ) (s_dict : Dictionary.State U) (o : Dynamic.Op U)
    (ν : PMF (LatentRState (DualLatent c U V) rWhp)) : Prop :=
  ∃ μ_step : LatentRState (DualLatent c U V) rWhp →
      PMF (WhpStepROutcome (DualLatent c U V) ((Dynamic.spec U V U).Result o) rWhp),
    (∀ t ∈ ν.support,
      ExecRCodeSteps w opCodeWhp
        ((subroutineCodeWhp c U V w).prepare whpEncode o t.data)
        ((μ_step t).map WhpStepROutcome.toCodeOutcome)
        (base + stepSuccinctPeakWordsWhp c V w s_dict o) ∧
      ∀ q ∈ (μ_step t).support,
        q.result = ((Dynamic.spec U V U).stepFn s_dict o).2 ∧
        whpDecode (V := V) o q.data.regs = some q.result ∧
        DualRep c U V w base ((Dynamic.spec U V U).stepFn s_dict o).1 q.latent q.data ∧
        (∀ addr < base, q.data.mem addr = t.data.mem addr)) ∧
    DualDistInv c U V w base ((Dynamic.spec U V U).stepFn s_dict o).1
      (ν.bind fun t => (μ_step t).map fun q => ⟨q.latent, q.data⟩) ∧
    (ν.bind μ_step).toOuterMeasure {q | ¬q.WithinBudget (worstCaseTimeWhp c)} ≤
      stepFailureProbWhp c s_dict o

private theorem toOuterMeasure_map_bad_eq_zero {β γ : Type*} (μ : PMF β) (g : β → γ)
    (S : Set γ) (h : ∀ b, g b ∉ S) :
    (μ.map g).toOuterMeasure S = 0 := by
  have hemp : g ⁻¹' S = ∅ := Set.eq_empty_iff_forall_notMem.mpr h
  rw [PMF.toOuterMeasure_map_apply, hemp, MeasureTheory.measure_empty]

private noncomputable def qDetNon58 {c U V w base opTag v_val : ℕ}
    (s_dict : Dictionary.State U) (o : Dynamic.Op U)
    (hv : (Dynamic.spec U V U).valid s_dict o)
    (hfit_peak : Fits w (base + stepSuccinctPeakWordsWhp c V w s_dict o))
    (u : Fin U) (v : Fin V)
    (ho_mut : (o = .insert u v.val ∧ opTag = 1 ∧ v_val = v.val) ∨
      (o = .delete u ∧ opTag = 2 ∧ v_val = 0))
    (t : LatentRState (DualLatent c U V) rWhp) :
    WhpStepROutcome (DualLatent c U V) ((Dynamic.spec U V U).Result o) rWhp := by
  classical
  exact
    if h : DualRep c U V w base s_dict t.latent t.data ∧
        t.data.mem (base + hdrPhase) ≠ 5 ∧ t.data.mem (base + hdrPhase) ≠ 8 then
      let hs := opCodeWhp_mutate_non58_exec h.1 o hv hfit_peak u v ho_mut h.2.1 h.2.2
      ⟨hs.choose_spec.choose_spec.choose_spec.choose, hs.choose,
        ((Dynamic.spec U V U).stepFn s_dict o).2, hs.choose_spec.choose, true⟩
    else ⟨t.latent, t.data, ((Dynamic.spec U V U).stepFn s_dict o).2, 0, true⟩

private theorem mutate_setup_bounds {c U V w base opTag v_val : ℕ}
    {s_dict : Dictionary.State U} {o : Dynamic.Op U} {u : Fin U} {v : Fin V}
    (ho_mut : (o = .insert u v.val ∧ opTag = 1 ∧ v_val = v.val) ∨
      (o = .delete u ∧ opTag = 2 ∧ v_val = 0))
    (hfit_peak : Fits w (base + stepSuccinctPeakWordsWhp c V w s_dict o))
    {L_rep : DualLatent c U V} {s_rep : Memory.State}
    (hinv_rep : DualStateInv c U V w base s_dict L_rep s_rep) :
    opTag ≠ 0 ∧
    (opTag = 1 → v_val = v.val) ∧
    ((if opTag = 1 then Function.update s_dict u (some v.val)
      else Function.update s_dict u none) = ((Dynamic.spec U V U).stepFn s_dict o).1) ∧
    base + spaceBoundWhp c V w
      (if opTag = 1 then Function.update s_dict u (some v.val)
       else Function.update s_dict u none) < 2 ^ w ∧
    base + dualPaddedWords c U V w (s_rep.mem (base + hdrNSrc))
      (if s_rep.mem (base + hdrPhase) = 0 then s_rep.mem (base + hdrNSrc)
       else s_rep.mem (base + hdrNDst))
      (Dictionary.dom (if opTag = 1 then Function.update s_dict u (some v.val)
        else Function.update s_dict u none)).card < 2 ^ w := by
  have hop_nz : opTag ≠ 0 := by rcases ho_mut with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> decide
  have hv_eq : opTag = 1 → v_val = v.val := by
    rcases ho_mut with ⟨_, _, hv_v⟩ | ⟨_, rfl, _⟩
    · exact fun _ => hv_v
    · intro h; cases h
  have hs_dict'_eq :
      (if opTag = 1 then Function.update s_dict u (some v.val)
       else Function.update s_dict u none) = ((Dynamic.spec U V U).stepFn s_dict o).1 := by
    rcases ho_mut with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ <;> rfl
  obtain ⟨_, hpad'_le⟩ := dualPaddedWords_step_le_peak hinv_rep hop_nz u v
  have hsucc_fits' :
      base + spaceBoundWhp c V w
        (if opTag = 1 then Function.update s_dict u (some v.val)
         else Function.update s_dict u none) < 2 ^ w := by
    rw [hs_dict'_eq]
    exact lt_of_le_of_lt (Nat.add_le_add_left (le_max_right _ _) base) hfit_peak
  exact ⟨hop_nz, hv_eq, hs_dict'_eq, hsucc_fits',
    lt_of_le_of_lt (Nat.add_le_add_left hpad'_le base) hsucc_fits'⟩

private theorem dualDistInv_mutate_le4 {c U V w base opTag v_val : ℕ}
    (s_dict : Dictionary.State U) (o : Dynamic.Op U)
    (hv : (Dynamic.spec U V U).valid s_dict o)
    (u : Fin U) (v : Fin V)
    (ho_mut : (o = .insert u v.val ∧ opTag = 1 ∧ v_val = v.val) ∨
      (o = .delete u ∧ opTag = 2 ∧ v_val = 0))
    (ν : PMF (LatentRState (DualLatent c U V) rWhp))
    (hfit_peak : Fits w (base + stepSuccinctPeakWordsWhp c V w s_dict o))
    {L_rep : DualLatent c U V} {s_rep : Memory.State}
    (hinv_rep : DualStateInv c U V w base s_dict L_rep s_rep)
    (hp4 : s_rep.mem (base + hdrPhase) ≤ 4)
    (hregimes : SingleEpochLaw c U V w base s_dict s_rep (dualCapSrc base s_rep.mem) false ν) :
    MutateStepPost c U V w base s_dict o ν := by
  classical
  set s_dict' := ((Dynamic.spec U V U).stepFn s_dict o).1
  set res_o := ((Dynamic.spec U V U).stepFn s_dict o).2
  obtain ⟨hop_nz, hv_eq, hs_dict'_eq, hsucc_fits', hpad_rep_fits'⟩ :=
    mutate_setup_bounds ho_mut hfit_peak hinv_rep
  let fgEv : EpochUpdate U V := if opTag = 1 then .insert u v else .delete u
  have hUw : Fits w U := hinv_rep.U_lt
  set ph := s_rep.mem (base + hdrPhase)
  set capSrc := dualCapSrc base s_rep.mem
  have hsrc_safe := dualCapSrc_safe hinv_rep
  obtain ⟨α, μ_idx, evs_of, f_act, hν, hf⟩ := hregimes
  obtain ⟨a₀, ha₀⟩ := μ_idx.support_nonempty
  let t₀ := f_act a₀ (zeroSeedWords c w capSrc)
  obtain ⟨hr₀, hsch₀, _, _, _⟩ := hf a₀ ha₀ (zeroSeedWords c w capSrc)
  let stepNon58 : ∀ {t : LatentRState (DualLatent c U V) rWhp}
      (hr : DualRep c U V w base s_dict t.latent t.data)
      (hne5 : t.data.mem (base + hdrPhase) ≠ 5)
      (hne8 : t.data.mem (base + hdrPhase) ≠ 8), _ := fun hr hne5 hne8 =>
    opCodeWhp_mutate_non58_exec hr o hv hfit_peak u v ho_mut hne5 hne8
  let q_det := qDetNon58 s_dict o hv hfit_peak u v ho_mut
  let μ_step := fun t => PMF.pure (q_det t)
  have hsupp_le4 : ∀ t ∈ ν.support,
      DualRep c U V w base s_dict t.latent t.data ∧
      SchedEq base s_rep (rMemState t.data) ∧
      t.data.mem (base + hdrPhase) ≤ 4 := by
    intro t ht; rw [hν, PMF.mem_support_bind_iff] at ht
    obtain ⟨a, ha, hmt⟩ := ht; rw [PMF.mem_support_map_iff] at hmt
    obtain ⟨ws, _, rfl⟩ := hmt
    obtain ⟨hr, hsch, _, _, _⟩ := hf a ha ws
    have hp_t : (f_act a ws).data.mem (base + hdrPhase) = ph :=
      (hsch.2 hdrPhase (by decide) (by decide)).symm
    exact ⟨hr, hsch, hp_t ▸ hp4⟩
  have hstep_all : ∀ t ∈ ν.support,
      ExecRCodeSteps w opCodeWhp ((subroutineCodeWhp c U V w).prepare whpEncode o t.data)
        ((μ_step t).map WhpStepROutcome.toCodeOutcome)
        (base + stepSuccinctPeakWordsWhp c V w s_dict o) ∧
      ∀ q ∈ (μ_step t).support,
        q.result = res_o ∧ whpDecode (V := V) o q.data.regs = some q.result ∧
        DualRep c U V w base s_dict' q.latent q.data ∧
        (∀ addr < base, q.data.mem addr = t.data.mem addr) := by
    intro t ht
    obtain ⟨hr, _, hle⟩ := hsupp_le4 t ht
    have hc_t : DualRep c U V w base s_dict t.latent t.data ∧
        t.data.mem (base + hdrPhase) ≠ 5 ∧ t.data.mem (base + hdrPhase) ≠ 8 :=
      ⟨hr, by clear *- hle; omega, by clear *- hle; omega⟩
    have hspec := (stepNon58 hr hc_t.2.1 hc_t.2.2).choose_spec.choose_spec.choose_spec.choose_spec
    dsimp only [μ_step, q_det, qDetNon58]; rw [dite_eq_left hc_t, PMF.pure_map]
    refine ⟨hspec.1, fun q hq => ?_⟩
    rw [PMF.mem_support_pure_iff] at hq; subst hq
    exact ⟨rfl, hspec.2.2.2.2.2.2.2.2.2.1, hspec.2.2.1, hspec.2.2.2.2.2.2.2.2.2.2.1⟩
  have hf_post : ∀ a ∈ μ_idx.support, ∀ ws : SeedWords c w capSrc,
      let t := f_act a ws
      let q := q_det t
      DualRep c U V w base s_dict' q.latent q.data ∧
      SchedEq base (rMemState (q_det t₀).data) (rMemState q.data) ∧
      q.latent.slotSrc.nCap = capSrc ∧
      q.latent.slotSrc.evs = evs_of a ++ [fgEv] ∧
      (0 < capSrc → HEq q.latent.slotSrc.seeds (seedsOfWords c U w capSrc ws)) ∧
      ((t.latent.applyFG (t.data.mem (base + hdrPhase)) opTag u v).slotSrc.GoodCovers →
        q.steps ≤ worstCaseTimeWhp c) ∧
      DualMidInv c U V w base s_dict'
        (t.latent.applyFG (t.data.mem (base + hdrPhase)) opTag u v)
        ((Memory.spec 0).clientState
          { mem := ((Memory.spec 0).clientState (rMemState t.data)
              (prepGrowProg (((base, t.data.frontier), opTag), u.val))).mem
            frontier := t.data.frontier +
              (Memory.spec 0).clientResult (rMemState t.data)
                (prepGrowProg (((base, t.data.frontier), opTag), u.val)) }
          (userMutateProg ((base, opTag), (u.val, v_val)))) := by
    intro a ha ws
    obtain ⟨hr, hsch, hnc, hev, hsd⟩ := hf a ha ws
    simp only [Bool.false_eq_true, ↓reduceIte] at hnc hev hsd
    have hp_t : (f_act a ws).data.mem (base + hdrPhase) = ph :=
      (hsch.2 hdrPhase (by decide) (by decide)).symm
    have hc_t : DualRep c U V w base s_dict (f_act a ws).latent (f_act a ws).data ∧
        (f_act a ws).data.mem (base + hdrPhase) ≠ 5 ∧
        (f_act a ws).data.mem (base + hdrPhase) ≠ 8 :=
      ⟨hr, by clear *- hp_t hp4; omega, by clear *- hp_t hp4; omega⟩
    have hc₀ : DualRep c U V w base s_dict t₀.latent t₀.data ∧
        t₀.data.mem (base + hdrPhase) ≠ 5 ∧ t₀.data.mem (base + hdrPhase) ≠ 8 := by
      have hp₀ : t₀.data.mem (base + hdrPhase) = ph :=
        (hsch₀.2 hdrPhase (by decide) (by decide)).symm
      exact ⟨hr₀, by clear *- hp₀ hp4; omega, by clear *- hp₀ hp4; omega⟩
    have hsp := (stepNon58 hr hc_t.2.1 hc_t.2.2).choose_spec.choose_spec.choose_spec.choose_spec
    have hsp₀ := (stepNon58 hr₀ hc₀.2.1 hc₀.2.2).choose_spec.choose_spec.choose_spec.choose_spec
    obtain ⟨hy_mem, hr_post, hmid, hsm_ph, htick_eq, hpre_sh, hpres1, hpres2, _, _, hT⟩ :=
      hsp.2
    have hsm_le4 := hp4
    rw [← hp_t] at hsm_le4
    dsimp only [rMemState] at hsm_ph
    rw [← hsm_ph] at hsm_le4
    have hpre_sh' := preShrink_congr_st hpre_sh htick_eq
    have hcls := bgTick_post_from_le4 hop_nz hmid hsm_le4 hpre_sh'
      (stateInv_congr_st hr_post.2.2.2 (by rw [hy_mem]; dsimp only; rw [htick_eq]))
    obtain ⟨hnc1, hsd1, hev1⟩ := hpres1.1.1 (fun ⟨h9, _⟩ => by clear *- h9 hp_t hp4; omega)
    obtain ⟨hnc2, hsd2, hev2⟩ := hpres2.1.1
      (fun ⟨h11, _⟩ => by rw [htick_eq] at h11; exact hcls.1 h11)
    have hfg_src : ((f_act a ws).latent.applyFG
        ((f_act a ws).data.mem (base + hdrPhase)) opTag u v).slotSrc =
        (f_act a ws).latent.slotSrc.applyFG false opTag u v := by
      unfold DualLatent.applyFG; rw [ite_eq_left (by clear *- hp_t hp4; omega)]
    have hsch_0_t := hsch₀.symm.trans hsch
    have hpad₀ : base + dualPaddedWords c U V w ((rMemState t₀.data).mem (base + hdrNSrc))
        (if (rMemState t₀.data).mem (base + hdrPhase) = 0 then
          (rMemState t₀.data).mem (base + hdrNSrc)
         else (rMemState t₀.data).mem (base + hdrNDst))
        (Dictionary.dom (if opTag = 1 then Function.update s_dict u (some v.val)
          else Function.update s_dict u none)).card < 2 ^ w := by
      rwa [← hsch₀.2 hdrNSrc (by decide) (by decide),
        ← hsch₀.2 hdrPhase (by decide) (by decide),
        ← hsch₀.2 hdrNDst (by decide) (by decide)]
    obtain ⟨_, _, _, hpost_ne5, _⟩ :=
      schedEq_mutate_step (v_val := v_val) hr₀.2.2.2 hr.2.2.2 hsch_0_t hop_nz u v hv_eq
        hsucc_fits' hpad₀
    obtain ⟨_, hsch_post⟩ := hpost_ne5 hc₀.2.1
    have hq_eq : q_det (f_act a ws) =
        ⟨(stepNon58 hr hc_t.2.1 hc_t.2.2).choose_spec.choose_spec.choose_spec.choose,
         (stepNon58 hr hc_t.2.1 hc_t.2.2).choose, res_o,
         (stepNon58 hr hc_t.2.1 hc_t.2.2).choose_spec.choose, true⟩ := by
      dsimp only [q_det, qDetNon58]; rw [dite_eq_left hc_t]
    have hq0_data : (q_det t₀).data = (stepNon58 hr₀ hc₀.2.1 hc₀.2.2).choose := by
      dsimp only [q_det, qDetNon58, t₀]; rw [dite_eq_left hc₀]
    dsimp only; rw [hq_eq]
    refine ⟨hr_post, ?_, ?_, ?_, fun hc => ?_, fun hgc => ?_, hmid⟩
    · rw [hq0_data, hsp₀.2.1, hy_mem]; exact hsch_post
    · rw [hnc2, hnc1, hfg_src, SlotLatent.applyFG_nCap]; exact hnc
    · rw [hev2, hev1, hfg_src, applyFG_false_evs, hev]
    · exact hsd2.trans (hsd1.trans (by rw [hfg_src]; exact (applyFG_seeds_heq ..).trans (hsd hc)))
    · exact hT (fun _ => hgc) (fun h9 => by clear *- h9 hp_t hp4; omega)
  let L_rep' := (q_det t₀).latent
  let s_rep' := rMemState (q_det t₀).data
  have hinv_rep' : DualStateInv c U V w base s_dict' L_rep' s_rep' :=
    (hf_post a₀ ha₀ (zeroSeedWords c w capSrc)).1.2.2.2
  have hcls₀ :
      s_rep'.mem (base + hdrPhase) ≤ 4 ∨
      (s_rep'.mem (base + hdrPhase) = 5 ∧ s_rep'.mem (base + hdrCur) = 32) ∨
      (s_rep'.mem (base + hdrPhase) = 6 ∧ s_rep'.mem (base + hdrNDst) = 0) := by
    have hp₀ : t₀.data.mem (base + hdrPhase) = ph :=
      (hsch₀.2 hdrPhase (by decide) (by decide)).symm
    have hc₀ : DualRep c U V w base s_dict t₀.latent t₀.data ∧
        t₀.data.mem (base + hdrPhase) ≠ 5 ∧ t₀.data.mem (base + hdrPhase) ≠ 8 :=
      ⟨hr₀, by clear *- hp₀ hp4; omega, by clear *- hp₀ hp4; omega⟩
    have hsp₀ := (stepNon58 hr₀ hc₀.2.1 hc₀.2.2).choose_spec.choose_spec.choose_spec.choose_spec
    obtain ⟨hy_m0, hr_p0, hmid0, hsm0, ht0, hpre0, _, _, _, _, _⟩ := hsp₀.2
    have hq0_data : (q_det t₀).data = (stepNon58 hr₀ hc₀.2.1 hc₀.2.2).choose := by
      dsimp only [q_det, qDetNon58]; rw [dite_eq_left hc₀]
    have hq0_m : s_rep' = rMemState (stepNon58 hr₀ hc₀.2.1 hc₀.2.2).choose := by
      dsimp only [s_rep']; rw [hq0_data]
    rw [hq0_m, hy_m0]; dsimp only; rw [ht0]
    have hsm0_le4 := hp4
    rw [← hp₀] at hsm0_le4
    dsimp only [rMemState] at hsm0
    rw [← hsm0] at hsm0_le4
    have hpre0' := preShrink_congr_st hpre0 ht0
    exact (bgTick_post_from_le4 hop_nz hmid0 hsm0_le4 hpre0'
      (stateInv_congr_st hr_p0.2.2.2 (by rw [hy_m0]; dsimp only; rw [ht0]))).2
  have hcapSrc'_eq : dualCapSrc base s_rep'.mem = capSrc := by
    have hle7' : s_rep'.mem (base + hdrPhase) ≤ 7 := by
      rcases hcls₀ with h | ⟨h, _⟩ | ⟨h, _⟩ <;> (clear *- h; omega)
    exact (hinv_rep'.sl_le7 hle7').1.symm.trans (hf_post a₀ ha₀ _).2.2.1
  let f_next : α → SeedWords c w capSrc → LatentRState (DualLatent c U V) rWhp :=
    fun a ws => ⟨(q_det (f_act a ws)).latent, (q_det (f_act a ws)).data⟩
  have hν'_bind : (ν.bind fun t => (μ_step t).map fun q => ⟨q.latent, q.data⟩) =
      μ_idx.bind (fun a => (PMF.uniformOfFintype (SeedWords c w capSrc)).map (f_next a)) := by
    rw [hν, PMF.bind_bind]
    refine congrArg (μ_idx.bind ·) (funext fun a => ?_)
    rw [PMF.bind_map]
    dsimp only [μ_step]
    conv_rhs => unfold PMF.map
    refine congrArg ((PMF.uniformOfFintype _).bind ·) (funext fun ws => ?_)
    dsimp only [Function.comp_def]; rw [PMF.pure_map]
  refine ⟨μ_step, hstep_all, ⟨L_rep', s_rep', hinv_rep', ?_⟩, ?_⟩
  · dsimp only
    rcases hcls₀ with hle4' | ⟨hp5', hcur32⟩ | ⟨hp6', hd0'⟩
    · rw [ite_eq_left hle4', hcapSrc'_eq]
      refine ⟨α, μ_idx, fun a => evs_of a ++ [fgEv], f_next, hν'_bind, fun a ha ws => ?_⟩
      obtain ⟨hr', hsch', hnc', hev', hsd', _, _⟩ := hf_post a ha ws
      exact ⟨hr', hsch', hnc', hev', hsd'⟩
    · rw [ite_eq_right (by clear *- hp5'; omega), ite_eq_left hp5', hcapSrc'_eq]
      refine ⟨α, μ_idx, 0, fun a => evs_of a ++ [fgEv],
        fun a ws => (f_next a ws).latent,
        fun a ws => rMemState (f_next a ws).data,
        fun a ws _ => f_next a ws, ?_, fun a ha ws => ?_⟩
      · rw [hν'_bind]
        refine congrArg (μ_idx.bind ·) (funext fun a => ?_)
        conv_lhs => unfold PMF.map
        refine congrArg ((PMF.uniformOfFintype _).bind ·) (funext fun ws => ?_)
        dsimp only [Function.comp_def]
        have hu0 : PMF.uniformOfFintype (Fin 0 → Fin (2 ^ w)) = PMF.pure Fin.elim0 := by
          ext g; rw [Subsingleton.elim g Fin.elim0, PMF.pure_apply_self,
            PMF.uniformOfFintype_apply,
            Fintype.card_eq_one_iff.mpr ⟨Fin.elim0, fun y => Subsingleton.elim y _⟩]
          simp
        rw [hu0, PMF.pure_map]
      · obtain ⟨hr', hsch', hnc', hev', hsd', _, _⟩ := hf_post a ha ws
        have hp5_t : (rMemState (f_next a ws).data).mem (base + hdrPhase) = 5 :=
          (hsch'.2 hdrPhase (by decide) (by decide)).symm.trans hp5'
        have hc32_t : (rMemState (f_next a ws).data).mem (base + hdrCur) = 32 :=
          (hsch'.2 hdrCur (by decide) (by decide)).symm.trans hcur32
        exact ⟨hr'.2.2.2, hsch', hnc', hev', hsd', fun wp =>
          ⟨hr', Ph5StateAt.of_entry hr'.2.2.2 hp5_t hc32_t wp, rfl⟩⟩
    · rw [ite_eq_right (by clear *- hp6'; omega), ite_eq_right (by clear *- hp6'; omega),
        ite_eq_left (Or.inl hp6'), hcapSrc'_eq, hd0']
      refine ⟨α, μ_idx, fun a => evs_of a ++ [fgEv],
        fun a ws => (f_next a ws).latent,
        fun a ws => rMemState (f_next a ws).data,
        fun a ws _ => f_next a ws, ?_, fun a ha ws => ?_⟩
      · rw [hν'_bind]
        refine congrArg (μ_idx.bind ·) (funext fun a => ?_)
        conv_lhs => unfold PMF.map
        refine congrArg ((PMF.uniformOfFintype _).bind ·) (funext fun ws => ?_)
        dsimp only [Function.comp_def]
        rw [uniformOfFintype_seedWords_zero c w, PMF.pure_map]
      · obtain ⟨hr', hsch', hnc', hev', hsd', _, _⟩ := hf_post a ha ws
        exact ⟨hr'.2.2.2, hsch', hnc', hev', hsd', fun _ =>
          ⟨hr', Coupled67.refl c w base _, rfl, fun h => absurd h (Nat.lt_irrefl 0)⟩⟩
  · rw [hν, PMF.bind_bind]
    refine toOuterMeasure_bind_le_const μ_idx _ _ _ fun a ha => ?_
    rw [PMF.bind_map]
    let sl_mid := fun ws =>
      ((f_act a ws).latent.applyFG
        ((f_act a ws).data.mem (base + hdrPhase)) opTag u v).slotSrc
    refine (toOuterMeasure_map_pure_le _ _ _ (fun ws => (sl_mid ws).GoodCovers)
      fun ws hgc hbad => ?_).trans ?_
    · apply hbad
      exact ⟨by dsimp only [q_det, qDetNon58]; split_ifs <;> rfl,
        (hf_post a ha ws).2.2.2.2.2.1 hgc⟩
    · refine (uniform_seedWords_bad_le hUw hsrc_safe (evs_of a ++ [fgEv]) sl_mid
        (fun ws => ?_) (fun ws => ?_) (fun hc ws => ?_) fun hc => ?_).trans
        (half_stepFailureProb_le c s_dict o)
      · obtain ⟨_, hsch, hnc, _, _⟩ := hf a ha ws
        simp only [Bool.false_eq_true, ↓reduceIte] at hnc
        have hp_t : (f_act a ws).data.mem (base + hdrPhase) = ph :=
          (hsch.2 hdrPhase (by decide) (by decide)).symm
        dsimp only [sl_mid]; unfold DualLatent.applyFG
        rw [ite_eq_left (by clear *- hp_t hp4; omega)]; dsimp only
        rw [SlotLatent.applyFG_nCap]; exact hnc
      · obtain ⟨_, hsch, _, hev, _⟩ := hf a ha ws
        simp only [Bool.false_eq_true, ↓reduceIte] at hev
        have hp_t : (f_act a ws).data.mem (base + hdrPhase) = ph :=
          (hsch.2 hdrPhase (by decide) (by decide)).symm
        dsimp only [sl_mid]; unfold DualLatent.applyFG
        rw [ite_eq_left (by clear *- hp_t hp4; omega)]; dsimp only
        rw [applyFG_false_evs, hev]
      · obtain ⟨_, hsch, _, _, hsd⟩ := hf a ha ws
        have hp_t : (f_act a ws).data.mem (base + hdrPhase) = ph :=
          (hsch.2 hdrPhase (by decide) (by decide)).symm
        dsimp only [sl_mid]; unfold DualLatent.applyFG
        rw [ite_eq_left (by clear *- hp_t hp4; omega)]; dsimp only
        exact (applyFG_seeds_heq ..).trans (hsd hc)
      · let ws₀ := zeroSeedWords c w capSrc
        have hmid₀ := (hf_post a ha ws₀).2.2.2.2.2.2
        obtain ⟨_, hsch₀', hnc₀', hev₀', _⟩ := hf a ha ws₀
        simp only [Bool.false_eq_true, ↓reduceIte] at hnc₀' hev₀'
        have hp_t0 : (f_act a ws₀).data.mem (base + hdrPhase) = ph :=
          (hsch₀'.2 hdrPhase (by decide) (by decide)).symm
        have hnc_m0 : (sl_mid ws₀).nCap = capSrc := by
          dsimp only [sl_mid]; unfold DualLatent.applyFG
          rw [ite_eq_left (by clear *- hp_t0 hp4; omega)]; dsimp only
          rw [SlotLatent.applyFG_nCap]; exact hnc₀'
        have hev_m0 : (sl_mid ws₀).evs = evs_of a ++ [fgEv] := by
          dsimp only [sl_mid]; unfold DualLatent.applyFG
          rw [ite_eq_left (by clear *- hp_t0 hp4; omega)]; dsimp only
          rw [applyFG_false_evs, hev₀']
        have hfg0 := fgStep_le7_aux (hf a ha ws₀).1.2.2.2 u v hv_eq
          (fgSetup_of_dualStateInv (hf a ha ws₀).1.2.2.2 hop_nz u v) rfl rfl rfl
          (by change (f_act a ws₀).data.mem (base + hdrPhase) ≤ 7; clear *- hp_t0 hp4; omega)
        have hsm_ph0_eq := hfg0.2.2.2.1 (base + hdrPhase) (by dsimp only [hdrPhase]; omega)
          (base_add_ne (by decide)) (base_add_ne (by decide))
        have hb₀ := (dualCoreInv_slot_evs_bounds hmid₀).1
          (by rw [hsm_ph0_eq]; change (f_act a ws₀).data.mem (base + hdrPhase) ≤ 8
              clear *- hp_t0 hp4; omega)
          (hnc_m0 ▸ hc)
        rwa [hnc_m0, hev_m0] at hb₀

private noncomputable def μStepPh5 {c U V w base opTag v_val : ℕ}
    (s_dict : Dictionary.State U) (o : Dynamic.Op U)
    (hv : (Dynamic.spec U V U).valid s_dict o)
    (hfit_peak : Fits w (base + stepSuccinctPeakWordsWhp c V w s_dict o))
    (u : Fin U) (v : Fin V)
    (ho_mut : (o = .insert u v.val ∧ opTag = 1 ∧ v_val = v.val) ∨
      (o = .delete u ∧ opTag = 2 ∧ v_val = 0))
    (s_rep : Memory.State) (k_pre : ℕ)
    (hd_pos : 0 < s_rep.mem (base + hdrNDst))
    (hcur_le_bm : s_rep.mem (base + hdrCur) ≤ offBktMeta c w (s_rep.mem (base + hdrNDst)))
    (hpre_eq_cur : 32 + k_pre = s_rep.mem (base + hdrCur))
    (t : LatentRState (DualLatent c U V) rWhp) :
    PMF (WhpStepROutcome (DualLatent c U V) ((Dynamic.spec U V U).Result o) rWhp) := by
  classical
  let capDst := s_rep.mem (base + hdrNDst)
  let cur := s_rep.mem (base + hdrCur)
  let offBM := offBktMeta c w capDst
  let endOff := cur + min bulkBatchWhp (offBM - cur)
  let metaDst := dualMbDst base s_rep.mem
  let k_batch := endOff - cur
  let extractPre : RData rWhp → (Fin k_pre → Fin (2 ^ w)) :=
    fun d i => wordOfNat w (d.mem ((metaDst + 32) + i.val))
  let res_o := ((Dynamic.spec U V U).stepFn s_dict o).2
  exact
    if hc : DualRep c U V w base s_dict t.latent t.data ∧
        t.data.mem (base + hdrPhase) = 5 ∧
        t.data.mem (base + hdrCur) = cur ∧
        t.data.mem (base + hdrNDst) = capDst then
      let h5 := opCodeWhp_mutate_ph5_exec hc.1 o hv hfit_peak u v ho_mut hc.2.1
      let y_fn := h5.choose
      let T_fn := h5.choose_spec.choose
      let h5_sp := h5.choose_spec.choose_spec.2
      let hcast : (endOff - cur) =
          (((rMemState t.data).mem (base + hdrCur) +
            min bulkBatchWhp
              (offBktMeta c w ((rMemState t.data).mem (base + hdrNDst)) -
                (rMemState t.data).mem (base + hdrCur))) -
            (rMemState t.data).mem (base + hdrCur)) := by
        dsimp only [endOff, offBM, rMemState]; rw [hc.2.2.1, hc.2.2.2]
      (PMF.uniformOfFintype (Fin k_batch → Fin (2 ^ w))).map fun wb =>
        let wb' := fun i => wb (Fin.cast hcast.symm i)
        let L_out : DualLatent c U V :=
          if hlt : endOff < offBM then
            ((h5_sp wb').2.2.2.2.2.2.1 (by
              dsimp only [endOff, offBM, rMemState] at hlt ⊢
              rw [hc.2.2.1, hc.2.2.2]; exact hlt)).choose
          else
            have heq_bm : endOff = offBM := le_antisymm
              (by dsimp only [endOff, offBM, capDst, cur]; clear *- hcur_le_bm; omega)
              (Nat.not_lt.mp hlt)
            have hlen : k_pre + k_batch = (if capDst = 0 then 0 else offBM - 32) := by
              rw [ite_eq_right hd_pos.ne']; dsimp only [k_batch]
              clear *- hpre_eq_cur heq_bm; omega
            let ws_seed : SeedWords c w capDst :=
              fun i => (finAppendWords (extractPre t.data) wb) (Fin.cast hlen.symm i)
            { (t.latent.applyFG 5 opTag u v) with
              slotDst := ⟨capDst, fun _ => none, seedsOfWords c U w capDst ws_seed, []⟩
              elapsed := t.latent.elapsed + 1 }
        ⟨L_out, y_fn wb', res_o, T_fn wb', true⟩
    else
      PMF.pure ⟨t.latent, t.data, res_o, 0, true⟩

private theorem dualDistInv_mutate_ph5 {c U V w base opTag v_val : ℕ}
    (s_dict : Dictionary.State U) (o : Dynamic.Op U)
    (hv : (Dynamic.spec U V U).valid s_dict o)
    (u : Fin U) (v : Fin V)
    (ho_mut : (o = .insert u v.val ∧ opTag = 1 ∧ v_val = v.val) ∨
      (o = .delete u ∧ opTag = 2 ∧ v_val = 0))
    (ν : PMF (LatentRState (DualLatent c U V) rWhp))
    (hfit_peak : Fits w (base + stepSuccinctPeakWordsWhp c V w s_dict o))
    {L_rep : DualLatent c U V} {s_rep : Memory.State}
    (hinv_rep : DualStateInv c U V w base s_dict L_rep s_rep)
    (hp5 : s_rep.mem (base + hdrPhase) = 5)
    (hregimes : Ph5Law c U V w base s_dict s_rep (dualCapSrc base s_rep.mem) ν) :
    MutateStepPost c U V w base s_dict o ν := by
  classical
  set s_dict' := ((Dynamic.spec U V U).stepFn s_dict o).1
  set res_o := ((Dynamic.spec U V U).stepFn s_dict o).2
  obtain ⟨hop_nz, hv_eq, hs_dict'_eq, hsucc_fits', hpad_rep_fits'⟩ :=
    mutate_setup_bounds ho_mut hfit_peak hinv_rep
  let fgEv : EpochUpdate U V := if opTag = 1 then .insert u v else .delete u
  have hUw : Fits w U := hinv_rep.U_lt
  set ph := s_rep.mem (base + hdrPhase)
  set capSrc := dualCapSrc base s_rep.mem
  set capDst := s_rep.mem (base + hdrNDst)
  have hsrc_safe := dualCapSrc_safe hinv_rep
  obtain ⟨α, μ_idx, k_pre, evs_src, L_anc, s_anc, f5, hν, hf⟩ := hregimes
  let cur := s_rep.mem (base + hdrCur)
  let offBM := offBktMeta c w capDst
  let endOff := cur + min bulkBatchWhp (offBM - cur)
  let metaDst := dualMbDst base s_rep.mem
  let k_batch := endOff - cur
  let extractPre : RData rWhp → (Fin k_pre → Fin (2 ^ w)) :=
    fun d i => wordOfNat w (d.mem ((metaDst + 32) + i.val))
  obtain ⟨a₀, ha₀⟩ := μ_idx.support_nonempty
  have hp5_rep : s_rep.mem (base + hdrPhase) = 5 := hp5
  have hd_pos : 0 < capDst := (hinv_rep.ph5_inv hp5_rep).1
  have hcur_le_bm : cur ≤ offBM := (hinv_rep.ph5_inv hp5_rep).2.2.1
  have hpre_eq_cur : 32 + k_pre = cur := by
    obtain ⟨_, ha_sch0, _, _, _, hwp0⟩ := hf a₀ ha₀ (zeroSeedWords c w capSrc)
    have hph5_0 := (hwp0 (fun _ => ⟨0, Nat.two_pow_pos w⟩)).2.1
    exact hph5_0.2.1.trans (ha_sch0.2 hdrCur (by decide) (by decide)).symm
  -- Build `μ_step` on Phase-`5` states
  let μ_step := μStepPh5 s_dict o hv hfit_peak u v ho_mut s_rep k_pre
    hd_pos hcur_le_bm hpre_eq_cur
  have hextract_pre : ∀ a ∈ μ_idx.support, ∀ ws_src wp,
      extractPre (f5 a ws_src wp).data = wp := by
    intro a ha ws_src wp
    obtain ⟨_, ha_sch, _, _, _, hwp⟩ := hf a ha ws_src
    obtain ⟨_, ⟨_, _, _, hs_eq⟩, _⟩ := hwp wp
    have hmb : dualMbDst base (s_anc a ws_src).mem = metaDst := ha_sch.mbDst_eq.symm
    funext i; apply Fin.ext
    dsimp only [extractPre]
    have hm := congrArg (fun st => st.mem ((metaDst + 32) + i.val)) hs_eq
    dsimp only at hm
    change (f5 a ws_src wp).data.mem ((metaDst + 32) + i.val) = _ at hm
    rw [hm, hmb, writeWords_apply_in _ _ _ i.isLt]
    exact wordOfNat_val_of_lt (wp i).isLt
  have hsupp_ph5 : ∀ a ∈ μ_idx.support, ∀ ws_src wp,
      let t := f5 a ws_src wp
      DualRep c U V w base s_dict t.latent t.data ∧
      t.data.mem (base + hdrPhase) = 5 ∧
      t.data.mem (base + hdrCur) = cur ∧
      t.data.mem (base + hdrNDst) = capDst := by
    intro a ha ws_src wp
    obtain ⟨ha_inv, ha_sch, _, _, _, hwp⟩ := hf a ha ws_src
    obtain ⟨hr, hph5, _⟩ := hwp wp
    have hsch_t := ha_sch.trans (hph5.schedEq ha_inv)
    exact ⟨hr,
      (hsch_t.2 hdrPhase (by decide) (by decide)).symm.trans hp5,
      (hsch_t.2 hdrCur (by decide) (by decide)).symm,
      (hsch_t.2 hdrNDst (by decide) (by decide)).symm⟩
  have hph5_sr_eq : ∀ a (ha : a ∈ μ_idx.support) (ws_src : SeedWords c w capSrc)
      (wp : Fin k_pre → Fin (2 ^ w)) (wb : Fin k_batch → Fin (2 ^ w))
      (hcast : k_batch =
        (((rMemState (f5 a ws_src wp).data).mem (base + hdrCur) +
          min bulkBatchWhp
            (offBktMeta c w ((rMemState (f5 a ws_src wp).data).mem (base + hdrNDst)) -
              (rMemState (f5 a ws_src wp).data).mem (base + hdrCur))) -
          (rMemState (f5 a ws_src wp).data).mem (base + hdrCur)))
      (hcast_a : (((s_anc a ws_src).mem (base + hdrCur) +
          min bulkBatchWhp
            (offBktMeta c w ((s_anc a ws_src).mem (base + hdrNDst)) -
              (s_anc a ws_src).mem (base + hdrCur))) -
          (s_anc a ws_src).mem (base + hdrCur)) = k_batch),
      let s_t := rMemState (f5 a ws_src wp).data
      let s_a := s_anc a ws_src
      let sg_t : Memory.State :=
        { mem := ((Memory.spec 0).clientState s_t
            (prepGrowProg (((base, s_t.frontier), opTag), u.val))).mem
          frontier := s_t.frontier +
            (Memory.spec 0).clientResult s_t
              (prepGrowProg (((base, s_t.frontier), opTag), u.val)) }
      let sg_a : Memory.State :=
        { mem := ((Memory.spec 0).clientState s_t
            (prepGrowProg (((base, s_t.frontier), opTag), u.val))).mem
          frontier := s_t.frontier +
            (Memory.spec 0).clientResult s_a
              (prepGrowProg (((base, s_a.frontier), opTag), u.val)) }
      let st_t := (Memory.spec 0).clientState sg_t
        (stepOpProg (((base, sg_t.frontier), opTag), (u.val, v_val)))
      let st_a := (Memory.spec 0).clientState sg_a
        (stepOpProg (((base, sg_a.frontier), opTag), (u.val, v_val)))
      (Memory.spec 0).clientResult s_a
          (prepGrowProg (((base, s_a.frontier), opTag), u.val)) =
        (Memory.spec 0).clientResult s_t
          (prepGrowProg (((base, s_t.frontier), opTag), u.val)) ∧
      ({ mem := writeWords st_t.mem (dualMbDst base s_t.mem + s_t.mem (base + hdrCur))
           (fun i => wb (Fin.cast hcast.symm i))
         frontier := st_t.frontier } : Memory.State) =
      { mem := writeWords st_a.mem (dualMbDst base s_a.mem + s_a.mem (base + hdrCur))
          (fun i => wb (Fin.cast hcast_a i))
        frontier := st_a.frontier } := by
    intro a ha ws_src wp wb hcast hcast_a s_t s_a sg_t sg_a st_t st_a
    have hc_t := hsupp_ph5 a ha ws_src wp
    obtain ⟨ha_inv, ha_sch, _, _, _, hwp⟩ := hf a ha ws_src
    obtain ⟨hr, hph5, _⟩ := hwp wp
    have hpad_a :
        base + dualPaddedWords c U V w (s_a.mem (base + hdrNSrc))
          (if s_a.mem (base + hdrPhase) = 0 then s_a.mem (base + hdrNSrc)
           else s_a.mem (base + hdrNDst))
          (Dictionary.dom (if opTag = 1 then Function.update s_dict u (some v.val)
            else Function.update s_dict u none)).card < 2 ^ w := by
      dsimp only [s_a]
      rwa [← ha_sch.2 hdrNSrc (by decide) (by decide),
        ← ha_sch.2 hdrPhase (by decide) (by decide),
        ← ha_sch.2 hdrNDst (by decide) (by decide)]
    have hkg_eq := (schedEq_mutate_step (v_val := v_val) ha_inv hr.2.2.2
      (hph5.schedEq ha_inv) hop_nz u v hv_eq hsucc_fits' hpad_a).1
    dsimp only at hkg_eq
    have hsg_eq : sg_t = sg_a := by dsimp only [sg_t, sg_a]; rw [hkg_eq]
    have hst_eq : st_t = st_a := by dsimp only [st_t, st_a]; rw [hsg_eq]
    have ha_cur : s_a.mem (base + hdrCur) = cur :=
      (ha_sch.2 hdrCur (by decide) (by decide)).symm
    have ha_mb : dualMbDst base s_a.mem = metaDst := ha_sch.mbDst_eq.symm
    have ht_mb : dualMbDst base (f5 a ws_src wp).data.mem = metaDst :=
      (ha_sch.trans (hph5.schedEq ha_inv)).mbDst_eq.symm
    have hww_eq :
        writeWords st_t.mem (dualMbDst base s_t.mem + s_t.mem (base + hdrCur))
          (fun i => wb (Fin.cast hcast.symm i)) =
          writeWords st_a.mem (dualMbDst base s_a.mem + s_a.mem (base + hdrCur))
            (fun i => wb (Fin.cast hcast_a i)) := by
      have haddr_t : dualMbDst base s_t.mem + s_t.mem (base + hdrCur) = metaDst + cur := by
        dsimp only [s_t, rMemState]; rw [ht_mb, hc_t.2.2.1]
      have haddr_a : dualMbDst base s_a.mem + s_a.mem (base + hdrCur) = metaDst + cur := by
        rw [ha_mb, ha_cur]
      rw [hst_eq, haddr_t, haddr_a]
      funext addr; unfold writeWords
      by_cases hin : metaDst + cur ≤ addr ∧ addr < (metaDst + cur) + k_batch
      · have hin1 := hcast ▸ hin
        have hin2 := hcast_a.symm ▸ hin
        rw [dite_eq_left hin1, dite_eq_left hin2]; rfl
      · have hin1 := hcast ▸ hin
        have hin2 := hcast_a.symm ▸ hin
        rw [dite_eq_right hin1, dite_eq_right hin2]
    exact ⟨hkg_eq, Memory.State.ext hww_eq (by rw [hst_eq])⟩
  -- Prove `hstep_all` on `ν.support`
  have hstep_all : ∀ t ∈ ν.support,
      ExecRCodeSteps w opCodeWhp ((subroutineCodeWhp c U V w).prepare whpEncode o t.data)
        ((μ_step t).map WhpStepROutcome.toCodeOutcome)
        (base + stepSuccinctPeakWordsWhp c V w s_dict o) ∧
      ∀ q ∈ (μ_step t).support,
        q.result = res_o ∧ whpDecode (V := V) o q.data.regs = some q.result ∧
        DualRep c U V w base s_dict' q.latent q.data ∧
        (∀ addr < base, q.data.mem addr = t.data.mem addr) := by
    intro t ht
    rw [hν, PMF.mem_support_bind_iff] at ht
    obtain ⟨a, ha, hmt1⟩ := ht; rw [PMF.mem_support_bind_iff] at hmt1
    obtain ⟨ws_src, _, hmt2⟩ := hmt1; rw [PMF.mem_support_map_iff] at hmt2
    obtain ⟨wp, _, rfl⟩ := hmt2
    have hc_t := hsupp_ph5 a ha ws_src wp
    obtain ⟨ha_inv, ha_sch, _, _, _, hwp⟩ := hf a ha ws_src
    obtain ⟨hr, hph5, _⟩ := hwp wp
    have hpad_anc :
        base + dualPaddedWords c U V w ((s_anc a ws_src).mem (base + hdrNSrc))
          (if (s_anc a ws_src).mem (base + hdrPhase) = 0 then
            (s_anc a ws_src).mem (base + hdrNSrc)
           else (s_anc a ws_src).mem (base + hdrNDst))
          (Dictionary.dom (if opTag = 1 then Function.update s_dict u (some v.val)
            else Function.update s_dict u none)).card < 2 ^ w := by
      rwa [← ha_sch.2 hdrNSrc (by decide) (by decide),
        ← ha_sch.2 hdrPhase (by decide) (by decide),
        ← ha_sch.2 hdrNDst (by decide) (by decide)]
    have hm5 := ph5_mutate_step ha_inv hr.2.2.2 hph5 hop_nz u v hv_eq hsucc_fits' hpad_anc
    have h5_ex := (opCodeWhp_mutate_ph5_exec hc_t.1 o hv hfit_peak u v ho_mut
      hc_t.2.1).choose_spec.choose_spec
    dsimp only [μ_step, μStepPh5]; rw [dite_eq_left hc_t]
    have hcast : k_batch =
        (((rMemState (f5 a ws_src wp).data).mem (base + hdrCur) +
          min bulkBatchWhp
            (offBktMeta c w ((rMemState (f5 a ws_src wp).data).mem (base + hdrNDst)) -
              (rMemState (f5 a ws_src wp).data).mem (base + hdrCur))) -
          (rMemState (f5 a ws_src wp).data).mem (base + hdrCur)) := by
      dsimp only [k_batch, endOff, offBM, rMemState]; rw [hc_t.2.2.1, hc_t.2.2.2]
    refine ⟨?_, fun q hq => ?_⟩
    · rw [PMF.map_comp]
      refine h5_ex.1.congr_dist ?_
      have hev_eq := PMF.uniformOfFintype_map_equiv
        (Equiv.arrowCongr (finCongr hcast.symm) (Equiv.refl (Fin (2 ^ w))))
      conv_rhs => rw [← hev_eq, PMF.map_comp]
      rfl
    · rw [PMF.mem_support_map_iff] at hq
      obtain ⟨wb, _, rfl⟩ := hq
      dsimp only
      let wb' := fun i => wb (Fin.cast hcast.symm i)
      obtain ⟨hy_mem, hyb, hy_base, hy_mfr, hy_dec, hy_out, hy_lt, _⟩ := h5_ex.2 wb'
      refine ⟨rfl, hy_dec, ⟨hyb, hy_base, hy_mfr, ?_⟩, hy_out⟩
      by_cases hlt : endOff < offBM
      · rw [dite_eq_left hlt]
        exact stateInv_congr_st (hy_lt (by
          dsimp only [endOff, offBM, rMemState] at hlt ⊢
          rw [hc_t.2.2.1, hc_t.2.2.2]; exact hlt)).choose_spec.2 hy_mem.symm
      · have hexp_eq := hextract_pre a ha ws_src wp
        dsimp only [extractPre, metaDst] at hexp_eq
        rw [dite_eq_right hlt, hexp_eq, hy_mem]
        have heq_bm : endOff = offBM :=
          le_antisymm (by dsimp only [endOff]; clear *- hcur_le_bm; omega) (Nat.not_lt.mp hlt)
        have ha_cur : (s_anc a ws_src).mem (base + hdrCur) = cur :=
          (ha_sch.2 hdrCur (by decide) (by decide)).symm
        have ha_nd : (s_anc a ws_src).mem (base + hdrNDst) = capDst :=
          (ha_sch.2 hdrNDst (by decide) (by decide)).symm
        have hcast_a : ((s_anc a ws_src).mem (base + hdrCur) +
            min bulkBatchWhp
              (offBktMeta c w ((s_anc a ws_src).mem (base + hdrNDst)) -
                (s_anc a ws_src).mem (base + hdrCur))) -
            (s_anc a ws_src).mem (base + hdrCur) = k_batch := by
          dsimp only [k_batch, endOff, offBM]; rw [ha_cur, ha_nd]
        let wb_a := fun i => wb (Fin.cast hcast_a i)
        have hinv_m := (hm5.2 wb_a).2 (by
          dsimp only [endOff, offBM] at heq_bm; rw [ha_cur, ha_nd]; exact heq_bm)
        obtain ⟨_, _, hinv_post⟩ := hinv_m
        rw [hs_dict'_eq] at hinv_post
        obtain ⟨hkg_eq, hsr_eq⟩ := hph5_sr_eq a ha ws_src wp wb hcast hcast_a
        have hlen : k_pre + k_batch = (if capDst = 0 then 0 else offBM - 32) := by
          rw [ite_eq_right hd_pos.ne']; dsimp only [k_batch]
          clear *- hpre_eq_cur heq_bm; omega
        have hlen_a :
            k_pre + (((s_anc a ws_src).mem (base + hdrCur) +
              min bulkBatchWhp
                (offBktMeta c w ((s_anc a ws_src).mem (base + hdrNDst)) -
                  (s_anc a ws_src).mem (base + hdrCur))) -
              (s_anc a ws_src).mem (base + hdrCur)) =
              (if (s_anc a ws_src).mem (base + hdrNDst) = 0 then 0
               else offBktMeta c w ((s_anc a ws_src).mem (base + hdrNDst)) - 32) := by
          rw [hcast_a, ha_nd]; exact hlen
        have hseed_eq :
            HEq (seedsOfWords c U w ((s_anc a ws_src).mem (base + hdrNDst))
              (fun i => (finAppendWords wp wb_a) (Fin.cast hlen_a.symm i)))
              (seedsOfWords c U w capDst
                (fun i => (finAppendWords wp wb) (Fin.cast hlen.symm i))) :=
          seedsOfWords_heq ha_nd _ _ fun i₁ i₂ hval => by
            dsimp only [finAppendWords, wb_a, Fin.val_cast]
            by_cases hi : i₂.val < k_pre
            · have hi₁ : i₁.val < k_pre := hval.symm ▸ hi
              rw [dite_eq_left hi₁, dite_eq_left hi]
              congr 1; exact Fin.ext hval
            · have hi₁ : ¬i₁.val < k_pre := hval.symm ▸ hi
              rw [dite_eq_right hi₁, dite_eq_right hi]
              congr 1; exact Fin.ext (by dsimp only [Fin.val_cast]; rw [hval])
        have hslot_eq :
            (⟨(s_anc a ws_src).mem (base + hdrNDst), fun _ => none,
              seedsOfWords c U w ((s_anc a ws_src).mem (base + hdrNDst))
                (fun i => (finAppendWords wp wb_a) (Fin.cast hlen_a.symm i)), []⟩ :
              SlotLatent c U V) =
            ⟨capDst, fun _ => none,
              seedsOfWords c U w capDst
                (fun i => (finAppendWords wp wb) (Fin.cast hlen.symm i)), []⟩ :=
          slotLatent_eq ha_nd rfl hseed_eq rfl
        have hL_eq :
            ({ ((f5 a ws_src wp).latent.applyFG 5 opTag u v) with
               slotDst := ⟨(s_anc a ws_src).mem (base + hdrNDst), fun _ => none,
                 seedsOfWords c U w ((s_anc a ws_src).mem (base + hdrNDst))
                   (fun i => (finAppendWords wp wb_a) (Fin.cast hlen_a.symm i)), []⟩
               elapsed := (f5 a ws_src wp).latent.elapsed + 1 } : DualLatent c U V) =
            { ((f5 a ws_src wp).latent.applyFG 5 opTag u v) with
              slotDst := ⟨capDst, fun _ => none,
                seedsOfWords c U w capDst
                  (fun i => (finAppendWords wp wb) (Fin.cast hlen.symm i)), []⟩
              elapsed := (f5 a ws_src wp).latent.elapsed + 1 } := by
          rw [hslot_eq]
        dsimp only [capDst] at hL_eq
        rw [← hL_eq]
        exact stateInv_congr_st hinv_post (by dsimp only; rw [← hsr_eq]; dsimp only; rw [hkg_eq])
  -- Advance anchors `(L_anc, s_anc)` via `ws_zero` and close `5 → 5` or `5 → 6`
  have hanc_step : ∀ a ∈ μ_idx.support, ∀ ws_src : SeedWords c w capSrc,
      let s_a := s_anc a ws_src
      let cur_a := s_a.mem (base + hdrCur)
      let offBM_a := offBktMeta c w (s_a.mem (base + hdrNDst))
      let endOff_a := cur_a + min bulkBatchWhp (offBM_a - cur_a)
      let metaDst_a := dualMbDst base s_a.mem
      let k_g := (Memory.spec 0).clientResult s_a
        (prepGrowProg (((base, s_a.frontier), opTag), u.val))
      let sp_a := (Memory.spec 0).clientState s_a
        (prepGrowProg (((base, s_a.frontier), opTag), u.val))
      let sg_a : Memory.State := { mem := sp_a.mem, frontier := s_a.frontier + k_g }
      let st_a := (Memory.spec 0).clientState sg_a
        (stepOpProg (((base, sg_a.frontier), opTag), (u.val, v_val)))
      let ws_z : Fin (endOff_a - cur_a) → Fin (2 ^ w) := fun _ => wordOfNat w 0
      let sr_a : Memory.State :=
        { mem := writeWords st_a.mem (metaDst_a + cur_a) ws_z, frontier := st_a.frontier }
      let sps_a := (Memory.spec 0).clientState sr_a
        (postRandShrinkProg ((base, sr_a.frontier), opTag))
      let ksh_a := (Memory.spec 0).clientResult sr_a
        (postRandShrinkProg ((base, sr_a.frontier), opTag))
      let spost_a : Memory.State :=
        { mem := clear sps_a.mem (sr_a.frontier - ksh_a) ksh_a
          frontier := sr_a.frontier - ksh_a }
      ∃ L_post_a : DualLatent c U V,
        DualStateInv c U V w base s_dict' L_post_a spost_a ∧
        L_post_a.slotSrc.nCap = capSrc ∧
        L_post_a.slotSrc.evs = evs_src a ++ [fgEv] ∧
        (0 < capSrc → HEq L_post_a.slotSrc.seeds (seedsOfWords c U w capSrc ws_src)) ∧
        HEq L_post_a.slotSrc.seeds (L_anc a ws_src).slotSrc.seeds := by
    intro a ha ws_src s_a cur_a offBM_a endOff_a metaDst_a k_g sp_a sg_a st_a ws_z sr_a
      sps_a ksh_a spost_a
    obtain ⟨ha_inv, ha_sch, ha_nc, ha_ev, ha_sd, _⟩ := hf a ha ws_src
    have hp5_a : s_a.mem (base + hdrPhase) = 5 :=
      (ha_sch.2 hdrPhase (by decide) (by decide)).symm.trans hp5
    have hcur_a : cur_a = cur := (ha_sch.2 hdrCur (by decide) (by decide)).symm
    have hnd_a : s_a.mem (base + hdrNDst) = capDst :=
      (ha_sch.2 hdrNDst (by decide) (by decide)).symm
    have hmb_a : metaDst_a = metaDst := ha_sch.mbDst_eq.symm
    have hpad_a :
        base + dualPaddedWords c U V w (s_a.mem (base + hdrNSrc))
          (if s_a.mem (base + hdrPhase) = 0 then s_a.mem (base + hdrNSrc)
           else s_a.mem (base + hdrNDst))
          (Dictionary.dom (if opTag = 1 then Function.update s_dict u (some v.val)
            else Function.update s_dict u none)).card < 2 ^ w := by
      rwa [← ha_sch.2 hdrNSrc (by decide) (by decide),
        ← ha_sch.2 hdrPhase (by decide) (by decide),
        ← ha_sch.2 hdrNDst (by decide) (by decide)]
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hmid_a, hpt_a, _, _⟩ :=
      stepOpProg_mutate_spec ha_inv hop_nz u v hv_eq hsucc_fits' hpad_a
    have hfg_a := fgStep_le7_aux ha_inv u v hv_eq
      (fgSetup_of_dualStateInv ha_inv hop_nz u v) rfl rfl rfl (by rw [hp5_a]; decide)
    have hsm_ph5 : ((Memory.spec 0).clientState sg_a
        (userMutateProg ((base, opTag), (u.val, v_val)))).mem (base + hdrPhase) = 5 :=
      (hfg_a.2.2.2.1 (base + hdrPhase) (by dsimp only [hdrPhase]; omega)
        (base_add_ne (by decide)) (base_add_ne (by decide))).trans hp5_a
    have hsm_cur : ((Memory.spec 0).clientState sg_a
        (userMutateProg ((base, opTag), (u.val, v_val)))).mem (base + hdrCur) = cur_a :=
      hfg_a.2.2.2.1 (base + hdrCur) (by dsimp only [hdrCur]; omega)
        (base_add_ne (by decide)) (base_add_ne (by decide))
    have hsm_nd : ((Memory.spec 0).clientState sg_a
        (userMutateProg ((base, opTag), (u.val, v_val)))).mem (base + hdrNDst) =
        s_a.mem (base + hdrNDst) :=
      hfg_a.2.2.2.1 (base + hdrNDst) (by dsimp only [hdrNDst]; omega)
        (base_add_ne (by decide)) (base_add_ne (by decide))
    have hsm_stg : ((Memory.spec 0).clientState sg_a
        (userMutateProg ((base, opTag), (u.val, v_val)))).mem (base + hdrStage) =
        s_a.mem (base + hdrStage) :=
      hfg_a.2.2.2.1 (base + hdrStage) (by dsimp only [hdrStage]; omega)
        (base_add_ne (by decide)) (base_add_ne (by decide))
    have hsm_pad : ((Memory.spec 0).clientState sg_a
        (userMutateProg ((base, opTag), (u.val, v_val)))).mem (base + hdrPad) =
        s_a.mem (base + hdrPad) :=
      hfg_a.2.2.2.1 (base + hdrPad) (by dsimp only [hdrPad]; omega)
        (base_add_ne (by decide)) (base_add_ne (by decide))
    have hsm_mb : dualMbDst base ((Memory.spec 0).clientState sg_a
        (userMutateProg ((base, opTag), (u.val, v_val)))).mem = metaDst_a := by
      dsimp only [metaDst_a]; unfold dualMbDst
      rw [hsm_ph5, hsm_nd, hsm_stg, hsm_pad, hp5_a]
    have hsm_pd : dualPDst base ((Memory.spec 0).clientState sg_a
        (userMutateProg ((base, opTag), (u.val, v_val)))).mem = dualPDst base s_a.mem := by
      unfold dualPDst; rw [hsm_ph5, hsm_stg, hp5_a]
    obtain ⟨_, _, _, hbr⟩ := hpt_a
    rw [ite_eq_right (not_not.mpr hsm_ph5)] at hbr
    dsimp only at hbr
    rw [hsm_cur, hsm_nd, hsm_mb, hsm_pd] at hbr
    obtain ⟨_, _, _, hend_le_bm, _, _, _, _, _, hr_all⟩ := hbr
    obtain ⟨_, _, hph_r, hstg_r, hcur_r, hp31_r, hpre_lt, hmid_eq⟩ := hr_all ws_z
    have hph_r' : sr_a.mem (base + hdrPhase) = 5 := hph_r
    have hfg_src : ((L_anc a ws_src).applyFG (s_a.mem (base + hdrPhase)) opTag u v).slotSrc =
        (L_anc a ws_src).slotSrc.applyFG false opTag u v := by
      rw [hp5_a]; rfl
    by_cases hlt_a : endOff_a < offBM_a
    · obtain ⟨_, _, _, _, _, _, L_p, hpres, hinv_p⟩ :=
        postRandShrinkProg_spec_pre hop_nz (hpre_lt hlt_a)
      rw [hs_dict'_eq] at hinv_p
      have hnp : ¬(sr_a.mem (base + hdrPhase) = 11 ∧ sps_a.mem (base + hdrPhase) = 0) :=
        fun ⟨h11, _⟩ => by rw [hph_r'] at h11; cases h11
      obtain ⟨hnc_p, hsd_p, hev_p⟩ := hpres.1.1 hnp
      refine ⟨L_p, hinv_p, ?_, ?_, fun hc => ?_, ?_⟩
      · rw [hnc_p, hfg_src, SlotLatent.applyFG_nCap]; exact ha_nc
      · rw [hev_p, hfg_src, applyFG_false_evs, ha_ev]
      · exact hsd_p.trans (by rw [hfg_src]; exact (applyFG_seeds_heq ..).trans (ha_sd hc))
      · exact hsd_p.trans (by rw [hfg_src]; exact applyFG_seeds_heq ..)
    · have heq_a : endOff_a = offBM_a := le_antisymm hend_le_bm (Nat.not_lt.mp hlt_a)
      have hpD_r : dualPDst base sr_a.mem = dualPDst base s_a.mem := by
        unfold dualPDst
        have hsr_stg : sr_a.mem (base + hdrStage) = s_a.mem (base + hdrStage) :=
          hstg_r.trans hsm_stg
        rw [hph_r', hsr_stg, hp5_a]
      have hd_r : sr_a.mem (dualPDst base sr_a.mem + 31) ≤ sr_a.mem (base + hdrCur) := by
        have hp31' : sr_a.mem (dualPDst base s_a.mem + 31) = offBM_a := hp31_r
        have hcur' : sr_a.mem (base + hdrCur) = endOff_a := hcur_r
        rw [hpD_r, hp31', hcur', heq_a]
      obtain ⟨_, _, _, _, _, _, hinv_rf⟩ :=
        postRandShrinkProg_spec hop_nz (hmid_eq heq_a) hph_r' hd_r
      rw [hs_dict'_eq] at hinv_rf
      refine ⟨_, hinv_rf, ?_, ?_, fun hc => ?_, ?_⟩
      · dsimp only; rw [hfg_src, SlotLatent.applyFG_nCap]; exact ha_nc
      · dsimp only; rw [hfg_src, applyFG_false_evs, ha_ev]
      · dsimp only; rw [hfg_src]; exact (applyFG_seeds_heq ..).trans (ha_sd hc)
      · dsimp only; rw [hfg_src]; exact applyFG_seeds_heq ..
  -- Reference post-state `s_rep'` via `s_anc a₀ (zeroSeedWords c w capSrc)`
  let ws_src0 := zeroSeedWords c w capSrc
  let L_rep' := (hanc_step a₀ ha₀ ws_src0).choose
  have hrep'_sp := (hanc_step a₀ ha₀ ws_src0).choose_spec
  refine ⟨μ_step, hstep_all, ?_, ?_⟩
  · -- Preserve `DualDistInv` across `5 → 5` (`endOff < offBM`) vs `5 → 6` (`endOff = offBM`)
    let s_anc_next : α → SeedWords c w capSrc → Memory.State := fun a ws_src =>
      let s_a := s_anc a ws_src
      let cur_a := s_a.mem (base + hdrCur)
      let offBM_a := offBktMeta c w (s_a.mem (base + hdrNDst))
      let endOff_a := cur_a + min bulkBatchWhp (offBM_a - cur_a)
      let metaDst_a := dualMbDst base s_a.mem
      let k_g := (Memory.spec 0).clientResult s_a
        (prepGrowProg (((base, s_a.frontier), opTag), u.val))
      let sp_a := (Memory.spec 0).clientState s_a
        (prepGrowProg (((base, s_a.frontier), opTag), u.val))
      let sg_a : Memory.State := { mem := sp_a.mem, frontier := s_a.frontier + k_g }
      let st_a := (Memory.spec 0).clientState sg_a
        (stepOpProg (((base, sg_a.frontier), opTag), (u.val, v_val)))
      let ws_z : Fin (endOff_a - cur_a) → Fin (2 ^ w) := fun _ => wordOfNat w 0
      let sr_a : Memory.State :=
        { mem := writeWords st_a.mem (metaDst_a + cur_a) ws_z, frontier := st_a.frontier }
      let sps_a := (Memory.spec 0).clientState sr_a
        (postRandShrinkProg ((base, sr_a.frontier), opTag))
      let ksh_a := (Memory.spec 0).clientResult sr_a
        (postRandShrinkProg ((base, sr_a.frontier), opTag))
      { mem := clear sps_a.mem (sr_a.frontier - ksh_a) ksh_a
        frontier := sr_a.frontier - ksh_a }
    let s_rep' := s_anc_next a₀ ws_src0
    have hsch_anc_next : ∀ a ∈ μ_idx.support, ∀ ws_src : SeedWords c w capSrc,
        SchedEq base s_rep' (s_anc_next a ws_src) := by
      intro a ha ws_src
      have ha0_inv := (hf a₀ ha₀ ws_src0).1
      have ha0_sch := (hf a₀ ha₀ ws_src0).2.1
      have ha_inv := (hf a ha ws_src).1
      have ha_sch := (hf a ha ws_src).2.1
      have hsch_0_a := ha0_sch.symm.trans ha_sch
      have hpad0 :
          base + dualPaddedWords c U V w ((s_anc a₀ ws_src0).mem (base + hdrNSrc))
            (if (s_anc a₀ ws_src0).mem (base + hdrPhase) = 0 then
              (s_anc a₀ ws_src0).mem (base + hdrNSrc)
             else (s_anc a₀ ws_src0).mem (base + hdrNDst))
            (Dictionary.dom (if opTag = 1 then Function.update s_dict u (some v.val)
              else Function.update s_dict u none)).card < 2 ^ w := by
        rwa [← ha0_sch.2 hdrNSrc (by decide) (by decide),
          ← ha0_sch.2 hdrPhase (by decide) (by decide),
          ← ha0_sch.2 hdrNDst (by decide) (by decide)]
      have hp5_0 : (s_anc a₀ ws_src0).mem (base + hdrPhase) = 5 :=
        (ha0_sch.2 hdrPhase (by decide) (by decide)).symm.trans hp5
      obtain ⟨_, _, _, _, hpost5⟩ :=
        schedEq_mutate_step (v_val := v_val) ha0_inv ha_inv hsch_0_a hop_nz u v hv_eq
          hsucc_fits' hpad0
      have hc_eq := hsch_0_a.2 hdrCur (by decide) (by decide)
      have hd_eq := hsch_0_a.2 hdrNDst (by decide) (by decide)
      have hmb_eq := hsch_0_a.mbDst_eq
      have hlen_eq :
          (((s_anc a ws_src).mem (base + hdrCur) +
              min bulkBatchWhp
                (offBktMeta c w ((s_anc a ws_src).mem (base + hdrNDst)) -
                  (s_anc a ws_src).mem (base + hdrCur))) -
            (s_anc a ws_src).mem (base + hdrCur)) =
          (((s_anc a₀ ws_src0).mem (base + hdrCur) +
              min bulkBatchWhp
                (offBktMeta c w ((s_anc a₀ ws_src0).mem (base + hdrNDst)) -
                  (s_anc a₀ ws_src0).mem (base + hdrCur))) -
            (s_anc a₀ ws_src0).mem (base + hdrCur)) := by rw [hc_eq, hd_eq]
      obtain ⟨_, hsch_p⟩ := hpost5 hp5_0
        (fun _ => wordOfNat w 0) (fun _ => wordOfNat w 0)
      dsimp only at hsch_p
      -- Align `s_anc_next` with `hsch_p`
      let s_0 := s_anc a₀ ws_src0
      let s_a := s_anc a ws_src
      let k₀ := (s_0.mem (base + hdrCur) +
        min bulkBatchWhp (offBktMeta c w (s_0.mem (base + hdrNDst)) - s_0.mem (base + hdrCur))) -
        s_0.mem (base + hdrCur)
      let k_a := (s_a.mem (base + hdrCur) +
        min bulkBatchWhp (offBktMeta c w (s_a.mem (base + hdrNDst)) - s_a.mem (base + hdrCur))) -
        s_a.mem (base + hdrCur)
      let sg_a : Memory.State :=
        { mem := ((Memory.spec 0).clientState s_a
            (prepGrowProg (((base, s_a.frontier), opTag), u.val))).mem
          frontier := s_a.frontier +
            (Memory.spec 0).clientResult s_a
              (prepGrowProg (((base, s_a.frontier), opTag), u.val)) }
      let st_a := (Memory.spec 0).clientState sg_a
        (stepOpProg (((base, sg_a.frontier), opTag), (u.val, v_val)))
      let ws_z0 : Fin k₀ → Fin (2 ^ w) := fun _ => wordOfNat w 0
      let ws_za : Fin k_a → Fin (2 ^ w) := fun _ => wordOfNat w 0
      have hsr_a_eq :
          ({ mem := writeWords st_a.mem (dualMbDst base s_0.mem + s_0.mem (base + hdrCur)) ws_z0
             frontier := st_a.frontier } : Memory.State) =
          { mem := writeWords st_a.mem (dualMbDst base s_a.mem + s_a.mem (base + hdrCur)) ws_za
            frontier := st_a.frontier } := by
        refine Memory.State.ext ?_ rfl
        have haddr_eq :
            dualMbDst base s_0.mem + s_0.mem (base + hdrCur) =
              dualMbDst base s_a.mem + s_a.mem (base + hdrCur) := by
          dsimp only [s_0, s_a]; rw [hmb_eq, hc_eq]
        rw [haddr_eq]
        funext addr; unfold writeWords; dsimp only
        by_cases hin : dualMbDst base s_a.mem + s_a.mem (base + hdrCur) ≤ addr ∧
            addr < (dualMbDst base s_a.mem + s_a.mem (base + hdrCur)) + k₀
        · have hin2 : dualMbDst base s_a.mem + s_a.mem (base + hdrCur) ≤ addr ∧
              addr < (dualMbDst base s_a.mem + s_a.mem (base + hdrCur)) + k_a := by
            dsimp only [k₀, k_a, s_0, s_a] at hin ⊢; rwa [hlen_eq]
          rw [dite_eq_left hin, dite_eq_left hin2]
        · have hin2 : ¬(dualMbDst base s_a.mem + s_a.mem (base + hdrCur) ≤ addr ∧
              addr < (dualMbDst base s_a.mem + s_a.mem (base + hdrCur)) + k_a) := by
            dsimp only [k₀, k_a, s_0, s_a] at hin ⊢; rwa [hlen_eq]
          rw [dite_eq_right hin, dite_eq_right hin2]
      dsimp only [s_rep', s_anc_next]
      rw [← hsr_a_eq]
      exact hsch_p
    -- Extract `q_step` map on `(a, ws_src, wp, wb)`
    let q_ph5 : α → SeedWords c w capSrc → (Fin k_pre → Fin (2 ^ w)) →
        (Fin k_batch → Fin (2 ^ w)) → LatentRState (DualLatent c U V) rWhp :=
      fun a ws_src wp wb =>
        if ha : a ∈ μ_idx.support then
          let hc_t := hsupp_ph5 a ha ws_src wp
          let h5 := opCodeWhp_mutate_ph5_exec hc_t.1 o hv hfit_peak u v ho_mut hc_t.2.1
          let y_fn := h5.choose
          let h5_sp := h5.choose_spec.choose_spec.2
          let hcast : k_batch = _ := by
            dsimp only [k_batch, endOff, offBM, rMemState]; rw [hc_t.2.2.1, hc_t.2.2.2]
          let wb' := fun i => wb (Fin.cast hcast.symm i)
          let L_out : DualLatent c U V :=
            if hlt : endOff < offBM then
              ((h5_sp wb').2.2.2.2.2.2.1 (by
                dsimp only [endOff, offBM, rMemState] at hlt ⊢
                rw [hc_t.2.2.1, hc_t.2.2.2]; exact hlt)).choose
            else
              have heq_bm : endOff = offBM := le_antisymm
                (by dsimp only [endOff]; clear *- hcur_le_bm; omega) (Nat.not_lt.mp hlt)
              have hlen : k_pre + k_batch = (if capDst = 0 then 0 else offBM - 32) := by
                rw [ite_eq_right hd_pos.ne']; dsimp only [k_batch]
                clear *- hpre_eq_cur heq_bm; omega
              let ws_seed : SeedWords c w capDst :=
                fun i => (finAppendWords (extractPre (f5 a ws_src wp).data) wb)
                  (Fin.cast hlen.symm i)
              { ((f5 a ws_src wp).latent.applyFG 5 opTag u v) with
                slotDst := ⟨capDst, fun _ => none, seedsOfWords c U w capDst ws_seed, []⟩
                elapsed := (f5 a ws_src wp).latent.elapsed + 1 }
          ⟨L_out, y_fn wb'⟩
        else f5 a ws_src wp
    have hν'_eq : (ν.bind fun t => (μ_step t).map fun q => ⟨q.latent, q.data⟩) =
        μ_idx.bind (fun a =>
          (PMF.uniformOfFintype (SeedWords c w capSrc)).bind (fun ws_src =>
            (PMF.uniformOfFintype (Fin k_pre → Fin (2 ^ w))).bind (fun wp =>
              (PMF.uniformOfFintype (Fin k_batch → Fin (2 ^ w))).map
                (q_ph5 a ws_src wp)))) := by
      rw [hν, PMF.bind_bind]
      refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun a ha => ?_
      rw [PMF.bind_bind]
      refine congrArg ((PMF.uniformOfFintype _).bind ·) (funext fun ws_src => ?_)
      rw [PMF.bind_map]
      refine congrArg ((PMF.uniformOfFintype _).bind ·) (funext fun wp => ?_)
      have hc_t := hsupp_ph5 a ha ws_src wp
      dsimp only at hc_t
      dsimp only [Function.comp_def, μ_step, μStepPh5, q_ph5]
      rw [dite_eq_left hc_t, PMF.map_comp]
      refine congrArg ((PMF.uniformOfFintype _).map ·) (funext fun wb => ?_)
      dsimp only [Function.comp_def]; rw [dite_eq_left ha]
    let L_anc_next : α → SeedWords c w capSrc → DualLatent c U V := fun a ws_src =>
      if ha : a ∈ μ_idx.support then (hanc_step a ha ws_src).choose else L_anc a ws_src
    let splitPre : (Fin (k_pre + k_batch) → Fin (2 ^ w)) → (Fin k_pre → Fin (2 ^ w)) :=
      fun w_all i => w_all (Fin.castAdd k_batch i)
    let splitBat : (Fin (k_pre + k_batch) → Fin (2 ^ w)) → (Fin k_batch → Fin (2 ^ w)) :=
      fun w_all j => w_all (Fin.natAdd k_pre j)
    have hsplit_pre : ∀ (wp : Fin k_pre → Fin (2 ^ w)) (wb : Fin k_batch → Fin (2 ^ w)),
        splitPre (finAppendWords wp wb) = wp := fun wp wb => by
      funext i; dsimp only [splitPre, finAppendWords, Fin.val_castAdd]
      rw [dite_eq_left i.isLt]
    have hsplit_bat : ∀ (wp : Fin k_pre → Fin (2 ^ w)) (wb : Fin k_batch → Fin (2 ^ w)),
        splitBat (finAppendWords wp wb) = wb := fun wp wb => by
      funext j; dsimp only [splitBat, finAppendWords, Fin.val_natAdd]
      rw [dite_eq_right (by omega)]
      congr 1; ext; dsimp only; omega
    have hsplit_app : ∀ w_all : Fin (k_pre + k_batch) → Fin (2 ^ w),
        finAppendWords (splitPre w_all) (splitBat w_all) = w_all := fun w_all => by
      funext i; dsimp only [finAppendWords, splitPre, splitBat]
      split_ifs with hi
      · congr 1
      · congr 1; ext; dsimp only [Fin.val_natAdd]; omega
    refine ⟨L_rep', s_rep', hrep'_sp.1, ?_⟩
    dsimp only
    by_cases hlt : endOff < offBM
    · -- `5 → 5`: concatenate `wp` and `wb` via `finAppendWords` (`uniform_bind_finAppendWords`)
      have hp5_rep' : s_rep'.mem (base + hdrPhase) = 5 := by
        obtain ⟨ha0_inv, ha0_sch, _, _, _, hwp0⟩ := hf a₀ ha₀ ws_src0
        obtain ⟨hr0, hph5_0, _⟩ := hwp0 (fun _ => ⟨0, Nat.two_pow_pos w⟩)
        have hpad0 :
            base + dualPaddedWords c U V w ((s_anc a₀ ws_src0).mem (base + hdrNSrc))
              (if (s_anc a₀ ws_src0).mem (base + hdrPhase) = 0 then
                (s_anc a₀ ws_src0).mem (base + hdrNSrc)
               else (s_anc a₀ ws_src0).mem (base + hdrNDst))
              (Dictionary.dom (if opTag = 1 then Function.update s_dict u (some v.val)
                else Function.update s_dict u none)).card < 2 ^ w := by
          rwa [← ha0_sch.2 hdrNSrc (by decide) (by decide),
            ← ha0_sch.2 hdrPhase (by decide) (by decide),
            ← ha0_sch.2 hdrNDst (by decide) (by decide)]
        have hm0 := ph5_mutate_step ha0_inv hr0.2.2.2 hph5_0 hop_nz u v hv_eq
          hsucc_fits' hpad0
        have hc0 := (ha0_sch.2 hdrCur (by decide) (by decide)).symm
        have hd0 := (ha0_sch.2 hdrNDst (by decide) (by decide)).symm
        exact ((hm0.2 (fun _ => wordOfNat w 0)).1 (by
          dsimp only [endOff, offBM] at hlt; rw [hc0, hd0]; exact hlt)).1
      have hcapSrc'_eq : dualCapSrc base s_rep'.mem = capSrc :=
        (hrep'_sp.1.sl_le7 (by rw [hp5_rep']; decide)).1.symm.trans hrep'_sp.2.1
      rw [ite_eq_right (by clear *- hp5_rep'; omega), ite_eq_left hp5_rep', hcapSrc'_eq]
      let f5_next : α → SeedWords c w capSrc → (Fin (k_pre + k_batch) → Fin (2 ^ w)) →
          LatentRState (DualLatent c U V) rWhp :=
        fun a ws_src w_all => q_ph5 a ws_src (splitPre w_all) (splitBat w_all)
      refine ⟨α, μ_idx, k_pre + k_batch, fun a => evs_src a ++ [fgEv],
        L_anc_next, s_anc_next, f5_next, ?_, fun a ha ws_src => ?_⟩
      · rw [hν'_eq]
        refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun a ha => ?_
        refine congrArg ((PMF.uniformOfFintype _).bind ·) (funext fun ws_src => ?_)
        conv_rhs => rw [← uniform_bind_finAppendWords w k_pre k_batch, PMF.map_bind]
        refine congrArg ((PMF.uniformOfFintype _).bind ·) (funext fun wp => ?_)
        rw [PMF.map_comp]
        refine congrArg ((PMF.uniformOfFintype _).map ·) (funext fun wb => ?_)
        dsimp only [Function.comp_def, f5_next]
        rw [hsplit_pre wp wb, hsplit_bat wp wb]
      · have hanc_sp : DualStateInv c U V w base s_dict' (L_anc_next a ws_src)
            (s_anc_next a ws_src) ∧
          (L_anc_next a ws_src).slotSrc.nCap = capSrc ∧
          (L_anc_next a ws_src).slotSrc.evs = evs_src a ++ [fgEv] ∧
          (0 < capSrc →
            HEq (L_anc_next a ws_src).slotSrc.seeds (seedsOfWords c U w capSrc ws_src)) ∧
          HEq (L_anc_next a ws_src).slotSrc.seeds (L_anc a ws_src).slotSrc.seeds := by
          dsimp only [L_anc_next]; rw [dite_eq_left ha]
          exact (hanc_step a ha ws_src).choose_spec
        refine ⟨hanc_sp.1, hsch_anc_next a ha ws_src, hanc_sp.2.1, hanc_sp.2.2.1,
          hanc_sp.2.2.2.1, fun w_all => ?_⟩
        let wp := splitPre w_all
        let wb := splitBat w_all
        have happ_eq : finAppendWords wp wb = w_all := hsplit_app w_all
        obtain ⟨ha_inv, ha_sch, ha_nc, ha_ev, _, hwp⟩ := hf a ha ws_src
        obtain ⟨hr, hph5, hsl⟩ := hwp wp
        have hc_t := hsupp_ph5 a ha ws_src wp
        have hpad_a :
            base + dualPaddedWords c U V w ((s_anc a ws_src).mem (base + hdrNSrc))
              (if (s_anc a ws_src).mem (base + hdrPhase) = 0 then
                (s_anc a ws_src).mem (base + hdrNSrc)
               else (s_anc a ws_src).mem (base + hdrNDst))
              (Dictionary.dom (if opTag = 1 then Function.update s_dict u (some v.val)
                else Function.update s_dict u none)).card < 2 ^ w := by
          rwa [← ha_sch.2 hdrNSrc (by decide) (by decide),
            ← ha_sch.2 hdrPhase (by decide) (by decide),
            ← ha_sch.2 hdrNDst (by decide) (by decide)]
        have hm5 := ph5_mutate_step ha_inv hr.2.2.2 hph5 hop_nz u v hv_eq hsucc_fits' hpad_a
        have ha_cur : (s_anc a ws_src).mem (base + hdrCur) = cur :=
          (ha_sch.2 hdrCur (by decide) (by decide)).symm
        have ha_nd : (s_anc a ws_src).mem (base + hdrNDst) = capDst :=
          (ha_sch.2 hdrNDst (by decide) (by decide)).symm
        have hcast : k_batch =
            (((rMemState (f5 a ws_src wp).data).mem (base + hdrCur) +
              min bulkBatchWhp
                (offBktMeta c w ((rMemState (f5 a ws_src wp).data).mem (base + hdrNDst)) -
                  (rMemState (f5 a ws_src wp).data).mem (base + hdrCur))) -
              (rMemState (f5 a ws_src wp).data).mem (base + hdrCur)) := by
          dsimp only [k_batch, endOff, offBM, rMemState]; rw [hc_t.2.2.1, hc_t.2.2.2]
        have hcast_a : ((s_anc a ws_src).mem (base + hdrCur) +
            min bulkBatchWhp
              (offBktMeta c w ((s_anc a ws_src).mem (base + hdrNDst)) -
                (s_anc a ws_src).mem (base + hdrCur))) -
            (s_anc a ws_src).mem (base + hdrCur) = k_batch := by
          dsimp only [k_batch, endOff, offBM]; rw [ha_cur, ha_nd]
        let wb' := fun i => wb (Fin.cast hcast.symm i)
        let wb_a := fun i => wb (Fin.cast hcast_a i)
        have h5_sp :=
          (opCodeWhp_mutate_ph5_exec hc_t.1 o hv hfit_peak u v ho_mut
            hc_t.2.1).choose_spec.choose_spec.2
        obtain ⟨hy_mem, hyb, hy_base, hy_mfr, _, _, hy_lt, _⟩ := h5_sp wb'
        have hlt_t : ((rMemState (f5 a ws_src wp).data).mem (base + hdrCur) +
            min bulkBatchWhp
              (offBktMeta c w ((rMemState (f5 a ws_src wp).data).mem (base + hdrNDst)) -
                (rMemState (f5 a ws_src wp).data).mem (base + hdrCur))) <
            offBktMeta c w ((rMemState (f5 a ws_src wp).data).mem (base + hdrNDst)) := by
          dsimp only [rMemState]; rw [hc_t.2.2.1, hc_t.2.2.2]; exact hlt
        obtain ⟨hpres_t, hinv_t⟩ := (hy_lt hlt_t).choose_spec
        have hq_eq : f5_next a ws_src w_all =
            ⟨(hy_lt hlt_t).choose,
             (opCodeWhp_mutate_ph5_exec hc_t.1 o hv hfit_peak u v ho_mut hc_t.2.1).choose
               wb'⟩ := by
          dsimp only [f5_next, q_ph5, wp, wb]
          rw [dite_eq_left ha, dite_eq_left hlt]
        obtain ⟨_, hsr_eq⟩ := hph5_sr_eq a ha ws_src wp wb hcast hcast_a
        have hph5_post_raw := ((hm5.2 wb_a).1 (by
          dsimp only [endOff, offBM] at hlt; rw [ha_cur, ha_nd]; exact hlt)).2
        have hph5_post : Ph5StateAt c w base (s_anc_next a ws_src) (k_pre + k_batch)
            w_all (rMemState (f5_next a ws_src w_all).data) := by
          rw [hq_eq]; dsimp only
          rw [hy_mem, hsr_eq]
          refine ph5StateAt_cast (by rw [hcast_a]) (fun i => ?_) hph5_post_raw
          rw [← happ_eq]
          dsimp only [finAppendWords, wb_a, Fin.val_cast]
          split_ifs <;> rfl
        have hr_post : DualRep c U V w base s_dict' (f5_next a ws_src w_all).latent
            (f5_next a ws_src w_all).data := by
          rw [hq_eq]; exact ⟨hyb, hy_base, hy_mfr, hy_mem.symm ▸ hinv_t⟩
        refine ⟨hr_post, hph5_post, ?_⟩
        obtain ⟨hnc_t, hsd_t, hev_t⟩ := hpres_t.1.1 not_false
        have hfg_src_t : ((f5 a ws_src wp).latent.applyFG 5 opTag u v).slotSrc =
            (L_anc a ws_src).slotSrc.applyFG false opTag u v := by
          unfold DualLatent.applyFG; simp only [Nat.reduceLeDiff, ↓reduceIte]; rw [hsl]
        have hp5_anc' : (s_anc_next a ws_src).mem (base + hdrPhase) = 5 :=
          ((hsch_anc_next a ha ws_src).2 hdrPhase (by decide) (by decide)).symm.trans hp5_rep'
        have hp5_t' : (rMemState (f5_next a ws_src w_all).data).mem (base + hdrPhase) = 5 :=
          ((hph5_post.schedEq hanc_sp.1).2 hdrPhase (by decide) (by decide)).symm.trans hp5_anc'
        have habs_t := (hr_post.2.2.2.sl_le7 (by rw [hp5_t']; decide)).2.1
        have habs_a := (hanc_sp.1.sl_le7 (by rw [hp5_anc']; decide)).2.1
        rw [hq_eq]; dsimp only
        exact slotLatent_eq
          (by rw [hnc_t, hfg_src_t, SlotLatent.applyFG_nCap, ha_nc, hanc_sp.2.1])
          (by rw [hq_eq] at habs_t; exact habs_t.trans habs_a.symm)
          (hsd_t.trans (by rw [hfg_src_t]; exact (applyFG_seeds_heq ..).trans hanc_sp.2.2.2.2.symm))
          (by rw [hev_t, hfg_src_t, applyFG_false_evs, ha_ev, hanc_sp.2.2.1])
    · -- `5 → 6`: `endOff = offBM`, entering `Coupled67` with uniform `SeedWords c w capDst`
      have heq_bm : endOff = offBM :=
        le_antisymm (by dsimp only [endOff]; clear *- hcur_le_bm; omega) (Nat.not_lt.mp hlt)
      have hlen : k_pre + k_batch = (if capDst = 0 then 0 else offBM - 32) := by
        rw [ite_eq_right hd_pos.ne']; dsimp only [k_batch]
        clear *- hpre_eq_cur heq_bm; omega
      have hp6_and_nd : s_rep'.mem (base + hdrPhase) = 6 ∧
          s_rep'.mem (base + hdrNDst) = capDst := by
        obtain ⟨ha0_inv, ha0_sch, _, _, _, hwp0⟩ := hf a₀ ha₀ ws_src0
        obtain ⟨hr0, hph5_0, _⟩ := hwp0 (fun _ => ⟨0, Nat.two_pow_pos w⟩)
        have hpad0 :
            base + dualPaddedWords c U V w ((s_anc a₀ ws_src0).mem (base + hdrNSrc))
              (if (s_anc a₀ ws_src0).mem (base + hdrPhase) = 0 then
                (s_anc a₀ ws_src0).mem (base + hdrNSrc)
               else (s_anc a₀ ws_src0).mem (base + hdrNDst))
              (Dictionary.dom (if opTag = 1 then Function.update s_dict u (some v.val)
                else Function.update s_dict u none)).card < 2 ^ w := by
          rwa [← ha0_sch.2 hdrNSrc (by decide) (by decide),
            ← ha0_sch.2 hdrPhase (by decide) (by decide),
            ← ha0_sch.2 hdrNDst (by decide) (by decide)]
        have hm0 := ph5_mutate_step ha0_inv hr0.2.2.2 hph5_0 hop_nz u v hv_eq
          hsucc_fits' hpad0
        have hc0 := (ha0_sch.2 hdrCur (by decide) (by decide)).symm
        have hd0 := (ha0_sch.2 hdrNDst (by decide) (by decide)).symm
        have heq0 : (s_anc a₀ ws_src0).mem (base + hdrCur) +
            min bulkBatchWhp
              (offBktMeta c w ((s_anc a₀ ws_src0).mem (base + hdrNDst)) -
                (s_anc a₀ ws_src0).mem (base + hdrCur)) =
            offBktMeta c w ((s_anc a₀ ws_src0).mem (base + hdrNDst)) := by
          rw [hc0, hd0]; exact heq_bm
        obtain ⟨hp6_0, hc67_0, hinv_0⟩ := (hm0.2 (fun _ => wordOfNat w 0)).2 heq0
        refine ⟨hp6_0, (hc67_0.1.2 hdrNDst (by decide) (by decide)).trans ?_⟩
        -- In `s_post0` (`hinv_0`), either `nDst = 0` or `sl_67` identifies `nDst = capDst`;
        -- prove `s_rep'.mem (base + hdrNDst) = capDst` directly via `finishRandFill_hdr_eq`!
        have hw_pos : 0 < w := by have := ha0_inv.hw11; omega
        have hp5_0 : (s_anc a₀ ws_src0).mem (base + hdrPhase) = 5 :=
          (ha0_sch.2 hdrPhase (by decide) (by decide)).symm.trans hp5
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hpt0, _, _⟩ :=
          stepOpProg_mutate_spec ha0_inv hop_nz u v hv_eq hsucc_fits' hpad0
        let sg0 : Memory.State :=
          { mem := ((Memory.spec 0).clientState (s_anc a₀ ws_src0)
              (prepGrowProg (((base, (s_anc a₀ ws_src0).frontier), opTag), u.val))).mem
            frontier := (s_anc a₀ ws_src0).frontier +
              (Memory.spec 0).clientResult (s_anc a₀ ws_src0)
                (prepGrowProg (((base, (s_anc a₀ ws_src0).frontier), opTag), u.val)) }
        let sm0 := (Memory.spec 0).clientState sg0
          (userMutateProg ((base, opTag), (u.val, v_val)))
        let k0_len := ((s_anc a₀ ws_src0).mem (base + hdrCur) +
          min bulkBatchWhp
            (offBktMeta c w ((s_anc a₀ ws_src0).mem (base + hdrNDst)) -
              (s_anc a₀ ws_src0).mem (base + hdrCur))) -
          (s_anc a₀ ws_src0).mem (base + hdrCur)
        have hfg0 := fgStep_le7_aux ha0_inv u v hv_eq
          (fgSetup_of_dualStateInv ha0_inv hop_nz u v) rfl rfl rfl (by rw [hp5_0]; decide)
        have hsm0_ph : sm0.mem (base + hdrPhase) = 5 :=
          (hfg0.2.2.2.1 (base + hdrPhase) (by dsimp only [hdrPhase]; omega)
            (base_add_ne (by decide)) (base_add_ne (by decide))).trans hp5_0
        have hsm0_cur := hfg0.2.2.2.1 (base + hdrCur) (by dsimp only [hdrCur]; omega)
          (base_add_ne (by decide)) (base_add_ne (by decide))
        have hsm0_nd := hfg0.2.2.2.1 (base + hdrNDst) (by dsimp only [hdrNDst]; omega)
          (base_add_ne (by decide)) (base_add_ne (by decide))
        have hsm0_stg := hfg0.2.2.2.1 (base + hdrStage) (by dsimp only [hdrStage]; omega)
          (base_add_ne (by decide)) (base_add_ne (by decide))
        have hsm0_pad := hfg0.2.2.2.1 (base + hdrPad) (by dsimp only [hdrPad]; omega)
          (base_add_ne (by decide)) (base_add_ne (by decide))
        have hsm0_mb : dualMbDst base sm0.mem = dualMbDst base (s_anc a₀ ws_src0).mem := by
          unfold dualMbDst; rw [hsm0_ph, hsm0_nd, hsm0_stg, hsm0_pad, hp5_0]
        have hsm0_pd : dualPDst base sm0.mem = dualPDst base (s_anc a₀ ws_src0).mem := by
          unfold dualPDst; rw [hsm0_ph, hsm0_stg, hp5_0]
        have hbr0 := hpt0.2.2.2
        rw [ite_eq_right (not_not.mpr hsm0_ph)] at hbr0
        dsimp only at hbr0
        rw [hsm0_cur, hsm0_nd, hsm0_mb, hsm0_pd] at hbr0
        obtain ⟨_, _, hph_r0, hstg_r0, hcur_r0, hp31_r0, _, hmid_eq0⟩ :=
          hbr0.2.2.2.2.2.2.2.2.2 (fun _ : Fin k0_len => wordOfNat w 0)
        let st0 := (Memory.spec 0).clientState sg0
          (stepOpProg (((base, sg0.frontier), opTag), (u.val, v_val)))
        let sr0 : Memory.State :=
          { mem := writeWords st0.mem
              (dualMbDst base (s_anc a₀ ws_src0).mem +
                (s_anc a₀ ws_src0).mem (base + hdrCur))
              (fun _ : Fin k0_len => wordOfNat w 0)
            frontier := st0.frontier }
        change sr0.mem (base + hdrPhase) = 5 at hph_r0
        change sr0.mem (base + hdrStage) = sm0.mem (base + hdrStage) at hstg_r0
        change sr0.mem (base + hdrCur) = _ at hcur_r0
        change sr0.mem (dualPDst base (s_anc a₀ ws_src0).mem + 31) = _ at hp31_r0
        have hmid_r0 : DualMidInv c U V w base _ _ sr0 := hmid_eq0 heq0
        have hpD_r0 : dualPDst base sr0.mem = dualPDst base (s_anc a₀ ws_src0).mem := by
          unfold dualPDst; rw [hph_r0, hstg_r0, hsm0_stg, hp5_0]
        have hdone_r0 : sr0.mem (dualPDst base sr0.mem + 31) ≤ sr0.mem (base + hdrCur) := by
          rw [hpD_r0, hp31_r0, hcur_r0, heq0]
        obtain ⟨hpre_rf0, _, _, _, _, hpre_sh0⟩ :=
          finishRandFillProg_spec hmid_r0 hph_r0 hdone_r0
        have hdone_if0 : sr0.mem ((if sr0.mem (base + hdrStage) = 0 then base + hdrPBase1
            else base + hdrPBase0) + 31) ≤ sr0.mem (base + hdrCur) := by
          have hpD_i : (if sr0.mem (base + hdrStage) = 0 then base + hdrPBase1
              else base + hdrPBase0) = dualPDst base sr0.mem := by
            unfold dualPDst; rw [hph_r0, ite_eq_left (by decide : 5 < 10)]
          rw [hpD_i]; exact hdone_r0
        have hw_rf0 := dualPreShrinkInv_hdr_w hpre_sh0
        have hph_rf0 : ((Memory.spec 0).clientState sr0 (finishRandFillProg base)).mem
            (base + hdrPhase) = 6 := by
          rw [(finishRandFillProg_eval base sr0).1]; exact Function.update_self ..
        have hsps0_eq : (Memory.spec 0).clientState sr0
            (postRandShrinkProg ((base, sr0.frontier), opTag)) =
            (Memory.spec 0).clientState sr0 (finishRandFillProg base) := by
          rw [(postRandShrinkProg_eval base sr0.frontier opTag sr0).1]; dsimp only
          rw [ite_eq_right hop_nz, ite_eq_left ⟨hph_r0, hdone_if0⟩,
            (calcPostShrinkProg_eval (curFr := sr0.frontier) (hw_rf0 ▸ hw_pos)).1]; dsimp only
          rw [hph_rf0, ite_eq_right (fun h => absurd h.1 (by decide))]
        have hb192_0 : base + 192 ≤ sr0.frontier -
            (Memory.spec 0).clientResult sr0
              (postRandShrinkProg ((base, sr0.frontier), opTag)) := hrep'_sp.1.base_fr
        have hsr0_nd : sr0.mem (base + hdrNDst) = capDst := by
          have hmd_192 : base + 192 ≤ dualMbDst base (s_anc a₀ ws_src0).mem := by
            unfold dualMbDst
            rw [hp5_0, ite_eq_left (by decide : 5 < 10), ite_eq_right (hd0.symm ▸ hd_pos.ne')]
            split_ifs <;> omega
          dsimp only [sr0, st0]
          rw [writeWords_apply_out _ _ _ (by dsimp only [hdrNDst]; omega),
            (stepOpProg_eval _ _ _ _ _ _).1, ite_eq_right hop_nz]
          change ((Memory.spec 0).clientState sm0 (bgTickProg (base, _))).mem (base + hdrNDst) =
            capDst
          rw [(bgTickProg_eval _ _ _).1, hsm0_ph]
          simp only [Nat.reduceEqDiff, ↓reduceIte]
          rw [(tickRandPrepProg_eval base sm0).1]; dsimp only
          rw [Function.update_of_ne (base_add_ne (by decide)), hsm0_nd, hd0]
        have hrep'_nd : s_rep'.mem (base + hdrNDst) = capDst := by
          change clear ((Memory.spec 0).clientState sr0
              (postRandShrinkProg ((base, sr0.frontier), opTag))).mem
            (sr0.frontier - (Memory.spec 0).clientResult sr0
              (postRandShrinkProg ((base, sr0.frontier), opTag)))
            ((Memory.spec 0).clientResult sr0
              (postRandShrinkProg ((base, sr0.frontier), opTag)))
            (base + hdrNDst) = capDst
          rw [hsps0_eq,
            clear_of_not_owns (by
              simp only [Block.Owns]; dsimp only [hdrNDst]; clear *- hb192_0; omega),
            finishRandFill_hdr_eq hmid_r0 hph_r0 hpre_rf0 (by decide) (by decide) (by decide)]
          exact hsr0_nd
        exact (hc67_0.1.2 hdrNDst (by decide) (by decide)).symm.trans hrep'_nd
      obtain ⟨hp6_rep', hnd_rep'⟩ := hp6_and_nd
      have hcapSrc'_eq : dualCapSrc base s_rep'.mem = capSrc :=
        (hrep'_sp.1.sl_le7 (by rw [hp6_rep']; decide)).1.symm.trans hrep'_sp.2.1
      rw [ite_eq_right (by clear *- hp6_rep'; omega),
        ite_eq_right (by clear *- hp6_rep'; omega),
        ite_eq_left (Or.inl hp6_rep'), hcapSrc'_eq, hnd_rep']
      let e_seed : (Fin (k_pre + k_batch) → Fin (2 ^ w)) ≃ SeedWords c w capDst :=
        Equiv.arrowCongr (finCongr hlen) (Equiv.refl (Fin (2 ^ w)))
      let f67_next : α → SeedWords c w capSrc → SeedWords c w capDst →
          LatentRState (DualLatent c U V) rWhp :=
        fun a ws_src ws_dst =>
          q_ph5 a ws_src (splitPre (e_seed.symm ws_dst)) (splitBat (e_seed.symm ws_dst))
      refine ⟨α, μ_idx, fun a => evs_src a ++ [fgEv], L_anc_next, s_anc_next, f67_next,
        ?_, fun a ha ws_src => ?_⟩
      · rw [hν'_eq]
        refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun a ha => ?_
        refine congrArg ((PMF.uniformOfFintype _).bind ·) (funext fun ws_src => ?_)
        conv_rhs =>
          rw [← PMF.uniformOfFintype_map_equiv e_seed,
            ← uniform_bind_finAppendWords w k_pre k_batch,
            PMF.map_bind, PMF.map_bind]
        refine congrArg ((PMF.uniformOfFintype _).bind ·) (funext fun wp => ?_)
        rw [PMF.map_comp, PMF.map_comp]
        refine congrArg ((PMF.uniformOfFintype _).map ·) (funext fun wb => ?_)
        dsimp only [Function.comp_def, f67_next]
        rw [e_seed.symm_apply_apply, hsplit_pre wp wb, hsplit_bat wp wb]
      · have hanc_sp : DualStateInv c U V w base s_dict' (L_anc_next a ws_src)
            (s_anc_next a ws_src) ∧
          (L_anc_next a ws_src).slotSrc.nCap = capSrc ∧
          (L_anc_next a ws_src).slotSrc.evs = evs_src a ++ [fgEv] ∧
          (0 < capSrc →
            HEq (L_anc_next a ws_src).slotSrc.seeds (seedsOfWords c U w capSrc ws_src)) ∧
          HEq (L_anc_next a ws_src).slotSrc.seeds (L_anc a ws_src).slotSrc.seeds := by
          dsimp only [L_anc_next]; rw [dite_eq_left ha]
          exact (hanc_step a ha ws_src).choose_spec
        refine ⟨hanc_sp.1, hsch_anc_next a ha ws_src, hanc_sp.2.1, hanc_sp.2.2.1,
          hanc_sp.2.2.2.1, fun ws_dst => ?_⟩
        let w_all := e_seed.symm ws_dst
        let wp := splitPre w_all
        let wb := splitBat w_all
        have happ_eq : finAppendWords wp wb = w_all := hsplit_app w_all
        have hseed_cast :
            (fun i => (finAppendWords wp wb) (Fin.cast hlen.symm i)) = ws_dst := by
          rw [happ_eq]
          exact e_seed.apply_symm_apply ws_dst
        have hc_t := hsupp_ph5 a ha ws_src wp
        dsimp only at hc_t
        obtain ⟨ha_inv, ha_sch, ha_nc, ha_ev, _, hwp⟩ := hf a ha ws_src
        obtain ⟨hr, hph5, hsl⟩ := hwp wp
        have hcast : k_batch =
            (((rMemState (f5 a ws_src wp).data).mem (base + hdrCur) +
              min bulkBatchWhp
                (offBktMeta c w ((rMemState (f5 a ws_src wp).data).mem (base + hdrNDst)) -
                  (rMemState (f5 a ws_src wp).data).mem (base + hdrCur))) -
              (rMemState (f5 a ws_src wp).data).mem (base + hdrCur)) := by
          dsimp only [k_batch, endOff, offBM, rMemState]; rw [hc_t.2.2.1, hc_t.2.2.2]
        have hmem_f5 : f5 a ws_src wp ∈ ν.support := by
          rw [hν, PMF.mem_support_bind_iff]
          refine ⟨a, ha, ?_⟩
          rw [PMF.mem_support_bind_iff]
          exact ⟨ws_src, PMF.mem_support_uniformOfFintype _,
            (PMF.mem_support_map_iff _ _ _).mpr
              ⟨wp, PMF.mem_support_uniformOfFintype _, rfl⟩⟩
        have hq_mem : (⟨(f67_next a ws_src ws_dst).latent, (f67_next a ws_src ws_dst).data,
            res_o,
            (opCodeWhp_mutate_ph5_exec hc_t.1 o hv hfit_peak u v ho_mut
              hc_t.2.1).choose_spec.choose
              (fun i => wb (Fin.cast hcast.symm i)), true⟩ :
            WhpStepROutcome _ _ rWhp) ∈ (μ_step (f5 a ws_src wp)).support := by
          dsimp only [μ_step, μStepPh5]
          rw [dite_eq_left hc_t, PMF.mem_support_map_iff]
          refine ⟨wb, PMF.mem_support_uniformOfFintype _, ?_⟩
          dsimp only [f67_next, q_ph5, wp, wb, w_all]
          rw [dite_eq_left ha, dite_eq_right hlt]
        have hr_post : DualRep c U V w base s_dict' (f67_next a ws_src ws_dst).latent
            (f67_next a ws_src ws_dst).data :=
          ((hstep_all (f5 a ws_src wp) hmem_f5).2 _ hq_mem).2.2.1
        have hpad_a :
            base + dualPaddedWords c U V w ((s_anc a ws_src).mem (base + hdrNSrc))
              (if (s_anc a ws_src).mem (base + hdrPhase) = 0 then
                (s_anc a ws_src).mem (base + hdrNSrc)
               else (s_anc a ws_src).mem (base + hdrNDst))
              (Dictionary.dom (if opTag = 1 then Function.update s_dict u (some v.val)
                else Function.update s_dict u none)).card < 2 ^ w := by
          rwa [← ha_sch.2 hdrNSrc (by decide) (by decide),
            ← ha_sch.2 hdrPhase (by decide) (by decide),
            ← ha_sch.2 hdrNDst (by decide) (by decide)]
        have hm5 := ph5_mutate_step ha_inv hr.2.2.2 hph5 hop_nz u v hv_eq hsucc_fits' hpad_a
        have ha_cur : (s_anc a ws_src).mem (base + hdrCur) = cur :=
          (ha_sch.2 hdrCur (by decide) (by decide)).symm
        have ha_nd : (s_anc a ws_src).mem (base + hdrNDst) = capDst :=
          (ha_sch.2 hdrNDst (by decide) (by decide)).symm
        have ha_mb : dualMbDst base (s_anc a ws_src).mem = metaDst := ha_sch.mbDst_eq.symm
        have ht_mb : dualMbDst base (f5 a ws_src wp).data.mem = metaDst :=
          (ha_sch.trans (hph5.schedEq ha_inv)).mbDst_eq.symm
        have hcast_a : ((s_anc a ws_src).mem (base + hdrCur) +
            min bulkBatchWhp
              (offBktMeta c w ((s_anc a ws_src).mem (base + hdrNDst)) -
                (s_anc a ws_src).mem (base + hdrCur))) -
            (s_anc a ws_src).mem (base + hdrCur) = k_batch := by
          dsimp only [k_batch, endOff, offBM]; rw [ha_cur, ha_nd]
        let wb' := fun i => wb (Fin.cast hcast.symm i)
        let wb_a := fun i => wb (Fin.cast hcast_a i)
        have hc67_raw := ((hm5.2 wb_a).2 (by
          dsimp only [endOff, offBM] at heq_bm; rw [ha_cur, ha_nd]; exact heq_bm)).2.1
        have h5_sp :=
          (opCodeWhp_mutate_ph5_exec hc_t.1 o hv hfit_peak u v ho_mut
            hc_t.2.1).choose_spec.choose_spec.2
        have hy_mem := (h5_sp wb').1
        let s_t := rMemState (f5 a ws_src wp).data
        let s_a := s_anc a ws_src
        let sg_t : Memory.State :=
          { mem := ((Memory.spec 0).clientState s_t
              (prepGrowProg (((base, s_t.frontier), opTag), u.val))).mem
            frontier := s_t.frontier +
              (Memory.spec 0).clientResult s_t
                (prepGrowProg (((base, s_t.frontier), opTag), u.val)) }
        let sg_a : Memory.State :=
          { mem := ((Memory.spec 0).clientState s_t
              (prepGrowProg (((base, s_t.frontier), opTag), u.val))).mem
            frontier := s_t.frontier +
              (Memory.spec 0).clientResult s_a
                (prepGrowProg (((base, s_a.frontier), opTag), u.val)) }
        let st_t := (Memory.spec 0).clientState sg_t
          (stepOpProg (((base, sg_t.frontier), opTag), (u.val, v_val)))
        let st_a := (Memory.spec 0).clientState sg_a
          (stepOpProg (((base, sg_a.frontier), opTag), (u.val, v_val)))
        have hkg_eq := (schedEq_mutate_step (v_val := v_val) ha_inv hr.2.2.2
          (hph5.schedEq ha_inv) hop_nz u v hv_eq hsucc_fits' hpad_a).1
        dsimp only at hkg_eq
        have hsg_eq : sg_t = sg_a := by dsimp only [sg_t, sg_a]; rw [hkg_eq]
        have hst_eq : st_t = st_a := by dsimp only [st_t, st_a]; rw [hsg_eq]
        have hww_eq :
            writeWords st_t.mem (dualMbDst base s_t.mem + s_t.mem (base + hdrCur)) wb' =
              writeWords st_a.mem (dualMbDst base s_a.mem + s_a.mem (base + hdrCur)) wb_a := by
          have haddr_t : dualMbDst base s_t.mem + s_t.mem (base + hdrCur) = metaDst + cur := by
            dsimp only [s_t, rMemState]; rw [ht_mb, hc_t.2.2.1]
          have haddr_a : dualMbDst base s_a.mem + s_a.mem (base + hdrCur) = metaDst + cur := by
            rw [ha_mb, ha_cur]
          rw [hst_eq, haddr_t, haddr_a]
          funext addr; unfold writeWords
          by_cases hin : metaDst + cur ≤ addr ∧ addr < (metaDst + cur) + k_batch
          · have hin1 := hcast ▸ hin
            have hin2 := hcast_a.symm ▸ hin
            rw [dite_eq_left hin1, dite_eq_left hin2]; rfl
          · have hin1 := hcast ▸ hin
            have hin2 := hcast_a.symm ▸ hin
            rw [dite_eq_right hin1, dite_eq_right hin2]
        have hsr_eq :
            ({ mem := writeWords st_t.mem (dualMbDst base s_t.mem + s_t.mem (base + hdrCur)) wb'
               frontier := st_t.frontier } : Memory.State) =
            { mem := writeWords st_a.mem (dualMbDst base s_a.mem + s_a.mem (base + hdrCur)) wb_a
              frontier := st_a.frontier } :=
          Memory.State.ext hww_eq (by rw [hst_eq])
        have hq_eq : f67_next a ws_src ws_dst =
            ⟨{ ((f5 a ws_src wp).latent.applyFG 5 opTag u v) with
                slotDst := ⟨capDst, fun _ => none, seedsOfWords c U w capDst ws_dst, []⟩
                elapsed := (f5 a ws_src wp).latent.elapsed + 1 },
             (opCodeWhp_mutate_ph5_exec hc_t.1 o hv hfit_peak u v ho_mut hc_t.2.1).choose
               wb'⟩ := by
          dsimp only [f67_next, q_ph5, wp, wb, w_all]
          rw [dite_eq_left ha, dite_eq_right hlt, hextract_pre a ha ws_src wp, hseed_cast]
        have hc67_post : Coupled67 c w base (s_anc_next a ws_src)
            (rMemState (f67_next a ws_src ws_dst).data) := by
          rw [hq_eq]; dsimp only
          rw [hy_mem, hsr_eq]
          exact hc67_raw
        have hp6_anc' : (s_anc_next a ws_src).mem (base + hdrPhase) = 6 :=
          ((hsch_anc_next a ha ws_src).2 hdrPhase (by decide) (by decide)).symm.trans hp6_rep'
        have hp6_t' : (rMemState (f67_next a ws_src ws_dst).data).mem (base + hdrPhase) = 6 :=
          (hc67_post.1.2 hdrPhase (by decide) (by decide)).symm.trans hp6_anc'
        have habs_t := (hr_post.2.2.2.sl_le7 (by rw [hp6_t']; decide)).2.1
        have habs_a := (hanc_sp.1.sl_le7 (by rw [hp6_anc']; decide)).2.1
        have hfg_src_t : ((f5 a ws_src wp).latent.applyFG 5 opTag u v).slotSrc =
            (L_anc a ws_src).slotSrc.applyFG false opTag u v := by
          unfold DualLatent.applyFG; simp only [Nat.reduceLeDiff, ↓reduceIte]; rw [hsl]
        refine ⟨hr_post, hc67_post, ?_, fun _ => ?_⟩
        · refine slotLatent_eq ?_ (habs_t.trans habs_a.symm) ?_ ?_
          · rw [hq_eq]; dsimp only; rw [hfg_src_t, SlotLatent.applyFG_nCap]
            exact ha_nc.trans hanc_sp.2.1.symm
          · rw [hq_eq]; dsimp only; rw [hfg_src_t]
            exact (applyFG_seeds_heq ..).trans hanc_sp.2.2.2.2.symm
          · rw [hq_eq]; dsimp only; rw [hfg_src_t, applyFG_false_evs, ha_ev, hanc_sp.2.2.1]
        · rw [hq_eq]; exact ⟨rfl, rfl, HEq.rfl⟩
  · -- Slow-path probability in Phase `5` (`slotSrc` of `L_anc.applyFG 5`)
    rw [hν, PMF.bind_bind]
    refine toOuterMeasure_bind_le_const μ_idx _ _ _ fun a ha => ?_
    rw [PMF.bind_bind]
    let μ_src := PMF.uniformOfFintype (SeedWords c w capSrc)
    let sl_mid := fun ws_src => ((L_anc a ws_src).slotSrc.applyFG false opTag u v)
    have h_inner : ∀ ws_src : SeedWords c w capSrc,
        (((PMF.uniformOfFintype (Fin k_pre → Fin (2 ^ w))).map (f5 a ws_src)).bind μ_step
          ).toOuterMeasure {q | ¬q.WithinBudget (worstCaseTimeWhp c)} ≤
        if (sl_mid ws_src).GoodCovers then 0 else 1 := fun ws_src => by
      obtain ⟨_, _, _, _, _, hwp⟩ := hf a ha ws_src
      by_cases hgc : (sl_mid ws_src).GoodCovers
      · rw [ite_eq_left hgc]
        refine toOuterMeasure_bind_le_const _ _ _ 0 fun t ht => ?_
        rw [PMF.mem_support_map_iff] at ht; obtain ⟨wp, _, rfl⟩ := ht
        have hc_t := hsupp_ph5 a ha ws_src wp
        have hsl := (hwp wp).2.2
        have h5_sp :=
          (opCodeWhp_mutate_ph5_exec hc_t.1 o hv hfit_peak u v ho_mut
            hc_t.2.1).choose_spec.choose_spec.2
        dsimp only [μ_step, μStepPh5]; rw [dite_eq_left hc_t]
        refine (toOuterMeasure_map_bad_eq_zero _ _ _ fun wb hnb => ?_).le
        simp only [Set.mem_ofPred_eq] at hnb
        apply hnb
        have hgc_t : ((f5 a ws_src wp).latent.applyFG 5 opTag u v).slotSrc.GoodCovers := by
          unfold DualLatent.applyFG; simp only [Nat.reduceLeDiff, ↓reduceIte]; rw [hsl]
          exact hgc
        exact ⟨rfl, (h5_sp _).2.2.2.2.2.2.2 hgc_t⟩
      · rw [ite_eq_right hgc]; exact PMF.toOuterMeasure_le_one _ _
    calc (μ_src.bind _).toOuterMeasure _
        = ∑' ws_src, μ_src ws_src * _ := PMF.toOuterMeasure_bind_apply _ _ _
      _ ≤ ∑' ws_src, μ_src ws_src * (if (sl_mid ws_src).GoodCovers then 0 else 1) :=
          tsum_le_tsum fun ws_src => mul_le_mul_right (h_inner ws_src) _
      _ = μ_src.toOuterMeasure {ws_src | ¬(sl_mid ws_src).GoodCovers} := by
          rw [PMF.toOuterMeasure_apply]
          refine tsum_congr fun ws_src => ?_
          by_cases hg : (sl_mid ws_src).GoodCovers <;> simp only [hg, ↓reduceIte, mul_zero,
            mul_one, Set.mem_ofPred_eq, not_true_eq_false, Set.indicator_of_notMem,
            not_false_eq_true, Set.indicator_of_mem]
      _ ≤ stepFailureProbWhp c s_dict o := by
          refine (uniform_seedWords_bad_le hUw hsrc_safe (evs_src a ++ [fgEv]) sl_mid
            (fun ws => by
              dsimp only [sl_mid]; rw [SlotLatent.applyFG_nCap]; exact (hf a ha ws).2.2.1)
            (fun ws => by dsimp only [sl_mid]; rw [applyFG_false_evs, (hf a ha ws).2.2.2.1])
            (fun hc ws => by
              dsimp only [sl_mid]
              exact (applyFG_seeds_heq ..).trans ((hf a ha ws).2.2.2.2.1 hc))
            fun hc => ?_).trans
            (half_stepFailureProb_le c s_dict o)
          let ws₀ := zeroSeedWords c w capSrc
          obtain ⟨ha_inv₀, ha_sch₀, ha_nc₀, ha_ev₀, _, _⟩ := hf a ha ws₀
          have hpad0 :
              base + dualPaddedWords c U V w ((s_anc a ws₀).mem (base + hdrNSrc))
                (if (s_anc a ws₀).mem (base + hdrPhase) = 0 then
                  (s_anc a ws₀).mem (base + hdrNSrc)
                 else (s_anc a ws₀).mem (base + hdrNDst))
                (Dictionary.dom (if opTag = 1 then Function.update s_dict u (some v.val)
                  else Function.update s_dict u none)).card < 2 ^ w := by
            rwa [← ha_sch₀.2 hdrNSrc (by decide) (by decide),
              ← ha_sch₀.2 hdrPhase (by decide) (by decide),
              ← ha_sch₀.2 hdrNDst (by decide) (by decide)]
          obtain ⟨_, _, _, _, _, _, _, _, _, _, hmid₀, _, _, _⟩ :=
            stepOpProg_mutate_spec ha_inv₀ hop_nz u v hv_eq hsucc_fits' hpad0
          have hp5_0 : (s_anc a ws₀).mem (base + hdrPhase) = 5 :=
            (ha_sch₀.2 hdrPhase (by decide) (by decide)).symm.trans hp5
          have hfg0 := fgStep_le7_aux ha_inv₀ u v hv_eq
            (fgSetup_of_dualStateInv ha_inv₀ hop_nz u v) rfl rfl rfl (by rw [hp5_0]; decide)
          have hsm_ph5 : ((Memory.spec 0).clientState _
              (userMutateProg ((base, opTag), (u.val, v_val)))).mem (base + hdrPhase) = 5 :=
            (hfg0.2.2.2.1 (base + hdrPhase) (by dsimp only [hdrPhase]; omega)
              (base_add_ne (by decide)) (base_add_ne (by decide))).trans hp5_0
          have hfg_src0 : ((L_anc a ws₀).applyFG ((s_anc a ws₀).mem (base + hdrPhase))
              opTag u v).slotSrc = sl_mid ws₀ := by
            rw [hp5_0]; rfl
          have hnc_m : (sl_mid ws₀).nCap = capSrc := by
            dsimp only [sl_mid]; rw [SlotLatent.applyFG_nCap]; exact ha_nc₀
          have hev_m : (sl_mid ws₀).evs = evs_src a ++ [fgEv] := by
            dsimp only [sl_mid]; rw [applyFG_false_evs, ha_ev₀]
          have hb₀ := (dualCoreInv_slot_evs_bounds hmid₀).1 (by rw [hsm_ph5]; decide)
            (by rw [hfg_src0, hnc_m]; exact hc)
          rw [hfg_src0, hnc_m, hev_m] at hb₀
          exact hb₀

private theorem dualDistInv_mutate_67 {c U V w base opTag v_val : ℕ}
    (s_dict : Dictionary.State U) (o : Dynamic.Op U)
    (hv : (Dynamic.spec U V U).valid s_dict o)
    (u : Fin U) (v : Fin V)
    (ho_mut : (o = .insert u v.val ∧ opTag = 1 ∧ v_val = v.val) ∨
      (o = .delete u ∧ opTag = 2 ∧ v_val = 0))
    (ν : PMF (LatentRState (DualLatent c U V) rWhp))
    (hfit_peak : Fits w (base + stepSuccinctPeakWordsWhp c V w s_dict o))
    {L_rep : DualLatent c U V} {s_rep : Memory.State}
    (hinv_rep : DualStateInv c U V w base s_dict L_rep s_rep)
    (hp67 : s_rep.mem (base + hdrPhase) = 6 ∨ s_rep.mem (base + hdrPhase) = 7)
    (hregimes : Coupled67Law c U V w base s_dict s_rep
      (dualCapSrc base s_rep.mem) (s_rep.mem (base + hdrNDst)) ν) :
    MutateStepPost c U V w base s_dict o ν := by
  classical
  set s_dict' := ((Dynamic.spec U V U).stepFn s_dict o).1
  set res_o := ((Dynamic.spec U V U).stepFn s_dict o).2
  obtain ⟨hop_nz, hv_eq, hs_dict'_eq, hsucc_fits', hpad_rep_fits'⟩ :=
    mutate_setup_bounds ho_mut hfit_peak hinv_rep
  let fgEv : EpochUpdate U V := if opTag = 1 then .insert u v else .delete u
  have hUw : Fits w U := hinv_rep.U_lt
  set ph := s_rep.mem (base + hdrPhase)
  set capSrc := dualCapSrc base s_rep.mem
  set capDst := s_rep.mem (base + hdrNDst)
  have hsrc_safe := dualCapSrc_safe hinv_rep
  obtain ⟨α, μ_idx, evs_src, L_anc, s_anc, f67, hν, hf⟩ := hregimes
  obtain ⟨a₀, ha₀⟩ := μ_idx.support_nonempty
  let ws_src0 := zeroSeedWords c w capSrc
  let wd0 := zeroSeedWords c w capDst
  let stepNon58 : ∀ {t : LatentRState (DualLatent c U V) rWhp}
      (hr : DualRep c U V w base s_dict t.latent t.data)
      (hne5 : t.data.mem (base + hdrPhase) ≠ 5)
      (hne8 : t.data.mem (base + hdrPhase) ≠ 8), _ := fun hr hne5 hne8 =>
    opCodeWhp_mutate_non58_exec hr o hv hfit_peak u v ho_mut hne5 hne8
  let q_det := qDetNon58 s_dict o hv hfit_peak u v ho_mut
  let μ_step := fun t => PMF.pure (q_det t)
  have hsupp_67 : ∀ a ∈ μ_idx.support, ∀ ws_src wd,
      let t := f67 a ws_src wd
      DualRep c U V w base s_dict t.latent t.data ∧
      t.data.mem (base + hdrPhase) ≠ 5 ∧
      t.data.mem (base + hdrPhase) ≠ 8 ∧
      (t.data.mem (base + hdrPhase) = 6 ∨ t.data.mem (base + hdrPhase) = 7) := by
    intro a ha ws_src wd
    obtain ⟨_, ha_sch, _, _, _, hwd⟩ := hf a ha ws_src
    obtain ⟨hr, hc67, _, _⟩ := hwd wd
    have hsch_t := ha_sch.trans hc67.1
    have hp_t : (f67 a ws_src wd).data.mem (base + hdrPhase) = ph :=
      (hsch_t.2 hdrPhase (by decide) (by decide)).symm
    exact ⟨hr, by clear *- hp_t hp67; omega,
      by clear *- hp_t hp67; omega, hp_t ▸ hp67⟩
  have hstep_all : ∀ t ∈ ν.support,
      ExecRCodeSteps w opCodeWhp ((subroutineCodeWhp c U V w).prepare whpEncode o t.data)
        ((μ_step t).map WhpStepROutcome.toCodeOutcome)
        (base + stepSuccinctPeakWordsWhp c V w s_dict o) ∧
      ∀ q ∈ (μ_step t).support,
        q.result = res_o ∧ whpDecode (V := V) o q.data.regs = some q.result ∧
        DualRep c U V w base s_dict' q.latent q.data ∧
        (∀ addr < base, q.data.mem addr = t.data.mem addr) := by
    intro t ht
    rw [hν, PMF.mem_support_bind_iff] at ht; obtain ⟨a, ha, hm1⟩ := ht
    rw [PMF.mem_support_bind_iff] at hm1; obtain ⟨ws_src, _, hm2⟩ := hm1
    rw [PMF.mem_support_map_iff] at hm2; obtain ⟨wd, _, rfl⟩ := hm2
    obtain ⟨hr, hne5, hne8, _⟩ := hsupp_67 a ha ws_src wd
    have hc_t : DualRep c U V w base s_dict _ _ ∧ _ ∧ _ := ⟨hr, hne5, hne8⟩
    have hsp := (stepNon58 hr hne5 hne8).choose_spec.choose_spec.choose_spec.choose_spec
    dsimp only [μ_step, q_det, qDetNon58]; rw [dite_eq_left hc_t, PMF.pure_map]
    refine ⟨hsp.1, fun q hq => ?_⟩
    rw [PMF.mem_support_pure_iff] at hq; subst hq
    exact ⟨rfl, hsp.2.2.2.2.2.2.2.2.2.1, hsp.2.2.1, hsp.2.2.2.2.2.2.2.2.2.2.1⟩
  -- Post-step slot properties and `Coupled67` / `Coupled8` vs `f67 a ws_src wd0`
  let f_step : α → SeedWords c w capSrc → SeedWords c w capDst →
      LatentRState (DualLatent c U V) rWhp :=
    fun a ws_src wd => ⟨(q_det (f67 a ws_src wd)).latent, (q_det (f67 a ws_src wd)).data⟩
  have hf_post67 : ∀ a ∈ μ_idx.support, ∀ ws_src wd,
      let t := f67 a ws_src wd
      let q := q_det t
      DualRep c U V w base s_dict' q.latent q.data ∧
      SchedEq base (rMemState (q_det (f67 a₀ ws_src0 wd0)).data) (rMemState q.data) ∧
      (rMemState q.data).mem (base + hdrNDst) = capDst ∧
      q.latent.slotSrc.nCap = capSrc ∧
      q.latent.slotSrc.evs = evs_src a ++ [fgEv] ∧
      HEq q.latent.slotSrc.seeds (L_anc a ws_src).slotSrc.seeds ∧
      (0 < capDst →
        q.latent.slotDst.nCap = capDst ∧
        q.latent.slotDst.evs = [] ∧
        HEq q.latent.slotDst.seeds (seedsOfWords c U w capDst wd)) ∧
      ((t.latent.applyFG (t.data.mem (base + hdrPhase)) opTag u v).slotSrc.GoodCovers →
        q.steps ≤ worstCaseTimeWhp c) ∧
      (((rMemState (f_step a ws_src wd0).data).mem (base + hdrPhase) = 6 ∨
          (rMemState (f_step a ws_src wd0).data).mem (base + hdrPhase) = 7) ∧
        Coupled67 c w base (rMemState (f_step a ws_src wd0).data) (rMemState q.data) ∨
       (rMemState (f_step a ws_src wd0).data).mem (base + hdrPhase) = 8 ∧
        Coupled8 c V w base (Dictionary.dom s_dict').card
          (rMemState (f_step a ws_src wd0).data) (rMemState q.data)) := by
    intro a ha ws_src wd
    obtain ⟨ha_inv, ha_sch, ha_nc, ha_ev, _, hwd⟩ := hf a ha ws_src
    obtain ⟨hr, hc67_t, hsl_t, hdst_t⟩ := hwd wd
    obtain ⟨hr_a0, hc67_a0, _, _⟩ := hwd wd0
    obtain ⟨hr₀, hc67_0, _, _⟩ := (hf a₀ ha₀ ws_src0).2.2.2.2.2 wd0
    have hsch₀ := (hf a₀ ha₀ ws_src0).2.1.trans hc67_0.1
    have hsch_t := ha_sch.trans hc67_t.1
    obtain ⟨_, hne5_t, hne8_t, hp67_t⟩ := hsupp_67 a ha ws_src wd
    obtain ⟨_, hne5_a0, hne8_a0, hp67_a0⟩ := hsupp_67 a ha ws_src wd0
    obtain ⟨_, hne5_0, hne8_0, _⟩ := hsupp_67 a₀ ha₀ ws_src0 wd0
    have hc_t : DualRep c U V w base s_dict _ _ ∧ _ ∧ _ := ⟨hr, hne5_t, hne8_t⟩
    have hc_a0 : DualRep c U V w base s_dict _ _ ∧ _ ∧ _ := ⟨hr_a0, hne5_a0, hne8_a0⟩
    have hc_0 : DualRep c U V w base s_dict _ _ ∧ _ ∧ _ := ⟨hr₀, hne5_0, hne8_0⟩
    have hsp := (stepNon58 hr hne5_t hne8_t).choose_spec.choose_spec.choose_spec.choose_spec
    have hsp_a0 :=
      (stepNon58 hr_a0 hne5_a0 hne8_a0).choose_spec.choose_spec.choose_spec.choose_spec
    have hsp_0 :=
      (stepNon58 hr₀ hne5_0 hne8_0).choose_spec.choose_spec.choose_spec.choose_spec
    obtain ⟨hy_mem, hr_post, hmid, hsm_ph, htick_eq, hpre_sh, hpres1, hpres2, _, _, hT⟩ :=
      hsp.2
    have hsm_67 := hp67_t
    dsimp only [rMemState] at hsm_ph
    rw [← hsm_ph] at hsm_67
    have hpre_sh' := preShrink_congr_st hpre_sh htick_eq
    have hcls := bgTick_post_from_67 hop_nz hmid hsm_67 hpre_sh'
      (stateInv_congr_st hr_post.2.2.2 (by rw [hy_mem]; dsimp only; rw [htick_eq]))
    obtain ⟨hnc1, hsd1, hev1⟩ := hpres1.1.1 (fun ⟨h9, _⟩ => by clear *- h9 hp67_t; omega)
    obtain ⟨hnc2, hsd2, hev2⟩ := hpres2.1.1
      (fun ⟨h11, _⟩ => by rw [htick_eq] at h11; exact hcls.1 h11)
    have hfg_src : ((f67 a ws_src wd).latent.applyFG
        ((f67 a ws_src wd).data.mem (base + hdrPhase)) opTag u v).slotSrc =
        (L_anc a ws_src).slotSrc.applyFG false opTag u v := by
      unfold DualLatent.applyFG
      rw [ite_eq_left (by clear *- hp67_t; omega), hsl_t]
    have hfg_dst : ((f67 a ws_src wd).latent.applyFG
        ((f67 a ws_src wd).data.mem (base + hdrPhase)) opTag u v).slotDst =
        (f67 a ws_src wd).latent.slotDst := by
      unfold DualLatent.applyFG
      rw [ite_eq_left (by clear *- hp67_t; omega)]
    have hfg_t := fgStep_le7_aux hr.2.2.2 u v hv_eq
      (fgSetup_of_dualStateInv hr.2.2.2 hop_nz u v) rfl rfl rfl
      (by change (f67 a ws_src wd).data.mem (base + hdrPhase) ≤ 7
          clear *- hp67_t; omega)
    have hsm_nd := (hfg_t.2.2.2.1 (base + hdrNDst) (by dsimp only [hdrNDst]; omega)
      (base_add_ne (by decide)) (base_add_ne (by decide))).trans
      (hsch_t.2 hdrNDst (by decide) (by decide)).symm
    have hnd_post : (rMemState (q_det (f67 a ws_src wd)).data).mem (base + hdrNDst) = capDst := by
      dsimp only [q_det, qDetNon58]; rw [dite_eq_left hc_t]
      change (rMemState (stepNon58 hr hne5_t hne8_t).choose).mem (base + hdrNDst) = capDst
      rw [congrArg Memory.State.mem hy_mem]; dsimp only; rw [htick_eq]
      exact hcls.2.trans hsm_nd
    -- `SchedEq` vs `(f67 a₀ ws_src0 wd0)`
    have hpad₀ :
        base + dualPaddedWords c U V w ((rMemState (f67 a₀ ws_src0 wd0).data).mem
            (base + hdrNSrc))
          (if (rMemState (f67 a₀ ws_src0 wd0).data).mem (base + hdrPhase) = 0 then
            (rMemState (f67 a₀ ws_src0 wd0).data).mem (base + hdrNSrc)
           else (rMemState (f67 a₀ ws_src0 wd0).data).mem (base + hdrNDst))
          (Dictionary.dom (if opTag = 1 then Function.update s_dict u (some v.val)
            else Function.update s_dict u none)).card < 2 ^ w := by
      rw [← hsch₀.2 hdrNSrc (by decide) (by decide),
        ← hsch₀.2 hdrPhase (by decide) (by decide),
        ← hsch₀.2 hdrNDst (by decide) (by decide)]
      exact hpad_rep_fits'
    obtain ⟨_, _, _, hps_ne5_0, _⟩ :=
      schedEq_mutate_step (v_val := v_val) hr₀.2.2.2 hr.2.2.2 (hsch₀.symm.trans hsch_t)
        hop_nz u v hv_eq hsucc_fits' hpad₀
    obtain ⟨_, hsch_post0⟩ := hps_ne5_0 hne5_0
    -- `coupled67_mutate_step` vs `f67 a ws_src wd0`
    have hc67_pair := coupled67_trans (coupled67_symm hc67_a0) hc67_t
    have hpad_a0 :
        base + dualPaddedWords c U V w ((rMemState (f67 a ws_src wd0).data).mem
            (base + hdrNSrc))
          (if (rMemState (f67 a ws_src wd0).data).mem (base + hdrPhase) = 0 then
            (rMemState (f67 a ws_src wd0).data).mem (base + hdrNSrc)
           else (rMemState (f67 a ws_src wd0).data).mem (base + hdrNDst))
          (Dictionary.dom (if opTag = 1 then Function.update s_dict u (some v.val)
            else Function.update s_dict u none)).card < 2 ^ w := by
      have hsch_a0 := ha_sch.trans hc67_a0.1
      rw [← hsch_a0.2 hdrNSrc (by decide) (by decide),
        ← hsch_a0.2 hdrPhase (by decide) (by decide),
        ← hsch_a0.2 hdrNDst (by decide) (by decide)]
      exact hpad_rep_fits'
    have hc67_out := coupled67_mutate_step hr_a0.2.2.2 hr.2.2.2 hc67_pair hp67_a0
      hop_nz u v hv_eq hsucc_fits' hpad_a0
    dsimp only at hc67_out
    obtain ⟨hkg_a0, _, _, hps_ne5_a0, _⟩ :=
      schedEq_mutate_step (v_val := v_val) hr_a0.2.2.2 hr.2.2.2 hc67_pair.1
        hop_nz u v hv_eq hsucc_fits' hpad_a0
    obtain ⟨hksh_a0, _⟩ := hps_ne5_a0 hne5_a0
    dsimp only at hkg_a0 hksh_a0
    rw [← hkg_a0] at hksh_a0
    rw [hs_dict'_eq] at hc67_out
    have hq_eq : q_det (f67 a ws_src wd) =
        ⟨(stepNon58 hr hne5_t hne8_t).choose_spec.choose_spec.choose_spec.choose,
         (stepNon58 hr hne5_t hne8_t).choose, res_o,
         (stepNon58 hr hne5_t hne8_t).choose_spec.choose, true⟩ := by
      dsimp only [q_det, qDetNon58]; rw [dite_eq_left hc_t]
    have hq0_data : (q_det (f67 a₀ ws_src0 wd0)).data =
        (stepNon58 hr₀ hne5_0 hne8_0).choose := by
      dsimp only [q_det, qDetNon58]; rw [dite_eq_left hc_0]
    have hqa0_data : (f_step a ws_src wd0).data =
        (stepNon58 hr_a0 hne5_a0 hne8_a0).choose := by
      dsimp only [f_step, q_det, qDetNon58]; rw [dite_eq_left hc_a0]
    have hc67_goal :
        (((rMemState (f_step a ws_src wd0).data).mem (base + hdrPhase) = 6 ∨
            (rMemState (f_step a ws_src wd0).data).mem (base + hdrPhase) = 7) ∧
          Coupled67 c w base (rMemState (f_step a ws_src wd0).data)
            (rMemState (q_det (f67 a ws_src wd)).data)) ∨
        ((rMemState (f_step a ws_src wd0).data).mem (base + hdrPhase) = 8 ∧
          Coupled8 c V w base (Dictionary.dom s_dict').card
            (rMemState (f_step a ws_src wd0).data)
            (rMemState (q_det (f67 a ws_src wd)).data)) := by
      rw [hqa0_data, hsp_a0.2.1, hq_eq]; dsimp only
      rw [hy_mem]; dsimp only; rw [← hkg_a0, ← hksh_a0]
      exact hc67_out
    refine ⟨by rw [hq_eq]; exact hr_post,
      by rw [hq0_data, hsp_0.2.1, hq_eq]; dsimp only; rw [hy_mem]; exact hsch_post0,
      hnd_post,
      by rw [hq_eq]; dsimp only; rw [hnc2, hnc1, hfg_src, SlotLatent.applyFG_nCap]; exact ha_nc,
      by rw [hq_eq]; dsimp only; rw [hev2, hev1, hfg_src, applyFG_false_evs, ha_ev],
      by rw [hq_eq]; dsimp only
         exact hsd2.trans (hsd1.trans (by rw [hfg_src]; exact applyFG_seeds_heq ..)),
      fun hcd_pos => ?_,
      fun hgc => by rw [hq_eq]; exact hT (fun _ => hgc) (fun h9 => by clear *- h9 hp67_t; omega),
      hc67_goal⟩
    -- `slotDst` preservation when `0 < capDst` (`ph' ∈ {6, 7, 8}`)
    obtain ⟨hd_nc, hd_ev, hd_sd⟩ := hdst_t hcd_pos
    have hd_post_pos : 0 < (q_det (f67 a ws_src wd)).latent.slotDst.nCap := by
      have hp_post_678 :
          (rMemState (q_det (f67 a ws_src wd)).data).mem (base + hdrPhase) = 6 ∨
          (rMemState (q_det (f67 a ws_src wd)).data).mem (base + hdrPhase) = 7 ∨
          (rMemState (q_det (f67 a ws_src wd)).data).mem (base + hdrPhase) = 8 := by
        rcases hc67_goal with ⟨hp_a0, hc67'⟩ | ⟨hp_a0, hc8'⟩
        · rw [← hc67'.1.2 hdrPhase (by decide) (by decide)]
          exact hp_a0.imp id Or.inl
        · rw [← hc8'.1.2 hdrPhase (by decide) (by decide)]
          exact Or.inr (Or.inr hp_a0)
      have hr_p : DualRep c U V w base s_dict' (q_det (f67 a ws_src wd)).latent
          (q_det (f67 a ws_src wd)).data := by rw [hq_eq]; exact hr_post
      rcases hp_post_678 with h6 | h7 | h8
      · rw [(hr_p.2.2.2.sl_67 (Or.inl h6)).2 (hnd_post ▸ hcd_pos) |>.1, hnd_post]
        exact hcd_pos
      · rw [(hr_p.2.2.2.sl_67 (Or.inr h7)).2 (hnd_post ▸ hcd_pos) |>.1, hnd_post]
        exact hcd_pos
      · rw [(hr_p.2.2.2.sl_8 h8).2.1, hnd_post]; exact hcd_pos
    rw [hq_eq] at hd_post_pos ⊢; dsimp only at hd_post_pos ⊢
    obtain ⟨hnd2, hsd_d2, _, hev_d2⟩ := hpres2.2.resolve_left hd_post_pos.ne'
    obtain ⟨hnd1, hsd_d1, _, hev_d1⟩ :=
      hpres1.2.resolve_left (hnd2 ▸ hd_post_pos.ne')
    exact ⟨by rw [hnd2, hnd1, hfg_dst]; exact hd_nc,
      by rw [hev_d2 not_false, hev_d1 not_false, hfg_dst]; exact hd_ev,
      hsd_d2.trans (hsd_d1.trans (by rw [hfg_dst]; exact hd_sd))⟩
  let L_rep' := (f_step a₀ ws_src0 wd0).latent
  let s_rep' := rMemState (f_step a₀ ws_src0 wd0).data
  have hpost0 := hf_post67 a₀ ha₀ ws_src0 wd0
  have hinv_rep' : DualStateInv c U V w base s_dict' L_rep' s_rep' := hpost0.1.2.2.2
  have hν'_bind : (ν.bind fun t => (μ_step t).map fun q => ⟨q.latent, q.data⟩) =
      μ_idx.bind (fun a =>
        (PMF.uniformOfFintype (SeedWords c w capSrc)).bind (fun ws_src =>
          (PMF.uniformOfFintype (SeedWords c w capDst)).map (f_step a ws_src))) := by
    rw [hν, PMF.bind_bind]
    refine congrArg (μ_idx.bind ·) (funext fun a => ?_)
    rw [PMF.bind_bind]
    refine congrArg ((PMF.uniformOfFintype _).bind ·) (funext fun ws_src => ?_)
    rw [PMF.bind_map]; dsimp only [μ_step]
    conv_rhs => unfold PMF.map
    refine congrArg ((PMF.uniformOfFintype _).bind ·) (funext fun wd => ?_)
    dsimp only [Function.comp_def]; rw [PMF.pure_map]
  refine ⟨μ_step, hstep_all, ⟨L_rep', s_rep', hinv_rep', ?_⟩, ?_⟩
  · dsimp only
    have hnd_rep' : s_rep'.mem (base + hdrNDst) = capDst := hpost0.2.2.1
    rcases hpost0.2.2.2.2.2.2.2.2 with ⟨hp67', _⟩ | ⟨hp8', _⟩
    · -- `6/7 → 6/7`: stays in `Coupled67`
      change s_rep'.mem (base + hdrPhase) = 6 ∨ s_rep'.mem (base + hdrPhase) = 7 at hp67'
      have hcapSrc'_eq : dualCapSrc base s_rep'.mem = capSrc :=
        (hinv_rep'.sl_le7 (by clear *- hp67'; omega)).1.symm.trans
          hpost0.2.2.2.1
      rw [ite_eq_right (by clear *- hp67'; omega),
        ite_eq_right (by clear *- hp67'; omega),
        ite_eq_left hp67', hcapSrc'_eq, hnd_rep']
      refine ⟨α, μ_idx, fun a => evs_src a ++ [fgEv],
        fun a ws_src => (f_step a ws_src wd0).latent,
        fun a ws_src => rMemState (f_step a ws_src wd0).data,
        f_step, hν'_bind, fun a ha ws_src => ?_⟩
      have hp_a0 := hf_post67 a ha ws_src wd0
      refine ⟨hp_a0.1.2.2.2, hp_a0.2.1, hp_a0.2.2.2.1, hp_a0.2.2.2.2.1,
        fun hc => hp_a0.2.2.2.2.2.1.trans ((hf a ha ws_src).2.2.2.2.1 hc), fun wd => ?_⟩
      have hp_wd := hf_post67 a ha ws_src wd
      have hc67_wd : Coupled67 c w base (rMemState (f_step a ws_src wd0).data)
          (rMemState (f_step a ws_src wd).data) := by
        rcases hp_wd.2.2.2.2.2.2.2.2 with ⟨_, hc⟩ | ⟨hp8_a, _⟩
        · exact hc
        · exfalso
          have hp_eq : s_rep'.mem (base + hdrPhase) = 8 :=
            (hp_a0.2.1.2 hdrPhase (by decide) (by decide)).trans hp8_a
          clear *- hp_eq hp67'; omega
      have hp_wd_le7 : (rMemState (f_step a ws_src wd).data).mem (base + hdrPhase) ≤ 7 := by
        have hp_eq : (rMemState (f_step a ws_src wd).data).mem (base + hdrPhase) =
            s_rep'.mem (base + hdrPhase) :=
          (hp_wd.2.1.2 hdrPhase (by decide) (by decide)).symm
        clear *- hp_eq hp67'; omega
      have hp_a0_le7 : (rMemState (f_step a ws_src wd0).data).mem (base + hdrPhase) ≤ 7 := by
        have hp_eq : (rMemState (f_step a ws_src wd0).data).mem (base + hdrPhase) =
            s_rep'.mem (base + hdrPhase) :=
          (hp_a0.2.1.2 hdrPhase (by decide) (by decide)).symm
        clear *- hp_eq hp67'; omega
      have habs_wd := (hp_wd.1.2.2.2.sl_le7 hp_wd_le7).2.1
      have habs_a0 := (hp_a0.1.2.2.2.sl_le7 hp_a0_le7).2.1
      refine ⟨hp_wd.1, hc67_wd,
        slotLatent_eq (hp_wd.2.2.2.1.trans hp_a0.2.2.2.1.symm)
          (habs_wd.trans habs_a0.symm)
          (hp_wd.2.2.2.2.2.1.trans hp_a0.2.2.2.2.2.1.symm)
          (hp_wd.2.2.2.2.1.trans hp_a0.2.2.2.2.1.symm),
        hp_wd.2.2.2.2.2.2.1⟩
    · -- `7 → 8`: enters `Coupled8`
      change s_rep'.mem (base + hdrPhase) = 8 at hp8'
      have hcapSrc'_eq : dualCapSrc base s_rep'.mem = capSrc :=
        (hinv_rep'.sl_8 hp8').1.symm.trans hpost0.2.2.2.1
      rw [ite_eq_right (by clear *- hp8'; omega), ite_eq_right (by clear *- hp8'; omega),
        ite_eq_right (by clear *- hp8'; omega), ite_eq_left hp8', hcapSrc'_eq, hnd_rep']
      refine ⟨α, μ_idx, fun a => evs_src a ++ [fgEv],
        fun a ws_src => (f_step a ws_src wd0).latent.slotDst.evs,
        fun a ws_src => (f_step a ws_src wd0).latent,
        fun a ws_src => rMemState (f_step a ws_src wd0).data,
        f_step, hν'_bind, fun a ha ws_src => ?_⟩
      have hp_a0 := hf_post67 a ha ws_src wd0
      refine ⟨hp_a0.1.2.2.2, hp_a0.2.1, hp_a0.2.2.2.1, hp_a0.2.2.2.2.1,
        fun hc => hp_a0.2.2.2.2.2.1.trans ((hf a ha ws_src).2.2.2.2.1 hc), rfl,
        fun wd => ?_⟩
      by_cases hcd0 : capDst = 0
      · have hwd_eq : wd = wd0 := @Subsingleton.elim _
          (hcd0 ▸ subsingleton_seedWords_zero c w) wd wd0
        subst hwd_eq
        have hc8_a0 : Coupled8 c V w base (Dictionary.dom s_dict').card
            (rMemState (f_step a ws_src wd0).data)
            (rMemState (f_step a ws_src wd0).data) := by
          rcases hp_a0.2.2.2.2.2.2.2.2 with ⟨hp67_a, _⟩ | ⟨_, hc8⟩
          · exfalso
            have hp_eq : (rMemState (f_step a ws_src wd0).data).mem (base + hdrPhase) =
                s_rep'.mem (base + hdrPhase) :=
              (hp_a0.2.1.2 hdrPhase (by decide) (by decide)).symm
            clear *- hp_eq hp67_a hp8'; omega
          · exact hc8
        have hp8_a0 : (rMemState (f_step a ws_src wd0).data).mem (base + hdrPhase) = 8 :=
          (hp_a0.2.1.2 hdrPhase (by decide) (by decide)).symm.trans hp8'
        exact ⟨hp_a0.1, hc8_a0, rfl,
          (hp_a0.1.2.2.2.sl_8 hp8_a0).2.1.trans hp_a0.2.2.1,
          rfl, rfl, fun hpos => absurd hcd0 hpos.ne'⟩
      · have hcd_pos : 0 < capDst := Nat.pos_of_ne_zero hcd0
        have hp_wd := hf_post67 a ha ws_src wd
        have hc8_wd : Coupled8 c V w base (Dictionary.dom s_dict').card
            (rMemState (f_step a ws_src wd0).data)
            (rMemState (f_step a ws_src wd).data) := by
          rcases hp_wd.2.2.2.2.2.2.2.2 with ⟨hp67_a, _⟩ | ⟨_, hc8⟩
          · exfalso
            have hp_eq : (rMemState (f_step a ws_src wd0).data).mem (base + hdrPhase) =
                s_rep'.mem (base + hdrPhase) :=
              (hp_a0.2.1.2 hdrPhase (by decide) (by decide)).symm
            clear *- hp_eq hp67_a hp8'; omega
          · exact hc8
        have hp8_wd : (rMemState (f_step a ws_src wd).data).mem (base + hdrPhase) = 8 :=
          (hp_wd.2.1.2 hdrPhase (by decide) (by decide)).symm.trans hp8'
        have hp8_a0 : (rMemState (f_step a ws_src wd0).data).mem (base + hdrPhase) = 8 :=
          (hp_a0.2.1.2 hdrPhase (by decide) (by decide)).symm.trans hp8'
        obtain ⟨hd_nc_w, hd_ev_w, hd_sd_w⟩ := hp_wd.2.2.2.2.2.2.1 hcd_pos
        obtain ⟨hd_nc_0, hd_ev_0, _⟩ := hp_a0.2.2.2.2.2.2.1 hcd_pos
        obtain ⟨_, _, _, hdict_w, _, _, hsl_dw, _, _⟩ := hp_wd.1.2.2.2.sl_8 hp8_wd
        obtain ⟨_, _, _, hdict_0, _, _, hsl_d0, _, _⟩ := hp_a0.1.2.2.2.sl_8 hp8_a0
        have habs_dw : (f_step a ws_src wd).latent.slotDst.s_abs = fun _ => none := by
          unfold EpochSlotInv at hsl_dw
          rw [ite_eq_right (hd_nc_w ▸ hcd0)] at hsl_dw
          have hev := hsl_dw.2.2.2.2.1
          rwa [hd_ev_w, eq_comm] at hev
        have habs_d0 : (f_step a ws_src wd0).latent.slotDst.s_abs = fun _ => none := by
          unfold EpochSlotInv at hsl_d0
          rw [ite_eq_right (hd_nc_0 ▸ hcd0)] at hsl_d0
          have hev := hsl_d0.2.2.2.2.1
          rwa [hd_ev_0, eq_comm] at hev
        rw [habs_dw, orOpt_empty_left] at hdict_w
        rw [habs_d0, orOpt_empty_left] at hdict_0
        refine ⟨hp_wd.1, hc8_wd,
          slotLatent_eq (hp_wd.2.2.2.1.trans hp_a0.2.2.2.1.symm)
            (hdict_w.trans hdict_0.symm)
            (hp_wd.2.2.2.2.2.1.trans hp_a0.2.2.2.2.2.1.symm)
            (hp_wd.2.2.2.2.1.trans hp_a0.2.2.2.2.1.symm),
          hd_nc_w, habs_dw.trans habs_d0.symm, hd_ev_w.trans hd_ev_0.symm,
          fun _ => hd_sd_w⟩
  · -- Slow-path probability in Phases `6..7` (`slotSrc` of `L_anc.applyFG`)
    rw [hν, PMF.bind_bind]
    refine toOuterMeasure_bind_le_const μ_idx _ _ _ fun a ha => ?_
    rw [PMF.bind_bind]
    let μ_src := PMF.uniformOfFintype (SeedWords c w capSrc)
    let sl_mid := fun ws_src => (L_anc a ws_src).slotSrc.applyFG false opTag u v
    have h_inner : ∀ ws_src : SeedWords c w capSrc,
        (((PMF.uniformOfFintype (SeedWords c w capDst)).map (f67 a ws_src)).bind μ_step
          ).toOuterMeasure {q | ¬q.WithinBudget (worstCaseTimeWhp c)} ≤
        if (sl_mid ws_src).GoodCovers then 0 else 1 := fun ws_src => by
      by_cases hgc : (sl_mid ws_src).GoodCovers
      · rw [ite_eq_left hgc]
        refine toOuterMeasure_bind_le_const _ _ _ 0 fun t ht => ?_
        rw [PMF.mem_support_map_iff] at ht; obtain ⟨wd, _, rfl⟩ := ht
        obtain ⟨_, _, _, hp67_t⟩ := hsupp_67 a ha ws_src wd
        have hsl := ((hf a ha ws_src).2.2.2.2.2 wd).2.2.1
        have hgc_t : ((f67 a ws_src wd).latent.applyFG
            ((f67 a ws_src wd).data.mem (base + hdrPhase)) opTag u v).slotSrc.GoodCovers := by
          unfold DualLatent.applyFG
          rw [ite_eq_left (by clear *- hp67_t; omega), hsl]; exact hgc
        have hT := (hf_post67 a ha ws_src wd).2.2.2.2.2.2.2.1 hgc_t
        have htimed : (q_det (f67 a ws_src wd)).timed = true := by
          dsimp only [q_det, qDetNon58]; split_ifs <;> rfl
        dsimp only [μ_step]
        rw [PMF.toOuterMeasure_apply]
        refine (tsum_eq_zero_iff.mpr fun q => ?_).le
        by_cases hq_eq : q = q_det (f67 a ws_src wd)
        · subst hq_eq
          have hnot : q_det (f67 a ws_src wd) ∉
              {q | ¬q.WithinBudget (worstCaseTimeWhp c)} := fun hnb => hnb ⟨htimed, hT⟩
          exact Set.indicator_of_notMem hnot _
        · rw [Set.indicator_apply]
          split_ifs
          · exact PMF.pure_apply_of_ne _ _ hq_eq
          · rfl
      · rw [ite_eq_right hgc]; exact PMF.toOuterMeasure_le_one _ _
    calc (μ_src.bind _).toOuterMeasure _
        = ∑' ws_src, μ_src ws_src * _ := PMF.toOuterMeasure_bind_apply _ _ _
      _ ≤ ∑' ws_src, μ_src ws_src * (if (sl_mid ws_src).GoodCovers then 0 else 1) :=
          tsum_le_tsum fun ws_src => mul_le_mul_right (h_inner ws_src) _
      _ = μ_src.toOuterMeasure {ws_src | ¬(sl_mid ws_src).GoodCovers} := by
          rw [PMF.toOuterMeasure_apply]
          refine tsum_congr fun ws_src => ?_
          by_cases hg : (sl_mid ws_src).GoodCovers <;>
            simp only [hg, ↓reduceIte, mul_zero, mul_one, Set.mem_ofPred_eq,
              not_true_eq_false, Set.indicator_of_notMem, not_false_eq_true,
              Set.indicator_of_mem]
      _ ≤ stepFailureProbWhp c s_dict o := by
          refine (uniform_seedWords_bad_le hUw hsrc_safe (evs_src a ++ [fgEv]) sl_mid
            (fun ws => by
              dsimp only [sl_mid]; rw [SlotLatent.applyFG_nCap]; exact (hf a ha ws).2.2.1)
            (fun ws => by dsimp only [sl_mid]; rw [applyFG_false_evs, (hf a ha ws).2.2.2.1])
            (fun hc ws => by
              dsimp only [sl_mid]
              exact (applyFG_seeds_heq ..).trans ((hf a ha ws).2.2.2.2.1 hc))
            fun hc => ?_).trans
            (half_stepFailureProb_le c s_dict o)
          let ws₀ := zeroSeedWords c w capSrc
          obtain ⟨ha_inv₀, ha_sch₀, ha_nc₀, ha_ev₀, _, _⟩ := hf a ha ws₀
          have hp67_0 : (s_anc a ws₀).mem (base + hdrPhase) = 6 ∨
              (s_anc a ws₀).mem (base + hdrPhase) = 7 := by
            rw [(ha_sch₀.2 hdrPhase (by decide) (by decide)).symm]; exact hp67
          have hpad0 :
              base + dualPaddedWords c U V w ((s_anc a ws₀).mem (base + hdrNSrc))
                (if (s_anc a ws₀).mem (base + hdrPhase) = 0 then
                  (s_anc a ws₀).mem (base + hdrNSrc)
                 else (s_anc a ws₀).mem (base + hdrNDst))
                (Dictionary.dom (if opTag = 1 then Function.update s_dict u (some v.val)
                  else Function.update s_dict u none)).card < 2 ^ w := by
            rwa [← ha_sch₀.2 hdrNSrc (by decide) (by decide),
              ← ha_sch₀.2 hdrPhase (by decide) (by decide),
              ← ha_sch₀.2 hdrNDst (by decide) (by decide)]
          obtain ⟨_, _, _, _, _, _, _, _, _, _, hmid₀, _, _, _⟩ :=
            stepOpProg_mutate_spec ha_inv₀ hop_nz u v hv_eq hsucc_fits' hpad0
          have hfg0 := fgStep_le7_aux ha_inv₀ u v hv_eq
            (fgSetup_of_dualStateInv ha_inv₀ hop_nz u v) rfl rfl rfl
            (by clear *- hp67_0; omega)
          have hsm_ph : ((Memory.spec 0).clientState _
              (userMutateProg ((base, opTag), (u.val, v_val)))).mem (base + hdrPhase) =
              (s_anc a ws₀).mem (base + hdrPhase) :=
            hfg0.2.2.2.1 (base + hdrPhase) (by dsimp only [hdrPhase]; omega)
              (base_add_ne (by decide)) (base_add_ne (by decide))
          have hfg_src0 : ((L_anc a ws₀).applyFG ((s_anc a ws₀).mem (base + hdrPhase))
              opTag u v).slotSrc = sl_mid ws₀ := by
            unfold DualLatent.applyFG
            rw [ite_eq_left (by clear *- hp67_0; omega)]
          have hnc_m : (sl_mid ws₀).nCap = capSrc := by
            dsimp only [sl_mid]; rw [SlotLatent.applyFG_nCap]; exact ha_nc₀
          have hev_m : (sl_mid ws₀).evs = evs_src a ++ [fgEv] := by
            dsimp only [sl_mid]; rw [applyFG_false_evs, ha_ev₀]
          have hb₀ := (dualCoreInv_slot_evs_bounds hmid₀).1
            (by rw [hsm_ph]; clear *- hp67_0; omega)
            (by rw [hfg_src0, hnc_m]; exact hc)
          rw [hfg_src0, hnc_m, hev_m] at hb₀
          exact hb₀

private noncomputable def qPh8 {c U V w base opTag v_val : ℕ}
    (s_dict : Dictionary.State U) (o : Dynamic.Op U)
    (hv : (Dynamic.spec U V U).valid s_dict o)
    (hfit_peak : Fits w (base + stepSuccinctPeakWordsWhp c V w s_dict o))
    (u : Fin U) (v : Fin V)
    (ho_mut : (o = .insert u v.val ∧ opTag = 1 ∧ v_val = v.val) ∨
      (o = .delete u ∧ opTag = 2 ∧ v_val = 0))
    (dflt t : LatentRState (DualLatent c U V) rWhp) :
    WhpStepROutcome (DualLatent c U V) ((Dynamic.spec U V U).Result o) rWhp := by
  classical
  have hop_nz : opTag ≠ 0 := by rcases ho_mut with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> decide
  have hv_eq : opTag = 1 → v_val = v.val := by
    rcases ho_mut with ⟨_, _, hv_v⟩ | ⟨_, rfl, _⟩
    · exact fun _ => hv_v
    · intro h; cases h
  have hs_dict'_eq :
      (if opTag = 1 then Function.update s_dict u (some v.val)
       else Function.update s_dict u none) = ((Dynamic.spec U V U).stepFn s_dict o).1 := by
    rcases ho_mut with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ <;> rfl
  have hsucc_fits' :
      base + spaceBoundWhp c V w
        (if opTag = 1 then Function.update s_dict u (some v.val)
         else Function.update s_dict u none) < 2 ^ w := by
    rw [hs_dict'_eq]
    exact lt_of_le_of_lt (Nat.add_le_add_left (le_max_right _ _) base) hfit_peak
  exact
    if hc : DualRep c U V w base s_dict t.latent t.data ∧
        t.data.mem (base + hdrPhase) = 8 then
      let hd_ex := opCodeWhp_mutate_det_exec hc.1 o hv hfit_peak u v ho_mut
        (by rw [hc.2]; decide)
      let hrel := rep8_rel dflt hc.1 hc.2
      let hc8_step := coupled8_mutate_step hrel.1.2.2.2 hrel.2.2.1
        hop_nz u v hv_eq hsucc_fits'
        (lt_of_le_of_lt
          (Nat.add_le_add_left (dualPaddedWords_step_le_peak hrel.1.2.2.2 hop_nz u v).2 base)
          hsucc_fits')
      let hinst := hc8_step.choose_spec.choose_spec.choose_spec
        hc.1.2.2.2 hrel.2.2.2.1 hrel.2.2.2.2.1 hrel.2.2.2.2.2.1 hrel.2.2.2.2.2.2
      ⟨hinst.1.choose, hd_ex.choose, ((Dynamic.spec U V U).stepFn s_dict o).2,
        hd_ex.choose_spec.choose, true⟩
    else ⟨t.latent, t.data, ((Dynamic.spec U V U).stepFn s_dict o).2, 0, true⟩

private theorem qPh8_spec {c U V w base opTag v_val : ℕ}
    (s_dict : Dictionary.State U) (o : Dynamic.Op U)
    (hv : (Dynamic.spec U V U).valid s_dict o)
    (hfit_peak : Fits w (base + stepSuccinctPeakWordsWhp c V w s_dict o))
    (u : Fin U) (v : Fin V)
    (ho_mut : (o = .insert u v.val ∧ opTag = 1 ∧ v_val = v.val) ∨
      (o = .delete u ∧ opTag = 2 ∧ v_val = 0))
    (hop_nz : opTag ≠ 0) (hv_eq : opTag = 1 → v_val = v.val)
    (hsucc_fits' :
      base + spaceBoundWhp c V w
        (if opTag = 1 then Function.update s_dict u (some v.val)
         else Function.update s_dict u none) < 2 ^ w)
    (dflt : LatentRState (DualLatent c U V) rWhp)
    {t : LatentRState (DualLatent c U V) rWhp}
    (hc : DualRep c U V w base s_dict t.latent t.data ∧
      t.data.mem (base + hdrPhase) = 8) :
    let q := qPh8 s_dict o hv hfit_peak u v ho_mut dflt t
    let s_dict' := ((Dynamic.spec U V U).stepFn s_dict o).1
    let res_o := ((Dynamic.spec U V U).stepFn s_dict o).2
    let r := rep8 c U V w base s_dict dflt t
    let hrel := rep8_rel dflt hc.1 hc.2
    let hc8_step := coupled8_mutate_step hrel.1.2.2.2 hrel.2.2.1
      hop_nz u v hv_eq hsucc_fits'
      (lt_of_le_of_lt
        (Nat.add_le_add_left (dualPaddedWords_step_le_peak hrel.1.2.2.2 hop_nz u v).2 base)
        hsucc_fits')
    let s_src1 := hc8_step.choose
    let s_dst1 := hc8_step.choose_spec.choose
    let extra := hc8_step.choose_spec.choose_spec.choose
    let k_grow_r := (Memory.spec 0).clientResult (rMemState r.data)
      (prepGrowProg (((base, r.data.frontier), opTag), u.val))
    let sg_r : Memory.State :=
      { mem := ((Memory.spec 0).clientState (rMemState r.data)
          (prepGrowProg (((base, r.data.frontier), opTag), u.val))).mem
        frontier := r.data.frontier + k_grow_r }
    let st_r := (Memory.spec 0).clientState sg_r
      (stepOpProg (((base, sg_r.frontier), opTag), (u.val, v_val)))
    let k_sh_r := (Memory.spec 0).clientResult st_r
      (postRandShrinkProg ((base, st_r.frontier), opTag))
    let s_post_r : Memory.State :=
      { mem := clear ((Memory.spec 0).clientState st_r
          (postRandShrinkProg ((base, st_r.frontier), opTag))).mem
          (st_r.frontier - k_sh_r) k_sh_r
        frontier := st_r.frontier - k_sh_r }
    ExecRCodeSteps w opCodeWhp
      ((subroutineCodeWhp c U V w).prepare whpEncode o t.data)
      (PMF.pure ⟨q.data, q.steps, true⟩)
      (base + stepSuccinctPeakWordsWhp c V w s_dict o) ∧
    DualRep c U V w base s_dict' q.latent q.data ∧
    whpDecode (V := V) o q.data.regs = some res_o ∧
    (∀ addr < base, q.data.mem addr = t.data.mem addr) ∧
    q.latent.slotSrc =
      ⟨r.latent.slotSrc.nCap, s_src1, r.latent.slotSrc.seeds, r.latent.slotSrc.evs⟩ ∧
    q.latent.slotDst =
      ⟨t.latent.slotDst.nCap, s_dst1, t.latent.slotDst.seeds,
        (r.latent.slotDst.applyFG false opTag u v).evs ++ extra⟩ ∧
    (r.latent.slotSrc.GoodCovers → q.latent.slotDst.GoodCovers →
      q.steps ≤ worstCaseTimeWhp c) ∧
    ((s_post_r.mem (base + hdrPhase) = 8 ∧
        Coupled8 c V w base (Dictionary.dom s_dict').card s_post_r (rMemState q.data)) ∨
     (s_post_r.mem (base + hdrPhase) = 9 ∧
        SchedEq base s_post_r (rMemState q.data))) := by
  classical
  intro q s_dict' res_o r hrel hc8_step s_src1 s_dst1 extra k_grow_r sg_r st_r k_sh_r s_post_r
  have hs_dict'_eq :
      (if opTag = 1 then Function.update s_dict u (some v.val)
       else Function.update s_dict u none) = s_dict' := by
    rcases ho_mut with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ <;> rfl
  have hd_sp := (opCodeWhp_mutate_det_exec hc.1 o hv hfit_peak u v ho_mut
    (by rw [hc.2]; decide)).choose_spec.choose_spec
  obtain ⟨hex, hy_mem, hyb, hy_base, hy_mfr, hy_dec, hy_out, hT_imp⟩ := hd_sp
  have hinst := hc8_step.choose_spec.choose_spec.choose_spec
    hc.1.2.2.2 hrel.2.2.2.1 hrel.2.2.2.2.1 hrel.2.2.2.2.2.1 hrel.2.2.2.2.2.2
  obtain ⟨hsl_s, hsl_d, hinv_p, hmc_pg, hmc_prs, hmc_so⟩ := hinst.1.choose_spec
  have hinv_p' := stateInv_congr_dict hinv_p hs_dict'_eq
  obtain ⟨hkg_eq, _, _, hps_ne5, _⟩ :=
    schedEq_mutate_step (v_val := v_val) hrel.1.2.2.2 hc.1.2.2.2 hrel.2.2.2.1.1
      hop_nz u v hv_eq hsucc_fits'
      (lt_of_le_of_lt
        (Nat.add_le_add_left (dualPaddedWords_step_le_peak hrel.1.2.2.2 hop_nz u v).2 base)
        hsucc_fits')
  obtain ⟨hksh_eq, _⟩ := hps_ne5 (by dsimp only [rMemState]; rw [hrel.2.2.1]; decide)
  dsimp only at hkg_eq hksh_eq
  rw [← hkg_eq] at hksh_eq
  let sp_t := (Memory.spec 0).clientState (rMemState t.data)
    (prepGrowProg (((base, t.data.frontier), opTag), u.val))
  let sg_t : Memory.State := { mem := sp_t.mem, frontier := t.data.frontier + k_grow_r }
  let st_t := (Memory.spec 0).clientState sg_t
    (stepOpProg (((base, sg_t.frontier), opTag), (u.val, v_val)))
  let sps_t := (Memory.spec 0).clientState st_t
    (postRandShrinkProg ((base, st_t.frontier), opTag))
  let s_post_t : Memory.State :=
    { mem := clear sps_t.mem (st_t.frontier - k_sh_r) k_sh_r
      frontier := st_t.frontier - k_sh_r }
  have hy_mem' : rMemState
      (opCodeWhp_mutate_det_exec hc.1 o hv hfit_peak u v ho_mut
        (by rw [hc.2]; decide)).choose = s_post_t := by
    rw [hy_mem]; dsimp only [s_post_t, sps_t, st_t, sg_t, sp_t]
    rw [← hkg_eq, ← hksh_eq]
  have hq_eq : q =
      ⟨hinst.1.choose,
       (opCodeWhp_mutate_det_exec hc.1 o hv hfit_peak u v ho_mut
         (by rw [hc.2]; decide)).choose, res_o,
       (opCodeWhp_mutate_det_exec hc.1 o hv hfit_peak u v ho_mut
         (by rw [hc.2]; decide)).choose_spec.choose, true⟩ := by
    dsimp only [q, qPh8]; rw [dite_eq_left hc]
  rw [hq_eq]; dsimp only
  refine ⟨hex, ⟨hyb, hy_base, hy_mfr, stateInv_congr_st hinv_p' hy_mem'.symm⟩, hy_dec, hy_out,
    hsl_s, hsl_d, fun hgs hgd => ?_, ?_⟩
  · rw [hsl_d] at hgd
    have hmc_so' := hmc_so hgs hgd
    dsimp only at hmc_so' hmc_prs
    rw [hkg_eq] at hmc_so' hmc_prs
    dsimp only [rMemState] at hmc_prs hT_imp
    exact hT_imp hmc_pg hmc_so' (by clear *- hmc_prs; omega)
  · rw [hy_mem', hs_dict'_eq.symm]; exact hinst.2

private theorem qPh8_slot_of_rep8_eq {c U V w base opTag v_val : ℕ}
    (s_dict : Dictionary.State U) (o : Dynamic.Op U)
    (hv : (Dynamic.spec U V U).valid s_dict o)
    (hfit_peak : Fits w (base + stepSuccinctPeakWordsWhp c V w s_dict o))
    (u : Fin U) (v : Fin V)
    (ho_mut : (o = .insert u v.val ∧ opTag = 1 ∧ v_val = v.val) ∨
      (o = .delete u ∧ opTag = 2 ∧ v_val = 0))
    (hop_nz : opTag ≠ 0) (hv_eq : opTag = 1 → v_val = v.val)
    (hsucc_fits' :
      base + spaceBoundWhp c V w
        (if opTag = 1 then Function.update s_dict u (some v.val)
         else Function.update s_dict u none) < 2 ^ w)
    (dflt : LatentRState (DualLatent c U V) rWhp)
    {t₁ t₂ : LatentRState (DualLatent c U V) rWhp}
    (hc₁ : DualRep c U V w base s_dict t₁.latent t₁.data ∧ t₁.data.mem (base + hdrPhase) = 8)
    (hc₂ : DualRep c U V w base s_dict t₂.latent t₂.data ∧ t₂.data.mem (base + hdrPhase) = 8)
    (hreq : rep8 c U V w base s_dict dflt t₁ = rep8 c U V w base s_dict dflt t₂) :
    (qPh8 s_dict o hv hfit_peak u v ho_mut dflt t₁).latent.slotSrc =
      (qPh8 s_dict o hv hfit_peak u v ho_mut dflt t₂).latent.slotSrc ∧
    (qPh8 s_dict o hv hfit_peak u v ho_mut dflt t₁).latent.slotDst.s_abs =
      (qPh8 s_dict o hv hfit_peak u v ho_mut dflt t₂).latent.slotDst.s_abs ∧
    (qPh8 s_dict o hv hfit_peak u v ho_mut dflt t₁).latent.slotDst.evs =
      (qPh8 s_dict o hv hfit_peak u v ho_mut dflt t₂).latent.slotDst.evs := by
  have hs₁ := (qPh8_spec s_dict o hv hfit_peak u v ho_mut hop_nz hv_eq hsucc_fits' dflt hc₁).2.2.2.2
  have hs₂ := (qPh8_spec s_dict o hv hfit_peak u v ho_mut hop_nz hv_eq hsucc_fits' dflt hc₂).2.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · rw [hs₁.1, hs₂.1]
    generalize_proofs pf1 pf2; revert pf1 pf2; rw [hreq]; intros; rfl
  · rw [congrArg SlotLatent.s_abs hs₁.2.1, congrArg SlotLatent.s_abs hs₂.2.1]
    dsimp only; generalize_proofs pf1 pf2; revert pf1 pf2; rw [hreq]; intros; rfl
  · rw [congrArg SlotLatent.evs hs₁.2.1, congrArg SlotLatent.evs hs₂.2.1]
    dsimp only; generalize_proofs pf1 pf2; revert pf1 pf2; rw [hreq]; intros; rfl

private theorem dualDistInv_mutate_8 {c U V w base opTag v_val : ℕ}
    (s_dict : Dictionary.State U) (o : Dynamic.Op U)
    (hv : (Dynamic.spec U V U).valid s_dict o)
    (u : Fin U) (v : Fin V)
    (ho_mut : (o = .insert u v.val ∧ opTag = 1 ∧ v_val = v.val) ∨
      (o = .delete u ∧ opTag = 2 ∧ v_val = 0))
    (ν : PMF (LatentRState (DualLatent c U V) rWhp))
    (hfit_peak : Fits w (base + stepSuccinctPeakWordsWhp c V w s_dict o))
    {L_rep : DualLatent c U V} {s_rep : Memory.State}
    (hinv_rep : DualStateInv c U V w base s_dict L_rep s_rep)
    (hp8 : s_rep.mem (base + hdrPhase) = 8)
    (hregimes : Coupled8Law c U V w base s_dict s_rep
      (dualCapSrc base s_rep.mem) (s_rep.mem (base + hdrNDst)) ν) :
    MutateStepPost c U V w base s_dict o ν := by
  classical
  set s_dict' := ((Dynamic.spec U V U).stepFn s_dict o).1
  set res_o := ((Dynamic.spec U V U).stepFn s_dict o).2
  obtain ⟨hop_nz, hv_eq, hs_dict'_eq, hsucc_fits', _⟩ :=
    mutate_setup_bounds ho_mut hfit_peak hinv_rep
  have hUw : Fits w U := hinv_rep.U_lt
  set ph := s_rep.mem (base + hdrPhase)
  set capSrc := dualCapSrc base s_rep.mem
  set capDst := s_rep.mem (base + hdrNDst)
  have hsrc_safe := dualCapSrc_safe hinv_rep
  obtain ⟨α, μ_idx, evs_src, evs_dst, L_anc, s_anc, f8, hν, hf⟩ := hregimes
  have hdst_safe := dualNDst_safe hinv_rep (by change ph ≠ 0; clear *- hp8; omega)
  obtain ⟨a₀, ha₀⟩ := μ_idx.support_nonempty
  let ws_src0 := zeroSeedWords c w capSrc
  let wd0 := zeroSeedWords c w capDst
  let dflt := f8 a₀ ws_src0 wd0
  -- Helper: pad fits on any `DualStateInv` state at phase `8`
  have hpad_of_inv : ∀ {L_s : DualLatent c U V} {st : Memory.State},
      DualStateInv c U V w base s_dict L_s st →
      base + dualPaddedWords c U V w (st.mem (base + hdrNSrc))
        (if st.mem (base + hdrPhase) = 0 then st.mem (base + hdrNSrc)
         else st.mem (base + hdrNDst))
        (Dictionary.dom (if opTag = 1 then Function.update s_dict u (some v.val)
          else Function.update s_dict u none)).card < 2 ^ w := fun hst =>
    lt_of_le_of_lt
      (Nat.add_le_add_left (dualPaddedWords_step_le_peak hst hop_nz u v).2 base)
      hsucc_fits'
  -- Canonical Phase-`8` transition on `t` via `r := rep8 c U V w base s_dict dflt t`
  let q_ph8 := qPh8 s_dict o hv hfit_peak u v ho_mut dflt
  let μ_step := fun t => PMF.pure (q_ph8 t)
  have hsupp_8 : ∀ a ∈ μ_idx.support, ∀ ws_src wd,
      DualRep c U V w base s_dict (f8 a ws_src wd).latent (f8 a ws_src wd).data ∧
      (f8 a ws_src wd).data.mem (base + hdrPhase) = 8 := by
    intro a ha ws_src wd
    obtain ⟨_, ha_sch, _, _, _, _, hwd⟩ := hf a ha ws_src
    obtain ⟨hr, hc8, _⟩ := hwd wd
    exact ⟨hr, ((ha_sch.trans hc8.1).2 hdrPhase (by decide) (by decide)).symm.trans hp8⟩
  have hrel_fibre : ∀ a ∈ μ_idx.support, ∀ ws_src wd,
      Rel8 c U V w base s_dict (f8 a ws_src wd0) (f8 a ws_src wd) := by
    intro a ha ws_src wd
    obtain ⟨_, _, _, _, _, _, hwd⟩ := hf a ha ws_src
    obtain ⟨hr0, hc8_0, hsl0, _, habs0, hev0, _⟩ := hwd wd0
    obtain ⟨hrw, hc8_w, hslw, _, habsw, hevw, _⟩ := hwd wd
    exact ⟨hr0, hrw, (hsupp_8 a ha ws_src wd0).2,
      coupled8_trans (coupled8_symm hc8_0) hc8_w,
      hslw.trans hsl0.symm, habsw.trans habs0.symm, hevw.trans hev0.symm⟩
  let hq8_spec := fun {t} hc =>
    qPh8_spec s_dict o hv hfit_peak u v ho_mut hop_nz hv_eq hsucc_fits' dflt (t := t) hc
  let hslot_of_rep8_eq := fun {t₁ t₂} hc₁ hc₂ hreq =>
    qPh8_slot_of_rep8_eq s_dict o hv hfit_peak u v ho_mut hop_nz hv_eq hsucc_fits' dflt
      (t₁ := t₁) (t₂ := t₂) hc₁ hc₂ hreq
  have hstep_all : ∀ t ∈ ν.support,
      ExecRCodeSteps w opCodeWhp ((subroutineCodeWhp c U V w).prepare whpEncode o t.data)
        ((μ_step t).map WhpStepROutcome.toCodeOutcome)
        (base + stepSuccinctPeakWordsWhp c V w s_dict o) ∧
      ∀ q ∈ (μ_step t).support,
        q.result = res_o ∧ whpDecode (V := V) o q.data.regs = some q.result ∧
        DualRep c U V w base s_dict' q.latent q.data ∧
        (∀ addr < base, q.data.mem addr = t.data.mem addr) := by
    intro t ht
    rw [hν, PMF.mem_support_bind_iff] at ht; obtain ⟨a, ha, hm1⟩ := ht
    rw [PMF.mem_support_bind_iff] at hm1; obtain ⟨ws_src, _, hm2⟩ := hm1
    rw [PMF.mem_support_map_iff] at hm2; obtain ⟨wd, _, rfl⟩ := hm2
    have hc := hsupp_8 a ha ws_src wd
    obtain ⟨hex, hr', hdec, hout, _⟩ := hq8_spec hc
    have htimed : (q_ph8 (f8 a ws_src wd)).timed = true := by
      dsimp only [q_ph8, qPh8]; rw [dite_eq_left hc]
    refine ⟨?_, fun q hq => ?_⟩
    · dsimp only [μ_step]; rw [PMF.pure_map]
      dsimp only [WhpStepROutcome.toCodeOutcome]; rw [htimed]; exact hex
    rw [PMF.mem_support_pure_iff] at hq; subst hq
    have hres : (q_ph8 (f8 a ws_src wd)).result = res_o := by
      dsimp only [q_ph8, qPh8]; rw [dite_eq_left hc]
    exact ⟨hres, hres ▸ hdec, hr', hout⟩
  let f_step : α → SeedWords c w capSrc → SeedWords c w capDst →
      LatentRState (DualLatent c U V) rWhp :=
    fun a ws_src wd => ⟨(q_ph8 (f8 a ws_src wd)).latent, (q_ph8 (f8 a ws_src wd)).data⟩
  have hν'_bind : (ν.bind fun t => (μ_step t).map fun q => ⟨q.latent, q.data⟩) =
      μ_idx.bind (fun a =>
        (PMF.uniformOfFintype (SeedWords c w capSrc)).bind (fun ws_src =>
          (PMF.uniformOfFintype (SeedWords c w capDst)).map (f_step a ws_src))) := by
    rw [hν, PMF.bind_bind]
    refine congrArg (μ_idx.bind ·) (funext fun a => ?_)
    rw [PMF.bind_bind]
    refine congrArg ((PMF.uniformOfFintype _).bind ·) (funext fun ws_src => ?_)
    rw [PMF.bind_map]; dsimp only [μ_step]
    conv_rhs => unfold PMF.map
    refine congrArg ((PMF.uniformOfFintype _).bind ·) (funext fun wd => ?_)
    dsimp only [Function.comp_def]; rw [PMF.pure_map]
  -- Reference post-state `t_rep' := f_step a₀ ws_src0 wd0`
  let L_rep' := (f_step a₀ ws_src0 wd0).latent
  let s_rep' := rMemState (f_step a₀ ws_src0 wd0).data
  have hc_0 := hsupp_8 a₀ ha₀ ws_src0 wd0
  have hsp_0 := hq8_spec hc_0
  have hinv_rep' : DualStateInv c U V w base s_dict' L_rep' s_rep' := hsp_0.2.1.2.2.2
  have hsch_post_all : ∀ a ∈ μ_idx.support, ∀ ws_src wd,
      SchedEq base s_rep' (rMemState (f_step a ws_src wd).data) := by
    intro a ha ws_src wd
    have hc_w := hsupp_8 a ha ws_src wd
    have hsch_pre : SchedEq base (rMemState dflt.data)
        (rMemState (f8 a ws_src wd).data) :=
      ((hf a₀ ha₀ ws_src0).2.1.trans ((hf a₀ ha₀ ws_src0).2.2.2.2.2.2 wd0).2.1.1).symm.trans
        ((hf a ha ws_src).2.1.trans ((hf a ha ws_src).2.2.2.2.2.2 wd).2.1.1)
    obtain ⟨_, _, _, hps_ne5, _⟩ :=
      schedEq_mutate_step (v_val := v_val) hc_0.1.2.2.2 hc_w.1.2.2.2 hsch_pre
        hop_nz u v hv_eq hsucc_fits' (hpad_of_inv hc_0.1.2.2.2)
    obtain ⟨_, hsch_p⟩ := hps_ne5 (by dsimp only [rMemState]; rw [hc_0.2]; decide)
    have hd0 := (opCodeWhp_mutate_det_exec hc_0.1 o hv hfit_peak u v ho_mut
      (by rw [hc_0.2]; decide)).choose_spec.choose_spec.2.1
    have hdw := (opCodeWhp_mutate_det_exec hc_w.1 o hv hfit_peak u v ho_mut
      (by rw [hc_w.2]; decide)).choose_spec.choose_spec.2.1
    have hd0_eq : (f_step a₀ ws_src0 wd0).data =
        (opCodeWhp_mutate_det_exec hc_0.1 o hv hfit_peak u v ho_mut
          (by rw [hc_0.2]; decide)).choose := by
      dsimp only [f_step, q_ph8, qPh8, dflt]; rw [dite_eq_left hc_0]
    have hdw_eq : (f_step a ws_src wd).data =
        (opCodeWhp_mutate_det_exec hc_w.1 o hv hfit_peak u v ho_mut
          (by rw [hc_w.2]; decide)).choose := by
      dsimp only [f_step, q_ph8, qPh8]; rw [dite_eq_left hc_w]
    have hm0 : s_rep' = rMemState (opCodeWhp_mutate_det_exec hc_0.1 o hv hfit_peak u v ho_mut
        (by rw [hc_0.2]; decide)).choose := by
      dsimp only [s_rep']; rw [hd0_eq]
    rw [hm0, hd0, hdw_eq, hdw]; exact hsch_p
  have hp_rep'_89 : s_rep'.mem (base + hdrPhase) = 8 ∨
      s_rep'.mem (base + hdrPhase) = 9 := by
    rcases hsp_0.2.2.2.2.2.2.2 with ⟨hp8_r, hc8⟩ | ⟨hp9_r, hsch⟩
    · exact Or.inl ((hc8.1.2 hdrPhase (by decide) (by decide)).symm.trans hp8_r)
    · exact Or.inr ((hsch.2 hdrPhase (by decide) (by decide)).symm.trans hp9_r)
  have hl_rep'_src : L_rep'.slotSrc.nCap = capSrc := by
    have hrel0 := rep8_rel dflt hc_0.1 hc_0.2
    have hr0_src : (rep8 c U V w base s_dict dflt dflt).latent.slotSrc =
        (L_anc a₀ ws_src0).slotSrc :=
      hrel0.2.2.2.2.1.symm.trans ((hf a₀ ha₀ ws_src0).2.2.2.2.2.2 wd0).2.2.1
    change (q_ph8 dflt).latent.slotSrc.nCap = capSrc
    rw [hsp_0.2.2.2.2.1]; dsimp only
    rw [hr0_src]; exact (hf a₀ ha₀ ws_src0).2.2.1
  have hl_rep'_dst : L_rep'.slotDst.nCap = capDst := by
    change (q_ph8 dflt).latent.slotDst.nCap = capDst
    rw [hsp_0.2.2.2.2.2.1]; dsimp only
    exact ((hf a₀ ha₀ ws_src0).2.2.2.2.2.2 wd0).2.2.2.1
  refine ⟨μ_step, hstep_all, ⟨L_rep', s_rep', hinv_rep', ?_⟩, ?_⟩
  · dsimp only
    rcases hp_rep'_89 with hp8' | hp9'
    · -- `8 → 8`: stays in `Coupled8`
      have hcapSrc'_eq : dualCapSrc base s_rep'.mem = capSrc :=
        (hinv_rep'.sl_8 hp8').1.symm.trans hl_rep'_src
      have hnd_rep' : s_rep'.mem (base + hdrNDst) = capDst :=
        (hinv_rep'.sl_8 hp8').2.1.symm.trans hl_rep'_dst
      rw [ite_eq_right (by clear *- hp8'; omega), ite_eq_right (by clear *- hp8'; omega),
        ite_eq_right (by clear *- hp8'; omega), ite_eq_left hp8', hcapSrc'_eq, hnd_rep']
      refine ⟨α, μ_idx, evs_src,
        fun a ws_src => (f_step a ws_src wd0).latent.slotDst.evs,
        fun a ws_src => (f_step a ws_src wd0).latent,
        fun a ws_src => rMemState (f_step a ws_src wd0).data,
        f_step, hν'_bind, fun a ha ws_src => ?_⟩
      have hc_a0 := hsupp_8 a ha ws_src wd0
      have hsp_a0 := hq8_spec hc_a0
      have hrel_a0 := rep8_rel dflt hc_a0.1 hc_a0.2
      have hr_src_a0 : (rep8 c U V w base s_dict dflt (f8 a ws_src wd0)).latent.slotSrc =
          (L_anc a ws_src).slotSrc :=
        hrel_a0.2.2.2.2.1.symm.trans ((hf a ha ws_src).2.2.2.2.2.2 wd0).2.2.1
      refine ⟨hsp_a0.2.1.2.2.2, hsch_post_all a ha ws_src wd0,
        by change (q_ph8 (f8 a ws_src wd0)).latent.slotSrc.nCap = capSrc
           rw [hsp_a0.2.2.2.2.1]; dsimp only; rw [hr_src_a0]; exact (hf a ha ws_src).2.2.1,
        by change (q_ph8 (f8 a ws_src wd0)).latent.slotSrc.evs = evs_src a
           rw [hsp_a0.2.2.2.2.1]; dsimp only; rw [hr_src_a0]; exact (hf a ha ws_src).2.2.2.1,
        fun hc => by
           change HEq (q_ph8 (f8 a ws_src wd0)).latent.slotSrc.seeds _
           rw [hsp_a0.2.2.2.2.1]; dsimp only; rw [hr_src_a0]
           exact (hf a ha ws_src).2.2.2.2.1 hc,
        rfl, fun wd => ?_⟩
      have hc_w := hsupp_8 a ha ws_src wd
      have hsp_w := hq8_spec hc_w
      have hrep8_eq : rep8 c U V w base s_dict dflt (f8 a ws_src wd) =
          rep8 c U V w base s_dict dflt (f8 a ws_src wd0) :=
        rep8_eq_of_rel dflt (hrel_fibre a ha ws_src wd).symm
      -- `Coupled8` between `f_step a ws_src wd0` and `f_step a ws_src wd` via shared `rep8`
      have hc8_a0 := (hsp_a0.2.2.2.2.2.2.2.resolve_right fun ⟨hp9_r, hsch⟩ => by
        have hp_eq := (hsch_post_all a ha ws_src wd0).2 hdrPhase (by decide) (by decide)
        have hp_r := (hsch.2 hdrPhase (by decide) (by decide)).symm.trans hp9_r
        have h9 : s_rep'.mem (base + hdrPhase) = 9 := hp_eq.trans hp_r
        rw [hp8'] at h9; cases h9).2
      have hc8_w_raw := (hsp_w.2.2.2.2.2.2.2.resolve_right fun ⟨hp9_r, hsch⟩ => by
        have hp_eq := (hsch_post_all a ha ws_src wd).2 hdrPhase (by decide) (by decide)
        have hp_r := (hsch.2 hdrPhase (by decide) (by decide)).symm.trans hp9_r
        have h9 : s_rep'.mem (base + hdrPhase) = 9 := hp_eq.trans hp_r
        rw [hp8'] at h9; cases h9).2
      have hc8_pair : Coupled8 c V w base (Dictionary.dom s_dict').card
          (rMemState (f_step a ws_src wd0).data)
          (rMemState (f_step a ws_src wd).data) := by
        refine coupled8_trans (coupled8_symm hc8_a0) ?_
        simpa only [hrep8_eq] using hc8_w_raw
      obtain ⟨hsl_s_eq, habs_d_eq, hev_d_eq⟩ := hslot_of_rep8_eq hc_w hc_a0 hrep8_eq
      have hd_w := hsp_w.2.2.2.2.2.1
      refine ⟨hsp_w.2.1, hc8_pair, hsl_s_eq,
        by change (q_ph8 (f8 a ws_src wd)).latent.slotDst.nCap = capDst
           rw [hd_w]; exact ((hf a ha ws_src).2.2.2.2.2.2 wd).2.2.2.1,
        habs_d_eq, hev_d_eq, fun hcd_pos => ?_⟩
      change HEq (q_ph8 (f8 a ws_src wd)).latent.slotDst.seeds _
      rw [hd_w]; exact ((hf a ha ws_src).2.2.2.2.2.2 wd).2.2.2.2.2.2 hcd_pos
    · -- `8 → 9`: enters `SingleEpochLaw` on `slotDst` (`α' := α × SeedWords c w capSrc`)
      have hnd_rep' : s_rep'.mem (base + hdrNDst) = capDst :=
        (hinv_rep'.sl_ge9 (by clear *- hp9'; omega)).1.symm.trans hl_rep'_dst
      rw [ite_eq_right (by clear *- hp9'; omega), ite_eq_right (by clear *- hp9'; omega),
        ite_eq_right (by clear *- hp9'; omega), ite_eq_right (by clear *- hp9'; omega),
        hnd_rep']
      let α' := α × SeedWords c w capSrc
      let μ_idx' : PMF α' :=
        μ_idx.bind fun a => (PMF.uniformOfFintype (SeedWords c w capSrc)).map (a, ·)
      refine ⟨α', μ_idx',
        fun p => (f_step p.1 p.2 wd0).latent.slotDst.evs,
        fun p wd => f_step p.1 p.2 wd, ?_, fun ⟨a, ws_src⟩ hp_mem wd => ?_⟩
      · rw [hν'_bind]; dsimp only [μ_idx']
        rw [PMF.bind_bind]
        refine congrArg (μ_idx.bind ·) (funext fun a => ?_)
        rw [PMF.bind_map]; rfl
      · dsimp only [μ_idx'] at hp_mem
        rw [PMF.mem_support_bind_iff] at hp_mem
        obtain ⟨a', ha', hm'⟩ := hp_mem
        rw [PMF.mem_support_map_iff] at hm'
        obtain ⟨ws', _, heq_p⟩ := hm'
        cases heq_p
        have hc_w := hsupp_8 a ha' ws_src wd
        have hc_a0 := hsupp_8 a ha' ws_src wd0
        have hsp_w := hq8_spec hc_w
        have hrep8_eq : rep8 c U V w base s_dict dflt (f8 a ws_src wd) =
            rep8 c U V w base s_dict dflt (f8 a ws_src wd0) :=
          rep8_eq_of_rel dflt (hrel_fibre a ha' ws_src wd).symm
        have hd_w := hsp_w.2.2.2.2.2.1
        have hev_d_eq := (hslot_of_rep8_eq hc_w hc_a0 hrep8_eq).2.2
        refine ⟨hsp_w.2.1, hsch_post_all a ha' ws_src wd, ?_, ?_, fun hcd_pos => ?_⟩
        · simp only [↓reduceIte]
          change (q_ph8 (f8 a ws_src wd)).latent.slotDst.nCap = capDst
          rw [hd_w]; exact ((hf a ha' ws_src).2.2.2.2.2.2 wd).2.2.2.1
        · simp only [↓reduceIte]; exact hev_d_eq
        · change HEq (q_ph8 (f8 a ws_src wd)).latent.slotDst.seeds _
          rw [hd_w]; exact ((hf a ha' ws_src).2.2.2.2.2.2 wd).2.2.2.2.2.2 hcd_pos
  · -- Slow-path union bound in Phase `8` (`BadS ∪ BadD`)
    rw [hν, PMF.bind_bind]
    refine toOuterMeasure_bind_le_const μ_idx _ _ _ fun a ha => ?_
    let μ_src := PMF.uniformOfFintype (SeedWords c w capSrc)
    let μ_dst := PMF.uniformOfFintype (SeedWords c w capDst)
    let μ_prod : PMF (SeedWords c w capSrc × SeedWords c w capDst) :=
      μ_src.bind fun ws => μ_dst.map (ws, ·)
    have hbind_eq :
        ((μ_src.bind fun ws => μ_dst.map (f8 a ws)).bind μ_step) =
          μ_prod.map (fun p => q_ph8 (f8 a p.1 p.2)) := by
      dsimp only [μ_prod, μ_step]
      rw [PMF.bind_bind, PMF.map_bind]
      refine congrArg (μ_src.bind ·) (funext fun ws => ?_)
      rw [PMF.bind_map, PMF.map_comp]
      unfold PMF.map; rfl
    rw [hbind_eq, PMF.toOuterMeasure_map_apply]
    let BadS : Set (SeedWords c w capSrc × SeedWords c w capDst) :=
      {p | ¬(L_anc a p.1).slotSrc.GoodCovers}
    let BadD : Set (SeedWords c w capSrc × SeedWords c w capDst) :=
      {p | ¬(f_step a p.1 p.2).latent.slotDst.GoodCovers}
    have hsub : (fun p : SeedWords c w capSrc × SeedWords c w capDst =>
        q_ph8 (f8 a p.1 p.2)) ⁻¹' {q | ¬q.WithinBudget (worstCaseTimeWhp c)} ⊆
        BadS ∪ BadD := by
      intro ⟨ws, wd⟩ hbad
      by_cases hgs : (L_anc a ws).slotSrc.GoodCovers
      · refine Or.inr fun hgd => hbad ?_
        have hc_w := hsupp_8 a ha ws wd
        have hsp_w := hq8_spec hc_w
        have hrel_w := rep8_rel dflt hc_w.1 hc_w.2
        have hr_src_w : (rep8 c U V w base s_dict dflt (f8 a ws wd)).latent.slotSrc =
            (L_anc a ws).slotSrc :=
          hrel_w.2.2.2.2.1.symm.trans ((hf a ha ws).2.2.2.2.2.2 wd).2.2.1
        have htimed : (q_ph8 (f8 a ws wd)).timed = true := by
          dsimp only [q_ph8, qPh8]; rw [dite_eq_left hc_w]
        exact ⟨htimed, hsp_w.2.2.2.2.2.2.1 (hr_src_w.symm ▸ hgs) hgd⟩
      · exact Or.inl hgs
    have hm_s : μ_prod.toOuterMeasure BadS ≤
        if U < whpThreshold c then 0
        else ((1 : ℝ≥0∞) / 2) *
          (((max (Dictionary.dom s_dict).card (whpThreshold c) : ℕ) : ℝ≥0∞)⁻¹ ^ c) := by
      have hfst : μ_prod.map Prod.fst = μ_src := by
        dsimp only [μ_prod]; rw [PMF.map_bind]
        conv_rhs => rw [← PMF.bind_pure μ_src]
        refine congrArg (μ_src.bind ·) (funext fun ws => ?_)
        rw [PMF.map_comp]; exact PMF.map_const μ_dst ws
      have heq_s : μ_prod.toOuterMeasure BadS =
          μ_src.toOuterMeasure {ws | ¬(L_anc a ws).slotSrc.GoodCovers} := by
        rw [← hfst, PMF.toOuterMeasure_map_apply]; rfl
      rw [heq_s]
      refine uniform_seedWords_bad_le hUw hsrc_safe (evs_src a)
        (fun ws => (L_anc a ws).slotSrc)
        (fun ws => (hf a ha ws).2.2.1) (fun ws => (hf a ha ws).2.2.2.1)
        (fun hc ws => (hf a ha ws).2.2.2.2.1 hc) fun hc => ?_
      obtain ⟨ha_inv₀, ha_sch₀, ha_nc₀, ha_ev₀, _, _, _⟩ := hf a ha ws_src0
      have hb₀ := (dualCoreInv_slot_evs_bounds ha_inv₀).1
        (by have h := (ha_sch₀.2 hdrPhase (by decide) (by decide)).symm
            change (s_anc a ws_src0).mem (base + hdrPhase) = ph at h
            clear *- h hp8; omega)
        (ha_nc₀ ▸ hc)
      rwa [ha_nc₀, ha_ev₀] at hb₀
    have hm_d : μ_prod.toOuterMeasure BadD ≤
        if U < whpThreshold c then 0
        else ((1 : ℝ≥0∞) / 2) *
          (((max (Dictionary.dom s_dict).card (whpThreshold c) : ℕ) : ℝ≥0∞)⁻¹ ^ c) := by
      refine toOuterMeasure_bind_le_const μ_src _ BadD _ fun ws _ => ?_
      rw [PMF.toOuterMeasure_map_apply]
      have hc_a0 := hsupp_8 a ha ws wd0
      have hsp_a0 := hq8_spec hc_a0
      refine uniform_seedWords_bad_le hUw hdst_safe
        (f_step a ws wd0).latent.slotDst.evs
        (fun wd => (f_step a ws wd).latent.slotDst)
        (fun wd => by
          have hsp_w := hq8_spec (hsupp_8 a ha ws wd)
          change (q_ph8 (f8 a ws wd)).latent.slotDst.nCap = capDst
          rw [hsp_w.2.2.2.2.2.1]; exact ((hf a ha ws).2.2.2.2.2.2 wd).2.2.2.1)
        (fun wd => (hslot_of_rep8_eq (hsupp_8 a ha ws wd) hc_a0
          (rep8_eq_of_rel dflt (hrel_fibre a ha ws wd).symm)).2.2)
        (fun hc wd => by
          have hsp_w := hq8_spec (hsupp_8 a ha ws wd)
          change HEq (q_ph8 (f8 a ws wd)).latent.slotDst.seeds _
          rw [hsp_w.2.2.2.2.2.1]
          exact ((hf a ha ws).2.2.2.2.2.2 wd).2.2.2.2.2.2 hc)
        fun hc => ?_
      have hge8_a0 : 8 ≤ (rMemState (f_step a ws wd0).data).mem (base + hdrPhase) := by
        rw [← (hsch_post_all a ha ws wd0).2 hdrPhase (by decide) (by decide)]
        clear *- hp_rep'_89; omega
      have hnc_a0 : (f_step a ws wd0).latent.slotDst.nCap = capDst := by
        change (q_ph8 (f8 a ws wd0)).latent.slotDst.nCap = capDst
        rw [hsp_a0.2.2.2.2.2.1]; exact ((hf a ha ws).2.2.2.2.2.2 wd0).2.2.2.1
      have hb₀ := (dualCoreInv_slot_evs_bounds hsp_a0.2.1.2.2.2).2 hge8_a0 (hnc_a0 ▸ hc)
      rwa [hnc_a0] at hb₀
    calc μ_prod.toOuterMeasure _
        ≤ μ_prod.toOuterMeasure (BadS ∪ BadD) := μ_prod.toOuterMeasure.mono hsub
      _ ≤ μ_prod.toOuterMeasure BadS + μ_prod.toOuterMeasure BadD :=
          MeasureTheory.measure_union_le BadS BadD
      _ ≤ _ := add_le_add hm_s hm_d
      _ = stepFailureProbWhp c s_dict o := two_half_stepFailureProb_eq c s_dict o

private theorem dualDistInv_mutate_ge9 {c U V w base opTag v_val : ℕ}
    (s_dict : Dictionary.State U) (o : Dynamic.Op U)
    (hv : (Dynamic.spec U V U).valid s_dict o)
    (u : Fin U) (v : Fin V)
    (ho_mut : (o = .insert u v.val ∧ opTag = 1 ∧ v_val = v.val) ∨
      (o = .delete u ∧ opTag = 2 ∧ v_val = 0))
    (ν : PMF (LatentRState (DualLatent c U V) rWhp))
    (hfit_peak : Fits w (base + stepSuccinctPeakWordsWhp c V w s_dict o))
    {L_rep : DualLatent c U V} {s_rep : Memory.State}
    (hinv_rep : DualStateInv c U V w base s_dict L_rep s_rep)
    (hp9 : 9 ≤ s_rep.mem (base + hdrPhase))
    (hregimes : SingleEpochLaw c U V w base s_dict s_rep (s_rep.mem (base + hdrNDst)) true ν) :
    MutateStepPost c U V w base s_dict o ν := by
  classical
  set s_dict' := ((Dynamic.spec U V U).stepFn s_dict o).1
  set res_o := ((Dynamic.spec U V U).stepFn s_dict o).2
  obtain ⟨hop_nz, hv_eq, hs_dict'_eq, hsucc_fits', hpad_rep_fits'⟩ :=
    mutate_setup_bounds ho_mut hfit_peak hinv_rep
  let fgEv : EpochUpdate U V := if opTag = 1 then .insert u v else .delete u
  have hUw : Fits w U := hinv_rep.U_lt
  set ph := s_rep.mem (base + hdrPhase)
  set capDst := s_rep.mem (base + hdrNDst)
  have hdst_safe := dualNDst_safe hinv_rep (by change ph ≠ 0; clear *- hp9; omega)
  obtain ⟨α, μ_idx, evs_of, f_act, hν, hf⟩ := hregimes
  obtain ⟨a₀, ha₀⟩ := μ_idx.support_nonempty
  let wd0 := zeroSeedWords c w capDst
  let t₀ := f_act a₀ wd0
  obtain ⟨hr₀, hsch₀, _, _, _⟩ := hf a₀ ha₀ wd0
  let stepNon58 : ∀ {t : LatentRState (DualLatent c U V) rWhp}
      (hr : DualRep c U V w base s_dict t.latent t.data)
      (hne5 : t.data.mem (base + hdrPhase) ≠ 5)
      (hne8 : t.data.mem (base + hdrPhase) ≠ 8), _ := fun hr hne5 hne8 =>
    opCodeWhp_mutate_non58_exec hr o hv hfit_peak u v ho_mut hne5 hne8
  let q_det := qDetNon58 s_dict o hv hfit_peak u v ho_mut
  let μ_step := fun t => PMF.pure (q_det t)
  have hsupp_ge9 : ∀ a ∈ μ_idx.support, ∀ wd : SeedWords c w capDst,
      DualRep c U V w base s_dict (f_act a wd).latent (f_act a wd).data ∧
      (f_act a wd).data.mem (base + hdrPhase) ≠ 5 ∧
      (f_act a wd).data.mem (base + hdrPhase) ≠ 8 ∧
      9 ≤ (f_act a wd).data.mem (base + hdrPhase) := by
    intro a ha wd
    obtain ⟨hr, hsch, _, _, _⟩ := hf a ha wd
    have hp_t : (f_act a wd).data.mem (base + hdrPhase) = ph :=
      (hsch.2 hdrPhase (by decide) (by decide)).symm
    exact ⟨hr, by clear *- hp_t hp9; omega, by clear *- hp_t hp9; omega, hp_t ▸ hp9⟩
  have hstep_all : ∀ t ∈ ν.support,
      ExecRCodeSteps w opCodeWhp ((subroutineCodeWhp c U V w).prepare whpEncode o t.data)
        ((μ_step t).map WhpStepROutcome.toCodeOutcome)
        (base + stepSuccinctPeakWordsWhp c V w s_dict o) ∧
      ∀ q ∈ (μ_step t).support,
        q.result = res_o ∧ whpDecode (V := V) o q.data.regs = some q.result ∧
        DualRep c U V w base s_dict' q.latent q.data ∧
        (∀ addr < base, q.data.mem addr = t.data.mem addr) := by
    intro t ht
    rw [hν, PMF.mem_support_bind_iff] at ht; obtain ⟨a, ha, hmt⟩ := ht
    rw [PMF.mem_support_map_iff] at hmt; obtain ⟨wd, _, rfl⟩ := hmt
    obtain ⟨hr, hne5, hne8, _⟩ := hsupp_ge9 a ha wd
    have hc_t : DualRep c U V w base s_dict _ _ ∧ _ ∧ _ := ⟨hr, hne5, hne8⟩
    have hsp := (stepNon58 hr hne5 hne8).choose_spec.choose_spec.choose_spec.choose_spec
    dsimp only [μ_step, q_det, qDetNon58]; rw [dite_eq_left hc_t, PMF.pure_map]
    refine ⟨hsp.1, fun q hq => ?_⟩
    rw [PMF.mem_support_pure_iff] at hq; subst hq
    exact ⟨rfl, hsp.2.2.2.2.2.2.2.2.2.1, hsp.2.2.1, hsp.2.2.2.2.2.2.2.2.2.2.1⟩
  -- Extract post-step classification across `(a, wd)`
  let f_next : α → SeedWords c w capDst → LatentRState (DualLatent c U V) rWhp :=
    fun a wd => ⟨(q_det (f_act a wd)).latent, (q_det (f_act a wd)).data⟩
  let L_rep' := (q_det t₀).latent
  let s_rep' := rMemState (q_det t₀).data
  have hf_post9 : ∀ a ∈ μ_idx.support, ∀ wd : SeedWords c w capDst,
      let t := f_act a wd
      let q := q_det t
      DualRep c U V w base s_dict' q.latent q.data ∧
      SchedEq base s_rep' (rMemState q.data) ∧
      (s_rep'.mem (base + hdrPhase) = 4 →
        q.latent.slotSrc.nCap = capDst ∧
        q.latent.slotSrc.evs = evs_of a ++ [fgEv] ∧
        (0 < capDst → HEq q.latent.slotSrc.seeds (seedsOfWords c U w capDst wd))) ∧
      (s_rep'.mem (base + hdrPhase) = 0 →
        0 < q.latent.slotSrc.nCap →
        q.latent.slotSrc.nCap = capDst ∧
        q.latent.slotSrc.evs = evs_of a ++ [fgEv] ∧
        (0 < capDst → HEq q.latent.slotSrc.seeds (seedsOfWords c U w capDst wd))) ∧
      (9 ≤ s_rep'.mem (base + hdrPhase) →
        (rMemState q.data).mem (base + hdrNDst) = capDst ∧
        (0 < q.latent.slotDst.nCap →
          q.latent.slotDst.nCap = capDst ∧
          q.latent.slotDst.evs = evs_of a ++ [fgEv] ∧
          (0 < capDst → HEq q.latent.slotDst.seeds (seedsOfWords c U w capDst wd)))) ∧
      ((t.latent.applyFG (t.data.mem (base + hdrPhase)) opTag u v).slotDst.GoodCovers →
        q.steps ≤ worstCaseTimeWhp c) ∧
      DualMidInv c U V w base s_dict'
        (t.latent.applyFG (t.data.mem (base + hdrPhase)) opTag u v)
        ((Memory.spec 0).clientState
          { mem := ((Memory.spec 0).clientState (rMemState t.data)
              (prepGrowProg (((base, t.data.frontier), opTag), u.val))).mem
            frontier := t.data.frontier +
              (Memory.spec 0).clientResult (rMemState t.data)
                (prepGrowProg (((base, t.data.frontier), opTag), u.val)) }
          (userMutateProg ((base, opTag), (u.val, v_val)))) ∧
      (s_rep'.mem (base + hdrPhase) = 4 ∨
        s_rep'.mem (base + hdrPhase) = 0 ∨
        9 ≤ s_rep'.mem (base + hdrPhase)) := by
    intro a ha wd
    obtain ⟨hr, hsch, hnc, hev, hsd⟩ := hf a ha wd
    simp only [↓reduceIte] at hnc hev hsd
    obtain ⟨_, hne5_t, hne8_t, hp9_t⟩ := hsupp_ge9 a ha wd
    obtain ⟨_, hne5_0, hne8_0, _⟩ := hsupp_ge9 a₀ ha₀ wd0
    have hc_t : DualRep c U V w base s_dict _ _ ∧ _ ∧ _ := ⟨hr, hne5_t, hne8_t⟩
    have hc_0 : DualRep c U V w base s_dict _ _ ∧ _ ∧ _ := ⟨hr₀, hne5_0, hne8_0⟩
    have hsp := (stepNon58 hr hne5_t hne8_t).choose_spec.choose_spec.choose_spec.choose_spec
    have hsp₀ :=
      (stepNon58 hr₀ hne5_0 hne8_0).choose_spec.choose_spec.choose_spec.choose_spec
    obtain ⟨hy_mem, hr_post, hmid, hsm_ph, htick_eq, hpre_sh, hpres1, hpres2, _, _, hT⟩ :=
      hsp.2
    have hsm_ge9 := hp9_t
    dsimp only [rMemState] at hsm_ph
    rw [← hsm_ph] at hsm_ge9
    have hpre_sh' := preShrink_congr_st hpre_sh htick_eq
    have hcls := bgTick_post_from_ge9 hop_nz hmid hsm_ge9 hpre_sh'
      (stateInv_congr_st hr_post.2.2.2 (by rw [hy_mem]; dsimp only; rw [htick_eq]))
    have hpad₀ :
        base + dualPaddedWords c U V w ((rMemState t₀.data).mem (base + hdrNSrc))
          (if (rMemState t₀.data).mem (base + hdrPhase) = 0 then
            (rMemState t₀.data).mem (base + hdrNSrc)
           else (rMemState t₀.data).mem (base + hdrNDst))
          (Dictionary.dom (if opTag = 1 then Function.update s_dict u (some v.val)
            else Function.update s_dict u none)).card < 2 ^ w := by
      rwa [← hsch₀.2 hdrNSrc (by decide) (by decide),
        ← hsch₀.2 hdrPhase (by decide) (by decide),
        ← hsch₀.2 hdrNDst (by decide) (by decide)]
    obtain ⟨_, _, _, hps_ne5, _⟩ :=
      schedEq_mutate_step (v_val := v_val) hr₀.2.2.2 hr.2.2.2 (hsch₀.symm.trans hsch)
        hop_nz u v hv_eq hsucc_fits' hpad₀
    obtain ⟨_, hsch_post⟩ := hps_ne5 hne5_0
    have hq_eq : q_det (f_act a wd) =
        ⟨(stepNon58 hr hne5_t hne8_t).choose_spec.choose_spec.choose_spec.choose,
         (stepNon58 hr hne5_t hne8_t).choose, res_o,
         (stepNon58 hr hne5_t hne8_t).choose_spec.choose, true⟩ := by
      dsimp only [q_det, qDetNon58]; rw [dite_eq_left hc_t]
    have hq0_data : (q_det t₀).data = (stepNon58 hr₀ hne5_0 hne8_0).choose := by
      dsimp only [q_det, qDetNon58, t₀]; rw [dite_eq_left hc_0]
    have hq0_m : s_rep' = rMemState (stepNon58 hr₀ hne5_0 hne8_0).choose := by
      dsimp only [s_rep']; rw [hq0_data]
    have hsch_q : SchedEq base s_rep' (rMemState (q_det (f_act a wd)).data) := by
      rw [hq0_m, hsp₀.2.1, hq_eq]; dsimp only; rw [hy_mem]; exact hsch_post
    have hp_q_eq : (rMemState (q_det (f_act a wd)).data).mem (base + hdrPhase) =
        s_rep'.mem (base + hdrPhase) :=
      (hsch_q.2 hdrPhase (by decide) (by decide)).symm
    have hfg_dst : ((f_act a wd).latent.applyFG
        ((f_act a wd).data.mem (base + hdrPhase)) opTag u v).slotDst =
        (f_act a wd).latent.slotDst.applyFG false opTag u v := by
      unfold DualLatent.applyFG
      rw [ite_eq_right (by clear *- hp9_t; omega), ite_eq_right (by clear *- hp9_t; omega)]
    have hfg_t := fgStep_ge9_aux hr.2.2.2 u v hv_eq
      (fgSetup_of_dualStateInv hr.2.2.2 hop_nz u v) rfl rfl rfl
      (show 9 ≤ (rMemState (f_act a wd).data).mem (base + hdrPhase) by exact hp9_t)
    have hsm_nd := (hfg_t.2.2.2.1 (base + hdrNDst) (by dsimp only [hdrNDst]; omega)
      (base_add_ne (by decide)) (base_add_ne (by decide))).trans
      (hsch.2 hdrNDst (by decide) (by decide)).symm
    have hcls' := hcls
    dsimp only at hcls'
    rw [← htick_eq] at hcls'
    rw [hsm_ph, hsm_nd] at hcls'
    have hy_mem_fn := congrArg Memory.State.mem hy_mem
    have hp_s : ((stepNon58 hr hne5_t hne8_t).choose).mem (base + hdrPhase) =
        s_rep'.mem (base + hdrPhase) := by
      have hp_tmp := hp_q_eq; rw [hq_eq] at hp_tmp; exact hp_tmp
    change (rMemState (stepNon58 hr hne5_t hne8_t).choose).mem (base + hdrPhase) = _ at hp_s
    rw [hy_mem_fn] at hp_s; dsimp only at hp_s
    have hnd_s : (rMemState (q_det (f_act a wd)).data).mem (base + hdrNDst) =
        (rMemState (q_det (f_act a wd)).data).mem (base + hdrNDst) := rfl
    conv_lhs at hnd_s =>
      rw [hq_eq]
      change (rMemState (stepNon58 hr hne5_t hne8_t).choose).mem (base + hdrNDst)
      rw [hy_mem_fn]; dsimp only
    rw [hp_s, hnd_s] at hcls'
    refine ⟨by rw [hq_eq]; exact hr_post, hsch_q,
      fun hp4' => ?_, fun hp0' hpos_s => ?_, fun hp9' => ?_,
      fun hgc => by
        rw [hq_eq]
        exact hT (fun h7 => by clear *- h7 hp9_t; omega) (fun _ => hgc),
      hmid, ?_⟩
    · rcases hcls' with ⟨hp1, hnp2, _⟩ | ⟨_, _, h0⟩ | ⟨_, _, h9, _⟩
      · obtain ⟨hnc1, hsd1, hev1⟩ := hpres1.1.2 hp1
        obtain ⟨hnc2, hsd2, hev2⟩ := hpres2.1.1 hnp2
        rw [hq_eq]; dsimp only
        exact ⟨by rw [hnc2, hnc1, hfg_dst, SlotLatent.applyFG_nCap]; exact hnc,
          by rw [hev2, hev1, hfg_dst, applyFG_false_evs, hev],
          fun hc => hsd2.trans (hsd1.trans (by
            rw [hfg_dst]; exact (applyFG_seeds_heq ..).trans (hsd hc)))⟩
      · clear *- hp4' h0; omega
      · clear *- hp4' h9; omega
    · rcases hcls' with ⟨_, _, h4⟩ | ⟨hnp1, hp2, _⟩ | ⟨_, _, h9, _⟩
      · clear *- hp0' h4; omega
      · rw [hq_eq] at hpos_s ⊢; dsimp only at hpos_s ⊢
        obtain ⟨hnc2, hsd2, hev2⟩ := hpres2.1.2 hp2
        obtain ⟨hnd1, hsd1, _, hev1⟩ :=
          hpres1.2.resolve_left (hnc2 ▸ hpos_s.ne')
        exact ⟨by rw [hnc2, hnd1, hfg_dst, SlotLatent.applyFG_nCap]; exact hnc,
          by rw [hev2, hev1 not_false, hfg_dst, applyFG_false_evs, hev],
          fun hc => hsd2.trans (hsd1.trans (by
            rw [hfg_dst]; exact (applyFG_seeds_heq ..).trans (hsd hc)))⟩
      · clear *- hp0' h9; omega
    · rcases hcls' with ⟨_, _, h4⟩ | ⟨_, _, h0⟩ | ⟨_, _, _, hnd_q⟩
      · clear *- hp9' h4; omega
      · clear *- hp9' h0; omega
      · refine ⟨hnd_q, fun hpos_d => ?_⟩
        rw [hq_eq] at hpos_d ⊢; dsimp only at hpos_d ⊢
        obtain ⟨hnd2, hsd2, _, hev2⟩ := hpres2.2.resolve_left hpos_d.ne'
        obtain ⟨hnd1, hsd1, _, hev1⟩ :=
          hpres1.2.resolve_left (hnd2 ▸ hpos_d.ne')
        exact ⟨by rw [hnd2, hnd1, hfg_dst, SlotLatent.applyFG_nCap]; exact hnc,
          by rw [hev2 not_false, hev1 not_false, hfg_dst, applyFG_false_evs, hev],
          fun hc => hsd2.trans (hsd1.trans (by
            rw [hfg_dst]; exact (applyFG_seeds_heq ..).trans (hsd hc)))⟩
    · rcases hcls' with ⟨_, _, h4⟩ | ⟨_, _, h0⟩ | ⟨_, _, h9, _⟩
      · exact Or.inl h4
      · exact Or.inr (Or.inl h0)
      · exact Or.inr (Or.inr h9)
  have hpost0 := hf_post9 a₀ ha₀ wd0
  have hinv_rep' : DualStateInv c U V w base s_dict' L_rep' s_rep' := hpost0.1.2.2.2
  have hν'_bind : (ν.bind fun t => (μ_step t).map fun q => ⟨q.latent, q.data⟩) =
      μ_idx.bind (fun a =>
        (PMF.uniformOfFintype (SeedWords c w capDst)).map (f_next a)) := by
    rw [hν, PMF.bind_bind]
    refine congrArg (μ_idx.bind ·) (funext fun a => ?_)
    rw [PMF.bind_map]; dsimp only [μ_step]
    conv_rhs => unfold PMF.map
    refine congrArg ((PMF.uniformOfFintype _).bind ·) (funext fun wd => ?_)
    dsimp only [Function.comp_def]; rw [PMF.pure_map]
  refine ⟨μ_step, hstep_all, ⟨L_rep', s_rep', hinv_rep', ?_⟩, ?_⟩
  · dsimp only
    rcases hpost0.2.2.2.2.2.2.2 with hp4' | hp0' | hp9'
    · -- Branch E1 (`9 → 4` Stage B promotion): `slotDst → slotSrc`
      have hcapSrc'_eq : dualCapSrc base s_rep'.mem = capDst :=
        (hinv_rep'.sl_le7 (by clear *- hp4'; omega)).1.symm.trans (hpost0.2.2.1 hp4').1
      rw [ite_eq_left (by clear *- hp4'; omega), hcapSrc'_eq]
      refine ⟨α, μ_idx, fun a => evs_of a ++ [fgEv], f_next, hν'_bind, fun a ha wd => ?_⟩
      have hp_w := hf_post9 a ha wd
      obtain ⟨hnc', hev', hsd'⟩ := hp_w.2.2.1 hp4'
      exact ⟨hp_w.1, hp_w.2.1, hnc', hev', hsd'⟩
    · -- Branch E2 (`10/11 → 0` rebuild completion): `slotDst → slotSrc`
      rw [ite_eq_left (by rw [hp0']; decide)]
      by_cases hcs0 : dualCapSrc base s_rep'.mem = 0
      · rw [hcs0]
        refine singleEpochLaw_zero fun t' ht' => ?_
        rw [hν'_bind, PMF.mem_support_bind_iff] at ht'; obtain ⟨a, ha, hm⟩ := ht'
        rw [PMF.mem_support_map_iff] at hm; obtain ⟨wd, _, rfl⟩ := hm
        have hp_w := hf_post9 a ha wd
        have hp0_w : (rMemState (f_next a wd).data).mem (base + hdrPhase) = 0 :=
          (hp_w.2.1.2 hdrPhase (by decide) (by decide)).symm.trans hp0'
        have hnc_w : (f_next a wd).latent.slotSrc.nCap = 0 :=
          (hp_w.1.2.2.2.sl_le7 (by rw [hp0_w]; decide)).1.trans
            (hp_w.2.1.capSrc_eq.symm.trans hcs0)
        exact ⟨hp_w.1, hp_w.2.1, hnc_w⟩
      · have hcs_pos : 0 < dualCapSrc base s_rep'.mem := Nat.pos_of_ne_zero hcs0
        have hl0_pos : 0 < L_rep'.slotSrc.nCap :=
          (hinv_rep'.sl_le7 (by rw [hp0']; decide)).1.symm ▸ hcs_pos
        have hcs_eq : dualCapSrc base s_rep'.mem = capDst :=
          (hinv_rep'.sl_le7 (by rw [hp0']; decide)).1.symm.trans
            (hpost0.2.2.2.1 hp0' hl0_pos).1
        rw [hcs_eq]
        refine ⟨α, μ_idx, fun a => evs_of a ++ [fgEv], f_next, hν'_bind,
          fun a ha wd => ?_⟩
        have hp_w := hf_post9 a ha wd
        have hp0_w : (rMemState (f_next a wd).data).mem (base + hdrPhase) = 0 :=
          (hp_w.2.1.2 hdrPhase (by decide) (by decide)).symm.trans hp0'
        have hpos_w : 0 < (f_next a wd).latent.slotSrc.nCap := by
          rw [(hp_w.1.2.2.2.sl_le7 (by rw [hp0_w]; decide)).1, ← hp_w.2.1.capSrc_eq]
          exact hcs_pos
        obtain ⟨hnc', hev', hsd'⟩ := hp_w.2.2.2.1 hp0' hpos_w
        exact ⟨hp_w.1, hp_w.2.1, hnc', hev', hsd'⟩
    · -- Branch E3 (`9 ≤ ph'`): stays in `SingleEpochLaw` on `slotDst`
      rw [ite_eq_right (by clear *- hp9'; omega), ite_eq_right (by clear *- hp9'; omega),
        ite_eq_right (by clear *- hp9'; omega), ite_eq_right (by clear *- hp9'; omega)]
      have hnd_rep' : s_rep'.mem (base + hdrNDst) = capDst := (hpost0.2.2.2.2.1 hp9').1
      rw [hnd_rep']
      by_cases hcd0 : capDst = 0
      · rw [hcd0]
        refine singleEpochLaw_zero fun t' ht' => ?_
        rw [hν'_bind, PMF.mem_support_bind_iff] at ht'; obtain ⟨a, ha, hm⟩ := ht'
        rw [PMF.mem_support_map_iff] at hm; obtain ⟨wd, _, rfl⟩ := hm
        have hp_w := hf_post9 a ha wd
        have hp9_w : 9 ≤ (rMemState (f_next a wd).data).mem (base + hdrPhase) := by
          rw [← hp_w.2.1.2 hdrPhase (by decide) (by decide)]; exact hp9'
        have hnc_w : (f_next a wd).latent.slotDst.nCap = 0 :=
          (hp_w.1.2.2.2.sl_ge9 hp9_w).1.trans
            ((hp_w.2.2.2.2.1 hp9').1.trans hcd0)
        exact ⟨hp_w.1, hp_w.2.1, hnc_w⟩
      · have hcd_pos : 0 < capDst := Nat.pos_of_ne_zero hcd0
        refine ⟨α, μ_idx, fun a => evs_of a ++ [fgEv], f_next, hν'_bind,
          fun a ha wd => ?_⟩
        have hp_w := hf_post9 a ha wd
        have hp9_w : 9 ≤ (rMemState (f_next a wd).data).mem (base + hdrPhase) := by
          rw [← hp_w.2.1.2 hdrPhase (by decide) (by decide)]; exact hp9'
        have hpos_w : 0 < (f_next a wd).latent.slotDst.nCap := by
          rw [(hp_w.1.2.2.2.sl_ge9 hp9_w).1, (hp_w.2.2.2.2.1 hp9').1]; exact hcd_pos
        obtain ⟨hnc', hev', hsd'⟩ := (hp_w.2.2.2.2.1 hp9').2 hpos_w
        exact ⟨hp_w.1, hp_w.2.1, hnc', hev', hsd'⟩
  · -- Slow-path probability in `9 ≤ ph`
    rw [hν, PMF.bind_bind]
    refine toOuterMeasure_bind_le_const μ_idx _ _ _ fun a ha => ?_
    rw [PMF.bind_map]
    let sl_mid := fun wd =>
      ((f_act a wd).latent.applyFG
        ((f_act a wd).data.mem (base + hdrPhase)) opTag u v).slotDst
    refine (toOuterMeasure_map_pure_le _ _ _ (fun wd => (sl_mid wd).GoodCovers)
      fun wd hgc hbad => ?_).trans ?_
    · apply hbad
      exact ⟨by dsimp only [q_det, qDetNon58]; split_ifs <;> rfl,
        (hf_post9 a ha wd).2.2.2.2.2.1 hgc⟩
    · refine (uniform_seedWords_bad_le hUw hdst_safe (evs_of a ++ [fgEv]) sl_mid
        (fun wd => ?_) (fun wd => ?_) (fun hc wd => ?_) fun hc => ?_).trans
        (half_stepFailureProb_le c s_dict o)
      · obtain ⟨_, hsch, hnc, _, _⟩ := hf a ha wd
        simp only [↓reduceIte] at hnc
        have hp_t : 9 ≤ (f_act a wd).data.mem (base + hdrPhase) := by
          have hp_e : (f_act a wd).data.mem (base + hdrPhase) = ph :=
            (hsch.2 hdrPhase (by decide) (by decide)).symm
          rw [hp_e]; exact hp9
        dsimp only [sl_mid]; unfold DualLatent.applyFG
        rw [ite_eq_right (by clear *- hp_t; omega), ite_eq_right (by clear *- hp_t; omega)]
        dsimp only; rw [SlotLatent.applyFG_nCap]; exact hnc
      · obtain ⟨_, hsch, _, hev, _⟩ := hf a ha wd
        simp only [↓reduceIte] at hev
        have hp_t : 9 ≤ (f_act a wd).data.mem (base + hdrPhase) := by
          have hp_e : (f_act a wd).data.mem (base + hdrPhase) = ph :=
            (hsch.2 hdrPhase (by decide) (by decide)).symm
          rw [hp_e]; exact hp9
        dsimp only [sl_mid]; unfold DualLatent.applyFG
        rw [ite_eq_right (by clear *- hp_t; omega), ite_eq_right (by clear *- hp_t; omega)]
        dsimp only; rw [applyFG_false_evs, hev]
      · obtain ⟨_, hsch, _, _, hsd⟩ := hf a ha wd
        have hp_t : 9 ≤ (f_act a wd).data.mem (base + hdrPhase) := by
          have hp_e : (f_act a wd).data.mem (base + hdrPhase) = ph :=
            (hsch.2 hdrPhase (by decide) (by decide)).symm
          rw [hp_e]; exact hp9
        dsimp only [sl_mid]; unfold DualLatent.applyFG
        rw [ite_eq_right (by clear *- hp_t; omega), ite_eq_right (by clear *- hp_t; omega)]
        dsimp only; exact (applyFG_seeds_heq ..).trans (hsd hc)
      · have hmid₀ := (hf_post9 a ha wd0).2.2.2.2.2.2.1
        obtain ⟨hr_0, hsch_0, hnc_0, hev_0, _⟩ := hf a ha wd0
        simp only [↓reduceIte] at hnc_0 hev_0
        have hp_t0 : 9 ≤ (f_act a wd0).data.mem (base + hdrPhase) := by
          have hp_e0 : (f_act a wd0).data.mem (base + hdrPhase) = ph :=
            (hsch_0.2 hdrPhase (by decide) (by decide)).symm
          rw [hp_e0]; exact hp9
        have hnc_m0 : (sl_mid wd0).nCap = capDst := by
          dsimp only [sl_mid]; unfold DualLatent.applyFG
          rw [ite_eq_right (by clear *- hp_t0; omega), ite_eq_right (by clear *- hp_t0; omega)]
          dsimp only; rw [SlotLatent.applyFG_nCap]; exact hnc_0
        have hev_m0 : (sl_mid wd0).evs = evs_of a ++ [fgEv] := by
          dsimp only [sl_mid]; unfold DualLatent.applyFG
          rw [ite_eq_right (by clear *- hp_t0; omega), ite_eq_right (by clear *- hp_t0; omega)]
          dsimp only; rw [applyFG_false_evs, hev_0]
        have hfg0 := fgStep_ge9_aux hr_0.2.2.2 u v hv_eq
          (fgSetup_of_dualStateInv hr_0.2.2.2 hop_nz u v) rfl rfl rfl hp_t0
        have hsm_ge8_eq := hfg0.2.2.2.1 (base + hdrPhase) (by dsimp only [hdrPhase]; omega)
          (base_add_ne (by decide)) (base_add_ne (by decide))
        have hb₀ := (dualCoreInv_slot_evs_bounds hmid₀).2
          (by rw [hsm_ge8_eq]; change 8 ≤ (f_act a wd0).data.mem (base + hdrPhase)
              clear *- hp_t0; omega)
          (hnc_m0 ▸ hc)
        rwa [hnc_m0, hev_m0] at hb₀

/-- Mutating operations (`insert` and `delete`) preserve `DualDistInv` across all 5 regimes and
bound slow-path probability by `stepFailureProbWhp c s_dict o`. -/
theorem dualDistInv_step_mutate {c U V w base opTag v_val : ℕ}
    (s_dict : Dictionary.State U) (o : Dynamic.Op U)
    (hv : (Dynamic.spec U V U).valid s_dict o)
    (u : Fin U) (v : Fin V)
    (ho_mut : (o = .insert u v.val ∧ opTag = 1 ∧ v_val = v.val) ∨
      (o = .delete u ∧ opTag = 2 ∧ v_val = 0))
    (ν : PMF (LatentRState (DualLatent c U V) rWhp))
    (hfit_peak : Fits w (base + stepSuccinctPeakWordsWhp c V w s_dict o))
    (hd : DualDistInv c U V w base s_dict ν) :
    ∃ μ_step : LatentRState (DualLatent c U V) rWhp →
        PMF (WhpStepROutcome (DualLatent c U V) ((Dynamic.spec U V U).Result o) rWhp),
      (∀ t ∈ ν.support,
        ExecRCodeSteps w opCodeWhp
          ((subroutineCodeWhp c U V w).prepare whpEncode o t.data)
          ((μ_step t).map WhpStepROutcome.toCodeOutcome)
          (base + stepSuccinctPeakWordsWhp c V w s_dict o) ∧
        ∀ q ∈ (μ_step t).support,
          q.result = ((Dynamic.spec U V U).stepFn s_dict o).2 ∧
          whpDecode (V := V) o q.data.regs = some q.result ∧
          DualRep c U V w base ((Dynamic.spec U V U).stepFn s_dict o).1 q.latent q.data ∧
          (∀ addr < base, q.data.mem addr = t.data.mem addr)) ∧
      DualDistInv c U V w base ((Dynamic.spec U V U).stepFn s_dict o).1
        (ν.bind fun t => (μ_step t).map fun q => ⟨q.latent, q.data⟩) ∧
      (ν.bind μ_step).toOuterMeasure {q | ¬q.WithinBudget (worstCaseTimeWhp c)} ≤
        stepFailureProbWhp c s_dict o := by
  obtain ⟨L_rep, s_rep, hinv_rep, hregimes⟩ := hd
  dsimp only at hregimes
  by_cases hp4 : s_rep.mem (base + hdrPhase) ≤ 4
  · rw [ite_eq_left hp4] at hregimes
    exact dualDistInv_mutate_le4 s_dict o hv u v ho_mut ν hfit_peak hinv_rep hp4 hregimes
  · rw [ite_eq_right hp4] at hregimes
    by_cases hp5 : s_rep.mem (base + hdrPhase) = 5
    · rw [ite_eq_left hp5] at hregimes
      exact dualDistInv_mutate_ph5 s_dict o hv u v ho_mut ν hfit_peak hinv_rep hp5 hregimes
    · rw [ite_eq_right hp5] at hregimes
      by_cases hp67 : s_rep.mem (base + hdrPhase) = 6 ∨ s_rep.mem (base + hdrPhase) = 7
      · rw [ite_eq_left hp67] at hregimes
        exact dualDistInv_mutate_67 s_dict o hv u v ho_mut ν hfit_peak hinv_rep hp67 hregimes
      · rw [ite_eq_right hp67] at hregimes
        by_cases hp8 : s_rep.mem (base + hdrPhase) = 8
        · rw [ite_eq_left hp8] at hregimes
          exact dualDistInv_mutate_8 s_dict o hv u v ho_mut ν hfit_peak hinv_rep hp8 hregimes
        · rw [ite_eq_right hp8] at hregimes
          have hp9 : 9 ≤ s_rep.mem (base + hdrPhase) := by
            clear *- hp4 hp5 hp67 hp8; omega
          exact dualDistInv_mutate_ge9 s_dict o hv u v ho_mut ν hfit_peak hinv_rep hp9 hregimes

/-! ## Section 2: `HighProbObliviousImpl` Certificates, `1 · OPT` Bit Bounds, and Headlines -/

/-- Distributional `HighProbStateTransitionImpl` certificate over `Basis.exact` for the deamortized
worst-case WHP resizable succinct dynamic dictionary of
[Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 3–6][BenderFarachColtonKuszmaulKuszmaul2024] on the word-granular Resizable Word RAM. -/
@[expose]
noncomputable def highProbStateImpl {c U V w base : ℕ}
    (hw11 : 11 ≤ w) (hU0 : 0 < U) (hUw : Fits w U) (hV0 : 0 < V) (hVw : V ≤ 2 ^ w) :
    HighProbStateTransitionImpl (subroutineCodeWhp c U V w) (Dynamic.spec U V U)
      w base ![] (Dictionary.empty U) where
  Latent := DualLatent c U V
  spaceBound := spaceBoundWhp c V w
  peakSpaceBound := stepSuccinctPeakWordsWhp c V w
  initSteps := initStepsWhp
  worstCaseTime := fun _ => worstCaseTimeWhp c
  failureProb := stepFailureProbWhp c
  rep := DualRep c U V w base
  distInv := fun pref ν =>
    DualDistInv c U V w base ((Dynamic.spec U V U).run (Dictionary.empty U) pref).1 ν
  encode := whpEncode
  decode := whpDecode (V := V)
  bounded := fun hr => hr.bounded
  frontier_le := fun hr => hr.frontier_le
  arguments_fit := fun o hv i _ => whpEncode_fits hUw hVw hw11 o hv i
  init_exec := fun hx₀ hfr₀ _ hfit₀ => by
    dsimp only [subroutineCodeWhp]
    rw [(Dynamic.spec U V U).run_nil]
    exact dualDistInv_init hw11 hU0 hUw hV0 hVw hx₀ hfr₀ hfit₀
  step_exec := fun pref o ν _ hv hfit hd hsupp => by
    set s := ((Dynamic.spec U V U).run (Dictionary.empty U) pref).1
    have hrun_app :
        ((Dynamic.spec U V U).run (Dictionary.empty U) (pref ++ [o])).1 =
          ((Dynamic.spec U V U).stepFn s o).1 := by
      rw [(Dynamic.spec U V U).run_append]; rfl
    rw [hrun_app]
    cases o with
    | query u =>
      exact dualDistInv_step_query s u ν hfit hd hsupp
    | insert u v_raw =>
      exact dualDistInv_step_mutate (opTag := 1) (v_val := v_raw) s (.insert u v_raw) hv
        u ⟨v_raw, hv.2⟩ (Or.inl ⟨rfl, rfl, rfl⟩) ν hfit hd
    | delete u =>
      exact dualDistInv_step_mutate (opTag := 2) (v_val := 0) s (.delete u) hv
        u ⟨0, hV0⟩ (Or.inr ⟨rfl, rfl, rfl⟩) ν hfit hd

/-- Reusable `HighProbObliviousImpl` certificate over `Basis.exact` for the deamortized worst-case
WHP resizable succinct dynamic dictionary (`initSteps = initStepsWhp`, `worstCaseTime = fun _ =>
worstCaseTimeWhp c`, `failureProb = stepFailureProbWhp c`, resting space `spaceBoundWhp`, peak space
`stepSuccinctPeakWordsWhp`). -/
@[expose]
noncomputable def highProbImpl {c U V w base : ℕ}
    (hw11 : 11 ≤ w) (hU0 : 0 < U) (hUw : Fits w U) (hV0 : 0 < V) (hVw : V ≤ 2 ^ w) :
    HighProbObliviousImpl (subroutineCodeWhp c U V w)
      ((Dynamic.spec U V U).toObliviousSequenceSpec (Dictionary.empty U)) w base ![] :=
  (highProbStateImpl (c := c) (base := base) hw11 hU0 hUw hV0 hVw).toHighProbObliviousImpl

/-- Standard-basis (`Basis.standard`) `HighProbObliviousImpl` certificate obtained via basis
simulation (`HighProbObliviousImpl.toStandard`). -/
noncomputable abbrev highProbImplStandard {c U V w base : ℕ}
    (hw11 : 11 ≤ w) (hU0 : 0 < U) (hUw : Fits w U) (hV0 : 0 < V) (hVw : V ≤ 2 ^ w) :
    HighProbObliviousImpl (subroutineCodeWhpStandard c U V w)
      ((Dynamic.spec U V U).toObliviousSequenceSpec (Dictionary.empty U)) w base ![] :=
  (highProbImpl (c := c) (base := base) hw11 hU0 hUw hV0 hVw).toStandard

/-- **`1 · OPT` Resting Bit-Space Bound (`w_mul_spaceBoundWhp_le_bits`):**
At any dictionary state `s_dict` with `n = #(Dictionary.dom s_dict)` active keys, the resting word
budget `spaceBoundWhp c V w s_dict` occupies at most
`Dynamic.optBits U V n + whpResizableSpaceFactor c * n * Dynamic.logLogFactor n +
(whpResizableSpaceConst + 1) * w` bits. -/
theorem w_mul_spaceBoundWhp_le_bits {U : ℕ} (c V w : ℕ) (s_dict : Dictionary.State U) :
    let n := (Dictionary.dom s_dict).card
    w * spaceBoundWhp c V w s_dict ≤
      Dynamic.optBits U V n +
        whpResizableSpaceFactor c * n * Dynamic.logLogFactor n +
        (whpResizableSpaceConst + 1) * w :=
  succinctWords_mul_w_le_bits (whpResizableSpaceFactor c) whpResizableSpaceConst U V w
    (Dictionary.dom s_dict).card

/-- **`1 · OPT` Stepwise Peak Bit-Space Bound (`w_mul_stepSuccinctPeakWordsWhp_le_bits`):**
Across any operation `o` from `s_dict` (`n₀ = #(dom s_dict)`) to `s_dict'` (`n₁ = #(dom s_dict')`),
the intermediate hardware frontier above `base` uses at most the maximum of the `1 · OPT` bit
bounds at `n₀` and `n₁` (never `2 · OPT`, including across all 12 background rebuild phases). -/
theorem w_mul_stepSuccinctPeakWordsWhp_le_bits {U : ℕ} (c V w : ℕ)
    (s_dict : Dictionary.State U) (o : Dynamic.Op U) :
    let s_dict' := ((Dynamic.spec U V U).stepFn s_dict o).1
    let n₀ := (Dictionary.dom s_dict).card
    let n₁ := (Dictionary.dom s_dict').card
    w * stepSuccinctPeakWordsWhp c V w s_dict o ≤
      max (Dynamic.optBits U V n₀ +
            whpResizableSpaceFactor c * n₀ * Dynamic.logLogFactor n₀ +
            (whpResizableSpaceConst + 1) * w)
          (Dynamic.optBits U V n₁ +
            whpResizableSpaceFactor c * n₁ * Dynamic.logLogFactor n₁ +
            (whpResizableSpaceConst + 1) * w) := by
  intro s_dict' n₀ n₁
  unfold stepSuccinctPeakWordsWhp
  rcases le_total (spaceBoundWhp c V w s_dict) (spaceBoundWhp c V w s_dict') with hle | hle
  · rw [max_eq_right hle]
    exact (w_mul_spaceBoundWhp_le_bits c V w s_dict').trans (le_max_right _ _)
  · rw [max_eq_left hle]
    exact (w_mul_spaceBoundWhp_le_bits c V w s_dict).trans (le_max_left _ _)

/-- Discharges `ObliviousPeakFits` for `highProbImpl` / `highProbImplStandard` from the pure
specification-level `PeakFitsHistory` condition over `stepSuccinctPeakWordsWhp`. -/
theorem obliviousPeakFits_of_succinctWords {c U V w base : ℕ}
    {ops : List (Dynamic.Op U)}
    (hfit : PeakFitsHistory (D := Dynamic.spec U V U) w base (stepSuccinctPeakWordsWhp c V w)
      (Dictionary.empty U) ops) :
    ObliviousPeakFits w base
      (fun pref o =>
        stepSuccinctPeakWordsWhp c V w ((Dynamic.spec U V U).run (Dictionary.empty U) pref).1 o)
      [] ops :=
  (obliviousPeakFits_iff_peakFitsHistory (Dynamic.spec U V U) w base
    (stepSuccinctPeakWordsWhp c V w) (Dictionary.empty U) [] ops).mpr hfit

/-- **Deamortized Worst-Case WHP Resizable Succinct Dictionary (`seq_whp_succinct`):**
Word-RAM adaptation of [Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Theorem 1.1 and Sections 3–6][BenderFarachColtonKuszmaulKuszmaul2024] to **oblivious operation
sequences** (`ValidHistory (Dictionary.empty U) ops` fixed before coin tosses) on the word-granular
**Resizable Word RAM** (`Basis.exact`, `11 ≤ w`, `0 < U < 2 ^ w`, `0 < V ≤ 2 ^ w`), replacing
idealized fully random hash functions with explicit `BitPackedDoubleTabulation` hash tables sampled
dynamically via `RInstr.rand` and zero-slack `.grow` / `.shrink` frontier resizing:
1. `initCodeWhp c U V w` executes in `initStepsWhp = 1164` deterministic instructions within
   `base + spaceBoundWhp c V w (Dictionary.empty U)` words;
2. The parameter-free operational body `opCodeWhp` (`¬ReadsWidth`) executes any admissible oblivious
   sequence `ops` under `ExecWhpSteps` within `1 · OPT` stepwise peak frontier
   `base + stepSuccinctPeakWordsWhp c V w s_t o`;
3. Every final trajectory `tr ∈ τ_final.support` is `w`-bounded, rests at frontier
   `≤ base + spaceBoundWhp c V w s_fin` (`1 · OPT`), keeps `regs mBaseWhp = base`, preserves caller
   memory `[0, base)`, and outputs the exact canonical dictionary transcript (`Las Vegas` exact on
   every branch);
4. With probability at least
   `1 - ∑_t stepFailureProbWhp c s_t o_t` (`stepFailureProbWhp c s_t o_t ≤
   (max #(dom s_t) (whpThreshold c))⁻¹ ^ c`, and `0` when `U < whpThreshold c`), **every** operation
   in `ops` completes within `worstCaseTimeWhp c` (`O_c(1)`) Resizable Word RAM instructions. -/
theorem seq_whp_succinct (c : ℕ) {U V w base : ℕ} {x₀ : RData rWhp}
    (ops : List (Dynamic.Op U))
    (hw11 : 11 ≤ w) (hU0 : 0 < U) (hUw : Fits w U) (hV0 : 0 < V) (hVw : V ≤ 2 ^ w)
    (hx₀ : x₀.Bounded w) (hfr₀ : x₀.frontier = base)
    (hfit₀ : Fits w (base + spaceBoundWhp c V w (Dictionary.empty U)))
    (hvh : (Dynamic.spec U V U).ValidHistory (Dictionary.empty U) ops)
    (hfit_ops : PeakFitsHistory (D := Dynamic.spec U V U) w base (stepSuccinctPeakWordsWhp c V w)
      (Dictionary.empty U) ops) :
    let C := highProbImpl (c := c) (base := base) hw11 hU0 hUw hV0 hVw
    let s_fin := ((Dynamic.spec U V U).run (Dictionary.empty U) ops).1
    let failSum := totalFailureProb
      (fun pref o => stepFailureProbWhp c ((Dynamic.spec U V U).run (Dictionary.empty U) pref).1 o)
      [] ops
    ∃ (ν₀ : PMF (LatentRState (DualLatent c U V) rWhp))
      (τ_final : PMF (WhpSeqROutcome (DualLatent c U V) (Dynamic.Op.Result (U := U)) rWhp)),
      ExecRCodeSteps w (initCodeWhp c U V w) x₀
        (ν₀.map fun t => ⟨t.data, initStepsWhp, true⟩)
        (base + spaceBoundWhp c V w (Dictionary.empty U)) ∧
      (∀ t ∈ ν₀.support, ∀ addr < base, t.data.mem addr = x₀.mem addr) ∧
      C.Steps ops (ν₀.map WhpSeqROutcome.ofLatentRState) τ_final ∧
      (∀ tr ∈ τ_final.support,
        tr.data.Bounded w ∧
        (base ≤ tr.data.frontier ∧ tr.data.frontier ≤ base + spaceBoundWhp c V w s_fin ∧
          tr.data.regs mBaseWhp = base) ∧
        (∀ addr < base, tr.data.mem addr = x₀.mem addr) ∧
        tr.transcript = ((Dynamic.spec U V U).run (Dictionary.empty U) ops).2) ∧
      τ_final.toOuterMeasure {tr | tr.allWithinBudget = false} ≤ failSum ∧
      1 - failSum ≤ τ_final.toOuterMeasure {tr | tr.allWithinBudget = true} := by
  intro C s_fin failSum
  have hv_seq : ((Dynamic.spec U V U).toObliviousSequenceSpec (Dictionary.empty U)).ValidOpSeq
      ops :=
    ((Dynamic.spec U V U).validOpSeq_iff_validHistory (Dictionary.empty U) ops).mpr hvh
  have hob_fit : ObliviousPeakFits w base C.peakSpaceBound [] ops :=
    obliviousPeakFits_of_succinctWords hfit_ops
  have hfit₀' : Fits w (base + C.spaceBound []) := by
    change Fits w (base + spaceBoundWhp c V w
      ((Dynamic.spec U V U).run (Dictionary.empty U) []).1)
    rwa [(Dynamic.spec U V U).run_nil]
  have hseq := C.seq_whp ops hx₀ hfr₀ (fun j => Fin.elim0 j) hfit₀' hv_seq hob_fit
  dsimp only [C, highProbImpl, HighProbStateTransitionImpl.toHighProbObliviousImpl,
    highProbStateImpl, StateTransitionSpec.toObliviousSequenceSpec] at hseq
  obtain ⟨ν₀, τ_final, he_init, hcaller₀, hex, hfin, hcontract, hfail, hsucc⟩ := hseq
  rw [(Dynamic.spec U V U).run_nil] at he_init
  have hcontract' :=
    ((Dynamic.spec U V U).toObliviousSequenceSpec_contract_iff_of_hasStepFn
      (Dictionary.empty U) hvh (τ_final.map WhpSeqROutcome.transcript)).mp hcontract
  refine ⟨ν₀, τ_final, he_init, hcaller₀, hex, fun tr htr => ?_, hfail, hsucc⟩
  obtain ⟨hbdd, ⟨hlo, hhi, hreg⟩, hmem⟩ := hfin tr htr
  have htr_eq : tr.transcript = ((Dynamic.spec U V U).run (Dictionary.empty U) ops).2 :=
    hcontract' tr.transcript ((PMF.mem_support_map_iff _ _ _).mpr ⟨tr, htr, rfl⟩)
  exact ⟨hbdd, ⟨hlo, hhi, hreg⟩, hmem, htr_eq⟩

/-- **Standard-Basis Deamortized Worst-Case WHP Resizable Succinct Dictionary
(`seq_whp_succinct_standard`):**
Transports `seq_whp_succinct` to `Basis.standard` via `highProbImplStandard`. -/
theorem seq_whp_succinct_standard (c : ℕ) {U V w base : ℕ} {x₀ : RData rWhp}
    (ops : List (Dynamic.Op U))
    (hw11 : 11 ≤ w) (hU0 : 0 < U) (hUw : Fits w U) (hV0 : 0 < V) (hVw : V ≤ 2 ^ w)
    (hx₀ : x₀.Bounded w) (hfr₀ : x₀.frontier = base)
    (hfit₀ : Fits w (base + spaceBoundWhp c V w (Dictionary.empty U)))
    (hvh : (Dynamic.spec U V U).ValidHistory (Dictionary.empty U) ops)
    (hfit_ops : PeakFitsHistory (D := Dynamic.spec U V U) w base (stepSuccinctPeakWordsWhp c V w)
      (Dictionary.empty U) ops) :
    let C := highProbImplStandard (c := c) (base := base) hw11 hU0 hUw hV0 hVw
    let s_fin := ((Dynamic.spec U V U).run (Dictionary.empty U) ops).1
    let failSum := totalFailureProb
      (fun pref o => stepFailureProbWhp c ((Dynamic.spec U V U).run (Dictionary.empty U) pref).1 o)
      [] ops
    ∃ (ν₀ : PMF (LatentRState (DualLatent c U V) rWhp))
      (τ_final : PMF (WhpSeqROutcome (DualLatent c U V) (Dynamic.Op.Result (U := U)) rWhp)),
      ExecRCodeSteps w (subroutineCodeWhpStandard c U V w).initCode x₀
        (ν₀.map fun t => ⟨t.data, initStepsWhp, true⟩)
        (base + spaceBoundWhp c V w (Dictionary.empty U)) ∧
      (∀ t ∈ ν₀.support, ∀ addr < base, t.data.mem addr = x₀.mem addr) ∧
      C.Steps ops (ν₀.map WhpSeqROutcome.ofLatentRState) τ_final ∧
      (∀ tr ∈ τ_final.support,
        tr.data.Bounded w ∧
        (base ≤ tr.data.frontier ∧ tr.data.frontier ≤ base + spaceBoundWhp c V w s_fin ∧
          tr.data.regs mBaseWhp = base) ∧
        (∀ addr < base, tr.data.mem addr = x₀.mem addr) ∧
        tr.transcript = ((Dynamic.spec U V U).run (Dictionary.empty U) ops).2) ∧
      τ_final.toOuterMeasure {tr | tr.allWithinBudget = false} ≤ failSum ∧
      1 - failSum ≤ τ_final.toOuterMeasure {tr | tr.allWithinBudget = true} := by
  intro C s_fin failSum
  obtain ⟨ν₀, τ_final, he_init, hcaller₀, hex, hfin, hfail, hsucc⟩ :=
    seq_whp_succinct c ops hw11 hU0 hUw hV0 hVw hx₀ hfr₀ hfit₀ hvh hfit_ops
  exact ⟨ν₀, τ_final, he_init.mapSimulates .exactStandard, hcaller₀,
    hex.mapSimulates .exactStandard, hfin, hfail, hsucc⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
