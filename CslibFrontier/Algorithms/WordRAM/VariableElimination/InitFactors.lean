/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.VariableElimination.Instance
public import CslibFrontier.Algorithms.WordRAM.VariableElimination.Memory
import CslibFrontier.Tactic.Realize

/-!
# Input Factor Parsing (`initFactors`)

Reads `factors.length` serialized `encodeFactor` payloads from the input word array and emits a
contiguous array of 4-word descriptors (`HoldsFactorList`). Parallel with bucket elimination steps.

## Main definitions

* `Cslib.Algorithms.WordRAM.VariableElimination.initFactors`: serialized factor descriptor parser.
-/

public section

namespace Cslib.Algorithms.WordRAM.VariableElimination

open Cslib.Logic.PL Cslib.Logic.PL.CSP
open Cslib.Algorithms.Lean.CSP
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

private theorem holdsIn_encodeFactor_cons {curRaw : ℕ} {f : FactorTable ℕ ℕ}
    {rest : List (FactorTable ℕ ℕ)} {s : Memory.State}
    (hraw : HoldsIn curRaw ((f :: rest).flatMap encodeFactor) s) :
    curRaw < s.frontier ∧
      curRaw + 1 < s.frontier ∧
      s.mem curRaw = f.scope.length ∧
      s.mem (curRaw + 1) = f.entries.size ∧
      HoldsIn (curRaw + 2) f.scope s ∧
      HoldsIn (curRaw + 2 + f.scope.length) f.entries.toList s ∧
      HoldsIn (curRaw + 2 + f.scope.length + f.entries.size)
        (rest.flatMap encodeFactor) s := by
  simp only [List.flatMap_cons, encodeFactor, List.cons_append, List.nil_append,
    List.append_assoc] at hraw
  obtain ⟨h1, hm_sc, hr1⟩ := holdsIn_cons_shift hraw
  obtain ⟨h2, hm_en, hr2⟩ := holdsIn_cons_shift hr1
  rw [show curRaw + 1 + 1 = curRaw + 2 by omega] at hr2
  obtain ⟨hsc, hr3⟩ := holdsIn_append_split hr2
  obtain ⟨hen, hrest⟩ := holdsIn_append_split hr3
  exact ⟨h1, h2, hm_sc, hm_en, hsc, hen, by simpa [Array.length_toList] using hrest⟩

private def initFactorStep : Unit × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ) :=
  fun ⟨_, (curRaw, curDesc)⟩ =>
    Memory.read curRaw >>= fun scLen =>
    Memory.read (curRaw + 1) >>= fun enLen =>
    writeDesc ⟨curDesc, curRaw + 2, scLen, curRaw + 2 + scLen, enLen⟩ >>= fun _ =>
    pure (curRaw + 2 + scLen + enLen, curDesc + 4)

/-- Parse serialized raw `encodeFactor` records into a 4-word descriptor array. -/
def initFactors (args : ℕ × ℕ) : Memory.Prog ℕ :=
  Memory.allocDirty (4 * args.2) >>= fun descBase =>
  iterate initFactorStep () args.2 (args.1, descBase) >>= fun _ =>
  pure descBase

private theorem initFactors_loop {w : ℕ} {s₀ : Memory.State} :
    ∀ (rem : List (FactorTable ℕ ℕ)) (curRaw curDesc : ℕ) (t : Memory.State),
      Memory.WellFormed w t →
      s₀.frontier ≤ curDesc →
      curDesc + 4 * rem.length ≤ t.frontier →
      PreservesBelow s₀.frontier s₀ t →
      HoldsIn curRaw (rem.flatMap encodeFactor) s₀ →
      let p := iterate initFactorStep () rem.length (curRaw, curDesc)
      let t' := (Memory.spec 0).clientState t p
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t p) ∧
        t'.frontier = t.frontier ∧
        PreservesBelow curDesc t t' ∧
        PreservesBelow s₀.frontier s₀ t' ∧
        HoldsFactorList curDesc rem t' ∧
        memoryCost p t ≤ 6 * rem.length
  | [], curRaw, curDesc, t, _, _, hbd, hpres, _ => by
      dsimp only
      have h0 : iterate initFactorStep () 0 (curRaw, curDesc) = pure (curRaw, curDesc) := rfl
      simp only [List.length_nil] at hbd ⊢
      rw [h0]
      exact ⟨validHistory_pure w t _, rfl, PreservesBelow.refl (by omega), hpres,
        by change curDesc ≤ t.frontier; omega,
        by simp [memoryCost_pure]⟩
  | f :: rest, curRaw, curDesc, t, hwf, hF_le, hbd, hpres, hraw => by
      dsimp only
      obtain ⟨h1, h2, hm_scLen, hm_enLen, hsc_s0, hen_s0, hrest_raw⟩ :=
        holdsIn_encodeFactor_cons hraw
      have ht_scLen : t.mem curRaw = f.scope.length := by
        rw [hpres.2.2 curRaw h1, hm_scLen]
      have ht_enLen : t.mem (curRaw + 1) = f.entries.size := by
        rw [hpres.2.2 (curRaw + 1) h2, hm_enLen]
      let wdArgs : WriteDescArgs :=
        ⟨curDesc, curRaw + 2, f.scope.length, curRaw + 2 + f.scope.length, f.entries.size⟩
      have hsc_t : HoldsIn (curRaw + 2) f.scope t := hsc_s0.mono hsc_s0.1 hpres
      have hen_t : HoldsIn (curRaw + 2 + f.scope.length) f.entries.toList t :=
        hen_s0.mono hen_s0.1 hpres
      simp only [List.length_cons] at hbd
      have hdst_lt : curDesc + 4 ≤ t.frontier := by omega
      have hfit_scPtr : Fits w (curRaw + 2) :=
        hwf.frontier_fits.of_le (by have := hsc_t.1; omega)
      have hfit_scLen : Fits w f.scope.length :=
        hwf.frontier_fits.of_le (by have := hsc_t.1; omega)
      have hfit_enPtr : Fits w (curRaw + 2 + f.scope.length) :=
        hwf.frontier_fits.of_le (by have := hen_t.1; omega)
      have hfit_enLen : Fits w f.entries.size :=
        hwf.frontier_fits.of_le (by have := hen_t.1; rw [Array.length_toList] at this; omega)
      have hwd_val := writeDesc_valid wdArgs hdst_lt hfit_scPtr hfit_scLen hfit_enPtr hfit_enLen
      have hwd_fr_p := writeDesc_frame wdArgs t
      have hst1_def : (Memory.spec 0).clientState t (writeDesc wdArgs) =
          ⟨Function.update (Function.update (Function.update
            (Function.update t.mem curDesc (curRaw + 2))
            (curDesc + 1) f.scope.length)
            (curDesc + 2) (curRaw + 2 + f.scope.length))
            (curDesc + 3) f.entries.size, t.frontier⟩ := rfl
      generalize ht₁ : (Memory.spec 0).clientState t (writeDesc wdArgs) = t₁ at hwd_fr_p hst1_def
      obtain ⟨ht1_fr, hwd_out⟩ := hwd_fr_p
      dsimp only [wdArgs] at hwd_out
      have hwf₁ : Memory.WellFormed w t₁ :=
        by rw [← ht₁]; exact wellFormed_clientState hwf hwd_val
      have hpres_cd : PreservesBelow curDesc t t₁ :=
        ⟨by omega, by rw [ht1_fr], fun a ha => hwd_out a (Or.inl ha)⟩
      have hpres₁ : PreservesBelow s₀.frontier s₀ t₁ := by
        refine ⟨hpres.1, by rw [ht1_fr]; exact hpres.2.1, fun a ha => ?_⟩
        rw [hwd_out a (Or.inl (lt_of_lt_of_le ha hF_le))]
        exact hpres.2.2 a ha
      have hih := initFactors_loop rest
        (curRaw + 2 + f.scope.length + f.entries.size) (curDesc + 4) t₁ hwf₁
        (by omega) (by rw [ht1_fr]; omega) hpres₁ hrest_raw
      dsimp only at hih
      obtain ⟨hih_val, hih_fr, hih_pres_cd, hih_pres_F, hih_holds, hih_cost⟩ := hih
      have hr_st (addr : ℕ) : (Memory.spec 0).clientState t (Memory.read addr) = t := rfl
      have hr_res (addr : ℕ) : (Memory.spec 0).clientResult t (Memory.read addr) = t.mem addr := rfl
      have hpure_st {α : Type} (x : α) (u : Memory.State) :
          (Memory.spec 0).clientState u (pure x) = u := rfl
      have hpure_res {α : Type} (x : α) (u : Memory.State) :
          (Memory.spec 0).clientResult u (pure x) = x := rfl
      have hstep_val : (Memory.spec w).ValidHistory t
          ((Memory.spec w).clientHistory t (initFactorStep ((), (curRaw, curDesc)))) := by
        unfold initFactorStep
        dsimp only
        refine validHistory_read_bind (lt_of_lt_of_le h1 hpres.2.1) ?_
        rw [ht_scLen]
        refine validHistory_read_bind (lt_of_lt_of_le h2 hpres.2.1) ?_
        rw [ht_enLen]
        refine validHistory_bind_step hwd_val ?_
        rw [ht₁]
        exact validHistory_pure w t₁ _
      have hstep_st : (Memory.spec 0).clientState t (initFactorStep ((), (curRaw, curDesc))) =
          t₁ := by
        unfold initFactorStep
        dsimp only
        rw [StateTransitionSpec.clientState_bind, hr_st, hr_res, ht_scLen,
          StateTransitionSpec.clientState_bind, hr_st, hr_res, ht_enLen,
          StateTransitionSpec.clientState_bind, ht₁, hpure_st]
      have hstep_res : (Memory.spec 0).clientResult t (initFactorStep ((), (curRaw, curDesc))) =
          (curRaw + 2 + f.scope.length + f.entries.size, curDesc + 4) := by
        unfold initFactorStep
        dsimp only
        rw [StateTransitionSpec.clientResult_bind, hr_st, hr_res, ht_scLen,
          StateTransitionSpec.clientResult_bind, hr_st, hr_res, ht_enLen,
          StateTransitionSpec.clientResult_bind, ht₁, hpure_res]
      have hstep_cost : memoryCost (initFactorStep ((), (curRaw, curDesc))) t ≤ 6 := by
        unfold initFactorStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read, hr_st, hr_res, ht_scLen,
          memoryCost_bind', memoryCost_read, hr_st, hr_res, ht_enLen,
          memoryCost_bind', ht₁, writeDesc_cost, memoryCost_pure, Nat.add_zero]
      have hf_final : HoldsFactor curDesc f
          ((Memory.spec 0).clientState t₁
            (iterate initFactorStep () rest.length
              (curRaw + 2 + f.scope.length + f.entries.size, curDesc + 4))) := by
        have hm0 : t₁.mem curDesc = curRaw + 2 := by
          rw [hst1_def]; dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_self]
        have hm1 : t₁.mem (curDesc + 1) = f.scope.length := by
          rw [hst1_def]; dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_self]
        have hm2 : t₁.mem (curDesc + 2) = curRaw + 2 + f.scope.length := by
          rw [hst1_def]; dsimp only
          rw [Function.update_of_ne (by omega), Function.update_self]
        have hm3 : t₁.mem (curDesc + 3) = f.entries.size := by
          rw [hst1_def]; dsimp only; rw [Function.update_self]
        unfold HoldsFactor
        rw [hih_pres_cd.2.2 curDesc (by omega),
          hih_pres_cd.2.2 (curDesc + 1) (by omega),
          hih_pres_cd.2.2 (curDesc + 2) (by omega),
          hih_pres_cd.2.2 (curDesc + 3) (by omega),
          hm0, hm1, hm2, hm3]
        exact ⟨by rw [hih_fr, ht1_fr]; exact hdst_lt, rfl, rfl,
          hsc_s0.mono hsc_s0.1 hih_pres_F,
          hen_s0.mono hen_s0.1 hih_pres_F⟩
      simp only [List.length_cons]
      have hiter_eq : iterate initFactorStep () (rest.length + 1) (curRaw, curDesc) =
          (initFactorStep ((), (curRaw, curDesc)) >>= iterate initFactorStep () rest.length) := rfl
      rw [hiter_eq, StateTransitionSpec.clientState_bind, hstep_st, hstep_res]
      refine ⟨validHistory_bind_step hstep_val ?_,
        by rw [hih_fr, ht1_fr],
        hpres_cd.trans (hih_pres_cd.mono_bound (by omega)),
        hih_pres_F,
        ⟨hf_final, hih_holds⟩, ?_⟩
      · rw [hstep_st, hstep_res]; exact hih_val
      · rw [memoryCost_bind', hstep_st, hstep_res]; omega

theorem initFactors_spec {w : ℕ} {rawPtr facLen : ℕ}
    {factors : List (FactorTable ℕ ℕ)} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hlen : factors.length = facLen)
    (hraw : HoldsIn rawPtr (factors.flatMap encodeFactor) s)
    (hfit : Fits w (s.frontier + 4 * facLen)) :
    let res := (Memory.spec 0).clientResult s (initFactors (rawPtr, facLen))
    let s' := (Memory.spec 0).clientState s (initFactors (rawPtr, facLen))
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (initFactors (rawPtr, facLen))) ∧
      s'.frontier = s.frontier + 4 * facLen ∧
      PreservesBelow s.frontier s s' ∧
      res = s.frontier ∧
      HoldsFactorList res factors s' ∧
      memoryCost (initFactors (rawPtr, facLen)) s ≤ 1 + 6 * facLen := by
  subst hlen
  dsimp only
  unfold initFactors
  dsimp only
  have hv_alloc : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (Memory.allocDirty (4 * factors.length))) :=
    validHistory_allocDirty hfit
  let s₁ : Memory.State := ⟨s.mem, s.frontier + 4 * factors.length⟩
  have ha_st :
      (Memory.spec 0).clientState s (Memory.allocDirty (4 * factors.length)) = s₁ := rfl
  have ha_res :
      (Memory.spec 0).clientResult s (Memory.allocDirty (4 * factors.length)) = s.frontier := rfl
  have hwf₁ : Memory.WellFormed w s₁ := ⟨hfit, hwf.mem_fits⟩
  have hpres₁ : PreservesBelow s.frontier s s₁ :=
    ⟨le_rfl, by dsimp only [s₁]; omega, fun _ _ => rfl⟩
  obtain ⟨hl_val, hl_fr, _, hl_pres, hl_holds, hl_cost⟩ :=
    initFactors_loop factors rawPtr s.frontier s₁ hwf₁ le_rfl
      (by dsimp only [s₁]; omega) hpres₁ hraw
  have hpure_st {α : Type} (x : α) (u : Memory.State) :
      (Memory.spec 0).clientState u (pure x) = u := rfl
  have hpure_res {α : Type} (x : α) (u : Memory.State) :
      (Memory.spec 0).clientResult u (pure x) = x := rfl
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    ha_st, ha_res,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    hpure_st, hpure_res]
  refine ⟨validHistory_bind_step hv_alloc ?_,
    by rw [hl_fr],
    hl_pres, rfl, hl_holds, ?_⟩
  · rw [ha_st, ha_res]
    exact validHistory_bind_step hl_val (validHistory_pure w _ _)
  · rw [memoryCost_bind', memoryCost_allocDirty, ha_st, ha_res,
      memoryCost_bind', memoryCost_pure, Nat.add_zero]
    omega

theorem initFactors_realizes :
    Realizes .exact initFactors WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        ∃ (factors : List (FactorTable ℕ ℕ)),
          Fits w 4 ∧
          Fits w (s.frontier + 4 * args.2) ∧
          factors.length = args.2 ∧
          HoldsIn args.1 (factors.flatMap encodeFactor) s)
      (fun _ _ => 0) := by
  unfold initFactors
  realize [writeDesc_realizes]
  · obtain ⟨_, _, hfit, _, _⟩ := h; exact hfit.of_le (by omega)
  · obtain ⟨_, h4, _, _, _⟩ := h; exact h4
  · obtain ⟨factors₀, _, hfit, hlen₀, hraw₀⟩ := h
    let s₁ : Memory.State := ⟨s.mem, s.frontier + 4 * d.2⟩
    have hwf₁ : Memory.WellFormed w s₁ := ⟨hfit, hmem.mem_fits⟩
    have hpres₁ : PreservesBelow s.frontier s s₁ :=
      ⟨le_rfl, by dsimp only [s₁]; omega, fun _ _ => rfl⟩
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (st : ℕ × ℕ) (t : Memory.State) =>
        Memory.WellFormed w t ∧
        t.frontier = s.frontier + 4 * d.2 ∧
        s.frontier ≤ st.2 ∧
        st.2 + 4 * j ≤ t.frontier ∧
        PreservesBelow s.frontier s t ∧
        ∃ rem,
          rem.length = j ∧
          HoldsIn st.1 (rem.flatMap encodeFactor) s)
      (fun j st t ⟨hwf_t, hfr_t, hlo_t, hbd_t, hpres_t, rem, hrem_l, hraw_t⟩ => ?_)
      ⟨hwf₁, rfl, le_rfl, by dsimp only [s₁]; omega, hpres₁, factors₀, hlen₀, hraw₀⟩
    dsimp only
    rcases rem with _ | ⟨f, rest⟩
    · cases hrem_l
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hrem_l
    subst hrem_l
    obtain ⟨h1, h2, hm_scLen, hm_enLen, hsc_s0, hen_s0, hrest_raw⟩ :=
      holdsIn_encodeFactor_cons hraw_t
    have ht_scLen : t.mem st.1 = f.scope.length := by
      rw [hpres_t.2.2 st.1 h1, hm_scLen]
    have ht_enLen : t.mem (st.1 + 1) = f.entries.size := by
      rw [hpres_t.2.2 (st.1 + 1) h2, hm_enLen]
    have hr_st (addr : ℕ) : (Memory.spec 0).clientState t (Memory.read addr) = t := rfl
    have hr_res (addr : ℕ) : (Memory.spec 0).clientResult t (Memory.read addr) = t.mem addr := rfl
    have hpure_st {α : Type} (x : α) (u : Memory.State) :
        (Memory.spec 0).clientState u (pure x) = u := rfl
    have hpure_res {α : Type} (x : α) (u : Memory.State) :
        (Memory.spec 0).clientResult u (pure x) = x := rfl
    have hraw_end : st.1 + 2 + f.scope.length + f.entries.size ≤ s.frontier := by
      have hbd := hen_s0.1
      rw [Array.length_toList] at hbd
      omega
    have ht_le : s.frontier ≤ t.frontier := hpres_t.2.1
    refine ⟨?_, ?_⟩
    · refine ⟨hwf_t.frontier_fits.of_le (by omega), ?_⟩
      simp only [ht_scLen, ht_enLen]
      repeat (any_goals refine ⟨?_, ?_⟩)
      all_goals exact hwf_t.frontier_fits.of_le (by omega)
    · let wdArgs : WriteDescArgs :=
        ⟨st.2, st.1 + 2, f.scope.length, st.1 + 2 + f.scope.length, f.entries.size⟩
      have hwd_val := writeDesc_valid (w := w) (s := t) wdArgs (by dsimp only [wdArgs]; omega)
        (hwf_t.frontier_fits.of_le (by dsimp only [wdArgs]; omega))
        (hwf_t.frontier_fits.of_le (by dsimp only [wdArgs]; omega))
        (hwf_t.frontier_fits.of_le (by dsimp only [wdArgs]; omega))
        (hwf_t.frontier_fits.of_le (by dsimp only [wdArgs]; omega))
      have hwd_fr_p := writeDesc_frame wdArgs t
      generalize ht₁ : (Memory.spec 0).clientState t (writeDesc wdArgs) = t₁ at hwd_fr_p
      obtain ⟨ht1_fr, hwd_out⟩ := hwd_fr_p
      dsimp only [wdArgs] at hwd_out
      have hwf₁ : Memory.WellFormed w t₁ :=
        by rw [← ht₁]; exact wellFormed_clientState hwf_t hwd_val
      have hpres_next : PreservesBelow s.frontier s t₁ := by
        refine ⟨hpres_t.1, by rw [ht1_fr]; exact hpres_t.2.1, fun a ha => ?_⟩
        rw [hwd_out a (Or.inl (lt_of_lt_of_le ha hlo_t))]
        exact hpres_t.2.2 a ha
      unfold initFactorStep
      dsimp only
      rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
        hr_st, hr_res, ht_scLen,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
        hr_st, hr_res, ht_enLen,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
        ht₁, hpure_st, hpure_res]
      exact ⟨hwf₁, by rw [ht1_fr]; exact hfr_t, by dsimp only; omega,
        by dsimp only; rw [ht1_fr]; omega, hpres_next, rest, rfl, hrest_raw⟩

end Cslib.Algorithms.WordRAM.VariableElimination
