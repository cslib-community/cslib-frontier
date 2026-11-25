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
  rw [Nat.add_assoc] at hr2
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

/-- One `initFactorStep`: read the two length words of the record at `curRaw` and write its
4-word descriptor at `curDesc`, leaving everything below `curDesc` untouched. -/
private theorem initFactorStep_spec {w curRaw curDesc : ℕ} {f : FactorTable ℕ ℕ}
    {rest : List (FactorTable ℕ ℕ)} {s₀ t : Memory.State} (hwf : Memory.WellFormed w t)
    (hF : s₀.frontier ≤ curDesc) (hdst : curDesc + 4 ≤ t.frontier)
    (hpres : PreservesBelow s₀.frontier s₀ t)
    (hraw : HoldsIn curRaw ((f :: rest).flatMap encodeFactor) s₀) :
    let p := initFactorStep ((), (curRaw, curDesc))
    let t₁ := (Memory.spec 0).clientState t p
    (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t p) ∧
      (Memory.spec 0).clientResult t p =
        (curRaw + 2 + f.scope.length + f.entries.size, curDesc + 4) ∧
      t₁.frontier = t.frontier ∧ Memory.WellFormed w t₁ ∧ PreservesBelow curDesc t t₁ ∧
      PreservesBelow s₀.frontier s₀ t₁ ∧
      (∀ t', PreservesBelow (curDesc + 4) t₁ t' → HoldsFactor curDesc f t') ∧
      memoryCost p t = 6 ∧
      HoldsIn (curRaw + 2 + f.scope.length + f.entries.size) (rest.flatMap encodeFactor) s₀ := by
  obtain ⟨h1, h2, hm_sc, hm_en, hsc, hen, hrest⟩ := holdsIn_encodeFactor_cons hraw
  have hen_bd := hen.1
  rw [Array.length_toList] at hen_bd
  have hr₀ : t.mem curRaw = f.scope.length := (hpres.2.2 _ h1).trans hm_sc
  have hr₁ : t.mem (curRaw + 1) = f.entries.size := (hpres.2.2 _ h2).trans hm_en
  obtain ⟨hv, hfr, hwf₁, hpF, hout, hhf, hm0, hm2⟩ := writeDesc_spec (w := w) (F := s₀.frontier)
    ⟨curDesc, curRaw + 2, f.scope.length, curRaw + 2 + f.scope.length, f.entries.size⟩ hwf hF
    hdst hsc.1 hen_bd rfl rfl (hsc.mono_frontier hpres) (hen.mono_frontier hpres)
  dsimp only at hout hhf hm0 hm2
  have hst : (Memory.spec 0).clientState t (initFactorStep ((), (curRaw, curDesc))) =
      (Memory.spec 0).clientState t (writeDesc ⟨curDesc, curRaw + 2, t.mem curRaw,
        curRaw + 2 + t.mem curRaw, t.mem (curRaw + 1)⟩) := rfl
  rw [hr₀, hr₁] at hst
  dsimp only
  rw [hst]
  refine ⟨?_, ?_, hfr, hwf₁, ⟨by omega, hfr.ge, fun a ha => hout a (Or.inl ha)⟩, hpres.trans hpF,
    fun t' hp => hhf.mono (by omega) (by rw [hm0]; omega) (by rw [hm2]; omega) hp, rfl, hrest⟩
  · refine validHistory_read_bind (lt_of_lt_of_le h1 hpres.2.1) ?_
    refine validHistory_read_bind (lt_of_lt_of_le h2 hpres.2.1) ?_
    rw [hr₀, hr₁]
    exact validHistory_bind_step hv (validHistory_pure _ _ _)
  · change (curRaw + 2 + t.mem curRaw + t.mem (curRaw + 1), curDesc + 4) = _
    rw [hr₀, hr₁]

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
  | [], _, curDesc, t, _, _, hbd, hpres, _ => by
      simp only [List.length_nil] at hbd
      exact ⟨validHistory_pure w t _, rfl, PreservesBelow.refl (by omega), hpres,
        show curDesc ≤ t.frontier by omega, (memoryCost_pure _ _).le⟩
  | f :: rest, curRaw, curDesc, t, hwf, hF, hbd, hpres, hraw => by
      simp only [List.length_cons] at hbd ⊢
      obtain ⟨hv, hres, hfr, hwf₁, hpcd, hpF, hhf, hcost, hrest⟩ :=
        initFactorStep_spec hwf hF (by omega) hpres hraw
      obtain ⟨hv', hfr', hpcd', hpF', hholds, hcost'⟩ :=
        initFactors_loop rest _ (curDesc + 4) _ hwf₁ (by omega) (by rw [hfr]; omega) hpF hrest
      rw [show iterate initFactorStep () (rest.length + 1) (curRaw, curDesc) =
          (initFactorStep ((), (curRaw, curDesc)) >>= iterate initFactorStep () rest.length)
          from rfl, StateTransitionSpec.clientState_bind, memoryCost_bind', hres]
      exact ⟨validHistory_bind_step hv (by rwa [hres]), hfr'.trans hfr,
        hpcd.trans (hpcd'.mono_bound (by omega)), hpF', ⟨hhf _ hpcd', hholds⟩, by omega⟩

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
  obtain ⟨hv, hfr, -, hpres, hholds, hcost⟩ :=
    initFactors_loop factors rawPtr s.frontier ⟨s.mem, s.frontier + 4 * factors.length⟩
      ⟨hfit, hwf.mem_fits⟩ le_rfl (by dsimp only; omega)
      ⟨le_rfl, by dsimp only; omega, fun _ _ => rfl⟩ hraw
  dsimp only [initFactors]
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    clientState_allocDirty, clientResult_allocDirty, StateTransitionSpec.clientState_bind,
    StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_pure,
    StateTransitionSpec.clientResult_pure, memoryCost_bind', memoryCost_allocDirty,
    clientState_allocDirty, clientResult_allocDirty, memoryCost_bind', memoryCost_pure]
  exact ⟨validHistory_allocDirty_bind hfit (validHistory_bind_step hv (validHistory_pure w _ _)),
    hfr, hpres, rfl, hholds, by omega⟩

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
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (st : ℕ × ℕ) (t : Memory.State) =>
        Memory.WellFormed w t ∧ s.frontier ≤ st.2 ∧ st.2 + 4 * j ≤ t.frontier ∧
          PreservesBelow s.frontier s t ∧
          ∃ rem : List (FactorTable ℕ ℕ), rem.length = j ∧
            HoldsIn st.1 (rem.flatMap encodeFactor) s)
      (fun j st t ⟨hwf_t, hlo_t, hbd_t, hpres_t, rem, hrem_l, hraw_t⟩ => ?_)
      ⟨⟨hfit, hmem.mem_fits⟩, le_rfl, by dsimp only; omega,
        ⟨le_rfl, by dsimp only; omega, fun _ _ => rfl⟩, factors₀, hlen₀, hraw₀⟩
    rcases rem with _ | ⟨f, rest⟩
    · cases hrem_l
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hrem_l
    subst hrem_l
    obtain ⟨h1, h2, hm_sc, hm_en, -, hen, -⟩ := holdsIn_encodeFactor_cons hraw_t
    have hen_bd := hen.1
    rw [Array.length_toList] at hen_bd
    have hle := hpres_t.2.1
    obtain ⟨-, hres, hfr, hwf₁, -, hpF, -, -, hrest⟩ :=
      initFactorStep_spec hwf_t hlo_t (by omega) hpres_t hraw_t
    dsimp only
    rw [hpres_t.2.2 _ h1, hpres_t.2.2 _ h2, hm_sc, hm_en, hres]
    refine ⟨⟨hwf_t.frontier_fits.of_le (by omega), ?_⟩, hwf₁, by omega, by rw [hfr]; omega, hpF,
      rest, rfl, hrest⟩
    repeat (any_goals refine ⟨?_, ?_⟩)
    all_goals exact hwf_t.frontier_fits.of_le (by omega)

end Cslib.Algorithms.WordRAM.VariableElimination
