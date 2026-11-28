/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.VariableElimination.Instance
public import CslibFrontier.Algorithms.WordRAM.VariableElimination.Memory
import CslibFrontier.Computability.WordRAM.Realization.FramedLoop
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
  obtain ⟨h1, hm_sc, hr1⟩ := hraw.cons
  obtain ⟨h2, hm_en, hr2⟩ := hr1.cons
  rw [Nat.add_assoc] at hr2
  obtain ⟨hsc, hr3⟩ := HoldsIn.append_iff.mp hr2
  obtain ⟨hen, hrest⟩ := HoldsIn.append_iff.mp hr3
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

/-- Invariant of the loop of `initFactors` after `k` records, for the input state `s`: the
descriptors of the first `k` factors sit at `s.frontier` and survive every later step that keeps
the cells below the next descriptor. -/
private abbrev InitInv (w L : ℕ) (factors : List (FactorTable ℕ ℕ)) (s : Memory.State) (k : ℕ)
    (st : ℕ × ℕ) (t : Memory.State) : Prop :=
  Memory.WellFormed w t ∧ t.frontier = s.frontier + 4 * L ∧ st.2 = s.frontier + 4 * k ∧
    HoldsIn st.1 ((factors.drop k).flatMap encodeFactor) s ∧
    ∀ t', PreservesBelow st.2 t t' → HoldsFactorList s.frontier (factors.take k) t'

private theorem initFactorStep_framed {w L k : ℕ} {factors : List (FactorTable ℕ ℕ)}
    {s t : Memory.State} {st : ℕ × ℕ} (hlen : factors.length = L) (hk : k < L)
    (hpres : PreservesBelow s.frontier s t) (hinv : InitInv w L factors s k st t) :
    Memory.FramedTriple w t (initFactorStep ((), st)) 6 (Set.Ici s.frontier)
      (InitInv w L factors s (k + 1)) := by
  obtain ⟨cur, desc⟩ := st
  obtain ⟨hwf_t, hfr, hd, hraw_t, hhold⟩ := hinv
  dsimp only at hd hraw_t hhold; subst hd
  rw [List.drop_eq_getElem_cons (by omega)] at hraw_t
  obtain ⟨h1, h2, hm_sc, hm_en, hsc, hen, hrest⟩ := holdsIn_encodeFactor_cons hraw_t
  have hen_bd := hen.1
  simp only [Array.length_toList] at hen_bd
  have hr₀ : t.mem cur = factors[k].scope.length := (hpres.2.2 _ h1).trans hm_sc
  have hr₁ : t.mem (cur + 1) = factors[k].entries.size := (hpres.2.2 _ h2).trans hm_en
  obtain ⟨hv, hfr₁, hwf₁, -, hout, hhf, hm0, hm2⟩ := writeDesc_spec (w := w) (F := s.frontier)
    ⟨s.frontier + 4 * k, cur + 2, t.mem cur, cur + 2 + t.mem cur, t.mem (cur + 1)⟩ hwf_t
    (Nat.le_add_right _ _) (by dsimp only; omega) hsc.1 (by dsimp only; omega) hr₀ hr₁
    (hsc.mono_frontier hpres) (hr₀ ▸ hen.mono_frontier hpres)
  have hwd := writeDesc_framed (F := s.frontier) _ hv (Nat.le_add_right _ _)
  dsimp only at hout hhf hm0 hm2
  unfold initFactorStep
  framed_triple
  · refine ⟨hwf₁, hfr₁.trans hfr, by omega, by rw [hr₀, hr₁]; exact hrest, fun t' hp => ?_⟩
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
      holdsFactorList_append, List.length_take_of_le (by omega)]
    have hf := hhf.mono le_rfl (by rw [hm0]; omega) (by rw [hm2]; omega) hp
    exact ⟨hhold t' (PreservesBelow.trans ⟨by omega, hfr₁.ge, fun a ha => hout a (Or.inl ha)⟩
      (hp.mono_bound (by omega))), hf, hf.1⟩

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
  obtain ⟨-, hloop⟩ := Memory.FramedTriple.iterate (w := w) (body := initFactorStep)
    (safe := fun _ _ _ => True) (d := ()) (n := factors.length) (c := 6)
    (s := ⟨s.mem, s.frontier + 4 * factors.length⟩) (a₀ := (rawPtr, s.frontier))
    (S := Set.Ici s.frontier) (InitInv w factors.length factors s)
    ⟨⟨hfit, hwf.mem_fits⟩, rfl, rfl, by simpa using hraw, fun t' hp => by
      simpa [HoldsFactorList] using (Nat.le_add_right _ _).trans hp.2.1⟩
    (fun k hk _ t hinv hmod => ⟨trivial, initFactorStep_framed rfl hk
      (preservesBelow_of_modifies hmod ⟨le_rfl, Nat.le_add_right _ _, fun _ _ => rfl⟩) hinv⟩)
    fun _ _ h _ => h
  have hft : Memory.FramedTriple w s (initFactors (rawPtr, factors.length))
      (1 + 6 * factors.length) (Set.Ici s.frontier) fun r t =>
        t.frontier = s.frontier + 4 * factors.length ∧ r = s.frontier ∧
        HoldsFactorList r factors t := by
    dsimp only [initFactors]
    exact Memory.FramedTriple.mono (Memory.FramedTriple.allocDirty_bind hfit
      (Memory.FramedTriple.call (c₂ := 0) hloop subset_rfl fun _ t h _ =>
        Memory.FramedTriple.pure ⟨h.2.1, rfl, by
          simpa using h.2.2.2.2 t (PreservesBelow.refl (by omega))⟩)) (by omega) fun _ _ => id
  obtain ⟨hv, hc, hm, hfr, hres, hholds⟩ := framedTriple_iff_realization.mp hft
  exact ⟨hv, hfr, preservesBelow_of_modifies hm (.refl le_rfl), hres, hholds, hc⟩

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
    refine (Memory.FramedTriple.iterate (w := w) (s := ⟨s.mem, s.frontier + 4 * d.2⟩) (c := 6)
      (S := Set.Ici s.frontier) (Q := fun _ _ => True) (InitInv w d.2 factors₀ s)
      ⟨⟨hfit, hmem.mem_fits⟩, rfl, rfl, by simpa using hraw₀, fun t' hp => by
        simpa [HoldsFactorList] using (Nat.le_add_right _ _).trans hp.2.1⟩
      (fun k hk st t hinv hmod => ?_) fun _ _ _ _ => trivial).1
    have hpres : PreservesBelow s.frontier s t :=
      preservesBelow_of_modifies hmod ⟨le_rfl, Nat.le_add_right _ _, fun _ _ => rfl⟩
    refine ⟨?_, initFactorStep_framed hlen₀ hk hpres hinv⟩
    obtain ⟨hwf_t, hfr, hd, hraw_t, -⟩ := hinv
    rw [List.drop_eq_getElem_cons (by omega)] at hraw_t
    obtain ⟨h1, h2, hm_sc, hm_en, -, hen, -⟩ := holdsIn_encodeFactor_cons hraw_t
    have hen_bd := hen.1
    simp only [Array.length_toList] at hen_bd
    dsimp only
    rw [hpres.2.2 _ h1, hpres.2.2 _ h2, hm_sc, hm_en]
    refine ⟨hwf_t.frontier_fits.of_le (by omega), ?_⟩
    repeat (any_goals refine ⟨?_, ?_⟩)
    all_goals exact hwf_t.frontier_fits.of_le (by omega)

end Cslib.Algorithms.WordRAM.VariableElimination
