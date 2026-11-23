/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SharedWordFork
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CountingTerminalDispatch
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WorkTapePredicate
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO

/-!
# A guarded continuation from a serialized work-tape input

The dispatcher computes a three-bit header followed by the child's word. A disabled query returns
its constant bit immediately. An enabled query copies the word to the child's designated tape,
resets its head to the origin, and transfers control. The header lies outside the child's tape view.
-/

public section

namespace Turing.MultiTapeATM.GuardedWord

open MultiTapeTM TwoWordLoad CountingTerminalDispatch

private theorem copied_view {K : ℕ} {S : Type} (src : Fin K) (child : MultiTapeATM K Bool S)
    (input flags word : List Bool) :
    let flag := Fin.last K
    let ix := src.castSucc
    let cfg := TwoWordInput.ready flag ix input flags []
    viewCfg Fin.castSuccEmb ((copied flag ix word cfg).withState (some child.toPTM.initial)) =
      SharedWordFork.start src child input word 0 := by
  apply Cfg.ext <;> try rfl
  · funext i z
    by_cases hi : i = src
    · subst i
      simp [viewCfg, copied, Cfg.withState, SharedWordFork.start, WordGameLeaf.config]
    · simp [viewCfg, copied, Cfg.withState, SharedWordFork.start, WordGameLeaf.config,
        TwoWordInput.ready, TwoWordInput.words, blank, wordsCfg, tapesCfg, hi,
        Fin.castSucc_ne_last]
  · funext i
    by_cases hi : i = src <;>
      simp [viewCfg, copied, Cfg.withState, SharedWordFork.start, WordGameLeaf.config,
        TwoWordInput.ready, blank, wordsCfg, tapesCfg, hi, Fin.castSucc_ne_last]

private theorem work_view {U : ℕ} {S : Type} (q : Fin U) (atm : MultiTapeATM U Bool S)
    (e : Fin U ↪ Fin (U + 2)) (he : e q = Fin.natAdd U 0) (input word : List Bool) :
    viewCfg e ((WorkTapePredicate.config input word).withState (some atm.toPTM.initial)) =
      SharedWordFork.start q atm input word 0 := by
  apply Cfg.ext <;> try rfl
  · funext i z
    by_cases hi : i = q
    · subst i
      simp [viewCfg, WorkTapePredicate.config, SharedWordFork.start, WordGameLeaf.config,
        tapesCfg, Cfg.withState, he]
    · have hn : e i ≠ Fin.natAdd U 0 := by rw [← he]; exact e.injective.ne hi
      simp [viewCfg, WorkTapePredicate.config, SharedWordFork.start, WordGameLeaf.config,
        blank, tapesCfg, Cfg.withState, hi, hn]
  · funext i
    by_cases hi : i = q <;>
      simp [viewCfg, WorkTapePredicate.config, SharedWordFork.start, WordGameLeaf.config,
        blank, tapesCfg, Cfg.withState, hi]

/-- Compute a guarded word and either return the constant bit or invoke the selected finite
machine. Only the active branch assumes a halting bound for that machine. -/
theorem exists_guarded_runner {α S : Type} {K : ℕ} [Finite S] (src : Fin K)
    (child : MultiTapeATM K Bool S) {enc : α ↪ List Bool} (active answer : α → Bool)
    (word : α → List Bool) (T : α → ℕ)
    (hf : ComputableInO (fun a => [active a, false, answer a] ++ word a) enc encBits T T) :
    ∃ (u : ℕ) (Q : Type) (_ : Finite Q) (run : MultiTapeATM (u + 2) Bool Q) (C : ℕ),
      ∀ (host : List Bool) (a : α) (t : ℕ),
        let source := (WorkTapePredicate.config host (enc a)).withState (some run.toPTM.initial)
        let target := SharedWordFork.start src child host (word a) 0
        let time := C * (T a + 1) + (2 * (word a).length + 16) + t
        (active a = true → child.HaltsWithin t target) →
          run.HaltsWithin time source ∧ (run.AcceptsWithin time source ↔
            if active a then child.AcceptsWithin t target else answer a = true) := by
  classical
  let flag := Fin.last K
  let ix := src.castSucc
  have hne : flag ≠ ix := (Fin.castSucc_ne_last src).symm
  let family := fun (_ _ : Bool) => child.extendTapes Fin.castSuccEmb
  let disp := machine flag ix hne family
  have hg : ComputableInDegree (fun _ : List Bool => ([] : List Bool)) encBits encBits 1 1 :=
    (ComputableInDegree.const (encMid := encBits) []).mono
  have hblank : ComputableInO (fun _ : α => ([] : List Bool)) enc encBits T T :=
    hg.inO_one.comp_linear hf
  obtain ⟨u, selected, Q, hQ, tm, c, ht⟩ :=
    exists_load_from hf hblank flag ix hne disp
  let e : Fin u ↪ Fin (u + 2) :=
    (Fin.castAddEmb 2).trans (Equiv.swap (selected.castAdd 2) (Fin.natAdd u 0)).toEmbedding
  have he : e selected = Fin.natAdd u 0 := by simp [e]
  refine ⟨u, Q, hQ, tm.extendTapes e, c, ?_⟩
  intro host a t source target time hchild
  let tag := [active a, false, answer a] ++ word a
  let cfg := TwoWordInput.ready flag ix host tag []
  let budget := 2 * (word a).length + 8 + t
  have hraw : cfg.workTapes flag = tapeOfList tag := by
    simp [cfg, TwoWordInput.ready, TwoWordInput.words, wordsCfg]
  have hrun : disp.HaltsWithin budget (cfg.withState (some disp.toPTM.initial)) ∧
      (disp.AcceptsWithin budget (cfg.withState (some disp.toPTM.initial)) ↔
        if active a then child.AcceptsWithin t target else answer a = true) := by
    cases h : active a with
    | false =>
      have h₀ := constant_spec flag ix hne family cfg false (answer a) (word a)
        (by simpa only [tag, h] using hraw) rfl rfl
      have hb : 3 ≤ budget := by dsimp [budget]; omega
      exact ⟨h₀.1.mono hb, ⟨fun ha => h₀.2.mp (ha.of_halted_stepCoins h₀.1),
        fun hv => (h₀.2.mpr hv).mono hb⟩⟩
    | true =>
      have hr : cfg.workTapes ix = tapeOfList [] := by
        simp [cfg, TwoWordInput.ready, TwoWordInput.words, wordsCfg, hne.symm]
      have hv : viewCfg Fin.castSuccEmb ((copied flag ix (word a) cfg).withState
          (some child.toPTM.initial)) = target := copied_view src child host tag (word a)
      have hh := (child.haltsWithin_extendTapes_iff Fin.castSuccEmb t _).2 (hv ▸ hchild h)
      have hs := query_spec flag ix hne family cfg false (answer a) (word a) t
        (by simpa only [tag, h] using hraw) rfl hr rfl rfl hh
      exact ⟨hs.1, hs.2.trans ((child.acceptsWithin_extendTapes_iff Fin.castSuccEmb t _).trans
        (hv ▸ Iff.rfl))⟩
  obtain ⟨hh, ha⟩ := ht host a 0 (Nat.zero_le _) budget hrun.1
  have hclock : 0 + c * (T a + 1) + 8 + budget = time := by dsimp [time, budget]; omega
  rw [hclock] at hh ha
  have hv := work_view selected tm e he host (enc a)
  exact ⟨(tm.haltsWithin_extendTapes_iff e time _).2 (hv ▸ hh),
    ((tm.acceptsWithin_extendTapes_iff e time _).trans (hv ▸ Iff.rfl)).trans (ha.trans hrun.2)⟩

end Turing.MultiTapeATM.GuardedWord
