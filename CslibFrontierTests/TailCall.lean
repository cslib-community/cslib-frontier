/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TailCall
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg

open Turing Turing.MultiTapeTM Turing.MultiTapeATM

namespace TailCallTest

-- A two-state loop tail-calls itself once per symbol of an arbitrary physical work word.
private noncomputable def body : MultiTapeATM 1 Bool Bool := ofTMs (fun _ =>
  ofTr false fun _ _ w => if (w 0).isSome then
    ⟨0, fun _ => (none, 1), none, some true⟩ else
    ⟨0, fun _ => (none, 0), some true, none⟩) (fun _ => false)

private def cfg (word : List Bool) (pos : ℕ) (s : Option Bool) (out : List Bool := []) :
    Cfg 1 Bool Bool [] := ⟨s, 0, fun _ => tapeOfList word, fun _ => pos, out⟩

private theorem step (word : List Bool) (pos : ℕ) (b : Bool) :
    body.next b (cfg word pos (some false)) =
      if pos < word.length then cfg word (pos + 1) (some true)
      else cfg word pos none [true] := by
  rw [body, next_ofTMs, MultiTapeTM.step_of_state rfl]
  by_cases h : pos < word.length <;>
    apply Cfg.ext <;>
    simp [cfg, tr_ofTr, Cfg.workTapeSymbols, tapeOfList_ofNat, h, Action.apply]

example (word : List Bool) :
    (TailCall.machine body id).HaltsWithin (2 * word.length + 2) (cfg word 0 (some false)) ∧
      (TailCall.machine body id).AcceptsWithin (2 * word.length + 2) (cfg word 0 (some false)) := by
  let atm := TailCall.machine body id
  have aux (n pos : ℕ) (hp : pos + n = word.length) :
      atm.HaltsWithin (2 * n + 2) (cfg word pos (some false)) ∧
        atm.AcceptsWithin (2 * n + 2) (cfg word pos (some false)) := by
    induction n generalizing pos with
    | zero =>
      have hz : pos = word.length := by omega
      have hs : TailCall.Segment body id (fun _ => False) (fun _ => True) 1
          (cfg word pos (some false)) True := by
        apply TailCall.Segment.iff (TailCall.Segment.step rfl rfl (fun _ => True) ?_)
          (by change (if false then _ else _) ↔ _; simp)
        intro b
        rw [step, ite_eq_right (by omega)]
        exact (TailCall.Segment.halt (by rfl)).iff (by simp [cfg])
      obtain ⟨hh, ha⟩ := hs.run body id (t := 0) (fun _ h => h.elim)
      exact ⟨hh, ha.mpr trivial⟩
    | succ n ih =>
      have hn : pos < word.length := by omega
      let good := fun z => z = cfg word (pos + 1) (some false)
      have hs : TailCall.Segment body id good (fun _ => True) 1
          (cfg word pos (some false)) True := by
        apply TailCall.Segment.iff (TailCall.Segment.step rfl rfl (fun _ => True) ?_)
          (by change (if false then _ else _) ↔ _; simp)
        intro b
        rw [step, ite_eq_left hn]
        apply TailCall.Segment.call rfl rfl
        rfl
      obtain ⟨hh, ha⟩ := hs.run body id (t := 2 * n + 2) (fun z hz => by
        subst z
        have h := ih (pos + 1) (by omega)
        exact ⟨h.1, iff_true_intro h.2⟩)
      have ht : 1 + 1 + (2 * n + 2) = 2 * (n + 1) + 2 := by omega
      exact ht ▸ ⟨hh, ha.mpr trivial⟩
  exact aux word.length 0 (by omega)

end TailCallTest
