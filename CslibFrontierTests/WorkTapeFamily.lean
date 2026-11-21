/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.WorkTapeFamily

open Turing MultiTapeTM MultiTapeATM

private def scratch : Bool → ℕ | false => 0 | true => 3
private def Control : Bool → Type | false => Unit | true => Bool
private def entry : (b : Bool) → Control b | false => () | true => true
private instance (b : Bool) : Finite (Control b) := by
  cases b <;> dsimp [Control] <;> infer_instance

private noncomputable def runner (b : Bool) : MultiTapeATM (scratch b + 2) Bool (Control b) :=
  ofTMs (fun _ => ofTr (entry b) fun _ _ _ => ⟨0, fun _ => (none, 0), some b, none⟩)
    (fun _ => false)

-- One verifier originally had no private scratch, the other three tapes and a two-state control.
-- The common physical family returns their opposite verdicts on the original one-step clock.
example : ∃ (k : ℕ) (Q : Type) (_ : Finite Q) (family : Bool → MultiTapeATM (k + 2) Bool Q),
    ∀ (b : Bool) (host word : List Bool),
      let c := (WorkTapePredicate.config (k := k) host word).withState
        (some (family b).toPTM.initial)
      (family b).HaltsWithin 1 c ∧ ((family b).AcceptsWithin 1 c ↔ b = true) := by
  obtain ⟨k, Q, hQ, family, h⟩ := WorkTapeFamily.exists_family scratch Control runner
  refine ⟨k, Q, hQ, family, fun b host word => ?_⟩
  have ⟨ht, ha⟩ := h b host word 1
  let c := (WorkTapePredicate.config (k := scratch b) host word).withState
    (some (runner b).toPTM.initial)
  have hs (coin : Bool) : ((runner b).next coin c).state = none ∧
      ((runner b).next coin c).output = [b] := by
    rw [runner, next_ofTMs, step_of_state rfl]
    simp [tr_ofTr, Turing.Action.apply, c, WorkTapePredicate.config, tapesCfg, Cfg.withState]
  have hh : (runner b).HaltsWithin 1 c := by
    simp only [haltsWithin_succ, haltsWithin_zero]
    exact fun coin => (hs coin).1
  refine ⟨ht.mpr hh, ha.trans ?_⟩
  change (∃ coin, ((runner b).next coin c).state = none ∧
    ((runner b).next coin c).output = [true]) ↔ _
  simp only [fun coin => (hs coin).1, fun coin => (hs coin).2, true_and, List.cons.injEq,
    and_true, exists_const]
