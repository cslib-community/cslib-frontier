/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.GuardedWord
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO

open Turing MultiTapeTM MultiTapeATM

-- A disabled request returns either constant on a nonempty host word. No time bound for the
-- supplied continuation is assumed, including when its timer is zero.
example {K : ℕ} {S : Type} [Finite S] (src : Fin K) (child : MultiTapeATM K Bool S)
    (answer : Bool) :
    ∃ (u : ℕ) (Q : Type) (_ : Finite Q) (run : MultiTapeATM (u + 2) Bool Q) (C : ℕ),
      ∀ host : List Bool,
        let start := (WorkTapePredicate.config host [true, false]).withState
          (some run.toPTM.initial)
        run.HaltsWithin (C * 3 + 16) start ∧ (run.AcceptsWithin (C * 3 + 16) start ↔
          answer = true) := by
  have hf : ComputableInDegree (fun _ : List Bool => [false, false, answer]) encBits encBits 1 1 :=
    (ComputableInDegree.const (encMid := encBits) [false, false, answer]).mono
  obtain ⟨u, Q, hQ, run, C, h⟩ := GuardedWord.exists_guarded_runner src child (fun _ => false)
    (fun _ => answer) (fun _ => []) (fun a : List Bool => (encBits a).length) hf.inO_one
  refine ⟨u, Q, hQ, run, C, fun host => ?_⟩
  simpa using h host [true, false] 0 (by simp)
