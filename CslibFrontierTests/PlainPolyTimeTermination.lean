/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.IterateWhile
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! Ordinary termination client: an immediate probe and the nonempty trajectory `2 → 1 → 0`.
The returned state precedes the empty probe, so the second case returns `1`, not `0`.
The resource statement retains the `rounds + 1` factor covering initialization and finalization.
-/

-- This ordinary-import regression module exports no fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.PlainPolyTimeTermination

open Turing.MultiTapeTM

private def init (b : Bool) : ℕ := if b then 2 else 0
private def step (n : ℕ) : ℕ := n - 1
private def rounds (b : Bool) : ℕ := if b then 1 else 0

example : ∃ c d, ComputableInTimeAndSpace (fun b : Bool => if b then 1 else 0)
    encBool encUnary
    (fun b => c * ((if b then 1 else 0) + 1) * (2 + (encBool b).length + 1) ^ d)
    (fun b => c * (2 + (encBool b).length + 1) ^ d) := by
  have hinit : ComputableInPolyTime init encBool encUnary := .of_finite _
  have hstep : ComputableInPolyTime step encUnary encUnary :=
    ComputableInPolyTime.unary_sub' ComputableInPolyTime.id' (ComputableInPolyTime.const 1)
  have hfin : ComputableInPolyTime (id : ℕ → ℕ) encUnary encUnary := .id'
  have hl : ∀ b, ∀ n ≤ rounds b, (encUnary (step^[n] (init b))).length ≤ 2 := by
    intro b n hn
    cases b with
    | false =>
      have hn0 : n = 0 := by simpa [rounds] using hn
      subst n
      simp [init, encUnary_apply]
    | true =>
      have hn1 : n ≤ 1 := by simpa [rounds] using hn
      have hn01 : n = 0 ∨ n = 1 := by omega
      rcases hn01 with rfl | rfl <;>
        simp [init, step, encUnary_apply]
  have hne : ∀ b, ∀ n < rounds b, encUnary (step^[n + 1] (init b)) ≠ [] := by
    intro b n hn
    cases b with
    | false => simp [rounds] at hn
    | true =>
      have hn0 : n = 0 := by simpa [rounds] using hn
      subst n
      simp [init, step, encUnary_apply]
  have hnil : ∀ b, encUnary (step^[rounds b + 1] (init b)) = [] := by
    intro b
    cases b <;> simp [rounds, init, step, Function.iterate_succ_apply', encUnary_apply]
  obtain ⟨c, d, h⟩ := exists_computableInTimeAndSpace_iterateWhile hinit hstep hfin
    (r := rounds) (l := fun _ => 2) hl hne hnil
  have hout : (fun b : Bool => id (step^[rounds b] (init b))) =
      (fun b => if b then 1 else 0) := by
    funext b
    cases b <;> rfl
  rw [hout] at h
  exact ⟨c, d, h⟩

end CslibFrontierTests.PlainPolyTimeTermination
