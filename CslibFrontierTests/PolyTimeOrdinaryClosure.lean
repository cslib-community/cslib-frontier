/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Init
public import CslibFrontier.Tactic.PolyTime
public import CslibFrontier.Tactic.Negligible
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree
import Mathlib.Basic.NNReal.Basic

/-! Ordinary automation after deleting the derived tidy calculus: order-sensitive captured
folds, independent degree certificates and unary negligible parameters. -/

set_option linter.privateModule false

namespace CslibFrontierTests.PolyTimeOrdinaryClosure

open Cslib Turing.MultiTapeTM
open scoped NNReal

private def tagged (p : List Bool × List Bool) : List Bool :=
  p.2.foldl (fun state bit => p.1 ++ bit :: state) []

private theorem tagged_growth (p : List Bool × List Bool) (state : List Bool) (bit : Bool) :
    (p.1 ++ bit :: state).length ≤ state.length + (p.1.length + 1) := by
  simp [Nat.add_left_comm]

example : ComputableInPolyTime tagged (encPair encBits encBits) encBits := by
  have hpoly : PolyBounded (fun p : List Bool × List Bool =>
      (encPair encBits encBits p).length) (fun p => p.1.length + 1) :=
    ComputableInPolyTime.polyBounded (input := encPair encBits encBits) (by fun_prop)
  have hgrowth := tagged_growth
  unfold tagged
  polytime

example : tagged ([true], [false, true]) = [true, true, true, false] := by decide

-- Output degree seven does not become the runtime degree zero when lifting to plain search.
example {α : Type} {input : α ↪ List Bool} (f : α → List Bool)
    (hf : ComputableInDegree f input encBits 0 7) :
    ComputableInPolyTime (fun x => true :: f x ++ [false]) input encBits := by
  have hplain := hf.computableInPolyTime
  fail_if_success (clear hf hplain; polytime)
  polytime

example {α : Type} {input : α ↪ List Bool} (f : α → List Bool) :
    ComputableInPolyTime (fun x => true :: f x) input encBits →
      ComputableInPolyTime f input encBits := by
  intro h
  exact ComputableInPolyTime.bitsTail.comp h

example (f : ℕ → ℕ) (hf : ComputableInPolyTime f encUnary encUnary)
    (ε : ℕ → ℝ≥0) (hε : Cslib.Crypto.Negligible ε) :
    Cslib.Crypto.Negligible (fun n => (f n : ℝ≥0) * ε n) := by
  negligible

-- Canonical ordinary operations remain exported; only actually removed names are forbidden.
run_cmd do
  let env ← Lean.getEnv
  for name in [`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableInPolyTime.of_tidy,
      `Turing.MultiTapeTM.ComputableInPolyTime.tidy] do
    if env.contains name then throwError "removed derived calculus survives: {name}"
  for name in [`Turing.MultiTapeTM.ComputableInPolyTime.finite_cases,
      `Turing.MultiTapeTM.ComputableInPolyTime.pi_apply,
      `Turing.MultiTapeTM.ComputableInPolyTime.optionElimWithInput,
      `Turing.MultiTapeTM.ComputableInPolyTime.iterate_spec,
      `Turing.MultiTapeTM.ComputableInPolyTime.foldlWith_spec] do
    unless env.contains name do throwError "ordinary provider missing: {name}"

end CslibFrontierTests.PolyTimeOrdinaryClosure
