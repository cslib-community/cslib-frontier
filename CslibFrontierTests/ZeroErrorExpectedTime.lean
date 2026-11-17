/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Classes.Time.ZeroError

/-! A checked instance of zero-error expected time: the fair-coin table `acceptAll`, which emits
`true` and halts at its first step, decides the full problem with zero error in expected time `1`,
so the hypotheses of `Cslib.Complexity.ZTIME_pow_subset_ZPP` are satisfiable. -/

set_option linter.privateModule false

namespace CslibFrontierTests.ZeroErrorExpectedTime

open Cslib Turing Turing.MultiTapePTM Turing.MultiTapeTM

/-- Every run of `acceptAll` has halted with output `[true]` after one step. -/
theorem acceptAll_halted (input : List Bool) :
    ∀ final ∈ (ProbComp.eval (acceptAll.runClosedConfigFrom 1
      (acceptAll.initialConfig input))).support,
      final.tapes.state = none ∧ final.tapes.output = [true] := by
  intro final hfinal
  rw [eval_runClosedConfigFrom_eq_map_coins, PMF.mem_support_map_iff] at hfinal
  obtain ⟨coins, hcoins, rfl⟩ := hfinal
  obtain ⟨b, rfl⟩ : ∃ b, coins = [b] := by
    match coins, BitString.mem_support_uniformList_iff.mp hcoins with
    | [b], _ => exact ⟨b, rfl⟩
  have hstep : (acceptAll.withCoin b).toTM.step (Cfg.init acceptAll.initial input) =
      ⟨none, 1, fun _ _ => none, fun _ => 0, [true]⟩ := by
    rw [MultiTapeTM.step_of_state rfl, MultiTapeMachine.toTM, MultiTapeTM.tr_ofTr]
    exact Cfg.ext rfl (by simp [acceptAll, MultiTapeMachine.Action.emptyOracleEquiv,
      withCoin]) (funext fun i => i.elim0) (funext fun i => i.elim0) rfl
  rw [tapes_runClosedConfigFromCoins]
  change (acceptAll.stepCoins [b] (Cfg.init acceptAll.initial input)).state = none ∧
    (acceptAll.stepCoins [b] (Cfg.init acceptAll.initial input)).output = [true]
  rw [stepCoins_cons, hstep]
  exact ⟨rfl, rfl⟩

/-- `acceptAll` decides the full problem with zero error in expected time `1`. -/
theorem acceptAll_decidesWithZeroErrorInExpectedTime :
    acceptAll.DecidesWithZeroErrorInExpectedTime encBits Set.univ
      fun a => 1 * (encBits a).length ^ 0 + 0 :=
  .of_halted fun a final hfinal => by
    simp only [pow_zero, mul_one, add_zero] at hfinal
    have hind : MultiTapeTM.indicator (Set.univ : Set (List Bool)) a = true := by
      simp [MultiTapeTM.indicator]
    rw [hind]
    exact acceptAll_halted _ final hfinal

example : (Set.univ : Set (List Bool)) ∈ Complexity.ZTIME encBits (· ^ 0) :=
  ⟨1, 0, 0, Unit, inferInstance, acceptAll, acceptAll_decidesWithZeroErrorInExpectedTime⟩

example : (Set.univ : Set (List Bool)) ∈ Complexity.ZPP encBits :=
  Complexity.ZTIME_pow_subset_ZPP 0
    ⟨1, 0, 0, Unit, inferInstance, acceptAll, acceptAll_decidesWithZeroErrorInExpectedTime⟩

end CslibFrontierTests.ZeroErrorExpectedTime
