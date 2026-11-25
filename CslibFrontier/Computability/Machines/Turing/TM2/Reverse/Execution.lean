/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.TM2.Reverse.Correct
public import CslibFrontier.Computability.Machines.Turing.TM2.Simulation

/-!
# Whole-run correspondence before cleanup

The compiler executes exactly one source transition per TM2 transition until the first halting
source configuration. Its next transition enters cleanup. These statements include the final
source action, which may write, move heads and emit a bit while halting.

## Main results

* `Turing.MultiTapeTM.ToTM2.iterate_encode`: correspondence of every source execution prefix.
* `Turing.MultiTapeTM.ToTM2.prefixEvals`: the same correspondence with Mathlib's partial clock.
-/

public section

namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type} [Fintype State]

private theorem stepTotal_encode (tm : MultiTapeTM k Bool State) (d : Data k State)
    {q : State} (hq : d.state = some q) :
    TM2.stepTotal (program tm.q₀ tm.tr) (encode d) = encode (Data.totalStep tm d) :=
  Option.some.inj (step_encode tm d hq)

theorem stepTotal_encode_halt (tm : MultiTapeTM k Bool State) (d : Data k State)
    (hq : d.state = none) :
    TM2.stepTotal (program tm.q₀ tm.tr) (encode d) =
      ⟨some .clean, control d d.input.right.head? false, store d⟩ :=
  Option.some.inj (step_encode_halt tm d hq)

private theorem iterate_encode_both (tm : MultiTapeTM k Bool State) (input : List Bool) {t : ℕ}
    (ht : tm.HaltsAt (tm.initCfg input) t) {i : ℕ} (hi : i ≤ t) :
    (TM2.stepTotal (program tm.q₀ tm.tr))^[i] (initList (machine tm.q₀ tm.tr) input) =
      encode (Data.run tm input i) ∧
    (fun c => c.bind (machine tm.q₀ tm.tr).step)^[i]
      (some (initList (machine tm.q₀ tm.tr) input)) = some (encode (Data.run tm input i)) := by
  induction i with
  | zero =>
    rw [Data.run_zero]
    exact ⟨(encode_init tm input).symm, congrArg some (encode_init tm input).symm⟩
  | succ i ih =>
    obtain ⟨ih₁, ih₂⟩ := ih (by omega)
    have hn : (Data.run tm input i).state ≠ none := by
      rw [Data.state_run]
      exact ht.not_halted (by omega)
    cases hq : (Data.run tm input i).state with
    | none => exact False.elim (hn hq)
    | some q =>
      refine ⟨(Function.iterate_succ_apply' _ i _).trans ?_, ?_⟩
      · rw [ih₁, stepTotal_encode tm _ hq, Data.run_succ]
      · rw [Function.iterate_succ_apply', ih₂, Data.run_succ]
        exact step_encode tm _ hq

/-- Every source prefix through the first halted configuration is reproduced exactly. -/
theorem iterate_encode (tm : MultiTapeTM k Bool State) (input : List Bool) {t : ℕ}
    (ht : tm.HaltsAt (tm.initCfg input) t) {i : ℕ} (hi : i ≤ t) :
    (TM2.stepTotal (program tm.q₀ tm.tr))^[i] (initList (machine tm.q₀ tm.tr) input) =
      encode (Data.run tm input i) :=
  (iterate_encode_both tm input ht hi).1

/-- The partial clock retains a successor throughout each source execution prefix. -/
private theorem partial_iterate_encode (tm : MultiTapeTM k Bool State) (input : List Bool)
    {t : ℕ} (ht : tm.HaltsAt (tm.initCfg input) t) {i : ℕ} (hi : i ≤ t) :
    (fun c => c.bind (machine tm.q₀ tm.tr).step)^[i]
      (some (initList (machine tm.q₀ tm.tr) input)) = some (encode (Data.run tm input i)) :=
  (iterate_encode_both tm input ht hi).2

/-- Mathlib's partial execution reaches each source prefix in exactly that many transitions. -/
def prefixEvals (tm : MultiTapeTM k Bool State) (input : List Bool) {t : ℕ}
    (ht : tm.HaltsAt (tm.initCfg input) t) {i : ℕ} (hi : i ≤ t) :
    StateTransition.EvalsToInTime (machine tm.q₀ tm.tr).step
      (initList (machine tm.q₀ tm.tr) input) (some (encode (Data.run tm input i))) i :=
  ⟨⟨i, partial_iterate_encode tm input ht hi⟩, le_rfl⟩

end

end Turing.MultiTapeTM.ToTM2
