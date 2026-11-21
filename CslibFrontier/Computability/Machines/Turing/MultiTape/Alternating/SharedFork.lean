/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.StateSimulation

/-!
# One universal choice with shared tapes

Both successor machines inherit exactly the same work tapes, positions and output. The universal
step costs one unit in addition to a common bound on the two successor computations.
-/

public section

namespace Turing.MultiTapeATM.SharedFork

open MultiTapeTM

variable {k : ℕ} {S : Bool → Type} (family : (b : Bool) → MultiTapeATM k Bool (S b))

private abbrev State (S : Bool → Type) := Option ((b : Bool) × S b)

private def tag (b : Bool) (q : S b) : State S := some ⟨b, q⟩

private noncomputable def tr (coin : Bool) :
    State S → Option Bool → (Fin k → Option Bool) → Turing.Action k Bool (State S)
  | none, _, _ => ⟨0, fun _ => (none, 0), none, some (tag coin (family coin).toPTM.initial)⟩
  | some ⟨b, q⟩, inp, work =>
    let act := (family b).action q inp work coin
    {act with state := act.state.map (tag b)}

private def player : State S → Bool
  | none => true
  | some ⟨b, q⟩ => (family b).universal q

private noncomputable def atState (q : State S) : MultiTapeATM k Bool (State S) :=
  ofTMs (fun coin => MultiTapeTM.ofTr q (tr family coin)) (player family)

/-- The chosen child sees the whole unmodified configuration. -/
noncomputable def machine : MultiTapeATM k Bool (Option ((b : Bool) × S b)) :=
  atState family none

/-- Start directly in a selected child with the common state type of the fork. -/
noncomputable def selected (b : Bool) : MultiTapeATM k Bool (Option ((b : Bool) × S b)) :=
  atState family (tag b (family b).toPTM.initial)

private noncomputable def sim (q₀ : State S) (b : Bool) :
    StateSimulation (family b) (atState family q₀) where
  stateMap := tag b
  universal_eq _ := rfl
  next_eq c bit := by
    cases hs : c.state with
    | none => rw [next_of_halted _ (by simp [Cfg.mapState, hs]), next_of_halted _ hs]
    | some q =>
      have hstate : (c.mapState (Option.map (tag b))).state = some (tag b q) := by
        simp [Cfg.mapState, hs]
      rw [atState, next_ofTMs, MultiTapeTM.step_of_state hstate, next_of_state _ hs]
      simp only [MultiTapeTM.tr_ofTr, tag, tr]
      rfl

/-- Selecting a child in finite control preserves its entire computation at the same clock. -/
theorem selected_spec (b : Bool) {input : List Bool} (c : Cfg k Bool Unit input) (t : ℕ) :
    let alt := selected family b
    let initial := c.withState (some alt.toPTM.initial)
    let child := c.withState (some (family b).toPTM.initial)
    (alt.HaltsWithin t initial ↔ (family b).HaltsWithin t child) ∧
      (alt.AcceptsWithin t initial ↔ (family b).AcceptsWithin t child) :=
  let h := sim family (tag b (family b).toPTM.initial) b
  let child := c.withState (some (family b).toPTM.initial)
  ⟨h.haltsWithin_iff t child, h.acceptsWithin_iff t child⟩

private theorem next_start {input : List Bool} (b : Bool) (c : Cfg k Bool Unit input) :
    (machine family).next b (c.withState (some (machine family).toPTM.initial)) =
      (c.withState (some (family b).toPTM.initial)).mapState (Option.map (tag b)) := by
  rw [machine, atState, next_ofTMs, MultiTapeTM.step_of_state rfl]
  apply Cfg.ext <;> simp [MultiTapeTM.tr_ofTr, tr, Cfg.withState, Cfg.mapState, Turing.Action.apply,
    moveInputPos_zero, ofTMs]

/-- All children halt by the common clock, and acceptance requires both child verdicts. -/
theorem spec {input : List Bool} (c : Cfg k Bool Unit input) (t : ℕ)
    (hh : ∀ b, (family b).HaltsWithin t (c.withState (some (family b).toPTM.initial))) :
    let atm := machine family
    let start := c.withState (some atm.toPTM.initial)
    atm.HaltsWithin (t + 1) start ∧ (atm.AcceptsWithin (t + 1) start ↔
      ∀ b, (family b).AcceptsWithin t (c.withState (some (family b).toPTM.initial))) := by
  dsimp only
  constructor
  · rw [haltsWithin_succ]
    intro b
    rw [next_start]
    exact ((sim family none b).haltsWithin_iff t _).2 (hh b)
  · rw [acceptsWithin_succ_of_universal _ rfl rfl]
    apply forall_congr'
    intro b
    rw [next_start]
    exact (sim family none b).acceptsWithin_iff t _

end Turing.MultiTapeATM.SharedFork
