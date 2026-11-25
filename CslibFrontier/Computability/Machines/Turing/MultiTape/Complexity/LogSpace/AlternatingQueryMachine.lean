/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine

/-!
# Alternating query machines

An alternating query machine is a nondeterministic query machine
(`Turing.NondeterministicQueryMachine`) whose states also name the player of the binary choice made
at them: the existential player or the universal player. As there, the abstract state is data to be
kept on work tapes rather than native finite control, the input is read by position, with `none`
past its end, and halted states self-loop.

Acceptance (`Turing.AlternatingQueryMachine.AcceptsFrom`) is the least fixed point of the usual
labelling [Chandra, Kozen and Stockmeyer, Section 2][ChandraKozenStockmeyer1981]: a halted
accepting state accepts, a live existential state accepts when some choice leads to an accepting
state, and a live universal state when every choice does. As for
`Turing.MultiTapeATM.Accepts` and `Turing.MultiTapeATM.WordGame.Wins`, an infinite play never
helps a state accept. When no state is universal, this is the existential acceptance of the
underlying nondeterministic query machine
(`Turing.AlternatingQueryMachine.accepts_iff_of_universal_eq_false`).

This model is the abstract side of the inclusion `DTIME(2 ^ O(s)) ⊆ ASPACE(s)` of
[Chandra, Kozen and Stockmeyer, Theorem 3.4][ChandraKozenStockmeyer1981]: the circuit-value game on
the tableau of a machine is an alternating query machine with states of `O(log n + log T)` bits
(`Cslib.Circuits.Boolean.Tableau.ValueGame.localMachine`). An alternating query machine is compiled
into an alternating Turing machine that keeps the state on its work tapes by
`Turing.AlternatingQueryMachine.exists_decidesInSpace`.

## Main definitions

* `Turing.AlternatingQueryMachine`: the binary-choice alternating query model.
* `Turing.AlternatingQueryMachine.AcceptsFrom`: the states from which the machine accepts.
* `Turing.AlternatingQueryMachine.Accepts`: acceptance from the initial state.

## Main results

* `Turing.AlternatingQueryMachine.acceptsFrom_iff`: the labelling equation at one state.
* `Turing.AlternatingQueryMachine.accepts_iff_of_universal_eq_false`: with no universal state,
  acceptance is existential acceptance of the underlying nondeterministic query machine.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
-/

@[expose] public section

namespace Turing

/-- **An alternating query machine**: a nondeterministic query machine whose states also name the
player of the binary choice made at them, the universal player when `universal s = true` and the
existential player otherwise. -/
structure AlternatingQueryMachine (σ : Type*) extends NondeterministicQueryMachine σ where
  /-- Whether the choice at a state is made by the universal player. -/
  universal : σ → Bool

namespace AlternatingQueryMachine

variable {σ : Type*} (M : AlternatingQueryMachine σ) (input : List Bool)

/-- **The states from which the machine accepts**, as a least fixed point: a halted accepting
state; a live existential state some choice of which leads to an accepting state; and a live
universal state every choice of which does. -/
inductive AcceptsFrom : σ → Prop
  | halt {s : σ} : M.halted s = true → M.accept s = true → AcceptsFrom s
  | existsChoice {s : σ} (b : Bool) : M.halted s = false → M.universal s = false →
      AcceptsFrom (M.step input s b) → AcceptsFrom s
  | forallChoice {s : σ} : M.halted s = false → M.universal s = true →
      (∀ b, AcceptsFrom (M.step input s b)) → AcceptsFrom s

/-- The machine accepts the input when it accepts from its initial state. -/
def Accepts : Prop := M.AcceptsFrom input M.init

/-- **The labelling equation**: a halted state accepts when it is accepting; a live state accepts
when some choice (existential state) or every choice (universal state) leads to an accepting
state. -/
theorem acceptsFrom_iff {s : σ} : M.AcceptsFrom input s ↔
    if M.halted s then M.accept s = true
    else if M.universal s then ∀ b, M.AcceptsFrom input (M.step input s b)
    else ∃ b, M.AcceptsFrom input (M.step input s b) := by
  constructor
  · rintro (⟨hh, ha⟩ | ⟨b, hh, hu, h⟩ | ⟨hh, hu, h⟩)
    · simp [hh, ha]
    · simp only [hh, hu, Bool.false_eq_true, ↓reduceIte]
      exact ⟨b, h⟩
    · simp [hh, hu, h]
  · cases hh : M.halted s
    · cases hu : M.universal s <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact fun ⟨b, hb⟩ => .existsChoice b hh hu hb
      · exact .forallChoice hh hu
    · simp only [↓reduceIte]
      exact .halt hh

/-- **With no universal state, alternating acceptance is nondeterministic acceptance**: if every
state is existential, the machine accepts exactly when some finite sequence of choices reaches a
halted accepting state (`Turing.NondeterministicQueryMachine.Accepts`). -/
theorem accepts_iff_of_universal_eq_false (h : ∀ s, M.universal s = false) :
    M.Accepts input ↔ M.toNondeterministicQueryMachine.Accepts input := by
  have hto : ∀ s, M.AcceptsFrom input s → ∃ choices : List Bool,
      M.halted (M.replay input choices s) = true ∧ M.accept (M.replay input choices s) = true := by
    intro s hs
    induction hs with
    | halt hh ha => exact ⟨[], hh, ha⟩
    | existsChoice b _ _ _ ih =>
      obtain ⟨choices, hc⟩ := ih
      exact ⟨b :: choices, hc⟩
    | @forallChoice s _ hu _ _ => exact absurd hu (by simp [h s])
  have hof : ∀ (choices : List Bool) (s : σ), M.halted (M.replay input choices s) = true →
      M.accept (M.replay input choices s) = true → M.AcceptsFrom input s := by
    intro choices
    induction choices with
    | nil => exact fun s hh ha => .halt hh ha
    | cons b choices ih =>
      intro s hh ha
      cases hs : M.halted s
      · exact .existsChoice b hs (h s) (ih _ hh ha)
      · rw [M.replay_of_halted input hs] at hh ha
        exact .halt hh ha
  exact ⟨fun hs => hto _ hs, fun ⟨choices, hh, ha⟩ => hof choices _ hh ha⟩

end AlternatingQueryMachine

end Turing
