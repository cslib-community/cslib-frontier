/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.GuessVerify

/-!
# Reusing one finite alternating controller for tail calls

A set of return states hands the current tapes and heads back to the entry state, preserving
all previously prepared arguments. Every other running state executes the original instruction.
A bounded local derivation checks a segment up to a true halt or a handover. Chaining such
segments adds their branch times and one transition per handover, using the same machine for
every runtime recursion depth.
-/

public section

namespace Turing.MultiTapeATM.TailCall

open MultiTapeTM

variable {k : ℕ} {S : Type} (body : MultiTapeATM k Bool S) (again : S → Bool)

/-- On a marked state, retain all tapes, heads and output while returning to the entry state. -/
@[expose] noncomputable def machine : MultiTapeATM k Bool S :=
  ofTMs (fun b => ofTr body.toPTM.initial fun s input work =>
    if again s then ⟨0, fun _ => (none, 0), none, some body.toPTM.initial⟩
    else body.action s input work b) body.universal

variable {input : List Bool}

/-- Configuration exposed to the next local segment. -/
@[expose] def restart (c : Cfg k Bool S input) : Cfg k Bool S input :=
  c.withState (some body.toPTM.initial)

private theorem next_again {c : Cfg k Bool S input} {s : S} (hs : c.state = some s)
    (ha : again s = true) (b : Bool) : (machine body again).next b c = restart body c := by
  rw [machine, next_ofTMs, MultiTapeTM.step_of_state hs]
  apply Cfg.ext <;> simp [tr_ofTr, ha, Action.apply, restart, Cfg.withState]

/-- Ordinary states take the same action as in the local segment. -/
theorem next_body {c : Cfg k Bool S input} {s : S} (hs : c.state = some s)
    (ha : again s = false) (b : Bool) : (machine body again).next b c = body.next b c := by
  rw [machine, next_ofTMs, MultiTapeTM.step_of_state hs, body.next_of_state hs]
  simp [tr_ofTr, ha]

/-- A derivation of at most the given number of local instructions. At a marked state the next
input satisfies `ready` and the value is the recursive specification `meaning`. -/
inductive Segment (ready meaning : Cfg k Bool S input → Prop) :
    ℕ → Cfg k Bool S input → Prop → Prop where
  | halt {n c} (hs : c.state = none) : Segment ready meaning n c (c.output = [true])
  | call {n c s} (hs : c.state = some s) (ha : again s = true)
      (hg : ready (restart body c)) : Segment ready meaning n c (meaning (restart body c))
  | step {n c s} (hs : c.state = some s) (ha : again s = false) (v : Bool → Prop)
      (children : ∀ b, Segment ready meaning n (body.next b c) (v b)) :
      Segment ready meaning (n + 1) c (if body.universal s then ∀ b, v b else ∃ b, v b)
  | iff {n c P Q} (h : Segment ready meaning n c P) (he : P ↔ Q) : Segment ready meaning n c Q

/-- Local evaluation with an actual recursive continuation. Along a branch its clock is
charged once regardless of how many universal or existential states occur in the segment. -/
theorem Segment.run {ready meaning : Cfg k Bool S input → Prop} {n t : ℕ} {c P}
    (h : Segment body again ready meaning n c P)
    (hrec : ∀ z, ready z → (machine body again).HaltsWithin t z ∧
      ((machine body again).AcceptsWithin t z ↔ meaning z)) :
    (machine body again).HaltsWithin (n + 1 + t) c ∧
      ((machine body again).AcceptsWithin (n + 1 + t) c ↔ P) := by
  let atm := machine body again
  induction h with
  | halt hs => exact ⟨haltsWithin_of_halted hs, atm.acceptsWithin_of_halted hs⟩
  | @call n c s hs ha hg =>
    obtain ⟨ht, hv⟩ := hrec _ hg
    have hn := next_again body again hs ha
    have hh : atm.HaltsWithin (t + 1) c :=
      (haltsWithin_succ).mpr fun b => (hn b).symm ▸ ht
    have he := (acceptsWithin_succ_of_next_eq (atm := atm) hn).trans hv
    have hb : t + 1 ≤ n + 1 + t := by omega
    exact ⟨hh.mono hb, ⟨fun h => he.mp (h.of_halted_stepCoins hh), fun h => (he.mpr h).mono hb⟩⟩
  | @step n c s hs ha v _ ih =>
    have hnext := next_body body again hs ha
    rw [show n + 1 + 1 + t = (n + 1 + t) + 1 by omega]
    refine ⟨haltsWithin_succ.mpr fun b => (hnext b).symm ▸ (ih b).1, ?_⟩
    cases hu : body.universal s with
    | false =>
      rw [atm.acceptsWithin_succ_of_existential hs hu]
      simpa only [atm, hnext, Bool.false_eq_true, ↓reduceIte] using exists_congr (fun b => (ih b).2)
    | true =>
      rw [atm.acceptsWithin_succ_of_universal hs hu]
      simpa only [atm, hnext, ↓reduceIte] using forall_congr' (fun b => (ih b).2)
  | iff _ he ih => exact ⟨ih.1, ih.2.trans he⟩

/-- One machine and the same tape count for an arbitrary list of runtime recursion levels.
The local witness at each level may change the encoded problem on the tapes before a handover. -/
theorem run_levels {α : Type*} (cost : α → ℕ) (baseTime : ℕ)
    (ready meaning : List α → Cfg k Bool S input → Prop)
    (base : ∀ c, ready [] c → (machine body again).HaltsWithin baseTime c ∧
      ((machine body again).AcceptsWithin baseTime c ↔ meaning [] c))
    (step : ∀ level levels c, ready (level :: levels) c →
      Segment body again (ready levels) (meaning levels) (cost level) c
        (meaning (level :: levels) c))
    (levels : List α) (c : Cfg k Bool S input) (hc : ready levels c) :
    let time := levels.foldr (fun l t => cost l + 1 + t) baseTime
    (machine body again).HaltsWithin time c ∧ ((machine body again).AcceptsWithin time c ↔
      meaning levels c) := by
  induction levels generalizing c with
  | nil => exact base c hc
  | cons l ls ih => exact (step l ls c hc).run body again ih

end Turing.MultiTapeATM.TailCall
