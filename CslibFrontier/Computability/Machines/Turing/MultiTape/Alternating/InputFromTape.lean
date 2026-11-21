/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.GuessVerify
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape

/-!
# Running an alternating machine on a virtual read-only input

A work tape holds the source word and a second tape marks its left boundary. The two heads
move together and clamp at either end exactly as the original input head does. Every
transition preserves its player and costs one physical step.
-/

public section

namespace Turing.MultiTapeATM

open MultiTapeTM

variable {k : ℕ} {S : Type} {input : List Bool}

/-- Redirect the two native alternating moves through the upstream clamped-input compiler. -/
@[expose] noncomputable def inputFromTape (atm : MultiTapeATM k Bool S) :
    MultiTapeATM (k + 2) Bool S :=
  ofTMs (fun b => (atm.toPTM.withCoin b).toTM.inputFromTape) atm.universal

/-- The configuration embedding commutes with either native move. -/
theorem next_inCfg (atm : MultiTapeATM k Bool S) (b mark : Bool) (outer : List Bool)
    (c : Cfg k Bool S input) :
    atm.inputFromTape.next b (inCfg mark c outer) = inCfg mark (atm.next b c) outer := by
  rw [inputFromTape, next_ofTMs]
  exact step_iff.mp (((atm.toPTM.withCoin b).toTM.inCfgHom mark outer).map_rel (step_iff.mpr rfl))

/-- The virtual source has the same bounded accepting computation tree. -/
theorem acceptsWithin_inCfg_iff (atm : MultiTapeATM k Bool S) (mark : Bool) (outer : List Bool)
    (n : ℕ) (c : Cfg k Bool S input) :
    atm.inputFromTape.AcceptsWithin n (inCfg mark c outer) ↔ atm.AcceptsWithin n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    cases hs : c.state with
    | none => simp [AcceptsWithin, inCfg, hs]
    | some q =>
      have he : (inCfg mark c outer).state = some q := hs
      simp only [AcceptsWithin, he, hs]
      change (if atm.universal q then ∀ b, _ else ∃ b, _) ↔ _
      simp only [next_inCfg, ih]

/-- The virtual source preserves all-branch halting, including rejecting branches. -/
theorem haltsWithin_inCfg_iff (atm : MultiTapeATM k Bool S) (mark : Bool) (outer : List Bool)
    (n : ℕ) (c : Cfg k Bool S input) :
    atm.inputFromTape.HaltsWithin n (inCfg mark c outer) ↔ atm.HaltsWithin n c := by
  induction n generalizing c with
  | zero => simp [haltsWithin_zero, inCfg]
  | succ n ih => simp only [haltsWithin_succ, next_inCfg, ih]

end Turing.MultiTapeATM
