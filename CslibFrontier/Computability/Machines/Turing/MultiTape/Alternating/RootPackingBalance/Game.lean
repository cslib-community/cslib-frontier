/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootPackingBalance.Initialize

/-!
# Executing a quantified root request on one choice tape

A finite branch machine consumes the public schedule and a complete play of a fixed length. The
quantifier machine preserves the public prefix on every branch. A common time bound for all full
plays gives a uniform clock for the composed alternating machine.
-/

public section

namespace Turing.MultiTapeATM.RootPackingBalance.Game

open MultiTapeTM QuantifiedWord RootBalanceRequest

/-- All choices are played before entering the terminal at the end of the same physical tape. -/
theorem compile {U : ℕ} {Q : Type} (leaf : MultiTapeATM U Bool Q) (src : Fin U)
    (value : Input → Prop) (flags : Public → List Bool) (clock : Input → ℕ) (bound : Public → ℕ)
    (h : ∀ (input : List Bool) (x : Input),
      let start := WordGameLeaf.config src (some leaf.toPTM.initial)
        (encInput x) (encInput x).length
        (TerminalLayout.blank U input)
      leaf.HaltsWithin (clock x) start ∧ (leaf.AcceptsWithin (clock x) start ↔ value x))
    (hc : ∀ (p : Public) (word : List Bool), word.length = (flags p).length →
      clock (p, word) ≤ bound p) (input : List Bool) (p : Public) :
    let pre := frame (encPublic p)
    let atm := machine leaf src
    let time := bound p + 2 * (flags p).length + 1
    let start := WordGameLeaf.config src (some atm.toPTM.initial) (pre ++ flags p) pre.length
      (TerminalLayout.blank U input)
    atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
      plays (fun word => value (p, word)) [] (flags p)) := by
  let pre := frame (encPublic p)
  let v := fun word : List Bool => value (p, word.drop pre.length)
  obtain ⟨halt, acc⟩ := spec leaf src (bound p) (TerminalLayout.blank U input) v pre (flags p) (by
    intro suffix hlen
    let x : Input := (p, suffix)
    obtain ⟨ht, ha⟩ := h input x
    have he : encInput x = pre ++ suffix := rfl
    have hv : v (pre ++ suffix) = value x := by simp [v, x]
    dsimp only
    rw [hv, ← he]
    exact ⟨ht.mono (hc p suffix hlen), ⟨fun hacc => ha.mp (hacc.of_halted_stepCoins ht),
      fun hx => (ha.mpr hx).mono (hc p suffix hlen)⟩⟩)
  dsimp only
  rw [QuantifiedWord.machine_initial]
  refine ⟨halt, acc.trans ?_⟩
  simpa only [List.append_nil, v, List.drop_left] using plays_append_prefix v pre [] (flags p)

end Turing.MultiTapeATM.RootPackingBalance.Game
