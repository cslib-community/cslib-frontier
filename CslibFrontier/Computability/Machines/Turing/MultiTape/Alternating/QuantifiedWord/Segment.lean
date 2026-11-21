/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TailCall

/-!
# Physical quantified words inside a recursive segment

The flag player writes its chosen bits on the work tape in the same state space as a surrounding
controller. Once the flags are exhausted, the terminal can issue a genuine tail call. Every move
of the quantified prefix is charged before entering its terminal.
-/

public section

namespace Turing.MultiTapeATM.QuantifiedWord

open WordGameLeaf (config)

variable {k : ℕ} {S H : Type} (leaf : MultiTapeATM k Bool S) (tape : Fin k)
  {host : MultiTapeATM k Bool H} (sim : StateSimulation (machine leaf tape) host)
  (mark : H → Bool) {input : List Bool} (ready meaning : Cfg k Bool H input → Prop)

/-- Play eager existential or universal fields inside a cyclic controller. Each terminal
derivation starts with the completed word at its right end, in the same surrounding storage. -/
theorem segment (t : ℕ) (storage : Cfg k Bool Unit input) (value : List Bool → Prop)
    (pre players : List Bool)
    (hd : mark (sim.stateMap .dispatch) = false)
    (hc : ∀ p, mark (sim.stateMap (.choose p)) = false)
    (h : ∀ suffix : List Bool, suffix.length = players.length →
      let word := pre ++ suffix
      let cfg := config tape (some (.leaf leaf.toPTM.initial)) word word.length storage
      TailCall.Segment host mark ready meaning t (cfg.mapState (Option.map sim.stateMap))
        (value word)) :
    let cfg := config tape (some .dispatch) (pre ++ players) pre.length storage
    TailCall.Segment host mark ready meaning (t + 2 * players.length + 1)
      (cfg.mapState (Option.map sim.stateMap)) (plays value pre players) := by
  dsimp only
  induction players generalizing pre with
  | nil =>
    have ht := h [] rfl
    simp only [List.append_nil] at ht ⊢
    simp only [List.length_nil, Nat.mul_zero, Nat.add_zero, plays]
    refine TailCall.Segment.deterministic host mark rfl hd ?_ ht
    intro b
    rw [sim.next_eq, next_end]
    rfl
  | cons p tail ih =>
    have hbranch (bit : Bool) := ih (pre ++ [bit]) (fun suffix hs => by
      simpa only [List.append_assoc, List.singleton_append] using
        h (bit :: suffix) (by simp [hs]))
    rw [show t + 2 * (p :: tail).length + 1 = (t + 2 * tail.length + 1) + 1 + 1 by
      simp; omega]
    apply TailCall.Segment.deterministic host mark rfl hd
      (fun b => (sim.next_eq _ b).trans (congrArg (Cfg.mapState (Option.map sim.stateMap))
        (next_dispatch leaf tape pre tail p b storage)))
    refine (TailCall.Segment.step (s := sim.stateMap (.choose p)) rfl (hc p)
      (fun bit => plays value (pre ++ [bit]) tail) ?_).iff ?_
    · intro bit
      rw [sim.next_eq, next_choose]
      exact hbranch bit
    · rw [sim.universal_eq, universal_choose, plays]

end Turing.MultiTapeATM.QuantifiedWord
