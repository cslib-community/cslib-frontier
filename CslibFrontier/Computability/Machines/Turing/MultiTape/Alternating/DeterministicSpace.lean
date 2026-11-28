/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating
public import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.BitGame
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunPropFinite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.ListSlice
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.AcceptCount
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ReplayVerdict
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.StateFlags

/-!
# Alternating time within deterministic space

A position of the game of an alternating machine on an input is the list of moves made so far,
latest first; the machine is then in the configuration reached by the moves
(`Turing.MultiTapeATM.cfgAfter`). The position is a leaf when that configuration has halted, the
existential player moves when its state is existential, and the existential player wins a leaf
when the output is `[true]`. With `n` moves of fuel this single-bit game
(`Cslib.Complexity.BitGame.value`) is acceptance within `n` moves
(`Turing.MultiTapeATM.gameValue_eq_true_iff`) [Chandra, Kozen and Stockmeyer, Theorem 3.2]
[ChandraKozenStockmeyer1981].

Each of the three tests replays the moves on the table: `Turing.MultiTapePTM.flag` reads off the
state reached, and `Turing.MultiTapePTM.computableInO_decide_runClosedCoins` tests the output.
Both take space linear in the input and the moves, so the depth-first evaluator of single-bit games
(`Turing.MultiTapeTM.ComputableInSpace.bitGame_value`) decides acceptance within `t` moves in space
`O(n + t)` on inputs of length `n`, without computing `t`
(`Turing.MultiTapeATM.computableInSpace_gameValue`).

## Main definitions

* `Turing.MultiTapeATM.cfgAfter`: the configuration reached by a list of moves, latest first.
* `Turing.MultiTapeATM.gameValue`: the value of the game of the machine with a given fuel.

## Main results

* `Turing.MultiTapeATM.gameValue_eq_true_iff`: the value of the game with fuel `n` is acceptance
  within `n` moves.
* `Turing.MultiTapeATM.DecidesInTime.mem_iff_gameValue`: under a time bound `t`, membership is the
  value of the game with fuel `t`.
* `Turing.MultiTapeATM.computableInSpace_gameValue`: the value of the game with fuel `m` is
  computable within space linear in the input and `m`.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*,
  Theorem 3.2][ChandraKozenStockmeyer1981]
* [M. Sipser, *Introduction to the Theory of Computation*, Section 10.3][Sipser2013]
-/

public section

namespace Turing.MultiTapeATM

open MultiTapeTM Cslib.Complexity

variable {k : ℕ} {State : Type} (atm : MultiTapeATM k Bool State)

/-- The configuration reached on `input` by the moves `u`, latest first. -/
noncomputable def cfgAfter (input : List Bool) (u : List Bool) : Cfg k Bool State input :=
  atm.toPTM.stepCoins u.reverse (atm.toPTM.toNTM.initCfg input)

/-- Whether the moves `p.2`, latest first, lead to a halted configuration on the input `p.1`. -/
private noncomputable def haltedAfter (p : List Bool × List Bool) : Bool :=
  (atm.cfgAfter p.1 p.2).state.isNone

/-- Whether the moves `p.2`, latest first, lead to a configuration in an existential state on the
input `p.1`. -/
private noncomputable def existentialAfter (p : List Bool × List Bool) : Bool :=
  (atm.cfgAfter p.1 p.2).state.elim false fun q => !atm.universal q

/-- Whether the moves `p.2`, latest first, lead to a halted configuration with output `[true]` on
the input `p.1`. -/
private noncomputable def acceptedAfter (p : List Bool × List Bool) : Bool :=
  atm.haltedAfter p && decide ((atm.cfgAfter p.1 p.2).output = [true])

/-- The value of the game of `atm` on `input` with fuel `n` from the moves `u`, latest first. -/
noncomputable def gameValue (input : List Bool) (n : ℕ) (u : List Bool) : Bool :=
  BitGame.value (fun u => atm.haltedAfter (input, u)) (fun u => atm.acceptedAfter (input, u))
    (fun u => atm.existentialAfter (input, u)) n u

/-- No moves leave the initial configuration. -/
@[simp] theorem cfgAfter_nil (input : List Bool) :
    atm.cfgAfter input [] = atm.toPTM.toNTM.initCfg input := by
  rw [cfgAfter, List.reverse_nil, MultiTapePTM.stepCoins_nil]

/-- A move from the configuration reached by `u` reaches the configuration of `b :: u`. -/
theorem next_cfgAfter (input : List Bool) (u : List Bool) (b : Bool) :
    atm.next b (atm.cfgAfter input u) = atm.cfgAfter input (b :: u) := by
  rw [cfgAfter, cfgAfter, List.reverse_cons, MultiTapePTM.stepCoins_append]
  rfl

/-- **The game with fuel `n` is acceptance within `n` moves.** -/
theorem gameValue_eq_true_iff (input : List Bool) (n : ℕ) (u : List Bool) :
    atm.gameValue input n u = true ↔ atm.AcceptsWithin n (atm.cfgAfter input u) := by
  induction n generalizing u with
  | zero =>
    simp [gameValue, BitGame.value, acceptedAfter, haltedAfter, AcceptsWithin,
      Option.isNone_iff_eq_none]
  | succ n ih =>
    rcases hs : (atm.cfgAfter input u).state with _ | q
    · have hL : atm.haltedAfter (input, u) = true := by simp [haltedAfter, hs]
      rw [gameValue, BitGame.value, ite_eq_left hL, atm.acceptsWithin_of_halted hs]
      simp [acceptedAfter, hL]
    · have hL : atm.haltedAfter (input, u) = false := by simp [haltedAfter, hs]
      cases hq : atm.universal q
      · have hP : atm.existentialAfter (input, u) = true := by simp [existentialAfter, hs, hq]
        rw [gameValue, BitGame.value, ite_eq_right (by simp [hL]), ite_eq_left hP,
          atm.acceptsWithin_succ_of_existential hs hq, Bool.or_eq_true, ← gameValue, ← gameValue,
          ih, ih, ← next_cfgAfter, ← next_cfgAfter, Bool.exists_bool]
      · have hP : atm.existentialAfter (input, u) = false := by simp [existentialAfter, hs, hq]
        rw [gameValue, BitGame.value, ite_eq_right (by simp [hL]), ite_eq_right (by simp [hP]),
          atm.acceptsWithin_succ_of_universal hs hq, Bool.and_eq_true, ← gameValue, ← gameValue,
          ih, ih, ← next_cfgAfter, ← next_cfgAfter, Bool.forall_bool]

/-- Under a time bound `t`, every list of `t` moves leads to a halted configuration. -/
private theorem haltedAfter_of_runsInTime {input : List Bool} {t : ℕ}
    (h : atm.toPTM.toNTM.RunsInTime input t) {u : List Bool} (hu : u.length = t) :
    atm.haltedAfter (input, u) = true := by
  rw [haltedAfter, cfgAfter, state_stepCoins_eq_none h (by simpa using hu)]
  rfl

/-- **Membership is the value of the game.** Under a time bound `t`, `a ∈ A` exactly when the
existential player wins the game of `atm` on `enc a` with fuel `t a` from the empty position. -/
theorem DecidesInTime.mem_iff_gameValue {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {t : α → ℕ} {atm : MultiTapeATM k Bool State} (h : atm.DecidesInTime enc A t) (a : α) :
    a ∈ A ↔ atm.gameValue (enc a) (t a) [] = true := by
  rw [h.mem_iff, gameValue_eq_true_iff, cfgAfter_nil]

/-! ### Space -/

variable [Finite State] {α : Type} {enc : α ↪ List Bool}

open ComputableInSpace

/-- The input and the moves in the order of their replay, within the length of the pair. -/
private theorem replayArgs :
    ComputableInSpace (fun p : α × List Bool => (p.2.reverse, enc p.1)) (encPair enc encBits)
      (encPair encBits encBits) fun p => (encPair enc encBits p).length := by
  exact budget_prod (budget_comp_linear bitsReverse (snd enc encBits))
    ((fst enc encBits).of_enc_eq fun _ => rfl)

/-- A flag of the state reached by the moves, within the length of the pair. -/
private theorem stateFlag (φ : Option State → Bool) :
    ComputableInSpace (fun p : α × List Bool => φ (atm.cfgAfter (enc p.1) p.2).state)
      (encPair enc encBits) encBool fun p => (encPair enc encBits p).length :=
  (budget_comp_linear (f := fun p : α × List Bool => (p.2.reverse, enc p.1))
    (g := fun p : List Bool × List Bool =>
      φ (atm.toPTM.stepCoins p.1 (Cfg.init atm.toPTM.initial p.2)).state)
    (lastFlag atm.toPTM φ) replayArgs).of_enc_eq fun _ => rfl

/-- The leaf test is computable within the length of the instance and the moves. -/
private theorem computableInSpace_haltedAfter :
    ComputableInSpace (fun p : α × List Bool => atm.haltedAfter (enc p.1, p.2))
      (encPair enc encBits) encBool fun p => (encPair enc encBits p).length :=
  atm.stateFlag Option.isNone

/-- The player to move is computable within the length of the instance and the moves. -/
private theorem computableInSpace_existentialAfter :
    ComputableInSpace (fun p : α × List Bool => atm.existentialAfter (enc p.1, p.2))
      (encPair enc encBits) encBool fun p => (encPair enc encBits p).length :=
  atm.stateFlag fun s => s.elim false fun q => !atm.universal q

/-- The value of a leaf is computable within the length of the instance and the moves: the halting
flag and a test of the replayed output. -/
private theorem computableInSpace_acceptedAfter :
    ComputableInSpace (fun p : α × List Bool => atm.acceptedAfter (enc p.1, p.2))
      (encPair enc encBits) encBool fun p => (encPair enc encBits p).length := by
  have hout := budget_comp_linear (of_inO (MultiTapePTM.computableInO_decide_runClosedCoins
    (enc := enc) atm.toPTM))
    (budget_prod (fst enc encBits) (budget_comp_linear bitsReverse (snd enc encBits)))
  refine (budget_boolAnd atm.computableInSpace_haltedAfter hout).of_enc_eq fun p => ?_
  simp only [acceptedAfter, cfgAfter, MultiTapePTM.runClosedCoins_eq_output_stepCoins]; rfl

/-- **Acceptance within `m` moves in space `O(n + m)`.** If every computation path of `atm` on
`enc a` of at least `m a` steps ends halted, the value of the game of `atm` on `enc a` with fuel
`m a` from the empty position is computable within space linear in the length of `enc a` and
`m a`, whether or not `m` is computable. -/
theorem computableInSpace_gameValue {m : α → ℕ}
    (hm : ∀ a, atm.toPTM.toNTM.RunsInTime (enc a) (m a)) :
    ComputableInSpace (fun a => atm.gameValue (enc a) (m a) []) enc encBool
      fun a => (enc a).length + m a := by
  refine (bitGame_value (Q := fun a => 3 * (2 * (enc a).length + 1 + m a))
    atm.computableInSpace_haltedAfter atm.computableInSpace_acceptedAfter
    atm.computableInSpace_existentialAfter (fun a u hu => atm.haltedAfter_of_runsInTime (hm a) hu)
    fun a u hu => ?_).weaken (.of_le_linear 7 3 fun a => by omega)
  simp only [encPair_apply, List.length_append, length_frame, encBits_apply]
  omega

end Turing.MultiTapeATM
