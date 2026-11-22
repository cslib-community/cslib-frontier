/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.IntervalSimulation

/-!
# A short input window for interval replay

A replay of at most `t` coin steps from input position `p` uses the input substring beginning at
`p - (t + 1)` and containing at most `2 * t + 1` symbols. Replaying on this substring preserves
the full finite configuration after restoring the input-position origin. Every reachable real
end cell is retained, and a newly introduced end cell cannot be read before the replay finishes.

`localRun_inputWindow` is consumed by the prepared interval witness check. It is the semantic
reduction for source-window preprocessing; extraction and native resource bounds are established
separately by the interval-count implementation.
-/

public section

namespace Turing.MultiTapePTM

variable {k : ℕ} {State : Type}

private theorem inputAt_drop_take (input : List Bool) {p a w : ℕ}
    (hleft : a = 0 ∨ a < p) (hright : p ≤ a + w) :
    inputAt ((input.drop a).take w) (p - a) = inputAt input p := by
  by_cases hp : p = 0
  · subst p
    have ha : a = 0 := by omega
    simp [inputAt, ha]
  · have hpa : a < p := by omega
    simp only [inputAt, ite_eq_right hp, ite_eq_right (by omega : p - a ≠ 0)]
    rw [List.getElem?_take, ite_eq_left (by omega), List.getElem?_drop]
    congr 1
    omega

private theorem moveInputPosNat_bounds (n p : ℕ) (d : SignType) (hp : p ≤ n + 1) :
    moveInputPosNat n p d ≤ n + 1 ∧ p ≤ moveInputPosNat n p d + 1 ∧
      moveInputPosNat n p d ≤ p + 1 := by
  let pos : Fin (n + 2) := ⟨p, by omega⟩
  have hr := (moveInputPos pos d).isLt
  rw [val_moveInputPos_eq_moveInputPosNat] at hr
  change moveInputPosNat n p d < n + 2 at hr
  have hd := le_add_one_of_moveInputPosNat_eq (n := n) (j' := p) (d := d) (by omega) rfl
  exact ⟨by omega, by omega, by omega⟩

private theorem moveInputPosNat_drop_take (n p a w : ℕ) (d : SignType)
    (ha : a ≤ n) (hp : p ≤ n + 1) (hleft : a = 0 ∨ a < p) (hright : p ≤ a + w) :
    moveInputPosNat (min w (n - a)) (p - a) d + a = moveInputPosNat n p d := by
  cases d <;>
    simp only [moveInputPosNat, SignType.zero_eq_zero, SignType.neg_eq_neg_one,
      SignType.pos_eq_one, SignType.coe_zero, SignType.coe_neg_one, SignType.coe_one] <;>
    omega

private theorem localRun_drop_take (machine : MultiTapePTM k Bool State) (input : List Bool)
    (coins : List Bool) (a w : ℕ) (l : LocalCfg k State)
    (ha : a ≤ input.length) (hp : l.inputPos ≤ input.length + 1)
    (hleft : a = 0 ∨ a + coins.length < l.inputPos)
    (hright : l.inputPos + coins.length ≤ a + w) :
    let result := machine.localRun ((input.drop a).take w) coins
      { l with inputPos := l.inputPos - a }
    { result with inputPos := result.inputPos + a } = machine.localRun input coins l := by
  induction coins generalizing l with
  | nil =>
    simp only [localRun, List.foldl_nil]
    have hpa : a ≤ l.inputPos := by omega
    simp [Nat.sub_add_cancel hpa]
  | cons bit coins ih =>
    have hs := inputAt_drop_take input (p := l.inputPos) (a := a) (w := w)
      (by simp only [List.length_cons] at hleft; omega) (by omega)
    let action := machine.coinAction l.state (inputAt input l.inputPos)
      (fun h => (l.workTapes h).head) bit
    have hm := moveInputPosNat_drop_take input.length l.inputPos a w action.inputTape ha hp
      (by simp only [List.length_cons] at hleft; omega) (by omega)
    have hb := moveInputPosNat_bounds input.length l.inputPos action.inputTape hp
    have hstep : machine.localCoinStep ((input.drop a).take w)
        { l with inputPos := l.inputPos - a } bit =
        { machine.localCoinStep input l bit with
          inputPos := (machine.localCoinStep input l bit).inputPos - a } := by
      simp only [localCoinStep, hs, List.length_take, List.length_drop]
      dsimp only [action] at hm
      congr 1
      omega
    simp only [localRun, List.foldl_cons, hstep]
    apply ih
    · exact hb.1
    · simp only [localCoinStep]
      change a = 0 ∨ a + coins.length < moveInputPosNat input.length l.inputPos action.inputTape
      simp only [List.length_cons] at hleft
      omega
    · simp only [localCoinStep]
      change moveInputPosNat input.length l.inputPos action.inputTape + coins.length ≤ a + w
      simp only [List.length_cons] at hright
      omega

/-- Every replay of at most `t` steps can use at most `2 * t + 1` source symbols. Restoring the
substring's origin gives exactly the original finite configuration, including its input position.
The initial position may be either real blank end cell; the source input may be empty. -/
theorem localRun_inputWindow (machine : MultiTapePTM k Bool State) (input : List Bool)
    (coins : List Bool) (l : LocalCfg k State) (t : ℕ)
    (hp : l.inputPos ≤ input.length + 1) (ht : coins.length ≤ t) :
    let a := l.inputPos - (t + 1)
    let result := machine.localRun ((input.drop a).take (2 * t + 1)) coins
      { l with inputPos := l.inputPos - a }
    { result with inputPos := result.inputPos + a } = machine.localRun input coins l := by
  apply localRun_drop_take
  · omega
  · exact hp
  · omega
  · omega

end Turing.MultiTapePTM
