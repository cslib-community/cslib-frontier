/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.AlternatingNative

/-!
# Resources of the alternating native machine

The alternating native machine `Turing.NondeterministicQueryMachine.Native.altMachine` is the native
machine `Turing.NondeterministicQueryMachine.Native.machine` with a guess register. Erasing the
register sends each of its moves to the native step under the same choice, with the same tapes and
heads, so every computation path of the alternating machine erases to a computation path of the
native machine of the same length visiting the same cells. Space and time bounds of the native
machine therefore hold for the alternating machine.

## Main results

* `Turing.NondeterministicQueryMachine.Native.mapState_next_altMachine`: erasing the guess
  register after a move is the native step under the same choice.
* `Turing.NondeterministicQueryMachine.Native.runsInSpace_altMachine`,
  `Turing.NondeterministicQueryMachine.Native.runsInTime_altMachine`: space and time bounds
  transfer from the native machine to the alternating native machine.
* `Turing.NondeterministicQueryMachine.Routines.runsInSpace_atm`,
  `Turing.NondeterministicQueryMachine.Routines.exists_runsInTime_atm`: the compiled alternating
  native machine runs in the space of the compiled native machine, and halts on every branch under
  a common abstract clock.
-/

@[expose] public section

namespace Turing.NondeterministicQueryMachine

namespace Native

variable {k : ℕ} {SI SF : Type} {SP : Bool → Type}
  (I : MultiTapeTM k Bool SI) (P : (b : Bool) → MultiTapeTM k Bool (SP b))
  (F : MultiTapeTM k Bool SF) (C : Fin k)

/-- Erasing a relabelling that a state map undoes, after applying the relabelled action, is
applying the original action to the erased configuration. -/
private theorem mapState_apply_relabelAction {S S' : Type} {input : List Bool}
    (φ : Option S → Option S') (ψ : Option S' → Option S) (hψφ : ∀ q, ψ (φ q) = q)
    (a : Turing.Action k Bool S) (c : Cfg k Bool S' input) :
    ((relabelAction φ a).apply c).mapState ψ = a.apply (c.mapState ψ) := by
  have ha : relabelAction ψ (relabelAction φ a) = a := by
    cases a
    simp only [relabelAction, hψφ]
  rw [← apply_relabelAction ψ ψ, ha]

/-- **Erasing the guess register is the native step.** Each move `b` of the alternating native
machine, with the guess register erased, is the native step under the choice `b`. -/
theorem mapState_next_altMachine (b : Bool) {input : List Bool}
    (c : Cfg k Bool (State SI SP SF × Option Bool) input) :
    ((altMachine I P F C).next b c).mapState (Option.map Prod.fst) =
      ((table I P F C).withCoin b).toTM.step (c.mapState (Option.map Prod.fst)) := by
  rw [altMachine, MultiTapeATM.next_ofTMs]
  rcases hs : c.state with _ | ⟨q, g⟩
  · rw [MultiTapeTM.step_of_halt hs, MultiTapeTM.step_of_halt (by simp [hs])]
  · have hs' : (c.mapState (Option.map Prod.fst)).state = some q := by simp [hs]
    rw [MultiTapeTM.step_of_state hs, MultiTapeTM.step_of_state hs', tr_withCoin, guessTM,
      MultiTapeTM.tr_ofTr]
    exact mapState_apply_relabelAction _ _ (fun o => by cases o <;> rfl) _ _

/-- Erase the guess register: steps of the alternating native machine are native steps, with the
same tapes and heads. -/
@[simps! apply]
def eraseGuessHom {input : List Bool} :
    ((altMachine I P F C).toPTM.toNTM.stepRel input).Hom ((machine I P F C).stepRel input) where
  toFun := Cfg.mapState (Option.map Prod.fst)
  map_rel' {c _} hc := by
    obtain ⟨b, hb⟩ := (altMachine I P F C).toPTM.step_toNTM_iff.mp hc
    exact (step_iff I P F C).mpr
      ⟨b, (mapState_next_altMachine I P F C b c).symm.trans (congrArg _ hb)⟩

/-- A computation path of the alternating native machine, with the guess register erased: a
native computation path of the same length visiting the same cells. -/
noncomputable def eraseGuessPath {input : List Bool}
    (p : (altMachine I P F C).toPTM.toNTM.ComputationPath input) :
    (machine I P F C).ComputationPath input where
  toRunPath := p.toRunPath.map (eraseGuessHom I P F C)
  head_eq := by
    rw [RelSeries.head_map, p.head_eq]
    rfl

/-- **Space bounds transfer to the alternating native machine.** -/
theorem runsInSpace_altMachine {input : List Bool} {s : ℕ}
    (h : (machine I P F C).RunsInSpace input s) :
    (altMachine I P F C).toPTM.toNTM.RunsInSpace input s := fun p =>
  h (eraseGuessPath I P F C p)

/-- **Time bounds transfer to the alternating native machine.** -/
theorem runsInTime_altMachine {input : List Bool} {t : ℕ}
    (h : (machine I P F C).RunsInTime input t) :
    (altMachine I P F C).toPTM.toNTM.RunsInTime input t := fun p hp =>
  Option.map_eq_none_iff.mp (h (eraseGuessPath I P F C p) hp)

end Native

namespace Routines

variable {α σ : Type} {M : NondeterministicQueryMachine σ} {start : α → σ}
  {enc : α ↪ List Bool} {S : α → ℕ} (R : Routines M start enc S)

/-- All prefixes of the compiled alternating native machine remain in the shared workspace
window. -/
theorem runsInSpace_atm (a : α) :
    R.atm.toPTM.toNTM.RunsInSpace (enc a) (R.k * (2 * (R.c * S a) + 1)) :=
  Native.runsInSpace_altMachine R.I R.P R.F R.C (R.runsInSpace a)

/-- A common abstract clock yields an all-branches clock for the compiled alternating native
machine. -/
theorem exists_runsInTime_atm (a : α) {time : ℕ}
    (hhalt : (M.withInit (start a)).HaltsWithin (enc a) time) :
    ∃ t, R.atm.toPTM.toNTM.RunsInTime (enc a) t :=
  (R.exists_runsInTime a hhalt).imp fun _ => Native.runsInTime_altMachine R.I R.P R.F R.C

end Routines

end Turing.NondeterministicQueryMachine
