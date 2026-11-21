/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.WordGameLeaf
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WordUpdate

/-!
# A native alternating prefix for bounded word choices

One work tape starts with a sequence of player flags. The machine reads a flag, lets the
specified player replace it with a chosen bit and moves right. At the final blank it enters
the supplied alternating continuation with the complete choices on the same tape. All ambient
tapes and cursors are preserved throughout the prefix.
-/

public section

namespace Turing.MultiTapeATM.QuantifiedWord

open WordGameLeaf (config)

/-- Dispatch and player states for the prefix, followed by the continuation's own control. -/
inductive State (S : Type) where
  | dispatch
  | choose (player : Bool)
  | leaf (state : S)

instance {S : Type} [Finite S] : Finite (State S) :=
  Finite.of_injective (fun s : State S => match s with
    | .dispatch => (Sum.inl none : Option Bool ⊕ S)
    | .choose player => .inl (some player)
    | .leaf q => .inr q) (by rintro (_ | _ | _) (_ | _ | _) h <;> simp_all)

variable {k : ℕ} {S : Type}

private def act (tape : Fin k) (write : Option (Option Bool)) (move : SignType)
    (q : State S) : Action k Bool (State S) :=
  ⟨0, Function.update (fun _ => (none, 0)) tape (write, move), none, some q⟩

private noncomputable def transition (leaf : MultiTapeATM k Bool S) (tape : Fin k) (bit : Bool) :
    State S → Option Bool → (Fin k → Option Bool) → Action k Bool (State S)
  | .dispatch, _, work => act tape none 0 ((work tape).elim (.leaf leaf.toPTM.initial) .choose)
  | .choose _, _, _ => act tape (some (some bit)) 1 .dispatch
  | .leaf q, input, work =>
    let action := leaf.action q input work bit
    { action with state := action.state.map .leaf }

private def universal (leaf : MultiTapeATM k Bool S) : State S → Bool
  | .choose player => player
  | .leaf q => leaf.universal q
  | .dispatch => false

/-- Play the runtime sequence of quantifiers and run the alternating continuation. -/
noncomputable def machine (leaf : MultiTapeATM k Bool S) (tape : Fin k) :
    MultiTapeATM k Bool (State S) :=
  ofTMs (fun bit => MultiTapeTM.ofTr .dispatch (transition leaf tape bit)) (universal leaf)

/-- The root of the choice prefix reads its first flag. -/
theorem machine_initial (leaf : MultiTapeATM k Bool S) (tape : Fin k) :
    (machine leaf tape).toPTM.initial = .dispatch := by rfl

variable {input : List Bool} (leaf : MultiTapeATM k Bool S) (tape : Fin k)

private theorem next_end (pre : List Bool) (storage : Cfg k Bool Unit input) (bit : Bool) :
    (machine leaf tape).next bit (config tape (some .dispatch) pre pre.length storage) =
      (config tape (some leaf.toPTM.initial) pre pre.length storage).mapState
        (Option.map State.leaf) := by
  rw [machine, next_ofTMs, MultiTapeTM.step_of_state rfl]
  have h : (config tape (some (State.dispatch (S := S))) pre pre.length storage).workTapeSymbols
      tape = none := by simp [config, Cfg.workTapeSymbols, tapeOfList_ofNat]
  simp only [MultiTapeTM.tr_ofTr, transition, h, Option.elim_none, act]
  refine Cfg.ext rfl (by simp [config, moveInputPos_zero]) ?_ ?_ (by simp [config, Cfg.mapState])
    <;> funext i <;> by_cases hi : i = tape <;> simp [config, Cfg.mapState, hi]

private theorem next_dispatch (pre tail : List Bool) (player bit : Bool)
    (storage : Cfg k Bool Unit input) :
    (machine leaf tape).next bit (config tape (some .dispatch) (pre ++ player :: tail)
        pre.length storage) =
      config tape (some (.choose player)) (pre ++ player :: tail) pre.length storage := by
  rw [machine, next_ofTMs, MultiTapeTM.step_of_state rfl]
  have h : (config tape (some (State.dispatch (S := S))) (pre ++ player :: tail) pre.length
      storage).workTapeSymbols tape = some player := by
    simp [config, Cfg.workTapeSymbols, tapeOfList_ofNat]
  simp only [MultiTapeTM.tr_ofTr, transition, h, Option.elim_some, act]
  refine Cfg.ext rfl (by simp [config, moveInputPos_zero]) ?_ ?_ (by simp [config]) <;>
    funext i <;> by_cases hi : i = tape <;> simp [config, hi]

private theorem next_choose (pre tail : List Bool) (player bit : Bool)
    (storage : Cfg k Bool Unit input) :
    (machine leaf tape).next bit (config tape (some (.choose player)) (pre ++ player :: tail)
        pre.length storage) =
      config tape (some .dispatch) ((pre ++ [bit]) ++ tail) (pre ++ [bit]).length storage := by
  rw [machine, next_ofTMs, MultiTapeTM.step_of_state rfl]
  simp only [MultiTapeTM.tr_ofTr, transition, act]
  refine Cfg.ext rfl (by simp [config, moveInputPos_zero]) ?_ ?_ (by simp [config]) <;>
    funext i <;> by_cases hi : i = tape <;>
      simp [config, hi, List.append_assoc, update_tapeOfList_append_cons]

private noncomputable def leafSimulation : StateSimulation leaf (machine leaf tape) where
  stateMap := .leaf
  universal_eq _ := rfl
  next_eq c bit := by
    cases hs : c.state with
    | none => rw [next_of_halted _ (by simp [Cfg.mapState, hs]), next_of_halted _ hs]
    | some q =>
      have hstate : (c.mapState (Option.map State.leaf)).state = some (State.leaf q) := by
        simp [Cfg.mapState, hs]
      rw [machine, next_ofTMs, MultiTapeTM.step_of_state hstate, next_of_state _ hs]
      simp only [MultiTapeTM.tr_ofTr, transition]
      rfl

/-- Quantify each chosen bit with the player named by the corresponding flag. -/
@[expose] def plays (value : List Bool → Prop) (pre : List Bool) : List Bool → Prop
  | [] => value pre
  | player :: tail => if player then ∀ bit, plays value (pre ++ [bit]) tail
      else ∃ bit, plays value (pre ++ [bit]) tail

/-- Two transitions per choice and one final dispatch suffice for every pattern of quantifiers.
The terminal clock is uniform over all candidate completions. -/
theorem spec (t : ℕ) (storage : Cfg k Bool Unit input) (value : List Bool → Prop)
    (pre players : List Bool)
    (h : ∀ suffix : List Bool, suffix.length = players.length →
      let word := pre ++ suffix
      let cfg := config tape (some leaf.toPTM.initial) word word.length storage
      leaf.HaltsWithin t cfg ∧ (leaf.AcceptsWithin t cfg ↔ value word)) :
    let cfg := config tape (some .dispatch) (pre ++ players) pre.length storage
    let time := t + 2 * players.length + 1
    (machine leaf tape).HaltsWithin time cfg ∧
      ((machine leaf tape).AcceptsWithin time cfg ↔ plays value pre players) := by
  dsimp only
  induction players generalizing pre with
  | nil =>
    have ht := h [] rfl
    simp only [List.append_nil] at ht ⊢
    simp only [List.length_nil, Nat.mul_zero, Nat.add_zero, plays]
    constructor
    · rw [haltsWithin_succ]
      intro bit
      rw [next_end]
      exact ((leafSimulation leaf tape).haltsWithin_iff t _).2 ht.1
    · rw [acceptsWithin_succ_of_next_eq (next_end leaf tape pre storage)]
      exact ((leafSimulation leaf tape).acceptsWithin_iff t _).trans ht.2
  | cons player tail ih =>
    have hbranch (bit : Bool) := ih (pre ++ [bit]) (fun suffix hs => by
      simpa only [List.append_assoc, List.singleton_append] using
        h (bit :: suffix) (by simp [hs]))
    rw [show t + 2 * (player :: tail).length + 1 = (t + 2 * tail.length + 1) + 1 + 1 by
      simp; omega]
    constructor
    · rw [haltsWithin_succ]
      intro b
      rw [next_dispatch, haltsWithin_succ]
      intro bit
      rw [next_choose]
      exact (hbranch bit).1
    · rw [acceptsWithin_succ_of_next_eq
        (fun b => next_dispatch leaf tape pre tail player b storage)]
      cases player with
      | false =>
        rw [acceptsWithin_succ_of_existential _ rfl rfl]
        simp only [next_choose, plays, Bool.false_eq_true, ↓reduceIte]
        exact exists_congr fun bit => (hbranch bit).2
      | true =>
        rw [acceptsWithin_succ_of_universal _ rfl rfl]
        simp only [next_choose, plays, ↓reduceIte]
        exact forall_congr' fun bit => (hbranch bit).2

end Turing.MultiTapeATM.QuantifiedWord
