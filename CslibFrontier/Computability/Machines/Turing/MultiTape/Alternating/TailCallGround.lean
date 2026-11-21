/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TailCall
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.StateSimulation

/-!
# A ground machine inside a finite tail-call controller

One entry instruction reads a work symbol to choose the ground case or the recursive body.
Only marked body states return to this entry. Once the ground case is selected, every one of
its transitions is preserved. The handover costs exactly one instruction.
-/

public section

namespace Turing.MultiTapeATM.TailCallGround

open MultiTapeTM

/-- Entry, local recursive control and closed ground control. -/
inductive State (S G : Type) where
  | entry
  | node (s : S)
  | ground (g : G)

instance {S G : Type} [Finite S] [Finite G] : Finite (State S G) :=
  Finite.of_injective (fun s : State S G => match s with
    | .entry => (none : Option (S ⊕ G))
    | .node q => some (.inl q)
    | .ground q => some (.inr q)) (by rintro (_ | _ | _) (_ | _ | _) h <;> simp_all)

variable {k : ℕ} {S G : Type} (flag : Fin k) (node : MultiTapeATM k Bool S)
    (ground : MultiTapeATM k Bool G)

/-- The entry reads true for a ground request and leaves all heads in place. -/
private def transition (b : Bool) (s : State S G) (i : Option Bool)
    (work : Fin k → Option Bool) : Action k Bool (State S G) :=
  match s with
  | .entry => ⟨0, fun _ => (none, 0), none, some (if work flag = some true then
        .ground ground.toPTM.initial else .node node.toPTM.initial)⟩
  | .node x =>
    let a := node.action x i work b
    { a with state := a.state.map .node }
  | .ground x =>
    let a := ground.action x i work b
    { a with state := a.state.map .ground }

/-- One local finite control with an actual ground branch. -/
noncomputable def body : MultiTapeATM k Bool (State S G) :=
  ofTMs (fun b => ofTr .entry (transition flag node ground b)) fun
    | .entry => false
    | .node s => node.universal s
    | .ground g => ground.universal g

/-- Only the recursive branch can issue a tail call. -/
def again (mark : S → Bool) : State S G → Bool
  | .node s => mark s
  | _ => false

/-- Close the local control under tail calls; the resulting state space is independent of depth. -/
noncomputable abbrev machine (mark : S → Bool) := TailCall.machine (body flag node ground)
  (again (G := G) mark)

/-- Every invocation begins at the physical ground-or-recursive dispatch. -/
@[simp] theorem machine_initial (mark : S → Bool) :
    (machine flag node ground mark).toPTM.initial = .entry := by rfl

variable (mark : S → Bool)

private noncomputable def groundSimulation : StateSimulation ground (machine flag node ground mark)
    where
  stateMap := .ground
  universal_eq _ := rfl
  next_eq c b := by
    cases hs : c.state with
    | none => rw [next_of_halted _ (by simp [Cfg.mapState, hs]), next_of_halted _ hs]
    | some s =>
      have hstate : (c.mapState (Option.map (State.ground (S := S)))).state =
          some (.ground s) := by simp [Cfg.mapState, hs]
      rw [TailCall.next_body _ _ hstate rfl, body, next_ofTMs, MultiTapeTM.step_of_state hstate,
        next_of_state _ hs]
      simp only [tr_ofTr, transition]
      rfl

/-- A true flag enters the supplied ground machine on exactly the same configuration, including
the read-only input cursor. An arbitrary outer tape embedding may hide the flag from it. -/
theorem ground_spec {input : List Bool} (c : Cfg k Bool Unit input)
    (hg : c.workTapeSymbols flag = some true) (t : ℕ)
    (h : ground.HaltsWithin t (c.withState (some ground.toPTM.initial))) :
    let atm := machine flag node ground mark
    atm.HaltsWithin (t + 1) (c.withState (some atm.toPTM.initial)) ∧
      (atm.AcceptsWithin (t + 1) (c.withState (some atm.toPTM.initial)) ↔
        ground.AcceptsWithin t (c.withState (some ground.toPTM.initial))) := by
  let atm := machine flag node ground mark
  let sim := groundSimulation flag node ground mark
  let src := c.withState (some ground.toPTM.initial)
  let tgt := c.withState (some atm.toPTM.initial)
  have hn (b : Bool) : atm.next b tgt = src.mapState (Option.map sim.stateMap) := by
    rw [TailCall.next_body _ _ (show tgt.state = some State.entry from rfl) rfl, body,
      next_ofTMs, MultiTapeTM.step_of_state (show tgt.state = some State.entry from rfl)]
    have hr : tgt.workTapeSymbols flag = some true := hg
    simp only [tr_ofTr, transition, hr, ↓reduceIte]
    apply Cfg.ext <;>
      simp [tgt, src, Cfg.withState, Cfg.mapState, sim, groundSimulation, Action.apply]
  refine ⟨haltsWithin_succ.mpr (fun b => (hn b).symm ▸ (sim.haltsWithin_iff t src).mpr h), ?_⟩
  exact (acceptsWithin_succ_of_next_eq hn).trans (sim.acceptsWithin_iff t src)

end Turing.MultiTapeATM.TailCallGround
