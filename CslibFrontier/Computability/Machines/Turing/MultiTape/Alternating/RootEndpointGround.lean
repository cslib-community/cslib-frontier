/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TailCallGround
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootEndpointCheck
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.ExtendTapes

/-!
# Native root endpoint branch for tail-call controllers

A true ground flag dispatches directly to the real marked-schedule endpoint checker. Its private
query tapes can be embedded in any larger finite controller. A client supplies the physical
tape layout and its surrounding controller; `exists_ground` constructs the root lookup and
proves its verdict and clock. The complete encoded descendant controller is provided separately
by the DescendantEndpoint module.
-/

public section

namespace Turing.MultiTapeATM.RootEndpointGround

open MultiTapeTM

/-- At the ground dispatcher, the state reads the flag and the projected root tapes contain
exactly the serialized claim. -/
def Ready {K u : ℕ} {S G : Type} {input : List Bool} (flag : Fin K) (emb : Fin (u + 2) ↪ Fin K)
    (a : RootEndpointCheck.Input) (z : Cfg K Bool (TailCallGround.State S G) input) : Prop :=
  z.state = some .entry ∧ z.workTapeSymbols flag = some true ∧
    viewCfg emb (z.withState (none : Option Unit)) =
      WorkTapePredicate.config input (RootEndpointCheck.encInput a)

/-- A private root query and a true dispatcher flag on the extra tape. -/
def groundConfig (u : ℕ) (S G : Type) (input : List Bool) (a : RootEndpointCheck.Input) :
    Cfg ((u + 2) + 1) Bool (TailCallGround.State S G) input :=
  let c := WorkTapePredicate.config (k := u) input (RootEndpointCheck.encInput a)
  ⟨some .entry, c.inputPos, Fin.append c.workTapes (fun _ => tapeOfList [true]),
    Fin.append c.workTapePos (fun _ => 0), c.output⟩

/-- The concrete ground layout satisfies all dispatch conditions for every proposed pair. -/
theorem ready_groundConfig (u : ℕ) (S G : Type) (input : List Bool) (a : RootEndpointCheck.Input) :
    Ready (Fin.natAdd (u + 2) 0) (Fin.castAddEmb 1) a (groundConfig u S G input a) := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [groundConfig, Cfg.workTapeSymbols, tapeOfList]
  · apply Cfg.ext <;> first | rfl | (funext i; simp [groundConfig, viewCfg, Cfg.withState])

/-- One finite ground component discharges every physically ready root request of the cyclic
controller. The recursive component and its remaining tapes may be chosen after the ground
machine and its two clock constants. -/
theorem exists_ground (k : ℕ) :
    ∃ (u : ℕ) (G : Type) (_ : Finite G) (ground : MultiTapeATM (u + 2) Bool G) (C d : ℕ),
      ∀ {K : ℕ} {S : Type} (emb : Fin (u + 2) ↪ Fin K) (flag : Fin K)
        (node : MultiTapeATM K Bool S) (again : S → Bool) {input : List Bool}
        (a : RootEndpointCheck.Input) (z : Cfg K Bool (TailCallGround.State S G) input),
        let atm := TailCallGround.machine flag node (ground.extendTapes emb) again
        let time := C * (a.2.raw.length + RootEndpointCheck.shortSize a ^ d + 1) + 1
        Ready flag emb a z → atm.HaltsWithin time z ∧
          (atm.AcceptsWithin time z ↔ RootEndpointQuery.query k a.2 = some a.1) := by
  obtain ⟨u, G, hG, ground, C, d, hground⟩ := RootEndpointCheck.exists_evaluator k
  refine ⟨u, G, hG, ground, C, d, ?_⟩
  intro K S emb flag node again input a z
  dsimp only
  rintro ⟨hs, hf, hv⟩
  let store := z.withState (none : Option Unit)
  let leaf := ground.extendTapes emb
  let time := C * (a.2.raw.length + RootEndpointCheck.shortSize a ^ d + 1)
  obtain ⟨hh, ha⟩ := hground a input
  have hview : viewCfg emb (store.withState (some leaf.toPTM.initial)) =
      (WorkTapePredicate.config input (RootEndpointCheck.encInput a)).withState
        (some ground.toPTM.initial) := by
    change (viewCfg emb store).withState _ = _
    rw [show viewCfg emb store = _ from hv]
    rfl
  have hl : leaf.HaltsWithin time (store.withState (some leaf.toPTM.initial)) := by
    rw [haltsWithin_extendTapes_iff, hview]
    exact hh
  obtain ⟨ht, he⟩ := TailCallGround.ground_spec flag node leaf again store hf time hl
  have hz : store.withState (some (TailCallGround.machine flag node leaf again).toPTM.initial) =
      z := by
    apply Cfg.ext
    · simpa only [Cfg.withState, TailCallGround.machine_initial] using hs.symm
    all_goals rfl
  rw [hz] at ht he
  rw [acceptsWithin_extendTapes_iff, hview] at he
  exact ⟨ht, he.trans ha⟩

end Turing.MultiTapeATM.RootEndpointGround
