/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.DescendantEndpointLoop
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TailCallGround
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootEndpointCheck
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.ExtendTapes

/-!
# Native ground branch of the descendant endpoint controller

A true ground flag dispatches directly to the real marked-schedule endpoint checker. Its private
query tapes can be embedded in any larger finite controller. The recursive client therefore
supplies a physical tape-layout and clock bound at depth zero, together with the nonempty local
segments. It does not supply a machine or acceptance hypothesis for a root endpoint lookup.
-/

public section

namespace Turing.MultiTapeATM.RootEndpointGround

open MultiTapeTM MultiTapePTM Cslib.Circuits.Frontier NativeChild EndpointQuery

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

/-- The descendant clock and numbered-endpoint semantics with the ground acceptance premise
discharged. At an empty stack only the tape layout and the promised terminal budget remain. -/
theorem exists_descendant_controller (k : ℕ) :
    ∃ (u : ℕ) (G : Type) (_ : Finite G) (ground : MultiTapeATM (u + 2) Bool G) (C d : ℕ),
      ∀ {K copies q : ℕ} {S R : Type} (emb : Fin (u + 2) ↪ Fin K) (flag : Fin K)
        (node : MultiTapeATM K Bool S) (mark : S → Bool)
        (source : MultiTapePTM k Bool R) (word : List Bool) (b σ : ℕ)
        (code : BlockLetter k R b → Fin copies → Bool) {input : List Bool}
        (read : Cfg K Bool (TailCallGround.State S G) input → ℕ × (ℕ × ℕ))
        (ready : List Labels → Cfg K Bool (TailCallGround.State S G) input → Prop)
        (cost : Labels → ℕ) (terminal : ℕ),
        let raw := ScheduleBits.rows (List.ofFn (scheduleOfNat k q σ))
        let root := RootEndpointQuery.endpointQuery k copies raw
        let argument z : RootEndpointCheck.Input := ((read z).2, ⟨raw, copies, (read z).1⟩)
        let meaning (stack : List Labels) z :=
          (DescendantEndpointLoop.atStack root stack).accepts (read z).1 (read z).2
        let body := TailCallGround.body flag node (ground.extendTapes emb)
        let again := TailCallGround.again (G := G) mark
        let atm := TailCall.machine body again
        (∀ z, ready [] z → Ready flag emb (argument z) z ∧
          C * (raw.length + RootEndpointCheck.shortSize (argument z) ^ d + 1) + 1 ≤ terminal) →
        (∀ l ls z, ready (l :: ls) z → TailCall.Segment body again (ready ls) (meaning ls)
          (cost l) z (meaning (l :: ls) z)) →
        ∀ stack z, ready stack z →
          let time := stack.foldr (fun l t => cost l + 1 + t) terminal
          let edges := stack.foldr (fun l es => l.edges es) (RootPortGraph.ends (q := q)
            source word b σ code)
          atm.HaltsWithin time z ∧ (atm.AcceptsWithin time z ↔
            (read z).1 < edges.length ∧ edges.getD (read z).1 (0, 0) = (read z).2) := by
  obtain ⟨u, G, hG, ground, C, d, hg⟩ := exists_ground k
  refine ⟨u, G, hG, ground, C, d, ?_⟩
  intro K copies q S R emb flag node mark source word b σ code input read ready cost terminal raw
    root argument meaning body again atm hbase hstep stack z hz
  apply DescendantEndpointLoop.run (q := q) source word b σ code body again read ready
    cost terminal ?_ hstep stack z hz
  intro c hc
  obtain ⟨hl, ht⟩ := hbase c hc
  obtain ⟨hh, ha⟩ := hg emb flag node mark (argument c) c hl
  exact ⟨hh.mono ht, ⟨fun h => ha.mp (h.of_halted_stepCoins hh), fun h => (ha.mpr h).mono ht⟩⟩

end Turing.MultiTapeATM.RootEndpointGround
