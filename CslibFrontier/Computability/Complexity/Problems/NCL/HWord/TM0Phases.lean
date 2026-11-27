/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.SingleTape.TM0Window

/-!
# Single-letter phases for moving a finite-window tape head

A move transfers the head in four phases: mark the old cell, mark its neighbour, release the
old cell, and activate the neighbour. This keeps all local rewrite rules length two with only
one changed letter. Writes have a single phase.

## Main results

* `TM0Window.Phases.respects`: the phase machine refines the original window machine.
* `TM0Window.Phases.reaches_halted_iff`: stable halted targets preserve reachability.
-/

public section

namespace Cslib.Complexity.NCL.TM0Window
open Turing.TM0Window
open Turing StateTransition

/-- The two cells and their surrounding tape during a head transfer. -/
structure PairCfg (Γ Q : Type*) where
  /-- State after the original move instruction. -/
  state : Q
  /-- Symbol of the left cell of the pair. -/
  first : Γ
  /-- Symbol of the right cell of the pair. -/
  second : Γ
  /-- Cells to the left of the pair, nearest first. -/
  left : List Γ
  /-- Cells to the right of the pair, nearest first. -/
  right : List Γ
  deriving DecidableEq

/-- The three intermediate stages of either transfer direction. -/
inductive Phase
  | rightStart | rightBoth | rightEnd | leftStart | leftBoth | leftEnd
  deriving DecidableEq

/-- Stable window configurations and the intermediate adjacent-cell transfers. -/
inductive MicroCfg (Γ Q : Type*)
  | stable (cfg : Cfg Γ Q)
  | moving (phase : Phase) (cfg : PairCfg Γ Q)
  deriving DecidableEq

namespace Phases
variable {Γ Q : Type*} [Inhabited Q]

/-- Execute a write immediately, and split each head transfer into four single-letter stages. -/
@[expose] def step (M : TM0.Machine Γ Q) : MicroCfg Γ Q → Option (MicroCfg Γ Q)
  | .stable c => (Turing.TM0Window.step M c).map fun d =>
      match M c.state c.scanned with
      | some (_, .move .right) =>
          .moving .rightStart ⟨d.state, c.scanned, d.scanned, c.left, d.right⟩
      | some (_, .move .left) =>
          .moving .leftStart ⟨d.state, d.scanned, c.scanned, d.left, c.right⟩
      | _ => .stable d
  | .moving .rightStart c => some (.moving .rightBoth c)
  | .moving .rightBoth c => some (.moving .rightEnd c)
  | .moving .rightEnd c => some (.stable ⟨c.state, c.second, c.first :: c.left, c.right⟩)
  | .moving .leftStart c => some (.moving .leftBoth c)
  | .moving .leftBoth c => some (.moving .leftEnd c)
  | .moving .leftEnd c => some (.stable ⟨c.state, c.first, c.left, c.second :: c.right⟩)

private theorem finish_left (M : TM0.Machine Γ Q) (p : PairCfg Γ Q) :
    Reaches₁ (step M) (.moving .leftStart p)
      (.stable ⟨p.state, p.first, p.left, p.second :: p.right⟩) :=
  .head (Option.mem_def.mpr rfl : MicroCfg.moving .leftBoth p ∈ _)
    (.head (Option.mem_def.mpr rfl : MicroCfg.moving .leftEnd p ∈ _)
      (.single (Option.mem_def.mpr rfl)))

private theorem finish_right (M : TM0.Machine Γ Q) (p : PairCfg Γ Q) :
    Reaches₁ (step M) (.moving .rightStart p)
      (.stable ⟨p.state, p.second, p.first :: p.left, p.right⟩) :=
  .head (Option.mem_def.mpr rfl : MicroCfg.moving .rightBoth p ∈ _)
    (.head (Option.mem_def.mpr rfl : MicroCfg.moving .rightEnd p ∈ _)
      (.single (Option.mem_def.mpr rfl)))

private theorem run_of_step {M : TM0.Machine Γ Q} {c d : Cfg Γ Q}
    (h : Turing.TM0Window.step M c = some d) : Reaches₁ (step M) (.stable c) (.stable d) := by
  rcases c with ⟨q, a, L, R⟩
  cases hM : M q a with
  | none => simp only [Turing.TM0Window.step, hM] at h; contradiction
  | some result =>
    rcases result with ⟨q', action⟩
    cases action with
    | write b =>
      simp only [Turing.TM0Window.step, hM] at h
      cases h
      exact .single (by
        simp only [step, Turing.TM0Window.step, hM, Option.map_some, Option.mem_def])
    | move direction =>
      cases direction with
      | left =>
        cases L with
        | nil => simp only [Turing.TM0Window.step, hM] at h; contradiction
        | cons b L =>
          simp only [Turing.TM0Window.step, hM] at h
          cases h
          exact .head
            (by simp only [step, Turing.TM0Window.step, hM, Option.map_some, Option.mem_def])
            (finish_left M ⟨q', b, a, L, R⟩)
      | right =>
        cases R with
        | nil => simp only [Turing.TM0Window.step, hM] at h; contradiction
        | cons b R =>
          simp only [Turing.TM0Window.step, hM] at h
          cases h
          exact .head
            (by simp only [step, Turing.TM0Window.step, hM, Option.map_some, Option.mem_def])
            (finish_right M ⟨q', a, b, L, R⟩)

/-- Each original window instruction has its exact finite micro-computation. -/
theorem respects (M : TM0.Machine Γ Q) :
    Respects (Turing.TM0Window.step M) (step M) (fun c d => MicroCfg.stable c = d) :=
  fun_respects.mpr fun c => by
    cases hc : Turing.TM0Window.step M c with
    | none => simp only [FRespects, step, hc, Option.map_none]
    | some _ => exact run_of_step hc

/-- The phase expansion preserves reachability of each stable halted target. -/
theorem reaches_halted_iff (M : TM0.Machine Γ Q) (c d : Cfg Γ Q)
    (hd : Turing.TM0Window.step M d = none) :
    Reaches (step M) (.stable c) (.stable d) ↔ Reaches (Turing.TM0Window.step M) c d := by
  refine ⟨fun hr => ?_, fun hr => ?_⟩
  · obtain ⟨e, he, heval⟩ := tr_eval_rev (respects M) rfl
      (mem_eval.mpr ⟨hr, by simp only [step, hd, Option.map_none]⟩)
    exact MicroCfg.stable.inj he ▸ (mem_eval.mp heval).1
  · obtain ⟨e, he, hre⟩ := tr_reaches (respects M) rfl hr
    exact he ▸ hre

end Phases
end Cslib.Complexity.NCL.TM0Window
