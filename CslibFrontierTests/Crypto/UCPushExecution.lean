/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/
module
-- upstream: local-only (test)

import CslibFrontier.Crypto.Protocols.UC.PushExecution
import CslibFrontier.Languages.Probabilistic.Iteration.Add

/-!
# Tests for the UC Single-Token Push Runtime

End-to-end concrete witnesses exercising `Cslib.Crypto.Protocols.UC.Push`:

* **Ping-pong witness**: a 3-node reactive system (`envNode` → `forwardNode` → `pongNode` →
  `envNode`) verifying:
  - a 4-step write chain yields `PMF.pure (some true)` under `pushRun` and `PMF.pure true` under
    `pushExec`, invariant under extra fuel (`4 + extra`),
  - flipping the leaf payload (`flipNode`) flips the output to `some false`,
  - denying the middle write via `ControlFunction` (`denyTo2`) bounces `Delivery.resume` back to
    the initial node and observably separates `allowAll` from `denyTo2`,
  - under-fueled execution (`fuel = 3`) yields `PMF.pure none` under `pushRun` and `PMF.pure false`
    under `pushExec`,
  - a probabilistic leaf node (`coinNode`) propagates `ProbComp` randomness through `pushExec`.
* **Halted-recipient witness**: a 2-node system contrasting `haltingPeer`, `replyingPeer`,
  and `yieldingPeer` to verify that:
  - writing to a halted recipient records the envelope in `TokenState.log`, skips the halted
    node's handler (keeping its state counter at `1`), and returns `Delivery.resume` to `initial`,
  - a non-halting reply delivers back to `0` (`pushExec = PMF.pure false`),
  - `Outcome.yield` returns `Delivery.resume` without marking the node halted (its state counter
    reaches `2` on the second activation).
* **Structural checks**: concrete checks of `OracleComp.iterate_add`, `isQueryBounded_iterate_step`,
  `eval_pushRun_zero`, and `κ`-dependent reactive nodes.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.UCPushExecution

open Cslib
open Cslib.Crypto.Protocols
open Cslib.Crypto.Protocols.UC
open Cslib.Crypto.Protocols.UC.Push
open Cslib.Probability

/-! ### 3-Node Ping-Pong Chain -/

private inductive PingPong where
  | ping
  | pong (bit : Bool)
  deriving DecidableEq

private abbrev envNode : ReactiveNode 3 PingPong where
  State := Unit
  init := pure ()
  handle
    | .start _, _ => pure (.write 1 .input .ping, ())
    | .deliver e, _ =>
      let out : Bool :=
        match e.payload with
        | .pong b => decide (e.sender = 2 ∧ e.tape = .subroutineOutput) && b
        | .ping => false
      pure (.halt out, ())
    | .resume, _ => pure (.halt false, ())

private abbrev forwardNode : ReactiveNode 3 PingPong where
  State := Unit
  init := pure ()
  handle
    | .deliver ⟨0, 1, .input, .ping⟩, _ => pure (.write 2 .input .ping, ())
    | _, _ => pure (.yield, ())

private abbrev pongNode : ReactiveNode 3 PingPong where
  State := Unit
  init := pure ()
  handle
    | .deliver ⟨1, 2, .input, .ping⟩, _ => pure (.write 0 .subroutineOutput (.pong true), ())
    | _, _ => pure (.yield, ())

private abbrev flipNode : ReactiveNode 3 PingPong where
  State := Unit
  init := pure ()
  handle
    | .deliver ⟨1, 2, .input, .ping⟩, _ => pure (.write 0 .subroutineOutput (.pong false), ())
    | _, _ => pure (.yield, ())

private abbrev coinNode : ReactiveNode 3 PingPong where
  State := Unit
  init := pure ()
  handle
    | .deliver ⟨1, 2, .input, .ping⟩, _ => do
      let b ← ProbOracleComp.sample (ProbComp.unifFin 1)
      pure (.write 0 .subroutineOutput (.pong (decide (b = 1))), ())
    | _, _ => pure (.yield, ())

private def allowAll {m : ℕ} {Msg : Type} : ControlFunction m Msg := fun _ _ => true

private def denyTo2 : ControlFunction 3 PingPong := fun _ e => decide (e.recipient ≠ 2)

private def pingPongSystem (q : ReactiveNode 3 PingPong) (ctrl : ControlFunction 3 PingPong) :
    PushSystem 3 PingPong where
  node _
    | 0 => envNode
    | 1 => forwardNode
    | 2 => q
  initial := 0
  control := ctrl

private def state3 (q : ReactiveNode 3 PingPong) (s₂ : q.State) (κ : ℕ)
    (ctrl : ControlFunction 3 PingPong) :
    (SSP.parFin ((pingPongSystem q ctrl).node κ)).State
  | 0 => ()
  | 1 => ()
  | 2 => s₂

private theorem update_state3_0 (q : ReactiveNode 3 PingPong) (s₂ : q.State) (κ : ℕ)
    (ctrl : ControlFunction 3 PingPong) :
    (Function.update (state3 q s₂ κ ctrl) 0 () :
      (SSP.parFin ((pingPongSystem q ctrl).node κ)).State) = state3 q s₂ κ ctrl := by
  funext j; fin_cases j <;> rfl

private theorem update_state3_1 (q : ReactiveNode 3 PingPong) (s₂ : q.State) (κ : ℕ)
    (ctrl : ControlFunction 3 PingPong) :
    (Function.update (state3 q s₂ κ ctrl) 1 () :
      (SSP.parFin ((pingPongSystem q ctrl).node κ)).State) = state3 q s₂ κ ctrl := by
  funext j; fin_cases j <;> rfl

private theorem update_state3_2 (q : ReactiveNode 3 PingPong) (s₂ s₂' : q.State) (κ : ℕ)
    (ctrl : ControlFunction 3 PingPong) :
    (Function.update (state3 q s₂ κ ctrl) 2 s₂' :
      (SSP.parFin ((pingPongSystem q ctrl).node κ)).State) = state3 q s₂' κ ctrl := by
  funext j; fin_cases j <;> rfl

private theorem init_pingPong (q : ReactiveNode 3 PingPong) (s₂ : q.State) (hq : q.init = pure s₂)
    (κ : ℕ) (ctrl : ControlFunction 3 PingPong) :
    ∀ j : Fin 3, ((pingPongSystem q ctrl).node κ j).init = pure (state3 q s₂ κ ctrl j) := by
  intro j; fin_cases j <;> first | rfl | exact hq

private def ppEnv01 : Envelope 3 PingPong := ⟨0, 1, .input, .ping⟩
private def ppEnv12 : Envelope 3 PingPong := ⟨1, 2, .input, .ping⟩
private def ppEnv20 (b : Bool) : Envelope 3 PingPong := ⟨2, 0, .subroutineOutput, .pong b⟩

private theorem pingPong_prefix2 (q : ReactiveNode 3 PingPong) (s₂ : q.State) (κ f : ℕ)
    (z : List Bool) :
    (SSP.parFin ((pingPongSystem q allowAll).node κ)).runFrom
      (OracleComp.iterate (f + 2) (step (pingPongSystem q allowAll))
        (TokenState.initialFor (pingPongSystem q allowAll).initial z))
      (state3 q s₂ κ allowAll) =
      (SSP.parFin ((pingPongSystem q allowAll).node κ)).runFrom
        (OracleComp.iterate f (step (pingPongSystem q allowAll))
          { target := 2, delivery := .deliver ppEnv12, log := [ppEnv01, ppEnv12],
            halted := ∅, output := none })
        (state3 q s₂ κ allowAll) := by
  rw [runFrom_iterate_step_succ_of_handle_eq_pure (pingPongSystem q allowAll) κ (f + 1) rfl
        (by simp [TokenState.initialFor]) rfl (update_state3_0 q s₂ κ allowAll),
      runFrom_iterate_step_succ_of_handle_eq_pure (pingPongSystem q allowAll) κ f rfl
        (by simp [TokenState.next, TokenState.initialFor, pingPongSystem, allowAll])
        rfl (update_state3_1 q s₂ κ allowAll)]
  rfl

private theorem pingPong_deterministic_steps (q : ReactiveNode 3 PingPong) (b : Bool)
    (hstep : ∀ u : q.State,
      (q.handle (.deliver ppEnv12)).run u = pure (.write 0 .subroutineOutput (.pong b), u))
    (s₂ : q.State) (κ extra : ℕ) (z : List Bool) :
    (SSP.parFin ((pingPongSystem q allowAll).node κ)).runFrom
      (OracleComp.iterate (4 + extra) (step (pingPongSystem q allowAll))
        (TokenState.initialFor (pingPongSystem q allowAll).initial z))
      (state3 q s₂ κ allowAll) =
      pure ({ target := 0, delivery := .deliver (ppEnv20 b),
              log := [ppEnv01, ppEnv12, ppEnv20 b], halted := ∅, output := some b },
            state3 q s₂ κ allowAll) := by
  rw [show 4 + extra = (extra + 2) + 2 by omega, pingPong_prefix2]
  have h3 := runFrom_iterate_step_succ_of_handle_eq_pure (pingPongSystem q allowAll) κ (extra + 1)
    (ts := { target := 2, delivery := .deliver ppEnv12, log := [ppEnv01, ppEnv12],
             halted := ∅, output := none })
    (s := state3 q s₂ κ allowAll)
    rfl (by simp) (hstep s₂) (update_state3_2 q s₂ s₂ κ allowAll)
  rw [h3,
    runFrom_iterate_step_succ_of_handle_eq_pure (pingPongSystem q allowAll) κ extra rfl
      (by simp [TokenState.next, pingPongSystem, allowAll]) rfl
      (update_state3_0 q s₂ κ allowAll)]
  rw [runFrom_iterate_step_of_output_isSome _ κ extra rfl]
  rfl

/-- 3-node ping-pong with `allowAll` halts in 4 steps with `some true`, and extra fuel leaves
the output unchanged. -/
theorem pingPong_allowAll_run (κ : ℕ) (z : List Bool) (extra : ℕ) :
    (pushRun (pingPongSystem pongNode allowAll) κ z (4 + extra)).eval =
      PMF.pure (some true) := by
  rw [eval_pushRun_of_init_pure _ κ z (4 + extra) (state3 pongNode () κ allowAll)
    (init_pingPong pongNode () rfl κ allowAll),
    pingPong_deterministic_steps pongNode true (fun () => rfl) () κ extra z]
  simp only [Machine.closeProgram_pure, map_pure, Function.comp_apply, ProbComp.eval_pure]

/-- `pushExec` on the 3-node ping-pong system outputs `true`. -/
theorem pingPong_allowAll_exec (κ : ℕ) (z : List Bool) (extra : ℕ) :
    (pushExec (pingPongSystem pongNode allowAll) κ z (4 + extra)).eval = PMF.pure true := by
  rw [pushExec, ProbComp.eval_map, pingPong_allowAll_run, PMF.pure_map]
  rfl

/-- Flipping the leaf payload to `pong false` flips the system output to `some false`
(non-triviality). -/
theorem pingPong_flip_run (κ : ℕ) (z : List Bool) (extra : ℕ) :
    (pushRun (pingPongSystem flipNode allowAll) κ z (4 + extra)).eval =
      PMF.pure (some false) := by
  rw [eval_pushRun_of_init_pure _ κ z (4 + extra) (state3 flipNode () κ allowAll)
    (init_pingPong flipNode () rfl κ allowAll),
    pingPong_deterministic_steps flipNode false (fun () => rfl) () κ extra z]
  simp only [Machine.closeProgram_pure, map_pure, Function.comp_apply, ProbComp.eval_pure]

/-- Denying writes to node `2` via `denyTo2` causes node `1`'s write to fail, bouncing
`Delivery.resume` back to `0` so `0` halts with `some false` in 3 steps. -/
theorem pingPong_denyForward_run (κ : ℕ) (z : List Bool) (extra : ℕ) :
    (pushRun (pingPongSystem pongNode denyTo2) κ z (3 + extra)).eval =
      PMF.pure (some false) := by
  rw [eval_pushRun_of_init_pure _ κ z (3 + extra) (state3 pongNode () κ denyTo2)
    (init_pingPong pongNode () rfl κ denyTo2),
    show 3 + extra = (extra + 2) + 1 by omega,
    runFrom_iterate_step_succ_of_handle_eq_pure (pingPongSystem pongNode denyTo2) κ (extra + 2) rfl
      (by simp [TokenState.initialFor]) rfl (update_state3_0 pongNode () κ denyTo2),
    runFrom_iterate_step_succ_of_handle_eq_pure (pingPongSystem pongNode denyTo2) κ (extra + 1) rfl
      (by simp [TokenState.next, TokenState.initialFor, pingPongSystem, denyTo2])
      rfl (update_state3_1 pongNode () κ denyTo2),
    runFrom_iterate_step_succ_of_handle_eq_pure (pingPongSystem pongNode denyTo2) κ extra rfl
      (by simp [TokenState.next, TokenState.initialFor, pingPongSystem, denyTo2])
      rfl (update_state3_0 pongNode () κ denyTo2)]
  rw [runFrom_iterate_step_of_output_isSome _ κ extra rfl]
  simp only [Machine.closeProgram_pure, map_pure, Function.comp_apply, ProbComp.eval_pure]
  rfl

/-- Observable contrast: the control function separates `allowAll` from `denyTo2`. -/
theorem pingPong_control_separates (κ : ℕ) (z : List Bool) :
    (pushRun (pingPongSystem pongNode allowAll) κ z 4).eval ≠
      (pushRun (pingPongSystem pongNode denyTo2) κ z 4).eval := by
  rw [pingPong_allowAll_run κ z 0, show (4 : ℕ) = 3 + 1 from rfl,
    pingPong_denyForward_run κ z 1]
  intro h
  have htrue := congrArg (fun p => p (some true)) h
  simp at htrue

/-- Under-fueled witness: with `fuel = 3` (one step short of `envNode`'s final halt), `pushRun`
returns `PMF.pure none` and `pushExec` defaults to `PMF.pure false`. -/
theorem pingPong_underfueled_run (κ : ℕ) (z : List Bool) :
    (pushRun (pingPongSystem pongNode allowAll) κ z 3).eval = PMF.pure none ∧
      (pushExec (pingPongSystem pongNode allowAll) κ z 3).eval = PMF.pure false := by
  have hpush : (pushRun (pingPongSystem pongNode allowAll) κ z 3).eval = PMF.pure none := by
    rw [eval_pushRun_of_init_pure _ κ z 3 (state3 pongNode () κ allowAll)
      (init_pingPong pongNode () rfl κ allowAll),
      pingPong_prefix2 pongNode () κ 1 z,
      runFrom_iterate_step_succ_of_handle_eq_pure (pingPongSystem pongNode allowAll) κ 0 rfl
        (by simp) rfl (update_state3_2 pongNode () () κ allowAll)]
    rw [OracleComp.iterate_zero, Machine.runFrom_pure]
    simp only [Machine.closeProgram_pure, map_pure, Function.comp_apply, ProbComp.eval_pure]
    rfl
  refine ⟨hpush, ?_⟩
  rw [pushExec, ProbComp.eval_map, hpush, PMF.pure_map]
  rfl

/-- Probabilistic leaf witness: a coin-flipping leaf node (`coinNode`) propagates `ProbComp`
randomness through `pushRun` and `pushExec`. -/
theorem pingPong_coinNode_exec (κ : ℕ) (z : List Bool) (extra : ℕ) :
    (pushExec (pingPongSystem coinNode allowAll) κ z (4 + extra)).eval =
      (PMF.uniformOfFintype (Fin 2)).map (fun b => decide (b = 1)) := by
  rw [pushExec, ProbComp.eval_map,
    eval_pushRun_of_init_pure _ κ z (4 + extra) (state3 coinNode () κ allowAll)
      (init_pingPong coinNode () rfl κ allowAll)]
  have hrun :
      (SSP.parFin ((pingPongSystem coinNode allowAll).node κ)).runFrom
        (OracleComp.iterate (4 + extra) (step (pingPongSystem coinNode allowAll))
          (TokenState.initialFor (pingPongSystem coinNode allowAll).initial z))
        (state3 coinNode () κ allowAll) =
        ProbOracleComp.sample (ProbComp.unifFin 1) >>= fun b =>
          pure ({ target := 0, delivery := .deliver (ppEnv20 (decide (b = 1))),
                  log := [ppEnv01, ppEnv12, ppEnv20 (decide (b = 1))],
                  halted := ∅, output := some (decide (b = 1)) },
                state3 coinNode () κ allowAll) := by
    rw [show 4 + extra = (extra + 2) + 2 by omega, pingPong_prefix2,
      runFrom_iterate_step_succ_of_not_mem_halted _ κ (extra + 1) rfl (by simp)]
    change (ProbOracleComp.sample (ProbComp.unifFin 1) >>= fun b =>
      (SSP.parFin ((pingPongSystem coinNode allowAll).node κ)).runFrom
        (OracleComp.iterate (extra + 1) (step (pingPongSystem coinNode allowAll))
          { target := 0, delivery := .deliver (ppEnv20 (decide (b = 1))),
            log := [ppEnv01, ppEnv12, ppEnv20 (decide (b = 1))], halted := ∅, output := none })
        (Function.update (state3 coinNode () κ allowAll) 2 ())) = _
    congr 1; funext b
    rw [update_state3_2 coinNode () () κ allowAll,
      runFrom_iterate_step_succ_of_handle_eq_pure (pingPongSystem coinNode allowAll) κ extra rfl
        (by simp) rfl (update_state3_0 coinNode () κ allowAll)]
    rw [runFrom_iterate_step_of_output_isSome _ κ extra rfl]
    rfl
  rw [hrun]
  simp only [Machine.closeProgram_bind, Machine.closeProgram_sample, Machine.closeProgram_pure,
    map_bind, map_pure, Function.comp_apply, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_unifFin, PMF.map_bind, PMF.pure_map]
  rfl

/-! ### Halted-Recipient No-Op vs Reply vs Yield -/

private abbrev resumeCountEnv : ReactiveNode 2 Unit where
  State := ℕ
  init := pure 0
  handle
    | .start _, n => pure (.write 1 .input (), n)
    | .resume, n =>
      if n + 1 ≥ 2 then pure (.halt true, n + 1)
      else pure (.write 1 .input (), n + 1)
    | .deliver _, n => pure (.halt false, n)

private abbrev haltingPeer : ReactiveNode 2 Unit where
  State := ℕ
  init := pure 0
  handle := fun _ k => pure (.halt false, k + 1)

private abbrev replyingPeer : ReactiveNode 2 Unit where
  State := ℕ
  init := pure 0
  handle := fun _ k => pure (.write 0 .subroutineOutput (), k + 1)

private abbrev yieldingPeer : ReactiveNode 2 Unit where
  State := ℕ
  init := pure 0
  handle := fun _ k => pure (.yield, k + 1)

private def peerSystem (peer : ReactiveNode 2 Unit) : PushSystem 2 Unit where
  node _
    | 0 => resumeCountEnv
    | 1 => peer
  initial := 0
  control := allowAll

private def state2 (peer : ReactiveNode 2 Unit) (a : ℕ) (b : peer.State) (κ : ℕ) :
    (SSP.parFin ((peerSystem peer).node κ)).State
  | 0 => a
  | 1 => b

private theorem update_state2_0 (peer : ReactiveNode 2 Unit) (a a' : ℕ) (b : peer.State)
    (κ : ℕ) :
    (Function.update (state2 peer a b κ) 0 a' :
      (SSP.parFin ((peerSystem peer).node κ)).State) = state2 peer a' b κ := by
  funext j; fin_cases j <;> rfl

private theorem update_state2_1 (peer : ReactiveNode 2 Unit) (a : ℕ) (b b' : peer.State)
    (κ : ℕ) :
    (Function.update (state2 peer a b κ) 1 b' :
      (SSP.parFin ((peerSystem peer).node κ)).State) = state2 peer a b' κ := by
  funext j; fin_cases j <;> rfl

private theorem init_peerSystem (peer : ReactiveNode 2 Unit) (b₀ : peer.State)
    (hp : peer.init = pure b₀) (κ : ℕ) :
    ∀ j : Fin 2, ((peerSystem peer).node κ j).init = pure (state2 peer 0 b₀ κ j) := by
  intro j; fin_cases j <;> first | rfl | exact hp

private def pEnv01 : Envelope 2 Unit := ⟨0, 1, .input, ()⟩
private def pEnv10 : Envelope 2 Unit := ⟨1, 0, .subroutineOutput, ()⟩

/-- State/log check: after 4 steps with `haltingPeer`, both writes from node `0` are logged, node
`1` is in `ts.halted`, and node `1`'s state counter remains `1` (the second write skipped its
handler and bounced `Delivery.resume` back to `0`). -/
theorem haltingPeer_step4_state (κ : ℕ) (z : List Bool) :
    (SSP.parFin ((peerSystem haltingPeer).node κ)).runFrom
      (OracleComp.iterate 4 (step (peerSystem haltingPeer))
        (TokenState.initialFor (peerSystem haltingPeer).initial z))
      (state2 haltingPeer 0 0 κ) =
      pure ({ target := 0, delivery := .resume, log := [pEnv01, pEnv01],
              halted := {1}, output := none }, state2 haltingPeer 1 1 κ) := by
  rw [runFrom_iterate_step_succ_of_handle_eq_pure (peerSystem haltingPeer) κ 3 rfl
        (by simp [TokenState.initialFor]) rfl (update_state2_0 haltingPeer 0 0 0 κ),
      runFrom_iterate_step_succ_of_handle_eq_pure (peerSystem haltingPeer) κ 2 rfl
        (by simp [TokenState.next, TokenState.initialFor, peerSystem, allowAll])
        rfl (update_state2_1 haltingPeer 0 0 1 κ),
      runFrom_iterate_step_succ_of_handle_eq_pure (peerSystem haltingPeer) κ 1 rfl
        (by simp [TokenState.next, TokenState.initialFor, peerSystem, allowAll])
        rfl (update_state2_0 haltingPeer 0 1 1 κ),
      runFrom_iterate_step_succ_of_mem_halted _ κ 0 rfl
        (by simp [TokenState.next, TokenState.initialFor, peerSystem, allowAll])]
  rw [OracleComp.iterate_zero, Machine.runFrom_pure]
  rfl

/-- End-to-end halted-recipient check: on step 5, `resumeCountEnv` receives the second `resume` and
halts with `true`. -/
theorem haltingPeer_exec (κ : ℕ) (z : List Bool) (extra : ℕ) :
    (pushExec (peerSystem haltingPeer) κ z (5 + extra)).eval = PMF.pure true := by
  rw [pushExec, ProbComp.eval_map,
    eval_pushRun_of_init_pure _ κ z (5 + extra) (state2 haltingPeer 0 0 κ)
      (init_peerSystem haltingPeer 0 rfl κ),
    show 5 + extra = 4 + (extra + 1) by omega]
  rw [OracleComp.iterate_add, Machine.runFrom_bind, haltingPeer_step4_state]
  change PMF.map (fun r => r.getD false) (((TokenState.output ∘ Prod.fst) <$> Machine.closeProgram
    ((SSP.parFin ((peerSystem haltingPeer).node κ)).runFrom
      (OracleComp.iterate (extra + 1) (step (peerSystem haltingPeer))
        { target := 0, delivery := .resume, log := [pEnv01, pEnv01],
          halted := {1}, output := none })
      (state2 haltingPeer 1 1 κ))).eval) = _
  rw [runFrom_iterate_step_succ_of_handle_eq_pure (peerSystem haltingPeer) κ extra rfl (by simp)
        rfl (update_state2_0 haltingPeer 1 2 1 κ)]
  rw [runFrom_iterate_step_of_output_isSome _ κ extra rfl]
  simp only [Machine.closeProgram_pure, map_pure, Function.comp_apply, ProbComp.eval_pure,
    PMF.pure_map]
  rfl

/-- Replying-peer contrast: replacing `haltingPeer` with `replyingPeer` sends a message back to
`0`, so `resumeCountEnv` halts with `false` in 3 steps. -/
theorem replyingPeer_exec (κ : ℕ) (z : List Bool) (extra : ℕ) :
    (pushExec (peerSystem replyingPeer) κ z (3 + extra)).eval = PMF.pure false := by
  rw [pushExec, ProbComp.eval_map,
    eval_pushRun_of_init_pure _ κ z (3 + extra) (state2 replyingPeer 0 0 κ)
      (init_peerSystem replyingPeer 0 rfl κ),
    show 3 + extra = (extra + 2) + 1 by omega,
    runFrom_iterate_step_succ_of_handle_eq_pure (peerSystem replyingPeer) κ (extra + 2) rfl
      (by simp [TokenState.initialFor]) rfl (update_state2_0 replyingPeer 0 0 0 κ),
    runFrom_iterate_step_succ_of_handle_eq_pure (peerSystem replyingPeer) κ (extra + 1) rfl
      (by simp [TokenState.next, TokenState.initialFor, peerSystem, allowAll])
      rfl (update_state2_1 replyingPeer 0 0 1 κ),
    runFrom_iterate_step_succ_of_handle_eq_pure (peerSystem replyingPeer) κ extra rfl
      (by simp [TokenState.next, TokenState.initialFor, peerSystem, allowAll])
      rfl (update_state2_0 replyingPeer 0 0 1 κ)]
  rw [runFrom_iterate_step_of_output_isSome _ κ extra rfl]
  simp only [Machine.closeProgram_pure, map_pure, Function.comp_apply, ProbComp.eval_pure,
    PMF.pure_map]
  rfl

/-- Yielding-peer contrast: unlike `haltingPeer`, `yieldingPeer` is not added to `ts.halted`, so
on the second write its handler runs a second time (state counter reaches `2`, vs `1` for
`haltingPeer`). -/
theorem yieldingPeer_step4_state (κ : ℕ) (z : List Bool) :
    (SSP.parFin ((peerSystem yieldingPeer).node κ)).runFrom
      (OracleComp.iterate 4 (step (peerSystem yieldingPeer))
        (TokenState.initialFor (peerSystem yieldingPeer).initial z))
      (state2 yieldingPeer 0 0 κ) =
      pure ({ target := 0, delivery := .resume, log := [pEnv01, pEnv01],
              halted := ∅, output := none }, state2 yieldingPeer 1 2 κ) := by
  rw [runFrom_iterate_step_succ_of_handle_eq_pure (peerSystem yieldingPeer) κ 3 rfl
        (by simp [TokenState.initialFor]) rfl (update_state2_0 yieldingPeer 0 0 0 κ),
      runFrom_iterate_step_succ_of_handle_eq_pure (peerSystem yieldingPeer) κ 2 rfl
        (by simp [TokenState.next, TokenState.initialFor, peerSystem, allowAll])
        rfl (update_state2_1 yieldingPeer 0 0 1 κ),
      runFrom_iterate_step_succ_of_handle_eq_pure (peerSystem yieldingPeer) κ 1 rfl
        (by simp [TokenState.next, TokenState.initialFor, peerSystem, allowAll])
        rfl (update_state2_0 yieldingPeer 0 1 1 κ),
      runFrom_iterate_step_succ_of_handle_eq_pure (peerSystem yieldingPeer) κ 0 rfl
        (by simp [TokenState.next, TokenState.initialFor, peerSystem, allowAll])
        rfl (update_state2_1 yieldingPeer 1 1 2 κ)]
  rw [OracleComp.iterate_zero, Machine.runFrom_pure]
  rfl

/-! ### Structural & Query-Bound Checks -/

example (κ : ℕ) (z : List Bool) :
    (pushRun (pingPongSystem pongNode allowAll) κ z 0).eval = PMF.pure none ∧
      (pushExec (pingPongSystem pongNode allowAll) κ z 0).eval = PMF.pure false := by
  refine ⟨eval_pushRun_zero _ κ z, ?_⟩
  rw [pushExec, ProbComp.eval_map, eval_pushRun_zero, PMF.pure_map]
  rfl

example (f : ℕ) (z : List Bool) :
    OracleComp.IsQueryBounded
      (OracleComp.iterate f (step (pingPongSystem pongNode allowAll))
        (TokenState.initialFor 0 z)) f :=
  isQueryBounded_iterate_step (pingPongSystem pongNode allowAll) f (TokenState.initialFor 0 z)

/-- Forward-compatibility check: a `PushSystem` readily hosts `κ`-dependent reactive nodes
whose state type and handler depend on the security parameter `κ`. -/
private def κParamSystem : PushSystem 1 ℕ where
  node κ _ := {
    State := Fin (κ + 1)
    init := pure ⟨0, Nat.succ_pos κ⟩
    handle := fun _ s => pure (.halt (decide (s.val ≤ κ)), s)
  }
  initial := 0
  control := allowAll

private def κInitState (κ : ℕ) : (SSP.parFin (κParamSystem.node κ)).State :=
  fun _ => ⟨0, Nat.succ_pos κ⟩

private theorem update_κInitState (κ : ℕ) :
    (Function.update (κInitState κ) 0 ⟨0, Nat.succ_pos κ⟩ :
      (SSP.parFin (κParamSystem.node κ)).State) = κInitState κ := by
  funext j; fin_cases j; rfl

example (κ : ℕ) (z : List Bool) :
    (pushExec κParamSystem κ z 1).eval = PMF.pure true := by
  rw [pushExec, ProbComp.eval_map,
    eval_pushRun_of_init_pure κParamSystem κ z 1 (κInitState κ) (fun _ => rfl),
    runFrom_iterate_step_succ_of_handle_eq_pure κParamSystem κ 0 rfl
      (by simp [TokenState.initialFor]) rfl (update_κInitState κ)]
  rw [OracleComp.iterate_zero, Machine.runFrom_pure]
  simp only [Machine.closeProgram_pure, map_pure, Function.comp_apply, ProbComp.eval_pure,
    PMF.pure_map, TokenState.next, κParamSystem, TokenState.initialFor, κInitState]
  simp

end CslibFrontierTests.Crypto.UCPushExecution
