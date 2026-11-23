/-
Copyright (c) 2026 Samuel Schlesinger, Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.StateTransition

/-!
# Mapping the result of a deterministic client

A result map `g <$> p` runs `p` and applies `g` to its answer. `StateTransitionSpec.runClient_map`
evaluates the map over the entire run, including the final state and the operation history, and
`StateTransitionSpec.clientResult_map` and `StateTransitionSpec.clientState_map` are its answer
and state. The run, the answer and the state (as `StateTransitionSpec.fst_snd_runClient_map`, the
form `simp` indexes) are in `client_simps`, together with `PFunctor.FreeM.map_eq_map`, so
`simp only [client_simps]` handles both spellings `g <$> p` and `p.map g`.

## Main results

* `StateTransitionSpec.runClient_map`, `StateTransitionSpec.clientResult_map`,
  `StateTransitionSpec.clientState_map`, `StateTransitionSpec.fst_snd_runClient_map`: running a
  mapped client.
-/

public section

namespace Cslib.DataStructure.StateTransitionSpec

universe u v w x

variable {D : StateTransitionSpec.{u, v, w}}
  {step : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn step]
  {α β : Type x}

/-- A result map applies the function to the answer and preserves the final state and history. -/
@[client_simps] theorem runClient_map (p : D.Client α) (g : α → β) (s : D.State) :
    D.runClient s (g <$> p) =
      (g (D.clientResult s p), D.clientState s p, D.clientHistory s p) := by
  rw [← bind_pure_comp, ← PFunctor.FreeM.bind_eq_bind, runClient_bind]
  simp only [runClient_pure', List.append_nil]

/-- A mapped client answers with the function applied to the client's answer. -/
@[client_simps] theorem clientResult_map (p : D.Client α) (g : α → β) (s : D.State) :
    D.clientResult s (g <$> p) = g (D.clientResult s p) := by
  rw [clientResult, runClient_map]

/-- A mapped client stops where the client stops. -/
theorem clientState_map (p : D.Client α) (g : α → β) (s : D.State) :
    D.clientState s (g <$> p) = D.clientState s p := by
  rw [clientState, runClient_map]

/-- `clientState_map`, stated in the form that `simp` indexes (see `fst_snd_runClient_bind`). -/
@[client_simps] theorem fst_snd_runClient_map (p : D.Client α) (g : α → β) (s : D.State) :
    (D.runClient s (g <$> p)).2.1 = D.clientState s p :=
  clientState_map p g s

attribute [client_simps] PFunctor.FreeM.map_eq_map

end Cslib.DataStructure.StateTransitionSpec
