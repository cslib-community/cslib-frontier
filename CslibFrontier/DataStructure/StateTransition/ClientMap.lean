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

`StateTransitionSpec.runClient_map` evaluates a result map over an entire run, including its
final state and operation history. Use `simp only [client_simps]` for both `g <$> p` and `p.map g`.
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

attribute [client_simps] PFunctor.FreeM.map_eq_map

end Cslib.DataStructure.StateTransitionSpec
