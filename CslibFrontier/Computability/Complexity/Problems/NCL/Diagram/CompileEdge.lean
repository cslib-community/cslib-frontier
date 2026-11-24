/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Compile

/-!
# Tracking edges through word compilation

A diagram edge keeps its creation-order number when its word is compiled. This connects the
semantic simulations of drawings to the finite graph format used by the decision problems.

## Main definitions

* `Diagram.compileEdgeEquiv`: diagram edges numbered in the compiled finite graph.

## Main results

* `Diagram.compileSimulation_abs`: abstraction reads the compiled representative.
-/

public section

namespace Cslib.Complexity.NCL.Diagram

variable {Γ : List Color → List Color → Type} (I : Interp Γ)

/-- Actual diagram edges numbered in the compiled creation order. -/
@[expose] def compileEdgeEquiv (D : Diagram Γ [] []) :
    D.Edge ≃ Fin (Word.compile (D.toWord I 0)).edgeCount :=
  D.numEquiv.trans (finCongr (by rw [compile_toWord]; rfl))

@[simp] theorem compileEdgeEquiv_val (D : Diagram Γ [] []) (e : D.Edge) :
    (compileEdgeEquiv I D e).val = D.num e := D.numEquiv_val e

private theorem transport_abs {V E : Type*} [DecidableEq E] (G : ConstraintGraph V E)
    {g g' : AndOrGraph} (h : g = g') (S : ConstraintGraph.Simulation G g'.graph)
    (s : Fin g.edgeCount → Bool) (e : E) :
    ((h.symm ▸ S) : ConstraintGraph.Simulation G g.graph).abs s e =
      S.abs (s ∘ finCongr (congrArg AndOrGraph.edgeCount h).symm) e := by
  cases h
  rfl

/-- Compilation reads the representative with the same creation-order edge number. -/
theorem compileSimulation_abs (D : Diagram Γ [] [])
    (s : Fin (Word.compile (D.toWord I 0)).edgeCount → Bool) (e : D.Edge) :
    (compileSimulation I D).abs s e = s (compileEdgeEquiv I D e) := by
  unfold compileSimulation
  rw [transport_abs (D.graph I) (compile_toWord I D)]
  simp only [ConstraintGraph.Simulation.trans, NCL.Simulation.trans, Function.comp_apply,
    finiteSimulation, AndOrGraph.ofFiniteSimulation, ConstraintGraph.Simulation.ofLegalEquiv]
  apply congrArg s
  apply Fin.ext
  rfl

end Cslib.Complexity.NCL.Diagram
