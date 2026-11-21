/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootPortParent
import Mathlib.Tactic.FinCases

open Turing Turing.MultiTapeTM Cslib Cslib.Circuits.Frontier
open RootPredecessorGraph (vertexCount)
open RootPortParent

private def seed : BalancedSchedules.SeededLabels.Seed (vertexCount 0 1 1) 6 := fun _ => 0

private theorem port (column : Bool) (bound e : Fin 2) :
    leaf (k := 0) (q := 1) (copies := 1) 0 seed (0 : Fin 1) 0 column (bound.val + 1) e.val =
      decide (e.val < bound.val + 1) := by
  cases column <;> fin_cases bound <;> fin_cases e <;>
    simp only [leaf, RootPredecessorGraph.inputOfIndices, RootPortQuery.query,
      RootPortQuery.finishInput, RootPredecessorQuery.request, RootPortFinish.run,
      RootPortFinish.symbol, TrinomialArithmetic.runSelected, TrinomialArithmetic.hash4,
      TrinomialArithmetic.eval4, TrinomialArithmetic.mul, TrinomialArithmetic.reduce,
      clmul_eq_foldr_bits, Probability.trinomialStep, Probability.trinomialTargetBits,
      Probability.trinomialStepAux_eq_findGreatest] <;> decide

-- The only original edge is copied once and subdivided. The constant seed puts both endpoints
-- of both parent half-edges in group zero. The child's last port is the second column port,
-- following its two row ports. Its parent index must therefore be one.
example {State : Type} (machine : MultiTapePTM 0 Bool State) (input : List Bool) (b : ℕ)
    (code : MultiTapePTM.BlockLetter 0 State b → Fin 1 → Bool) :
    let es := RootPortGraph.ends (q := 1) machine input b 0 code
    let gs := RootPortGraph.groups (k := 0) (q := 1) (copies := 1) seed (0 : Fin 1)
    3 < (NativeChild.portEdges gs 0 es Prod.fst).length +
        (NativeChild.portEdges gs 0 es Prod.snd).length ∧ NativeChild.parentEdge gs 0 es 3 = 1 := by
  have h₂ : prefixCount (k := 0) (q := 1) (copies := 1) 0 seed (0 : Fin 1) 0 false 2 = 2 := by
    unfold prefixCount
    simp_rw [port false 1]
    decide
  have h₁ : prefixCount (k := 0) (q := 1) (copies := 1) 0 seed (0 : Fin 1) 0 true 1 = 1 := by
    unfold prefixCount
    simp_rw [port true 0]
    decide
  apply (parentEdge_witness_iff_bits (q := 1) machine input b 0 code seed (0 : Fin 1) 0
    (width := 2) (rows := 2) (j := 3) (e := 1) (by decide) (by decide)
    (fun bit => by rw [show RootPredecessorGraph.edgeCount 0 1 1 = 2 by decide, h₂])).mpr
  exact ⟨by decide, Or.inr ⟨port true 1 1, by decide, by decide, fun bit => by rw [h₁]; rfl⟩⟩
