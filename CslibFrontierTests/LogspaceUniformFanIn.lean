/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.UniformFanIn
import CslibFrontier.Computability.Circuit.Encoding.Combinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary

/-! A nullary conjunction gives a uniform family at every input length, including zero.
A binary disjunction may read the same input twice. -/

namespace CslibFrontierTests.LogspaceUniformFanIn

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Turing.MultiTapeTM

private def alwaysTrue (n : ℕ) : Circuit Unbounded.signature n 1 :=
  Circuit.oneGate (.and 0) Fin.elim0

private theorem uniform_alwaysTrue : Circuit.IsLogspaceUniform Unbounded.encOp alwaysTrue := by
  have h := ComputableInLogSpace.id (encIn := encUnary)
  have rows := ComputableInLogSpace.const (encIn := encUnary)
    (encMid := encList (Circuit.encGate Unbounded.encOp)) [(Unbounded.Op.and 0, [])]
  have outputs := ComputableInLogSpace.listSingleton.comp' (ComputableInLogSpace.unaryToBinary h)
  apply (h.pair (rows.pair outputs)).congr
  intro n
  simp [Circuit.encCircuit_apply, alwaysTrue, Circuit.code_oneGate]

example : (Set.univ : Language Bool) ∈ LogspaceUniformNC 2 := by
  apply logspaceUniformAC_subset_NC_succ 1
  refine ⟨alwaysTrue, uniform_alwaysTrue, 1, fun n => ⟨?_, ?_⟩⟩
  · intro x
    funext j
    simp only [alwaysTrue, Circuit.eval_oneGate, Unbounded.interpretation_and, IsEmpty.forall_iff,
      decide_true, single, Language.slice, true_eq_decide_iff]
    trivial
  · simp [alwaysTrue, Circuit.depth_oneGate]

example {n : ℕ} (wire : Fin n) (x : Cslib.BitString n) :
    let c : Circuit Unbounded.signature n 1 := Circuit.oneGate (.or 2) fun _ => wire
    (Unbounded.toFanInTwo c).eval interpretation x 0 = x wire := by
  dsimp only
  rw [Unbounded.eval_toFanInTwo]
  simp [Unbounded.interpretation]

end CslibFrontierTests.LogspaceUniformFanIn
