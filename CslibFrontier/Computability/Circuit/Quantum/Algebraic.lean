/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Output
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import Mathlib.RingTheory.Algebraic.Defs
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Uniform circuits over finite algebraic gate sets

A polynomial-time generator emits a width and a list of labelled gates with their wires.
The unitary for each gate label is fixed across all input lengths and has algebraic entries.

## Main definitions

* `Cslib.Quantum.AlgebraicGateInstruction`: a gate label with its ordered wire list.
* `Cslib.Quantum.UniformAlgebraicCircuitFamily`: the uniform circuit model.
* `Cslib.Quantum.UniformAlgebraicCircuitFamily.answerProb`: probability of a flagged answer.
-/

@[expose] public section

namespace Cslib.Quantum

open Turing.MultiTapeTM

/-- A gate instruction identifies a gate by its label and gives its ordered list of wires. -/
structure AlgebraicGateInstruction where
  /-- Gate label in the family's finite gate set. -/
  label : ℕ
  /-- Wires on which the gate is placed, in its local wire order. -/
  wires : List ℕ

/-- Encode the gate label and the ordered wire indices in unary. -/
enc_structure encAlgebraicGateInstruction : AlgebraicGateInstruction where
  label : encUnary, wires : (encList encUnary)

/-- A uniform family of circuits over finitely many algebraic gates. Width and instructions
are generated from the input length in unary. The first two wires encode the answer and an
indicator that an answer was returned. -/
structure UniformAlgebraicCircuitFamily where
  /-- Number of labels in the fixed gate set. -/
  gateCount : ℕ
  /-- Arity of each gate. -/
  arity : Fin gateCount → ℕ
  /-- Gate assigned to each label. -/
  gate : (i : Fin gateCount) → Gate (arity i)
  algebraic : ∀ i x y, IsAlgebraic ℚ ((gate i).val x y)
  /-- Register width at each input length. -/
  width : ℕ → ℕ
  /-- Gate instructions in execution order. -/
  instructions : ℕ → List AlgebraicGateInstruction
  computableInPolyTime_width : ComputableInPolyTime width encUnary encUnary
  computableInPolyTime_instructions :
    ComputableInPolyTime instructions encUnary (encList encAlgebraicGateInstruction)
  input_le_width : ∀ n, n ≤ width n
  output_le_width : ∀ n, 2 ≤ width n
  label_lt : ∀ n, ∀ g ∈ instructions n, g.label < gateCount
  wires_length : ∀ n, ∀ g, (h : g ∈ instructions n) →
    g.wires.length = arity ⟨g.label, label_lt n g h⟩
  wires_nodup : ∀ n, ∀ g ∈ instructions n, g.wires.Nodup
  wires_lt : ∀ n, ∀ g ∈ instructions n, ∀ w ∈ g.wires, w < width n

namespace UniformAlgebraicCircuitFamily

/-- Decode the family's certified gate instructions as a circuit on its register. -/
noncomputable def circuit (F : UniformAlgebraicCircuitFamily) (n : ℕ) : Circuit (F.width n) :=
  (F.instructions n).attach.map fun ⟨g, hg⟩ =>
    let label : Fin F.gateCount := ⟨g.label, F.label_lt n g hg⟩
    let wireIndex : Fin (F.arity label) → Fin g.wires.length :=
      Fin.cast (F.wires_length n g hg).symm
    ⟨F.arity label, F.gate label,
      ⟨fun i => ⟨g.wires[wireIndex i], F.wires_lt n g hg _ (List.getElem_mem _)⟩, by
        intro i j h
        have hw' : g.wires[wireIndex i] = g.wires[wireIndex j] := congrArg Fin.val h
        exact Fin.ext ((F.wires_nodup n g hg).getElem_inj_iff.mp hw')⟩⟩

/-- Probability of returning `b` rather than abstaining, using wire one as the answer flag. -/
noncomputable def answerProb (F : UniformAlgebraicCircuitFamily)
    (x : List Bool) (b : Bool) : ℝ :=
  measureProb ((F.circuit x.length).run (inputState (F.width x.length) x))
    (patternAt (F.width x.length) [(0, b), (1, true)])

end UniformAlgebraicCircuitFamily
end Cslib.Quantum
