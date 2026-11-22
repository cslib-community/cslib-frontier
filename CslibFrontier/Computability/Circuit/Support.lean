/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (additions to `Cslib/Computability/Circuit/Program.lean` and `Basic.lean`)
public import Cslib.Computability.Circuit.Basic
public import CslibFrontier.Computability.Circuit.Program
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Function.DependsOn

/-!
# Circuit input support

cslib computes the original inputs that can affect each wire
(`Cslib.Circuits.Program.wireSupport`, `Cslib.Circuits.Circuit.inputSupport`) and proves that
circuit evaluation depends only on those inputs (`Cslib.Circuits.Circuit.dependsOn_eval`); these
were upstreamed from this file in cslib#1181. This file keeps the additions cslib does not have:
the support of a gate and of a designated output, and essential coordinates. An input on which a
function depends essentially (`EssentialAt`) reaches an output of every circuit computing it.

## Main definitions

* `Cslib.Circuits.EssentialAt`: coordinates whose change can change a function.
* `Cslib.Circuits.Program.gateSupport`, `Cslib.Circuits.Circuit.outputSupport`: the structural
  input supports of gates and of designated outputs.

## Main results

* `Cslib.Circuits.EssentialAt.mem_support`: an essential coordinate belongs to every support.
* `Cslib.Circuits.Circuit.Computes.dependsOn`: a computed function depends only on the circuit's
  input support.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {U V : Type*} {n m g : ℕ}

/-- Changing only coordinate `i` can change the value of `f`. -/
def EssentialAt (f : (Fin n → U) → V) (i : Fin n) : Prop :=
  ∃ x y, (∀ k, k ≠ i → x k = y k) ∧ f x ≠ f y

/-- Every essential coordinate belongs to any support of the function. -/
theorem EssentialAt.mem_support {f : (Fin n → U) → V} {support : Finset (Fin n)} {i : Fin n}
    (h : EssentialAt f i) (hf : DependsOn f (support : Set (Fin n))) : i ∈ support := by
  obtain ⟨x, y, hxy, hne⟩ := h
  by_contra hi
  exact hne (hf fun k hk => hxy k fun e => hi (e ▸ hk))

/-- A coordinate is essential exactly when the function does not depend only on the others. -/
theorem essentialAt_iff_not_dependsOn {f : (Fin n → U) → V} {i : Fin n} :
    EssentialAt f i ↔ ¬DependsOn f {i}ᶜ := by
  simp only [EssentialAt, DependsOn, Set.mem_compl_iff, Set.mem_singleton_iff, not_forall,
    exists_prop]


/-- The input support of every gate in a program. -/
def Program.gateSupport (program : Program σ n g) : Fin g → Finset (Fin n) :=
  program.eval (supportInterpretation σ n) (fun i => {i})


/-- A gate-output wire has the support of that gate. -/
@[simp] theorem Program.wireSupport_gate
    (program : Program σ n g)
    (gate : Fin g) :
    program.wireSupport (Wire.gate gate) =
      program.gateSupport gate := rfl


/-- The new gate is supported by precisely the inputs supporting the new line. -/
@[simp] theorem Program.gateSupport_gate_last
    (program : Program σ n g)
    (line : Line σ n g) :
    (program.gate line).gateSupport (Fin.last g) =
      line.inputSupport program.wireSupport :=
  program.eval_gate_last line (supportInterpretation σ n) (fun i => {i})


/-- The input support of every designated output wire in a circuit. -/
def Circuit.outputSupport
    (c : Circuit σ n m) : Fin m → Finset (Fin n) :=
  c.program.wireSupport ∘ c.outputs


/-- Program gates agree whenever their supporting inputs agree. -/
theorem Program.eval_congr
    (program : Program σ n g)
    (interpretation : Interpretation σ U)
    (left right : Fin n → U)
    (k : Fin g)
    (agree : ∀ i ∈ program.gateSupport k, left i = right i) :
    program.eval interpretation left k = program.eval interpretation right k :=
  program.trace_congr interpretation left right (.gate k) agree


/-- A computed function depends only on the circuit's structural input support. -/
theorem Circuit.Computes.dependsOn
    {c : Circuit σ n m}
    {interpretation : Interpretation σ U}
    {target : (Fin n → U) → Fin m → U}
    (computes : c.Computes interpretation target) :
    DependsOn target (c.inputSupport : Set (Fin n)) := by
  intro left right agree
  rw [← computes left, ← computes right]
  exact c.dependsOn_eval interpretation agree


end Cslib.Circuits
