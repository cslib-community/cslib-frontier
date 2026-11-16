/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.PrefixLocality
public import CslibFrontier.Computability.Probabilistic.Oracle.Composition
public import CslibFrontier.Computability.Probabilistic.PPT.Composition

/-!
# Public primary-input clock contracts

`IsPPTWithAux` and `IsOraclePPTWithAux` clock a machine in the primary encoded input alone,
independently of its arbitrary auxiliary suffix. Basic machine introduction and semantic
congruence facts accompany the definitions. Prefix-truncation machines and their proofs are
internal implementations exported through the `PPT.AuxClock` facade.
-/

@[expose] public section

namespace Cslib.Probability

open _root_.Turing _root_.Turing.MultiTapeMachine _root_.Turing.MultiTapeTM
  _root_.Turing.MultiTapePTM

variable {Operation α β : Type} [DecidableEq Operation]
  {input : α ↪ List Bool} {output : β ↪ List Bool}

/-- **Closed uniform strict PPT clocked in the primary input.** One finite fair-coin machine runs
on the pair encoding `encPair input encBits (a, z) = frame (input a) ++ z`, clocked by a polynomial
`c * ((input a).length + 1) ^ d` in the primary input length `(input a).length` alone. -/
def IsPPTWithAux {α β : Type} (input : α ↪ List Bool) (output : β ↪ List Bool)
    (program : α → List Bool → ProbComp β) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : Turing.MultiTapePTM k Bool State)
    (c d : ℕ), ∀ a z, (ProbComp.eval (program a z)).map output =
      ProbComp.eval (machine.runClosed (c * ((input a).length + 1) ^ d)
        (encPair input encBits (a, z)))

/-- **Oracle uniform strict PPT clocked in the primary input.** One finite oracle fair-coin machine
runs on `encPair input encBits (a, z) = frame (input a) ++ z`, clocked by a polynomial
`c * ((input a).length + 1) ^ d` in `(input a).length` alone, preserving the full joint output and
external oracle state for every stateful handler. -/
def IsOraclePPTWithAux {Operation α β : Type} [DecidableEq Operation]
    (input : α ↪ List Bool) (output : β ↪ List Bool)
    (program : α → List Bool → WordOracleComp Operation β) : Prop :=
  Finite Operation ∧ ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
    (machine : Turing.MultiTapePTM k Bool Control Operation) (c d : ℕ),
    ∀ a z (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool)) s,
      ProbOracleComp.runWith oracle (output <$> program a z) s =
      ProbOracleComp.runWith oracle
          (machine.runOracle (c * ((input a).length + 1) ^ d) (encPair input encBits (a, z))) s

/-- A fixed finite-control closed machine and polynomial clock in the primary input supply an
`IsPPTWithAux` certificate directly. -/
theorem IsPPTWithAux.of_machine {k : ℕ} {State : Type} [Finite State]
    (machine : Turing.MultiTapePTM k Bool State) (c d : ℕ) :
    IsPPTWithAux input encBits
      (fun a z =>
        machine.runClosed (c * ((input a).length + 1) ^ d) (encPair input encBits (a, z))) := by
  refine ⟨k, State, inferInstance, machine, c, d, fun a z => ?_⟩
  simp only [encBits, Function.Embedding.coe_refl, PMF.map_id]

/-- Distributional equality preserves `IsPPTWithAux`. -/
theorem IsPPTWithAux.congr {program program' : α → List Bool → ProbComp β}
    (h : IsPPTWithAux input output program)
    (heq : ∀ a z, ProbComp.eval (program a z) = ProbComp.eval (program' a z)) :
    IsPPTWithAux input output program' := by
  obtain ⟨k, State, hfinite, machine, c, d, h⟩ := h
  exact ⟨k, State, hfinite, machine, c, d, fun a z =>
    (congrArg (PMF.map output) (heq a z)).symm.trans (h a z)⟩

/-- A fixed finite-control oracle machine and polynomial clock in the primary input supply an
`IsOraclePPTWithAux` certificate directly. -/
theorem IsOraclePPTWithAux.of_machine [Finite Operation] {k : ℕ} {Control : Type} [Finite Control]
    (machine : Turing.MultiTapePTM k Bool Control Operation) (c d : ℕ) :
    IsOraclePPTWithAux input encBits
      (fun a z =>
        machine.runOracle (c * ((input a).length + 1) ^ d) (encPair input encBits (a, z))) := by
  refine ⟨inferInstance, k, Control, inferInstance, machine, c, d, fun a z State oracle s => ?_⟩
  simp only [encBits, Function.Embedding.coe_refl, id_map]

/-- Equality of the complete stateful semantics preserves `IsOraclePPTWithAux`. -/
theorem IsOraclePPTWithAux.congr {program program' : α → List Bool → WordOracleComp Operation β}
    (h : IsOraclePPTWithAux input output program)
    (heq : ∀ a z (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool)) s,
      ProbOracleComp.runWith oracle (program a z) s =
      ProbOracleComp.runWith oracle (program' a z) s) :
    IsOraclePPTWithAux input output program' := by
  obtain ⟨hops, k, Control, hfinite, machine, c, d, h⟩ := h
  refine ⟨hops, k, Control, hfinite, machine, c, d, fun a z State oracle s => ?_⟩
  simpa only [ProbOracleComp.runWith_map, heq] using h a z State oracle s

end Cslib.Probability
