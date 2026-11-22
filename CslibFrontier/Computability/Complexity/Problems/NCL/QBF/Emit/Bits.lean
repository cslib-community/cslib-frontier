/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Bits
public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Emit
public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Emit.Interpretation.Bits

/-!
# Emitting initial and target configurations

Each fixed fragment contributes a fixed bit list. The output fragment carries the record bit;
the remaining fragments initialize quantifier memories and the inactive matrix network.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Emit.Opcode.configurationBits`: a fixed fragment's configuration.
* `Cslib.Complexity.NCL.QBF.Emit.configurationBits`: concatenate fragment configurations.

## Main results

* `Cslib.Complexity.NCL.QBF.Emit.configurationBits_body`: canonical expanded body configurations.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Emit

/-- The created-edge directions in the canonical initial configuration of a fixed fragment. -/
@[expose] def Opcode.configurationBits (recorded : Bool) : Opcode → List Bool
  | .output => Gate.extendedBits OutputLatch.diagram
      (OutputLatch.canonical recorded true false).orient
  | .ex => Gate.extendedBits existsGadget Initial.existsInitial.orient
  | .all => Gate.extendedBits forallGadget Initial.forallInitial.orient
  | .tapFirst => Gate.extendedBits Network.tapFirst (fun _ => false)
  | .tap => Gate.extendedBits Network.tap (fun _ => false)
  | .conj => Gate.extendedBits Network.conj (fun _ => false)
  | .returnGate => Gate.extendedBits Matrix.returnGate Initial.returnInitial.orient
  | .cap => Gate.extendedBits (.gen Gate.cap) (fun _ => false)
  | .start => Gate.extendedBits (.gen Gate.start) (fun _ => false)
  | .fixed => Gate.extendedBits (Gate.node [] [.blue]) (fun _ => false)
  | .swap => []

/-- Concatenate the fixed fragment configurations in edge-creation order. -/
@[expose] def configurationBits (recorded : Bool) (p : Program) : List Bool :=
  p.flatMap fun i => i.2.configurationBits recorded

/-- Appending instruction lists concatenates their configuration bits. -/
theorem configurationBits_append (recorded : Bool) (p q : Program) :
    configurationBits recorded (p ++ q) =
      configurationBits recorded p ++ configurationBits recorded q := List.flatMap_append

/-- One instruction contributes the fixed bit list of its fragment. -/
theorem configurationBits_singleton (recorded : Bool) (k : ℕ) (op : Opcode) :
    configurationBits recorded [(k, op)] = op.configurationBits recorded :=
  List.flatMap_singleton _ _

/-- Forgetting swap colors preserves the ordinary primitive configuration bits. -/
theorem configurationBits_erase (recorded : Bool) (p : Interpretation.Program) :
    Interpretation.configurationBits Gate.bitMap recorded p =
      configurationBits recorded (Interpretation.erase p) := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    simp only [Interpretation.configurationBits, Interpretation.erase, List.map_cons,
      List.flatMap_cons, configurationBits]
    change _ ++ Interpretation.configurationBits Gate.bitMap recorded p =
      _ ++ configurationBits recorded (Interpretation.erase p)
    rw [ih]
    congr 1
    rcases i with ⟨k, op⟩
    cases op with
    | none => rfl
    | some op => cases op <;> rfl

/-- Chain and terminal instruction bits agree with the canonical expanded body configuration. -/
theorem configurationBits_body (recorded : Bool) (qs : List Quantifier) (ms : List (List Bool)) :
    configurationBits recorded (chain 0 qs ++ terminal 0 qs.length ms) =
      Gate.extendedBits (Matrix.body qs ms) (Initial.body qs ms).orient := by
  have h := Interpretation.configurationBits_body Gate.bitMap recorded qs ms
  rw [configurationBits_erase] at h
  have he : Interpretation.erase
      (Interpretation.lift (chain 0 qs) ++ Interpretation.terminal 0 qs.length ms) =
      chain 0 qs ++ terminal 0 qs.length ms := by
    unfold Interpretation.erase
    rw [List.map_append]
    change Interpretation.erase (Interpretation.lift _) ++ Interpretation.erase _ = _
    rw [Interpretation.erase_lift, Interpretation.erase_terminal]
  rw [he] at h
  exact h

end Cslib.Complexity.NCL.QBF.Emit
