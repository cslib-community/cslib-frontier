/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Emit.Basic

/-!
# Colored source programs

Source instructions distinguish the two color orders of swaps.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Emit.Interpretation.Program`: colored source instructions.
* `Cslib.Complexity.NCL.QBF.Emit.Interpretation.circuit`: emit the source circuit.

## Main results

* `Cslib.Complexity.NCL.QBF.Emit.Interpretation.erase_circuit`: recover the ordinary program.
-/

public section

namespace Cslib.Complexity.NCL.QBF.Emit.Interpretation

/-- Fragment instructions with a separate tag for the red-blue return swap. -/
abbrev Program := List (ℕ × Option Opcode)

/-- Retain an ordinary source instruction under a new interpretation. -/
@[expose] def lift (p : QBF.Emit.Program) : Program := p.map fun i => (i.1, some i.2)

/-- Emit the terminal with red-blue swaps distinguished from scanning swaps. -/
@[expose] def terminal (k p : ℕ) (ms : List (List Bool)) : Program :=
  lift (network (k + 2) (2 * p) ms) ++
    ((List.range (2 * p)).reverse.map fun i => (k + 2 + i, none)) ++
      lift [(k, .returnGate)] ++ lift (List.replicate p (k, .cap))

/-- Emit the complete circuit with both color orders of swaps. -/
@[expose] def circuit (qs : List Quantifier) (ms : List (List Bool)) : Program :=
  lift [(0, .output)] ++ lift (chain 0 qs) ++ terminal 0 qs.length ms

/-- Forget the return swap color, recovering the ordinary source instruction format. -/
@[expose] def erase (p : Program) : Emit.Program :=
  p.map fun i => (i.1, i.2.getD .swap)

/-- Forgetting swap colors cancels the lift of ordinary source instructions. -/
theorem erase_lift (p : Emit.Program) : erase (lift p) = p := by
  simp [erase, lift, List.map_map, Function.comp_def]

/-- Forgetting swap colors recovers the ordinary terminal instructions. -/
theorem erase_terminal (k p : ℕ) (ms : List (List Bool)) :
    erase (terminal k p ms) = Emit.terminal k p ms := by
  simp [terminal, Emit.terminal, erase, lift, List.map_map,
    Function.comp_def]

/-- Forgetting swap colors recovers the ordinary complete circuit instructions. -/
theorem erase_circuit (qs : List Quantifier) (ms : List (List Bool)) :
    erase (circuit qs ms) = Emit.circuit qs ms := by
  simp only [circuit, Emit.circuit, erase, List.map_append]
  change erase (lift _) ++ erase (lift _) ++ _ = _
  rw [erase_lift, erase_lift]
  exact congrArg (fun p => [(0, Opcode.output)] ++ chain 0 qs ++ p)
    (erase_terminal 0 qs.length ms)

end Cslib.Complexity.NCL.QBF.Emit.Interpretation
