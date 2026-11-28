/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Encoding.Basic
public import CslibFrontier.Computability.Circuit.Simulation
import CslibFrontier.Computability.Circuit.Encoding.Combinators
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Circuit codes for constant-size gate replacements

When each gate is replaced by a block of the same positive size and each block returns its last
gate, the location of every simulated wire follows from its original wire number. The simulating
program concatenates the replacement blocks in source order and substitutes the relocated source
wires for each block's inputs.

## Main definitions

* `Cslib.Circuits.Circuit.simulateWireNumber` gives the wire number after gate replacement.

## Main results

* `Cslib.Circuits.Program.toNat_simulateRenaming_uniform` locates every original wire in the
  replacement program.
* `Cslib.Circuits.Circuit.code_simulate_uniform` gives the gate list and output wires of the
  simulating circuit. Only operations occurring in the source circuit need have the given size.
-/

public section

namespace Cslib.Circuits

universe v w

variable {σ : Signature.{v}} {τ : Signature.{w}} {n g m B : ℕ}

/-- Relocate a wire when each source gate becomes a block of `B` gates returning its last gate. -/
@[expose] def Circuit.simulateWireNumber (n B w : ℕ) : ℕ :=
  if w < n then w else n + (w - n + 1) * B - 1

private abbrev UniformBlock (impl : ∀ op : σ.Op, Circuit τ (σ.Arity op) 1) (B : ℕ)
    (op : σ.Op) : Prop :=
  (impl op).size = B ∧ ((impl op).outputs 0).toNat = σ.Arity op + B - 1

private theorem prefix_uniform (p : Program σ n g) (line : Line σ n g)
    {impl : ∀ op : σ.Op, Circuit τ (σ.Arity op) 1}
    (h : ∀ i, UniformBlock impl B ((p.gate line).lines i).op) (i : Fin g) :
    UniformBlock impl B (p.lines i).op := by
  simpa only [Program.lines_gate_castSucc, Line.mapWires_op] using h i.castSucc

private theorem cost_uniform (p : Program σ n g) (impl : ∀ op : σ.Op, Circuit τ (σ.Arity op) 1)
    (h : ∀ i, UniformBlock impl B (p.lines i).op) :
    p.cost (fun op => (impl op).size) = g * B := by
  rw [Program.cost_eq_sum]
  simp [fun i => (h i).1]

/-- An original program wire is relocated to its fixed block position in the simulation. -/
theorem Program.toNat_simulateRenaming_uniform (p : Program σ n g)
    (impl : ∀ op : σ.Op, Circuit τ (σ.Arity op) 1) (hB : 0 < B)
    (h : ∀ i : Fin g, (impl (p.lines i).op).size = B ∧
      ((impl (p.lines i).op).outputs 0).toNat = σ.Arity (p.lines i).op + B - 1) (w : Wire n g) :
    (p.simulateRenaming impl w).toNat = Circuit.simulateWireNumber n B w.toNat := by
  change ∀ i, UniformBlock impl B (p.lines i).op at h
  induction p with
  | empty => cases w with
    | input i => simp [Program.simulateRenaming, Program.simulate, Circuit.simulateWireNumber]
    | gate j => exact j.elim0
  | @gate g p line ih =>
    have hp := prefix_uniform p line h
    have hl : UniformBlock impl B line.op := by
      simpa only [Program.lines_gate_last, Line.mapWires_op] using h (Fin.last g)
    dsimp only [Program.simulateRenaming, Program.simulate, Program.cost_gate] at ih ⊢
    refine Wire.lastCases ?_ (fun w => ?_) w
    · simp only [Wire.Renaming.apply_gate, Wire.Renaming.skipLast_gates_last,
        Program.appendedWire_toNat, hl.2, Wire.toNat_gate, Fin.val_last]
      have har : ¬ σ.Arity line.op + B - 1 < σ.Arity line.op := by omega
      simp [Program.appendWireCode, har, Circuit.simulateWireNumber, cost_uniform p impl hp,
        Nat.add_mul]
      omega
    · rw [Wire.Renaming.skipLast_castSucc, Wire.toNat_castSucc]
      have hw := (Wire.toNat_castAdd ((p.simulate impl).2 w) (impl line.op).size).trans (ih w hp)
      cases w <;> exact hw

private def blockRows (n B i : ℕ) (impl : ∀ op : σ.Op, Circuit τ (σ.Arity op) 1)
    (source : σ.Op × List ℕ) : List (τ.Op × List ℕ) :=
  (impl source.1).program.code.map fun row =>
    (row.1, row.2.map fun w =>
      if w < σ.Arity source.1 then Circuit.simulateWireNumber n B (source.2.getD w 0)
      else n + i * B + (w - σ.Arity source.1))

private theorem code_simulateProgram (p : Program σ n g)
    (impl : ∀ op : σ.Op, Circuit τ (σ.Arity op) 1) (hB : 0 < B)
    (h : ∀ i, UniformBlock impl B (p.lines i).op) :
    (p.simulateProgram impl).code =
      (List.finRange g).flatMap fun (i : Fin g) => blockRows n B i.val impl (p.lines i).code := by
  induction p with
  | empty => rfl
  | @gate g p line ih =>
    have hp := prefix_uniform p line h
    change ((p.simulateProgram impl).append (p.simulateRenaming impl ∘ line.wires)
      (impl line.op).program).code = _
    rw [Program.code_append, ih hp, List.finRange_succ_last]
    simp only [List.flatMap_append, List.flatMap_map, Program.lines_gate_castSucc,
      Program.lines_gate_last, Line.code_mapWires_castSucc, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, Fin.val_castSucc, Fin.val_last, List.append_cancel_left_eq]
    suffices hf : Program.appendWireCode n (σ.Arity line.op) _
        (p.simulateRenaming impl ∘ line.wires) =
        (fun w => if w < σ.Arity line.op then Circuit.simulateWireNumber n B (line.code.2.getD w 0)
          else n + g * B + (w - σ.Arity line.op)) by
      rw [hf]
      rfl
    funext w
    by_cases hw : w < σ.Arity line.op
    · simp only [Program.appendWireCode, hw, dite_true, ite_true, Function.comp_apply,
        Program.toNat_simulateRenaming_uniform p impl hB hp]
      exact congrArg _ (List.getD_ofFn (fun a => (line.wires a).toNat) ⟨w, hw⟩ 0).symm
    · simp [Program.appendWireCode, hw, cost_uniform p impl hp]

/-- Replace each gate by a block of `B` gates whose sole output is the block's last gate.
Input references in a block read the corresponding relocated source wire. Internal references
read earlier gates of that same block. Output references use the same relocation as input
references. Operations absent from the circuit can have arbitrary implementations. -/
theorem Circuit.code_simulate_uniform (c : Circuit σ n m)
    (impl : ∀ op : σ.Op, Circuit τ (σ.Arity op) 1) (hB : 0 < B)
    (h : ∀ i : Fin c.size, (impl (c.program.lines i).op).size = B ∧
      ((impl (c.program.lines i).op).outputs 0).toNat = σ.Arity (c.program.lines i).op + B - 1) :
    (c.simulate impl).code =
      ((List.finRange c.size).flatMap (fun i =>
        let line := c.program.lines i
        (impl line.op).program.code.map fun row =>
          (row.1, row.2.map fun w =>
            if w < σ.Arity line.op then simulateWireNumber n B (line.code.2.getD w 0)
            else n + i.val * B + (w - σ.Arity line.op))),
        c.code.2.map (simulateWireNumber n B)) := by
  apply Prod.ext
  · exact code_simulateProgram c.program impl hB h
  · simp [Circuit.code, Circuit.simulate, List.map_ofFn, Function.comp_def,
      Program.toNat_simulateRenaming_uniform c.program impl hB h]

end Cslib.Circuits
