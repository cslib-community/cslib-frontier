/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Encoding.Basic
public import CslibFrontier.Computability.Circuit.MapOp
import Mathlib.Data.List.OfFn

/-!
# Circuit encodings under maps of signatures

## Main results

* `Cslib.Circuits.Circuit.code_mapOp`: mapping the operations maps the gate list and preserves
  the output wires.
* `Cslib.Circuits.Circuit.mapOp_injective`: an injective map of operations induces an injective
  map of circuits.
* `Cslib.Circuits.Program.isCodeFrom_map_iff`: mapping the operations of a gate list keeps it a
  program code.
-/

public section

namespace Cslib.Circuits

variable {σ τ : Signature} (φ : σ.Hom τ) {n g m : ℕ}

/-- The code of a translated line: the translated operation on the same wires. -/
theorem Line.code_mapOp (line : Line σ n g) :
    (line.mapOp φ).code = (φ line.op, line.code.2) := by
  simp only [Line.code, Line.mapOp_op, Line.mapOp_wires, List.ofFn_congr (φ.arity_eq line.op)]
  simp

/-- The code of a translated program: the operations of its gates translated. -/
theorem Program.code_mapOp (p : Program σ n g) :
    (p.mapOp φ).code = p.code.map fun g => (φ g.1, g.2) := by
  induction p with
  | empty => rfl
  | gate p line ih => simp [ih, Line.code_mapOp]

/-- **The code of a translated circuit**: the operations of its gates translated, the same output
wires. -/
theorem Circuit.code_mapOp (c : Circuit σ n m) :
    (c.mapOp φ).code = (c.code.1.map fun g => (φ g.1, g.2), c.code.2) := by
  simp [Circuit.code, Program.code_mapOp]

/-- Translation along an injective map of operations is injective. -/
theorem Circuit.mapOp_injective (hφ : Function.Injective φ) :
    Function.Injective (Circuit.mapOp (n := n) (m := m) φ) := fun c c' h => by
  have hc := congrArg Circuit.code h
  simp only [Circuit.code_mapOp, Prod.mk.injEq] at hc
  exact Circuit.code_injective (Prod.ext (List.map_injective_iff.2
    (fun _ _ hg => Prod.ext (hφ (Prod.mk.inj hg).1) (Prod.mk.inj hg).2) hc.1) hc.2)

/-- **Mapping the operations of a gate list keeps it a program code.** A list of gates is the code
of a program over `τ` after mapping its operations along `φ` exactly when it is one over `σ`. -/
theorem Program.isCodeFrom_map_iff {k : ℕ} {gates : List (σ.Op × List ℕ)} :
    Program.IsCodeFrom τ n k (gates.map fun g => (φ g.1, g.2)) ↔
      Program.IsCodeFrom σ n k gates := by
  induction gates generalizing k with
  | nil => simp
  | cons g gates ih =>
    have ha : τ.Arity (φ g.1) = σ.Arity g.1 := φ.arity_eq g.1
    simp [Program.isCodeFrom_cons, ih, ha]

end Cslib.Circuits
