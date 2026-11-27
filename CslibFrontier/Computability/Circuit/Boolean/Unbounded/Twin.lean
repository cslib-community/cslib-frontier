/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AltFormula
public import Cslib.Computability.Circuit.Depth

/-!
# Pushing negations to the inputs of unbounded fan-in circuits

Every circuit over the unbounded fan-in basis (negation, and conjunction and disjunction of any
number of arguments) is equivalent to a circuit **without negation gates** that reads the `2 n`
literals `x₀, …, x_{n-1}, ¬x₀, …, ¬x_{n-1}` (`AltFormula.literals`), with twice as many gates and
the same depth [Arora and Barak, Exercise 13.1][AroraBarak07].

The construction gives every gate a *twin* computing its negation, as the exercise's hint says. Gate
`j` becomes gates `2 j` (its value) and `2 j + 1` (its negation); an input `i` is carried by the
literal inputs `i` and `n + i` (`twinWire`). A conjunction becomes the conjunction of the positive
rails and the disjunction of the negative rails, a disjunction dually, and a negation becomes two
disjunctions of one argument reading the crossed rails of its argument (`twinLine`). Every rail has
exactly the depth of the wire it carries (`wireDepths_twinProgram`), because a negation gate is
replaced by a gate of the same depth.

This is the twin construction of `Monotone.dualRail` (fan-in two, De Morgan basis) for unbounded
fan-in, where the depth statement is what the exercise asks for.

## Main definitions

* `Cslib.Circuits.Boolean.Unbounded.twinWire`: the positive and the negative rail of a wire.
* `Cslib.Circuits.Boolean.Unbounded.twinLine`: a gate's positive or negative twin.
* `Cslib.Circuits.Boolean.Unbounded.twinProgram`, `Cslib.Circuits.Boolean.Unbounded.twinCircuit`:
  the translation of programs and circuits.

## Main results

* `Cslib.Circuits.Boolean.Unbounded.eval_twinCircuit`: the translated circuit computes the same
  function on the literals.
* `Cslib.Circuits.Boolean.Unbounded.size_twinCircuit`,
  `Cslib.Circuits.Boolean.Unbounded.depth_twinCircuit`: twice the size, the same depth.
* `Cslib.Circuits.Boolean.Unbounded.op_lines_twinCircuit_ne_not`: no negation gates.
* `Cslib.Circuits.Boolean.Unbounded.exists_notFree_circuit`: Arora–Barak, Exercise 13.1.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, draft of January
  2007][AroraBarak07], Exercise 13.1 (p. 252, PDF p. 268)
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Unbounded

variable {n g m : ℕ}

/-! ### Rails -/

/-- **The rails of a wire**: the positive rail (`b = true`) and the negative rail (`b = false`).
Input `i` is carried by the literal inputs `i` and `n + i`; gate `j` by the gates `2 j` and
`2 j + 1`. -/
def twinWire (b : Bool) : Wire n g → Wire (n + n) (2 * g)
  | .input i => .input (if b then Fin.castAdd n i else Fin.natAdd n i)
  | .gate j => .gate ⟨2 * j + if b then 0 else 1, by split <;> omega⟩

/-- **The twin of a gate** with positive (`b = true`) or negative (`b = false`) polarity. A
conjunction becomes the conjunction of the positive rails or the disjunction of the negative
rails, a disjunction dually; a negation becomes the disjunction of one argument reading the
crossed rail of its argument. -/
def twinLine (b : Bool) : Line signature n g → Line signature (n + n) (2 * g)
  | ⟨.not, ws⟩ => ⟨.or 1, fun _ => twinWire (!b) (ws (0 : Fin 1))⟩
  | ⟨.and k, ws⟩ => if b then ⟨.and k, twinWire true ∘ ws⟩ else ⟨.or k, twinWire false ∘ ws⟩
  | ⟨.or k, ws⟩ => if b then ⟨.or k, twinWire true ∘ ws⟩ else ⟨.and k, twinWire false ∘ ws⟩

/-- No twin is a negation gate. -/
theorem op_twinLine_ne_not (b : Bool) (l : Line signature n g) : (twinLine b l).op ≠ .not := by
  obtain ⟨_ | _ | _, ws⟩ := l <;> cases b <;> simp [twinLine]

/-- **The twin translation of a program**: every gate followed by its negative twin. -/
def twinProgram : {g : ℕ} → Program signature n g → Program signature (n + n) (2 * g)
  | _, .empty => .empty
  | _, .gate p l =>
    ((twinProgram p).gate (twinLine true l)).gate ((twinLine false l).mapWires Wire.castSucc)

@[simp] theorem twinProgram_empty : twinProgram (.empty : Program signature n 0) = .empty := rfl

theorem twinProgram_gate (p : Program signature n g) (l : Line signature n g) :
    twinProgram (p.gate l) =
      ((twinProgram p).gate (twinLine true l)).gate
        ((twinLine false l).mapWires Wire.castSucc) := rfl

/-- The rails of an old wire, seen in the twin program of one more gate. -/
theorem twinWire_castSucc (b : Bool) (w : Wire n g) :
    (twinWire b w.castSucc : Wire (n + n) (2 * (g + 1))) = (twinWire b w).castSucc.castSucc := by
  cases w with
  | input i => rfl
  | gate j => simp only [twinWire, Wire.castSucc_gate, Fin.val_castSucc]; rfl

/-- The positive rail of the last gate is the second-to-last twin gate. -/
theorem twinWire_true_last :
    (twinWire true (.gate (Fin.last g)) : Wire (n + n) (2 * (g + 1))) =
      .gate (Fin.last (2 * g)).castSucc := by
  simp only [twinWire, ↓reduceIte, Fin.val_last, Nat.add_zero]
  rfl

/-- The negative rail of the last gate is the last twin gate. -/
theorem twinWire_false_last :
    (twinWire false (.gate (Fin.last g)) : Wire (n + n) (2 * (g + 1))) =
      .gate (Fin.last (2 * g + 1)) := by
  simp only [twinWire, Bool.false_eq_true, ↓reduceIte, Fin.val_last]
  rfl

/-! ### Values -/

/-- Evaluating a twin from rails that carry the right values. -/
theorem eval_twinLine (b : Bool) (l : Line signature n g) (x : BitString n)
    (vals : Fin g → Bool) (y : BitString (n + n)) (ys : Fin (2 * g) → Bool)
    (h : ∀ c w, Wire.elim y ys (twinWire c w) = (Wire.elim x vals w == c)) :
    (twinLine b l).eval interpretation y ys = (l.eval interpretation x vals == b) := by
  obtain ⟨_ | k | k, ws⟩ := l <;> cases b <;> rw [Bool.eq_iff_iff] <;>
    simp [twinLine, Line.eval, h]

/-- **The rails carry the values**: on the literals of `x`, the positive rail of a wire carries
its value and the negative rail its negation. -/
theorem trace_twinProgram (p : Program signature n g) (x : BitString n) (b : Bool)
    (w : Wire n g) :
    (twinProgram p).trace interpretation (AltFormula.literals x) (twinWire b w) =
      (p.trace interpretation x w == b) := by
  induction p generalizing b with
  | empty =>
    obtain ⟨i⟩ | ⟨j⟩ := w
    · cases b
      · exact (Fin.append_right x (fun i => !x i) i).trans (by simp)
      · exact (Fin.append_left x (fun i => !x i) i).trans (by simp)
    · exact j.elim0
  | gate p l ih =>
    induction w using Wire.lastCases with
    | castSucc w =>
      rw [twinWire_castSucc, twinProgram_gate, Program.trace_gate_castSucc,
        Program.trace_gate_castSucc, Program.trace_gate_castSucc, ih]
    | last =>
      have hl : ∀ c, (twinLine c l).eval interpretation (AltFormula.literals x)
          ((twinProgram p).eval interpretation (AltFormula.literals x)) =
          (l.eval interpretation x (p.eval interpretation x) == c) :=
        fun c => eval_twinLine c l x _ _ _ fun c w => ih c w
      cases b
      · rw [twinWire_false_last, twinProgram_gate]
        simp only [Program.trace, Wire.elim_gate, Program.eval_gate_last]
        rw [Line.eval_mapWires _ _ _ (AltFormula.literals x) (AltFormula.literals x)
          ((twinProgram p).eval interpretation (AltFormula.literals x)) _ (fun w => by
            cases w <;> simp)]
        exact hl false
      · rw [twinWire_true_last, twinProgram_gate]
        simp only [Program.trace, Wire.elim_gate, Program.eval_gate_castSucc,
          Program.eval_gate_last]
        exact hl true

/-! ### Depth -/

private theorem eq_of_le_add_one_iff {A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (h : ∀ e, A ≤ e + 1 ↔ B ≤ e + 1) : A = B := by
  have h₁ := (h (B - 1)).2 (by omega)
  have h₂ := (h (A - 1)).1 (by omega)
  omega

/-- A twin has the depth of its gate, when every rail has the depth of its wire. -/
theorem depth_twinLine (b : Bool) (l : Line signature n g) (d : Wire n g → ℕ)
    (d' : Wire (n + n) (2 * g) → ℕ) (h : ∀ c w, d' (twinWire c w) = d w) :
    (twinLine b l).depth d' = l.depth d := by
  refine eq_of_le_add_one_iff (Line.depth_pos _ _) (Line.depth_pos _ _) fun e => ?_
  rw [Line.depth_le_add_one_iff, Line.depth_le_add_one_iff]
  obtain ⟨_ | k | k, ws⟩ := l <;> cases b <;> simp [twinLine, h, Fin.forall_fin_one]

/-- **Every rail has the depth of the wire it carries.** -/
theorem wireDepths_twinProgram (p : Program signature n g) (b : Bool) (w : Wire n g) :
    (twinProgram p).wireDepths (twinWire b w) = p.wireDepths w := by
  induction p generalizing b with
  | empty =>
    obtain ⟨i⟩ | ⟨j⟩ := w
    · rfl
    · exact j.elim0
  | gate p l ih =>
    induction w using Wire.lastCases with
    | castSucc w =>
      rw [twinWire_castSucc, twinProgram_gate, Program.wireDepths_gate_castSucc,
        Program.wireDepths_gate_castSucc, Program.wireDepths_gate_castSucc, ih]
    | last =>
      have hl : ∀ c, (twinLine c l).depth (twinProgram p).wireDepths = l.depth p.wireDepths :=
        fun c => depth_twinLine c l _ _ ih
      cases b
      · rw [twinWire_false_last, twinProgram_gate, Program.wireDepths_gateWire,
          Program.depths_gate_last, Program.wireDepths_gateWire, Program.depths_gate_last,
          ← hl false]
        simp only [Line.depth, Line.mapWires_op, Line.mapWires_wires,
          Program.wireDepths_gate_castSucc]
      · rw [twinWire_true_last, twinProgram_gate, Program.wireDepths_gateWire,
          Program.depths_gate_castSucc, Program.depths_gate_last, Program.wireDepths_gateWire,
          Program.depths_gate_last, hl true]

/-- No gate of a twin program is a negation. -/
theorem op_lines_twinProgram_ne_not (p : Program signature n g) (k : Fin (2 * g)) :
    ((twinProgram p).lines k).op ≠ .not := by
  induction p with
  | empty => exact k.elim0
  | gate p l ih =>
    rw [twinProgram_gate] at *
    induction k using Fin.lastCases with
    | last => simpa using op_twinLine_ne_not false l
    | cast k =>
      induction k using Fin.lastCases with
      | last => simpa using op_twinLine_ne_not true l
      | cast k => simpa using ih k

/-! ### Circuits -/

/-- **The twin translation of a circuit**: the twin program, with the positive rails of the
outputs. -/
def twinCircuit (C : Circuit signature n m) : Circuit signature (n + n) m where
  program := twinProgram C.program
  outputs := twinWire true ∘ C.outputs

/-- The translated circuit computes the same function on the literals. -/
theorem eval_twinCircuit (C : Circuit signature n m) (x : BitString n) :
    (twinCircuit C).eval interpretation (AltFormula.literals x) = C.eval interpretation x := by
  funext j
  simp [twinCircuit, Circuit.eval, trace_twinProgram]

/-- The translated circuit has twice as many gates. -/
@[simp] theorem size_twinCircuit (C : Circuit signature n m) :
    (twinCircuit C).size = 2 * C.size := rfl

/-- The translated circuit has the same depth. -/
@[simp] theorem depth_twinCircuit (C : Circuit signature n m) :
    (twinCircuit C).depth = C.depth := by
  have : (twinCircuit C).outputDepths = C.outputDepths := by
    funext j
    exact wireDepths_twinProgram C.program true (C.outputs j)
  simp only [Circuit.depth, this]

/-- The translated circuit has no negation gates. -/
theorem op_lines_twinCircuit_ne_not (C : Circuit signature n m) (k : Fin (twinCircuit C).size) :
    ((twinCircuit C).program.lines k).op ≠ .not :=
  op_lines_twinProgram_ne_not C.program k

/-- **Negations pushed to the inputs** [Arora and Barak, Exercise 13.1][AroraBarak07]. A circuit
over the unbounded fan-in basis of depth `d` with `S` gates computing `f` gives a circuit of depth
`d` with `2 S` gates (the exercise allows `10 S`) and no negation gates computing `f` from the
literals `x₀, …, x_{n-1}, ¬x₀, …, ¬x_{n-1}`. -/
theorem exists_notFree_circuit {f : BitString n → BitString m} {d S : ℕ}
    (C : Circuit signature n m) (hC : C.Computes interpretation f) (hd : C.depth ≤ d)
    (hS : C.size ≤ S) :
    ∃ C' : Circuit signature (n + n) m, (∀ k, (C'.program.lines k).op ≠ .not) ∧
      (∀ x, C'.eval interpretation (AltFormula.literals x) = f x) ∧
      C'.depth ≤ d ∧ C'.size ≤ 2 * S :=
  ⟨twinCircuit C, op_lines_twinCircuit_ne_not C, fun x => (eval_twinCircuit C x).trans (hC x),
    by simpa using hd, by simpa using hS⟩

end Cslib.Circuits.Boolean.Unbounded
