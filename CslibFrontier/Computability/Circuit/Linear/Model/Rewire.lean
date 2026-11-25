/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Linear.Model.Basic
public import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic.Ring

/-!
# Reindexing and scaling linear circuits

Input weights are absorbed in the incident gates, and output weights in the readouts.
Row selection and restriction to an injectively indexed subset of the columns also preserve
a gate budget, including when every input is deleted.

Adapted from `CircuitReindex` of the Lean release accompanying [OpenAI2026FiniteFourier].
-/

public section

namespace Cslib.Circuit.Linear

variable {K I I' O O' W W' : Type*}

section Semiring

variable [Semiring K]

/-- Substitute a scaled wire at both sources of a gate. -/
private def BinaryGate.rewire (g : BinaryGate K W) (f : W → K × W') : BinaryGate K W' where
  left := (f g.left).2
  right := (f g.right).2
  leftCoeff := g.leftCoeff * (f g.left).1
  rightCoeff := g.rightCoeff * (f g.right).1

private theorem BinaryGate.eval_rewire (g : BinaryGate K W) (f : W → K × W') (v : W' → K) :
    (g.rewire f).eval v = g.eval (fun w => (f w).1 * v (f w).2) := by
  simp [rewire, eval, mul_assoc]

/-- Substitute at the source of a free readout and multiply its coefficient. -/
private def Readout.rewire (r : Readout K W) (z : K) (f : W → K × W') : Readout K W' :=
  match r with
  | .zero => .zero
  | .scaled c w => .scaled (z * c * (f w).1) (f w).2

private theorem Readout.eval_rewire (r : Readout K W) (z : K) (f : W → K × W') (v : W' → K) :
    (r.rewire z f).eval v = z * r.eval (fun w => (f w).1 * v (f w).2) := by
  cases r <;> simp [rewire, eval, mul_assoc]

/-- A substitution on inputs acts identically on internal state wires. -/
private def Program.wireMap {r : ℕ} (f : I → K × I') : I ⊕ Fin r → K × (I' ⊕ Fin r)
  | .inl i => ((f i).1, .inl (f i).2)
  | .inr j => (1, .inr j)

/-- Relabel and scale input wires, at identical gate count. -/
private def Program.rewire (f : I → K × I') : {r : ℕ} → Program K I r → Program K I' r
  | _, .nil => .nil
  | _, .step p g => .step (p.rewire f) (g.rewire (wireMap f))

private theorem Program.value_rewire {r : ℕ} (p : Program K I r) (f : I → K × I') (x : I' → K) :
    (p.rewire f).value x = p.value (fun i => (f i).1 * x (f i).2) := by
  induction p with
  | nil => rfl
  | step p g ih =>
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · change (g.rewire (wireMap f)).eval _ = g.eval _
      rw [BinaryGate.eval_rewire]
      congr 1
      funext w
      cases w <;> simp [wireMap, ih]
    · exact congrFun ih k

/-- A circuit with relabeled, scaled inputs and relabeled, scaled outputs. -/
def LinearCircuit.rewire {s : ℕ} (p : LinearCircuit K I O s) (f : I → K × I') (g : O' → K × O) :
    LinearCircuit K I' O' s where
  program := p.program.rewire f
  output o := (p.output (g o).2).rewire (g o).1 (Program.wireMap f)

/-- Evaluation commutes with substitution and scaling of wires. -/
theorem LinearCircuit.eval_rewire {s : ℕ} (p : LinearCircuit K I O s)
    (f : I → K × I') (g : O' → K × O)
    (x : I' → K) (o : O') :
    (p.rewire f g).eval x o = (g o).1 * p.eval (fun i => (f i).1 * x (f i).2) (g o).2 := by
  simp only [eval, rewire, Readout.eval_rewire, Program.value_rewire]
  congr 2
  funext w
  cases w <;> simp [Program.wireMap]

end Semiring

section

variable [CommSemiring K]

private theorem programValue_scale {s : ℕ} (p : Program K I s) (v : I → K) (a : K) :
    p.value (fun j => a * v j) = fun j => a * p.value v j := by
  induction p with
  | nil => funext j; exact j.elim0
  | step p g ih =>
    have hw (w : I ⊕ _) : Sum.elim (fun j => a * v j) (p.value (fun j => a * v j)) w =
        a * Sum.elim v (p.value v) w := by cases w <;> simp [ih]
    funext j
    refine Fin.cases ?_ (fun i => congrFun ih i) j
    change g.eval _ = a * g.eval _
    simp only [BinaryGate.eval, hw]
    ring

private theorem circuitEval_scale {s : ℕ} (p : LinearCircuit K I O s) (v : I → K) (a : K) (o : O) :
    p.eval (fun j => a * v j) o = a * p.eval v o := by
  simp only [LinearCircuit.eval, programValue_scale]
  cases p.output o with
  | zero => simp [Readout.eval]
  | scaled c w => cases w <;> simp [Readout.eval] <;> ring

/-- Matrix entries after independent index bijections and diagonal scalings. -/
private theorem LinearCircuit.matrix_rewire_equiv {s : ℕ} (p : LinearCircuit K I O s)
    (eo : O ≃ O') (ei : I ≃ I')
    (a : I → K) (b : O' → K) (o : O') (i : I') :
    (p.rewire (fun j => (a j, ei j)) (fun k => (b k, eo.symm k))).matrix o i =
      b o * (a (ei.symm i) * p.matrix (eo.symm o) (ei.symm i)) := by
  classical
  unfold LinearCircuit.matrix
  rw [eval_rewire]
  have he : (fun j : I => a j * (Pi.single i (1 : K) : I' → K) (ei j)) =
      fun j => a (ei.symm i) * (Pi.single (ei.symm i) (1 : K) : I → K) j := by
    funext j
    by_cases h : j = ei.symm i
    · simp [h]
    · simp [h, (ei.eq_symm_apply.not).mp h]
  change b o * p.eval (fun j => a j * (Pi.single i (1 : K) : I' → K) (ei j)) (eo.symm o) = _
  rw [he, circuitEval_scale]

/-- Input and output permutations cost no binary gates. -/
theorem RealizableAtMost.reindex {M : Matrix O I K} {s : ℕ} (h : RealizableAtMost M s)
    (eo : O ≃ O') (ei : I ≃ I') : RealizableAtMost (Matrix.reindex eo ei M) s := by
  obtain ⟨r, hr, p, rfl⟩ := h
  refine ⟨r, hr, p.rewire (fun i => (1, ei i)) (fun o => (1, eo.symm o)), ?_⟩
  ext o i
  simpa [Matrix.reindex] using p.matrix_rewire_equiv eo ei (fun _ => 1) (fun _ => 1) o i

/-- Diagonal scaling can be folded into existing gates and readouts. -/
theorem RealizableAtMost.diagonal {M : Matrix O I K} {s : ℕ} (h : RealizableAtMost M s)
    (b : O → K) (a : I → K) :
    RealizableAtMost (Matrix.of fun o i => b o * (a i * M o i)) s := by
  obtain ⟨r, hr, p, rfl⟩ := h
  refine ⟨r, hr, p.rewire (fun i => (a i, i)) (fun o => (b o, o)), ?_⟩
  ext o i
  exact p.matrix_rewire_equiv (Equiv.refl _) (Equiv.refl _) a b o i

/-- Restrict to an arbitrary selection of output rows and a subset of input columns.
Deleted input coordinates are set to zero in all their incident gates. -/
theorem RealizableAtMost.submatrix {M : Matrix O I K} {s : ℕ} (h : RealizableAtMost M s)
    (fo : O' → O) (fi : I' ↪ I) : RealizableAtMost (M.submatrix fo fi) s := by
  classical
  cases isEmpty_or_nonempty I' with
  | inl he =>
    exact ⟨0, Nat.zero_le _, ⟨.nil, fun _ => .zero⟩, by ext _ i; exact (he.false i).elim⟩
  | inr hn =>
    let f (j : I) : K × I' :=
      if hj : ∃ i, fi i = j then (1, hj.choose) else (0, hn.some)
    have hf (i : I') (j : I) :
        (f j).1 * (Pi.single i (1 : K) : I' → K) (f j).2 = (Pi.single (fi i) 1 : I → K) j := by
      by_cases hj : ∃ k, fi k = j
      · have hj' := hj.choose_spec
        have hi : hj.choose = i ↔ j = fi i :=
          ⟨fun h => hj'.symm.trans (congrArg fi h), fun h => fi.injective (hj'.trans h)⟩
        simp [f, hj, Pi.single_apply, hi]
      · have hi : j ≠ fi i := fun he => hj ⟨i, he.symm⟩
        simp [f, hj, hi]
    obtain ⟨r, hr, p, rfl⟩ := h
    refine ⟨r, hr, p.rewire f (fun o => (1, fo o)), ?_⟩
    ext o i
    unfold LinearCircuit.matrix
    rw [LinearCircuit.eval_rewire]
    simp [hf, Matrix.submatrix]

/-- Permuting the inputs and outputs preserves the minimum gate count. -/
theorem complexity_reindex [Fintype I] [Fintype O] [Fintype I'] [Fintype O']
    (M : Matrix O I K) (eo : O ≃ O') (ei : I ≃ I') :
    complexity (Matrix.reindex eo ei M) = complexity M := by
  apply le_antisymm
  · exact (complexity_le_iff ..).2 ((realizableAtMost_complexity M).reindex eo ei)
  · apply (complexity_le_iff ..).2
    simpa using (realizableAtMost_complexity (Matrix.reindex eo ei M)).reindex eo.symm ei.symm

end

end Cslib.Circuit.Linear
