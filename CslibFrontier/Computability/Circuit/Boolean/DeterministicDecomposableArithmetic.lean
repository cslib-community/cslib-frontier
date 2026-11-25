/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.DeterministicDecomposable
public import CslibFrontier.Computability.Circuit.Arithmetic.SyntacticMultilinear
public import CslibFrontier.Computability.Circuit.Simulation
public import CslibFrontier.Foundations.Data.BitString.Sign
public import Mathlib.Data.Fin.VecNotation

/-!
# Arithmetizing deterministic decomposable circuits

Over a commutative ring, replace every AND of a De Morgan circuit by a multiplication, every OR by
an addition and every NOT by `x ↦ 1 - x` (`Cslib.Circuits.Boolean.ringInterpretation`). On the
points `0` and `1` of the ring these agree with the Boolean operations, except that the OR of two
ones is `2`. In a deterministic decomposable circuit (d-D) no OR sees two ones, so the arithmetic
values at the Boolean points are the Boolean values
(`Cslib.Circuits.Program.trace_ringInterpretation_bitPoint`)
[Monet and Olteanu, Section 2][MonetOlteanu2018].

Each operation is computed by a small arithmetic circuit (`Cslib.Circuits.Boolean.arithImpl`): a
multiplication, an addition, a constant, or `1 + (-1) * x` with four gates. Replacing the gates of a
De Morgan circuit by these circuits (`Cslib.Circuits.Circuit.arithmetize`) gives an arithmetic
circuit with at most four times as many gates (`Cslib.Circuits.Circuit.size_arithmetize_le`), which
computes the ring interpretation in every algebra (`Cslib.Circuits.Circuit.eval_arithmetize`).
Decomposable ANDs become multiplications of polynomials in disjoint sets of inputs, so the
arithmetic circuit of a d-D is syntactically multilinear
(`Cslib.Circuits.Circuit.IsDeterministicDecomposable.isDecomposableAt_arithmetize`). It computes the
multilinear extension of the Boolean function of the d-D
(`Cslib.Circuits.Circuit.IsDeterministicDecomposable.eval_arithmetize_X`).

## Main definitions

* `Cslib.Circuits.Boolean.ringInterpretation`: the De Morgan operations in a commutative ring.
* `Cslib.Circuits.Boolean.arithImpl`: an arithmetic circuit for each De Morgan operation.
* `Cslib.Circuits.Circuit.arithmetize`: the arithmetic circuit of a De Morgan circuit.

## Main results

* `Cslib.Circuits.Circuit.size_arithmetize_le`: at most four gates for each gate.
* `Cslib.Circuits.Circuit.eval_arithmetize`: the arithmetic circuit computes the ring
  interpretation.
* `Cslib.Circuits.Program.trace_ringInterpretation_bitPoint`: in a deterministic program the ring
  interpretation agrees with the Boolean one on the Boolean points.
* `Cslib.Circuits.Circuit.IsDeterministicDecomposable.isDecomposableAt_arithmetize`: the arithmetic
  circuit of a d-D is syntactically multilinear.
* `Cslib.Circuits.Circuit.IsDeterministicDecomposable.eval_arithmetize_X`: it computes the
  multilinear extension of the function of the d-D.
* `Cslib.Circuits.Circuit.IsDeterministicDecomposable.exists_syntacticallyMultilinear`: d-Ds
  simulate syntactically multilinear circuits with four gates per gate.

## References

* [M. Monet and D. Olteanu, *Towards Deterministic Decomposable Circuits for Safe
  Queries*][MonetOlteanu2018]
-/

public section

namespace Cslib.Circuits

open MvPolynomial BitString

universe u

variable {n g m : ℕ}

namespace Boolean

/-- The De Morgan operations in a commutative ring: NOT is `x ↦ 1 - x`, AND is multiplication, OR is
addition, and the constants are `0` and `1`. -/
@[expose]
def ringInterpretation (A : Type*) [CommRing A] : Interpretation signature A
  | .const b, _ => bitVal A b
  | .not, x => 1 - x 0
  | .and, x => x 0 * x 1
  | .or, x => x 0 + x 1

variable (R : Type u) [CommRing R]

/-- An arithmetic circuit for each De Morgan operation: a constant gate, `1 + (-1) * x`, a
multiplication or an addition. -/
@[expose]
def arithImpl : ∀ op : Op, Circuit (arithSignature R) (signature.Arity op) 1
  | .const b => ⟨(Program.empty : Program (arithSignature R) 0 0).gate
      ⟨ArithOp.const (bitVal R b), Fin.elim0⟩, fun _ => Wire.gate 0⟩
  | .not => ⟨((((Program.empty : Program (arithSignature R) 1 0).gate
      ⟨ArithOp.const (-1), Fin.elim0⟩).gate ⟨ArithOp.mul, ![Wire.gate 0, Wire.input 0]⟩).gate
      ⟨ArithOp.const 1, Fin.elim0⟩).gate ⟨ArithOp.add, ![Wire.gate 2, Wire.gate 1]⟩,
      fun _ => Wire.gate 3⟩
  | .and => ⟨(Program.empty : Program (arithSignature R) 2 0).gate
      ⟨ArithOp.mul, ![Wire.input 0, Wire.input 1]⟩, fun _ => Wire.gate 0⟩
  | .or => ⟨(Program.empty : Program (arithSignature R) 2 0).gate
      ⟨ArithOp.add, ![Wire.input 0, Wire.input 1]⟩, fun _ => Wire.gate 0⟩

/-- Each replacement circuit has at most four gates. -/
theorem size_arithImpl_le (op : Op) : (arithImpl R op).size ≤ 4 := by
  cases op <;> simp [arithImpl]

/-- Each replacement circuit computes its operation in every `R`-algebra. -/
theorem computes_arithImpl (A : Type*) [CommRing A] [Algebra R A] (op : Op) :
    (arithImpl R op).Computes (arithInterpretationWith R (algebraMap R A))
      (single (ringInterpretation A op)) := by
  intro x
  funext j
  cases op with
  | const b =>
    change algebraMap R A (bitVal R b) = bitVal A b
    cases b <;> simp [bitVal]
  | not =>
    change algebraMap R A 1 + algebraMap R A (-1) * x 0 = 1 - x 0
    simp only [map_one, map_neg]
    ring
  | and => rfl
  | or => rfl

/-- Each replacement circuit unions the supports of its arguments. -/
theorem computes_arithImpl_support (op : Op) :
    (arithImpl R op).Computes (supportInterpretation (arithSignature R) n)
      (single (supportInterpretation signature n op)) := by
  intro S
  funext j
  cases op with
  | const b =>
    change Finset.univ.biUnion (Fin.elim0 : Fin 0 → Finset (Fin n)) = Finset.univ.biUnion S
    simp
  | not =>
    change Finset.univ.biUnion ![Finset.univ.biUnion (Fin.elim0 : Fin 0 → Finset (Fin n)),
      Finset.univ.biUnion ![Finset.univ.biUnion (Fin.elim0 : Fin 0 → Finset (Fin n)), S 0]] =
        Finset.univ.biUnion S
    ext
    simp [Fin.exists_fin_two]
  | and | or =>
    change Finset.univ.biUnion ![S 0, S 1] = Finset.univ.biUnion S
    ext
    simp [Fin.exists_fin_two]

/-- The multiplications of each replacement circuit are decomposable over the supports of its
arguments, when these are disjoint for an AND. -/
theorem decomposesOver_arithImpl (op : Op) (S : Fin (signature.Arity op) → Finset (Fin n))
    (hS : op = .and → Pairwise fun a b => Disjoint (S a) (S b)) :
    (arithImpl R op).program.DecomposesOver (· = .mul) S := by
  cases op with
  | const b => simp [arithImpl]
  | or => simp [arithImpl]
  | not =>
    have h0 : ((Program.empty : Program (arithSignature R) 1 0).gate
        ⟨ArithOp.const (-1), Fin.elim0⟩).wireSupport (Wire.gate 0) = ∅ := by
      change Finset.univ.biUnion (Fin.elim0 : Fin 0 → Finset (Fin 1)) = ∅
      simp
    simp [arithImpl, Program.decomposesOver_gate_iff, Pairwise, Fin.forall_fin_two, h0]
  | and =>
    simp only [arithImpl, Program.decomposesOver_gate_iff, Program.decomposesOver_empty,
      true_and]
    intro _ a b hab
    have := hS rfl hab
    fin_cases a <;> fin_cases b <;> simp_all [Disjoint.symm]

end Boolean

variable (R : Type u) [CommRing R]

/-- The arithmetic circuit of a De Morgan circuit: every gate replaced by its arithmetic circuit
`Boolean.arithImpl`. -/
@[expose]
def Circuit.arithmetize (c : Circuit Boolean.signature n m) : Circuit (arithSignature R) n m :=
  c.simulate (Boolean.arithImpl R)

/-- The arithmetic circuit has at most four gates for each gate. -/
theorem Circuit.size_arithmetize_le (c : Circuit Boolean.signature n m) :
    (c.arithmetize R).size ≤ 4 * c.size :=
  c.program.cost_le_mul (Boolean.size_arithImpl_le R)

/-- The arithmetic circuit computes, in every `R`-algebra, the ring interpretation of the De Morgan
circuit. -/
theorem Circuit.eval_arithmetize (c : Circuit Boolean.signature n m) (A : Type*) [CommRing A]
    [Algebra R A] :
    (c.arithmetize R).eval (arithInterpretationWith R (algebraMap R A)) =
      c.eval (Boolean.ringInterpretation A) :=
  c.eval_simulate _ (Boolean.computes_arithImpl R A)

/-- **Arithmetizing a deterministic program.** If no input makes both arguments of an OR true, the
ring interpretation at the Boolean points is the Boolean value. -/
theorem Program.trace_ringInterpretation_bitPoint (A : Type*) [CommRing A]
    (p : Program Boolean.signature n g) (hp : p.IsDeterministic) (x : Fin n → Bool)
    (w : Wire n g) :
    p.trace (Boolean.ringInterpretation A) (bitPoint x) w =
      bitVal A (p.trace Boolean.interpretation x w) := by
  induction p with
  | empty =>
    cases w with
    | input i => rfl
    | gate k => exact k.elim0
  | gate p line ih =>
    rw [isDeterministic_gate_iff] at hp
    refine Wire.lastCases ?_ (fun w => ?_) w
    · change (p.gate line).eval _ _ (Fin.last _) = bitVal A ((p.gate line).eval _ _ (Fin.last _))
      rw [eval_gate_last, eval_gate_last]
      obtain ⟨op, args⟩ := line
      have harg (a) : p.trace (Boolean.ringInterpretation A) (bitPoint x) (args a) =
          bitVal A (p.trace Boolean.interpretation x (args a)) := ih hp.1 (args a)
      cases op with
      | const b => rfl
      | not =>
        change 1 - p.trace _ _ (args 0) = bitVal A (!p.trace Boolean.interpretation x (args 0))
        rw [harg]
        cases p.trace Boolean.interpretation x (args 0) <;> simp [bitVal]
      | and =>
        change p.trace _ _ (args 0) * p.trace _ _ (args 1) = bitVal A
          (p.trace Boolean.interpretation x (args 0) && p.trace Boolean.interpretation x (args 1))
        rw [harg, harg]
        cases p.trace Boolean.interpretation x (args 0) <;>
          cases p.trace Boolean.interpretation x (args 1) <;> simp [bitVal]
      | or =>
        have hdet : ¬(p.trace Boolean.interpretation x (args 0) = true ∧
            p.trace Boolean.interpretation x (args 1) = true) :=
          hp.2 rfl x (show (0 : Fin 2) ≠ 1 by decide)
        change p.trace _ _ (args 0) + p.trace _ _ (args 1) = bitVal A
          (p.trace Boolean.interpretation x (args 0) || p.trace Boolean.interpretation x (args 1))
        rw [harg, harg]
        revert hdet
        cases p.trace Boolean.interpretation x (args 0) <;>
          cases p.trace Boolean.interpretation x (args 1) <;> simp [bitVal]
    · rw [trace_gate_castSucc, trace_gate_castSucc]
      exact ih hp.1 w

namespace Circuit.IsDeterministicDecomposable

variable {R} {c : Circuit Boolean.signature n m}

/-- **The arithmetic circuit of a d-D is syntactically multilinear**: its multiplications come from
decomposable ANDs and from multiplications by the constant `-1`. -/
theorem isDecomposableAt_arithmetize (hc : c.IsDeterministicDecomposable) :
    (c.arithmetize R).program.IsDecomposableAt (· = .mul) :=
  c.program.isDecomposableAt_simulateProgram _ (Boolean.computes_arithImpl_support R)
    (fun op S hS => Boolean.decomposesOver_arithImpl R op S hS) hc.decomposable

/-- **A d-D computes the multilinear extension of its function.** The polynomial computed by its
arithmetic circuit at each output is the multilinear extension of the Boolean function computed at
that output, with values `0` and `1` in `R`. -/
theorem eval_arithmetize_X (hc : c.IsDeterministicDecomposable) (j : Fin m) :
    (c.arithmetize R).eval (arithInterpretationWith R C) X j =
      multilinearExtension fun x => bitVal R (c.eval Boolean.interpretation x j) := by
  have h := (c.arithmetize R).program.trace_eq_multilinearExtension hc.isDecomposableAt_arithmetize
    id ((c.arithmetize R).outputs j)
  refine h.trans ?_
  congr 1
  funext x
  have := congrFun (congrFun (c.eval_arithmetize R R) (bitPoint x)) j
  simp only [Circuit.eval, Function.comp_apply, Algebra.algebraMap_self] at this
  rw [show arithInterpretationWith R id = arithInterpretationWith R (RingHom.id R) from rfl, this]
  exact c.program.trace_ringInterpretation_bitPoint R hc.deterministic x (c.outputs j)

/-- The arithmetic circuit of a d-D computes the multilinear representative of its function. -/
theorem computesMultilinear_arithmetize {c : Circuit Boolean.signature n 1}
    (hc : c.IsDeterministicDecomposable) :
    (c.arithmetize R).ComputesMultilinear fun z => c.eval Boolean.interpretation z 0 :=
  hc.eval_arithmetize_X 0

/-- **d-Ds simulate syntactically multilinear circuits.** The function of a d-D with `s` gates has
a syntactically multilinear circuit with at most `4 s` gates computing its multilinear
representative, over every commutative ring. -/
theorem exists_syntacticallyMultilinear {c : Circuit Boolean.signature n 1}
    (hc : c.IsDeterministicDecomposable) :
    ∃ A : Circuit (arithSignature R) n 1, A.IsSyntacticallyMultilinear ∧
      (A.ComputesMultilinear fun z => c.eval Boolean.interpretation z 0) ∧ A.size ≤ 4 * c.size :=
  ⟨c.arithmetize R, hc.isDecomposableAt_arithmetize, hc.computesMultilinear_arithmetize,
    c.size_arithmetize_le R⟩

end Circuit.IsDeterministicDecomposable

end Cslib.Circuits
