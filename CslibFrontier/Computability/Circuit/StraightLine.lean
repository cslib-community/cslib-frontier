/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Program

/-!
# Programs from closed-form gate values

A construction often describes its gates by a closed formula for each gate value, because that is
how locality and counting arguments read them. `Program.exists_eval_eq_of_lines` turns such a
description into a program: if `line j` is a line whose gate wires point before gate `j`, and
`h x j` is what `line j` computes from the input `x` and the values `h x`, then some program with
those operations has gate values `h x`.

## Main results

* `Cslib.Circuits.Program.exists_eval_eq_of_lines`: a program with prescribed gate values and
  operations, given lines that read only earlier gates.
* `Cslib.Circuits.Program.exists_eval_eq_of_prefixLines`: the same for lines over the gates before
  each one, with gate values indexed by any type through an input map.
-/

public section

namespace Cslib.Circuits

universe v u
variable {σ : Signature.{v}} {U : Type u} {n : ℕ}

/-- **Programs from lines over the gates before each one.** Let `line j` be a line over the gates
before `j`, and let `h x j` be its value on the inputs `input x` and the values `h x` of the earlier
gates, for `x` in any type `X`. Then some program has gate values `h x` on the inputs `input x`,
and its gate `j` performs the operation of `line j`. -/
theorem Program.exists_eval_eq_of_prefixLines {X : Type*} (I : Interpretation σ U)
    (input : X → Fin n → U) :
    ∀ {G : ℕ} (line : (j : Fin G) → Line σ n j) (h : X → Fin G → U),
      (∀ x j, h x j = (line j).eval I (input x) fun t => h x (Fin.castLE j.isLt.le t)) →
      ∃ P : Program σ n G, (∀ x, P.eval I (input x) = h x) ∧ ∀ j, (P.lines j).op = (line j).op
  | 0, _, _, _ => ⟨.empty, fun _ => funext fun j => j.elim0, fun j => j.elim0⟩
  | G + 1, line, h, heval => by
    obtain ⟨P, hP, hop⟩ := Program.exists_eval_eq_of_prefixLines I input
      (fun j => line j.castSucc) (fun x j => h x j.castSucc) fun x j => heval x j.castSucc
    refine ⟨P.gate (line (Fin.last G)), fun x => funext fun j => ?_, fun j => ?_⟩
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [Program.eval_gate_last, hP x, heval x (Fin.last G)]
        rfl
      · rw [Program.eval_gate_castSucc, hP x]
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [Program.lines_gate_last, Line.mapWires_op]
      · rw [Program.lines_gate_castSucc, Line.mapWires_op, hop j]

/-- **Programs from closed-form gate values.** Let `line j` be a line over all `G` gates whose
gate wires point to gates before `j`, and let `h x j` be the value of `line j` on the input `x`
and the gate values `h x`. Then some program on `n` inputs with `G` gates has gate values `h x`,
and its gate `j` performs the operation of `line j`. -/
theorem Program.exists_eval_eq_of_lines (I : Interpretation σ U) {G : ℕ}
    (line : Fin G → Line σ n G) (h : (Fin n → U) → Fin G → U)
    (hearly : ∀ j a t, (line j).wires a = Wire.gate t → t < j)
    (heval : ∀ x j, h x j = (line j).eval I x (h x)) :
    ∃ P : Program σ n G, (∀ x, P.eval I x = h x) ∧ ∀ j, (P.lines j).op = (line j).op := by
  -- The same lines, with every gate wire read among the gates before it.
  let prefixLine (j : Fin G) : Line σ n j :=
    ⟨(line j).op, fun a =>
      match hw : (line j).wires a with
      | .input i => .input i
      | .gate t => .gate ⟨t, hearly j a t hw⟩⟩
  refine Program.exists_eval_eq_of_prefixLines I id prefixLine h fun x j => (heval x j).trans ?_
  simp only [Line.eval, prefixLine]
  congr 1
  funext a
  simp only [Function.comp_apply]
  split <;> rename_i hw <;> simp [hw]

end Cslib.Circuits
