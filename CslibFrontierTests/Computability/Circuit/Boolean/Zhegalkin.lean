/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin

/-!
# Tests for `CslibFrontier.Computability.Circuit.Boolean.Zhegalkin`

Concrete boundary witnesses for:
- `Matrix.activeSquare` on an asymmetric `2 × 5` Boolean matrix `asymMatrix` (`activeSquare = 5`,
  whereas strict `< Nat.log 2 m` would give `2`, column-log `Nat.log 2 n = 2` would give `8`, and
  the transpose `asymMatrixᵀ` has `activeSquare = 4`).
- `Additive.exists_circuit_matrix_le_bound` over `ℕ` and `Bool` with `s ∤ n` (`n = 5, s = 2`) and an
  all-zero row.
- `Boolean.Zhegalkin` evaluation, `andCost`, `multiplicativeComplexity = 1`, and
  `exists_circuit_of_andCost_le_bound` on `f(x₀, x₁, x₂) = (x₀ ⊕ 1) ∧ (x₁ ⊕ x₂) ⊕ x₀`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Computability.Circuit.Boolean.Zhegalkin

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

/-- Asymmetric `2 × 5` Boolean matrix:
row `0` is `[true, false, false, false, false]` (activates columns `0, 1` at radius `log₂ 2 = 1`),
row `1` is `[false, false, true, false, false]` (activates columns `1, 2, 3` at radius `1`). -/
private def asymMatrix : Matrix (Fin 2) (Fin 5) Bool :=
  Matrix.of fun i j =>
    (i.val = 0 && j.val = 0) || (i.val = 1 && j.val = 2)

/-- Exact boundary check: `asymMatrix.activeSquare = 5` (`2 + 3`).
Using `< Nat.log 2 m` would yield `2`, using `Nat.log 2 n = 2` would yield `3 + 5 = 8`, and
transposing `asymMatrix` yields `4`. -/
example : asymMatrix.activeSquare = 5 := by decide

/-- Asymmetry check: `(asymMatrix.transpose).activeSquare = 4 ≠ 5` (`Nat.log 2 5 = 2`, so row `0`
of `asymMatrixᵀ` activates both columns `0, 1`, row `2` activates both `0, 1`, and rows `1, 3, 4`
are all-zero). -/
example : asymMatrix.transpose.activeSquare = 4 := by decide

/-- `3 × 5` matrix with an all-zero middle row and `s = 2 ∤ 5 = n`, exercising both the partial
tail-block path and the shared `0`-gate path of `Additive.exists_circuit_matrix_le_bound`. -/
private def zeroRowMatrix : Matrix (Fin 3) (Fin 5) Bool :=
  Matrix.of fun i j =>
    (i.val = 0 && (j.val = 0 || j.val = 4)) || (i.val = 2 && j.val = 3)

example :
    ∃ c : Circuit Additive.signature 5 3,
      c.Computes (Additive.interpretation ℕ)
        (fun x i => ∑ j : Fin 5, if zeroRowMatrix i j then x j else 0) ∧
      c.size ≤ Additive.matrixBound zeroRowMatrix 2 2 :=
  Additive.exists_circuit_matrix_le_bound ℕ zeroRowMatrix (by decide) (by decide) (by decide)

/-- Concrete `{⊕, ∧, 1}`-circuit on `3` inputs with `1` conjunction gate computing
`targetFn x = ((x 0 ^^ true) && (x 1 ^^ x 2)) ^^ x 0`:
- gate `0`: `.one` (`true`)
- gate `1`: `.xor (in 0, gate 0)` (`x 0 ^^ true`)
- gate `2`: `.xor (in 1, in 2)` (`x 1 ^^ x 2`)
- gate `3`: `.and (gate 1, gate 2)` (`(x 0 ^^ true) && (x 1 ^^ x 2)`)
- gate `4`: `.xor (gate 3, in 0)` (`((x 0 ^^ true) && (x 1 ^^ x 2)) ^^ x 0`). -/
private def targetFn (x : Fin 3 → Bool) : Bool :=
  ((x 0 ^^ true) && (x 1 ^^ x 2)) ^^ x 0

private def sampleZhegCircuit : Circuit Zhegalkin.signature 3 1 :=
  let p0 : Program Zhegalkin.signature 3 0 := .empty
  let p1 := p0.gate ⟨.one, Fin.elim0⟩
  let p2 := p1.gate ⟨.xor, ![.input 0, .gate 0]⟩
  let p3 := p2.gate ⟨.xor, ![.input 1, .input 2]⟩
  let p4 := p3.gate ⟨.and, ![.gate 1, .gate 2]⟩
  let p5 := p4.gate ⟨.xor, ![.gate 3, .input 0]⟩
  ⟨p5, fun _ => .gate 4⟩

private theorem sampleZhegCircuit_computes :
    sampleZhegCircuit.Computes Zhegalkin.interpretation (single targetFn) := by
  intro x
  funext i
  fin_cases i
  revert x
  decide

private theorem sampleZhegCircuit_andCost :
    sampleZhegCircuit.program.cost Zhegalkin.andCost = 1 := rfl

/-- `targetFn` has multiplicative complexity at most `1`, and in fact equal to `1` because every
`0`-conjunction `{⊕, ∧, 1}`-circuit computes an affine function over `GF(2)` whereas `targetFn` has
degree `2` (`targetFn 000 ⊕ targetFn 100 ⊕ targetFn 010 ⊕ targetFn 110 = true`). -/
example : Zhegalkin.multiplicativeComplexity (single targetFn) = 1 := by
  apply le_antisymm
  · exact (Zhegalkin.multiplicativeComplexity_le_of_computes
      sampleZhegCircuit sampleZhegCircuit_computes).trans_eq sampleZhegCircuit_andCost
  · by_contra hlt
    have h0 : Zhegalkin.multiplicativeComplexity (single targetFn) ≤ 0 := by omega
    obtain ⟨c, hc, hcost⟩ := Zhegalkin.multiplicativeComplexity_le_iff.mp h0
    -- Prove by induction on any `0`-`andCost` program that every wire has even 4-point sum on
    -- `(x₀, x₁)` with `x₂ = false`.
    have haff : ∀ {g : ℕ} (p : Program Zhegalkin.signature 3 g),
        p.cost Zhegalkin.andCost = 0 →
        ∀ w : Wire 3 g,
          ((p.trace Zhegalkin.interpretation ![false, false, false] w ^^
            p.trace Zhegalkin.interpretation ![true, false, false] w) ^^
           (p.trace Zhegalkin.interpretation ![false, true, false] w ^^
            p.trace Zhegalkin.interpretation ![true, true, false] w)) = false := by
      intro g p hp w
      induction p with
      | empty =>
        cases w with
        | gate j => exact j.elim0
        | input i => fin_cases i <;> rfl
      | @gate g q line ih =>
        rw [Program.cost_gate] at hp
        have hq0 : q.cost Zhegalkin.andCost = 0 := by omega
        have hop0 : Zhegalkin.andCost line.op = 0 := by omega
        refine Wire.lastCases ?_ (fun w₀ => ?_) w
        · have hlast (x : Fin 3 → Bool) :
              (q.gate line).trace Zhegalkin.interpretation x (.gate (Fin.last g)) =
                (q.gate line).eval Zhegalkin.interpretation x (Fin.last g) := rfl
          rw [hlast, hlast, hlast, hlast, Program.eval_gate_last, Program.eval_gate_last,
            Program.eval_gate_last, Program.eval_gate_last]
          rcases line with ⟨op, wires⟩
          cases op with
          | one => simp [Line.eval]
          | and => simp [Zhegalkin.andCost] at hop0
          | xor =>
            have hxor4 : ∀ a00 a10 a01 a11 b00 b10 b01 b11 : Bool,
                ((a00 ^^ a10) ^^ (a01 ^^ a11)) = false →
                ((b00 ^^ b10) ^^ (b01 ^^ b11)) = false →
                (((a00 ^^ b00) ^^ (a10 ^^ b10)) ^^ ((a01 ^^ b01) ^^ (a11 ^^ b11))) = false := by
              decide
            exact hxor4 _ _ _ _ _ _ _ _ (ih hq0 (wires 0)) (ih hq0 (wires 1))
        · simp only [Program.trace_gate_castSucc]
          exact ih hq0 w₀
    have hc0 : c.program.cost Zhegalkin.andCost = 0 := Nat.eq_zero_of_le_zero hcost
    have h4 := haff c.program hc0 (c.outputs 0)
    have hev (x : Fin 3 → Bool) :
        c.program.trace Zhegalkin.interpretation x (c.outputs 0) = targetFn x :=
      congrFun (hc x) 0
    rw [hev, hev, hev, hev] at h4
    revert h4
    decide

/-- Instantiating Theorem 1's explicit staged synthesis on `sampleZhegCircuit` preserves
`andCost ≤ 1` and meets `Zhegalkin.totalBound 3 1 2 2`. -/
example :
    ∃ c' : Circuit Zhegalkin.signature 3 1,
      c'.Computes Zhegalkin.interpretation (single targetFn) ∧
      c'.program.cost Zhegalkin.andCost ≤ 1 ∧
      c'.size ≤ Zhegalkin.totalBound 3 1 2 2 := by
  obtain ⟨c', hc', hcost, hsize⟩ :=
    Zhegalkin.exists_circuit_of_andCost_le_bound sampleZhegCircuit sampleZhegCircuit_computes
      (M := 1) (by rw [sampleZhegCircuit_andCost]) (s := 2) (p := 2) (by decide) (by decide)
  exact ⟨c', hc', hcost.trans_eq sampleZhegCircuit_andCost, hsize⟩

end CslibFrontierTests.Computability.Circuit.Boolean.Zhegalkin
