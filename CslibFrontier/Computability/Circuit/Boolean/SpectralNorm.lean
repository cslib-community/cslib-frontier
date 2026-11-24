/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Simulation
public import CslibFrontier.Foundations.BooleanAnalysis.SpectralNorm
public import CslibFrontier.Foundations.BooleanAnalysis.Granularity

/-!
# Joint Fourier bounds for Boolean circuits

If each primitive Boolean operation has Fourier spectral norm at most `2 ^ cost op`, then
every parity of the input and gate wires of a program has spectral norm at most
`2 ^ program.cost cost`. In particular this bounds each output of a circuit.

The induction keeps a bound on **every character of the whole available wire vector**.
Expanding one new gate in its Fourier basis produces linear combinations of old characters.
Their products are old characters as well, including when a gate reads a wire repeatedly.
Consequently the proof charges each gate once and allows arbitrary sharing and fan-out; it
does not unfold a circuit into a formula. The signature and finite gate arities are arbitrary.

The same joint invariant also controls denominators. If every primitive operation has Fourier
coefficients in `2 ^ (-cost op) ℤ`, every workspace character has coefficients in
`2 ^ (-program.cost cost) ℤ`. The norm and denominator bounds use the same character identities,
but neither bound is inferred from the other.

## Main results

* `Cslib.Circuits.Program.sum_abs_fourierCoeff_chi_trace_le_two_pow_cost`: the joint bound
  for all characters of all currently available wires.
* `Cslib.Circuits.Circuit.sum_abs_fourierCoeff_signVal_eval_le_two_pow_cost`: the resulting
  bound for each circuit output.
* `Cslib.Circuits.Program.exists_fourierCoeff_chi_trace_eq_intCast_div_two_pow_cost`:
  the denominator bound for every workspace character.
* `Cslib.Circuits.Circuit.exists_fourierCoeff_signVal_eval_eq_intCast_div_two_pow_cost`:
  the denominator bound for each circuit output.
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.Circuits

open BitString

variable {σ : Signature} {n g m : ℕ}

private theorem Program.chi_trace_empty (I : Interpretation σ Bool)
    (S : Finset (Wire n 0)) :
    (fun x => chi ℝ S ((Program.empty : Program σ n 0).trace I x)) =
      chi ℝ (projectSet (Wire.elim id Fin.elim0) S) := by
  let π : Wire n 0 → Fin n := Wire.elim id Fin.elim0
  have htrace (x : Fin n → Bool) : (Program.empty : Program σ n 0).trace I x = x ∘ π := by
    funext w
    cases w with
    | input i => rfl
    | gate j => exact j.elim0
  funext x
  rw [htrace]
  exact chi_comp_eq_chi_projectSet π S x

private theorem Program.chi_trace_gate (p : Program σ n g) (line : Line σ n g)
    (I : Interpretation σ Bool) (S : Finset (Wire n (g + 1))) (x : Fin n → Bool) :
    chi ℝ S ((p.gate line).trace I x) =
      chi ℝ (projectSet (Wire.lastCases none some) S)
        (fun o => o.elim (I line.op (p.trace I x ∘ line.wires)) (p.trace I x)) := by
  let π : Wire n (g + 1) → Option (Wire n g) := Wire.lastCases none some
  have htrace : (p.gate line).trace I x =
      (fun o => o.elim (I line.op (p.trace I x ∘ line.wires)) (p.trace I x)) ∘ π := by
    funext w
    induction w using Wire.lastCases with
    | last => simp [π, Wire.lastCases, Line.eval, Program.trace, Function.comp_def]
    | castSucc w =>
      have hπ : π w.castSucc = some w := by
        cases w <;> simp [π, Wire.lastCases]
      simp only [Function.comp_apply, hπ, Option.elim_some, Program.trace_gate_castSucc]
  rw [htrace]
  exact chi_comp_eq_chi_projectSet π S _

/-- Every character of the available input and gate values has spectral norm at most the
exponential of the total gate cost, provided each primitive operation satisfies its own
spectral bound. This controls arbitrary sharing and repeated gate arguments. -/
theorem Program.sum_abs_fourierCoeff_chi_trace_le_two_pow_cost
    (p : Program σ n g) (I : Interpretation σ Bool) (cost : σ.Op → ℕ)
    (hgate : ∀ op,
      ∑ S, |fourierCoeff (fun y => signVal (I op y)) S| ≤ (2 : ℝ) ^ cost op)
    (S : Finset (Wire n g)) :
    ∑ T, |fourierCoeff (fun x => chi ℝ S (p.trace I x)) T| ≤
      (2 : ℝ) ^ p.cost cost := by
  classical
  revert S
  induction p with
  | empty =>
    intro S
    rw [Program.chi_trace_empty]
    simp [apply_ite]
  | @gate g p line ih =>
    intro S
    simp only [Program.chi_trace_gate]
    calc
      ∑ T, |fourierCoeff
          (fun x => chi ℝ (projectSet (Wire.lastCases none some) S)
            (fun o => o.elim (I line.op (p.trace I x ∘ line.wires)) (p.trace I x))) T| ≤
          (∑ U, |fourierCoeff (fun y => signVal (I line.op y)) U|) *
            (2 : ℝ) ^ p.cost cost :=
        sum_abs_fourierCoeff_chi_append_le (p.trace I) (I line.op) line.wires ih _
      _ ≤ (2 : ℝ) ^ cost line.op * (2 : ℝ) ^ p.cost cost :=
        mul_le_mul_of_nonneg_right (hgate line.op) (pow_nonneg (by norm_num) _)
      _ = (2 : ℝ) ^ (p.gate line).cost cost := by
        rw [Program.cost_gate, pow_add, mul_comm]

/-- The spectral norm of each circuit output is bounded by the exponential of the total
gate cost whenever every primitive operation satisfies the corresponding spectral bound. -/
theorem Circuit.sum_abs_fourierCoeff_signVal_eval_le_two_pow_cost
    (c : Circuit σ n m) (I : Interpretation σ Bool) (cost : σ.Op → ℕ)
    (hgate : ∀ op,
      ∑ S, |fourierCoeff (fun y => signVal (I op y)) S| ≤ (2 : ℝ) ^ cost op)
    (j : Fin m) :
    ∑ S, |fourierCoeff (fun x => signVal (c.eval I x j)) S| ≤
      (2 : ℝ) ^ c.program.cost cost := by
  simpa only [chi_singleton, Circuit.eval, Function.comp_apply] using
    c.program.sum_abs_fourierCoeff_chi_trace_le_two_pow_cost I cost hgate {c.outputs j}

/-- Every workspace character has Fourier coefficients with denominator dividing two to the
total gate cost, when each gate has that property at its own cost. Sharing and repeated gate
arguments are unrestricted, and a gate's denominator cost is charged only once. -/
theorem Program.exists_fourierCoeff_chi_trace_eq_intCast_div_two_pow_cost
    (p : Program σ n g) (I : Interpretation σ Bool) (cost : σ.Op → ℕ)
    (hgate : ∀ op T, ∃ z : ℤ,
      fourierCoeff (fun y => signVal (I op y)) T = z / (2 : ℝ) ^ cost op)
    (S : Finset (Wire n g)) (T : Finset (Fin n)) :
    ∃ z : ℤ, fourierCoeff (fun x => chi ℝ S (p.trace I x)) T =
      z / (2 : ℝ) ^ p.cost cost := by
  classical
  revert S T
  induction p with
  | empty =>
    intro S T
    rw [Program.chi_trace_empty, fourierCoeff_chi]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  | @gate g p line ih =>
    intro S T
    simp only [Program.chi_trace_gate, Program.cost_gate]
    exact exists_fourierCoeff_chi_append_eq_intCast_div_two_pow
      (p.trace I) (I line.op) line.wires ih (hgate line.op) _ T

/-- The Fourier coefficients of each output have denominator dividing two to the total
gate cost, provided the primitive gates satisfy the corresponding denominator bounds. -/
theorem Circuit.exists_fourierCoeff_signVal_eval_eq_intCast_div_two_pow_cost
    (c : Circuit σ n m) (I : Interpretation σ Bool) (cost : σ.Op → ℕ)
    (hgate : ∀ op T, ∃ z : ℤ,
      fourierCoeff (fun y => signVal (I op y)) T = z / (2 : ℝ) ^ cost op)
    (j : Fin m) (T : Finset (Fin n)) :
    ∃ z : ℤ, fourierCoeff (fun x => signVal (c.eval I x j)) T =
      z / (2 : ℝ) ^ c.program.cost cost := by
  simpa only [chi_singleton, Circuit.eval, Function.comp_apply] using
    c.program.exists_fourierCoeff_chi_trace_eq_intCast_div_two_pow_cost I cost hgate
      {c.outputs j} T

end Cslib.Circuits
