/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ModGates
public import CslibFrontier.Foundations.Data.BitString.Parity.DotProduct
import Mathlib.Data.Finset.Sort
import CslibFrontier.Computability.Circuit.Boolean.Simps

/-!
# Small AC⁰[2] circuits

Building blocks for circuits over `Unbounded.extSignature` read with `MOD₂` gates,
`Unbounded.extInterpretation (modGate 2)`, the basis of AC⁰[2]:

* `Unbounded.parityOnCircuit s`: one `MOD₂` gate on the inputs in `s`, computing `parityOn s`.
* `Unbounded.andCircuit i j`: one binary conjunction of two inputs.
* `Unbounded.innerProductCircuit k`: the inner product `b ⬝ᵥ r` over GF(2) of two strings of `k`
  bits, as `k` conjunctions under one `MOD₂` gate.

The first two have depth at most one and the inner product depth at most two. Gates count
towards the size; wires do not. The bits of a fixed string, `Unbounded.constsCircuit`, are in
`CslibFrontier.Computability.Circuit.Boolean.AC0`.

## Main definitions

* `Cslib.Circuits.Boolean.Unbounded.parityOnCircuit`,
  `Cslib.Circuits.Boolean.Unbounded.andCircuit`: a parity and a conjunction.
* `Cslib.Circuits.Boolean.Unbounded.innerProductCircuit`: the inner product over GF(2).

## Main results

* `Cslib.Circuits.Boolean.Unbounded.eval_parityOnCircuit`,
  `Cslib.Circuits.Boolean.Unbounded.eval_andCircuit`,
  `Cslib.Circuits.Boolean.Unbounded.eval_innerProductCircuit`: what they compute.
* `Cslib.Circuits.Boolean.Unbounded.size_innerProductCircuit`,
  `Cslib.Circuits.Boolean.Unbounded.depth_innerProductCircuit_le`: the inner product has `k + 1`
  gates and depth at most two.
-/

public section

namespace Cslib.Circuits.Boolean.Unbounded

open Finset

variable {n : ℕ}

/-! ### Parity of some inputs -/

/-- One `MOD₂` gate on the inputs in `s`, listed in increasing order. -/
def parityOnCircuit (s : Finset (Fin n)) : Circuit extSignature n 1 :=
  Circuit.oneGate (.gate #s) fun a => s.orderEmbOfFin rfl a

/-- With `MOD₂` gates, `parityOnCircuit s` computes the parity of the inputs in `s`. -/
@[simp] theorem eval_parityOnCircuit (s : Finset (Fin n)) (x : BitString n) (o : Fin 1) :
    (parityOnCircuit s).eval (extInterpretation (modGate 2)) x o = parityOn s x := by
  rw [parityOnCircuit, Circuit.eval_oneGate, extInterpretation_gate, modGate_two_eq_parity,
    parity, parityOn_eq_sum, parityOn_eq_sum]
  have h := sum_map univ (s.orderEmbOfFin rfl).toEmbedding x
  rw [map_orderEmbOfFin_univ] at h
  exact h.symm

/-- `parityOnCircuit s` is one gate. -/
@[simp] theorem size_parityOnCircuit (s : Finset (Fin n)) : (parityOnCircuit s).size = 1 :=
  Circuit.size_oneGate _ _

/-- `parityOnCircuit s` has depth one. -/
@[simp] theorem depth_parityOnCircuit (s : Finset (Fin n)) : (parityOnCircuit s).depth = 1 :=
  Circuit.depth_oneGate _ _

/-! ### Conjunction of two inputs -/

/-- One conjunction of the inputs `i` and `j`. -/
def andCircuit (i j : Fin n) : Circuit extSignature n 1 :=
  binCircuit toExt (.and 2) rfl (Circuit.wiring _ fun _ => i) (Circuit.wiring _ fun _ => j)

/-- `andCircuit i j` computes the conjunction of the inputs `i` and `j`, whatever the extra
gates compute. -/
@[simp] theorem eval_andCircuit (g : ∀ m, BooleanFunction m) (i j : Fin n) (x : BitString n)
    (o : Fin 1) : (andCircuit i j).eval (extInterpretation g) x o = (x i && x j) := by
  rw [andCircuit, eval_binCircuit_and]
  rfl

/-- `andCircuit i j` is one gate. -/
@[simp] theorem size_andCircuit (i j : Fin n) : (andCircuit i j).size = 1 := by
  simp [andCircuit]

/-- `andCircuit i j` has depth at most one. -/
@[circuit_bound]
theorem depth_andCircuit_le (i j : Fin n) : (andCircuit i j).depth ≤ 1 :=
  (depth_binCircuit_le _ _ _ _).trans (by simp)

/-! ### Inner product over GF(2) -/

/-- On inputs `(b, r)` of `k` bits each, the conjunctions `bᵢ ∧ rᵢ` under one `MOD₂` gate. -/
def innerProductCircuit (k : ℕ) : Circuit extSignature (k + k) 1 :=
  (parityOnCircuit univ).comp (Circuit.pi fun i => andCircuit (Fin.castAdd k i) (Fin.natAdd k i))

/-- With `MOD₂` gates, `innerProductCircuit k` computes the inner product over GF(2). -/
@[simp] theorem eval_innerProductCircuit {k : ℕ} (b r : BitString k) (o : Fin 1) :
    (innerProductCircuit k).eval (extInterpretation (modGate 2)) (Fin.append b r) o = b ⬝ᵥ r := by
  rw [innerProductCircuit, Circuit.eval_comp, eval_parityOnCircuit, Circuit.eval_pi,
    parityOn_eq_sum]
  simp only [eval_andCircuit, Fin.append_left, Fin.append_right]
  rfl

/-- `innerProductCircuit k` has `k + 1` gates. -/
@[simp] theorem size_innerProductCircuit (k : ℕ) : (innerProductCircuit k).size = k + 1 := by
  simp [innerProductCircuit]

/-- `innerProductCircuit k` has depth at most two. -/
@[circuit_bound]
theorem depth_innerProductCircuit_le (k : ℕ) : (innerProductCircuit k).depth ≤ 2 := by
  circuit_bound [innerProductCircuit, depth_parityOnCircuit]

end Cslib.Circuits.Boolean.Unbounded
