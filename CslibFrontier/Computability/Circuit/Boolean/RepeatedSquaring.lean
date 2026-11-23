/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.Unbounded
public import CslibFrontier.Computability.Circuit.Iteration
public import Cslib.Foundations.Relation.RelatesInSteps
public import Mathlib.Logic.Equiv.Fin.Basic
import CslibFrontier.Foundations.Relation.RelatesWithinSteps

/-!
# Transitive closure by repeated Boolean matrix squaring

An `N × N` Boolean matrix stored row by row in `N * N` bits (`matrixIndex`) is the adjacency matrix
of a relation on `Fin N`. Over the unbounded fan-in basis, `squareCircuit N` computes its Boolean
square: entry `(i, j)` is the disjunction over `k` of the conjunctions of entries `(i, k)` and
`(k, j)`. This is a circuit of depth two with `N ^ 2 * (N + 1)` gates.

`closureCircuit N t` squares `t` times. Its entry `(i, j)` records a walk of exactly `2 ^ t` steps
from `i` to `j` (`eval_closureCircuit_iff_relatesInSteps`). For a reflexive relation, once
`N ≤ 2 ^ t`, that is reachability (`eval_closureCircuit_iff_reflTransGen`). With
`t = ⌈log₂ N⌉` this computes reflexive-transitive closure with depth `2 ⌈log₂ N⌉` and
`N ^ 2 * (N + 1) * ⌈log₂ N⌉` gates, the matrix-powering circuit behind
[Arora–Barak (2007 draft), Exercise 6.9][AroraBarak07] (`NL ⊆ NC`).

## Main definitions

* `Cslib.Circuits.Boolean.matrixIndex`: the bit holding entry `(i, j)` of a matrix stored row by
  row.
* `Cslib.Circuits.Boolean.squareCircuit`: one Boolean matrix squaring.
* `Cslib.Circuits.Boolean.closureCircuit`: `t` repeated squarings.

## Main results

* `Cslib.Circuits.Boolean.eval_squareCircuit`, `Cslib.Circuits.Boolean.size_squareCircuit`,
  `Cslib.Circuits.Boolean.depth_squareCircuit_le`: one squaring, its size and its depth.
* `Cslib.Circuits.Boolean.eval_closureCircuit_iff_relatesInSteps`: `t` squarings record walks of
  `2 ^ t` steps.
* `Cslib.Circuits.Boolean.eval_closureCircuit_iff_reflTransGen`: for a reflexive relation on
  at most `2 ^ t` elements, `t` squarings compute reachability.
* `Cslib.Circuits.Boolean.size_closureCircuit`, `Cslib.Circuits.Boolean.depth_closureCircuit_le`:
  `t` squarings use `t * (N ^ 2 * (N + 1))` gates and depth at most `2 * t`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft 2007,
  Exercise 6.9][AroraBarak07]
-/

public section

namespace Cslib.Circuits.Boolean

open Relation

variable {N : ℕ}

/-- The bit holding entry `(i, j)` of an `N × N` matrix stored row by row in `N * N` bits. -/
@[expose] def matrixIndex (i j : Fin N) : Fin (N * N) :=
  finProdFinEquiv (i, j)

private theorem symm_matrixIndex (i j : Fin N) : finProdFinEquiv.symm (matrixIndex i j) = (i, j) :=
  finProdFinEquiv.symm_apply_apply _

/-- **One Boolean matrix squaring.** Output `(i, j)` is the disjunction over `k` of the
conjunctions of input entries `(i, k)` and `(k, j)`. -/
@[expose] def squareCircuit (N : ℕ) : Circuit Unbounded.signature (N * N) (N * N) :=
  Circuit.pi fun o =>
    (Circuit.oneGate (Unbounded.Op.or N) (id : Fin N → Fin N)).comp
      (Circuit.pi fun k =>
        Circuit.oneGate (Unbounded.Op.and 2)
          ![matrixIndex (finProdFinEquiv.symm o).1 k, matrixIndex k (finProdFinEquiv.symm o).2])

/-- Entry `(i, j)` of the square is true iff some `k` has entries `(i, k)` and `(k, j)` true. -/
@[simp] theorem eval_squareCircuit (x : BitString (N * N)) (i j : Fin N) :
    (squareCircuit N).eval Unbounded.interpretation x (matrixIndex i j) =
      decide (∃ k, x (matrixIndex i k) = true ∧ x (matrixIndex k j) = true) := by
  simp only [squareCircuit, Circuit.eval_pi, symm_matrixIndex]
  simp [Fin.forall_fin_two]

/-- One squaring has `N ^ 2 * (N + 1)` gates: `N` conjunctions and one disjunction per entry. -/
@[simp] theorem size_squareCircuit : (squareCircuit N).size = N ^ 2 * (N + 1) := by
  simp only [squareCircuit, Circuit.size_pi, Circuit.size_comp, Circuit.size_oneGate,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one, sq]

/-- One squaring has depth at most two. -/
theorem depth_squareCircuit_le : (squareCircuit N).depth ≤ 2 :=
  Circuit.depth_pi_le _ fun _ => (Circuit.depth_comp_le _ _).trans <| by
    rw [Circuit.depth_oneGate]
    exact Nat.add_le_add_left (Circuit.depth_pi_le _ fun _ => (Circuit.depth_oneGate _ _).le) 1

/-- **Repeated squaring.** `t` Boolean squarings of an `N × N` matrix. -/
@[expose] def closureCircuit (N t : ℕ) : Circuit Unbounded.signature (N * N) (N * N) :=
  (squareCircuit N).iterate t

/-- **`t` squarings record walks of `2 ^ t` steps.** If `x` is the adjacency matrix of `r`, entry
`(i, j)` after `t` squarings is true iff `r` relates `i` to `j` in exactly `2 ^ t` steps. -/
theorem eval_closureCircuit_iff_relatesInSteps {r : Fin N → Fin N → Prop} {x : BitString (N * N)}
    (hx : ∀ i j, x (matrixIndex i j) = true ↔ r i j) (t : ℕ) (i j : Fin N) :
    (closureCircuit N t).eval Unbounded.interpretation x (matrixIndex i j) = true ↔
      RelatesInSteps r i j (2 ^ t) := by
  rw [closureCircuit, Circuit.eval_iterate]
  induction t generalizing i j with
  | zero =>
    change _ ↔ RelatesInSteps r i j (0 + 1)
    rw [Function.iterate_zero_apply, RelatesInSteps.succ_iff, hx]
    simp only [RelatesInSteps.zero_iff, exists_eq_left']
  | succ t ih =>
    rw [Function.iterate_succ_apply', eval_squareCircuit, decide_eq_true_iff, pow_succ,
      Nat.mul_two, RelatesInSteps.add_iff]
    simp only [ih]

/-- **Repeated squaring computes reachability.** If `x` is the adjacency matrix of a reflexive
relation `r` on `Fin N` and `N ≤ 2 ^ t`, entry `(i, j)` after `t` squarings is true iff `j` is
reachable from `i`. -/
theorem eval_closureCircuit_iff_reflTransGen {r : Fin N → Fin N → Prop} {x : BitString (N * N)}
    (hx : ∀ i j, x (matrixIndex i j) = true ↔ r i j) (hr : ∀ i, r i i) {t : ℕ} (hN : N ≤ 2 ^ t)
    (i j : Fin N) :
    (closureCircuit N t).eval Unbounded.interpretation x (matrixIndex i j) = true ↔
      ReflTransGen r i j := by
  have : Std.Refl r := ⟨hr⟩
  rw [eval_closureCircuit_iff_relatesInSteps hx,
    reflTransGen_iff_relatesWithinSteps (N := 2 ^ t) (by rw [Nat.card_fin]; omega),
    relatesWithinSteps_iff_relatesInSteps_reflGen, reflGen_eq_self]

/-- `t` squarings use `t * (N ^ 2 * (N + 1))` gates. -/
@[simp] theorem size_closureCircuit (t : ℕ) :
    (closureCircuit N t).size = t * (N ^ 2 * (N + 1)) := by
  rw [closureCircuit, Circuit.size_iterate, size_squareCircuit]

/-- `t` squarings have depth at most `2 * t`. -/
theorem depth_closureCircuit_le (t : ℕ) : (closureCircuit N t).depth ≤ 2 * t :=
  ((squareCircuit N).depth_iterate_le t).trans <| by
    rw [Nat.mul_comm 2]
    exact Nat.mul_le_mul_left t depth_squareCircuit_le

end Cslib.Circuits.Boolean
