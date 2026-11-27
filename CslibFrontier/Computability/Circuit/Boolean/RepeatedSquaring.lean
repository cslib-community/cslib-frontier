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
import CslibFrontier.Computability.Circuit.Simps
import CslibFrontier.Foundations.Relation.RelatesWithinSteps

/-!
# Reachability by repeated Boolean matrix squaring

An `N × N` Boolean matrix stored row by row in `N * N` bits via `finProdFinEquiv` is the adjacency
matrix of a relation on `Fin N`. Over the unbounded fan-in basis, `squareCircuit N` computes its
Boolean square: entry `(i, j)` is the disjunction over `k` of the conjunctions of entries `(i, k)`
and `(k, j)`. This is a circuit of depth at most two (`depth_squareCircuit_le`, registered with
`@[circuit_bound]`) and `N ^ 2 * (N + 1)` gates (`size_squareCircuit`).

Composing `t` copies as `(squareCircuit N).iterate t` uses `t * (N ^ 2 * (N + 1))` gates
(`Circuit.size_iterate`) and depth at most `2 * t` (`Circuit.depth_iterate_le`). Its entry `(i, j)`
records a walk of exactly `2 ^ t` steps from `i` to `j`
(`eval_iterate_squareCircuit_iff_relatesInSteps`); on general relations without self-loops it does
not add the diagonal. For a reflexive relation, once `N ≤ 2 ^ t`, a walk of `2 ^ t` steps is
reachability (`eval_iterate_squareCircuit_iff_reflTransGen`). With `t = ⌈log₂ N⌉` this computes
reflexive-transitive closure on reflexive adjacency matrices in depth `2 ⌈log₂ N⌉` and
`⌈log₂ N⌉ * (N ^ 2 * (N + 1))` gates, the matrix-powering circuit step of
[Arora and Barak, Chapter 6, Exercise 9][AroraBarak07].
`Cslib.Complexity.NL_subset_AC_one` applies it to machine configuration graphs.

## Main definitions

* `Cslib.Circuits.Boolean.squareCircuit`: one Boolean matrix squaring on `N * N` bits.

## Main results

* `Cslib.Circuits.Boolean.eval_squareCircuit`, `Cslib.Circuits.Boolean.size_squareCircuit`,
  `Cslib.Circuits.Boolean.depth_squareCircuit_le`: semantics, exact gate count and
  `@[circuit_bound]` depth bound of one squaring.
* `Cslib.Circuits.Boolean.eval_iterate_squareCircuit_iff_relatesInSteps`: `t` squarings record
  walks of `2 ^ t` steps.
* `Cslib.Circuits.Boolean.eval_iterate_squareCircuit_iff_reflTransGen`: for a reflexive relation
  on at most `2 ^ t` elements, `t` squarings compute reachability.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, 2007 web draft, Chapter 6,
  Exercise 9][AroraBarak07]
-/

public section

namespace Cslib.Circuits.Boolean

open Relation

variable {N : ℕ}

/-- **One Boolean matrix squaring.** An `N × N` Boolean matrix is stored row by row in `N * N`
bits via `finProdFinEquiv`. Output `(i, j)` is the disjunction over `k` of the conjunctions of
input entries `(i, k)` and `(k, j)`. -/
@[expose] def squareCircuit (N : ℕ) : Circuit Unbounded.signature (N * N) (N * N) :=
  Circuit.pi fun o =>
    (Circuit.oneGate (Unbounded.Op.or N) (id : Fin N → Fin N)).comp
      (Circuit.pi fun k =>
        Circuit.oneGate (Unbounded.Op.and 2)
          ![finProdFinEquiv ((finProdFinEquiv.symm o).1, k),
            finProdFinEquiv (k, (finProdFinEquiv.symm o).2)])

/-- Entry `(i, j)` of the square is true iff some `k` has entries `(i, k)` and `(k, j)` true. -/
@[simp] theorem eval_squareCircuit (x : BitString (N * N)) (i j : Fin N) :
    (squareCircuit N).eval Unbounded.interpretation x (finProdFinEquiv (i, j)) =
      decide (∃ k,
        x (finProdFinEquiv (i, k)) = true ∧ x (finProdFinEquiv (k, j)) = true) := by
  simp only [squareCircuit, Circuit.eval_pi, Equiv.symm_apply_apply]
  simp [Fin.forall_fin_two]

/-- One squaring has `N ^ 2 * (N + 1)` gates: `N` conjunctions and one disjunction per entry. -/
@[simp] theorem size_squareCircuit : (squareCircuit N).size = N ^ 2 * (N + 1) := by
  simp only [circuit_simps, squareCircuit, Nat.mul_one, sq]

/-- One squaring has depth at most two. -/
@[circuit_bound] theorem depth_squareCircuit_le : (squareCircuit N).depth ≤ 2 := by
  circuit_bound [squareCircuit]

/-- **`t` squarings record walks of `2 ^ t` steps.** If `x` is the adjacency matrix of `r`, entry
`(i, j)` of `(squareCircuit N).iterate t` is true iff `r` relates `i` to `j` in exactly `2 ^ t`
steps. -/
theorem eval_iterate_squareCircuit_iff_relatesInSteps {r : Fin N → Fin N → Prop}
    {x : BitString (N * N)} (hx : ∀ i j, x (finProdFinEquiv (i, j)) = true ↔ r i j) (t : ℕ)
    (i j : Fin N) :
    ((squareCircuit N).iterate t).eval Unbounded.interpretation x (finProdFinEquiv (i, j)) =
      true ↔ RelatesInSteps r i j (2 ^ t) := by
  rw [Circuit.eval_iterate]
  induction t generalizing i j with
  | zero =>
    change _ ↔ RelatesInSteps r i j (0 + 1)
    rw [Function.iterate_zero_apply, RelatesInSteps.succ_iff, hx]
    simp only [RelatesInSteps.zero_iff, exists_eq_left']
  | succ t ih =>
    rw [Function.iterate_succ_apply', eval_squareCircuit, decide_eq_true_iff, pow_succ,
      Nat.mul_two, RelatesInSteps.add_iff]
    simp only [ih]

/-- **Repeated squaring computes reachability on reflexive relations.** If `x` is the adjacency
matrix of a reflexive relation `r` on `Fin N` and `N ≤ 2 ^ t`, entry `(i, j)` of
`(squareCircuit N).iterate t` is true iff `j` is reachable from `i`. -/
theorem eval_iterate_squareCircuit_iff_reflTransGen {r : Fin N → Fin N → Prop}
    {x : BitString (N * N)} (hx : ∀ i j, x (finProdFinEquiv (i, j)) = true ↔ r i j)
    (hr : ∀ i, r i i) {t : ℕ} (hN : N ≤ 2 ^ t) (i j : Fin N) :
    ((squareCircuit N).iterate t).eval Unbounded.interpretation x (finProdFinEquiv (i, j)) =
      true ↔ ReflTransGen r i j := by
  have : Std.Refl r := ⟨hr⟩
  rw [eval_iterate_squareCircuit_iff_relatesInSteps hx,
    reflTransGen_iff_relatesWithinSteps (N := 2 ^ t) (by rw [Nat.card_fin]; omega),
    relatesWithinSteps_iff_relatesInSteps_reflGen, reflGen_eq_self]

end Cslib.Circuits.Boolean
