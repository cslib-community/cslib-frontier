/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Boolean.Complexity
public import CslibFrontier.Probability.BitString.LinearHash
public import Mathlib.Algebra.Order.Floor.Div
import CslibFrontier.Computability.Circuit.Boolean.Parity
import CslibFrontier.Computability.Circuit.Boolean.Rectifier

/-!
# Native circuits for binary linear hashing

Every Boolean matrix defines a linear map over the two-element field. The usual independent
parity construction costs at most `m * (4 * n + 1)` gates for `n` inputs and `m` outputs.
Lupanov's row-pattern decomposition shares intermediate parities between the outputs. With
blocks of `s > 0` outputs, its native De Morgan gate count is bounded by

`4 * (⌈m / s⌉ * n + m * 2 ^ (s - 1)) + ⌈m / s⌉ * 2 ^ s + m`.

The proof interprets the existing rectifier construction additively, then replaces every sum
gate by a Boolean parity circuit. Constants are charged, including the nullary row classes.
The computed map is the existing `BitString.LinearHash.hash` used by the collision bounds.

## Main results

* `Cslib.Circuits.Boolean.complexity_linearHash_le`: independent output parities.
* `Cslib.Circuits.Boolean.complexity_linearHash_le_blocked`: shared row-pattern parities.

## References

* [O. B. Lupanov, *On rectifier and switching-and-rectifier circuits*][Lupanov1956], §2.
  The additive interpretation uses the same partition into disjoint row classes.
-/

public section

namespace Cslib.Circuits.Boolean

open Finset

variable {n m : ℕ}

private theorem sumInterpretation_eq_parity (r : ℕ) :
    Rectifier.sumInterpretation Bool r = parity r := by
  funext x
  simp only [Rectifier.sumInterpretation, parity, parityOn_eq_sum]
  rfl

private theorem simulates_sum :
    interpretation.SimulatesWithCost (Rectifier.sumInterpretation Bool) (fun r => 4 * r + 1) := by
  intro r
  cases r with
  | zero =>
    refine ⟨Circuit.oneGate (σ := signature) (.const false) Fin.elim0, ?_, by simp⟩
    intro x
    funext j
    change false = ∑ i : Fin 0, x i
    simp only [Fin.sum_univ_zero]
    rfl
  | succ r =>
    obtain ⟨c, hc, _, hsize⟩ := exists_computes_parity r
    refine ⟨c, ?_, ?_⟩
    · simpa only [sumInterpretation_eq_parity] using hc
    · change c.size ≤ 4 * (r + 1) + 1
      omega

private theorem cost_sumSimulation {g : ℕ} (p : Program Rectifier.signature n g) :
    p.cost (fun r => 4 * r + 1) = 4 * p.cost id + g := by
  induction p with
  | empty => rfl
  | gate p line ih =>
    simp only [Program.cost_gate, ih, id_eq]
    omega

private theorem complexity_le_sumCost (c : Circuit Rectifier.signature n m) :
    complexity interpretation (c.eval (Rectifier.sumInterpretation Bool)) ≤
      4 * c.program.cost id + c.size := by
  obtain ⟨d, hd, hsize⟩ := c.exists_simulationWithCost (fun r => 4 * r + 1) simulates_sum
  exact (complexity_le_of_computes d (fun x => congrFun hd x)).trans
    (hsize.trans_eq (cost_sumSimulation c.program))

private theorem sumAction_eq_hash (rows : Fin m → BitString n) :
    (fun x j => ∑ i, if rows j i = true then x i else 0) = BitString.LinearHash.hash rows := by
  funext x j
  simp only [BitString.LinearHash.hash, dotProduct]
  apply sum_congr rfl
  intro i _
  cases rows j i <;> rfl

/-- Computing the output parities independently costs at most `4 n + 1` gates per output. -/
theorem complexity_linearHash_le (rows : Fin m → BitString n) :
    complexity interpretation (BitString.LinearHash.hash rows) ≤ m * (4 * n + 1) := by
  let A : Matrix (Fin n) (Fin m) Bool := Matrix.of fun i j => rows j i
  have heval : (Rectifier.layer A).eval (Rectifier.sumInterpretation Bool) =
      BitString.LinearHash.hash rows := by
    funext x
    exact (Rectifier.eval_layer_sum A x).trans (congrFun (sumAction_eq_hash rows) x)
  have hcost : (Rectifier.layer A).program.cost id ≤ m * n := by
    rw [Rectifier.cost_layer]
    calc
      _ ≤ ∑ _j : Fin m, n := sum_le_sum fun j _ => by
        simpa only [card_univ, Fintype.card_fin] using card_le_univ {i | A i j = true}
      _ = _ := by simp
  rw [← heval]
  have h := complexity_le_sumCost (Rectifier.layer A)
  have hsize := Rectifier.size_layer A
  nlinarith only [h, hcost, hsize]

/-- Sharing the row-pattern parities in blocks of `s` outputs gives Lupanov's matrix bound
in the native binary De Morgan basis. Every gate, including constants, is counted. -/
theorem complexity_linearHash_le_blocked (rows : Fin m → BitString n) {s : ℕ} (hs : 0 < s) :
    complexity interpretation (BitString.LinearHash.hash rows) ≤
      4 * ((m ⌈/⌉ s) * n + m * 2 ^ (s - 1)) + (m ⌈/⌉ s) * 2 ^ s + m := by
  let A : Matrix (Fin n) (Fin m) Bool := Matrix.of fun i j => rows j i
  obtain ⟨c, _, hc, hcost, hsize⟩ := Rectifier.exists_twoLayer_sum (R := Bool) A hs
  have heval : c.eval (Rectifier.sumInterpretation Bool) = BitString.LinearHash.hash rows := by
    funext x
    exact (hc x).trans (congrFun (sumAction_eq_hash rows) x)
  rw [← heval]
  simpa only [hcost, hsize, Nat.add_assoc] using complexity_le_sumCost c

end Cslib.Circuits.Boolean
