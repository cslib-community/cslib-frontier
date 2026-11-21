/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Simps

/-! # Bounding depth, size and cost with `circuit_bound` and `circuit_simps` -/

set_option linter.privateModule false

namespace CslibFrontierTests.CircuitBoundTactic

open Cslib Cslib.Circuits

variable {σ : Signature} {n m k : ℕ}

/-! ### Combinators, with the pieces bounded by hypotheses -/

-- Sequential composition adds depths.
example (d : Circuit σ m k) (c : Circuit σ n m) (hd : d.depth ≤ 3) (hc : c.depth ≤ 4) :
    (d.comp c).depth ≤ 7 := by
  circuit_bound

-- A piece without a bound stays in the bound.
example (d : Circuit σ m k) (c : Circuit σ n m) (hd : d.depth ≤ 3) :
    (d.comp c).depth ≤ c.depth + 3 := by
  circuit_bound

-- Parallel composition takes the larger depth.
example (c : Circuit σ n m) (d : Circuit σ n k) (hc : c.depth ≤ 2) (hd : d.depth ≤ 5) :
    (c.append d).depth ≤ 5 := by
  circuit_bound

example (c : Circuit σ n m) (d : Circuit σ n k) :
    (c.append d).depth ≤ max c.depth d.depth := by
  circuit_bound

-- A family needs one bound for all its members: here a hypothesis.
example (cs : Fin m → Circuit σ n 1) (d : Circuit σ m 1) (D : ℕ)
    (hcs : ∀ j, (cs j).depth ≤ D) (hd : d.depth ≤ 3) :
    (d.comp (Circuit.pi cs)).depth ≤ D + 3 := by
  circuit_bound

-- A family whose members have the same structural bound, through a conditional.
example (c d : Circuit σ n 1) (p : Fin m → Prop) [DecidablePred p]
    (hc : c.depth ≤ 2) (hd : d.depth ≤ 3) :
    (Circuit.pi fun j => if p j then c else d).depth ≤ 3 := by
  circuit_bound

-- A dependent conditional, as in a construction that needs a side condition.
example (c : Circuit σ n 1) (d : 0 < m → Circuit σ n 1) (hc : c.depth ≤ 2)
    (hd : ∀ h, (d h).depth ≤ 3) : (if h : 0 < m then d h else c).depth ≤ 3 := by
  circuit_bound

-- Wiring has depth zero, and a single gate depth one: exact rules of the simp set.
example (c : Circuit σ n m) (f : Fin k → Fin m) (hc : c.depth ≤ 4) :
    ((Circuit.wiring σ f).comp c).depth ≤ 4 := by
  circuit_bound

-- The depth of a formula bounds the depth of its circuit.
example (i j : Fin n) :
    (Formula.toCircuit ((Formula.input i).and (.input j) : Formula Boolean.signature n)).depth
      ≤ 1 := by
  circuit_bound

/-! ### Size and cost -/

-- The size of a family is a sum, bounded term by term.
example (cs : Fin m → Circuit σ n 1) (d : Circuit σ m 1) (S : ℕ)
    (hcs : ∀ j, (cs j).size ≤ S) (hd : d.size ≤ 7) :
    (d.comp (Circuit.pi cs)).size ≤ 7 + m * S := by
  circuit_bound

example (d : Circuit σ m k) (c : Circuit σ n m) (w : σ.Op → ℕ)
    (hd : d.program.cost w ≤ 3) (hc : c.program.cost w ≤ 4) :
    (d.comp c).program.cost w ≤ 7 := by
  circuit_bound

example (d : Circuit σ m k) (c : Circuit σ n m) (cost : σ.Op → ℕ)
    (hd : d.depthWith cost ≤ 1) (hc : c.depthWith cost ≤ 1) :
    (d.comp c).depthWith cost ≤ 2 := by
  circuit_bound

-- An equation needs no bound: the simp set alone computes the size.
example (d : Circuit σ m k) (c : Circuit σ n m) (e : Circuit σ n k) :
    ((d.comp c).append e).size = c.size + d.size + e.size := by
  simp only [circuit_simps]

/-! ### Definitions, induction hypotheses and registered bounds -/

/-- `t` rounds of a circuit, after a circuit `c₀`. -/
def rounds (c : Circuit σ n n) (c₀ : Circuit σ n n) : ℕ → Circuit σ n n
  | 0 => c₀
  | t + 1 => c.comp (rounds c c₀ t)

-- The definition is unfolded on request; the induction hypothesis bounds the recursive call.
theorem depth_rounds_le (c c₀ : Circuit σ n n) (hc : c.depth ≤ 2) (h₀ : c₀.depth ≤ 1) (t : ℕ) :
    (rounds c c₀ t).depth ≤ 2 * t + 1 := by
  induction t with
  | zero => simpa [rounds] using h₀
  | succ t ih => circuit_bound [rounds]

-- The program cost of a named construction, unfolded by the same call. The lemma
-- `Circuit.cost_program_comp` alone would not apply here: the gate count, an implicit argument of
-- the cost, is rewritten first.
example (c c₀ : Circuit σ n n) (w : σ.Op → ℕ) (t : ℕ) :
    (rounds c c₀ (t + 1)).program.cost w = (rounds c c₀ t).program.cost w + c.program.cost w := by
  simp only [circuit_simps, rounds]

example (c c₀ : Circuit σ n n) (w : σ.Op → ℕ) (hc : c.program.cost w ≤ 2)
    (h₀ : c₀.program.cost w ≤ 1) (t : ℕ) : (rounds c c₀ t).program.cost w ≤ 2 * t + 1 := by
  induction t with
  | zero => simpa [rounds] using h₀
  | succ t ih => circuit_bound [rounds]

-- A registered bound is used wherever the construction occurs; its hypotheses are assumptions.
attribute [local circuit_bound] depth_rounds_le in
example (c c₀ d : Circuit σ n n) (hc : c.depth ≤ 2) (h₀ : c₀.depth ≤ 1) (hd : d.depth ≤ 5) :
    ((rounds c c₀ 3).append d).depth ≤ 7 := by
  circuit_bound

-- The trace lists the registered bounds and the hypotheses used.
/--
trace: [circuit_bound] Circuit.depth_comp_le: (d.comp c).depth ≤ d.depth + c.depth
[circuit_bound] hd: d.depth ≤ 3
[circuit_bound] hc: c.depth ≤ 4
-/
#guard_msgs in
set_option trace.circuit_bound true in
example (d : Circuit σ m k) (c : Circuit σ n m) (hd : d.depth ≤ 3) (hc : c.depth ≤ 4) :
    (d.comp c).depth ≤ 7 := by
  circuit_bound

/-! ### Other open goals

The calls below are not focused on purpose, hence the linter option. -/

-- Called on the first of two goals, the tactic closes it and leaves the second: here `omega`
-- compares the bound `3 + 4` with the right-hand side.
set_option linter.style.multiGoal false in
example (d : Circuit σ m k) (c : Circuit σ n m) (hd : d.depth ≤ 3) (hc : c.depth ≤ 4) :
    (d.comp c).depth ≤ 7 ∧ c.depth ≤ 4 := by
  constructor
  circuit_bound
  exact hc

-- The same when the simp lemmas given already close the comparison.
set_option linter.style.multiGoal false in
example (c : Circuit σ n m) (d : Circuit σ n k) (hd : d.depth ≤ 5) :
    (c.append d).depth ≤ max c.depth d.depth ∧ d.depth ≤ 5 := by
  constructor
  circuit_bound [le_refl]
  exact hd

/-! ### Metavariables in a cost -/

-- The cost procedure of `circuit_simps` rewrites a cost that contains a metavariable and leaves
-- the metavariable open.
example (d : Circuit σ m k) (c : Circuit σ n m) :
    ∃ w : σ.Op → ℕ, (d.comp c).program.cost w = c.program.cost w + d.program.cost w := by
  constructor
  · simp only [circuit_simps]
  · exact fun _ => 1

-- It does not assign a metavariable that stands for the circuit: no cost rule applies.
example (w : σ.Op → ℕ) (c : Circuit σ n k) (h : c.program.cost w = 0) :
    ∃ p : Circuit σ n k, p.program.cost w = 0 := by
  constructor
  · fail_if_success simp only [circuit_simps]
    exact h

/-! ### Failures -/

-- A piece with no bound, where the goal needs one.
/--
error: circuit_bound could not prove
  3 + c.depth ≤ 7
No bound is registered or assumed for
  c.depth
-/
#guard_msgs in
example (d : Circuit σ m k) (c : Circuit σ n m) (hd : d.depth ≤ 3) : (d.comp c).depth ≤ 7 := by
  circuit_bound

-- A family whose bound depends on the index.
/--
error: circuit_bound could not prove
  (Circuit.pi cs).depth ≤ 5
No bound is registered or assumed for
  (Circuit.pi cs).depth
No bound of
  (cs j).depth
is known that does not depend on `j`. State a bound of the family as a hypothesis `∀ j, … ≤ D`.
-/
#guard_msgs in
example (cs : Fin m → Circuit σ n 1) : (Circuit.pi cs).depth ≤ 5 := by
  circuit_bound

-- The structural bound is found, and the arithmetic left is not linear.
/--
error: circuit_bound could not prove
  m * S ≤ m * k
-/
#guard_msgs in
example (cs : Fin m → Circuit σ n 1) (S : ℕ) (hcs : ∀ j, (cs j).size ≤ S) (hS : S ≤ k) :
    (Circuit.pi cs).size ≤ m * k := by
  circuit_bound

-- In that case state the structural bound and finish by hand.
example (cs : Fin m → Circuit σ n 1) (S : ℕ) (hcs : ∀ j, (cs j).size ≤ S) (hS : S ≤ k) :
    (Circuit.pi cs).size ≤ m * k := by
  have h : (Circuit.pi cs).size ≤ m * S := by circuit_bound
  exact h.trans (Nat.mul_le_mul_left m hS)

-- The goal must be a bound between natural numbers.
/--
error: circuit_bound expects a goal `m ≤ b` between natural numbers, got
  c.depth = 3
-/
#guard_msgs in
example (c : Circuit σ n m) : c.depth = 3 := by
  circuit_bound

-- The attribute accepts only bounds and values of natural numbers.
/--
error: `circuit_bound` expects a theorem `m ≤ b` or `m = b` between natural numbers, got
  True
-/
#guard_msgs in
attribute [local circuit_bound] trivial

end CslibFrontierTests.CircuitBoundTactic
