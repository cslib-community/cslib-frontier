/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Circuit.Boolean.Simps

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

-- A formula gate of arbitrary arity bounds its depth uniformly across its arguments (`Finset.sup`).
example (op : σ.Op) (args : Fin (σ.Arity op) → Formula σ n) (D : ℕ)
    (hargs : ∀ j, (args j).depth ≤ D) :
    (Formula.gate op args).depth ≤ D + 1 := by
  circuit_bound

-- Small-arity tuple gates (`Fin 0`, `Fin 1`, `Fin 2`) expand to exact maxima without needing a
-- uniform bound across distinct arguments.
example (F G : Formula Boolean.signature n) (a b : ℕ)
    (hF : F.depth ≤ a) (hG : G.depth ≤ b) :
    (Formula.gate (σ := Boolean.signature) .or ![.gate .not ![F], G]).depth ≤
      max a b + 2 := by
  circuit_bound

-- Formula substitution (`Formula.bind`) adds at most the uniform depth of the substituted leaves.
example (F : Formula σ m) (sub : Fin m → Formula σ n) (D c : ℕ)
    (hF : F.depth ≤ D) (hsub : ∀ i, (sub i).depth ≤ c) :
    (F.bind sub).depth ≤ D + c := by
  circuit_bound

-- Fixed-exponent powers are monotone in their base (`Nat.pow_le_pow_left`).
example (c : Circuit σ n m) (r : ℕ) (hc : c.size ≤ r) :
    (c.size + 1) ^ 2 + 2 ≤ (r + 1) ^ 2 + 2 := by
  circuit_bound

-- Iterating a circuit multiplies its program cost via `Circuit.costProgram`.
example (c : Circuit σ n n) (w : σ.Op → ℕ) (t : ℕ) (hc : c.program.cost w ≤ 4) :
    (c.iterate t).program.cost w ≤ t * 4 := by
  circuit_bound

-- Boolean formula size and cost rules (`size_const`, `size_xor`, `cost_*`) in `circuit_simps`.
example (i : Fin n) :
    ((Formula.input i).xor (.const false) : Formula Boolean.signature n).size = 7 := by
  simp only [circuit_simps]

example (i j : Fin n) (w : Boolean.signature.Op → ℕ) :
    ((Formula.input i).and (.not (.input j)) : Formula Boolean.signature n).toCircuit.program.cost
      w = w .not + w .and := by
  simp only [circuit_simps]
  omega

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
private def rounds (c : Circuit σ n n) (c₀ : Circuit σ n n) : ℕ → Circuit σ n n
  | 0 => c₀
  | t + 1 => c.comp (rounds c c₀ t)

-- The definition is unfolded on request; the induction hypothesis bounds the recursive call.
private theorem depth_rounds_le (c c₀ : Circuit σ n n) (hc : c.depth ≤ 2) (h₀ : c₀.depth ≤ 1)
    (t : ℕ) : (rounds c c₀ t).depth ≤ 2 * t + 1 := by
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

-- Polynomial arithmetic after the structural bound is discharged by `nlinarith`.
example (cs : Fin m → Circuit σ n 1) (S : ℕ) (hcs : ∀ j, (cs j).size ≤ S) (hS : S ≤ k) :
    (Circuit.pi cs).size ≤ m * k := by
  circuit_bound

-- Nonlinear conditional bounds split top-level `max` before trying `omega`/`nlinarith`.
example (c : Circuit Boolean.signature n 1) (p : Prop) [Decidable p] (w : ℕ)
    (hc : c.size ≤ w ^ 2 + w) :
    (if p then c else Circuit.oneGate (σ := Boolean.signature) (.const false) Fin.elim0).size ≤
      (w + 1) ^ 2 := by
  circuit_bound

-- Uniform bounds over `List.ofFn` families are proved by bounding the indexed body uniformly.
private def listDepthWrap (cs : List (Circuit σ n 1)) : ℕ :=
  (cs.map Circuit.depth).foldr max 0

private theorem listDepthWrap_le (cs : List (Circuit σ n 1)) {D : ℕ} (h : ∀ C ∈ cs, C.depth ≤ D) :
    listDepthWrap cs ≤ D := by
  induction cs with
  | nil => exact Nat.zero_le _
  | cons C cs ih =>
    exact max_le (h C List.mem_cons_self) (ih fun C' hC' => h C' (List.mem_cons_of_mem _ hC'))

attribute [local circuit_bound] listDepthWrap_le in
example (cs : Fin m → Circuit σ n 1) (D : ℕ) (hcs : ∀ j, (cs j).depth ≤ D) :
    listDepthWrap (List.ofFn cs) ≤ D := by
  circuit_bound

-- Formula leaf sizes are normalized by `circuit_simps` and bounded by `circuit_bound`.
example (F G : Formula Boolean.signature m) (a b : ℕ) (hF : F.leafSize ≤ a) (hG : G.leafSize ≤ b) :
    (F.and G.not).leafSize ≤ a + b := by
  circuit_bound

-- When a polynomial comparison still does not hold, the error reports the unproved inequality.
/--
error: circuit_bound could not prove
  m * S ≤ m * k
-/
#guard_msgs in
example (cs : Fin m → Circuit σ n 1) (S : ℕ) (hcs : ∀ j, (cs j).size ≤ S) :
    (Circuit.pi cs).size ≤ m * k := by
  circuit_bound

-- The goal must be a bound between natural numbers.
/--
error: circuit_bound expects a goal `m ≤ b` between natural numbers, got
  c.depth = 3
-/
#guard_msgs in
example (c : Circuit σ n m) : c.depth = 3 := by
  circuit_bound

-- Soundness: `circuit_bound` leaves an exponent untouched even when a bound on the exponent is in
-- context.
example (b d : ℕ) (_h : 1 ≤ d) (_hd : d ≤ 2) (hb : b ^ d ≤ 9) : b ^ d ≤ 9 := by
  circuit_bound

/--
error: circuit_bound could not prove
  0 ^ d ≤ 0 ^ 2
-/
#guard_msgs in
example (d : ℕ) (_hd : d ≤ 2) : 0 ^ d ≤ 0 ^ 2 := by
  circuit_bound

-- A uniform bound on a mapped list sum uses the membership hypothesis.
example (cs : List (Circuit σ n m)) (k : ℕ) (h : ∀ c ∈ cs, c.size ≤ k) :
    (cs.map Circuit.size).sum ≤ cs.length * k := by
  circuit_bound

-- A `Finset.sup` family whose bound depends on the index reports the same diagnostic note.
/--
error: circuit_bound could not prove
  (Finset.univ.sup fun j => (args j).depth) + 1 ≤ 5
No bound of
  (args j).depth
is known that does not depend on `j`. State a bound of the family as a hypothesis `∀ j, … ≤ D`.
-/
#guard_msgs in
example (op : σ.Op) (args : Fin (σ.Arity op) → Formula σ n) :
    (Formula.gate op args).depth ≤ 5 := by
  circuit_bound

-- The attribute accepts only bounds and values of natural numbers.
/--
error: `circuit_bound` expects a theorem `m ≤ b` or `m = b` between natural numbers, got
  True
-/
#guard_msgs in
attribute [local circuit_bound] trivial

end CslibFrontierTests.CircuitBoundTactic
