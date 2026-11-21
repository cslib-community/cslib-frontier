/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.ResidueCoordinates
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-! # Short addresses and single-path accounting for shared Newton inversion -/

@[expose] public section
namespace Cslib.Circuits.Frontier.FastContraction.NewtonQuery

open Turing.MultiTapeTM ComputableInPolyTime GaloisRingArith

/-- The four forms of a Newton request. A round uses two products and one subtraction. -/
inductive Node where
  | input
  | iterate (k : ℕ)
  | product (k : ℕ)
  | factor (k : ℕ)
  deriving DecidableEq

/-- An address serves directly as the decreasing rank. -/
def address : Node → ℕ
  | .input => 0
  | .iterate k => 3 * k + 1
  | .product k => 3 * k + 2
  | .factor k => 3 * k + 3

/-- The scalar supplied by an iteration node. -/
noncomputable def iterate (m p : ℕ) (x : List ℕ) (k : ℕ) : Ring p (modulus m) :=
  val p (modulus m) (roundsFrom p (modulus m) x (residueSeed (modulus m) x) k)

/-- Values of the finite collection of query forms, for semantic comparison only. -/
noncomputable def value (m p : ℕ) (x : List ℕ) : Node → Ring p (modulus m)
  | .input => val p (modulus m) x
  | .iterate k => iterate m p x k
  | .product k => val p (modulus m) x * iterate m p x k
  | .factor k => 2 - val p (modulus m) x * iterate m p x k

/-- A single branch selects just one predecessor, including the residue challenge's operand. -/
def child : Node → Bool → Node
  | .input, _ | .iterate 0, _ => .input
  | .iterate (k + 1), right => if right then .factor k else .iterate k
  | .product k, right => if right then .iterate k else .input
  | .factor k, _ => .product k

/-- Control states are ground input, residue inverse, reduced product and Newton correction. -/
def operation : Node → ℕ
  | .input => 0
  | .iterate 0 => 1
  | .iterate (_ + 1) | .product _ => 2
  | .factor _ => 3

/-- Binary dispatch from a stage and operand side to the operation and next stage. -/
def step (v : ℕ × Bool) : ℕ × ℕ :=
  let s := v.1
  if decide (s ≤ 1) then (s, 0)
  else if decide (s % 3 = 0) then (3, s - 1)
  else if decide (s % 3 = 2) then (2, if v.2 then s - 1 else 0)
  else (2, if v.2 then s - 1 else s - 3)

/-- The stage dispatcher itself is a fixed native polynomial-time function on binary addresses. -/
theorem computableInPolyTime_step :
    ComputableInPolyTime step (encPair encNat encBool) (encPair encNat encNat) := by
  have hs := fst encNat encBool
  have hr := snd encNat encBool
  have hrem := binary_mod' hs (const 3)
  have hprev := binary_sub' hs (const 1)
  exact ite' (binary_le' hs (const 1)) (hs.prod (const 0))
    (ite' (decide_eq' hrem (const 0)) ((const 3).prod hprev)
      (ite' (decide_eq' hrem (const 2)) ((const 2).prod (ite' hr hprev (const 0)))
        ((const 2).prod (ite' hr hprev (binary_sub' hs (const 3))))))

/-- Native dispatch takes precisely the specified one-child branch in every operation. -/
theorem step_address (node : Node) (right : Bool) :
    step (address node, right) = (operation node, address (child node right)) := by
  cases node with
  | input => rfl
  | iterate k =>
    cases k with
    | zero => rfl
    | succ k =>
      cases right <;> simp [step, address, operation, child, Nat.add_mod] <;> omega
  | product k =>
    cases right <;> simp [step, address, operation, child, Nat.add_mod]
  | factor k => simp [step, address, operation, child]

/-- Both product ports decrease rank, including the requests for a shared iterate. -/
theorem address_child_lt (n : Node) (hn : n ≠ .input) (right : Bool) :
    address (child n right) < address n := by
  cases n with
  | input => contradiction
  | iterate k =>
    cases k <;> cases right <;> simp [address, child]
    omega
  | product k => cases right <;> simp [address, child]
  | factor k => simp [address, child]

/-- The first iterate is exactly the lifted, one-bit residue inverse. -/
theorem iterate_zero (m p : ℕ) (x : List ℕ) :
    iterate m p x 0 = val p (modulus m) (residueSeed (modulus m) x) := by
  simp only [iterate, roundsFrom, List.range_zero, List.foldl_nil]

/-- The next iterate multiplies its two actual operand values. -/
theorem iterate_succ (m p : ℕ) (x : List ℕ) (k : ℕ) :
    iterate m p x (k + 1) = value m p x (.iterate k) * value m p x (.factor k) := by
  simp only [iterate, roundsFrom, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil, newton, val_mul, val_sub, val_add, val_one, value]
  ring

/-- The queried final stage computes the true inverse of every unit, also in precision zero. -/
theorem iterate_final (m p : ℕ) (x : List ℕ) (hx : IsUnit (val p (modulus m) x)) :
    iterate m p x (Nat.clog 2 p) = _root_.Ring.inverse (val p (modulus m) x) := by
  have h := val_roundsFrom_residueSeed (modulus m) x (irreducible_modulus m) hx
  rw [← _root_.Ring.inverse_mul_cancel_left _ (iterate m p x (Nat.clog 2 p)) hx]
  exact (congrArg (_root_.Ring.inverse (val p (modulus m) x) * ·) h).trans (mul_one _)

end Cslib.Circuits.Frontier.FastContraction.NewtonQuery
