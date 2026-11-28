/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import CslibFrontier.Foundations.Data.List.GetD
import CslibFrontier.Foundations.Data.Nat.Bitwise.Carry
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Gates and gadgets for succinct formulas

A formula with exponentially many clauses is described here by its *gates*: an operation
(`Cslib.Complexity.CookLevin.Quasilinear.Gate.Op`), an output variable and three argument
variables, the variables numbered by natural numbers
(`Cslib.Complexity.CookLevin.Quasilinear.Gate`). Each gate stands for at most four clauses of three
literals (`Gate.clause`), satisfied exactly when the gate holds (`Gate.forall_clause_iff`): its
output is the conjunction, disjunction, exclusive or, equivalence, negation or selection of its
arguments, or, for the two assertion gates, its first argument is true or implies its second.

Gadgets are lists of gates computing a value into fresh variables numbered from a base `β`:
equality of two bit vectors (`eqGadget`), comparison of two numbers written in binary
(`ltGadget`), adding `1`, subtracting `1` or keeping a number (`addGadget`), and membership of a
tuple of bits in a list of patterns (`tableGadget`). Each comes with the value of its output
variable in every assignment satisfying its gates. Every gate of a gadget defines a fresh variable
from earlier ones, so any assignment of the other variables extends to the fresh variables
(`exists_extension`).

## Main definitions

* `Cslib.Complexity.CookLevin.Quasilinear.Gate`, `Gate.Op`, `Gate.Holds`, `Gate.clause`.
* `Cslib.Complexity.CookLevin.Quasilinear.bitsVal`: a number written in binary by variables.
* `Cslib.Complexity.CookLevin.Quasilinear.eqGadget`, `ltGadget`, `addGadget`, `matchGadget`,
  `tableGadget`.

## Main results

* `Cslib.Complexity.CookLevin.Quasilinear.Gate.forall_clause_iff`: the clauses of a gate.
* `Cslib.Complexity.CookLevin.Quasilinear.eqGadget_out`, `ltGadget_out`, `addGadget_out`,
  `matchGadget_out`, `tableGadget_out`: the values the gadgets compute.
* `Cslib.Complexity.CookLevin.Quasilinear.exists_extension`: assignments extend to the variables
  that gates define.
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin.Quasilinear

open Cslib.Logic.PL

/-- The operation of a gate. The first six define their output variable from their arguments: the
conjunction, disjunction, exclusive or and equivalence of `a` and `b`, the negation of `a`, and
the selection `if c then a else b`. The last two define nothing and only constrain: `assert` says
that `a` is true, and `imp` that `a` implies `b`. -/
inductive Gate.Op
  /-- the output is the conjunction of `a` and `b` -/
  | and
  /-- the output is the disjunction of `a` and `b` -/
  | or
  /-- the output is the exclusive or of `a` and `b` -/
  | xor
  /-- the output is the equivalence of `a` and `b` -/
  | xnor
  /-- the output is the negation of `a` -/
  | not
  /-- the output is `a` if `c` is true and `b` otherwise -/
  | mux
  /-- `a` is true -/
  | assert
  /-- `a` implies `b` -/
  | imp
  deriving DecidableEq, Inhabited

/-- A gate on variables numbered by natural numbers: an operation, an output variable and three
argument variables. The arguments an operation does not use are `0`; `out` is also unused by the
two assertions. -/
structure Gate where
  /-- the operation -/
  op : Gate.Op
  /-- the output variable -/
  out : ℕ
  /-- the first argument -/
  a : ℕ
  /-- the second argument -/
  b : ℕ
  /-- the third argument, the selector of a selection -/
  c : ℕ
  deriving DecidableEq, Inhabited

namespace Gate

/-- Whether an operation defines its output variable from its arguments, rather than asserting. -/
def Op.IsDefining (o : Op) : Prop := o ≠ .assert ∧ o ≠ .imp

/-- The value a defining gate gives its output, from the values of its arguments. The two
assertions define nothing; their value is `false`. -/
def eval (σ : ℕ → Bool) (g : Gate) : Bool :=
  match g.op with
  | .and => σ g.a && σ g.b
  | .or => σ g.a || σ g.b
  | .xor => xor (σ g.a) (σ g.b)
  | .xnor => σ g.a == σ g.b
  | .not => !σ g.a
  | .mux => cond (σ g.c) (σ g.a) (σ g.b)
  | .assert | .imp => false

/-- The constraint a gate imposes on an assignment. -/
def Holds (σ : ℕ → Bool) (g : Gate) : Prop :=
  match g.op with
  | .assert => σ g.a = true
  | .imp => σ g.a = true → σ g.b = true
  | _ => σ g.out = eval σ g

/-- The clauses of a gate, one for each slot `s < 4`; unused slots are tautologies. -/
def clause (g : Gate) (s : ℕ) : Clause ℕ :=
  let o := g.out
  let a := g.a
  let b := g.b
  let c := g.c
  let taut : Clause ℕ := [(o, true), (o, false), (o, false)]
  if g.op = .and then
    if s = 0 then [(o, false), (a, true), (a, true)]
    else if s = 1 then [(o, false), (b, true), (b, true)]
    else if s = 2 then [(o, true), (a, false), (b, false)] else taut
  else if g.op = .or then
    if s = 0 then [(o, true), (a, false), (a, false)]
    else if s = 1 then [(o, true), (b, false), (b, false)]
    else if s = 2 then [(o, false), (a, true), (b, true)] else taut
  else if g.op = .xor then
    if s = 0 then [(o, false), (a, true), (b, true)]
    else if s = 1 then [(o, false), (a, false), (b, false)]
    else if s = 2 then [(o, true), (a, false), (b, true)]
    else [(o, true), (a, true), (b, false)]
  else if g.op = .xnor then
    if s = 0 then [(o, false), (a, false), (b, true)]
    else if s = 1 then [(o, false), (a, true), (b, false)]
    else if s = 2 then [(o, true), (a, true), (b, true)]
    else [(o, true), (a, false), (b, false)]
  else if g.op = .not then
    if s = 0 then [(o, true), (a, true), (a, true)]
    else if s = 1 then [(o, false), (a, false), (a, false)] else taut
  else if g.op = .mux then
    if s = 0 then [(c, false), (a, false), (o, true)]
    else if s = 1 then [(c, false), (a, true), (o, false)]
    else if s = 2 then [(c, true), (b, false), (o, true)]
    else [(c, true), (b, true), (o, false)]
  else if g.op = .assert then
    if s = 0 then [(a, true), (a, true), (a, true)] else [(a, true), (a, false), (a, false)]
  else
    if s = 0 then [(a, false), (b, true), (b, true)] else [(a, true), (a, false), (a, false)]

/-- A statement about every slot below `4` is one about each of the four slots. -/
private theorem forall_lt_four {P : ℕ → Prop} : (∀ s < 4, P s) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 := by
  constructor
  · intro h
    exact ⟨h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)⟩
  · rintro ⟨h0, h1, h2, h3⟩ s hs
    interval_cases s <;> assumption

/-- **The clauses of a gate hold exactly when the gate does.** -/
theorem forall_clause_iff (σ : ℕ → Bool) (g : Gate) :
    (∀ s < 4, Clause.eval σ (g.clause s) = true) ↔ g.Holds σ := by
  rw [forall_lt_four]
  obtain ⟨op, o, a, b, c⟩ := g
  cases op <;>
    simp only [clause, Holds, eval, reduceCtorEq, ite_true, ite_false, Clause.eval] <;>
    norm_num <;> cases σ o <;> cases σ a <;> cases σ b <;> cases σ c <;> simp

/-- A conjunction gate holds when its output is the conjunction of its arguments. -/
private theorem holds_and (σ : ℕ → Bool) (o a b c : ℕ) :
    Holds σ ⟨.and, o, a, b, c⟩ ↔ σ o = (σ a && σ b) := Iff.rfl

/-- A disjunction gate holds when its output is the disjunction of its arguments. -/
private theorem holds_or (σ : ℕ → Bool) (o a b c : ℕ) :
    Holds σ ⟨.or, o, a, b, c⟩ ↔ σ o = (σ a || σ b) := Iff.rfl

/-- An exclusive-or gate holds when its output is the exclusive or of its arguments. -/
private theorem holds_xor (σ : ℕ → Bool) (o a b c : ℕ) :
    Holds σ ⟨.xor, o, a, b, c⟩ ↔ σ o = xor (σ a) (σ b) := Iff.rfl

/-- An equivalence gate holds when its output is the equivalence of its arguments. -/
theorem holds_xnor (σ : ℕ → Bool) (o a b c : ℕ) :
    Holds σ ⟨.xnor, o, a, b, c⟩ ↔ σ o = (σ a == σ b) := Iff.rfl

/-- A negation gate holds when its output is the negation of its argument. -/
theorem holds_not (σ : ℕ → Bool) (o a b c : ℕ) :
    Holds σ ⟨.not, o, a, b, c⟩ ↔ σ o = !σ a := Iff.rfl

/-- A selection gate holds when its output is the selected argument. -/
theorem holds_mux (σ : ℕ → Bool) (o a b c : ℕ) :
    Holds σ ⟨.mux, o, a, b, c⟩ ↔ σ o = cond (σ c) (σ a) (σ b) := Iff.rfl

/-- An assertion gate holds when its argument is true. -/
theorem holds_assert (σ : ℕ → Bool) (o a b c : ℕ) :
    Holds σ ⟨.assert, o, a, b, c⟩ ↔ σ a = true := Iff.rfl

/-- An implication gate holds when its first argument implies its second. -/
theorem holds_imp (σ : ℕ → Bool) (o a b c : ℕ) :
    Holds σ ⟨.imp, o, a, b, c⟩ ↔ (σ a = true → σ b = true) := Iff.rfl

end Gate

/-! ### Numbers written by variables -/

/-- The number whose binary digits, least significant first, are the values of `f 0, …, f (k - 1)`:
Batteries' `Nat.ofBits` of the first `k` values of `f`. -/
abbrev bitsVal (f : ℕ → Bool) (k : ℕ) : ℕ := Nat.ofBits (fun i : Fin k => f i)

/-- No digits write `0`. -/
private theorem bitsVal_zero (f : ℕ → Bool) : bitsVal f 0 = 0 := Nat.ofBits_zero _

/-- The number of `k + 1` digits is twice that of the digits after the first, plus the first. -/
private theorem bitsVal_cons (f : ℕ → Bool) (k : ℕ) :
    bitsVal f (k + 1) = 2 * bitsVal (fun i => f (i + 1)) k + (f 0).toNat :=
  Nat.ofBits_succ _

/-- The number of `k + 1` digits is that of `k` digits plus the new digit. -/
private theorem bitsVal_succ (f : ℕ → Bool) (k : ℕ) :
    bitsVal f (k + 1) = bitsVal f k + (f k).toNat * 2 ^ k := by
  induction k generalizing f with
  | zero => simp [bitsVal_cons]
  | succ k ih =>
    rw [bitsVal_cons, ih, bitsVal_cons f k, Nat.pow_succ]
    ring

/-- The number written by the first `k` digits depends only on those digits. -/
theorem bitsVal_congr {f g : ℕ → Bool} {k : ℕ} (h : ∀ j < k, f j = g j) :
    bitsVal f k = bitsVal g k :=
  congrArg Nat.ofBits (funext fun i => h i i.2)

/-- Splitting the digits of a number at `a`. -/
theorem bitsVal_add (f : ℕ → Bool) (a b : ℕ) :
    bitsVal f (a + b) = bitsVal f a + 2 ^ a * bitsVal (fun i => f (a + i)) b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← Nat.add_assoc, bitsVal_succ, ih, bitsVal_succ, Nat.pow_add]
    ring

/-- All digits `false` write `0`. -/
theorem bitsVal_false (k : ℕ) : bitsVal (fun _ => false) k = 0 := by
  induction k with
  | zero => exact bitsVal_zero _
  | succ k ih => rw [bitsVal_succ, ih]; simp

/-- `k` digits write a number below `2 ^ k`. -/
private theorem bitsVal_lt (f : ℕ → Bool) (k : ℕ) : bitsVal f k < 2 ^ k :=
  Nat.ofBits_lt_two_pow _

/-- The digits of a number determine it. -/
theorem bitsVal_testBit (n k : ℕ) (h : n < 2 ^ k) : bitsVal (fun j => n.testBit j) k = n := by
  have := Nat.ofBits_testBit n k
  rwa [Nat.mod_eq_of_lt h] at this

/-- The digits below `k` of a number written by `f` are those of `f`. -/
private theorem testBit_bitsVal (f : ℕ → Bool) {k j : ℕ} (hj : j < k) :
    (bitsVal f k).testBit j = f j :=
  Nat.testBit_ofBits_lt (fun i : Fin k => f i) j hj

/-- The digits from `k` on of a number written by `k` digits are `false`. -/
private theorem testBit_bitsVal_of_le (f : ℕ → Bool) {k j : ℕ} (hj : k ≤ j) :
    (bitsVal f k).testBit j = false :=
  Nat.testBit_ofBits_ge (fun i : Fin k => f i) j hj

/-- Equal numbers written by `k` digits have equal digits. -/
theorem bitsVal_injective {f g : ℕ → Bool} {k : ℕ} (h : bitsVal f k = bitsVal g k) :
    ∀ j < k, f j = g j := fun j hj => by
  rw [← testBit_bitsVal f hj, ← testBit_bitsVal g hj, h]

/-! ### Gadgets -/

section Gadgets

variable (σ : ℕ → Bool)

/-- A member of one of the first `m` blocks is a member of their flattening. -/
private theorem mem_flatMap_range {β : Type*} {m : ℕ} {f : ℕ → List β} {x : β} {i : ℕ} (hi : i < m)
    (hx : x ∈ f i) : x ∈ (List.range m).flatMap f :=
  List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, hx⟩

/-- A property of every entry of a list is one of every defaulted lookup in range. -/
theorem forall_mem_iff_getD {β : Type*} {l : List β} {d : β} {P : β → Prop} :
    (∀ x ∈ l, P x) ↔ ∀ j < l.length, P (l.getD j d) := by
  constructor
  · intro h j hj
    exact h _ (List.getD_mem _ hj)
  · intro h x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have := h j hj
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at this

/-- Equality of the pairs of `ps`, chained from the variable `tt` into fresh variables from `β`:
two gates per pair. -/
def eqGadget (β tt : ℕ) (ps : List (ℕ × ℕ)) : List Gate :=
  (List.range ps.length).flatMap fun i =>
    [⟨.xnor, β + 2 * i, (ps.getD i (0, 0)).1, (ps.getD i (0, 0)).2, 0⟩,
      ⟨.and, β + 2 * i + 1, if i = 0 then tt else β + 2 * i - 1, β + 2 * i, 0⟩]

/-- The output variable of `eqGadget`. -/
def eqOut (β tt m : ℕ) : ℕ := if m = 0 then tt else β + 2 * m - 1

/-- One step of the equality chain: pair `i` is added to the conjunction. -/
private theorem eqGadget_step {β tt : ℕ} {ps : List (ℕ × ℕ)}
    (h : ∀ g ∈ eqGadget β tt ps, g.Holds σ) {i : ℕ} (hi : i < ps.length)
    (hprev : σ (if i = 0 then tt else β + 2 * i - 1) =
      decide (∀ j < i, σ (ps.getD j (0, 0)).1 = σ (ps.getD j (0, 0)).2)) :
    σ (β + 2 * i + 1) =
      decide (∀ j < i + 1, σ (ps.getD j (0, 0)).1 = σ (ps.getD j (0, 0)).2) := by
  have hx := h ⟨.xnor, β + 2 * i, (ps.getD i (0, 0)).1, (ps.getD i (0, 0)).2, 0⟩
    (mem_flatMap_range hi (by simp))
  have hc := h ⟨.and, β + 2 * i + 1, if i = 0 then tt else β + 2 * i - 1, β + 2 * i, 0⟩
    (mem_flatMap_range hi (by simp))
  rw [Gate.holds_xnor] at hx
  rw [Gate.holds_and] at hc
  rw [hc, hx, hprev, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Nat.forall_lt_succ_right]

/-- The prefix induction of the two-gate chains: if the accumulator after entry `i` (the variable
`β + 2 * i + 1`, chained from `tt`) follows from the accumulator before it, then it is the
conjunction of the per-entry test `e` over the entries up to `i`. -/
private theorem prefix_chain (β tt n : ℕ) (e : ℕ → Prop) [DecidablePred e] (htt : σ tt = true)
    (step : ∀ i < n, σ (if i = 0 then tt else β + 2 * i - 1) = decide (∀ j < i, e j) →
      σ (β + 2 * i + 1) = decide (∀ j < i + 1, e j)) (i : ℕ) (hi : i < n) :
    σ (β + 2 * i + 1) = decide (∀ j < i + 1, e j) := by
  induction i with
  | zero => exact step 0 hi (by simp [htt])
  | succ i ih =>
    refine step (i + 1) hi ?_
    rw [ite_eq_right (by omega), show β + 2 * (i + 1) - 1 = β + 2 * i + 1 by omega]
    exact ih (by omega)

/-- The output of pair `i` of the equality chain is the conjunction over pairs up to `i`. -/
private theorem eqGadget_chain {β tt : ℕ} {ps : List (ℕ × ℕ)}
    (h : ∀ g ∈ eqGadget β tt ps, g.Holds σ) (htt : σ tt = true) (i : ℕ) (hi : i < ps.length) :
    σ (β + 2 * i + 1) =
      decide (∀ j < i + 1, σ (ps.getD j (0, 0)).1 = σ (ps.getD j (0, 0)).2) :=
  prefix_chain σ β tt ps.length (fun j => σ (ps.getD j (0, 0)).1 = σ (ps.getD j (0, 0)).2) htt
    (fun _ hi hprev => eqGadget_step σ h hi hprev) i hi

/-- **The value of `eqGadget`**: whether every pair has equal values. -/
theorem eqGadget_out {β tt : ℕ} {ps : List (ℕ × ℕ)}
    (h : ∀ g ∈ eqGadget β tt ps, g.Holds σ) (htt : σ tt = true) :
    σ (eqOut β tt ps.length) = decide (∀ p ∈ ps, σ p.1 = σ p.2) := by
  unfold eqOut
  split_ifs with hm
  · rw [List.length_eq_zero_iff] at hm
    simp [hm, htt]
  · rw [show β + 2 * ps.length - 1 = β + 2 * (ps.length - 1) + 1 by omega,
      eqGadget_chain σ h htt (ps.length - 1) (by omega), Nat.sub_add_cancel (by omega),
      Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    exact (forall_mem_iff_getD (l := ps) (d := (0, 0)) (P := fun p => σ p.1 = σ p.2)).symm

/-- Comparison of two numbers written by the pairs of `ps` (first and second components, least
significant first), chained from the variable `ff` into fresh variables from `β`: five gates
per digit. -/
def ltGadget (β ff : ℕ) (ps : List (ℕ × ℕ)) : List Gate :=
  (List.range ps.length).flatMap fun i =>
    [⟨.xnor, β + 5 * i, (ps.getD i (0, 0)).1, (ps.getD i (0, 0)).2, 0⟩,
      ⟨.not, β + 5 * i + 1, (ps.getD i (0, 0)).1, 0, 0⟩,
      ⟨.and, β + 5 * i + 2, β + 5 * i + 1, (ps.getD i (0, 0)).2, 0⟩,
      ⟨.and, β + 5 * i + 3, β + 5 * i, if i = 0 then ff else β + 5 * i - 1, 0⟩,
      ⟨.or, β + 5 * i + 4, β + 5 * i + 2, β + 5 * i + 3, 0⟩]

/-- The output variable of `ltGadget`. -/
def ltOut (β ff m : ℕ) : ℕ := if m = 0 then ff else β + 5 * m - 1

/-- The comparison of two numbers with one more high digit each. -/
private theorem lt_digit_step (A B : ℕ) (x y : Bool) (k : ℕ) (hA : A < 2 ^ k) (hB : B < 2 ^ k) :
    decide (A + x.toNat * 2 ^ k < B + y.toNat * 2 ^ k) =
      (!x && y || (x == y) && decide (A < B)) := by
  rw [Bool.eq_iff_iff]
  cases x <;> cases y <;> simp <;> omega

/-- One step of the comparison chain: digit `i` updates the comparison of the lower digits. -/
private theorem ltGadget_step {β ff : ℕ} {ps : List (ℕ × ℕ)}
    (h : ∀ g ∈ ltGadget β ff ps, g.Holds σ) {i : ℕ} (hi : i < ps.length)
    (hprev : σ (if i = 0 then ff else β + 5 * i - 1) =
      decide (bitsVal (fun j => σ (ps.getD j (0, 0)).1) i <
        bitsVal (fun j => σ (ps.getD j (0, 0)).2) i)) :
    σ (β + 5 * i + 4) =
      decide (bitsVal (fun j => σ (ps.getD j (0, 0)).1) (i + 1) <
        bitsVal (fun j => σ (ps.getD j (0, 0)).2) (i + 1)) := by
  have g0 := h ⟨.xnor, β + 5 * i, (ps.getD i (0, 0)).1, (ps.getD i (0, 0)).2, 0⟩
    (mem_flatMap_range hi (by simp))
  have g1 := h ⟨.not, β + 5 * i + 1, (ps.getD i (0, 0)).1, 0, 0⟩ (mem_flatMap_range hi (by simp))
  have g2 := h ⟨.and, β + 5 * i + 2, β + 5 * i + 1, (ps.getD i (0, 0)).2, 0⟩
    (mem_flatMap_range hi (by simp))
  have g3 := h ⟨.and, β + 5 * i + 3, β + 5 * i, if i = 0 then ff else β + 5 * i - 1, 0⟩
    (mem_flatMap_range hi (by simp))
  have g4 := h ⟨.or, β + 5 * i + 4, β + 5 * i + 2, β + 5 * i + 3, 0⟩
    (mem_flatMap_range hi (by simp))
  rw [Gate.holds_xnor] at g0
  rw [Gate.holds_not] at g1
  rw [Gate.holds_and] at g2 g3
  rw [Gate.holds_or] at g4
  rw [g4, g2, g3, g1, g0, hprev, bitsVal_succ, bitsVal_succ,
    lt_digit_step _ _ _ _ _ (bitsVal_lt _ _) (bitsVal_lt _ _)]

/-- The output of digit `i` of the comparison chain compares the numbers of digits up to `i`. -/
private theorem ltGadget_chain {β ff : ℕ} {ps : List (ℕ × ℕ)}
    (h : ∀ g ∈ ltGadget β ff ps, g.Holds σ) (hff : σ ff = false) (i : ℕ) (hi : i < ps.length) :
    σ (β + 5 * i + 4) =
      decide (bitsVal (fun j => σ (ps.getD j (0, 0)).1) (i + 1) <
        bitsVal (fun j => σ (ps.getD j (0, 0)).2) (i + 1)) := by
  induction i with
  | zero => exact ltGadget_step σ h hi (by simp [hff])
  | succ i ih =>
    refine ltGadget_step σ h hi ?_
    rw [ite_eq_right (by omega), show β + 5 * (i + 1) - 1 = β + 5 * i + 4 by omega]
    exact ih (by omega)

/-- **The value of `ltGadget`**: whether the first number is smaller. -/
theorem ltGadget_out {β ff : ℕ} {ps : List (ℕ × ℕ)}
    (h : ∀ g ∈ ltGadget β ff ps, g.Holds σ) (hff : σ ff = false) :
    σ (ltOut β ff ps.length) =
      decide (bitsVal (fun j => σ (ps.getD j (0, 0)).1) ps.length <
        bitsVal (fun j => σ (ps.getD j (0, 0)).2) ps.length) := by
  unfold ltOut
  split_ifs with hm
  · simp [hm, hff]
  · rw [show β + 5 * ps.length - 1 = β + 5 * (ps.length - 1) + 4 by omega,
      ltGadget_chain σ h hff (ps.length - 1) (by omega), Nat.sub_add_cancel (by omega)]

/-- The digits of a number plus one, and of a number minus one, least significant first: digit `i`
flips exactly when every lower digit is `true` (for adding) or `false` (for subtracting). -/
def incDigit (f : ℕ → Bool) (i : ℕ) : Bool := xor (f i) (decide (∀ j < i, f j = true))

/-- See `incDigit`. -/
def decDigit (f : ℕ → Bool) (i : ℕ) : Bool := xor (f i) (decide (∀ j < i, f j = false))

/-- The lower bits of a number written by `f` are all `b` exactly when the lower digits are. -/
private theorem forall_testBit_bitsVal_iff (f : ℕ → Bool) {k q : ℕ} (hq : q < k) (b : Bool) :
    (∀ i < q, (bitsVal f k).testBit i = b) ↔ ∀ i < q, f i = b :=
  forall₂_congr fun i hi => by rw [testBit_bitsVal f (by omega)]

/-- The digits of `incDigit f` write the successor, modulo `2 ^ k`. -/
theorem bitsVal_incDigit (f : ℕ → Bool) (k : ℕ) :
    bitsVal (incDigit f) k = (bitsVal f k + 1) % 2 ^ k := by
  refine Nat.eq_of_testBit_eq fun q => ?_
  rw [Nat.testBit_mod_two_pow]
  by_cases hq : q < k
  · rw [testBit_bitsVal _ hq, decide_eq_true hq, Bool.true_and,
      Nat.testBit_add_one_eq_ite_forall, testBit_bitsVal f hq]
    by_cases h : ∀ i < q, f i = true
    · rw [ite_eq_left ((forall_testBit_bitsVal_iff f hq true).2 h), incDigit, decide_eq_true h]
      cases f q <;> rfl
    · rw [ite_eq_right (mt (forall_testBit_bitsVal_iff f hq true).1 h), incDigit, decide_eq_false h,
        Bool.xor_false]
  · rw [decide_eq_false hq, Bool.false_and]
    exact testBit_bitsVal_of_le _ (by omega)

/-- A number is a multiple of `2 ^ q` exactly when its bits below `q` are `false`. -/
private theorem mod_two_pow_eq_zero_iff (V q : ℕ) :
    V % 2 ^ q = 0 ↔ ∀ j < q, V.testBit j = false := by
  constructor
  · intro h j hj
    have := Nat.testBit_mod_two_pow V q j
    rwa [h, Nat.zero_testBit, decide_eq_true hj, Bool.true_and, eq_comm] at this
  · intro h
    refine Nat.eq_of_testBit_eq fun j => ?_
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    by_cases hj : j < q
    · rw [decide_eq_true hj, Bool.true_and, h j hj]
    · rw [decide_eq_false hj, Bool.false_and]

/-- Subtracting one: the successor of `decDigit f` is `f`, plus `2 ^ k` when every digit is
`false`. -/
theorem bitsVal_decDigit_add_one (f : ℕ → Bool) (k : ℕ) :
    bitsVal (decDigit f) k + 1 =
      bitsVal f k + (if ∀ j < k, f j = false then 2 ^ k else 0) := by
  by_cases hall : ∀ j < k, f j = false
  · -- wraparound: the input is zero and every digit of the result is set
    rw [ite_eq_left hall, bitsVal_congr hall, bitsVal_false, Nat.zero_add]
    have hd : ∀ j < k, decDigit f j = (2 ^ k - 1).testBit j := fun j hj => by
      rw [Nat.testBit_two_pow_sub_one, decide_eq_true hj, decDigit, hall j hj,
        decide_eq_true fun i hi => hall i (by omega)]
      rfl
    rw [bitsVal_congr hd, bitsVal_testBit _ _ (Nat.sub_lt (Nat.two_pow_pos k) one_pos)]
    have := Nat.two_pow_pos k
    omega
  · rw [ite_eq_right hall, Nat.add_zero]
    have hV : 1 ≤ bitsVal f k := by
      by_contra hV
      refine hall fun j hj => ?_
      rw [← testBit_bitsVal f hj, show bitsVal f k = 0 by omega, Nat.zero_testBit]
    have hlt : bitsVal f k - 1 < 2 ^ k := by have := bitsVal_lt f k; omega
    have : bitsVal (decDigit f) k = bitsVal f k - 1 := by
      refine Nat.eq_of_testBit_eq fun q => ?_
      by_cases hq : q < k
      · rw [testBit_bitsVal _ hq, Nat.testBit_sub_one_eq_xor hV, testBit_bitsVal f hq, decDigit]
        have hz := mod_two_pow_eq_zero_iff (bitsVal f k) q
        rw [(forall_testBit_bitsVal_iff f hq false)] at hz
        by_cases h : ∀ i < q, f i = false
        · rw [decide_eq_true h, decide_eq_true (hz.2 h)]
        · rw [decide_eq_false h, decide_eq_false (mt hz.1 h)]
      · rw [testBit_bitsVal_of_le _ (by omega)]
        exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt
          (Nat.pow_le_pow_right (by omega) (by omega)))).symm
    omega

/-- Adding `1` (when `σ P`), subtracting `1` (when `σ Q` but not `σ P`) or keeping the number
written by the first components of `ps`, and comparing with the number written by the second
components: nine gates per digit, chained from the variable `tt`. -/
def addGadget (β tt P Q : ℕ) (ps : List (ℕ × ℕ)) : List Gate :=
  (List.range ps.length).flatMap fun i =>
    [⟨.xor, β + 9 * i, (ps.getD i (0, 0)).1, if i = 0 then tt else β + 9 * i - 8, 0⟩,
      ⟨.and, β + 9 * i + 1, (ps.getD i (0, 0)).1, if i = 0 then tt else β + 9 * i - 8, 0⟩,
      ⟨.not, β + 9 * i + 2, (ps.getD i (0, 0)).1, 0, 0⟩,
      ⟨.xor, β + 9 * i + 3, (ps.getD i (0, 0)).1, if i = 0 then tt else β + 9 * i - 5, 0⟩,
      ⟨.and, β + 9 * i + 4, β + 9 * i + 2, if i = 0 then tt else β + 9 * i - 5, 0⟩,
      ⟨.mux, β + 9 * i + 5, β + 9 * i + 3, (ps.getD i (0, 0)).1, Q⟩,
      ⟨.mux, β + 9 * i + 6, β + 9 * i, β + 9 * i + 5, P⟩,
      ⟨.xnor, β + 9 * i + 7, (ps.getD i (0, 0)).2, β + 9 * i + 6, 0⟩,
      ⟨.and, β + 9 * i + 8, if i = 0 then tt else β + 9 * i - 1, β + 9 * i + 7, 0⟩]

/-- The output variable of `addGadget`. -/
def addOut (β tt m : ℕ) : ℕ := if m = 0 then tt else β + 9 * m - 1

/-- The digit `addGadget` expects at position `i`. -/
def addTarget (P Q : Bool) (f : ℕ → Bool) (i : ℕ) : Bool :=
  cond P (incDigit f i) (cond Q (decDigit f i) (f i))

/-- One step of the addition chain: the outputs of position `i` from those below. -/
private theorem addGadget_step {β tt P Q : ℕ} {ps : List (ℕ × ℕ)}
    (h : ∀ g ∈ addGadget β tt P Q ps, g.Holds σ) {i : ℕ} (hi : i < ps.length)
    (hc : σ (if i = 0 then tt else β + 9 * i - 8) =
      decide (∀ j < i, σ (ps.getD j (0, 0)).1 = true))
    (hd : σ (if i = 0 then tt else β + 9 * i - 5) =
      decide (∀ j < i, σ (ps.getD j (0, 0)).1 = false))
    (he : σ (if i = 0 then tt else β + 9 * i - 1) = decide (∀ j < i, σ (ps.getD j (0, 0)).2 =
      addTarget (σ P) (σ Q) (fun j => σ (ps.getD j (0, 0)).1) j)) :
    σ (β + 9 * i + 1) = decide (∀ j < i + 1, σ (ps.getD j (0, 0)).1 = true) ∧
      σ (β + 9 * i + 4) = decide (∀ j < i + 1, σ (ps.getD j (0, 0)).1 = false) ∧
      σ (β + 9 * i + 8) = decide (∀ j < i + 1, σ (ps.getD j (0, 0)).2 =
        addTarget (σ P) (σ Q) (fun j => σ (ps.getD j (0, 0)).1) j) := by
  have g0 := h ⟨.xor, β + 9 * i, (ps.getD i (0, 0)).1, if i = 0 then tt else β + 9 * i - 8, 0⟩
    (mem_flatMap_range hi (by simp))
  have g1 := h ⟨.and, β + 9 * i + 1, (ps.getD i (0, 0)).1, if i = 0 then tt else β + 9 * i - 8, 0⟩
    (mem_flatMap_range hi (by simp))
  have g2 := h ⟨.not, β + 9 * i + 2, (ps.getD i (0, 0)).1, 0, 0⟩ (mem_flatMap_range hi (by simp))
  have g3 := h ⟨.xor, β + 9 * i + 3, (ps.getD i (0, 0)).1, if i = 0 then tt else β + 9 * i - 5, 0⟩
    (mem_flatMap_range hi (by simp))
  have g4 := h ⟨.and, β + 9 * i + 4, β + 9 * i + 2, if i = 0 then tt else β + 9 * i - 5, 0⟩
    (mem_flatMap_range hi (by simp))
  have g5 := h ⟨.mux, β + 9 * i + 5, β + 9 * i + 3, (ps.getD i (0, 0)).1, Q⟩
    (mem_flatMap_range hi (by simp))
  have g6 := h ⟨.mux, β + 9 * i + 6, β + 9 * i, β + 9 * i + 5, P⟩ (mem_flatMap_range hi (by simp))
  have g7 := h ⟨.xnor, β + 9 * i + 7, (ps.getD i (0, 0)).2, β + 9 * i + 6, 0⟩
    (mem_flatMap_range hi (by simp))
  have g8 := h ⟨.and, β + 9 * i + 8, if i = 0 then tt else β + 9 * i - 1, β + 9 * i + 7, 0⟩
    (mem_flatMap_range hi (by simp))
  rw [Gate.holds_xor] at g0 g3
  rw [Gate.holds_and] at g1 g4 g8
  rw [Gate.holds_not] at g2
  rw [Gate.holds_mux] at g5 g6
  rw [Gate.holds_xnor] at g7
  refine ⟨?_, ?_, ?_⟩
  · rw [g1, hc, Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.forall_lt_succ_right]
    exact and_comm
  · rw [g4, g2, hd, Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.forall_lt_succ_right, Bool.not_eq_true']
    exact and_comm
  · have htarget : σ (β + 9 * i + 6) =
        addTarget (σ P) (σ Q) (fun j => σ (ps.getD j (0, 0)).1) i := by
      rw [g6, g5, g0, g3, hc, hd]
      rfl
    rw [g8, g7, htarget, he, Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Nat.forall_lt_succ_right]

/-- The outputs of position `i` of the addition chain, from the base case up. -/
private theorem addGadget_chain {β tt P Q : ℕ} {ps : List (ℕ × ℕ)}
    (h : ∀ g ∈ addGadget β tt P Q ps, g.Holds σ) (htt : σ tt = true) (i : ℕ)
    (hi : i < ps.length) :
    σ (β + 9 * i + 1) = decide (∀ j < i + 1, σ (ps.getD j (0, 0)).1 = true) ∧
      σ (β + 9 * i + 4) = decide (∀ j < i + 1, σ (ps.getD j (0, 0)).1 = false) ∧
      σ (β + 9 * i + 8) = decide (∀ j < i + 1, σ (ps.getD j (0, 0)).2 =
        addTarget (σ P) (σ Q) (fun j => σ (ps.getD j (0, 0)).1) j) := by
  induction i with
  | zero => exact addGadget_step σ h hi (by simp [htt]) (by simp [htt]) (by simp [htt])
  | succ i ih =>
    obtain ⟨c1, c2, c3⟩ := ih (by omega)
    refine addGadget_step σ h hi ?_ ?_ ?_
    · rw [ite_eq_right (by omega), show β + 9 * (i + 1) - 8 = β + 9 * i + 1 by omega, c1]
    · rw [ite_eq_right (by omega), show β + 9 * (i + 1) - 5 = β + 9 * i + 4 by omega, c2]
    · rw [ite_eq_right (by omega), show β + 9 * (i + 1) - 1 = β + 9 * i + 8 by omega, c3]

/-- **The value of `addGadget`**: whether the second number is the first plus one, minus one or
unchanged, digit by digit. -/
theorem addGadget_out {β tt P Q : ℕ} {ps : List (ℕ × ℕ)}
    (h : ∀ g ∈ addGadget β tt P Q ps, g.Holds σ) (htt : σ tt = true) :
    σ (addOut β tt ps.length) = decide (∀ j < ps.length, σ (ps.getD j (0, 0)).2 =
      addTarget (σ P) (σ Q) (fun j => σ (ps.getD j (0, 0)).1) j) := by
  unfold addOut
  split_ifs with hm
  · simp [hm, htt]
  · rw [show β + 9 * ps.length - 1 = β + 9 * (ps.length - 1) + 8 by omega,
      (addGadget_chain σ h htt (ps.length - 1) (by omega)).2.2, Nat.sub_add_cancel (by omega)]

/-- Whether every literal of `lits` holds, chained from the variable `tt` into fresh variables
from `β`: two gates per literal. -/
def matchGadget (β tt : ℕ) (lits : List (ℕ × Bool)) : List Gate :=
  (List.range lits.length).flatMap fun i =>
    [⟨.not, β + 2 * i, (lits.getD i (0, true)).1, 0, 0⟩,
      ⟨.and, β + 2 * i + 1, if i = 0 then tt else β + 2 * i - 1,
        if (lits.getD i (0, true)).2 then (lits.getD i (0, true)).1 else β + 2 * i, 0⟩]

/-- The output variable of `matchGadget`. -/
def matchOut (β tt m : ℕ) : ℕ := if m = 0 then tt else β + 2 * m - 1

/-- One step of the match chain: literal `i` is added to the conjunction. -/
private theorem matchGadget_step {β tt : ℕ} {lits : List (ℕ × Bool)}
    (h : ∀ g ∈ matchGadget β tt lits, g.Holds σ) {i : ℕ} (hi : i < lits.length)
    (hprev : σ (if i = 0 then tt else β + 2 * i - 1) =
      decide (∀ j < i, σ (lits.getD j (0, true)).1 = (lits.getD j (0, true)).2)) :
    σ (β + 2 * i + 1) =
      decide (∀ j < i + 1, σ (lits.getD j (0, true)).1 = (lits.getD j (0, true)).2) := by
  have hn := h ⟨.not, β + 2 * i, (lits.getD i (0, true)).1, 0, 0⟩ (mem_flatMap_range hi (by simp))
  have hc := h ⟨.and, β + 2 * i + 1, if i = 0 then tt else β + 2 * i - 1,
    if (lits.getD i (0, true)).2 then (lits.getD i (0, true)).1 else β + 2 * i, 0⟩
    (mem_flatMap_range hi (by simp))
  rw [Gate.holds_not] at hn
  rw [Gate.holds_and] at hc
  have hlit : σ (if (lits.getD i (0, true)).2 then (lits.getD i (0, true)).1 else β + 2 * i) =
      decide (σ (lits.getD i (0, true)).1 = (lits.getD i (0, true)).2) := by
    split_ifs with hs
    · rw [hs]
      cases σ (lits.getD i (0, true)).1 <;> simp
    · rw [hn, show (lits.getD i (0, true)).2 = false by simpa using hs]
      cases σ (lits.getD i (0, true)).1 <;> simp
  rw [hc, hlit, hprev, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.forall_lt_succ_right]

/-- The output of literal `i` of the match chain is the conjunction over literals up to `i`. -/
private theorem matchGadget_chain {β tt : ℕ} {lits : List (ℕ × Bool)}
    (h : ∀ g ∈ matchGadget β tt lits, g.Holds σ) (htt : σ tt = true) (i : ℕ)
    (hi : i < lits.length) :
    σ (β + 2 * i + 1) =
      decide (∀ j < i + 1, σ (lits.getD j (0, true)).1 = (lits.getD j (0, true)).2) :=
  prefix_chain σ β tt lits.length
    (fun j => σ (lits.getD j (0, true)).1 = (lits.getD j (0, true)).2) htt
    (fun _ hi hprev => matchGadget_step σ h hi hprev) i hi

/-- **The value of `matchGadget`**: whether every literal holds. -/
theorem matchGadget_out {β tt : ℕ} {lits : List (ℕ × Bool)}
    (h : ∀ g ∈ matchGadget β tt lits, g.Holds σ) (htt : σ tt = true) :
    σ (matchOut β tt lits.length) = decide (∀ l ∈ lits, σ l.1 = l.2) := by
  unfold matchOut
  split_ifs with hm
  · rw [List.length_eq_zero_iff] at hm
    simp [hm, htt]
  · rw [show β + 2 * lits.length - 1 = β + 2 * (lits.length - 1) + 1 by omega,
      matchGadget_chain σ h htt (lits.length - 1) (by omega), Nat.sub_add_cancel (by omega),
      Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    exact (forall_mem_iff_getD (l := lits) (d := (0, true)) (P := fun l => σ l.1 = l.2)).symm

/-- Whether some pattern of `pats` matches: a `matchGadget` of `2 w` gates per pattern, the
pattern `r` placed at `β + 2 * w * r`, then `pats.length` disjunction gates `β + 2 * w * pats.length
+ r`, each an `or` of the previous disjunction (`ff` for the first) with the output of the match
chain of pattern `r`.

**Width contract.** The block of each pattern is reserved `2 * w` addresses, but `matchGadget`
emits two gates per literal. Only when every pattern has exactly `w` literals do the blocks fill
their addresses, so that the gates define the contiguous range `β, β + 1, …`
(`defining_tableGadget`, `length_tableGadget`). A shorter pattern leaves a hole of unused
addresses before the next block. `tableGadget_out` holds for any widths, since it only reads the
outputs, but `Defining` needs exact width. -/
def tableGadget (β tt ff w : ℕ) (pats : List (List (ℕ × Bool))) : List Gate :=
  ((List.range pats.length).flatMap fun r => matchGadget (β + 2 * w * r) tt (pats.getD r [])) ++
    (List.range pats.length).map fun r =>
      ⟨.or, β + 2 * w * pats.length + r, if r = 0 then ff else β + 2 * w * pats.length + r - 1,
        matchOut (β + 2 * w * r) tt (pats.getD r []).length, 0⟩

/-- The output variable of `tableGadget`: the last disjunction gate, or `ff` with no pattern. -/
def tableOut (β ff w R : ℕ) : ℕ := if R = 0 then ff else β + 2 * w * R + R - 1

/-- One step of the table chain: pattern `r` is added to the disjunction. -/
private theorem tableGadget_step {β tt ff w : ℕ} {pats : List (List (ℕ × Bool))}
    (h : ∀ g ∈ tableGadget β tt ff w pats, g.Holds σ) (htt : σ tt = true)
    {r : ℕ} (hr : r < pats.length)
    (hprev : σ (if r = 0 then ff else β + 2 * w * pats.length + r - 1) =
      decide (∃ s < r, ∀ l ∈ pats.getD s [], σ l.1 = l.2)) :
    σ (β + 2 * w * pats.length + r) =
      decide (∃ s < r + 1, ∀ l ∈ pats.getD s [], σ l.1 = l.2) := by
  have hor := h ⟨.or, β + 2 * w * pats.length + r,
    if r = 0 then ff else β + 2 * w * pats.length + r - 1,
    matchOut (β + 2 * w * r) tt (pats.getD r []).length, 0⟩
    (List.mem_append_right _ (List.mem_map.2 ⟨r, List.mem_range.2 hr, rfl⟩))
  have hmatch := matchGadget_out σ (β := β + 2 * w * r) (lits := pats.getD r [])
    (fun g hg => h g (List.mem_append_left _ (mem_flatMap_range hr hg))) htt
  rw [Gate.holds_or] at hor
  rw [hor, hmatch, hprev, Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (⟨s, hs, h⟩ | h)
    · exact ⟨s, by omega, h⟩
    · exact ⟨r, by omega, h⟩
  · rintro ⟨s, hs, h⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
    · exact Or.inl ⟨s, hs, h⟩
    · exact Or.inr h

/-- The output of pattern `r` of the table chain is the disjunction over patterns up to `r`. -/
private theorem tableGadget_chain {β tt ff w : ℕ} {pats : List (List (ℕ × Bool))}
    (h : ∀ g ∈ tableGadget β tt ff w pats, g.Holds σ) (htt : σ tt = true) (hff : σ ff = false)
    (r : ℕ) (hr : r < pats.length) :
    σ (β + 2 * w * pats.length + r) =
      decide (∃ s < r + 1, ∀ l ∈ pats.getD s [], σ l.1 = l.2) := by
  induction r with
  | zero => exact tableGadget_step σ h htt hr (by simp [hff])
  | succ r ih =>
    refine tableGadget_step σ h htt hr ?_
    rw [ite_eq_right (by omega),
      show β + 2 * w * pats.length + (r + 1) - 1 = β + 2 * w * pats.length + r by omega]
    exact ih (by omega)

/-- **The value of `tableGadget`**: whether some pattern matches. -/
theorem tableGadget_out {β tt ff w : ℕ} {pats : List (List (ℕ × Bool))}
    (h : ∀ g ∈ tableGadget β tt ff w pats, g.Holds σ) (htt : σ tt = true) (hff : σ ff = false) :
    σ (tableOut β ff w pats.length) = decide (∃ π ∈ pats, ∀ l ∈ π, σ l.1 = l.2) := by
  unfold tableOut
  split_ifs with hR
  · rw [List.length_eq_zero_iff] at hR
    simp [hR, hff]
  · rw [show β + 2 * w * pats.length + pats.length - 1 =
      β + 2 * w * pats.length + (pats.length - 1) by omega,
      tableGadget_chain σ h htt hff (pats.length - 1) (by omega), Nat.sub_add_cancel (by omega),
      Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    constructor
    · rintro ⟨s, hs, h⟩
      exact ⟨pats.getD s [], List.getD_mem _ hs, h⟩
    · rintro ⟨π, hπ, h⟩
      obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hπ
      refine ⟨s, hs, ?_⟩
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs, Option.getD_some]

end Gadgets

/-! ### Extending assignments to defined variables -/

/-- The value of a variable, defined by recursion along `rank`: a variable with a defining gate gets
the value of the gate on variables of smaller rank, and any other keeps its value under `σ₀`. -/
private noncomputable def extension (σ₀ : ℕ → Bool) (dfn : ℕ → Option Gate) (rank : ℕ → ℕ) (v : ℕ) :
    Bool :=
  match dfn v with
  | none => σ₀ v
  | some g => Gate.eval (fun u => if _h : rank u < rank v then extension σ₀ dfn rank u else false) g
termination_by rank v
decreasing_by assumption

/-- The defining equation of `extension`, as a rewriting rule. -/
private theorem extension_eq (σ₀ : ℕ → Bool) (dfn : ℕ → Option Gate) (rank : ℕ → ℕ) (v : ℕ) :
    extension σ₀ dfn rank v = match dfn v with
      | none => σ₀ v
      | some g => Gate.eval (fun u => if _h : rank u < rank v then extension σ₀ dfn rank u
          else false) g := by
  rw [extension]

/-- **Assignments extend to the variables that gates define**, when each defining gate computes
its own output from variables of smaller rank. -/
theorem exists_extension (σ₀ : ℕ → Bool) (dfn : ℕ → Option Gate) (rank : ℕ → ℕ)
    (hdfn : ∀ v g, dfn v = some g → g.op.IsDefining ∧ g.out = v ∧ rank g.a < rank v ∧
      rank g.b < rank v ∧ rank g.c < rank v) :
    ∃ σ : ℕ → Bool, (∀ v, dfn v = none → σ v = σ₀ v) ∧ ∀ v g, dfn v = some g → g.Holds σ := by
  refine ⟨extension σ₀ dfn rank, fun v hv => ?_, fun v g hg => ?_⟩
  · rw [extension_eq, hv]
  · obtain ⟨hop, hout, ha, hb, hc⟩ := hdfn v g hg
    have hv := extension_eq σ₀ dfn rank v
    rw [hg] at hv
    obtain ⟨op, o, a, b, c⟩ := g
    obtain ⟨h1, h2⟩ := hop
    obtain rfl : o = v := hout
    cases op
    all_goals try first | exact absurd rfl h1 | exact absurd rfl h2
    all_goals simp only [Gate.Holds, hv, Gate.eval, ha, hb, hc, dite_true]

end Cslib.Complexity.CookLevin.Quasilinear
