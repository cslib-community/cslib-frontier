/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of the wram_omega tactic)

public import CslibFrontier.Tactic.WramOmega
public import CslibFrontier.Tactic.Fits
public import CslibFrontier.Computability.WordRAM.Allocation
public import CslibFrontierTests.WramOmegaTactic.Hidden

/-!
# Tests for `wram_omega`

What the tactic unfolds (tagged numbers and predicates, also in the bodies of tagged definitions,
fields of a structure given by its constructor, local definitions), when it reads the hypotheses,
the facts given as terms, which word-size bounds are for `fits`, the linter for calls that unfold
nothing, the error messages of the tactic and of the attribute `@[wram_arith]`, and that a failed
call leaves nothing behind.
-/

public section

open Cslib.WordRAM

namespace WramOmegaTest

/-! A memory layout in the style of the word-RAM data structures: a header of 20 words, then two
tables of `2 ^ n` words each. -/

/-- The number of words of a table. -/
@[wram_arith, expose] def tableSize (n : ℕ) : ℕ := 2 ^ n

/-- The address of the first table. -/
@[wram_arith, expose] def t1Base (base : ℕ) : ℕ := base + 20

/-- The address of the second table. -/
@[wram_arith, expose] def t2Base (base n : ℕ) : ℕ := t1Base base + tableSize n

/-- The number of words of the structure. -/
@[wram_arith, expose] def space (n : ℕ) : ℕ := 20 + 2 * tableSize n

/-- The address `a` is in the second table. -/
@[wram_arith, expose] def InSecond (base n a : ℕ) : Prop := t2Base base n ≤ a ∧ a < base + space n

/-- The first table, as a block. -/
abbrev table (base n : ℕ) : Block := ⟨t1Base base, tableSize n⟩

/-- The signed distance from the address `a` to the first table: a tagged definition may return
an integer. -/
@[wram_arith, expose] def gap (base a : ℕ) : ℤ := (t1Base base : ℤ) - a

/-- A definition that is not tagged. -/
@[expose] def stride (n : ℕ) : ℕ := n + 1

variable {w base n a i : ℕ}

/-! The tagged definitions in the goal are unfolded, with those in their bodies; a power of two is
positive. -/

example : t2Base base n + tableSize n = base + space n := by wram_omega

example : t1Base base < t2Base base n := by wram_omega

example (h : i < tableSize n) : t2Base base n + i < base + space n := by wram_omega

example (h : a ≤ base) : 20 ≤ gap base a := by wram_omega

/-! A word-size bound on an address follows from the bound on the end of the layout. `fits` unfolds
`Fits` only, so it proves a word-size bound that needs no tagged definition unfolded, and leaves
this one to `wram_omega`. -/

example (hfit : Fits w (base + space n)) (h : i < tableSize n) : Fits w (t2Base base n + i) := by
  fail_if_success fits
  wram_omega

example (hfit : Fits w (base + 20 + i)) : Fits w (base + i) := by fits

/-! `fits` refuses a goal that is not a word-size bound, also when it follows from one. -/

example (hfit : Fits w (a + 1)) : a ≠ 2 ^ w := by
  fail_if_success fits
  wram_omega

/-! A field of a structure given by its constructor, also behind an abbreviation, is its value. -/

example : (Block.mk (t1Base base) (tableSize n)).base + 1 = base + 21 := by wram_omega

example : (table base n).base + (table base n).length = t2Base base n := by wram_omega

/-! Fields are read under a binder too, where the structure may be the bound variable. -/

example (s : Finset (ℕ × ℕ)) :
    (s.filter fun p => p.1 < (table base n).base).card ≤ s.card + tableSize n := by
  wram_omega [Finset.card_filter_le s fun p => p.1 < (table base n).base]

/-! Hypotheses about the layout are read unfolded when the goal needs them, including tagged
predicates and those of the library over a structure. -/

example (h : t2Base base n ≤ a) : t1Base base < a := by wram_omega

example (h : InSecond base n a) : ¬(Block.mk (t1Base base) (tableSize n)).Owns a := by wram_omega

example (h : (table base n).Owns a) : a < t2Base base n := by wram_omega

/-! A fact given as a term is unfolded like the goal. `omega` reads a product as an unknown. -/

example (h : i * i < tableSize n) : t1Base base + i * i < t2Base base n := by wram_omega [h]

example (h : a ≤ i) : t1Base base + a * n ≤ t1Base base + i * n := by
  wram_omega [Nat.mul_le_mul_right n h]

/-! A local definition whose value mentions the layout is unfolded with the goal. One that does
not is unfolded when the goal needs it. -/

example : True := by
  set S := space n
  have : 20 < S := by wram_omega
  trivial

example : True := by
  set k := n + 1
  have : t1Base base + k = base + n + 21 := by wram_omega
  trivial

/-! So is a local definition in the argument of a function, and a local function is applied. -/

example (f : ℕ → ℕ) : True := by
  let k := n + 1
  have : f k ≤ f (n + 1) := by wram_omega
  trivial

example : True := by
  let bound : ℕ → ℕ := fun i => t1Base base + i
  have : base < bound 3 := by wram_omega
  trivial

/-! A definition tagged in its own module needs no `@[expose]` there. -/

/-- An address whose definition is not exposed. -/
@[wram_arith] def footerBase (base n : ℕ) : ℕ := base + space n

example : t2Base base n < footerBase base n := by wram_omega

/-! When nothing was unfolded, `omega` proves the goal and the linter asks for it. -/

/--
warning: `wram_omega` unfolded no `@[wram_arith]` definition here: `omega` proves this goal.

Note: This linter can be disabled with `set_option linter.unnecessaryWramOmega false`
-/
#guard_msgs in
example (h : a ≤ i) : a < stride i := by
  unfold stride
  wram_omega

/-! `omega` reads a `let` inside a term as an unknown. The tactic reduces it, so the linter does
not ask for `omega` here. -/

#guard_msgs in
example : (let k := n + 1; k + 1) ≤ n + 2 := by
  fail_if_success omega
  wram_omega

/-! Failures. -/

/--
error: wram_omega: `omega` could not prove the goal with the `@[wram_arith]` definitions and the local definitions unfolded in the goal and in the arithmetic hypotheses. Products are unknowns to `omega`: give bounds on them with `wram_omega [h]`.
No `@[wram_arith]` definition occurs in the goal or in an arithmetic hypothesis.
omega could not prove the goal:
a possible counterexample may satisfy the constraints
  c ≥ 0
  b ≥ 0
  b - c ≥ 0
where
 b := ↑i
 c := ↑(stride i)
-/
#guard_msgs in
example : i < stride i := by wram_omega

/--
error: wram_omega: `omega` could not prove the goal with the `@[wram_arith]` definitions and the local definitions unfolded in the goal and in the arithmetic hypotheses. Products are unknowns to `omega`: give bounds on them with `wram_omega [h]`.
Unfolded: `t1Base`.
Tagged `@[wram_arith]` but not unfolded, as their bodies are not visible in this module: `sealedBase`.
omega could not prove the goal:
a possible counterexample may satisfy the constraints
  c ≥ 0
  b ≥ 0
  b - c ≥ 20
where
 b := ↑(sealedBase base)
 c := ↑base
-/
#guard_msgs in
example : sealedBase base < t1Base base := by wram_omega

/-! What `@[wram_arith]` rejects. -/

/-- A definition that returns neither a number nor a proposition. -/
def cells (base : ℕ) : List ℕ := [base, base + 1]

/--
error: @[wram_arith]: `cells` returns neither a natural number, an integer nor a proposition; `wram_omega` reasons by linear arithmetic over `ℕ` and `ℤ`.
-/
#guard_msgs in
attribute [local wram_arith] cells

/-- A definition by recursion. -/
def chainEnd : ℕ → ℕ
  | 0 => 0
  | n + 1 => chainEnd n + 3

/--
error: @[wram_arith]: `chainEnd` is defined by recursion, so it has no body that `wram_omega` could unfold.
-/
#guard_msgs in
attribute [local wram_arith] chainEnd

/--
error: @[wram_arith]: `Nat.succ_le_of_lt` is not a definition whose body is visible here, so `wram_omega` could not unfold it.
-/
#guard_msgs in
attribute [local wram_arith] Nat.succ_le_of_lt

/-! A failed call leaves the goal as it was, for the next alternative. The first alternative never
succeeds here, which the unused-tactic linter reports: a failed `wram_omega` restores the state,
where a failed `omega` leaves the goal assigned. -/

set_option linter.unusedTactic false in
example : i < stride i := by
  first
    | wram_omega
    | exact Nat.lt_succ_self i

/-! `wram_arith` and `wram_omega` are not reserved words. -/

example (wram_arith wram_omega : ℕ) : wram_arith + wram_omega = wram_omega + wram_arith := by
  omega

/-! Nothing is left behind. `omega` proofs are checked by the kernel as declarations of their own,
and Lean keeps the statement of a declaration that the kernel rejects as an axiom unless the state
is restored. No declaration of this file is an axiom, also after the failed calls above. -/

open Lean Elab Command in
run_cmd do
  let leftover := (← getEnv).checked.get.constants.map₂.foldl (init := #[]) fun acc name info =>
    if info matches .axiomInfo _ then acc.push name else acc
  unless leftover.isEmpty do
    throwError "wram_omega left axioms in the environment: {leftover}"

end WramOmegaTest

end
