/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of the layout_omega tactic)

public import CslibFrontier.Tactic.LayoutOmega
public import CslibFrontier.Computability.WordRAM.Allocation
public import CslibFrontierTests.LayoutOmegaTactic.Hidden

/-!
# Tests for `layout_omega`

What the tactic unfolds (tagged numbers and predicates, also in the bodies of tagged definitions,
fields of a structure given by its constructor, local definitions), when it reads the hypotheses,
the facts given as terms, the linter for calls that unfold nothing, and the error messages of the
tactic and of the attribute `@[layout]`.
-/

public section

open Cslib.WordRAM

namespace LayoutOmegaTest

/-! A layout in the style of the word-RAM data structures: a header of 20 words, then two tables
of `2 ^ n` words each. -/

/-- The number of words of a table. -/
@[layout, expose] def tableSize (n : ℕ) : ℕ := 2 ^ n

/-- The address of the first table. -/
@[layout, expose] def t1Base (base : ℕ) : ℕ := base + 20

/-- The address of the second table. -/
@[layout, expose] def t2Base (base n : ℕ) : ℕ := t1Base base + tableSize n

/-- The number of words of the structure. -/
@[layout, expose] def space (n : ℕ) : ℕ := 20 + 2 * tableSize n

/-- The address `a` is in the second table. -/
@[layout, expose] def InSecond (base n a : ℕ) : Prop := t2Base base n ≤ a ∧ a < base + space n

/-- The first table, as a block. -/
abbrev table (base n : ℕ) : Block := ⟨t1Base base, tableSize n⟩

/-- A definition that is not part of the layout. -/
@[expose] def stride (n : ℕ) : ℕ := n + 1

variable {w base n a i : ℕ}

/-! The tagged definitions in the goal are unfolded, with those in their bodies; a power of two is
positive. -/

example : t2Base base n + tableSize n = base + space n := by layout_omega

example : t1Base base < t2Base base n := by layout_omega

example (h : i < tableSize n) : t2Base base n + i < base + space n := by layout_omega

/-! A word-size bound on an address follows from the bound on the end of the layout. -/

example (hfit : Fits w (base + space n)) (h : i < tableSize n) : Fits w (t2Base base n + i) := by
  layout_omega

/-! A field of a structure given by its constructor, also behind an abbreviation, is its value. -/

example : (Block.mk (t1Base base) (tableSize n)).base + 1 = base + 21 := by layout_omega

example : (table base n).base + (table base n).length = t2Base base n := by layout_omega

/-! Fields are read under a binder too, where the structure may be the bound variable. -/

example (s : Finset (ℕ × ℕ)) :
    (s.filter fun p => p.1 < (table base n).base).card ≤ s.card + tableSize n := by
  layout_omega [Finset.card_filter_le s fun p => p.1 < (table base n).base]

/-! Hypotheses about the layout are read unfolded when the goal needs them, including tagged
predicates and those of the library over a structure. -/

example (h : t2Base base n ≤ a) : t1Base base < a := by layout_omega

example (h : InSecond base n a) : ¬(Block.mk (t1Base base) (tableSize n)).Owns a := by layout_omega

example (h : (table base n).Owns a) : a < t2Base base n := by layout_omega

/-! A fact given as a term is unfolded like the goal. `omega` reads a product as an unknown. -/

example (h : i * i < tableSize n) : t1Base base + i * i < t2Base base n := by layout_omega [h]

example (h : a ≤ i) : t1Base base + a * n ≤ t1Base base + i * n := by
  layout_omega [Nat.mul_le_mul_right n h]

/-! A local definition whose value mentions the layout is unfolded with the goal. One that does
not is unfolded when the goal needs it. -/

example : True := by
  set S := space n
  have : 20 < S := by layout_omega
  trivial

example : True := by
  set k := n + 1
  have : t1Base base + k = base + n + 21 := by layout_omega
  trivial

/-! So is a local definition in the argument of a function, and a local function is applied. -/

example (f : ℕ → ℕ) : True := by
  let k := n + 1
  have : f k ≤ f (n + 1) := by layout_omega
  trivial

example : True := by
  let bound : ℕ → ℕ := fun i => t1Base base + i
  have : base < bound 3 := by layout_omega
  trivial

/-! A definition tagged in its own module needs no `@[expose]` there. -/

/-- An address whose definition is not exposed. -/
@[layout] def footerBase (base n : ℕ) : ℕ := base + space n

example : t2Base base n < footerBase base n := by layout_omega

/-! When nothing was unfolded, `omega` proves the goal and the linter asks for it. -/

/--
warning: `layout_omega` unfolded no `@[layout]` definition here: `omega` proves this goal.

Note: This linter can be disabled with `set_option linter.unnecessaryLayoutOmega false`
-/
#guard_msgs in
example (h : a ≤ i) : a < stride i := by
  unfold stride
  layout_omega

/-! Failures. -/

/--
error: layout_omega: `omega` could not prove the goal with the `@[layout]` definitions and the local definitions unfolded in the goal and in the arithmetic hypotheses. Products are unknowns to `omega`: give bounds on them with `layout_omega [h]`.
No `@[layout]` definition occurs in the goal or in an arithmetic hypothesis.
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
example : i < stride i := by layout_omega

/--
error: layout_omega: `omega` could not prove the goal with the `@[layout]` definitions and the local definitions unfolded in the goal and in the arithmetic hypotheses. Products are unknowns to `omega`: give bounds on them with `layout_omega [h]`.
Unfolded: `t1Base`.
Tagged `@[layout]` but not unfolded, as their bodies are not visible in this module: `sealedBase`.
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
example : sealedBase base < t1Base base := by layout_omega

/-! What `@[layout]` rejects. -/

/-- A definition that returns neither a number nor a proposition. -/
def cells (base : ℕ) : List ℕ := [base, base + 1]

/--
error: @[layout]: `cells` returns neither a natural number, an integer nor a proposition; `layout_omega` reasons by linear arithmetic over `ℕ` and `ℤ`.
-/
#guard_msgs in
attribute [local layout] cells

/-- A definition by recursion. -/
def chainEnd : ℕ → ℕ
  | 0 => 0
  | n + 1 => chainEnd n + 3

/--
error: @[layout]: `chainEnd` is defined by recursion, so it has no body that `layout_omega` could unfold.
-/
#guard_msgs in
attribute [local layout] chainEnd

/--
error: @[layout]: `Nat.succ_le_of_lt` is not a definition whose body is visible here, so `layout_omega` could not unfold it.
-/
#guard_msgs in
attribute [local layout] Nat.succ_le_of_lt

/-! `layout` and `layout_omega` are not reserved words: the library has definitions and variables
named `layout`. -/

example (layout layout_omega : ℕ) : layout + layout_omega = layout_omega + layout := by omega

end LayoutOmegaTest

end
