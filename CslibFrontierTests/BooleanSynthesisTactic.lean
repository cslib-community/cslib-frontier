/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (regression tests for Boolean expression synthesis)

import CslibFrontier.Tactic.SynthesisBool

/-! # Boolean construction keeps source wires and gate budgets explicit -/
set_option linter.privateModule false

namespace CslibFrontierTests.BooleanSynthesisTactic

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

private def updateBit {n : ℕ} (f g h j : BooleanFunction n) : BooleanFunction n :=
  fun x => f x ^^ (g x && (!h x && j x))

section Builds

variable {n : ℕ} {s : Set (BooleanFunction n)} {f g h j : BooleanFunction n}

example : Synthesis interpretation (inputs 3) {fun x => x 0} 0 := by
  synthesis_bool

example : Synthesis interpretation (∅ : Set (BooleanFunction 2)) {fun _ => true} 1 := by
  synthesis_bool

example (hf : f ∈ s) (hg : g ∈ s) (hh : h ∈ s) :
    Synthesis interpretation s {fun x => f x ^^ (g x && !h x)} 6 := by
  synthesis_bool

-- The bound need not be the sum of the gates used.
example (hf : f ∈ s) (hg : g ∈ s) (hh : h ∈ s) :
    Synthesis interpretation s {fun x => f x ^^ (g x || !h x)} (n + 10) := by
  synthesis_bool

-- The seven-gate entry update of the Gauss–Jordan client. The caller unfolds the definition.
example (hf : f ∈ s) (hg : g ∈ s) (hh : h ∈ s) (hj : j ∈ s) :
    Synthesis interpretation s {updateBit f g h j} 7 := by
  unfold updateBit
  synthesis_bool

-- A local `let` is seen through.
example (hf : f ∈ s) (hg : g ∈ s) : Synthesis interpretation s {fun x => f x || !g x} 2 := by
  let t : BooleanFunction n := fun x => f x || !g x
  change Synthesis interpretation s {t} 2
  synthesis_bool

end Builds

/-! Each failure names its cause and shows the gates counted or the function not built. -/

-- Each occurrence of the negation is charged, so three gates do not suffice.
/--
error: synthesis_bool built the expression, but its gates do not fit the bound: `omega` could not
prove the inequality below, whose left side counts the gates used.
case hab
⊢ 0 + 1 + 0 + 1 + (0 + 1) + 1 ≤ 3
-/
#guard_msgs in
example : Synthesis interpretation (inputs 3) {fun x => (!x 0 && x 1) || !x 0} 3 := by
  synthesis_bool

-- An exclusive or costs four gates.
/--
error: synthesis_bool built the expression, but its gates do not fit the bound: `omega` could not
prove the inequality below, whose left side counts the gates used.
case hab
⊢ 0 + 0 + 4 ≤ 3
-/
#guard_msgs in
example : Synthesis interpretation (inputs 2) {fun x => x 0 ^^ x 1} 3 := by
  synthesis_bool

-- A constant costs a gate even over an empty source set.
/--
error: synthesis_bool built the expression, but its gates do not fit the bound: `omega` could not
prove the inequality below, whose left side counts the gates used.
case hab
⊢ 1 ≤ 0
-/
#guard_msgs in
example : Synthesis interpretation (∅ : Set (BooleanFunction 1)) {fun _ => false} 0 := by
  synthesis_bool

-- A generous bound cannot supply a missing wire. The report names `g`, not `f`.
/--
error: synthesis_bool could not build the functions below. Each is neither a constant, nor `!`,
`&&`, `||` or `^^` applied to other functions, nor found by `synthesis_available`. Unfold
definitions before calling it, and retain missing wires first.
case h.hg.h
n : ℕ
s : Set (BooleanFunction n)
f g : BooleanFunction n
hf : f ∈ s
⊢ Synthesis interpretation s {g}
-/
#guard_msgs (substring := true) in
example {n : ℕ} {s : Set (BooleanFunction n)} {f g : BooleanFunction n} (hf : f ∈ s) :
    Synthesis interpretation s {fun x => f x && !g x} 100 := by
  synthesis_bool

-- A definition is not unfolded into gates, although all its wires are available.
/--
error: synthesis_bool could not build the functions below. Each is neither a constant, nor `!`,
`&&`, `||` or `^^` applied to other functions, nor found by `synthesis_available`. Unfold
definitions before calling it, and retain missing wires first.
case h
n : ℕ
s : Set (BooleanFunction n)
f g h j : BooleanFunction n
hf : f ∈ s
hg : g ∈ s
hh : h ∈ s
hj : j ∈ s
⊢ Synthesis interpretation s {updateBit f g h j}
-/
#guard_msgs (substring := true) in
example {n : ℕ} {s : Set (BooleanFunction n)} {f g h j : BooleanFunction n}
    (hf : f ∈ s) (hg : g ∈ s) (hh : h ∈ s) (hj : j ∈ s) :
    Synthesis interpretation s {updateBit f g h j} 7 := by
  synthesis_bool

-- A compound wire is not reused: the available exclusive or is built again, and its operand `f`
-- is not available.
/--
error: synthesis_bool could not build the functions below. Each is neither a constant, nor `!`,
`&&`, `||` or `^^` applied to other functions, nor found by `synthesis_available`. Unfold
definitions before calling it, and retain missing wires first.
case h.hf.hf
n : ℕ
s : Set (BooleanFunction n)
f g h : BooleanFunction n
hfg : (fun x => f x ^^ g x) ∈ s
hh : h ∈ s
⊢ Synthesis interpretation s {f}
-/
#guard_msgs (substring := true) in
example {n : ℕ} {s : Set (BooleanFunction n)} {f g h : BooleanFunction n}
    (hfg : (fun x => f x ^^ g x) ∈ s) (hh : h ∈ s) :
    Synthesis interpretation s {fun x => (f x ^^ g x) && h x} 1 := by
  synthesis_bool

/--
error: synthesis_bool proves goals of the form `Synthesis interpretation s {f} n`.
p : Prop
⊢ p
-/
#guard_msgs in
example (p : Prop) : p := by
  synthesis_bool

end CslibFrontierTests.BooleanSynthesisTactic
