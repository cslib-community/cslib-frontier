/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Tactic.Degree

/-! Tests of `degree`: `[f, g]` unfolding, option matches at arbitrary degrees, `Option.toList`,
list/Boolean/successor composition, and failure diagnostics. -/

namespace CslibFrontierTests.DegreeTactic

open Turing.MultiTapeTM

/-- A definition by `match` on an option. -/
def bumpOr (o : Option ℕ) (l : List ℕ) : List ℕ :=
  match o with
  | none => l
  | some n => n :: l

-- `degree [bumpOr]` unfolds `bumpOr`, rewrites the `match` to `Option.elim`, and composes.
example : ComputableInDegree (fun p : Option ℕ × List ℕ => bumpOr p.1 p.2)
    (encPair (encOption encUnary) (encList encUnary)) (encList encUnary) 1 1 := by
  degree [bumpOr]

-- General-degree `Option.elim` when a branch has higher cost degree (`d = 2, e = 1`).
def addOr (o : Option ℕ) (n : ℕ) : ℕ :=
  match o with
  | none => n
  | some m => m + n

example : ComputableInDegree (fun p : Option ℕ × ℕ => addOr p.1 p.2)
    (encPair (encOption encNat) encNat) encNat 2 1 := by
  have hadd := computableInDegree_add
  degree [addOr]

-- The head of a list, as an option, and a default.
example : ComputableInDegree (fun l : List ℕ => (l.head?).getD 0)
    (encList encUnary) encUnary 1 1 := by
  degree

-- `Option.toList` without an inhabitant of the element type.
example {α : Type} (enc : α ↪ List Bool) :
    ComputableInDegree (fun p : List α × Option α => p.1 ++ p.2.toList)
      (encPair (encList enc) (encOption enc)) (encList enc) 1 1 := by
  degree

-- Unapplied tuple-matching definition, local `let`, binary `+ 1`, and framed list append.
def stepState : (ℕ × List ℕ) → (ℕ × List ℕ)
  | (addr, acc) => (addr + 1, acc ++ [addr])

example : ComputableInDegree stepState
    (encPair encNat (encList encNat)) (encPair encNat (encList encNat)) 2 1 := by
  let localStep := stepState
  change ComputableInDegree localStep _ _ 2 1
  degree [localStep, stepState]

-- Boolean negation, `cond`, and unary zero testing.
def stepGuard (p : ℕ × Bool) : ℕ :=
  if decide (p.1 = 0) then 0 else p.1 + cond (!p.2) 1 0

example : ComputableInDegree stepGuard (encPair encUnary encBool) encUnary 1 1 := by
  degree [stepGuard]

-- Unknown identifiers in `degree [...]` fail immediately.
/-- error: Unknown constant `noSuchDef` -/
#guard_msgs in
example : ComputableInDegree (fun n : ℕ => n) encUnary encUnary 1 1 := by
  degree [noSuchDef]

-- Goals not of the form `ComputableInDegree ...` fail immediately.
/--
error: degree expects a goal `ComputableInDegree f encIn encOut d e`, got
  True
-/
#guard_msgs in
example : True := by
  degree

end CslibFrontierTests.DegreeTactic
