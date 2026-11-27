/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of the time_simps simp set and the time_spec tactic)

public import CslibFrontier.Algorithms.Lean.TimeM.Loops

/-!
# Tests for `time_simps` and `time_spec`
-/

public section

namespace CslibFrontierTests.TimeMSpec

open Cslib.Algorithms.Lean TimeM

/-! A recursive program: one goal for each branch, closed with the induction hypothesis. -/

/-- Sum a list, one tick for each element. -/
def sumM : List ℕ → TimeM ℕ ℕ
  | [] => pure 0
  | x :: xs => do
    tick 1
    let s ← sumM xs
    pure (x + s)

@[time_simps] theorem ret_sumM (l : List ℕ) : (sumM l).ret = l.sum := by
  time_spec sumM

@[time_simps] theorem time_sumM (l : List ℕ) : (sumM l).time = l.length := by
  time_spec sumM

/-- The variables of a statement that binds them are introduced first. -/
example : ∀ l : List ℕ, (sumM l).time = l.length := by
  time_spec sumM

/-! A program that is not recursive is opened by `fun_cases`. The specifications of the programs it
calls come from the simp set; the definition of the pure function it computes is passed. -/

/-- Compare the sums of two lists. -/
def leM (l₁ l₂ : List ℕ) : TimeM ℕ Bool := do
  let a ← sumM l₁
  let b ← sumM l₂
  tick 1
  pure (decide (a ≤ b))

/-- What `leM` computes. -/
def sumLe (l₁ l₂ : List ℕ) : Bool := decide (l₁.sum ≤ l₂.sum)

example (l₁ l₂ : List ℕ) : (leM l₁ l₂).time = l₁.length + l₂.length + 1 := by
  time_spec leM

example (l₁ l₂ : List ℕ) : (leM l₁ l₂).ret = sumLe l₁ l₂ := by
  time_spec leM [sumLe]

/-- Both halves of a specification at once. -/
example (l₁ l₂ : List ℕ) :
    (leM l₁ l₂).ret = sumLe l₁ l₂ ∧ (leM l₁ l₂).time = l₁.length + l₂.length + 1 := by
  time_spec leM [sumLe]

/-- The simp set alone. -/
example (l₁ l₂ : List ℕ) : (leM l₁ l₂).time = l₁.length + l₂.length + 1 := by
  simp only [leM, time_simps]
  omega

/-! A bound from a hypothesis on the step, through an `if` on a computed value, which is split. -/

/-- The first element on which `f` answers `true`. -/
def findM {α : Type} (f : α → TimeM ℕ Bool) : List α → TimeM ℕ (Option α)
  | [] => pure none
  | a :: l => do
    let b ← f a
    if b then pure (some a) else findM f l

theorem ret_findM {α : Type} (f : α → TimeM ℕ Bool) (l : List α) :
    (findM f l).ret = l.find? fun a => (f a).ret := by
  time_spec findM [List.find?]

theorem time_findM_le {α : Type} (f : α → TimeM ℕ Bool) (l : List α) (c : ℕ)
    (hf : ∀ a ∈ l, (f a).time ≤ c) : (findM f l).time ≤ l.length * c := by
  time_spec findM

/-! Arithmetic that `omega` does not do is passed as a fact, here `(k + 1) * c = k * c + c`: the
proof then ends in `rfl` or `omega`, without `grind`. -/

/-- Run a program `k` times. -/
def repeatM (p : TimeM ℕ Unit) : ℕ → TimeM ℕ Unit
  | 0 => pure ()
  | k + 1 => do
    repeatM p k
    p

example (p : TimeM ℕ Unit) (k : ℕ) : (repeatM p k).time = k * p.time := by
  time_spec repeatM [Nat.succ_mul]

/-! A bound that needs the bound of a called program is not a job for `time_spec`: the simp set
computes the cost of the unfolded program, the bounds of the called programs are stated, and
arithmetic finishes. -/

/-- Search two lists. -/
def find₂M {α : Type} (f : α → TimeM ℕ Bool) (l₁ l₂ : List α) : TimeM ℕ Bool := do
  let a ← findM f l₁
  let b ← findM f l₂
  pure (a.isSome || b.isSome)

example {α : Type} (f : α → TimeM ℕ Bool) (l₁ l₂ : List α) (c : ℕ)
    (hf : ∀ a, (f a).time ≤ c) : (find₂M f l₁ l₂).time ≤ (l₁.length + l₂.length) * c := by
  simp only [find₂M, time_simps]
  guard_target = (findM f l₁).time + (findM f l₂).time ≤ (l₁.length + l₂.length) * c
  have h₁ := time_findM_le f l₁ c fun a _ => hf a
  have h₂ := time_findM_le f l₂ c fun a _ => hf a
  rw [Nat.add_mul]
  omega

/-! The failure report. A goal that cannot be closed is left as the simp step produced it: the `if`
is not split, and the branch that was closed is gone. Here the bound is false. -/

/--
error: unsolved goals
case case2
α : Type
f : α → TimeM ℕ Bool
a✝ : α
l✝ : List α
ih1✝ : (findM f l✝).time ≤ l✝.length
⊢ (f a✝).time + (if (f a✝).ret = true then pure (some a✝) else findM f l✝).time ≤ l✝.length + 1
-/
#guard_msgs in
example {α : Type} (f : α → TimeM ℕ Bool) (l : List α) : (findM f l).time ≤ l.length := by
  time_spec findM

/-! The tactic fails only when the program cannot be opened: here the goal has no call of `sumM`. -/

/--
error: Could not find suitable call of `sumM` in the goal
-/
#guard_msgs in
example (l₁ l₂ : List ℕ) : (leM l₁ l₂).time = l₁.length + l₂.length + 1 := by
  time_spec sumM

/-! Loops. A fold whose step cost does not depend on the accumulator costs the sum of the step
costs, and `simp only [time_simps]` finds this without being told the cost. -/

/-- Sum a list with a fold, one tick for each element. -/
def foldSumM (l : List ℕ) : TimeM ℕ ℕ :=
  l.foldlM (fun acc x => do tick 1; pure (acc + x)) 0

example (l : List ℕ) : (foldSumM l).time = l.length := by
  time_spec foldSumM

example (l : List ℕ) : (foldSumM l).ret = l.foldl (· + ·) 0 := by
  time_spec foldSumM

/-- A cost that depends on the element. -/
example (l : List (List ℕ)) :
    (l.foldlM (fun acc x => do let s ← sumM x; pure (acc + s)) 0).time =
      (l.map List.length).sum := by
  simp only [time_simps]

/-- `simp` with its default set does not always use the fold lemma: once `bind_pure_comp` has
rewritten the step to `(fun _ => g acc x) <$> tick 1`, it proves the side condition and then fails
to use the proof. Run `simp only [time_simps]` first, as `time_spec` does. -/
example {β : Type} (g : β → ℕ → β) (b : β) (l : List ℕ) :
    (l.foldlM (fun acc x => do tick 1; pure (g acc x)) b).time = l.length := by
  fail_if_success (simp [time_simps]; done)
  simp only [time_simps]
  simp

/-- A bound on a fold from a bound on its step. -/
example {α : Type} (f : α → TimeM ℕ Bool) (l : List (List α)) (c : ℕ)
    (hf : ∀ a, (f a).time ≤ c) (hl : ∀ x ∈ l, x.length ≤ 3) :
    (l.foldlM (fun acc x => do let r ← findM f x; pure (acc || r.isSome)) false).time ≤
      l.length * (3 * c) := by
  refine time_foldlM_le _ _ _ fun acc x hx => ?_
  have h := time_findM_le f x c fun a _ => hf a
  have := Nat.mul_le_mul_right c (hl x hx)
  simp only [time_simps]
  omega

end CslibFrontierTests.TimeMSpec
