/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.TimeM.Simps
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Loops in the time monad

Return values and costs of three loop combinators run in `Cslib.Algorithms.Lean.TimeM`:
`Vector.ofFnM`, which fills a vector cell by cell, `List.mapM` and `List.foldlM`. The return value
of each loop is the corresponding pure loop over the return values. The cost of `Vector.ofFnM` and
of `List.mapM` is the sum of the costs of the cells, and a `List.foldlM` whose step always costs `c`
costs `c` per element; more generally, if the cost of a step depends only on the element, the fold
costs the sum of the element costs, and a fold whose step costs at most `c` costs at most `c` per
element.

The equations are in the simp set `time_simps`
(`CslibFrontier.Algorithms.Lean.TimeM.Simps`), so `simp only [time_simps]` and the tactic
`time_spec` compute the return value and the cost of a program built from these loops. For a fold
the set uses `time_foldlM_eq_sum_map`, which needs no cost function; a bound is applied by name
with `time_foldlM_le`.

## Main results

* `Cslib.Algorithms.Lean.TimeM.ret_vectorOfFnM`, `time_vectorOfFnM`.
* `Cslib.Algorithms.Lean.TimeM.ret_listMapM`, `time_listMapM`.
* `Cslib.Algorithms.Lean.TimeM.ret_foldlM`, `time_foldlM_of_time_eq`, `time_foldlM_eq_sum`,
  `time_foldlM_eq_sum_map`, `time_foldlM_le`.
-/

public section

namespace Cslib.Algorithms.Lean.TimeM

/-- The vector filled by `Vector.ofFnM` in the time monad is the vector of the return values. -/
@[simp, time_simps] theorem ret_vectorOfFnM {α : Type*} : ∀ {n : ℕ} (f : Fin n → TimeM ℕ α),
    (Vector.ofFnM f).ret = Vector.ofFn fun i => (f i).ret
  | 0, f => by
    rw [Vector.ofFnM_zero]
    ext i hi
    exact absurd hi (Nat.not_lt_zero i)
  | n + 1, f => by
    rw [Vector.ofFnM_succ]
    simp only [ret_bind, ret_pure]
    rw [ret_vectorOfFnM]
    ext i hi
    rw [Vector.getElem_push, Vector.getElem_ofFn]
    split_ifs with h
    · rw [Vector.getElem_ofFn]
      rfl
    · have : i = n := by omega
      subst this
      rfl

/-- Filling a vector by `Vector.ofFnM` costs the sum of the costs of its cells. -/
@[simp, time_simps] theorem time_vectorOfFnM {α : Type*} : ∀ {n : ℕ} (f : Fin n → TimeM ℕ α),
    (Vector.ofFnM f).time = ∑ i, (f i).time
  | 0, f => by
    rw [Vector.ofFnM_zero]
    rfl
  | n + 1, f => by
    rw [Vector.ofFnM_succ]
    simp only [time_bind, time_pure, add_zero]
    rw [time_vectorOfFnM, Fin.sum_univ_castSucc]

/-- A map over a list in the time monad returns the list of the return values. -/
@[simp, time_simps] theorem ret_listMapM {α β : Type*} (f : α → TimeM ℕ β) (l : List α) :
    (l.mapM f).ret = l.map fun a => (f a).ret := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.mapM_cons, ret_bind, ret_pure, ih, List.map_cons]

/-- A map over a list in the time monad costs the sum of the costs of its elements. -/
@[simp, time_simps] theorem time_listMapM {α β : Type*} (f : α → TimeM ℕ β) (l : List α) :
    (l.mapM f).time = (l.map fun a => (f a).time).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.mapM_cons, time_bind, time_pure, ih, List.map_cons, List.sum_cons, add_zero]

/-- A fold in the time monad returns the pure fold of the return values. -/
@[simp, time_simps] theorem ret_foldlM {α β : Type*} (f : β → α → TimeM ℕ β) (l : List α) (b : β) :
    (l.foldlM f b).ret = l.foldl (fun acc a => (f acc a).ret) b := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldlM_cons, ret_bind, ih]
    rfl

/-- A fold in the time monad whose step always costs `c` costs `c` per element. -/
theorem time_foldlM_of_time_eq {α β : Type*} (f : β → α → TimeM ℕ β) (l : List α) (b : β)
    {c : ℕ} (hf : ∀ acc a, (f acc a).time = c) : (l.foldlM f b).time = l.length * c := by
  induction l generalizing b with
  | nil => simp only [List.foldlM_nil, time_pure, List.length_nil, zero_mul]
  | cons a l ih =>
    rw [List.foldlM_cons, time_bind, ih, hf, List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- A fold in the time monad whose step cost depends only on the element costs the sum of those
costs. -/
theorem time_foldlM_eq_sum {α β : Type*} (f : β → α → TimeM ℕ β) (c : α → ℕ)
    (hf : ∀ acc a, (f acc a).time = c a) (l : List α) (b : β) :
    (l.foldlM f b).time = (l.map c).sum := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih => rw [List.foldlM_cons, time_bind, ih, hf, List.map_cons, List.sum_cons]

/-- `time_foldlM_eq_sum` in a form `simp` can apply: the hypothesis says that the step cost ignores
the accumulator, and names no cost function. `simp only [time_simps]` proves the hypothesis from
the laws of the monad; see the docstring of `time_simps` for why `simp [time_simps]` may not. -/
@[time_simps] theorem time_foldlM_eq_sum_map {α β : Type*} (f : β → α → TimeM ℕ β) (l : List α)
    (b : β) (hf : ∀ acc acc' a, (f acc a).time = (f acc' a).time) :
    (l.foldlM f b).time = (l.map fun a => (f b a).time).sum :=
  time_foldlM_eq_sum f _ (fun acc a => hf acc b a) l b

/-- A fold in the time monad whose step costs at most `c` on each element of the list costs at
most `c` per element. -/
theorem time_foldlM_le {α β : Type*} (f : β → α → TimeM ℕ β) (l : List α) (b : β) {c : ℕ}
    (hf : ∀ acc, ∀ a ∈ l, (f acc a).time ≤ c) : (l.foldlM f b).time ≤ l.length * c := by
  induction l generalizing b with
  | nil => simp only [List.foldlM_nil, time_pure, List.length_nil, zero_mul, le_refl]
  | cons a l ih =>
    rw [List.foldlM_cons, time_bind, List.length_cons, Nat.succ_mul, Nat.add_comm (l.length * c)]
    exact Nat.add_le_add (hf b a List.mem_cons_self)
      (ih _ fun acc x hx => hf acc x (List.mem_cons_of_mem a hx))

end Cslib.Algorithms.Lean.TimeM
