/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of the fin_index tactic)

public import CslibFrontier.Tactic.FinIndex

/-!
# Tests for `fin_index`
-/

public section

namespace FinIndexTest

/-- A layout slot: block `q`, offset `r`. -/
@[expose] def slot (q : Fin 27) (r : Fin 6) : Fin 162 := ⟨6 * q.val + r.val, by omega⟩

/-- Two register banks placed one after the other. -/
@[expose] def left {a b : ℕ} (i : Fin a) : Fin (a + b + 1) := ⟨i.val, by omega⟩

/-- The second bank, after the separator at index `a`. -/
@[expose] def right {a b : ℕ} (j : Fin b) : Fin (a + b + 1) := ⟨a + 1 + j.val, by omega⟩

/-- A definition that branches on its index. -/
@[expose] def skip (i : Fin 5) : Fin 9 := if i.val = 0 then ⟨7, by omega⟩ else ⟨i.val, by omega⟩

/-! Constructors and casts need no list. -/

example (a b : ℕ) (ha : a < 9) (hb : b < 9) (h : a ≠ b) : (⟨a, ha⟩ : Fin 9) ≠ ⟨b, hb⟩ := by
  fin_index

example (n k : ℕ) (hk : k < n) (i : Fin n) (h : k + 1 ≤ i.val) : i ≠ ⟨k, hk⟩ := by
  fin_index

example (m n : ℕ) (i : Fin m) (j : Fin n) : Fin.castAdd n i ≠ Fin.natAdd m j := by
  fin_index

example (n : ℕ) (i : Fin n) : i.castSucc < Fin.last n ∧ i.castSucc < i.succ := by
  constructor <;> fin_index

example (n : ℕ) (i : Fin (n + 1)) (h : i ≠ 0) : (0 : Fin (n + 1)) < i := by
  fin_index

example (n : ℕ) (i : Fin (n + 2)) (h : i ≠ Fin.last (n + 1)) : i.rev ≠ 0 := by
  fin_index

example (n : ℕ) : Function.Injective (Fin.castSucc : Fin n → Fin (n + 1)) := by
  fin_index

example (i : Fin 9) (h : 4 ≤ i.val) : i ≠ ⟨0, by omega⟩ ∧ i ≠ ⟨3, by omega⟩ := by
  fin_index

/-! Definitions are named at the call, as are local `let` variables. -/

example (i : Fin 162) : ∃ q r, slot q r = i :=
  ⟨⟨i.val / 6, by omega⟩, ⟨i.val % 6, by omega⟩, by fin_index [slot]⟩

example (i : Fin 162) : True := by
  let q : Fin 27 := ⟨i.val / 6, by omega⟩
  let r : Fin 6 := ⟨i.val % 6, by omega⟩
  have : slot q r = i := by fin_index [slot, q, r]
  trivial

example {a b : ℕ} (i : Fin a) (j : Fin b) : left (b := b) i ≠ right j := by
  fin_index [left, right]

example {a b : ℕ} : Function.Injective (right : Fin b → Fin (a + b + 1)) := by
  fin_index [right]

example {a b : ℕ} (i j : Fin b) (h : i < j) : right (a := a) i < right j := by
  fin_index [right]

/-! A fact about values can stand in for the definition. -/

example {r : ℕ} {f : Fin r → Fin 16} (hf : ∀ i, (f i).val = i.val + 7) :
    Function.Injective f := by
  fin_index [hf]

/-! Facts in context are used in the form they have. -/

example {a b : ℕ} (i j : Fin b) (h : right (a := a) i = right j) (hne : i ≠ j) : False := by
  fin_index [right]

example (n : ℕ) (i j : Fin n) (h : ¬ i ≤ j) : j < i := by
  fin_index

/-! A hypothesis that a term depends on is used too: here `hk` under `k.pred hk`. -/

example (n : ℕ) (k : Fin (n + 2)) (hk : k ≠ 0) (j : Fin (n + 1)) (h : j = k.pred hk) :
    j.castSucc < k := by
  fin_index

example (q q' : Fin 27) (r r' : Fin 6) : slot q r = slot q' r' → q = q' ∧ r = r' := by
  intro h
  constructor <;> fin_index [slot]

/-! Pairs of indices: pass `Prod.mk.injEq`. -/

example (n : ℕ) (i j : Fin n) (h : (i.castSucc, j.succ) = (j.castSucc, i.succ)) : i = j := by
  fin_index [Prod.mk.injEq]

/-! A definition that branches on an `if`: the cases are split. -/

example : Function.Injective skip := by
  fin_index [skip]

example (i : Fin 5) : skip i ≠ ⟨0, by omega⟩ := by
  fin_index [skip]

/-! On failure the error of `omega` ends with a note: the goal as `omega` received it, and what
to do about a definition that is still folded. -/

/--
error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  e ≥ 0
  d ≥ 0
  c ≥ 0
  c - d - e ≤ 0
where
 c := ↑↑(right j)
 d := ↑a
 e := ↑b

Note: fin_index rewrote the goal and the hypotheses to comparisons of numbers, and `omega` could
not close the result, also not after splitting each `if`:
  a b : ℕ
  i : Fin a
  j : Fin b
  ⊢ ¬↑(left i) = ↑(right j)
A term in the `where` list of `omega`, such as `↑(f i)`, names a definition to unfold:
`fin_index [f]`.
-/
#guard_msgs in
example {a b : ℕ} (i : Fin a) (j : Fin b) : left (b := b) i ≠ right j := by
  fin_index

/-! A false goal: the note shows it, and the hypotheses, as comparisons of numbers. -/

/--
  h : a + 1 + ↑i ≤ a + 1 + ↑j
  ⊢ a + 1 + ↑i < a + 1 + ↑j
-/
#guard_msgs (substring := true) in
example {a b : ℕ} (i j : Fin b) (h : right (a := a) i ≤ right j) : right (a := a) i < right j := by
  fin_index [right]

/-! Splitting does not hide a false goal: the report is the one from before the split. -/

/-- ⊢ (if ↑i = 0 then 7 else ↑i) = if ↑j = 0 then 7 else ↑j -/
#guard_msgs (substring := true) in
example (i j : Fin 5) : skip i = skip j := by
  fin_index [skip]

/-! A bad name in the list reports the real error. -/

/-- error: Unknown identifier `noSuchDefinition` -/
#guard_msgs in
example (n : ℕ) (i : Fin n) : i.castSucc ≠ Fin.last n := by
  fin_index [noSuchDefinition]

/-! The list is checked like a `simp only` list: an entry that the rewriting never used is
reported. A call that runs on several goals is judged on all of them together. -/

/--
warning: This `fin_index` list entry is unused:
  right
-/
#guard_msgs (substring := true) in
example {a b : ℕ} (i : Fin a) : left (b := b) i ≠ ⟨a, by omega⟩ := by
  fin_index [left, right]

#guard_msgs in
example {a b : ℕ} (i : Fin a) (j : Fin b) :
    left (b := b) i ≠ ⟨a, by omega⟩ ∧ right (a := a) j ≠ ⟨a, by omega⟩ := by
  constructor <;> fin_index [left, right]

#guard_msgs in
set_option linter.unusedSimpArgs false in
example {a b : ℕ} (i : Fin a) : left (b := b) i ≠ ⟨a, by omega⟩ := by
  fin_index [left, right]

end FinIndexTest
