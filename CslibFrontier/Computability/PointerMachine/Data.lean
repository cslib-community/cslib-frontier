/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Basic

/-!
# Data invariants for pointer machines

A predicate on data that holds of the undefined value and is closed under the operations of the
model is preserved by execution. This separates a general data basis from restricted ones such
as equality-only symbols.

## Main definitions

* `Model.Closed`, `State.DataValid`: closed data predicates and their state invariant.

## Main results

* `Runs.dataValid`, `Executes.dataValid`: preservation through runs and halting executions.
-/

public section

namespace Cslib.PointerMachine

variable {M : Model} {L : Layout}

/-- A predicate on data which holds of `undefined` and is closed under every operation. -/
@[expose] def Model.Closed (M : Model) (P : M.Value → Prop) : Prop :=
  P M.undefined ∧ ∀ o a b, P a → P b → P (M.evalOp o a b)

/-- All data in registers and records satisfy a predicate. -/
@[expose] def State.DataValid (x : State M L) (P : M.Value → Prop) : Prop :=
  (∀ s, P (x.data s)) ∧ ∀ n ∈ x.heap, ∀ f, P (n.data f)

/-- An instruction transports a data predicate when old values, newly allocated values,
and operation results all satisfy the target predicate. -/
theorem Instr.effect_dataValid_of {P Q : M.Value → Prop}
    (promote : ∀ a, P a → Q a) (undefined : Q M.undefined)
    (operation : ∀ o a b, P a → P b → Q (M.evalOp o a b)) {i : Instr M L}
    {x : State M L} (hx : x.DataValid P) : (i.effect x).DataValid Q := by
  obtain ⟨hr, hh⟩ := hx
  have old : x.DataValid Q := ⟨fun s => promote _ (hr s),
    fun n hn f => promote _ (hh n hn f)⟩
  have set (s : Fin L.dataRegs) {v : M.Value} (hv : Q v) : (x.setData s v).DataValid Q :=
    ⟨fun s' => by simp only [State.setData, Function.update_apply]; split_ifs <;> simp_all,
      old.2⟩
  cases i <;> simp only [Instr.effect]
  case moveData s s' => exact set s (old.1 s')
  case op o s s₁ s₂ => exact set s (operation o _ _ (hr s₁) (hr s₂))
  case loadData s f base =>
    cases hn : x.deref base with
    | none => exact old
    | some n =>
      obtain ⟨a, -, ha⟩ := State.deref_eq_some.mp hn
      exact set s (old.2 n (List.mem_of_getElem? ha) f)
  case loadPtr r f base => cases x.deref base <;> exact old
  case storePtr f base r =>
    refine ⟨by simpa using old.1, fun n hn f' => ?_⟩
    rcases State.mem_heap_modify hn with hn | ⟨m, hm, rfl⟩
    · exact old.2 n hn f'
    · exact old.2 m hm f'
  case storeData f base s =>
    refine ⟨by simpa using old.1, fun n hn f' => ?_⟩
    rcases State.mem_heap_modify hn with hn | ⟨m, hm, rfl⟩
    · exact old.2 n hn f'
    · simp only [Function.update_apply]
      split_ifs
      · exact old.1 s
      · exact old.2 m hm f'
  case create r =>
    refine ⟨old.1, fun n hn f => ?_⟩
    rcases List.mem_append.mp hn with hn | hn
    · exact old.2 n hn f
    · rw [List.mem_singleton.mp hn]
      exact undefined
  all_goals exact old

/-- Closed predicates on data survive every instruction. -/
theorem Instr.effect_dataValid {P : M.Value → Prop} (closed : M.Closed P) {i : Instr M L}
    {x : State M L} (hx : x.DataValid P) : (i.effect x).DataValid P :=
  i.effect_dataValid_of (fun _ h => h) closed.1 closed.2 hx

/-- Data invariants are preserved through an entire run. -/
theorem Runs.dataValid {P : M.Value → Prop} (closed : M.Closed P)
    {code : List (Instr M L)} {x y : State M L} {n : ℕ}
    (h : Runs code x y n) (hx : x.DataValid P) : y.DataValid P := by
  induction h with
  | refl => exact hx
  | tail _ _ _ _ hxy ih =>
    obtain ⟨i, -, -, rfl⟩ := step_eq_some_iff.mp hxy
    exact i.effect_dataValid closed ih

/-- Closed data predicates survive successful execution. -/
theorem Executes.dataValid {P : M.Value → Prop} (closed : M.Closed P)
    {code : List (Instr M L)} {x y : State M L} {time : ℕ}
    (h : Executes code x y time) (hx : x.DataValid P) : y.DataValid P := by
  obtain ⟨n, hr, -, -⟩ := h
  exact hr.dataValid closed hx

end Cslib.PointerMachine
