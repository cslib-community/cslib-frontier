/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.CDCL.System
public import CslibFrontier.Algorithms.Lean.CDCL.Assign
public import CslibFrontier.Logics.Propositional.Resolution.LRATLog
public import CslibFrontier.Algorithms.Lean.DPLL

/-! # The state and moves of the CDCL solver

The state of the executable CDCL solver (`Cslib.Algorithms.Lean.CDCL.solve`), an instance of
abstract DPLL with learning (`Cslib.Algorithms.Lean.CDCL.Step`), with its moves and their
invariant. Finding a conflict or a unit clause is left to the solver, which uses watched literals.

**State.** The solver keeps a trail of decisions and of implied literals carrying the number of
their *reason*, a clause of the log (`Cslib.Algorithms.Lean.CDCL.XEntry`), the numbered clauses of
its database, and an LRAT certificate under construction (`Cslib.Logic.PL.CNF.LRATLog`). Its
invariant (`Cslib.Algorithms.Lean.CDCL.ExecL.Inv`) is the invariant of the abstract system together
with:

* every reason contains its literal, and its other literals are false further down the trail
  (`Cslib.Algorithms.Lean.CDCL.Reasons`);
* every clause of the database is in the log under its number;
* no clause of the database is false on the part of the trail below a decision;
* the numbered clauses of the input stay in the database.

**Representation.** The solver's state `Cslib.Algorithms.Lean.CDCL.Exec` keeps the trail in two
arrays of small numbers, oldest first: the code of each literal and the code of its reason
(`Cslib.Algorithms.Lean.CDCL.ATrail`). Numbers in the scalar range of Lean's runtime are unboxed,
so an entry makes no object; the arrays are written in place when they are not shared, growing or
copying otherwise. Backjump and Restart pop the entries undone, and conflict analysis and the
backjump read the arrays position by position. The
trail read back as a list of entries, newest first (`Cslib.Algorithms.Lean.CDCL.ATrail.toX`), gives
the state `Cslib.Algorithms.Lean.CDCL.ExecL` (`Cslib.Algorithms.Lean.CDCL.Exec.toL`), on which the
moves are specified and the invariant is stated (`Cslib.Algorithms.Lean.CDCL.Exec.Inv`). Each move
on arrays has a representation lemma (`Cslib.Algorithms.Lean.CDCL.Exec.toL_propagate`,
`Cslib.Algorithms.Lean.CDCL.Exec.toL_afterConflict`, …), through which the invariant carries over.

**Moves.**

* If a clause is false and the trail has no decision, resolving it with the reasons of the trail,
  newest first, derives the empty clause (`Cslib.Algorithms.Lean.CDCL.refute`). The resolvents are
  not built: the variables met are marked, and the certificate is the log closed by one
  empty-clause step hinting the reasons resolved, oldest first, and the conflict clause
  (`Cslib.Algorithms.Lean.CDCL.Refutation.cert`).
* If a clause is false and the trail has a decision, *first-UIP analysis*
  (`Cslib.Algorithms.Lean.CDCL.analyze`) resolves it with the reasons of the newest implied
  literals until exactly one of its literals is false at the current level. As in MiniSat, the
  resolvents are not built: the variables met are marked in an array, the literals below the
  current level are collected, and the marked variables of the current level not yet passed are
  counted (`Cslib.Algorithms.Lean.CDCL.Marks`). The invariant of the analysis guarantees an
  asserting clause: the count is never zero, and at the decision only the decision's variable can
  be counted. It also guarantees the hints of the learned clause, the reasons resolved, oldest
  first, and then the conflict clause: they refute the clause that the marks describe
  (`Cslib.Logic.PL.CNF.RupHints`), which is the resolvent so far. The solver backjumps, as MiniSat
  does, to the second-highest level of the learned clause: below the newest decision and every
  level below it with no variable of the clause (`Cslib.Algorithms.Lean.CDCL.ExecL.jump`, without
  decision levels). It adds the asserting literal with the learned clause as its reason, and learns
  the clause, adding it to the log as one RUP step (Backjump and Learn,
  `Cslib.Algorithms.Lean.CDCL.Exec.afterConflict`).
* UnitPropagate (`Cslib.Algorithms.Lean.CDCL.Exec.propagate`) and Decide
  (`Cslib.Algorithms.Lean.CDCL.Exec.decide`).
* Restart (`Cslib.Algorithms.Lean.CDCL.Exec.restart`), back to the literals implied below every
  decision.
* Forget (`Cslib.Algorithms.Lean.CDCL.Exec.forget`): deleting clauses other than the reasons of
  the trail from the database and the log, input clauses only if a literal of the root of the
  trail, implied without any decision, satisfies them
  (`Cslib.Algorithms.Lean.CDCL.Exec.forget_inv`). The reasons kept are in the database and entail
  the root (`Cslib.Algorithms.Lean.CDCL.Reasons.eval_of_no_decision`), so under total
  assignments the remaining clauses entail the input clauses, and with them the clauses deleted.
  For partial assignments the guarantee concerns the input only: a partial model of the remaining
  clauses satisfies the input clauses through the root. It is not shown to satisfy the deleted
  clauses.

Every move other than Restart and Forget is a Basic DPLL step, or Backjump followed by Learn, of
the abstract system, and so lowers its rank (`Cslib.Algorithms.Lean.CDCL.rank`); Forget keeps it.
Every learned clause enters the certificate as one RUP step whose hints are proved to propagate to
a conflict, so the checker accepts the certificate by construction, with no check at run time
(`Cslib.Logic.PL.CNF.LRATLog.checkLRAT_finish`).

**Scope.** `Exec` does not choose decisions: the solver with watched literals chooses them
(`Cslib.Algorithms.Lean.CDCL.Activity`).

## Main definitions

* `Cslib.Algorithms.Lean.CDCL.Exec`, `Cslib.Algorithms.Lean.CDCL.Exec.Inv`: the state and its
  invariant, with the trail as arrays (`Cslib.Algorithms.Lean.CDCL.ATrail`), read back as
  `Cslib.Algorithms.Lean.CDCL.ExecL`.
* `Cslib.Algorithms.Lean.CDCL.analyze`: first-UIP conflict analysis, with its marks
  `Cslib.Algorithms.Lean.CDCL.Marks`, and the learned clause `Cslib.Algorithms.Lean.CDCL.Learned`.
* `Cslib.Algorithms.Lean.CDCL.ExecL.jump`: the backjump to the second-highest level of the learned
  clause, found on the arrays by `Cslib.Algorithms.Lean.CDCL.ATrail.cutPos`
  (`Cslib.Algorithms.Lean.CDCL.Exec.jump_eq`).
* `Cslib.Algorithms.Lean.CDCL.refute`: the certificate when there is no decision.

## Main results

* `Cslib.Algorithms.Lean.CDCL.Exec.afterConflict_spec`,
  `Cslib.Algorithms.Lean.CDCL.Exec.propagate_spec`, `Cslib.Algorithms.Lean.CDCL.Exec.decide_spec`:
  the moves keep the invariant and lower the rank.
* `Cslib.Algorithms.Lean.CDCL.Exec.restart_inv`, `Cslib.Algorithms.Lean.CDCL.Exec.forget_inv`:
  Restart and Forget keep the invariant.

## References

* [R. Nieuwenhuis, A. Oliveras, C. Tinelli, *Solving SAT and SAT Modulo Theories: From an Abstract
  Davis–Putnam–Logemann–Loveland Procedure to DPLL(T)*][NieuwenhuisOliverasTinelli2006], §2.4–2.5
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.CDCL

open Cslib.Logic.PL Cslib.Logic.PL.CNF
open Cslib.Algorithms.WordRAM.ClauseCode (litCode)

variable {φ : CNF ℕ}

/-- An entry of the solver's trail: a decision, or an implied literal with the number of its
reason clause in the log. -/
inductive XEntry
  /-- A decision. -/
  | decision (l : Literal ℕ)
  /-- An implied literal and the number of its reason. -/
  | implied (l : Literal ℕ) (reason : ℕ)

/-- The entry of the abstract trail. -/
def XEntry.entry : XEntry → Entry
  | .decision l => ⟨l, true⟩
  | .implied l _ => ⟨l, false⟩

@[simp] theorem XEntry.entry_decision (l : Literal ℕ) : (XEntry.decision l).entry = ⟨l, true⟩ :=
  rfl

@[simp] theorem XEntry.entry_implied (l : Literal ℕ) (r : ℕ) :
    (XEntry.implied l r).entry = ⟨l, false⟩ := rfl

/-- The solver's trail, newest first. -/
abbrev XTrail := List XEntry

/-- The abstract trail of the solver's trail. -/
def XTrail.trail (M : XTrail) : Trail := M.map XEntry.entry

@[simp] theorem XTrail.trail_nil : XTrail.trail [] = [] := rfl

@[simp] theorem XTrail.trail_cons (x : XEntry) (M : XTrail) :
    XTrail.trail (x :: M) = x.entry :: XTrail.trail M := rfl

@[simp] theorem XTrail.trail_append (M N : XTrail) :
    XTrail.trail (M ++ N) = XTrail.trail M ++ XTrail.trail N := List.map_append ..

/-- The literal of an entry of the solver's trail. -/
def XEntry.lit : XEntry → Literal ℕ
  | .decision l => l
  | .implied l _ => l

@[simp] theorem XEntry.lit_entry (e : XEntry) : e.entry.lit = e.lit := by cases e <;> rfl

@[simp] theorem XEntry.var_entry (e : XEntry) : e.entry.var = e.lit.1 := by cases e <;> rfl

/-- Whether an entry is a decision, read on the entry. -/
def XEntry.isDecision : XEntry → Bool
  | .decision _ => true
  | .implied _ _ => false

@[simp] theorem XEntry.isDecision_eq (e : XEntry) : e.isDecision = e.entry.decision := by
  cases e <;> rfl

/-- The code of the reason of an entry: `0` for a decision, and `r + 1` for an implied literal
whose reason is numbered `r`. -/
def XEntry.rsnCode : XEntry → ℕ
  | .decision _ => 0
  | .implied _ r => r + 1

/-! ### The trail as arrays -/

/-- The variable of a literal is its key halved. -/
theorem litCode_div_two (l : Literal ℕ) : litCode l / 2 = l.1 :=
  congrArg Prod.fst (litOfKey_litCode l)

/-- **The solver's trail as two arrays**, oldest first: the code of each literal (`litCode`), and
the code of the reason of each entry (`Cslib.Algorithms.Lean.CDCL.XEntry.rsnCode`). Codes in the
scalar range of Lean's runtime are unboxed, so an entry makes no object; `push` and `shrink` write
the arrays in place when they are not shared (and `push` has room), and grow or copy them
otherwise. Backjumping pops the entries undone. The trail read back as a list of entries, newest
first, is `Cslib.Algorithms.Lean.CDCL.ATrail.toX`, on which the invariants are stated. -/
structure ATrail where
  /-- The codes of the literals, oldest first. -/
  lits : Array ℕ
  /-- The codes of the reasons, oldest first. -/
  rsns : Array ℕ
  size_eq : lits.size = rsns.size

namespace ATrail

/-- The number of entries. -/
def size (T : ATrail) : ℕ := T.lits.size

/-- The empty trail. -/
def empty : ATrail := ⟨#[], #[], rfl⟩

/-- The literal at position `i`. -/
@[inline] def lit (T : ATrail) (i : ℕ) : Literal ℕ := litOfKey (T.lits.getD i 0)

/-- The entry at position `i`. -/
def entry (T : ATrail) (i : ℕ) : XEntry :=
  match T.rsns.getD i 0 with
  | 0 => .decision (T.lit i)
  | r + 1 => .implied (T.lit i) r

/-- **The entries at positions `lo` to `lo + k - 1`**, newest first. -/
def seg (T : ATrail) (lo : ℕ) : ℕ → XTrail
  | 0 => []
  | k + 1 => T.entry (lo + k) :: T.seg lo k

/-- **The trail read back** as a list of entries, newest first. -/
def toX (T : ATrail) : XTrail := T.seg 0 T.size

/-- Adding an entry, given by the code of its literal and of its reason. -/
@[inline] def push (T : ATrail) (c r : ℕ) : ATrail :=
  ⟨T.lits.push c, T.rsns.push r, by simp [T.size_eq]⟩

/-- Popping `k` elements, in place if the array is not shared. Unlike `Array.shrink`, whose body is
not exposed, the kernel can unfold it, so that `decide +kernel` runs the solver. -/
def popN {α : Type} : ℕ → Array α → Array α
  | 0, a => a
  | k + 1, a => popN k a.pop

theorem size_popN {α : Type} : ∀ (k : ℕ) (a : Array α), (popN k a).size = a.size - k
  | 0, _ => rfl
  | k + 1, a => by rw [popN, size_popN k, Array.size_pop]; omega

private theorem getD_popN : ∀ (k : ℕ) (a : Array ℕ) {i : ℕ}, i < a.size - k →
    (popN k a).getD i 0 = a.getD i 0
  | 0, _, _, _ => rfl
  | k + 1, a, i, h => by
    rw [popN, getD_popN k a.pop (by rw [Array.size_pop]; omega), Array.getD_eq_getD_getElem?,
      Array.getD_eq_getD_getElem?, Array.getElem?_pop]
    simp only [show i < a.size - 1 by omega, ↓reduceIte]

/-- Keeping the first `q` entries, by popping the others, in place if the arrays are not
shared. -/
@[inline] def shrink (T : ATrail) (q : ℕ) : ATrail :=
  ⟨popN (T.lits.size - q) T.lits, popN (T.lits.size - q) T.rsns, by
    simp only [size_popN, T.size_eq]⟩

/-- **A loop down the positions** `lo + k - 1` to `lo`, newest first, reading the codes of each
entry: the fold of the entries `T.seg lo k` (`ATrail.foldDown_eq`). -/
@[specialize] def foldDown {β : Type} (T : ATrail) (f : β → ℕ → ℕ → β) (lo : ℕ) : ℕ → β → β
  | 0, b => b
  | k + 1, b => T.foldDown f lo k (f b (T.lits.getD (lo + k) 0) (T.rsns.getD (lo + k) 0))

/-- **A loop up the positions** `lo` to `lo + k - 1`, oldest first, reading the codes of each entry:
the right fold of the entries `T.seg lo k` (`ATrail.foldUp_eq`). -/
@[specialize] def foldUp {β : Type} (T : ATrail) (f : β → ℕ → ℕ → β) : ℕ → ℕ → β → β
  | _, 0, b => b
  | lo, k + 1, b => T.foldUp f (lo + 1) k (f b (T.lits.getD lo 0) (T.rsns.getD lo 0))

theorem entry_lit (T : ATrail) (i : ℕ) : (T.entry i).lit = T.lit i := by
  unfold entry; split <;> rfl

theorem litCode_entry_lit (T : ATrail) (i : ℕ) : litCode (T.entry i).lit = T.lits.getD i 0 := by
  rw [entry_lit, lit, litCode_litOfKey]

theorem rsnCode_entry (T : ATrail) (i : ℕ) : (T.entry i).rsnCode = T.rsns.getD i 0 := by
  unfold entry; split <;> simp_all [XEntry.rsnCode]

theorem entry_of_rsn_zero {T : ATrail} {i : ℕ} (h : T.rsns.getD i 0 = 0) :
    T.entry i = .decision (T.lit i) := by
  simp [entry, h]

theorem entry_of_rsn_succ {T : ATrail} {i r : ℕ} (h : T.rsns.getD i 0 = r + 1) :
    T.entry i = .implied (T.lit i) r := by
  simp [entry, h]

theorem isDecision_entry (T : ATrail) (i : ℕ) :
    (T.entry i).isDecision = (T.rsns.getD i 0 == 0) := by
  unfold entry; split <;> simp_all [XEntry.isDecision]

/-- The entry at a position holding the codes of `e` is `e`. -/
theorem entry_eq_of {T : ATrail} {i : ℕ} {e : XEntry} (hl : T.lits.getD i 0 = litCode e.lit)
    (hr : T.rsns.getD i 0 = e.rsnCode) : T.entry i = e := by
  cases e <;> simp only [entry, lit, hl, hr, XEntry.rsnCode, XEntry.lit, litOfKey_litCode]

/-- Two trails with the same codes at a position have the same entry there. -/
theorem entry_congr {T T' : ATrail} {i : ℕ} (hl : T'.lits.getD i 0 = T.lits.getD i 0)
    (hr : T'.rsns.getD i 0 = T.rsns.getD i 0) : T'.entry i = T.entry i := by
  simp only [entry, lit, hl, hr]

@[simp] theorem seg_zero (T : ATrail) (lo : ℕ) : T.seg lo 0 = [] := rfl

theorem seg_succ (T : ATrail) (lo k : ℕ) : T.seg lo (k + 1) = T.entry (lo + k) :: T.seg lo k :=
  rfl

@[simp] theorem length_seg (T : ATrail) (lo k : ℕ) : (T.seg lo k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [seg_succ, ih]

/-- **Cutting a segment**: the newer `b` entries, then the older `a`. -/
theorem seg_add (T : ATrail) (lo a b : ℕ) : T.seg lo (a + b) = T.seg (lo + a) b ++ T.seg lo a := by
  induction b with
  | zero => rfl
  | succ b ih => rw [← Nat.add_assoc, seg_succ, ih, seg_succ, Nat.add_assoc, List.cons_append]

theorem seg_succ_bottom (T : ATrail) (lo k : ℕ) :
    T.seg lo (k + 1) = T.seg (lo + 1) k ++ [T.entry lo] := by
  rw [Nat.add_comm, seg_add]; rfl

theorem mem_seg {T : ATrail} {lo k : ℕ} {x : XEntry} :
    x ∈ T.seg lo k ↔ ∃ i, lo ≤ i ∧ i < lo + k ∧ T.entry i = x := by
  induction k with
  | zero => simp; omega
  | succ k ih =>
    rw [seg_succ, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨i, h₁, h₂, h₃⟩)
      · exact ⟨lo + k, by omega, by omega, rfl⟩
      · exact ⟨i, h₁, by omega, h₃⟩
    · rintro ⟨i, h₁, h₂, rfl⟩
      by_cases hi : i = lo + k
      · exact .inl (by rw [hi])
      · exact .inr ⟨i, h₁, by omega, rfl⟩

/-- Segments of two trails agreeing on their positions are equal. -/
theorem seg_congr {T T' : ATrail} {lo k : ℕ}
    (h : ∀ i, lo ≤ i → i < lo + k → T'.entry i = T.entry i) : T'.seg lo k = T.seg lo k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [seg_succ, seg_succ, h _ (by omega) (by omega), ih fun i h₁ h₂ => h i h₁ (by omega)]

theorem foldDown_eq {β : Type} (T : ATrail) (f : β → ℕ → ℕ → β) (lo : ℕ) :
    ∀ (k : ℕ) (b : β),
      T.foldDown f lo k b = (T.seg lo k).foldl (fun b e => f b (litCode e.lit) e.rsnCode) b
  | 0, _ => rfl
  | k + 1, b => by
    rw [foldDown, foldDown_eq T f lo k, seg_succ, List.foldl_cons, litCode_entry_lit,
      rsnCode_entry]

theorem foldUp_eq {β : Type} (T : ATrail) (f : β → ℕ → ℕ → β) :
    ∀ (lo k : ℕ) (b : β),
      T.foldUp f lo k b = (T.seg lo k).foldr (fun e b => f b (litCode e.lit) e.rsnCode) b
  | _, 0, _ => rfl
  | lo, k + 1, b => by
    rw [foldUp, foldUp_eq T f (lo + 1) k, seg_succ_bottom, List.foldr_append, List.foldr_cons,
      List.foldr_nil, litCode_entry_lit, rsnCode_entry]

@[simp] theorem size_push (T : ATrail) (c r : ℕ) : (T.push c r).size = T.size + 1 := by
  simp [push, size]

theorem entry_push_lt (T : ATrail) {c r i : ℕ} (h : i < T.size) :
    (T.push c r).entry i = T.entry i := by
  have hl : i < T.lits.size := h
  have h' : i < T.rsns.size := T.size_eq ▸ h
  refine entry_congr ?_ ?_ <;>
    simp [push, Array.getD_eq_getD_getElem?, Array.getElem?_push, hl, h', Nat.ne_of_lt]

theorem entry_push_size (T : ATrail) (e : XEntry) :
    (T.push (litCode e.lit) e.rsnCode).entry T.size = e := by
  have h₁ : (T.push (litCode e.lit) e.rsnCode).lits.getD T.size 0 = litCode e.lit := by
    simp [push, size]
  have h₂ : (T.push (litCode e.lit) e.rsnCode).rsns.getD T.size 0 = e.rsnCode := by
    simp [push, size, T.size_eq]
  exact entry_eq_of h₁ h₂

/-- **Pushing an entry** puts it at the head of the trail read back. -/
theorem toX_push (T : ATrail) (e : XEntry) :
    (T.push (litCode e.lit) e.rsnCode).toX = e :: T.toX := by
  rw [toX, size_push, seg_succ, Nat.zero_add, entry_push_size, toX]
  exact congrArg _ (seg_congr fun i _ h => T.entry_push_lt (by omega))

@[simp] theorem size_shrink (T : ATrail) (q : ℕ) : (T.shrink q).size = min q T.size := by
  simp only [shrink, size, size_popN]; omega

private theorem entry_shrink (T : ATrail) {q i : ℕ} (h : i < q) :
    (T.shrink q).entry i = T.entry i := by
  by_cases hi : i < T.size
  · have h₁ : i < T.lits.size - (T.lits.size - q) := by simp only [size] at hi; omega
    have h₂ : i < T.rsns.size - (T.lits.size - q) := by rw [← T.size_eq]; exact h₁
    exact entry_congr (getD_popN _ _ h₁) (getD_popN _ _ h₂)
  · have hn : ∀ (a : Array ℕ), T.lits.size ≤ a.size → a.size ≤ i →
        (popN (T.lits.size - q) a).getD i 0 = a.getD i 0 := fun a h₁ h₂ => by
      rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_none (by rw [size_popN]; omega), Array.getElem?_eq_none (by omega)]
    simp only [size] at hi
    exact entry_congr (hn _ le_rfl (by omega))
      (hn _ (T.size_eq ▸ le_rfl) (by rw [← T.size_eq]; omega))

/-- **Popping down to `q` entries** keeps the oldest `q`. -/
theorem toX_shrink (T : ATrail) {q : ℕ} (h : q ≤ T.size) : (T.shrink q).toX = T.seg 0 q := by
  rw [toX, size_shrink, Nat.min_eq_left h]
  exact seg_congr fun i _ hi => T.entry_shrink (by omega)

@[simp] theorem length_toX (T : ATrail) : T.toX.length = T.size := length_seg ..

@[simp] theorem toX_empty : ATrail.empty.toX = [] := rfl

theorem mem_toX {T : ATrail} {x : XEntry} : x ∈ T.toX ↔ ∃ i < T.size, T.entry i = x := by
  rw [toX, mem_seg]; simp

end ATrail

/-- Every implied literal of the trail has a reason clause in the log, containing it, whose other
literals are false further down the trail; decisions have no reason. -/
inductive Reasons (log : LRATLog φ) : XTrail → Prop
  | nil : Reasons log []
  | decision {M : XTrail} (l : Literal ℕ) : Reasons log M → Reasons log (.decision l :: M)
  | implied {M : XTrail} (l : Literal ℕ) (r : ℕ) {R : Clause ℕ} : Reasons log M →
      log.clause? r = some R → l ∈ R →
      (∀ l' ∈ R, l' ≠ l → l'.negate ∈ Trail.lits (XTrail.trail M)) →
      Reasons log (.implied l r :: M)

theorem Reasons.mono {log log' : LRATLog φ} (hext : log.Extends log') {M : XTrail}
    (h : Reasons log M) : Reasons log' M := by
  induction h with
  | nil => exact .nil
  | decision l _ ih => exact .decision l ih
  | implied l r _ hr hl hfalse ih => exact .implied l r ih (hext _ _ hr) hl hfalse

theorem Reasons.tail {log : LRATLog φ} {x : XEntry} {M : XTrail} (h : Reasons log (x :: M)) :
    Reasons log M := by
  cases h <;> assumption

/-- The reason of an implied literal at the head of a trail. -/
theorem Reasons.reason {log : LRATLog φ} {l : Literal ℕ} {r : ℕ} {M : XTrail} {R : Clause ℕ}
    (h : Reasons log (.implied l r :: M)) (hR : log.clause? r = some R) :
    l ∈ R ∧ ∀ l' ∈ R, l' ≠ l → l'.negate ∈ Trail.lits (XTrail.trail M) := by
  cases h with
  | implied _ _ _ hr hl hfalse =>
    rw [hR] at hr
    cases hr
    exact ⟨hl, hfalse⟩

/-- An implied literal at the head of a trail has a reason. -/
theorem Reasons.isSome {log : LRATLog φ} {l : Literal ℕ} {r : ℕ} {M : XTrail}
    (h : Reasons log (.implied l r :: M)) : (log.clause? r).isSome := by
  cases h with
  | implied _ _ _ hr => simp [hr]

theorem Reasons.append_right {log : LRATLog φ} {N M : XTrail} (h : Reasons log (N ++ M)) :
    Reasons log M := by
  induction N with
  | nil => simpa using h
  | cons x N ih => exact ih h.tail

/-- The number of the reason of an entry, if it is implied. -/
def XEntry.reason? : XEntry → Option ℕ
  | .decision _ => none
  | .implied _ r => some r

/-- The numbers of the reasons of a trail, MiniSat's *locked* clauses. -/
def XTrail.reasonIds (M : XTrail) : List ℕ := M.filterMap XEntry.reason?

@[simp] theorem XTrail.reasonIds_nil : XTrail.reasonIds [] = [] := rfl

@[simp] theorem XTrail.reasonIds_decision (l : Literal ℕ) (M : XTrail) :
    XTrail.reasonIds (.decision l :: M) = XTrail.reasonIds M := rfl

@[simp] theorem XTrail.reasonIds_implied (l : Literal ℕ) (r : ℕ) (M : XTrail) :
    XTrail.reasonIds (.implied l r :: M) = r :: XTrail.reasonIds M := rfl

/-- The reasons of a trail are numbers of the log, so below its next number. -/
theorem Reasons.lt_next {log : LRATLog φ} {M : XTrail} (h : Reasons log M) :
    ∀ r ∈ XTrail.reasonIds M, r < log.next := by
  induction h with
  | nil => simp
  | decision l _ ih => simpa using ih
  | implied l r _ hr _ _ ih =>
    intro r' h'
    rcases List.mem_cons.1 (by simpa using h') with rfl | h'
    · exact LRATLog.lt_next_of_clause? hr
    · exact ih r' h'

/-- Deleting clauses other than the reasons keeps the reasons. -/
theorem Reasons.delete {log : LRATLog φ} {ids : List ℕ} {M : XTrail} (h : Reasons log M)
    (hids : ∀ r ∈ XTrail.reasonIds M, r ∉ ids) : Reasons (log.delete ids) M := by
  induction h with
  | nil => exact .nil
  | decision l _ ih => exact .decision l (ih (by simpa using hids))
  | implied l r _ hr hl hfalse ih =>
    have hr' : r ∉ ids := hids r (by simp)
    exact .implied l r (ih fun r' h' => hids r' (by simp [h']))
      ((LRATLog.clause?_delete hr').trans hr) hl hfalse

/-- The negation is injective. -/
theorem negate_inj {l l' : Literal ℕ} (h : l.negate = l'.negate) : l = l' := by
  obtain ⟨v, b⟩ := l
  obtain ⟨v', b'⟩ := l'
  cases b <;> cases b' <;> simp_all [Std.Sat.Literal.negate]

private theorem negate_eq_iff {y l : Literal ℕ} : y.negate = l ↔ y = l.negate :=
  ⟨fun h => by subst h; simp, fun h => by subst h; simp⟩

theorem lits_append (M N : Trail) : Trail.lits (M ++ N) = Trail.lits M ++ Trail.lits N :=
  List.map_append ..

theorem vars_append (M N : Trail) : Trail.vars (M ++ N) = Trail.vars M ++ Trail.vars N :=
  List.map_append ..

theorem mem_lits_cons {e : Entry} {M : Trail} {y : Literal ℕ} :
    y ∈ Trail.lits (e :: M) ↔ y = e.lit ∨ y ∈ Trail.lits M := by
  simp [Trail.lits]

/-- On a trail assigning each variable once, a literal is determined by its variable. -/
theorem eq_of_mem_lits {M : Trail} (hM : (Trail.vars M).Nodup) {a b : Literal ℕ}
    (ha : a ∈ Trail.lits M) (hb : b ∈ Trail.lits M) (h : a.1 = b.1) : a = b := by
  induction M with
  | nil => simp [Trail.lits] at ha
  | cons e M ih =>
    simp only [Trail.vars, List.map_cons, List.nodup_cons] at hM
    rw [mem_lits_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd (by rw [show e.var = b.1 from h]; exact Trail.mem_vars_of_mem_lits hb) hM.1
    · exact absurd (by rw [show e.var = a.1 from h.symm]; exact Trail.mem_vars_of_mem_lits ha) hM.1
    · exact ih hM.2 ha hb

/-! ### Conflict analysis with marks -/

/-- **The state of conflict analysis**, as MiniSat keeps it: the array of the variables `seen`, the
literals `out` of the analysed clause false below the current level, the number `path` of seen
variables of the current level not yet passed, and the variables seen, newest first. -/
structure Marks where
  /-- The variables seen, as an array. -/
  seen : Assign
  /-- The literals of the analysed clause false below the current level. -/
  out : Clause ℕ
  /-- The seen variables of the current level not yet passed. -/
  path : ℕ
  /-- The variables seen, newest first. -/
  vars : List ℕ

/-- Nothing seen, in an array of `n` slots, so that seeing a variable below `n` does not grow it. -/
def Marks.start (n : ℕ) : Marks := ⟨⟨Array.replicate n 0⟩, [], 0, []⟩

/-- **The analysed clause** of the state `m`, with the entries `Cur` of the current level still to
pass: the literals of `out`, and the negations of the literals of `Cur` whose variables are seen.
It is never built; the hints of the learned clause refute it (`Cslib.Logic.PL.CNF.RupHints`). -/
def Marks.clause (m : Marks) (Cur : Trail) (y : Literal ℕ) : Prop :=
  y ∈ m.out ∨ (m.seen.assigned y.1 = true ∧ y.negate ∈ Trail.lits Cur)

/-- The loop of `Marks.absorb`, with the four parts of the state as arguments, so that compiled
code builds no state per literal. -/
def Marks.absorbGo (cur : Assign) (seen : Assign) (out : Clause ℕ) (path : ℕ) (vars : List ℕ) :
    Clause ℕ → Marks
  | [] => ⟨seen, out, path, vars⟩
  | y :: R =>
    if seen.assigned y.1 then Marks.absorbGo cur seen out path vars R
    else if cur.isFalse y then
      Marks.absorbGo cur (seen.set y.1 (some true)) out (path + 1) (y.1 :: vars) R
    else Marks.absorbGo cur (seen.set y.1 (some true)) (y :: out) path (y.1 :: vars) R

/-- **Adding the literals of a clause** to the analysis: each literal on a variable not yet seen is
seen; it counts on the path if it is false on the current level, whose literals `cur` holds, and
goes to `out` otherwise. -/
def Marks.absorb (cur : Assign) (m : Marks) (R : Clause ℕ) : Marks :=
  Marks.absorbGo cur m.seen m.out m.path m.vars R

theorem Marks.absorb_nil (cur : Assign) (m : Marks) : m.absorb cur [] = m := rfl

theorem Marks.absorb_cons (cur : Assign) (m : Marks) (y : Literal ℕ) (R : Clause ℕ) :
    m.absorb cur (y :: R) =
      if m.seen.assigned y.1 then m.absorb cur R
      else if cur.isFalse y then
        Marks.absorb cur ⟨m.seen.set y.1 (some true), m.out, m.path + 1, y.1 :: m.vars⟩ R
      else Marks.absorb cur ⟨m.seen.set y.1 (some true), y :: m.out, m.path, y.1 :: m.vars⟩ R :=
  rfl

/-- The invariant of the analysis, with the entries `Cur` of the current level still to pass, the
trail `M₀` below it, and the variables `V` of the formula: the literals of `out` are false below the
current level, and are those of the seen variables there; `path` counts the seen variables of
`Cur`; and `vars` lists the seen variables, of `V`. -/
structure Marks.Inv (m : Marks) (Cur M₀ : Trail) (V : List ℕ) : Prop where
  out_below : ∀ y ∈ m.out, y.negate ∈ Trail.lits M₀
  out_seen : ∀ y ∈ m.out, m.seen.assigned y.1 = true
  below_out : ∀ y, y.negate ∈ Trail.lits M₀ → m.seen.assigned y.1 = true → y ∈ m.out
  path_eq : m.path = Cur.countP fun e => m.seen.assigned e.lit.1
  seen_iff : ∀ v, m.seen.assigned v = true ↔ v ∈ m.vars
  vars_mem : ∀ v ∈ m.vars, v ∈ V
  vars_nodup : m.vars.Nodup
  out_nodup : m.out.Nodup

private theorem assigned_replicate (n v : ℕ) :
    (⟨Array.replicate n 0⟩ : Assign).assigned v = false := by
  simp only [Assign.assigned, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> simp

theorem Marks.inv_start (n : ℕ) (Cur M₀ : Trail) (V : List ℕ) : (Marks.start n).Inv Cur M₀ V where
  out_below := by simp [Marks.start]
  out_seen := by simp [Marks.start]
  below_out _ _ h := by simp [Marks.start, assigned_replicate] at h
  path_eq := by
    simp [Marks.start, assigned_replicate]
  seen_iff _ := by simp [Marks.start, assigned_replicate]
  vars_mem := by simp [Marks.start]
  vars_nodup := List.nodup_nil
  out_nodup := List.nodup_nil

/-- Seeing the variable `v` adds one to the count of the seen variables of a trail assigning each
variable once, if it is one of its variables. -/
private theorem countP_set_seen {s : Assign} {v : ℕ} (hv : s.assigned v = false) :
    ∀ {Cur : Trail}, (Trail.vars Cur).Nodup →
      (Cur.countP fun e => (s.set v (some true)).assigned e.lit.1) =
        (Cur.countP fun e => s.assigned e.lit.1) + if v ∈ Trail.vars Cur then 1 else 0
  | [], _ => by simp [Trail.vars]
  | e :: Cur, hnd => by
    simp only [Trail.vars, List.map_cons, List.nodup_cons] at hnd
    rw [List.countP_cons, List.countP_cons, countP_set_seen hv hnd.2, Assign.assigned_set]
    by_cases he : e.lit.1 = v
    · subst he
      have h₁ : e.lit.1 ∈ Trail.vars (e :: Cur) := List.mem_cons_self
      have h₂ : e.lit.1 ∉ Trail.vars Cur := hnd.1
      simp only [h₁, h₂, hv, ↓reduceIte, Option.isSome_some, Bool.false_eq_true]
    · have : (v ∈ Trail.vars (e :: Cur)) ↔ v ∈ Trail.vars Cur := by
        simp [Trail.vars, Ne.symm he]
      simp only [he, ↓reduceIte, this]
      omega

theorem Marks.Inv.clause_of_seen {m : Marks} {Cur M₀ : Trail} {V : List ℕ} (hm : m.Inv Cur M₀ V)
    {y : Literal ℕ} (hs : m.seen.assigned y.1 = true)
    (hy : y.negate ∈ Trail.lits Cur ∨ y.negate ∈ Trail.lits M₀) : m.clause Cur y :=
  hy.elim (fun h => .inr ⟨hs, h⟩) fun h => .inl (hm.below_out y h hs)

/-- **Adding a clause** keeps the invariant, if the literals of the clause on variables not yet
seen are false on the current level or below; every variable of the clause is seen afterwards,
and nothing seen or in `out` is lost. -/
theorem Marks.absorb_spec {cur : Assign} {Cur M₀ : Trail} {V : List ℕ} (hcur : cur.Agrees Cur)
    (hnd : (Trail.vars (Cur ++ M₀)).Nodup) :
    ∀ (m : Marks) (R : Clause ℕ), m.Inv Cur M₀ V → (∀ y ∈ R, y.1 ∈ V) →
      (∀ y ∈ R, m.seen.assigned y.1 = false →
        y.negate ∈ Trail.lits Cur ∨ y.negate ∈ Trail.lits M₀) →
      (m.absorb cur R).Inv Cur M₀ V ∧ (∀ y ∈ R, (m.absorb cur R).seen.assigned y.1 = true) ∧
      (∀ v, m.seen.assigned v = true → (m.absorb cur R).seen.assigned v = true) ∧
      (∀ y ∈ m.out, y ∈ (m.absorb cur R).out)
  | m, [], hm, _, _ => by rw [Marks.absorb_nil]; exact ⟨hm, by simp, fun _ h => h, fun _ h => h⟩
  | m, y :: R, hm, hV, hR => by
    rw [vars_append] at hnd
    have hdisj := List.disjoint_of_nodup_append hnd
    have hndM : (Trail.vars M₀).Nodup := hnd.of_append_right
    have hndC : (Trail.vars Cur).Nodup := hnd.of_append_left
    rw [← vars_append] at hnd
    have hV' : ∀ z ∈ R, z.1 ∈ V := fun z hz => hV z (List.mem_cons_of_mem _ hz)
    rw [Marks.absorb_cons]
    split
    · rename_i hs
      obtain ⟨h₁, h₂, h₃, h₄⟩ := Marks.absorb_spec hcur hnd m R hm hV'
        fun z hz => hR z (List.mem_cons_of_mem _ hz)
      refine ⟨h₁, fun z hz => ?_, h₃, h₄⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · exact h₃ _ hs
      · exact h₂ z hz
    · rename_i hs
      have hs' : m.seen.assigned y.1 = false := by simpa using hs
      have hy := hR y List.mem_cons_self hs'
      -- seeing `y.1` keeps what was seen
      have hmono : ∀ v, m.seen.assigned v = true → (m.seen.set y.1 (some true)).assigned v = true :=
        fun v hv => by rw [Assign.assigned_set]; split <;> simp [hv]
      have hR' : ∀ z ∈ R, (m.seen.set y.1 (some true)).assigned z.1 = false →
          z.negate ∈ Trail.lits Cur ∨ z.negate ∈ Trail.lits M₀ := fun z hz hz' => by
        refine hR z (List.mem_cons_of_mem _ hz) ?_
        cases h : m.seen.assigned z.1
        · rfl
        · rw [hmono _ h] at hz'; exact hz'
      have hseen_iff : ∀ v, (m.seen.set y.1 (some true)).assigned v = true ↔ v ∈ y.1 :: m.vars :=
        fun v => by
          rw [Assign.assigned_set, List.mem_cons, ← hm.seen_iff]
          by_cases hv : v = y.1 <;> simp [hv]
      have hvars : ∀ v ∈ y.1 :: m.vars, v ∈ V := fun v hv => by
        rcases List.mem_cons.1 hv with rfl | hv
        · exact hV y List.mem_cons_self
        · exact hm.vars_mem v hv
      have hvnd : (y.1 :: m.vars).Nodup :=
        List.nodup_cons.2 ⟨fun h => by rw [← hm.seen_iff, hs'] at h; exact absurd h (by simp),
          hm.vars_nodup⟩
      have hfin : ∀ (m' : Marks), m'.seen = m.seen.set y.1 (some true) →
          (∀ z ∈ m.out, z ∈ m'.out) → m'.Inv Cur M₀ V →
          (m'.absorb cur R).Inv Cur M₀ V ∧
            (∀ z ∈ y :: R, (m'.absorb cur R).seen.assigned z.1 = true) ∧
            (∀ v, m.seen.assigned v = true → (m'.absorb cur R).seen.assigned v = true) ∧
            (∀ z ∈ m.out, z ∈ (m'.absorb cur R).out) := fun m' hseen hout hm' => by
        obtain ⟨h₁, h₂, h₃, h₄⟩ := Marks.absorb_spec hcur hnd m' R hm' hV' (hseen ▸ hR')
        refine ⟨h₁, fun z hz => ?_, fun v hv => h₃ v (hseen ▸ hmono v hv),
          fun z hz => h₄ z (hout z hz)⟩
        rcases List.mem_cons.1 hz with rfl | hz
        · exact h₃ _ (by rw [hseen, Assign.assigned_set]; simp)
        · exact h₂ z hz
      split
      · rename_i hc
        have hyc : y.negate ∈ Trail.lits Cur := (hcur.isFalse_iff _).1 hc
        have hyv : y.1 ∈ Trail.vars Cur := by
          simpa [Std.Sat.Literal.negate] using Trail.mem_vars_of_mem_lits hyc
        refine hfin _ rfl (fun z hz => hz) ⟨hm.out_below, fun z hz => hmono _ (hm.out_seen z hz),
          fun z hz hzs => ?_, ?_, hseen_iff, hvars, hvnd, hm.out_nodup⟩
        · rw [Assign.assigned_set] at hzs
          split at hzs
          · rename_i hzy
            have : z.1 ∈ Trail.vars M₀ := by
              simpa [Std.Sat.Literal.negate] using Trail.mem_vars_of_mem_lits hz
            exact absurd (hzy ▸ this) (hdisj hyv)
          · exact hm.below_out z hz hzs
        · simp only
          rw [countP_set_seen hs' hndC, ← hm.path_eq, ite_eq_left hyv]
      · rename_i hc
        have hyM : y.negate ∈ Trail.lits M₀ :=
          hy.resolve_left fun h => hc ((hcur.isFalse_iff _).2 h)
        have hyv : y.1 ∉ Trail.vars Cur := fun h => hdisj h (by
          simpa [Std.Sat.Literal.negate] using Trail.mem_vars_of_mem_lits hyM)
        refine hfin _ rfl (fun z hz => List.mem_cons_of_mem _ hz) ⟨fun z hz => ?_,
          fun z hz => ?_, fun z hz hzs => ?_, ?_, hseen_iff, hvars, hvnd,
          List.nodup_cons.2 ⟨fun h => by rw [hm.out_seen y h] at hs'; exact absurd hs' (by simp),
            hm.out_nodup⟩⟩
        · rcases List.mem_cons.1 hz with rfl | hz
          · exact hyM
          · exact hm.out_below z hz
        · rcases List.mem_cons.1 hz with rfl | hz
          · simp [Assign.assigned_set]
          · exact hmono _ (hm.out_seen z hz)
        · rw [Assign.assigned_set] at hzs
          split at hzs
          · rename_i hzy
            have : z.negate = y.negate := eq_of_mem_lits hndM hz hyM (by
              simpa [Std.Sat.Literal.negate] using hzy)
            rw [negate_inj this]
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hm.below_out z hz hzs)
        · simp only
          rw [countP_set_seen hs' hndC, ← hm.path_eq, ite_eq_right hyv]
          rfl

/-- Passing an entry of the current level: if its variable is not seen, nothing changes. -/
theorem Marks.Inv.pass {m : Marks} {e : Entry} {Cur M₀ : Trail} {V : List ℕ}
    (hm : m.Inv (e :: Cur) M₀ V) (he : m.seen.assigned e.lit.1 = false) : m.Inv Cur M₀ V :=
  { hm with
    path_eq := by rw [hm.path_eq, List.countP_cons, he]; rfl }

/-- Passing an entry of the current level whose variable is seen takes one off the path. -/
theorem Marks.Inv.resolve {m : Marks} {e : Entry} {Cur M₀ : Trail} {V : List ℕ}
    (hm : m.Inv (e :: Cur) M₀ V) (he : m.seen.assigned e.lit.1 = true) :
    (⟨m.seen, m.out, m.path - 1, m.vars⟩ : Marks).Inv Cur M₀ V :=
  { hm with
    path_eq := by
      have := hm.path_eq
      rw [List.countP_cons, he] at this
      simp only [↓reduceIte] at this
      simp only
      omega }

/-- A learned clause: a clause all of whose literals but `lit` are false in the trail `M₀`, where
`lit` is undefined, and whose negation is among the literals `A` above `M₀`, with hints along which
unit propagation in the log refutes it. Adding it to the log
(`Cslib.Algorithms.Lean.CDCL.Learned.log`) is one RUP step. -/
structure Learned (log : LRATLog φ) (A M₀ : Trail) where
  /-- The learned clause. -/
  clause : Clause ℕ
  /-- The asserting literal. -/
  lit : Literal ℕ
  /-- The hints of the RUP step: the reasons resolved, oldest first, and the conflict clause. -/
  hints : List ℕ
  /-- The variables met by the analysis: those of the conflict clause and of the reasons resolved.
  Branching heuristics bump them. -/
  seen : List ℕ
  /-- The numbers of the clauses met by the analysis: the conflict clause and the reasons resolved.
  Clause activities bump them. -/
  used : List ℕ
  seen_mem : ∀ v ∈ seen, v ∈ φ.vars
  rup : propagateHints log.db (clause.map Std.Sat.Literal.negate) hints = true
  vars_mem : ∀ l ∈ clause, l.1 ∈ φ.vars
  mem : lit ∈ clause
  false_below : ∀ y ∈ clause, y ≠ lit → y.negate ∈ Trail.lits M₀
  undef : lit.1 ∉ Trail.vars M₀
  above : lit.negate ∈ Trail.lits A
  /-- The assignment array the analysis was reading when it stopped, returned so that the solver
  can clear it and use it again: it has values only for variables of `A`. -/
  marks : Assign
  marks_none : ∀ v, v ∉ Trail.vars A → marks.value v = none
  /-- The learned clause has no repeated literal, so that the solver need not remove repetitions. -/
  nodup : clause.Nodup
  /-- The asserting literal comes first, the literal the watch store watches first. -/
  head : clause.head? = some lit
  /-- The variables met are listed once each, so that bumping them need not remove repetitions. -/
  seen_nodup : seen.Nodup

namespace Learned

variable {log₀ : LRATLog φ} {A M₀ : Trail}

/-- The log with the learned clause added, as one RUP step. -/
def log (L : Learned log₀ A M₀) : LRATLog φ := log₀.addRup L.clause L.hints L.rup L.vars_mem

/-- The number of the learned clause in `L.log`. -/
def id (_L : Learned log₀ A M₀) : ℕ := log₀.next

theorem clause?_eq (L : Learned log₀ A M₀) : L.log.clause? L.id = some L.clause :=
  LRATLog.clause?_addRup

theorem ext (L : Learned log₀ A M₀) : log₀.Extends L.log := LRATLog.extends_addRup

end Learned

/-- **The learned clause at the first unique implication point** `l`, the entry of the current
level `⟨l, b⟩ :: Cur` whose variable is the only one seen there: the negation of `l` and the
literals `out`. -/
def Marks.learned (log : LRATLog φ) {A M₀ Cur : Trail} (m : Marks) (l : Literal ℕ) (b : Bool)
    (hm : m.Inv (⟨l, b⟩ :: Cur) M₀ φ.vars) (hl : m.seen.assigned l.1 = true) (hp : m.path = 1)
    (hints : List ℕ) (hh : RupHints log.db (m.clause (⟨l, b⟩ :: Cur)) hints)
    (hlA : l ∈ Trail.lits A) (hlM : l.1 ∉ Trail.vars M₀) (cur : Assign)
    (hcur : ∀ v, v ∉ Trail.vars A → cur.value v = none) : Learned log A M₀ where
  clause := l.negate :: m.out
  lit := l.negate
  hints := hints
  seen := m.vars
  used := hints
  seen_mem := hm.vars_mem
  rup := hh.propagateHints_eq fun y hy => by
    rcases hy with hy | ⟨hs, hy⟩
    · exact List.mem_cons_of_mem _ hy
    rcases mem_lits_cons.1 hy with hy | hy
    · exact negate_eq_iff.1 hy ▸ List.mem_cons_self
    -- `l` is the only seen variable of the level
    have h0 : (Cur.countP fun e => m.seen.assigned e.lit.1) = 0 := by
      have := hm.path_eq
      rw [List.countP_cons, hl] at this
      simp only [↓reduceIte] at this
      omega
    obtain ⟨e, he, hey⟩ := List.mem_map.1 hy
    have := List.countP_eq_zero.1 h0 e he
    rw [hey] at this
    exact absurd hs (by simpa [Std.Sat.Literal.negate] using this)
  vars_mem y hy := by
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hm.vars_mem _ ((hm.seen_iff _).1 hl)
    · exact hm.vars_mem _ ((hm.seen_iff _).1 (hm.out_seen y hy))
  mem := List.mem_cons_self
  false_below y hy hne := hm.out_below y ((List.mem_cons.1 hy).resolve_left hne)
  undef := by simpa [Std.Sat.Literal.negate] using hlM
  above := by simpa using hlA
  marks := cur
  marks_none := hcur
  nodup := List.nodup_cons.2 ⟨fun h => hlM (by
      simpa [Std.Sat.Literal.negate] using Trail.mem_vars_of_mem_lits (hm.out_below _ h)),
    hm.out_nodup⟩
  head := rfl
  seen_nodup := hm.vars_nodup

/-- The trail split at a decision, the current level first. -/
theorem trail_level (N M₀ : XTrail) (d : Literal ℕ) :
    XTrail.trail (N ++ XEntry.decision d :: M₀) =
      (XTrail.trail N ++ [⟨d, true⟩]) ++ XTrail.trail M₀ := by
  simp

/-- An assignment agreeing with the current level has values only on the literals above. -/
private theorem value_eq_none_of_agrees {cur : Assign} {Cur A : Trail} (h : cur.Agrees Cur)
    (hA : Trail.lits Cur ⊆ Trail.lits A) : ∀ v, v ∉ Trail.vars A → cur.value v = none :=
  fun v hv => by
    cases hc : cur.value v with
    | none => rfl
    | some b => exact absurd (Trail.mem_vars_of_mem_lits (hA ((h v b).1 hc))) hv

/-- **The current level read back**: the entries above position `p`, then the decision at `p`. -/
def ATrail.level (T : ATrail) (p : ℕ) : Trail :=
  XTrail.trail (T.seg (p + 1) (T.size - (p + 1))) ++ [⟨T.lit p, true⟩]

/-- **First-UIP conflict analysis**, as MiniSat's, on the trail `T` with its newest decision at
position `p`: with the `k` implied literals over it still to pass, at positions `p + 1` to `p + k`,
and the trail below it, the state `m` marks the analysed clause, which the hints refute. At an entry
whose variable is seen, the analysis stops if it is the only seen variable left on the level, its
first unique implication point, and otherwise adds its reason, whose number it prepends to the
hints; entries whose variables are not seen are passed. The entries are read from the arrays of
the trail, position by position, so no list is built; the entries read back (`ATrail.seg`) appear
only in the invariant. The literals of the current level are read from the assignment `cur`, which
agrees with them; passing an implied literal unassigns its variable. -/
def analyzeGo (log : LRATLog φ) (T : ATrail) (p : ℕ) :
    (k : ℕ) → Trail.lits (XTrail.trail (T.seg (p + 1) k) ++ [⟨T.lit p, true⟩]) ⊆
      Trail.lits (T.level p) →
    (cur : Assign) → cur.Agrees (XTrail.trail (T.seg (p + 1) k) ++ [⟨T.lit p, true⟩]) →
    (m : Marks) →
    m.Inv (XTrail.trail (T.seg (p + 1) k) ++ [⟨T.lit p, true⟩]) (XTrail.trail (T.seg 0 p)) φ.vars →
    1 ≤ m.path → (hints : List ℕ) →
    RupHints log.db (m.clause (XTrail.trail (T.seg (p + 1) k) ++ [⟨T.lit p, true⟩])) hints →
    Reasons log (T.seg (p + 1) k ++ XEntry.decision (T.lit p) :: T.seg 0 p) →
    (∀ x ∈ T.seg (p + 1) k, x.entry.decision = false) →
    (Trail.vars (XTrail.trail (T.seg (p + 1) k ++ XEntry.decision (T.lit p) :: T.seg 0 p))).Nodup →
    Learned log (T.level p) (XTrail.trail (T.seg 0 p))
  | 0, hA, cur, hcurA, m, hm, hpath, hints, hh, _, _, hnd =>
    -- at the decision, the path has only its variable
    have hd : m.seen.assigned (T.lit p).1 = true := by
      have := hm.path_eq
      by_contra h
      simp only [ATrail.seg_zero, XTrail.trail_nil, List.nil_append, List.countP_singleton]
        at this
      simp only [Bool.not_eq_true] at h
      rw [h] at this
      simp at this
      omega
    have hp : m.path = 1 := by
      have := hm.path_eq
      simp only [ATrail.seg_zero, XTrail.trail_nil, List.nil_append, List.countP_singleton, hd]
        at this
      simpa using this
    m.learned log (T.lit p) true hm hd hp hints hh (hA (by simp [Trail.lits]))
      (fun h => by
        simp only [ATrail.seg_zero, List.nil_append, XTrail.trail_cons, XEntry.entry_decision,
          Trail.vars, List.map_cons, List.nodup_cons] at hnd
        exact hnd.1 h)
      cur (by exact value_eq_none_of_agrees hcurA hA)
  | k + 1, hA, cur, hcurA, m, hm, hpath, hints, hh, hreasons, hdec, hnd =>
    match hr : T.rsns.getD (p + 1 + k) 0 with
    | 0 =>
      absurd (hdec (T.entry (p + 1 + k)) (by rw [ATrail.seg_succ]; exact List.mem_cons_self))
        (by rw [ATrail.entry_of_rsn_zero hr]; simp)
    | r + 1 =>
    have hN : T.seg (p + 1) (k + 1) = .implied (T.lit (p + 1 + k)) r :: T.seg (p + 1) k := by
      rw [ATrail.seg_succ, ATrail.entry_of_rsn_succ hr]
    have hA : Trail.lits (XTrail.trail (.implied (T.lit (p + 1 + k)) r :: T.seg (p + 1) k) ++
        [⟨T.lit p, true⟩]) ⊆ Trail.lits (T.level p) := by rw [← hN]; exact hA
    have hcurA : cur.Agrees (XTrail.trail (.implied (T.lit (p + 1 + k)) r :: T.seg (p + 1) k) ++
        [⟨T.lit p, true⟩]) := by rw [← hN]; exact hcurA
    have hm : m.Inv (XTrail.trail (.implied (T.lit (p + 1 + k)) r :: T.seg (p + 1) k) ++
        [⟨T.lit p, true⟩]) (XTrail.trail (T.seg 0 p)) φ.vars := by rw [← hN]; exact hm
    have hh : RupHints log.db (m.clause (XTrail.trail (.implied (T.lit (p + 1 + k)) r ::
        T.seg (p + 1) k) ++ [⟨T.lit p, true⟩])) hints := by rw [← hN]; exact hh
    have hreasons : Reasons log (.implied (T.lit (p + 1 + k)) r :: T.seg (p + 1) k ++
        XEntry.decision (T.lit p) :: T.seg 0 p) := by rw [← hN]; exact hreasons
    have hnd : (Trail.vars (XTrail.trail (.implied (T.lit (p + 1 + k)) r :: T.seg (p + 1) k ++
        XEntry.decision (T.lit p) :: T.seg 0 p))).Nodup := by rw [← hN]; exact hnd
    have hA' : Trail.lits (XTrail.trail (T.seg (p + 1) k) ++ [⟨T.lit p, true⟩]) ⊆
        Trail.lits (T.level p) :=
      fun x hx => hA (mem_lits_cons.2 (.inr hx))
    have hdec' : ∀ x ∈ T.seg (p + 1) k, x.entry.decision = false :=
      fun x hx => hdec x (by rw [hN]; exact List.mem_cons_of_mem _ hx)
    have hnd' : (Trail.vars (XTrail.trail (T.seg (p + 1) k ++
        XEntry.decision (T.lit p) :: T.seg 0 p))).Nodup := by
      have := hnd
      simp only [List.cons_append, XTrail.trail_cons, Trail.vars, List.map_cons,
        List.nodup_cons] at this
      exact this.2
    -- passing `l` unassigns its variable, which is not further down the trail
    have hl₀ : (T.lit (p + 1 + k)).1 ∉
        Trail.vars (XTrail.trail (T.seg (p + 1) k ++ XEntry.decision (T.lit p) :: T.seg 0 p)) := by
      have := hnd
      simp only [List.cons_append, XTrail.trail_cons, Trail.vars, List.map_cons,
        List.nodup_cons] at this
      exact this.1
    have hl : (T.lit (p + 1 + k)).1 ∉
        Trail.vars (XTrail.trail (T.seg (p + 1) k) ++ [⟨T.lit p, true⟩]) := fun h =>
      hl₀ (by rw [trail_level, vars_append]; exact List.mem_append_left _ h)
    have hlM : (T.lit (p + 1 + k)).1 ∉ Trail.vars (XTrail.trail (T.seg 0 p)) := fun h =>
      hl₀ (by rw [trail_level, vars_append]; exact List.mem_append_right _ h)
    -- `cur.clear l.1` is `cur.unassign [l.1]`, with no list built
    have hcurA' : (cur.clear (T.lit (p + 1 + k)).1).Agrees
        (XTrail.trail (T.seg (p + 1) k) ++ [⟨T.lit p, true⟩]) :=
      (Assign.Agrees.drop (N := [⟨T.lit (p + 1 + k), false⟩]) hcurA fun v hv => by
        rw [show v = (T.lit (p + 1 + k)).1 by simpa [Trail.vars] using hv]; exact hl :
        (cur.unassign [(T.lit (p + 1 + k)).1]).Agrees
          (XTrail.trail (T.seg (p + 1) k) ++ [⟨T.lit p, true⟩]))
    if hs : m.seen.assigned (T.lit (p + 1 + k)).1 = true then
      if hp : m.path = 1 then
        m.learned log (T.lit (p + 1 + k)) false hm hs hp hints hh
          (hA (mem_lits_cons.2 (.inl rfl))) hlM cur (by exact value_eq_none_of_agrees hcurA hA)
      else
        match hR : log.clause? r with
        | none => absurd hreasons.isSome (by simp [hR])
        | some R =>
          have hRfalse := (hreasons.reason hR).2
          have hm₀ := hm.resolve (e := ⟨T.lit (p + 1 + k), false⟩) hs
          have hspec := Marks.absorb_spec hcurA' (by rw [← trail_level]; exact hnd')
            ⟨m.seen, m.out, m.path - 1, m.vars⟩ R hm₀ (LRATLog.vars_mem_of_clause? hR)
            fun y hy hys => by
              have hne : y ≠ T.lit (p + 1 + k) := fun h => by simp_all
              have : y.negate ∈ Trail.lits (XTrail.trail (T.seg (p + 1) k ++
                  XEntry.decision (T.lit p) :: T.seg 0 p)) := hRfalse y hy hne
              rw [trail_level, lits_append, List.mem_append] at this
              exact this
          analyzeGo log T p k hA' (cur.clear (T.lit (p + 1 + k)).1) hcurA'
            -- `Marks.absorb` of the state with one off the path, without building that state
            (Marks.absorbGo (cur.clear (T.lit (p + 1 + k)).1) m.seen m.out (m.path - 1) m.vars R)
            hspec.1
            (by
              change 1 ≤ (Marks.absorb (cur.clear (T.lit (p + 1 + k)).1)
                ⟨m.seen, m.out, m.path - 1, m.vars⟩ R).path
              rw [hspec.1.path_eq]
              calc 1 ≤ m.path - 1 := by omega
                _ = _ := hm₀.path_eq
                _ ≤ _ := List.countP_mono_left fun e _ he => hspec.2.2.1 _ he)
            (r :: hints)
            (hh.resolve (LRATLog.find?_of_clause? hR)
              (fun y hy hne => hspec.1.clause_of_seen (hspec.2.1 y hy) (by
                have : y.negate ∈ Trail.lits (XTrail.trail (T.seg (p + 1) k ++
                    XEntry.decision (T.lit p) :: T.seg 0 p)) := hRfalse y hy hne
                rw [trail_level, lits_append, List.mem_append] at this
                exact this))
              fun y hy => by
                rcases hy with hy | ⟨hys, hy⟩
                · exact .inr (.inl (hspec.2.2.2 y hy))
                rcases mem_lits_cons.1 hy with hy | hy
                · exact .inl (negate_eq_iff.1 hy)
                · exact .inr (.inr ⟨hspec.2.2.1 _ hys, hy⟩))
            hreasons.tail hdec' hnd'
    else
      analyzeGo log T p k hA' (cur.clear (T.lit (p + 1 + k)).1) hcurA' m
        (hm.pass (e := ⟨T.lit (p + 1 + k), false⟩) (by simpa using hs)) hpath hints
        (hh.mono fun y hy => by
          rcases hy with hy | ⟨hys, hy⟩
          · exact .inl hy
          rcases mem_lits_cons.1 hy with hy | hy
          · refine absurd ?_ hs
            obtain rfl := negate_eq_iff.1 hy
            simpa [Std.Sat.Literal.negate] using hys
          · exact .inr ⟨hys, hy⟩)
        hreasons.tail hdec' hnd'

/-- **First-UIP conflict analysis** on the trail `T`, whose newest decision is at position `p`:
with `N`, the implied literals over it, and `M₀`, the trail below it, read back
(`ATrail.seg`), the clause numbered `i` is false and has a literal false at the current level. Its
literals are marked (`Cslib.Algorithms.Lean.CDCL.Marks.absorb`), and the analysis walks down the
level, adding the reasons of the entries whose variables are seen, until one seen variable is left
on the level, its first unique implication point, which is reached at the latest at the decision.
The learned clause is never false at the current level elsewhere, and the hints, the reasons
added, oldest first, and then the clause `i`, refute it by unit propagation. The variables seen are
marked in an array of `n` slots, which grows only for variables beyond it: `n` affects the cost,
not the result. -/
def analyze (log : LRATLog φ) (T : ATrail) (p : ℕ) (cur : Assign)
    (hcurA : cur.Agrees (T.level p)) (n : ℕ) (i : ℕ) (C : Clause ℕ)
    (hC : log.clause? i = some C)
    (hreasons : Reasons log
      (T.seg (p + 1) (T.size - (p + 1)) ++ XEntry.decision (T.lit p) :: T.seg 0 p))
    (hdec : ∀ x ∈ T.seg (p + 1) (T.size - (p + 1)), x.entry.decision = false)
    (hfalse : ∀ y ∈ C, y.negate ∈ Trail.lits (XTrail.trail
      (T.seg (p + 1) (T.size - (p + 1)) ++ XEntry.decision (T.lit p) :: T.seg 0 p)))
    (hcur : ∃ y ∈ C, y.negate ∈ Trail.lits (T.level p))
    (hnd : (Trail.vars (XTrail.trail
      (T.seg (p + 1) (T.size - (p + 1)) ++ XEntry.decision (T.lit p) :: T.seg 0 p))).Nodup) :
    Learned log (T.level p) (XTrail.trail (T.seg 0 p)) :=
  have hfalse' : ∀ y ∈ C, y.negate ∈ Trail.lits (T.level p) ∨
      y.negate ∈ Trail.lits (XTrail.trail (T.seg 0 p)) := fun y hy => by
    have := hfalse y hy
    rw [trail_level, lits_append, List.mem_append] at this
    exact this
  have hspec := Marks.absorb_spec hcurA (by rw [ATrail.level, ← trail_level]; exact hnd)
    (Marks.start n) C (Marks.inv_start _ _ _ _) (LRATLog.vars_mem_of_clause? hC) fun y hy _ =>
      hfalse' y hy
  analyzeGo log T p (T.size - (p + 1)) (fun _ h => h) cur hcurA ((Marks.start n).absorb cur C)
    hspec.1
    (by
      obtain ⟨y, hy, hyc⟩ := hcur
      rw [hspec.1.path_eq]
      obtain ⟨e, he, hey⟩ := List.mem_map.1 hyc
      refine List.countP_pos_iff.2 ⟨e, he, ?_⟩
      have := hspec.2.1 y hy
      rw [show e.lit.1 = y.1 by rw [hey]; rfl]
      exact this)
    [i] (RupHints.single (LRATLog.find?_of_clause? hC) fun y hy =>
      hspec.1.clause_of_seen (hspec.2.1 y hy) (hfalse' y hy))
    hreasons hdec hnd

/-- A refutation in the log: hints along which unit propagation in the log reaches a conflict from
no assumption. -/
structure Refutation (φ : CNF ℕ) where
  /-- The log. -/
  log : LRATLog φ
  /-- The hints of the empty-clause step. -/
  hints : List ℕ
  rup : propagateHints log.db [] hints = true

/-- The certificate of a refutation: its log closed with an empty-clause step. -/
def Refutation.cert (r : Refutation φ) : Array Std.Tactic.BVDecide.LRAT.IntAction :=
  r.log.finish r.hints r.rup

/-- The hints refuting a conflict with no decision, the trail `T` still to pass: at an implied
literal whose variable is seen, its reason is hinted, first, and its variables are seen. -/
def refuteGo (log : LRATLog φ) : (T : XTrail) → (seen : Assign) → (hints : List ℕ) →
    RupHints log.db (fun y => seen.assigned y.1 = true ∧ y.negate ∈ Trail.lits (XTrail.trail T))
      hints →
    Reasons log T → (∀ x ∈ T, x.entry.decision = false) → Refutation φ
  | [], _, hints, h, _, _ => ⟨log, hints, h [] fun y hy => by simp [Trail.lits] at hy⟩
  | .implied l r :: T, seen, hints, h, hreasons, hdec =>
    if hl : seen.assigned l.1 = true then
      match hR : log.clause? r with
      | some R =>
        refuteGo log T (seen.mark (R.map Prod.fst)) (r :: hints)
          (h.resolve (LRATLog.find?_of_clause? hR)
            (fun y hy hne => ⟨(Assign.assigned_mark _ _ _).2 (.inl (List.mem_map.2 ⟨y, hy, rfl⟩)),
              (hreasons.reason hR).2 y hy hne⟩)
            fun y ⟨hs, hy⟩ => by
              rcases mem_lits_cons.1 hy with hy | hy
              · exact .inl (negate_eq_iff.1 hy)
              · exact .inr ⟨(Assign.assigned_mark _ _ _).2 (.inr hs), hy⟩)
          hreasons.tail fun x hx => hdec x (List.mem_cons_of_mem _ hx)
      | none => absurd hreasons.isSome (by simp [hR])
    else
      refuteGo log T seen hints
        (h.mono fun y ⟨hs, hy⟩ => by
          rcases mem_lits_cons.1 hy with hy | hy
          · refine absurd ?_ hl
            obtain rfl := negate_eq_iff.1 hy
            simpa [Std.Sat.Literal.negate] using hs
          · exact ⟨hs, hy⟩)
        hreasons.tail fun x hx => hdec x (List.mem_cons_of_mem _ hx)
  | .decision _ :: _, _, _, _, _, hdec => absurd (hdec _ List.mem_cons_self) (by simp)

/-- **Refuting a conflict with no decision**: the clause numbered `i`, falsified by a trail of
implied literals, is hinted last, after the reasons of the entries of the trail whose variables
it or a reason hinted contains, oldest first. -/
def refute (T : XTrail) (log : LRATLog φ) (i : ℕ) (C : Clause ℕ) (hC : log.clause? i = some C)
    (hreasons : Reasons log T) (hdec : ∀ x ∈ T, x.entry.decision = false)
    (hfalse : ∀ y ∈ C, y.negate ∈ Trail.lits (XTrail.trail T)) : Refutation φ :=
  refuteGo log T (Assign.marks (C.map Prod.fst)) [i]
    (RupHints.single (LRATLog.find?_of_clause? hC) fun y hy =>
      ⟨(Assign.assigned_marks _ _).2 (List.mem_map.2 ⟨y, hy, rfl⟩), hfalse y hy⟩)
    hreasons hdec

/-- The root of a trail, in one tail-recursive pass from the newest entry: `acc` is the part below
the oldest decision seen so far, or the whole trail if there is none. -/
def XTrail.rootGo : XTrail → XTrail → XTrail
  | acc, [] => acc
  | acc, x :: M => XTrail.rootGo (if x.entry.decision then M else acc) M

/-- **The root of a trail**: the part below its oldest decision, the literals implied without any
decision. It is found in one tail-recursive pass over the trail. -/
def XTrail.root (M : XTrail) : XTrail := XTrail.rootGo M M

theorem XTrail.rootGo_eq : ∀ (M acc : XTrail),
    XTrail.rootGo acc M = if M.any (·.entry.decision) then XTrail.root M else acc
  | [], _ => rfl
  | x :: M, acc => by
    have h : XTrail.root (x :: M) =
        XTrail.rootGo (if x.entry.decision then M else x :: M) M := rfl
    rw [rootGo, h, XTrail.rootGo_eq M, XTrail.rootGo_eq M]
    by_cases hM : M.any (·.entry.decision) <;> by_cases hx : x.entry.decision <;> simp [hM, hx]

theorem XTrail.root_cons (x : XEntry) (M : XTrail) :
    XTrail.root (x :: M) = if M.any (·.entry.decision) then XTrail.root M
      else if x.entry.decision then M else x :: M := by
  rw [root, rootGo, XTrail.rootGo_eq]

theorem XTrail.root_no_decision : ∀ (M : XTrail), ∀ x ∈ XTrail.root M, x.entry.decision = false
  | [] => by simp [XTrail.root, XTrail.rootGo]
  | x :: M => by
    rw [XTrail.root_cons]
    split
    · exact XTrail.root_no_decision M
    · rename_i hM
      have hM' : ∀ y ∈ M, y.entry.decision = false := fun y hy => by
        simpa using List.any_eq_false.1 (by simpa using hM) y hy
      split
      · exact hM'
      · rename_i hx
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · simpa using hx
        · exact hM' y hy

theorem XTrail.root_suffix : ∀ (M : XTrail), ∃ A, M = A ++ XTrail.root M
  | [] => ⟨[], rfl⟩
  | x :: M => by
    rw [XTrail.root_cons]
    split
    · obtain ⟨A, hA⟩ := XTrail.root_suffix M
      exact ⟨x :: A, by rw [List.cons_append, ← hA]⟩
    · split
      · exact ⟨[x], rfl⟩
      · exact ⟨[], rfl⟩

/-- The root is the whole trail, or the part below a decision. -/
theorem XTrail.root_split : ∀ (M : XTrail), XTrail.root M = M ∨
    ∃ N d, XTrail.trail M = N ++ ⟨d, true⟩ :: XTrail.trail (XTrail.root M)
  | [] => .inl rfl
  | x :: M => by
    rw [XTrail.root_cons]
    split
    · rename_i hM
      rcases XTrail.root_split M with h | ⟨N, d, hN⟩
      · exfalso
        obtain ⟨y, hy, hyd⟩ := List.any_eq_true.1 hM
        have := XTrail.root_no_decision M y (by rw [h]; exact hy)
        simp_all
      · exact .inr ⟨x.entry :: N, d, by rw [XTrail.trail_cons, hN]; rfl⟩
    · split
      · rename_i hx
        cases x with
        | decision l => exact .inr ⟨[], l, rfl⟩
        | implied l r => simp [XEntry.entry] at hx
      · exact .inl rfl

theorem XTrail.root_of_no_decision :
    ∀ M : XTrail, (∀ x ∈ M, x.entry.decision = false) → XTrail.root M = M
  | [], _ => rfl
  | x :: M, h => by
    have hM : M.any (·.entry.decision) = false :=
      List.any_eq_false.2 fun y hy => by simp [h y (List.mem_cons_of_mem _ hy)]
    rw [XTrail.root_cons]
    simp [hM, h x List.mem_cons_self]

theorem XTrail.root_root (M : XTrail) : XTrail.root (XTrail.root M) = XTrail.root M :=
  XTrail.root_of_no_decision _ (XTrail.root_no_decision M)

/-- Below a decision, the root is that of the trail below it. -/
theorem XTrail.root_append_decision (d : Literal ℕ) (K : XTrail) :
    ∀ J : XTrail, XTrail.root (J ++ .decision d :: K) = XTrail.root K
  | [] => by
    rw [List.nil_append, XTrail.root_cons]
    split
    · rfl
    · rename_i hK
      simp only [XEntry.entry, ite_true]
      exact (XTrail.root_of_no_decision K fun y hy => by
        simpa using List.any_eq_false.1 (by simpa using hK) y hy).symm
  | x :: J => by
    rw [List.cons_append, XTrail.root_cons, ite_eq_left_iff.2 fun h => absurd (by simp) h]
    exact XTrail.root_append_decision d K J

/-- The root only grows when an entry is added. -/
theorem XTrail.lits_root_cons {x : XEntry} {M : XTrail} {l : Literal ℕ}
    (h : l ∈ Trail.lits (XTrail.trail (XTrail.root M))) :
    l ∈ Trail.lits (XTrail.trail (XTrail.root (x :: M))) := by
  rw [XTrail.root_cons]
  split
  · exact h
  · rename_i hM
    rw [XTrail.root_of_no_decision M fun y hy => by
      simpa using List.any_eq_false.1 (by simpa using hM) y hy] at h
    split
    · exact h
    · simp only [XTrail.trail_cons, Trail.lits, List.map_cons, List.mem_cons] at h ⊢
      exact .inr h

namespace ATrail

/-- Scanning up from position `i`, through `k` positions: the first decision, or `i + k` if there
is none. -/
def firstDecGo (T : ATrail) : ℕ → ℕ → ℕ
  | i, 0 => i
  | i, k + 1 => if T.rsns.getD i 0 == 0 then i else T.firstDecGo (i + 1) k

/-- **The position of the oldest decision**, or the size of the trail if there is none: the
entries below it are the root of the trail (`ATrail.root_seg`). -/
def rootPos (T : ATrail) : ℕ := T.firstDecGo 0 T.size

theorem firstDecGo_spec (T : ATrail) : ∀ i k, i ≤ T.firstDecGo i k ∧ T.firstDecGo i k ≤ i + k ∧
    (∀ j, i ≤ j → j < T.firstDecGo i k → T.rsns.getD j 0 ≠ 0) ∧
    (T.firstDecGo i k < i + k → T.rsns.getD (T.firstDecGo i k) 0 = 0)
  | i, 0 => ⟨le_rfl, le_rfl, fun j h₁ h₂ => absurd h₂ (by simp [firstDecGo]; omega),
      fun h => absurd h (by simp [firstDecGo])⟩
  | i, k + 1 => by
    simp only [firstDecGo]
    split
    · rename_i h
      exact ⟨le_rfl, by omega, fun j h₁ h₂ => absurd h₂ (by omega), fun _ => by simpa using h⟩
    · rename_i h
      obtain ⟨h₁, h₂, h₃, h₄⟩ := T.firstDecGo_spec (i + 1) k
      refine ⟨by omega, by omega, fun j hj₁ hj₂ => ?_, fun hl => h₄ (by omega)⟩
      by_cases hji : j = i
      · subst hji; simpa using h
      · exact h₃ j (by omega) hj₂

private theorem firstDecGo_succ (T : ATrail) : ∀ i k, T.firstDecGo i (k + 1) =
    if T.firstDecGo i k < i + k then T.firstDecGo i k
    else if T.rsns.getD (i + k) 0 = 0 then i + k else i + k + 1
  | i, 0 => by
    simp only [firstDecGo, Nat.add_zero, Nat.lt_irrefl, ↓reduceIte, beq_iff_eq]
  | i, k + 1 => by
    rw [firstDecGo, T.firstDecGo_succ (i + 1) k, firstDecGo]
    by_cases h : T.rsns.getD i 0 = 0
    · simp [h]
    · simp only [h, beq_iff_eq, ↓reduceIte, show i + 1 + k = i + (k + 1) by omega]

private theorem any_seg_decision (T : ATrail) (k : ℕ) :
    (T.seg 0 k).any (·.entry.decision) = true ↔ T.firstDecGo 0 k < k := by
  obtain ⟨-, h₂, h₃, h₄⟩ := T.firstDecGo_spec 0 k
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hxd⟩
    obtain ⟨j, -, hj, rfl⟩ := mem_seg.1 hx
    rw [← XEntry.isDecision_eq, isDecision_entry] at hxd
    by_contra hc
    exact h₃ j (Nat.zero_le _) (by omega) (by simpa using hxd)
  · intro hlt
    refine ⟨T.entry (T.firstDecGo 0 k), mem_seg.2 ⟨_, Nat.zero_le _, by omega, rfl⟩, ?_⟩
    rw [← XEntry.isDecision_eq, isDecision_entry]
    simpa using h₄ (by omega)

/-- **The root of the trail read back** is the part below the oldest decision. -/
theorem root_seg (T : ATrail) : ∀ k, XTrail.root (T.seg 0 k) = T.seg 0 (T.firstDecGo 0 k)
  | 0 => rfl
  | k + 1 => by
    rw [seg_succ, XTrail.root_cons, T.firstDecGo_succ 0 k, Nat.zero_add]
    by_cases hlt : T.firstDecGo 0 k < k
    · have ha := (T.any_seg_decision k).2 hlt
      simp only [ha, hlt, ↓reduceIte]
      exact T.root_seg k
    · have ha : (T.seg 0 k).any (·.entry.decision) = false :=
        Bool.eq_false_iff.2 fun h => hlt ((T.any_seg_decision k).1 h)
      simp only [ha, hlt, ↓reduceIte, Bool.false_eq_true]
      by_cases hd : T.rsns.getD k 0 = 0
      · have hx : (T.entry k).entry.decision = true := by rw [entry_of_rsn_zero hd]; rfl
        simp only [hx, hd, ↓reduceIte]
      · obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hd
        have hx : (T.entry k).entry.decision = false := by rw [entry_of_rsn_succ hr]; rfl
        simp only [hx, hd, ↓reduceIte, Bool.false_eq_true]
        rw [seg_succ, Nat.zero_add]

theorem rootPos_le (T : ATrail) : T.rootPos ≤ T.size := by
  have := (T.firstDecGo_spec 0 T.size).2.1
  unfold rootPos; omega

end ATrail

theorem XTrail.reasonIds_append (M N : XTrail) :
    XTrail.reasonIds (M ++ N) = XTrail.reasonIds M ++ XTrail.reasonIds N :=
  List.filterMap_append

theorem XTrail.mem_reasonIds_root {M : XTrail} {r : ℕ} (h : r ∈ XTrail.reasonIds (XTrail.root M)) :
    r ∈ XTrail.reasonIds M := by
  obtain ⟨A, hA⟩ := XTrail.root_suffix M
  rw [hA, XTrail.reasonIds_append]
  exact List.mem_append_right _ h

/-- **The reasons make the root true in partial models**: on a trail without decisions, every
partial model of numbered clauses containing the reasons makes every literal of the trail true. -/
theorem Reasons.psat_of_no_decision {log : LRATLog φ} {db : List (ℕ × Clause ℕ)}
    (hdb : ∀ e ∈ db, log.clause? e.1 = some e.2) {ρ : ℕ → Option Bool}
    (hρ : ∀ e ∈ db, PSat ρ e.2) {M : XTrail} (h : Reasons log M)
    (hnodec : ∀ x ∈ M, x.entry.decision = false)
    (hR : ∀ r ∈ XTrail.reasonIds M, ∃ R, (r, R) ∈ db) :
    ∀ l ∈ Trail.lits (XTrail.trail M), ρ l.1 = some l.2 := by
  induction h with
  | nil => simp [Trail.lits]
  | decision l _ _ => exact absurd (hnodec _ List.mem_cons_self) (by simp [XEntry.entry])
  | @implied M l r R _ hr hl hfalse ih =>
    have ih' := ih (fun x hx => hnodec x (List.mem_cons_of_mem _ hx))
      (fun r' hr' => hR r' (by simp [hr']))
    intro l' hl'
    simp only [XTrail.trail_cons, XEntry.entry_implied, Trail.lits, List.map_cons,
      List.mem_cons] at hl'
    rcases hl' with rfl | hl'
    · obtain ⟨R', hR'⟩ := hR r (by simp)
      have hRR : R' = R := by have := hdb _ hR'; rw [hr] at this; cases this; rfl
      subst hRR
      obtain ⟨z, hz, hzρ⟩ := hρ _ hR'
      by_contra hne
      have hzl : z ≠ l' := fun h => hne (h ▸ hzρ)
      have := ih' _ (hfalse z hz hzl)
      simp [Std.Sat.Literal.negate, hzρ] at this
    · exact ih' l' hl'

/-- **The reasons entail the root**: on a trail without decisions, in every model of numbered
clauses containing the reasons, every literal holds. The total assignment `σ` is the partial
assignment `fun v => some (σ v)`, so this is `Reasons.psat_of_no_decision`. -/
theorem Reasons.eval_of_no_decision {log : LRATLog φ} {db : List (ℕ × Clause ℕ)}
    (hdb : ∀ e ∈ db, log.clause? e.1 = some e.2) {σ : ℕ → Bool}
    (hσ : ∀ e ∈ db, e.2.eval σ = true) {M : XTrail} (h : Reasons log M)
    (hnodec : ∀ x ∈ M, x.entry.decision = false)
    (hR : ∀ r ∈ XTrail.reasonIds M, ∃ R, (r, R) ∈ db) :
    ∀ l ∈ Trail.lits (XTrail.trail M), Literal.eval σ l = true := fun l hl => by
  have hρ : ∀ e ∈ db, PSat (fun v => some (σ v)) e.2 := fun e he => by
    obtain ⟨z, hz, hzσ⟩ := (Clause.eval_eq_true_iff σ e.2).1 (hσ e he)
    exact ⟨z, hz, by simp [hzσ]⟩
  simpa using Reasons.psat_of_no_decision hdb hρ h hnodec hR l hl

/-! ### The solver state -/

/-- A trail split at its newest decision: the implied literals above it, the decision, and the
trail below it. -/
structure Split where
  /-- The implied literals above the decision. -/
  above : XTrail
  /-- The decision literal. -/
  decision : Literal ℕ
  /-- The trail below the decision. -/
  below : XTrail

/-- The split of a trail at its newest decision, if it has one. -/
def XTrail.split : XTrail → Option Split
  | [] => none
  | .decision l :: M => some ⟨[], l, M⟩
  | .implied l r :: M =>
    (XTrail.split M).map fun s => ⟨.implied l r :: s.above, s.decision, s.below⟩

theorem XTrail.split_eq_none {M : XTrail} (h : XTrail.split M = none) :
    ∀ x ∈ M, x.entry.decision = false := by
  induction M with
  | nil => simp
  | cons x M ih =>
    cases x with
    | decision l => simp [XTrail.split] at h
    | implied l r =>
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · rfl
      · exact ih (by simpa [XTrail.split] using h) y hy

theorem XTrail.split_eq_some {M : XTrail} {s : Split} (h : XTrail.split M = some s) :
    M = s.above ++ .decision s.decision :: s.below ∧ ∀ x ∈ s.above, x.entry.decision = false := by
  induction M generalizing s with
  | nil => simp [XTrail.split] at h
  | cons x M ih =>
    cases x with
    | decision l =>
      simp only [XTrail.split, Option.some.injEq] at h
      subst h
      exact ⟨rfl, by simp⟩
    | implied l r =>
      obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨hM, habove⟩ := ih hs'
      refine ⟨by simp [hM], fun y hy => ?_⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · rfl
      · exact habove y hy

namespace ATrail

/-- **The newest decision** among the first `k` positions, found by scanning down from `k - 1`. -/
def newestDecision (T : ATrail) : ℕ → Option ℕ
  | 0 => none
  | k + 1 => if T.rsns.getD k 0 == 0 then some k else T.newestDecision k

/-- Position `p` holds the newest decision of the trail. -/
structure IsNewest (T : ATrail) (p : ℕ) : Prop where
  lt : p < T.size
  decision : T.rsns.getD p 0 = 0
  above : ∀ j, p < j → j < T.size → T.rsns.getD j 0 ≠ 0

/-- The split of the trail at the position `p` of its newest decision, read back. It appears only
in statements: the solver reads the arrays. -/
def splitAt (T : ATrail) (p : ℕ) : Split := ⟨T.seg (p + 1) (T.size - (p + 1)), T.lit p, T.seg 0 p⟩

private theorem newestDecision_none (T : ATrail) :
    ∀ k, T.newestDecision k = none → ∀ j < k, T.rsns.getD j 0 ≠ 0
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | k + 1, h, j, hj => by
    simp only [newestDecision] at h
    split at h
    · simp at h
    · rename_i hk
      by_cases hjk : j = k
      · subst hjk; simpa using hk
      · exact T.newestDecision_none k h j (by omega)

private theorem newestDecision_some (T : ATrail) : ∀ k p, T.newestDecision k = some p →
    p < k ∧ T.rsns.getD p 0 = 0 ∧ ∀ j, p < j → j < k → T.rsns.getD j 0 ≠ 0
  | 0, _, h => by simp [newestDecision] at h
  | k + 1, p, h => by
    simp only [newestDecision] at h
    split at h
    · rename_i hk
      cases h
      exact ⟨by omega, by simpa using hk, fun j h₁ h₂ => absurd h₂ (by omega)⟩
    · rename_i hk
      obtain ⟨h₁, h₂, h₃⟩ := T.newestDecision_some k p h
      refine ⟨by omega, h₂, fun j hj₁ hj₂ => ?_⟩
      by_cases hjk : j = k
      · subst hjk; simpa using hk
      · exact h₃ j hj₁ (by omega)

theorem isNewest_of_newestDecision {T : ATrail} {p : ℕ} (h : T.newestDecision T.size = some p) :
    T.IsNewest p :=
  let ⟨h₁, h₂, h₃⟩ := T.newestDecision_some _ p h
  ⟨h₁, h₂, h₃⟩

private theorem split_seg_none (T : ATrail) :
    ∀ k, (∀ j < k, T.rsns.getD j 0 ≠ 0) → XTrail.split (T.seg 0 k) = none
  | 0, _ => rfl
  | k + 1, h => by
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (h k (by omega))
    rw [seg_succ, Nat.zero_add, entry_of_rsn_succ hr, XTrail.split,
      T.split_seg_none k fun j hj => h j (by omega)]
    rfl

private theorem split_seg_some (T : ATrail) {p : ℕ} (hp : T.rsns.getD p 0 = 0) :
    ∀ k, p < k → (∀ j, p < j → j < k → T.rsns.getD j 0 ≠ 0) →
      XTrail.split (T.seg 0 k) = some ⟨T.seg (p + 1) (k - (p + 1)), T.lit p, T.seg 0 p⟩
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | k + 1, h, habove => by
    rw [seg_succ, Nat.zero_add]
    by_cases hpk : p = k
    · subst hpk
      rw [entry_of_rsn_zero hp, XTrail.split, Nat.sub_self]
      rfl
    · obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (habove k (by omega) (by omega))
      rw [entry_of_rsn_succ hr, XTrail.split,
        T.split_seg_some hp k (by omega) fun j h₁ h₂ => habove j h₁ (by omega)]
      obtain ⟨m, rfl⟩ : ∃ m, k = p + 1 + m := ⟨k - (p + 1), by omega⟩
      simp only [Option.map_some, Option.some.injEq, Split.mk.injEq, and_true]
      rw [show p + 1 + m + 1 - (p + 1) = m + 1 by omega, show p + 1 + m - (p + 1) = m by omega,
        seg_succ, entry_of_rsn_succ hr]

theorem IsNewest.split {T : ATrail} {p : ℕ} (h : T.IsNewest p) :
    XTrail.split T.toX = some (T.splitAt p) :=
  T.split_seg_some h.decision _ h.lt h.above

theorem split_toX_none {T : ATrail} (h : T.newestDecision T.size = none) :
    XTrail.split T.toX = none :=
  T.split_seg_none _ (T.newestDecision_none _ h)

end ATrail

/-- **The state of the solver read back**, with the trail as a list of entries: its trail, the
numbered clauses of the database, and the log. The moves are specified, and the invariant stated,
on it; the solver's state `Cslib.Algorithms.Lean.CDCL.Exec` keeps the trail as arrays. -/
structure ExecL (φ : CNF ℕ) where
  /-- The trail. -/
  trail : XTrail
  /-- The numbered clauses of the database. -/
  db : List (ℕ × Clause ℕ)
  /-- The log of the certificate. -/
  log : LRATLog φ

/-- The clauses of the database. -/
def ExecL.clauses (S : ExecL φ) : CNF ℕ := S.db.map Prod.snd

/-- The abstract state of a solver state. -/
def ExecL.state (S : ExecL φ) : State := .run (XTrail.trail S.trail) S.clauses

/-- **The invariant of the solver**: the abstract invariant, the reasons of the trail, the numbers
of the database in the log, no clause of the database false below a decision, the numbered clauses
of `φ` in the database unless the root satisfies them, and the reasons in the database. -/
structure ExecL.Inv (S : ExecL φ) : Prop where
  run : RunInv φ φ.vars (XTrail.trail S.trail) S.clauses
  reasons : Reasons S.log S.trail
  db_log : ∀ e ∈ S.db, S.log.clause? e.1 = some e.2
  below : ∀ N d M₀, XTrail.trail S.trail = N ++ ⟨d, true⟩ :: M₀ →
    ∀ c ∈ S.clauses, ¬ Trail.Falsifies M₀ c
  /-- The numbered clauses of `φ` stay in the database, unless a literal of the root of the trail
  satisfies them. -/
  orig : ∀ e ∈ φ.lratDB,
    e ∈ S.db ∨ ∃ l ∈ e.2, l ∈ Trail.lits (XTrail.trail (XTrail.root S.trail))
  /-- The reasons of the trail are clauses of the database. -/
  reasons_db : ∀ r ∈ XTrail.reasonIds S.trail, ∃ R, (r, R) ∈ S.db

/-- The initial state: the empty trail, the clauses of `φ` with their numbers, and the empty log. -/
def ExecL.init (φ : CNF ℕ) : ExecL φ := ⟨[], φ.lratDB, LRATLog.init φ⟩

/-- In the numbering of `checkLRAT`, each number names its own clause. -/
theorem find?_zipIdx_map {e : ℕ × Clause ℕ} :
    ∀ (φ : CNF ℕ) (n : ℕ), e ∈ (φ.zipIdx n).map (fun p => (p.2 + 1, p.1)) →
      ((φ.zipIdx n).map (fun p => (p.2 + 1, p.1))).find? (·.1 == e.1) = some e
  | [], _, h => by simp at h
  | c :: φ, n, h => by
    simp only [List.zipIdx_cons, List.map_cons, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · simp
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
      have := List.le_snd_of_mem_zipIdx hp
      rw [List.find?_cons_of_neg (by simp; omega)]
      exact find?_zipIdx_map φ (n + 1) (List.mem_map.2 ⟨p, hp, rfl⟩)

/-- The clauses of the initial state are those of `φ`. -/
theorem ExecL.clauses_init (φ : CNF ℕ) : (ExecL.init φ).clauses = φ := by
  simp only [ExecL.clauses, ExecL.init, lratDB, List.map_map]
  conv_rhs => rw [← List.zipIdx_map_fst 0 φ]
  rfl

theorem ExecL.init_inv (φ : CNF ℕ) : (ExecL.init φ).Inv := by
  have hclauses : (ExecL.init φ).clauses = φ := ExecL.clauses_init φ
  refine ⟨?_, .nil, fun e he => ?_, fun N d M₀ h => by simp [ExecL.init, XTrail.trail] at h,
    fun e he => .inl he, fun r hr => by simp [ExecL.init] at hr⟩
  · rw [hclauses]
    exact (Inv.init fun c hc l hl => CNF.mem_vars.2 ⟨c, hc, l.2, hl⟩ : RunInv _ _ _ _)
  · rw [LRATLog.clause?_eq]
    simp only [ExecL.init, LRATLog.init, lratDB] at he ⊢
    rw [find?_zipIdx_map φ 0 he]
    rfl

/-! ### Steps of the solver -/

theorem XTrail.trail_of_split {M : XTrail} {sp : Split} (hsp : XTrail.split M = some sp) :
    XTrail.trail M = XTrail.trail sp.above ++ ⟨sp.decision, true⟩ :: XTrail.trail sp.below := by
  rw [(XTrail.split_eq_some hsp).1]
  simp

theorem ExecL.Inv.split_reasons {S : ExecL φ} (hS : S.Inv) {sp : Split}
    (hsp : XTrail.split S.trail = some sp) :
    Reasons S.log (sp.above ++ XEntry.decision sp.decision :: sp.below) := by
  rw [← (XTrail.split_eq_some hsp).1]
  exact hS.reasons

theorem ExecL.Inv.split_nodup {S : ExecL φ} (hS : S.Inv) {sp : Split}
    (hsp : XTrail.split S.trail = some sp) :
    (Trail.vars (XTrail.trail (sp.above ++ XEntry.decision sp.decision :: sp.below))).Nodup := by
  rw [← (XTrail.split_eq_some hsp).1]
  exact hS.run.nodup

/-- The variables of the current level, from the newest decision up, are distinct. -/
theorem ExecL.Inv.split_level_nodup {S : ExecL φ} (hS : S.Inv) {sp : Split}
    (hsp : XTrail.split S.trail = some sp) :
    (Trail.vars (XTrail.trail sp.above ++ [⟨sp.decision, true⟩])).Nodup := by
  have := hS.split_nodup hsp
  rw [XTrail.trail_append, XTrail.trail_cons, show XTrail.trail sp.above ++
    XEntry.entry (XEntry.decision sp.decision) :: XTrail.trail sp.below =
      (XTrail.trail sp.above ++ [⟨sp.decision, true⟩]) ++ XTrail.trail sp.below by simp,
    vars_append] at this
  exact this.of_append_left

theorem XTrail.falsifies_of_split {M : XTrail} {sp : Split} (hsp : XTrail.split M = some sp)
    {c : Clause ℕ} (hconf : Trail.Falsifies (XTrail.trail M) c) :
    Trail.Falsifies (XTrail.trail (sp.above ++ XEntry.decision sp.decision :: sp.below)) c := by
  rw [← (XTrail.split_eq_some hsp).1]
  exact hconf

/-- A clause false on the trail but not below its newest decision has a literal false at the
current level. -/
theorem exists_cur {A B : Trail} {d : Literal ℕ} {c : Clause ℕ}
    (hconf : Trail.Falsifies (A ++ ⟨d, true⟩ :: B) c) (hnb : ¬ Trail.Falsifies B c) :
    ∃ y ∈ c, y.negate ∈ Trail.lits (A ++ [⟨d, true⟩]) := by
  by_contra hne
  push Not at hne
  refine hnb fun y hy => ?_
  have := hconf y hy
  rw [show A ++ ⟨d, true⟩ :: B = (A ++ [⟨d, true⟩]) ++ B by simp, lits_append,
    List.mem_append] at this
  exact this.resolve_left (hne y hy)

theorem ExecL.Inv.split_cur {S : ExecL φ} (hS : S.Inv) {sp : Split}
    (hsp : XTrail.split S.trail = some sp) {e : ℕ × Clause ℕ} (he : e ∈ S.db)
    (hconf : Trail.Falsifies (XTrail.trail S.trail) e.2) :
    ∃ y ∈ e.2, y.negate ∈ Trail.lits (XTrail.trail sp.above ++ [⟨sp.decision, true⟩]) :=
  exists_cur (XTrail.trail_of_split hsp ▸ hconf)
    (hS.below _ _ _ (XTrail.trail_of_split hsp) e.2 (List.mem_map.2 ⟨e, he, rfl⟩))

/-- A clause learned at a conflict, above and below the newest decision of the split `sp`. -/
abbrev ExecL.LearnedAt (S : ExecL φ) (sp : Split) : Type :=
  Learned S.log (XTrail.trail sp.above ++ [⟨sp.decision, true⟩]) (XTrail.trail sp.below)

/-- Walking down the trail for `XTrail.dropLevels`: `acc` holds the entries of the current level
seen so far, newest last, and `hit` whether one of them is marked. At a decision, the level is
dropped if neither it nor its entries are marked, and otherwise kept with everything below; at the
bottom, the entries left are the root level, which is kept. -/
def XTrail.dropLevelsGo (marked : ℕ → Bool) : XTrail → Bool → XTrail → XTrail × XTrail
  | acc, _, [] => ([], acc.reverse)
  | acc, hit, x :: M =>
    match x with
    | .decision d =>
      if hit || marked d.1 then ([], acc.reverse ++ .decision d :: M)
      else
        let r := XTrail.dropLevelsGo marked [] false M
        (acc.reverse ++ .decision d :: r.1, r.2)
    | .implied l i => XTrail.dropLevelsGo marked (.implied l i :: acc) (hit || marked l.1) M

/-- **Dropping the newest levels** of the trail `M` none of whose variables is `marked`: the entries
dropped, and the trail kept. It reads the levels dropped and the first level kept, entry by
entry. -/
def XTrail.dropLevels (marked : ℕ → Bool) (M : XTrail) : XTrail × XTrail :=
  XTrail.dropLevelsGo marked [] false M

theorem XTrail.dropLevelsGo_spec (marked : ℕ → Bool) : ∀ (acc : XTrail) (hit : Bool) (M : XTrail),
    (∀ x ∈ acc, x.entry.decision = false) →
    hit = acc.any (fun x => marked x.entry.lit.1) →
    acc.reverse ++ M = (XTrail.dropLevelsGo marked acc hit M).1 ++
      (XTrail.dropLevelsGo marked acc hit M).2 ∧
    ((XTrail.dropLevelsGo marked acc hit M).1 = [] ∨
      ∃ J d, (XTrail.dropLevelsGo marked acc hit M).1 = J ++ [.decision d]) ∧
    (∀ x ∈ (XTrail.dropLevelsGo marked acc hit M).1, marked x.entry.lit.1 = false) ∧
    ((∀ x ∈ (XTrail.dropLevelsGo marked acc hit M).2, x.entry.decision = false) ∨
      ∃ N d M₀, (XTrail.dropLevelsGo marked acc hit M).2 = N ++ .decision d :: M₀ ∧
        (∀ x ∈ N, x.entry.decision = false) ∧
        (marked d.1 = true ∨ ∃ x ∈ N, marked x.entry.lit.1 = true))
  | acc, hit, [], hacc, _ => by
    refine ⟨by simp [dropLevelsGo], .inl rfl, by simp [dropLevelsGo], .inl ?_⟩
    simpa [dropLevelsGo] using hacc
  | acc, hit, x :: M, hacc, hhit => by
    cases x with
    | decision d =>
      simp only [dropLevelsGo]
      split
      · rename_i hm
        refine ⟨by simp, .inl rfl, by simp, .inr ⟨acc.reverse, d, M, rfl, by simpa using hacc, ?_⟩⟩
        rcases Bool.or_eq_true_iff.1 hm with h | h
        · subst hhit
          obtain ⟨x, hx, hxm⟩ := List.any_eq_true.1 h
          exact .inr ⟨x, List.mem_reverse.2 hx, hxm⟩
        · exact .inl h
      · rename_i hm
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hm
        obtain ⟨ih₁, ih₂, ih₃, ih₄⟩ :=
          XTrail.dropLevelsGo_spec marked [] false M (by simp) (by simp)
        refine ⟨?_, .inr ?_, fun y hy => ?_, ih₄⟩
        · simp only [List.reverse_nil, List.nil_append] at ih₁
          conv_lhs => rw [ih₁]
          simp
        · rcases ih₂ with h | ⟨J, d', h⟩
          · exact ⟨acc.reverse, d, by simp [h]⟩
          · exact ⟨acc.reverse ++ .decision d :: J, d', by simp [h]⟩
        · simp only [List.mem_append, List.mem_reverse, List.mem_cons] at hy
          rcases hy with hy | rfl | hy
          · subst hhit
            have := hm.1
            rw [List.any_eq_false] at this
            simpa using this y hy
          · exact hm.2
          · exact ih₃ y hy
    | implied l i =>
      simp only [dropLevelsGo]
      have := XTrail.dropLevelsGo_spec marked (.implied l i :: acc) (hit || marked l.1) M
        (fun y hy => by
          rcases List.mem_cons.1 hy with rfl | hy
          · rfl
          · exact hacc y hy)
        (by subst hhit; simp [XEntry.entry, Bool.or_comm])
      simpa using this

/-- The entries dropped and the trail kept make up the trail; the entries dropped end with a
decision, if any, and none of their variables is marked; and the trail kept is the root, or its
newest level has a marked variable, in an implied entry or in the decision. -/
theorem XTrail.dropLevels_spec (marked : ℕ → Bool) (M : XTrail) :
    M = (XTrail.dropLevels marked M).1 ++ (XTrail.dropLevels marked M).2 ∧
    ((XTrail.dropLevels marked M).1 = [] ∨
      ∃ J d, (XTrail.dropLevels marked M).1 = J ++ [.decision d]) ∧
    (∀ x ∈ (XTrail.dropLevels marked M).1, marked x.entry.lit.1 = false) ∧
    ((∀ x ∈ (XTrail.dropLevels marked M).2, x.entry.decision = false) ∨
      ∃ N d M₀, (XTrail.dropLevels marked M).2 = N ++ .decision d :: M₀ ∧
        (∀ x ∈ N, x.entry.decision = false) ∧
        (marked d.1 = true ∨ ∃ x ∈ N, marked x.entry.lit.1 = true)) := by
  have := XTrail.dropLevelsGo_spec marked [] false M (by simp) (by simp)
  simpa [XTrail.dropLevels] using this

/-- **The backjump of a conflict** at the split `sp`, as MiniSat's: the entries undone, the newest
decision level and the levels below it with no `marked` variable, and the trail kept. With the
variables of the learned clause marked, the trail kept is the trail at the second highest level of
the learned clause (`Cslib.Algorithms.Lean.CDCL.ExecL.jump_kept`). The cost is that of reading the
levels undone and the first level kept. -/
def ExecL.jump (_S : ExecL φ) (sp : Split) (marked : ℕ → Bool) : XTrail × XTrail :=
  let r := XTrail.dropLevels marked sp.below
  (sp.above ++ .decision sp.decision :: r.1, r.2)

/-- The entries undone end with a decision, and the learned clause is asserting on the trail
kept. -/
theorem ExecL.jump_spec {S : ExecL φ} {sp : Split} (hsp : XTrail.split S.trail = some sp)
    (L : S.LearnedAt sp) {marked : ℕ → Bool}
    (hmarked : ∀ v ∈ L.clause.map Prod.fst, marked v = true) :
    S.trail = (S.jump sp marked).1 ++ (S.jump sp marked).2 ∧
    (∃ J d, (S.jump sp marked).1 = J ++ [.decision d]) ∧
    (∀ y ∈ L.clause, y ≠ L.lit → y.negate ∈ Trail.lits (XTrail.trail (S.jump sp marked).2)) ∧
    L.lit.1 ∉ Trail.vars (XTrail.trail (S.jump sp marked).2) := by
  obtain ⟨h₁, h₂, h₃, -⟩ := XTrail.dropLevels_spec marked sp.below
  simp only [ExecL.jump]
  set r := XTrail.dropLevels marked sp.below
  have hbelow : XTrail.trail sp.below = XTrail.trail r.1 ++ XTrail.trail r.2 := by
    conv_lhs => rw [h₁]
    exact XTrail.trail_append _ _
  refine ⟨?_, ?_, fun y hy hne => ?_, fun h => L.undef ?_⟩
  · rw [(XTrail.split_eq_some hsp).1]
    conv_lhs => rw [h₁]
    simp
  · rcases h₂ with h | ⟨J, d, h⟩
    · exact ⟨sp.above, sp.decision, by rw [h]⟩
    · exact ⟨sp.above ++ .decision sp.decision :: J, d, by rw [h]; simp⟩
  · have := L.false_below y hy hne
    rw [hbelow, lits_append, List.mem_append] at this
    refine this.resolve_left fun hU => ?_
    obtain ⟨e, he, hel⟩ := List.mem_map.1 hU
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
    have hm := h₃ x hx
    rw [hel] at hm
    have := hmarked y.1 (List.mem_map.2 ⟨y, hy, rfl⟩)
    simp only [Std.Sat.Literal.negate] at hm
    rw [this] at hm
    exact absurd hm (by decide)
  · have hv : Trail.vars (XTrail.trail sp.below) =
        Trail.vars (XTrail.trail r.1) ++ Trail.vars (XTrail.trail r.2) := by
      rw [hbelow, vars_append]
    exact hv ▸ List.mem_append_right _ h

/-- **The target of the backjump**: the trail kept is the root, or its newest level has a marked
variable, in an implied entry or in the decision. With exactly the variables of the learned clause
marked, and none in the levels undone (`Cslib.Algorithms.Lean.CDCL.XTrail.dropLevels_spec`), this
is MiniSat's target: the highest level of the learned clause's literals other than the asserting
one, or the root for a unit clause. -/
theorem ExecL.jump_kept {S : ExecL φ} (sp : Split) {marked : ℕ → Bool} :
    (∀ x ∈ (S.jump sp marked).2, x.entry.decision = false) ∨
      ∃ N d M₀, (S.jump sp marked).2 = N ++ .decision d :: M₀ ∧
        (∀ x ∈ N, x.entry.decision = false) ∧
        (marked d.1 = true ∨ ∃ x ∈ N, marked x.entry.lit.1 = true) :=
  (XTrail.dropLevels_spec marked sp.below).2.2.2

/-- The state after Backjump and Learn, back to the trail `K` with the asserting literal implied by
the learned clause, which is added to the log. -/
def ExecL.afterConflictWith {sp : Split} (S : ExecL φ) (L : S.LearnedAt sp) (K : XTrail) :
    ExecL φ :=
  ⟨.implied L.lit L.id :: K, (L.id, L.clause) :: S.db, L.log⟩

/-- The learned clause of a conflict, and the state after Backjump and Learn: back to the trail
kept by `ExecL.jump`, with the asserting literal implied by the learned clause, which is added to
the log as one RUP step. -/
def ExecL.afterConflict (S : ExecL φ) (sp : Split) (L : S.LearnedAt sp) (marked : ℕ → Bool) :
    ExecL φ :=
  S.afterConflictWith L (S.jump sp marked).2

/-- Backjump and Learn keep the invariant and lower the rank. -/
theorem ExecL.afterConflict_spec {S : ExecL φ} (hS : S.Inv) {e : ℕ × Clause ℕ} (he : e ∈ S.db)
    (hconf : Trail.Falsifies (XTrail.trail S.trail) e.2) {sp : Split}
    (hsp : XTrail.split S.trail = some sp) (L : S.LearnedAt sp) {marked : ℕ → Bool}
    (hmarked : ∀ v ∈ L.clause.map Prod.fst, marked v = true) :
    (S.afterConflict sp L marked).Inv ∧
      rank φ.vars (S.afterConflict sp L marked).state < rank φ.vars S.state := by
  obtain ⟨hUK, ⟨J, d', hJ⟩, hfalseK, hundefK⟩ := ExecL.jump_spec hsp L hmarked
  set K := (S.jump sp marked).2
  have hsplitK : XTrail.trail S.trail = XTrail.trail J ++ ⟨d', true⟩ :: XTrail.trail K := by
    conv_lhs => rw [hUK, hJ]
    simp [XTrail.trail_append, XTrail.trail_cons]
  have hsplit := XTrail.trail_of_split hsp
  have hc : e.2 ∈ S.clauses := List.mem_map.2 ⟨e, he, rfl⟩
  have hentails : ∀ σ, CNF.eval σ S.clauses = true → L.clause.eval σ = true :=
    fun σ hσ => L.log.eval_of_clause? L.clause?_eq (by rw [← hS.run.models]; exact hσ)
  have hbj : BasicStep (.run (XTrail.trail S.trail) S.clauses)
      (.run (⟨L.lit, false⟩ :: XTrail.trail K) S.clauses) := by
    -- the asserting literal is over a variable of the current level
    have hocc : L.lit.1 ∈ Trail.vars (XTrail.trail S.trail) := by
      have := Trail.mem_vars_of_mem_lits L.above
      rw [hsplit]
      simp only [Std.Sat.Literal.negate, Trail.vars, List.map_append, List.mem_append,
        List.map_cons, List.mem_cons, List.map_nil, List.not_mem_nil, or_false] at this ⊢
      tauto
    rw [hsplitK] at hconf hocc ⊢
    exact .backjump hc hconf hentails L.mem hfalseK hundefK (.inr hocc)
  have hlearn : Learn (.run (⟨L.lit, false⟩ :: XTrail.trail K) S.clauses)
      (.run (⟨L.lit, false⟩ :: XTrail.trail K) (L.clause :: S.clauses)) :=
    .learn hentails fun l hl => .inr (by
      by_cases hne : l = L.lit
      · subst hne; simp [Trail.vars]
      · have := Trail.mem_vars_of_mem_lits (hfalseK l hl hne)
        simp only [Std.Sat.Literal.negate] at this
        simp only [Trail.vars, List.map_cons, List.mem_cons] at this ⊢
        exact .inr this)
  have hrun₁ := Step.inv (.inl hbj) (show CDCL.Inv φ φ.vars (.run _ _) from hS.run)
  have hrun₂ := Step.inv (.inr (.inl hlearn)) hrun₁
  have hroot : XTrail.root S.trail = XTrail.root K := by
    rw [hUK, hJ, List.append_assoc, List.singleton_append, XTrail.root_append_decision]
  refine ⟨⟨hrun₂, ?_, ?_, ?_, fun e' he' => ?_, fun r hr => ?_⟩, ?_⟩
  rotate_left 3
  · rcases hS.orig e' he' with h | ⟨l, hl, hlr⟩
    · exact .inl (List.mem_cons_of_mem _ h)
    · exact .inr ⟨l, hl, XTrail.lits_root_cons (hroot ▸ hlr)⟩
  · simp only [ExecL.afterConflict, ExecL.afterConflictWith, XTrail.reasonIds_implied,
      List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact ⟨L.clause, List.mem_cons_self⟩
    · obtain ⟨R, hR⟩ := hS.reasons_db r (by
        rw [hUK, XTrail.reasonIds_append]; exact List.mem_append_right _ hr)
      exact ⟨R, List.mem_cons_of_mem _ hR⟩
  rotate_left 1
  · have hbelow : Reasons S.log K := by
      have := hS.reasons
      rw [hUK] at this
      exact this.append_right
    exact .implied L.lit L.id (hbelow.mono L.ext) L.clause?_eq L.mem hfalseK
  · intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · exact L.clause?_eq
    · exact L.ext _ _ (hS.db_log e' he')
  · intro N d M₁ hN c hc'
    -- a split of the new trail is below the asserting literal, so a split of the old trail
    obtain ⟨x, N, rfl⟩ : ∃ x N', N = x :: N' := by
      cases N with
      | nil => simp [ExecL.afterConflict, ExecL.afterConflictWith] at hN
      | cons x N => exact ⟨x, N, rfl⟩
    simp only [ExecL.afterConflict, ExecL.afterConflictWith, XTrail.trail_cons, List.cons_append,
      List.cons.injEq] at hN
    obtain ⟨-, hN⟩ := hN
    rcases List.mem_cons.1 hc' with rfl | hc'
    · intro hfalse
      apply hundefK
      have := hfalse _ L.mem
      rw [congrArg Trail.vars hN]
      have hv := Trail.mem_vars_of_mem_lits this
      simp only [Trail.vars, Std.Sat.Literal.negate] at hv
      simp only [Trail.vars, List.map_append, List.map_cons, List.mem_append, List.mem_cons]
      exact .inr (.inr hv)
    · exact hS.below (XTrail.trail J ++ ⟨d', true⟩ :: N) d M₁
        (by rw [hsplitK, hN]; simp) c hc'
  · change rank φ.vars (.run (⟨L.lit, false⟩ :: XTrail.trail K) (L.clause :: S.clauses)) <
      rank φ.vars (.run (XTrail.trail S.trail) S.clauses)
    exact (LearnOrForget.rank_eq (.inl hlearn)).trans_lt (hbj.rank_lt hS.run)

/-- A unit clause of the database under the assignment `A`: a numbered clause with every literal but
one false, that literal being unassigned. -/
def findUnit (A : Assign) (db : List (ℕ × Clause ℕ)) : Option ((ℕ × Clause ℕ) × Literal ℕ) :=
  db.findSome? fun e => (e.2.find? fun l =>
    !A.assigned l.1 && e.2.all fun l' => l' == l || A.holds l'.negate).map (e, ·)

theorem findUnit_spec {A : Assign} {M : Trail} (hA : A.Agrees M) {db : List (ℕ × Clause ℕ)}
    {e : ℕ × Clause ℕ} {l : Literal ℕ} (h : findUnit A db = some (e, l)) :
    e ∈ db ∧ l ∈ e.2 ∧ l.1 ∉ Trail.vars M ∧ ∀ l' ∈ e.2, l' ≠ l → l'.negate ∈ Trail.lits M := by
  obtain ⟨e', he', h'⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨l', hl', hel⟩ := Option.map_eq_some_iff.1 h'
  cases hel
  have := List.find?_some hl'
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, Bool.or_eq_true,
    beq_iff_eq] at this
  refine ⟨he', List.mem_of_find?_eq_some hl', fun hv => ?_, fun l' hl' hne => ?_⟩
  · rw [(hA.assigned_iff _).2 hv] at this
    exact absurd this.1 (by decide)
  · exact (hA.holds_iff _).1 ((this.2 l' hl').resolve_left hne)

/-- **UnitPropagate**: add the literal of a unit clause, with that clause as its reason. -/
def ExecL.propagate (S : ExecL φ) (e : ℕ × Clause ℕ) (l : Literal ℕ) : ExecL φ :=
  ⟨.implied l e.1 :: S.trail, S.db, S.log⟩

/-- UnitPropagate with a clause of the database keeps the invariant and lowers the rank. -/
theorem ExecL.propagate_spec {S : ExecL φ} (hS : S.Inv) {e : ℕ × Clause ℕ} {l : Literal ℕ}
    (he : e ∈ S.db) (hl : l ∈ e.2) (hundef : l.1 ∉ Trail.vars (XTrail.trail S.trail))
    (hfalse : ∀ l' ∈ e.2, l' ≠ l → l'.negate ∈ Trail.lits (XTrail.trail S.trail)) :
    (S.propagate e l).Inv ∧ rank φ.vars (S.propagate e l).state < rank φ.vars S.state := by
  have hc : e.2 ∈ S.clauses := List.mem_map.2 ⟨e, he, rfl⟩
  have hstep : BasicStep (.run (XTrail.trail S.trail) S.clauses)
      (.run (⟨l, false⟩ :: XTrail.trail S.trail) S.clauses) :=
    .unitPropagate hc hl hfalse hundef
  refine ⟨⟨Step.inv (.inl hstep) (show CDCL.Inv φ φ.vars (.run _ _) from hS.run),
    .implied l e.1 hS.reasons (hS.db_log e he) hl hfalse, hS.db_log, ?_,
    fun e' he' => (hS.orig e' he').imp id fun ⟨l', hl', hr⟩ => ⟨l', hl', XTrail.lits_root_cons hr⟩,
    fun r hr => by
      simp only [ExecL.propagate, XTrail.reasonIds_implied, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨e.2, he⟩
      · exact hS.reasons_db r hr⟩,
    hstep.rank_lt hS.run⟩
  intro N d M₁ hN c hc'
  cases N with
  | nil => simp [ExecL.propagate] at hN
  | cons x N =>
    simp only [ExecL.propagate, XTrail.trail_cons, List.cons_append, List.cons.injEq] at hN
    exact hS.below N d M₁ hN.2 c hc'

/-- **Decide**: add the literal of the variable `x` with polarity `b` as a decision. -/
def ExecL.decide (S : ExecL φ) (x : ℕ) (b : Bool) : ExecL φ :=
  ⟨.decision (x, b) :: S.trail, S.db, S.log⟩

theorem ExecL.decide_spec {S : ExecL φ} (hS : S.Inv)
    (hnoconf : ∀ c ∈ S.clauses, ¬ Trail.Falsifies (XTrail.trail S.trail) c) {x : ℕ}
    (hx : x ∈ S.clauses.vars) (hundef : x ∉ Trail.vars (XTrail.trail S.trail)) (b : Bool) :
    (S.decide x b).Inv ∧ rank φ.vars (S.decide x b).state < rank φ.vars S.state := by
  have hstep : BasicStep (.run (XTrail.trail S.trail) S.clauses)
      (.run (⟨(x, b), true⟩ :: XTrail.trail S.trail) S.clauses) :=
    .decide (l := (x, b)) hundef hx
  refine ⟨⟨Step.inv (.inl hstep) (show CDCL.Inv φ φ.vars (.run _ _) from hS.run),
    .decision _ hS.reasons, hS.db_log, ?_,
    fun e' he' => (hS.orig e' he').imp id fun ⟨l', hl', hr⟩ => ⟨l', hl', XTrail.lits_root_cons hr⟩,
    fun r hr => hS.reasons_db r hr⟩, hstep.rank_lt hS.run⟩
  intro N d M₁ hN c hc'
  cases N with
  | nil =>
    simp only [ExecL.decide, XTrail.trail_cons, List.nil_append, List.cons.injEq] at hN
    rw [← hN.2]
    exact hnoconf c hc'
  | cons y N =>
    simp only [ExecL.decide, XTrail.trail_cons, List.cons_append, List.cons.injEq] at hN
    exact hS.below N d M₁ hN.2 c hc'


/-! ### Restarts -/

/-- **Restart**: going back to the root of the trail, keeping the database and the log. -/
def ExecL.restart (S : ExecL φ) : ExecL φ := ⟨XTrail.root S.trail, S.db, S.log⟩

/-- Restart keeps the invariant. -/
theorem ExecL.restart_inv {S : ExecL φ} (hS : S.Inv) : S.restart.Inv := by
  obtain ⟨A, hA⟩ := XTrail.root_suffix S.trail
  have hrun := hS.run
  have hreasons := hS.reasons
  rw [hA] at hrun hreasons
  rw [XTrail.trail_append] at hrun
  have hnodup := hrun.nodup
  rw [vars_append] at hnodup
  refine ⟨⟨hrun.models, hrun.pmodels, hnodup.of_append_right, fun x hx => hrun.subset x
    (by rw [vars_append]; exact List.mem_append_right _ hx), hrun.db_vars,
    Trail.entailed_append hrun.entailed⟩, hreasons.append_right, hS.db_log, ?_,
    fun e' he' => by
      change e' ∈ S.db ∨
        ∃ l ∈ e'.2, l ∈ Trail.lits (XTrail.trail (XTrail.root (XTrail.root S.trail)))
      rw [XTrail.root_root]; exact hS.orig e' he',
    fun r hr => hS.reasons_db r (XTrail.mem_reasonIds_root hr)⟩
  intro N d M₀ hN
  have hd : (⟨d, true⟩ : Entry) ∈ XTrail.trail (XTrail.root S.trail) := by
    change _ ∈ XTrail.trail S.restart.trail
    rw [hN]; simp
  obtain ⟨x, hx, hxe⟩ := List.mem_map.1 hd
  have := XTrail.root_no_decision S.trail x hx
  rw [hxe] at this
  exact absurd this (by simp)

/-! ### Forgetting clauses -/

/-- The numbers of the clauses of `φ` are at most its length. -/
theorem le_length_of_mem_lratDB {e : ℕ × Clause ℕ} (he : e ∈ φ.lratDB) : e.1 ≤ φ.length := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
  have := List.snd_lt_add_of_mem_zipIdx hp
  simp only at this ⊢
  omega

/-- Every clause of `φ` has a number. -/
theorem exists_mem_lratDB {c : Clause ℕ} (hc : c ∈ φ) : ∃ e ∈ φ.lratDB, e.2 = c := by
  rw [← List.zipIdx_map_fst 0 φ] at hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
  exact ⟨(p.2 + 1, p.1), List.mem_map.2 ⟨p, hp, rfl⟩, rfl⟩

/-- **Forget**: deleting the clauses numbered `ids` from the database and the log. -/
def ExecL.forget (S : ExecL φ) (ids : List ℕ) : ExecL φ :=
  ⟨S.trail, CNF.LRATLog.eraseIds S.db ids, S.log.delete ids⟩

/-- The database after Forget: the clauses whose number is not deleted. -/
theorem ExecL.mem_forget_db {S : ExecL φ} {ids : List ℕ} {e : ℕ × Clause ℕ} :
    e ∈ (S.forget ids).db ↔ e ∈ S.db ∧ e.1 ∉ ids := by
  change e ∈ CNF.LRATLog.eraseIds S.db ids ↔ _
  simp [CNF.LRATLog.eraseIds_eq]

/-- **Forgetting clauses** keeps the invariant, if they are not reasons of the trail, and the
clauses of `φ` among them are satisfied by the root of the trail. The reasons kept entail the root
(`Cslib.Algorithms.Lean.CDCL.Reasons.eval_of_no_decision`), so the remaining clauses still have the
models of `φ`, and their partial models, through the root, satisfy `φ`. This does not show that
each removed clause is partially entailed by the remaining ones, the side condition of the abstract
`Forget` rule; the invariant does not need it. -/
theorem ExecL.forget_inv {S : ExecL φ} (hS : S.Inv) {ids : List ℕ}
    (horig : ∀ e ∈ S.db, e ∈ φ.lratDB → e.1 ∈ ids →
      ∃ l ∈ e.2, l ∈ Trail.lits (XTrail.trail (XTrail.root S.trail)))
    (hreasons : ∀ r ∈ XTrail.reasonIds S.trail, r ∉ ids) :
    (S.forget ids).Inv := by
  have hmem : ∀ e ∈ (S.forget ids).db, e ∈ S.db ∧ e.1 ∉ ids := fun e he =>
    ExecL.mem_forget_db.1 he
  have hmem' : ∀ e ∈ S.db, e.1 ∉ ids → e ∈ (S.forget ids).db := fun e he hid =>
    ExecL.mem_forget_db.2 ⟨he, hid⟩
  have hsub : ∀ c ∈ (S.forget ids).clauses, c ∈ S.clauses := fun c hc => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
    exact List.mem_map.2 ⟨e, (hmem e he).1, rfl⟩
  have hkeep : ∀ e ∈ φ.lratDB, e ∈ (S.forget ids).db ∨
      ∃ l ∈ e.2, l ∈ Trail.lits (XTrail.trail (XTrail.root S.trail)) := fun e he => by
    rcases hS.orig e he with h | h
    · by_cases hid : e.1 ∈ ids
      · exact .inr (horig e h he hid)
      · exact .inl (hmem' e h hid)
    · exact .inr h
  have hreasons_db : ∀ r ∈ XTrail.reasonIds S.trail, ∃ R, (r, R) ∈ (S.forget ids).db :=
    fun r hr => by
      obtain ⟨R, hR⟩ := hS.reasons_db r hr
      exact ⟨R, hmem' _ hR (hreasons r hr)⟩
  have hrun := hS.run
  refine ⟨⟨fun σ => ?_, fun ρ hρ c hc => ?_, hrun.nodup, hrun.subset,
    fun c hc => hrun.db_vars c (hsub c hc), hrun.entailed⟩, hS.reasons.delete hreasons,
    fun e he => ?_, fun N d M₀ hN c hc => hS.below N d M₀ hN c (hsub c hc), hkeep, hreasons_db⟩
  · apply Bool.eq_iff_iff.2
    rw [CNF.eval_eq_true_iff, CNF.eval_eq_true_iff]
    refine ⟨fun h c hc => ?_, fun h c hc => ?_⟩
    · -- the root holds, so the clauses of `φ` it satisfies do too
      have hroot : ∀ l ∈ Trail.lits (XTrail.trail (XTrail.root S.trail)),
          Literal.eval σ l = true := by
        obtain ⟨A, hA⟩ := XTrail.root_suffix S.trail
        have hR := hS.reasons
        rw [hA] at hR
        exact Reasons.eval_of_no_decision (db := (S.forget ids).db)
          (fun e he => hS.db_log e (hmem e he).1)
          (fun e he => h e.2 (List.mem_map.2 ⟨e, he, rfl⟩)) hR.append_right
          (XTrail.root_no_decision _)
          (fun r hr => hreasons_db r (XTrail.mem_reasonIds_root hr))
      obtain ⟨e, he, rfl⟩ := exists_mem_lratDB hc
      rcases hkeep e he with h' | ⟨l, hl, hlr⟩
      · exact h e.2 (List.mem_map.2 ⟨e, h', rfl⟩)
      · exact (Clause.eval_eq_true_iff σ e.2).2
          ⟨l, hl, (Literal.eval_eq_true_iff σ l).1 (hroot l hlr)⟩
    · have hall := (CNF.eval_eq_true_iff σ S.clauses).1
        (by rw [hrun.models]; exact (CNF.eval_eq_true_iff σ φ).2 h)
      exact hall c (hsub c hc)
  · -- a partial model of the remaining clauses makes the root true, so it satisfies the
    -- clauses of `φ` that the root satisfies
    have hroot : ∀ l ∈ Trail.lits (XTrail.trail (XTrail.root S.trail)), ρ l.1 = some l.2 := by
      obtain ⟨A, hA⟩ := XTrail.root_suffix S.trail
      have hR := hS.reasons
      rw [hA] at hR
      exact Reasons.psat_of_no_decision (db := (S.forget ids).db)
        (fun e he => hS.db_log e (hmem e he).1)
        (fun e he => hρ e.2 (List.mem_map.2 ⟨e, he, rfl⟩)) hR.append_right
        (XTrail.root_no_decision _)
        (fun r hr => hreasons_db r (XTrail.mem_reasonIds_root hr))
    obtain ⟨e, he, rfl⟩ := exists_mem_lratDB hc
    rcases hkeep e he with h' | ⟨l, hl, hlr⟩
    · exact hρ e.2 (List.mem_map.2 ⟨e, h', rfl⟩)
    · exact ⟨l, hl, hroot l hlr⟩
  · obtain ⟨he, hid⟩ := hmem e he
    exact (LRATLog.clause?_delete hid).trans (hS.db_log e he)

/-- Forgetting leaves the trail, hence the rank, unchanged. -/
theorem ExecL.rank_forget (S : ExecL φ) (ids : List ℕ) :
    rank φ.vars (S.forget ids).state = rank φ.vars S.state := rfl

/-! ### The solver state on arrays -/

namespace ATrail

/-- Scanning down for the backjump from position `i` (exclusive): `cut` is the lowest position of
the levels dropped so far, and `hit` whether the level being read has a `marked` variable. At a
decision, the scan stops if the level has a marked variable, its decision's included, and otherwise
the level is dropped. -/
def cutGo (T : ATrail) (marked : ℕ → Bool) : ℕ → ℕ → Bool → ℕ
  | 0, cut, _ => cut
  | i + 1, cut, hit =>
    if T.rsns.getD i 0 == 0 then
      if hit || marked (T.lits.getD i 0 / 2) then cut else T.cutGo marked i i false
    else T.cutGo marked i cut (hit || marked (T.lits.getD i 0 / 2))

/-- **The backjump point** below the decision at position `p`: the entries from it up are undone.
It is what `XTrail.dropLevels` finds on the trail below `p` read back
(`ATrail.dropLevels_seg`). -/
def cutPos (T : ATrail) (marked : ℕ → Bool) (p : ℕ) : ℕ := T.cutGo marked p p false

private theorem dropLevelsGo_seg (T : ATrail) (marked : ℕ → Bool) :
    ∀ (i cut : ℕ) (hit : Bool), i ≤ cut →
    T.cutGo marked i cut hit ≤ cut ∧
    XTrail.dropLevelsGo marked (T.seg i (cut - i)).reverse hit (T.seg 0 i) =
      (T.seg (T.cutGo marked i cut hit) (cut - T.cutGo marked i cut hit),
        T.seg 0 (T.cutGo marked i cut hit))
  | 0, cut, hit, _ => by
    simp [cutGo, XTrail.dropLevelsGo]
  | i + 1, cut, hit, hic => by
    have hv : (T.lit i).1 = T.lits.getD i 0 / 2 := rfl
    -- the trail from `i + 1` to `cut`, with the entry at `i` under it
    have hup : T.seg i (cut - i) = T.seg (i + 1) (cut - (i + 1)) ++ [T.entry i] := by
      rw [show cut - i = cut - (i + 1) + 1 by omega, seg_succ_bottom]
    by_cases hd : T.rsns.getD i 0 = 0
    · have hseg : T.seg 0 (i + 1) = .decision (T.lit i) :: T.seg 0 i := by
        rw [seg_succ, Nat.zero_add, entry_of_rsn_zero hd]
      have hall : T.seg 0 cut = T.seg (i + 1) (cut - (i + 1)) ++ T.seg 0 (i + 1) := by
        have := T.seg_add 0 (i + 1) (cut - (i + 1))
        rwa [Nat.zero_add, Nat.add_sub_cancel' hic] at this
      rw [hseg, XTrail.dropLevelsGo]
      simp only [cutGo, hd, beq_self_eq_true, ↓reduceIte, hv]
      by_cases hm : (hit || marked (T.lits.getD i 0 / 2)) = true
      · simp only [hm, ↓reduceIte, Nat.sub_self, seg_zero, List.reverse_reverse, le_rfl,
          true_and, hall, hseg]
      · obtain ⟨h₁, h₂⟩ := T.dropLevelsGo_seg marked i i false le_rfl
        simp only [Nat.sub_self, seg_zero, List.reverse_nil] at h₂
        simp only [hm, Bool.false_eq_true, ↓reduceIte, h₂, List.reverse_reverse]
        refine ⟨by omega, ?_⟩
        set q := T.cutGo marked i i false
        have : T.seg q (cut - q) = T.seg (i + 1) (cut - (i + 1)) ++ T.seg q (i + 1 - q) := by
          have := T.seg_add q (i + 1 - q) (cut - (i + 1))
          rwa [show q + (i + 1 - q) = i + 1 by omega,
            show i + 1 - q + (cut - (i + 1)) = cut - q by omega] at this
        rw [this, show i + 1 - q = i - q + 1 by omega, seg_succ,
          show q + (i - q) = i by omega, entry_of_rsn_zero hd]
    · obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hd
      have hseg : T.seg 0 (i + 1) = .implied (T.lit i) r :: T.seg 0 i := by
        rw [seg_succ, Nat.zero_add, entry_of_rsn_succ hr]
      rw [hseg, XTrail.dropLevelsGo]
      have hcg : T.cutGo marked (i + 1) cut hit =
          T.cutGo marked i cut (hit || marked (T.lits.getD i 0 / 2)) := by
        simp only [cutGo, beq_iff_eq, hd, ↓reduceIte]
      rw [hcg]
      have := T.dropLevelsGo_seg marked i cut (hit || marked (T.lits.getD i 0 / 2)) (by omega)
      rw [hup, List.reverse_append, entry_of_rsn_succ hr] at this
      simpa [hv] using this

/-- **The backjump point read back**: `XTrail.dropLevels` on the trail below `p` drops the entries
from the backjump point to `p`, and keeps those below it. -/
theorem dropLevels_seg (T : ATrail) (marked : ℕ → Bool) (p : ℕ) :
    T.cutPos marked p ≤ p ∧ XTrail.dropLevels marked (T.seg 0 p) =
      (T.seg (T.cutPos marked p) (p - T.cutPos marked p), T.seg 0 (T.cutPos marked p)) := by
  have := T.dropLevelsGo_seg marked p p false le_rfl
  simpa [XTrail.dropLevels, cutPos] using this

end ATrail

/-- **The state of the solver**: its trail as arrays (`Cslib.Algorithms.Lean.CDCL.ATrail`), the
numbered clauses of the database, and the log. Its moves and its invariant are those of the state
`ExecL` it reads back as (`Cslib.Algorithms.Lean.CDCL.Exec.toL`): each move has a representation
lemma, through which the invariants carry over. -/
structure Exec (φ : CNF ℕ) where
  /-- The trail, as arrays. -/
  tr : ATrail
  /-- The numbered clauses of the database. -/
  db : List (ℕ × Clause ℕ)
  /-- The log of the certificate. -/
  log : LRATLog φ

namespace Exec

/-- The state read back, with the trail as a list of entries. -/
def toL (S : Exec φ) : ExecL φ := ⟨S.tr.toX, S.db, S.log⟩

/-- The trail read back as a list of entries, newest first. -/
def trail (S : Exec φ) : XTrail := S.tr.toX

/-- The clauses of the database. -/
def clauses (S : Exec φ) : CNF ℕ := S.db.map Prod.snd

/-- The abstract state. -/
def state (S : Exec φ) : State := S.toL.state

@[simp] theorem toL_trail (S : Exec φ) : S.toL.trail = S.trail := rfl

@[simp] theorem toL_db (S : Exec φ) : S.toL.db = S.db := rfl

@[simp] theorem toL_log (S : Exec φ) : S.toL.log = S.log := rfl

@[simp] theorem toL_clauses (S : Exec φ) : S.toL.clauses = S.clauses := rfl

/-- The invariant, `ExecL.Inv` of the state read back. -/
def Inv (S : Exec φ) : Prop := S.toL.Inv

/-- A clause learned at a conflict, above and below the newest decision of the split `sp`: the
type `ExecL.LearnedAt` of the state read back, stated on the log itself, so that compiled code
reading the log of a learned clause does not read the trail back. -/
abbrev LearnedAt (S : Exec φ) (sp : Split) : Type :=
  Learned S.log (XTrail.trail sp.above ++ [⟨sp.decision, true⟩]) (XTrail.trail sp.below)

/-- The initial state: the empty trail, the clauses of `φ` with their numbers, and the empty
log. -/
def init (φ : CNF ℕ) : Exec φ := ⟨ATrail.empty, φ.lratDB, LRATLog.init φ⟩

theorem toL_init (φ : CNF ℕ) : (init φ).toL = ExecL.init φ := rfl

theorem clauses_init (φ : CNF ℕ) : (init φ).clauses = φ := ExecL.clauses_init φ

theorem init_inv (φ : CNF ℕ) : (init φ).Inv := ExecL.init_inv φ

/-- **UnitPropagate**: the literal of a unit clause pushed, with that clause as its reason. -/
def propagate (S : Exec φ) (e : ℕ × Clause ℕ) (l : Literal ℕ) : Exec φ :=
  ⟨S.tr.push (litCode l) (e.1 + 1), S.db, S.log⟩

theorem toL_propagate (S : Exec φ) (e : ℕ × Clause ℕ) (l : Literal ℕ) :
    (S.propagate e l).toL = S.toL.propagate e l := by
  simp only [toL, propagate, ExecL.propagate, ExecL.mk.injEq, and_true]
  exact S.tr.toX_push (.implied l e.1)

@[simp] theorem trail_propagate (S : Exec φ) (e : ℕ × Clause ℕ) (l : Literal ℕ) :
    (S.propagate e l).trail = .implied l e.1 :: S.trail :=
  S.tr.toX_push (.implied l e.1)

theorem propagate_spec {S : Exec φ} (hS : S.Inv) {e : ℕ × Clause ℕ} {l : Literal ℕ}
    (he : e ∈ S.db) (hl : l ∈ e.2) (hundef : l.1 ∉ Trail.vars (XTrail.trail S.trail))
    (hfalse : ∀ l' ∈ e.2, l' ≠ l → l'.negate ∈ Trail.lits (XTrail.trail S.trail)) :
    (S.propagate e l).Inv ∧ rank φ.vars (S.propagate e l).state < rank φ.vars S.state := by
  rw [Inv, state, state, toL_propagate]
  exact ExecL.propagate_spec hS he hl hundef hfalse

/-- **Decide**: the literal of the variable `x` with polarity `b` pushed as a decision. -/
def decide (S : Exec φ) (x : ℕ) (b : Bool) : Exec φ := ⟨S.tr.push (litCode (x, b)) 0, S.db, S.log⟩

theorem toL_decide (S : Exec φ) (x : ℕ) (b : Bool) : (S.decide x b).toL = S.toL.decide x b := by
  simp only [toL, decide, ExecL.decide, ExecL.mk.injEq, and_true]
  exact S.tr.toX_push (.decision (x, b))

@[simp] theorem trail_decide (S : Exec φ) (x : ℕ) (b : Bool) :
    (S.decide x b).trail = .decision (x, b) :: S.trail :=
  S.tr.toX_push (.decision (x, b))

theorem decide_spec {S : Exec φ} (hS : S.Inv)
    (hnoconf : ∀ c ∈ S.clauses, ¬ Trail.Falsifies (XTrail.trail S.trail) c) {x : ℕ}
    (hx : x ∈ S.clauses.vars) (hundef : x ∉ Trail.vars (XTrail.trail S.trail)) (b : Bool) :
    (S.decide x b).Inv ∧ rank φ.vars (S.decide x b).state < rank φ.vars S.state := by
  rw [Inv, state, state, toL_decide]
  exact ExecL.decide_spec hS hnoconf hx hundef b

/-- **Restart**: popping back to the oldest decision, keeping the root of the trail. -/
def restart (S : Exec φ) : Exec φ := ⟨S.tr.shrink S.tr.rootPos, S.db, S.log⟩

@[simp] theorem trail_restart (S : Exec φ) : S.restart.trail = XTrail.root S.trail := by
  rw [trail, restart, ATrail.toX_shrink _ S.tr.rootPos_le, trail, ATrail.toX,
    ATrail.root_seg, ATrail.rootPos]

theorem toL_restart (S : Exec φ) : S.restart.toL = S.toL.restart := by
  simp only [toL, ExecL.restart, ExecL.mk.injEq]
  exact ⟨S.trail_restart, rfl, rfl⟩

theorem restart_inv {S : Exec φ} (hS : S.Inv) : S.restart.Inv := by
  rw [Inv, toL_restart]; exact ExecL.restart_inv hS

/-- **Forget**: deleting the clauses numbered `ids` from the database and the log. -/
def forget (S : Exec φ) (ids : List ℕ) : Exec φ :=
  ⟨S.tr, CNF.LRATLog.eraseIds S.db ids, S.log.delete ids⟩

theorem toL_forget (S : Exec φ) (ids : List ℕ) : (S.forget ids).toL = S.toL.forget ids := rfl

@[simp] theorem trail_forget (S : Exec φ) (ids : List ℕ) : (S.forget ids).trail = S.trail := rfl

theorem mem_forget_db {S : Exec φ} {ids : List ℕ} {e : ℕ × Clause ℕ} :
    e ∈ (S.forget ids).db ↔ e ∈ S.db ∧ e.1 ∉ ids :=
  ExecL.mem_forget_db (S := S.toL)

theorem forget_inv {S : Exec φ} (hS : S.Inv) {ids : List ℕ}
    (horig : ∀ e ∈ S.db, e ∈ φ.lratDB → e.1 ∈ ids →
      ∃ l ∈ e.2, l ∈ Trail.lits (XTrail.trail (XTrail.root S.trail)))
    (hreasons : ∀ r ∈ XTrail.reasonIds S.trail, r ∉ ids) :
    (S.forget ids).Inv :=
  ExecL.forget_inv hS horig hreasons

theorem rank_forget (S : Exec φ) (ids : List ℕ) :
    rank φ.vars (S.forget ids).state = rank φ.vars S.state := rfl

/-- The state after Backjump and Learn: the trail popped down to `q` entries, the asserting
literal pushed with the learned clause as its reason, and the clause added to the log. -/
def afterConflictAt {sp : Split} (S : Exec φ) (L : S.LearnedAt sp) (q : ℕ) : Exec φ :=
  ⟨(S.tr.shrink q).push (litCode L.lit) (L.id + 1), (L.id, L.clause) :: S.db, L.log⟩

theorem toL_afterConflictAt {sp : Split} (S : Exec φ) (L : S.LearnedAt sp) {q : ℕ}
    (hq : q ≤ S.tr.size) :
    (S.afterConflictAt L q).toL = S.toL.afterConflictWith L (S.tr.seg 0 q) := by
  simp only [toL, afterConflictAt, ExecL.afterConflictWith, ExecL.mk.injEq, and_true]
  exact ((S.tr.shrink q).toX_push (XEntry.implied L.lit L.id)).trans
    (by rw [ATrail.toX_shrink _ hq])

/-- **Backjump and Learn**, at the newest decision `p`: back to the trail kept by `ExecL.jump`,
popping the entries undone, with the asserting literal implied by the learned clause. -/
def afterConflict (S : Exec φ) (p : ℕ) (L : S.LearnedAt (S.tr.splitAt p)) (marked : ℕ → Bool) :
    Exec φ :=
  S.afterConflictAt L (S.tr.cutPos marked p)

/-- **The backjump read back**: the entries undone are those from the backjump point up, and the
trail kept is the one below it. -/
theorem jump_eq (S : Exec φ) {p : ℕ} (hp : S.tr.IsNewest p) (marked : ℕ → Bool) :
    S.toL.jump (S.tr.splitAt p) marked =
      (S.tr.seg (S.tr.cutPos marked p) (S.tr.size - S.tr.cutPos marked p),
        S.tr.seg 0 (S.tr.cutPos marked p)) := by
  obtain ⟨hq, hd⟩ := S.tr.dropLevels_seg marked p
  set q := S.tr.cutPos marked p
  simp only [ExecL.jump, ATrail.splitAt, hd, Prod.mk.injEq, and_true]
  have := S.tr.seg_add q (p - q + 1) (S.tr.size - (p + 1))
  rw [show q + (p - q + 1) = p + 1 by omega,
    show p - q + 1 + (S.tr.size - (p + 1)) = S.tr.size - q by have := hp.lt; omega,
    ATrail.seg_succ, show q + (p - q) = p by omega, ATrail.entry_of_rsn_zero hp.decision] at this
  exact this.symm

theorem cutPos_le {S : Exec φ} {p : ℕ} (hp : S.tr.IsNewest p) (marked : ℕ → Bool) :
    S.tr.cutPos marked p ≤ S.tr.size := by
  have := (S.tr.dropLevels_seg marked p).1; have := hp.lt; omega

theorem toL_afterConflict (S : Exec φ) {p : ℕ} (hp : S.tr.IsNewest p)
    (L : S.LearnedAt (S.tr.splitAt p)) (marked : ℕ → Bool) :
    (S.afterConflict p L marked).toL = S.toL.afterConflict (S.tr.splitAt p) L marked := by
  rw [afterConflict, toL_afterConflictAt _ _ (cutPos_le hp marked)]
  unfold ExecL.afterConflict
  rw [S.jump_eq hp]

/-- Backjump and Learn keep the invariant and lower the rank. -/
theorem afterConflict_spec {S : Exec φ} (hS : S.Inv) {e : ℕ × Clause ℕ} (he : e ∈ S.db)
    (hconf : Trail.Falsifies (XTrail.trail S.trail) e.2) {p : ℕ} (hp : S.tr.IsNewest p)
    (L : S.LearnedAt (S.tr.splitAt p)) {marked : ℕ → Bool}
    (hmarked : ∀ v ∈ L.clause.map Prod.fst, marked v = true) :
    (S.afterConflict p L marked).Inv ∧
      rank φ.vars (S.afterConflict p L marked).state < rank φ.vars S.state := by
  rw [Inv, state, state, S.toL_afterConflict hp]
  exact ExecL.afterConflict_spec hS he hconf hp.split L hmarked

end Exec

end Cslib.Algorithms.Lean.CDCL
