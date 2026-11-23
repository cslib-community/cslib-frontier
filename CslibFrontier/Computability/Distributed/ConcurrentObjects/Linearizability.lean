/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Relation.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic

/-!
# Herlihy–Wing linearizability, sequential consistency, and locality

This module formalizes concurrent invocation/response histories over multiple typed shared objects,
real-time operation precedence, **linearizability**, **sequential consistency**, and the fundamental
locality and nonblocking theorems of [HerlihyWing1990] (§§2.1–2.2, §§3.1–3.3, pp. 467–472) with the
amended L2 condition of [SelaHerlihyPetrank2021] (§4, Definition 4.1, p. 6; §§5.2–5.3,
Theorems 5.1–5.2, pp. 7–9).

Unlike upstream `Cslib.DistributedConsistency` (which axiomatizes single-object consistency
declaratively via visibility and arbitration relations on abstract event sets), this module models
operational finite sequences of invocation and response events across an arbitrary family of typed
objects `x : Obj` (`Op x`, `Resp x`), supporting incomplete execution prefixes via response-append
completion extensions (`History.IsExtension`) and per-object subhistory projections
(`History.objSubhistory`, written `H | x` in [HerlihyWing1990]). In `IsLinearizable`,
`History.prec H e₀ e₁` sees invocations `e₁` pending in `H` and enforces real-time precedence on all
operations completed in the extension `H'` (`History.IsCompletedOp H'`, equivalent to `<_{H'} ⊆ <_S`
by `History.prec_append_resp_iff`), matching Definition 4.1 of [SelaHerlihyPetrank2021] rather than
the literal printed L2 of [HerlihyWing1990] (which restricts `<_H` to operations completed in `H`
and fails both locality and nonblocking).

## Main definitions

* `Cslib.Distributed.ConcurrentObjects.Event`,
  `Cslib.Distributed.ConcurrentObjects.History`: invocation and response events and finite execution
  histories over processes `P` and object-indexed operations `Op` / responses `Resp`.
* `Cslib.Distributed.ConcurrentObjects.History.procSubhistory`,
  `Cslib.Distributed.ConcurrentObjects.History.objSubhistory`: process (`H | P`) and object
  (`H | x`) subhistory projections ([HerlihyWing1990], §2.1, p. 467).
* `Cslib.Distributed.ConcurrentObjects.History.IsSequential`,
  `Cslib.Distributed.ConcurrentObjects.History.WellFormed`,
  `Cslib.Distributed.ConcurrentObjects.History.Equivalent`,
  `Cslib.Distributed.ConcurrentObjects.History.complete`,
  `Cslib.Distributed.ConcurrentObjects.History.IsExtension`: sequentiality, per-process
  well-formedness, process-subhistory equivalence, maximal completed subhistory `complete(H)`, and
  response-append extensions ([HerlihyWing1990], §§2.1–2.2, pp. 467–469).
* `Cslib.Distributed.ConcurrentObjects.OpId`,
  `Cslib.Distributed.ConcurrentObjects.History.IsCompletedOp`,
  `Cslib.Distributed.ConcurrentObjects.History.prec`: per-process operation identifiers
  `(proc, idx)` and the irreflexive real-time precedence partial order `<_H`
  ([HerlihyWing1990], §2.2, p. 468).
* `Cslib.Distributed.ConcurrentObjects.SeqSpec`,
  `Cslib.Distributed.ConcurrentObjects.SeqSpec.ofMachine`,
  `Cslib.Distributed.ConcurrentObjects.SeqSpec.IsTotalOp`,
  `Cslib.Distributed.ConcurrentObjects.History.IsLegal`: prefix-closed single-object sequential
  specifications, deterministic state-machine specifications, total operations, and legal sequential
  histories ([HerlihyWing1990], §2.1, p. 468).
* `Cslib.Distributed.ConcurrentObjects.IsLinearizable`,
  `Cslib.Distributed.ConcurrentObjects.IsSequentiallyConsistent`: Herlihy–Wing linearizability
  ([HerlihyWing1990], §2.2, p. 469; amended L2 of [SelaHerlihyPetrank2021], §4, Definition 4.1,
  p. 6) and sequential consistency (extending [HerlihyWing1990], §3.3, p. 472 to incomplete
  histories via `History.IsExtension` and `History.complete`).
* `Cslib.Distributed.ConcurrentObjects.RegOp`,
  `Cslib.Distributed.ConcurrentObjects.RegResp`,
  `Cslib.Distributed.ConcurrentObjects.registerSeqSpec`: sequential atomic read/write register
  specification.

## Main results

* `Cslib.Distributed.ConcurrentObjects.History.prec_irrefl`,
  `Cslib.Distributed.ConcurrentObjects.History.prec_trans`,
  `Cslib.Distributed.ConcurrentObjects.History.isIntervalOrder_prec_completed`: `<_H` is a strict
  partial order and forms a `Relation.IsIntervalOrder` on completed operations.
* `Cslib.Distributed.ConcurrentObjects.acyclic_sup_of_isIntervalOrder`: algebraic interval-order
  cycle-collapse theorem showing the union of per-object strict orders with a compatible interval
  order is `Relation.Acyclic`.
* `Cslib.Distributed.ConcurrentObjects.IsLinearizable.isSequentiallyConsistent`: every linearizable
  history is sequentially consistent (after [HerlihyWing1990], §3.3, p. 472).
* `Cslib.Distributed.ConcurrentObjects.isLinearizable_iff_forall_obj`: **Herlihy–Wing Theorem 1
  (Locality)** — a well-formed history `H` is linearizable if and only if for every object `x`, its
  object subhistory `History.objSubhistory H x` is linearizable ([HerlihyWing1990], §3.1, Theorem 1,
  pp. 470–471; [SelaHerlihyPetrank2021], §5.2, Theorem 5.1, pp. 7–9).
* `Cslib.Distributed.ConcurrentObjects.exists_linearizable_append_resp_of_total`: **Herlihy–Wing
  Theorem 2 (Nonblocking)** — any pending invocation of a total operation in a linearizable history
  admits a matching response whose append remains linearizable ([HerlihyWing1990], §3.2, Theorem 2,
  pp. 471–472; [SelaHerlihyPetrank2021], §5.3, Theorem 5.2, p. 9).
* `Cslib.Distributed.ConcurrentObjects.exists_sequentiallyConsistent_not_linearizable`: explicit
  well-formed single-register history that is sequentially consistent but not linearizable
  (register counterpart of `H_7` in [HerlihyWing1990], §3.3, p. 472).
* `Cslib.Distributed.ConcurrentObjects.exists_obj_sequentiallyConsistent_not_global`: **non-locality
  of sequential consistency** — explicit well-formed 2-process, 2-register history whose per-object
  subhistories are each sequentially consistent while the combined history is not sequentially
  consistent (register counterpart of `H_8` in [HerlihyWing1990], §3.3, p. 472).

## References

* [M. P. Herlihy, J. M. Wing, *Linearizability: A Correctness Condition for Concurrent
  Objects*][HerlihyWing1990]
* [G. Sela, M. Herlihy, E. Petrank, *Brief Announcement: Linearizability: A
  Typo*][SelaHerlihyPetrank2021]
-/

public section

namespace Cslib.Distributed.ConcurrentObjects

open Relation

/-! ### Events, histories, and subhistory projections -/

/-- A single invocation or response event in a concurrent object history ([HerlihyWing1990], §2.1,
p. 467), parameterized by process type `P`, object index type `Obj`, and per-object operation and
response families `Op` and `Resp`. -/
inductive Event (P : Type*) {Obj : Type*} (Op Resp : Obj → Type*) where
  /-- Process `proc` invokes `op` on object `obj` (`⟨obj op proc⟩`). -/
  | inv (proc : P) (obj : Obj) (op : Op obj)
  /-- Process `proc` receives `res` from object `obj` (`⟨obj res proc⟩`). -/
  | resp (proc : P) (obj : Obj) (res : Resp obj)

namespace Event

variable {P Obj : Type*} {Op Resp : Obj → Type*}

/-- Process associated with an event. -/
@[expose]
def proc : Event P Op Resp → P
  | .inv p _ _ => p
  | .resp p _ _ => p

/-- Object associated with an event. -/
@[expose]
def obj : Event P Op Resp → Obj
  | .inv _ x _ => x
  | .resp _ x _ => x

/-- Whether an event is a response event. -/
@[expose]
def isResp : Event P Op Resp → Bool
  | .inv _ _ _ => false
  | .resp _ _ _ => true

@[simp]
theorem proc_inv (p : P) (x : Obj) (op : Op x) : (Event.inv p x op : Event P Op Resp).proc = p :=
  rfl

@[simp]
theorem proc_resp (p : P) (x : Obj) (res : Resp x) :
    (Event.resp p x res : Event P Op Resp).proc = p :=
  rfl

@[simp]
theorem obj_inv (p : P) (x : Obj) (op : Op x) : (Event.inv p x op : Event P Op Resp).obj = x :=
  rfl

@[simp]
theorem obj_resp (p : P) (x : Obj) (res : Resp x) :
    (Event.resp p x res : Event P Op Resp).obj = x :=
  rfl

@[simp]
theorem isResp_inv (p : P) (x : Obj) (op : Op x) :
    (Event.inv p x op : Event P Op Resp).isResp = false :=
  rfl

@[simp]
theorem isResp_resp (p : P) (x : Obj) (res : Resp x) :
    (Event.resp p x res : Event P Op Resp).isResp = true :=
  rfl

instance instDecidableEq [DecidableEq P] [DecidableEq Obj]
    [∀ x, DecidableEq (Op x)] [∀ x, DecidableEq (Resp x)] :
    DecidableEq (Event P Op Resp) := fun a b =>
  match a, b with
  | .inv p₁ x₁ op₁, .inv p₂ x₂ op₂ =>
    if hp : p₁ = p₂ then
      if hx : x₁ = x₂ then by
        subst hp hx
        exact if hop : op₁ = op₂ then isTrue (congrArg _ hop)
          else isFalse fun h => hop (by injection h)
      else isFalse fun h => hx (by injection h)
    else isFalse fun h => hp (by injection h)
  | .resp p₁ x₁ res₁, .resp p₂ x₂ res₂ =>
    if hp : p₁ = p₂ then
      if hx : x₁ = x₂ then by
        subst hp hx
        exact if hres : res₁ = res₂ then isTrue (congrArg _ hres)
          else isFalse fun h => hres (by injection h)
      else isFalse fun h => hx (by injection h)
    else isFalse fun h => hp (by injection h)
  | .inv _ _ _, .resp _ _ _ => isFalse fun h => nomatch h
  | .resp _ _ _, .inv _ _ _ => isFalse fun h => nomatch h

end Event

/-- A history is a finite sequence of invocation and response events ([HerlihyWing1990], §2.1,
p. 467). -/
abbrev History (P : Type*) {Obj : Type*} (Op Resp : Obj → Type*) : Type _ :=
  List (Event P Op Resp)

/-- Completed operation call `(proc, obj, op, res)` pairing an invocation with its matching
response. -/
structure OpCall (P : Type*) {Obj : Type*} (Op Resp : Obj → Type*) where
  /-- Invoking process. -/
  proc : P
  /-- Target object. -/
  obj : Obj
  /-- Invoked operation. -/
  op : Op obj
  /-- Returned response. -/
  res : Resp obj

namespace OpCall

variable {P Obj : Type*} {Op Resp : Obj → Type*}

/-- Expand a completed `OpCall` into its adjacent `[inv, resp]` event pair. -/
@[expose]
def toEvents (c : OpCall P Op Resp) : History P Op Resp :=
  [.inv c.proc c.obj c.op, .resp c.proc c.obj c.res]

end OpCall

/-- Per-process operation identifier `(proc, idx)` naming the `idx`-th operation invoked by process
`proc` in a history. -/
@[ext]
structure OpId (P : Type*) where
  /-- Process that invoked this operation. -/
  proc : P
  /-- Zero-based index among operations invoked by `proc`. -/
  idx : ℕ
  deriving @[expose] DecidableEq

namespace History

variable {P Obj : Type*} {Op Resp : Obj → Type*}

/-- Process subhistory `H | p` ([HerlihyWing1990], §2.1, p. 467): the subsequence of all events in
`H` whose process is `p`. -/
@[expose]
def procSubhistory [DecidableEq P] (H : History P Op Resp) (p : P) : History P Op Resp :=
  H.filter fun e => decide (e.proc = p)

/-- Object subhistory `H | x` ([HerlihyWing1990], §2.1, p. 467): the subsequence of all events in
`H` whose object is `x`. -/
@[expose]
def objSubhistory [DecidableEq Obj] (H : History P Op Resp) (x : Obj) : History P Op Resp :=
  H.filter fun e => decide (e.obj = x)

@[simp]
theorem procSubhistory_nil [DecidableEq P] (p : P) :
    procSubhistory ([] : History P Op Resp) p = [] :=
  rfl

@[simp]
theorem procSubhistory_cons [DecidableEq P] (e : Event P Op Resp) (H : History P Op Resp) (p : P) :
    procSubhistory (e :: H) p =
      if e.proc = p then e :: procSubhistory H p else procSubhistory H p := by
  simp only [procSubhistory, List.filter]
  by_cases h : e.proc = p <;> simp only [h, decide_true, decide_false, ↓reduceIte]

@[simp]
theorem procSubhistory_append [DecidableEq P] (H₁ H₂ : History P Op Resp) (p : P) :
    procSubhistory (H₁ ++ H₂) p = procSubhistory H₁ p ++ procSubhistory H₂ p := by
  simp only [procSubhistory, List.filter_append]

@[simp]
theorem objSubhistory_nil [DecidableEq Obj] (x : Obj) :
    objSubhistory ([] : History P Op Resp) x = [] :=
  rfl

@[simp]
theorem objSubhistory_cons [DecidableEq Obj] (e : Event P Op Resp) (H : History P Op Resp)
    (x : Obj) :
    objSubhistory (e :: H) x =
      if e.obj = x then e :: objSubhistory H x else objSubhistory H x := by
  simp only [objSubhistory, List.filter]
  by_cases h : e.obj = x <;> simp only [h, decide_true, decide_false, ↓reduceIte]

@[simp]
theorem objSubhistory_append [DecidableEq Obj] (H₁ H₂ : History P Op Resp) (x : Obj) :
    objSubhistory (H₁ ++ H₂) x = objSubhistory H₁ x ++ objSubhistory H₂ x := by
  simp only [objSubhistory, List.filter_append]

theorem procSubhistory_objSubhistory_comm [DecidableEq P] [DecidableEq Obj]
    (H : History P Op Resp) (p : P) (x : Obj) :
    procSubhistory (objSubhistory H x) p = objSubhistory (procSubhistory H p) x := by
  simp only [procSubhistory, objSubhistory, List.filter_filter]
  congr 1
  funext e
  exact Bool.and_comm _ _

theorem objSubhistory_idem [DecidableEq Obj] (H : History P Op Resp) (x : Obj) :
    objSubhistory (objSubhistory H x) x = objSubhistory H x := by
  simp only [objSubhistory, List.filter_filter, Bool.and_self]

theorem objSubhistory_of_ne [DecidableEq Obj] (H : History P Op Resp) {x y : Obj} (hne : x ≠ y) :
    objSubhistory (objSubhistory H x) y = [] := by
  simp only [objSubhistory, List.filter_filter, List.filter_eq_nil_iff]
  intro e _
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rintro ⟨rfl, hy⟩
  exact hne hy.symm

theorem objSubhistory_eq_self_of_forall_obj [DecidableEq Obj] {H : History P Op Resp} {x : Obj}
    (h : ∀ e ∈ H, e.obj = x) : objSubhistory H x = H :=
  List.filter_eq_self.mpr fun e hm => decide_eq_true (h e hm)

theorem objSubhistory_eq_nil_of_forall_ne [DecidableEq Obj] {H : History P Op Resp} {x : Obj}
    (h : ∀ e ∈ H, e.obj ≠ x) : objSubhistory H x = [] :=
  List.filter_eq_nil_iff.mpr fun e hm hd => h e hm (of_decide_eq_true hd)

/-- Two histories are *equivalent* if they have identical process subhistories for every process `p`
([HerlihyWing1990], §2.1, p. 467). -/
@[expose]
def Equivalent [DecidableEq P] (H₁ H₂ : History P Op Resp) : Prop :=
  ∀ p, procSubhistory H₁ p = procSubhistory H₂ p

theorem Equivalent.refl [DecidableEq P] (H : History P Op Resp) : Equivalent H H :=
  fun _ => rfl

theorem Equivalent.symm [DecidableEq P] {H₁ H₂ : History P Op Resp} (h : Equivalent H₁ H₂) :
    Equivalent H₂ H₁ :=
  fun p => (h p).symm

theorem Equivalent.trans [DecidableEq P] {H₁ H₂ H₃ : History P Op Resp}
    (h₁₂ : Equivalent H₁ H₂) (h₂₃ : Equivalent H₂ H₃) : Equivalent H₁ H₃ :=
  fun p => (h₁₂ p).trans (h₂₃ p)

theorem Equivalent.objSubhistory [DecidableEq P] [DecidableEq Obj] {H₁ H₂ : History P Op Resp}
    (h : Equivalent H₁ H₂) (x : Obj) :
    Equivalent (objSubhistory H₁ x) (objSubhistory H₂ x) := by
  intro p
  rw [procSubhistory_objSubhistory_comm, procSubhistory_objSubhistory_comm, h p]

/-- Sequential history ([HerlihyWing1990], §2.1, p. 467): starts with an invocation (when nonempty),
alternates invocations with immediately matching responses (`proc` and `obj` agree), and optionally
ends with a single pending invocation. -/
@[expose]
def IsSequential : History P Op Resp → Prop
  | [] => True
  | [.inv _ _ _] => True
  | .inv p₁ x₁ _ :: .resp p₂ x₂ _ :: rest => p₁ = p₂ ∧ x₁ = x₂ ∧ IsSequential rest
  | _ => False

instance instDecidableIsSequential [DecidableEq P] [DecidableEq Obj] :
    ∀ H : History P Op Resp, Decidable (IsSequential H)
  | [] => isTrue trivial
  | [.inv _ _ _] => isTrue trivial
  | [.resp _ _ _] => isFalse id
  | .inv p₁ x₁ _ :: .resp p₂ x₂ _ :: rest =>
    have := instDecidableIsSequential rest
    inferInstanceAs (Decidable (p₁ = p₂ ∧ x₁ = x₂ ∧ IsSequential rest))
  | .inv _ _ _ :: .inv _ _ _ :: _ => isFalse id
  | .resp _ _ _ :: _ :: _ => isFalse id

/-- A history is *well-formed* if every process subhistory `H | p` is sequential
([HerlihyWing1990], §2.1, p. 467). -/
@[expose]
def WellFormed [DecidableEq P] (H : History P Op Resp) : Prop :=
  ∀ p, IsSequential (procSubhistory H p)

theorem wellFormed_nil [DecidableEq P] : WellFormed ([] : History P Op Resp) :=
  fun _ => trivial

theorem isSequential_objSubhistory [DecidableEq Obj] {H : History P Op Resp}
    (hseq : IsSequential H) (x : Obj) : IsSequential (objSubhistory H x) := by
  match H with
  | [] => trivial
  | [.inv p y op] =>
    simp only [objSubhistory_cons, objSubhistory_nil, Event.obj_inv]
    by_cases h : y = x <;> simp only [h, ↓reduceIte] <;> trivial
  | [.resp _ _ _] => exact False.elim hseq
  | .inv _ _ _ :: .inv _ _ _ :: _ => exact False.elim hseq
  | .resp _ _ _ :: _ :: _ => exact False.elim hseq
  | .inv p₁ x₁ op :: .resp p₂ x₂ res :: rest =>
    obtain ⟨hp, hx, hrest⟩ := hseq
    subst hp hx
    simp only [objSubhistory_cons, Event.obj_inv, Event.obj_resp]
    by_cases hxx : x₁ = x
    · simp only [hxx, ↓reduceIte]
      exact ⟨rfl, rfl, isSequential_objSubhistory hrest x⟩
    · simp only [hxx, ↓reduceIte]
      exact isSequential_objSubhistory hrest x

theorem WellFormed.objSubhistory [DecidableEq P] [DecidableEq Obj] {H : History P Op Resp}
    (hwf : WellFormed H) (x : Obj) : WellFormed (objSubhistory H x) := by
  intro p
  rw [procSubhistory_objSubhistory_comm]
  exact isSequential_objSubhistory (hwf p) x

theorem isSequential_flatMap_toEvents (calls : List (OpCall P Op Resp)) :
    IsSequential (calls.flatMap OpCall.toEvents) := by
  induction calls with
  | nil => trivial
  | cons c rest ih => exact ⟨rfl, rfl, ih⟩

theorem length_flatMap_toEvents (calls : List (OpCall P Op Resp)) :
    (calls.flatMap OpCall.toEvents).length = 2 * calls.length := by
  induction calls with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.flatMap_cons, OpCall.toEvents, List.cons_append, List.nil_append,
      List.length_cons, ih]
    omega

theorem procSubhistory_flatMap_toEvents [DecidableEq P] (calls : List (OpCall P Op Resp)) (p : P) :
    procSubhistory (calls.flatMap OpCall.toEvents) p =
      (calls.filter fun c => decide (c.proc = p)).flatMap OpCall.toEvents := by
  induction calls with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.flatMap_cons, OpCall.toEvents, List.cons_append, List.nil_append,
      procSubhistory_cons, Event.proc_inv, Event.proc_resp, List.filter]
    by_cases hcp : c.proc = p
    · simp only [hcp, decide_true, ↓reduceIte, List.flatMap_cons, OpCall.toEvents,
        List.cons_append, List.nil_append, ih]
    · simp only [hcp, decide_false, ↓reduceIte, ih]

theorem objSubhistory_flatMap_toEvents [DecidableEq Obj] (calls : List (OpCall P Op Resp))
    (x : Obj) :
    objSubhistory (calls.flatMap OpCall.toEvents) x =
      (calls.filter fun c => decide (c.obj = x)).flatMap OpCall.toEvents := by
  induction calls with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.flatMap_cons, OpCall.toEvents, List.cons_append, List.nil_append,
      objSubhistory_cons, Event.obj_inv, Event.obj_resp, List.filter]
    by_cases hcx : c.obj = x
    · simp only [hcx, decide_true, ↓reduceIte, List.flatMap_cons, OpCall.toEvents,
        List.cons_append, List.nil_append, ih]
    · simp only [hcx, decide_false, ↓reduceIte, ih]

theorem wellFormed_flatMap_toEvents [DecidableEq P] (calls : List (OpCall P Op Resp)) :
    WellFormed (calls.flatMap OpCall.toEvents) := by
  intro p
  rw [procSubhistory_flatMap_toEvents]
  exact isSequential_flatMap_toEvents _

theorem exists_calls_of_isSequential_even {S : History P Op Resp}
    (hseq : IsSequential S) (heven : S.length % 2 = 0) :
    ∃ calls : List (OpCall P Op Resp), S = calls.flatMap OpCall.toEvents := by
  match S with
  | [] => exact ⟨[], rfl⟩
  | [.inv _ _ _] =>
    simp only [List.length_singleton] at heven
    omega
  | [.resp _ _ _] => exact False.elim hseq
  | .inv _ _ _ :: .inv _ _ _ :: _ => exact False.elim hseq
  | .resp _ _ _ :: _ :: _ => exact False.elim hseq
  | .inv p₁ x₁ op :: .resp p₂ x₂ res :: rest =>
    obtain ⟨hp, hx, hrest⟩ := hseq
    subst hp hx
    simp only [List.length_cons] at heven
    obtain ⟨cs, rfl⟩ := exists_calls_of_isSequential_even hrest (by omega)
    exact ⟨⟨p₁, x₁, op, res⟩ :: cs, rfl⟩

theorem isSequential_decomp {S : History P Op Resp} (hseq : IsSequential S) :
    (∃ calls : List (OpCall P Op Resp), S = calls.flatMap OpCall.toEvents) ∨
      ∃ (calls : List (OpCall P Op Resp)) (p : P) (x : Obj) (op : Op x),
        S = calls.flatMap OpCall.toEvents ++ [.inv p x op] := by
  match S with
  | [] => exact Or.inl ⟨[], rfl⟩
  | [.inv p x op] => exact Or.inr ⟨[], p, x, op, rfl⟩
  | [.resp _ _ _] => exact False.elim hseq
  | .inv _ _ _ :: .inv _ _ _ :: _ => exact False.elim hseq
  | .resp _ _ _ :: _ :: _ => exact False.elim hseq
  | .inv p₁ x₁ op :: .resp p₂ x₂ res :: rest =>
    obtain ⟨hp, hx, hrest⟩ := hseq
    subst hp hx
    rcases isSequential_decomp hrest with ⟨cs, rfl⟩ | ⟨cs, p, x, op', rfl⟩
    · exact Or.inl ⟨⟨p₁, x₁, op, res⟩ :: cs, rfl⟩
    · exact Or.inr ⟨⟨p₁, x₁, op, res⟩ :: cs, p, x, op', rfl⟩

theorem isSequential_append_pair {S : History P Op Resp} (hseq : IsSequential S)
    (heven : S.length % 2 = 0) (p : P) (x : Obj) (op : Op x) (res : Resp x) :
    IsSequential (S ++ [.inv p x op, .resp p x res]) := by
  obtain ⟨cs, rfl⟩ := exists_calls_of_isSequential_even hseq heven
  have h := isSequential_flatMap_toEvents (cs ++ [⟨p, x, op, res⟩])
  simpa only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    OpCall.toEvents] using h

/-- Maximal completed subhistory `complete(H)` ([HerlihyWing1990], §2.1, p. 467): drops pending
invocations (those with no subsequent event of the same process) while retaining all matched
invocations and responses. -/
@[expose]
def complete [DecidableEq P] : History P Op Resp → History P Op Resp
  | [] => []
  | .inv p x op :: rest =>
    if rest.any fun e => decide (e.proc = p) then .inv p x op :: complete rest
    else complete rest
  | .resp p x res :: rest => .resp p x res :: complete rest

@[simp]
theorem complete_nil [DecidableEq P] : complete ([] : History P Op Resp) = [] :=
  rfl

theorem procSubhistory_complete [DecidableEq P] (H : History P Op Resp) (p : P) :
    procSubhistory (complete H) p = complete (procSubhistory H p) := by
  induction H with
  | nil => rfl
  | cons e rest ih =>
    cases e with
    | inv q x op =>
      by_cases hqp : q = p
      · subst hqp
        simp only [complete, procSubhistory_cons, Event.proc_inv, ↓reduceIte]
        by_cases hany : (rest.any fun e' => decide (e'.proc = q)) = true
        · have hany' : ((procSubhistory rest q).any fun e' => decide (e'.proc = q)) = true := by
            rw [List.any_eq_true] at hany ⊢
            obtain ⟨e', hmem, heq⟩ := hany
            exact ⟨e', List.mem_filter.mpr ⟨hmem, heq⟩, heq⟩
          simp only [hany, hany', ↓reduceIte, procSubhistory_cons, Event.proc_inv, ih]
        · have hanyf : (rest.any fun e' => decide (e'.proc = q)) = false :=
            Bool.eq_false_iff.mpr hany
          have hfil_nil : procSubhistory rest q = [] := by
            rw [procSubhistory, List.filter_eq_nil_iff]
            intro e' hmem
            by_contra ht
            exact hany (List.any_eq_true.mpr ⟨e', hmem, ht⟩)
          simp only [hanyf, Bool.false_eq_true, ↓reduceIte, hfil_nil, complete, List.any_nil, ih]
      · simp only [complete, procSubhistory_cons, Event.proc_inv, hqp, ↓reduceIte]
        by_cases hany : (rest.any fun e' => decide (e'.proc = q)) = true
        · simp only [hany, ↓reduceIte, procSubhistory_cons, Event.proc_inv, hqp, ih]
        · have hanyf : (rest.any fun e' => decide (e'.proc = q)) = false :=
            Bool.eq_false_iff.mpr hany
          simp only [hanyf, Bool.false_eq_true, ↓reduceIte, ih]
    | resp q x res =>
      simp only [complete, procSubhistory_cons, Event.proc_resp]
      by_cases hqp : q = p
      · subst hqp
        simp only [↓reduceIte, complete, ih]
      · simp only [hqp, ↓reduceIte, ih]

theorem complete_isSequential [DecidableEq P] {H : History P Op Resp} (hseq : IsSequential H) :
    IsSequential (complete H) ∧ (complete H).length % 2 = 0 := by
  match H with
  | [] => exact ⟨trivial, rfl⟩
  | [.inv p x op] =>
    simp only [complete, List.any_nil, Bool.false_eq_true, ↓reduceIte]
    exact ⟨trivial, rfl⟩
  | [.resp _ _ _] => exact False.elim hseq
  | .inv _ _ _ :: .inv _ _ _ :: _ => exact False.elim hseq
  | .resp _ _ _ :: _ :: _ => exact False.elim hseq
  | .inv p₁ x₁ op :: .resp p₂ x₂ res :: rest =>
    obtain ⟨hp, hx, hrest⟩ := hseq
    subst hp hx
    have hany : ((Event.resp p₁ x₁ res :: rest).any fun e => decide (e.proc = p₁)) = true := by
      simp only [List.any_cons, Event.proc_resp, decide_true, Bool.true_or]
    simp only [complete, hany, ↓reduceIte, List.length_cons]
    obtain ⟨hseq', hev'⟩ := complete_isSequential hrest
    exact ⟨⟨rfl, rfl, hseq'⟩, by omega⟩

theorem complete_eq_self_of_isSequential_even [DecidableEq P] {H : History P Op Resp}
    (hseq : IsSequential H) (heven : H.length % 2 = 0) : complete H = H := by
  match H with
  | [] => rfl
  | [.inv _ _ _] =>
    simp only [List.length_singleton] at heven
    omega
  | [.resp _ _ _] => exact False.elim hseq
  | .inv _ _ _ :: .inv _ _ _ :: _ => exact False.elim hseq
  | .resp _ _ _ :: _ :: _ => exact False.elim hseq
  | .inv p₁ x₁ op :: .resp p₂ x₂ res :: rest =>
    obtain ⟨hp, hx, hrest⟩ := hseq
    subst hp hx
    have hany : ((Event.resp p₁ x₁ res :: rest).any fun e => decide (e.proc = p₁)) = true := by
      simp only [List.any_cons, Event.proc_resp, decide_true, Bool.true_or]
    simp only [List.length_cons] at heven
    simp only [complete, hany, ↓reduceIte]
    exact congrArg (fun t => .inv p₁ x₁ op :: .resp p₁ x₁ res :: t)
      (complete_eq_self_of_isSequential_even hrest (by omega))

theorem complete_wellFormed [DecidableEq P] {H : History P Op Resp} (hwf : WellFormed H) :
    WellFormed (complete H) := by
  intro p
  rw [procSubhistory_complete]
  exact (complete_isSequential (hwf p)).1

private theorem isSequential_inv_suffix_resp {L₁ L₂ : History P Op Resp} {p : P} {x : Obj}
    {op : Op x} (hseq : IsSequential (L₁ ++ .inv p x op :: L₂)) (hne : L₂ ≠ []) :
    ∃ (res : Resp x) (L₂' : History P Op Resp), L₂ = .resp p x res :: L₂' := by
  match L₁ with
  | [] =>
    match L₂ with
    | [] => exact absurd rfl hne
    | .inv _ _ _ :: _ => exact False.elim hseq
    | .resp p₂ x₂ res :: L₂' =>
      obtain ⟨hp, hx, _⟩ := hseq
      subst hp hx
      exact ⟨res, L₂', rfl⟩
  | [.resp _ _ _] => exact False.elim hseq
  | [.inv _ _ _] => exact False.elim hseq
  | .inv _ _ _ :: .inv _ _ _ :: _ => exact False.elim hseq
  | .resp _ _ _ :: _ :: _ => exact False.elim hseq
  | .inv _ _ _ :: .resp _ _ _ :: rest₁ =>
    exact isSequential_inv_suffix_resp hseq.2.2 hne

theorem complete_objSubhistory [DecidableEq P] [DecidableEq Obj] {H : History P Op Resp}
    (hwf : WellFormed H) (x : Obj) :
    complete (objSubhistory H x) = objSubhistory (complete H) x := by
  let rec go (pre suf : History P Op Resp) (h : pre ++ suf = H) :
      complete (objSubhistory suf x) = objSubhistory (complete suf) x := by
    match suf with
    | [] => rfl
    | .resp p y res :: rest =>
      have ih := go (pre ++ [.resp p y res]) rest (by rw [List.append_assoc]; exact h)
      simp only [objSubhistory_cons, Event.obj_resp, complete]
      by_cases hyx : y = x
      · simp only [hyx, ↓reduceIte, complete, ih]
      · simp only [hyx, ↓reduceIte, ih]
    | .inv p y op :: rest =>
      have ih := go (pre ++ [.inv p y op]) rest (by rw [List.append_assoc]; exact h)
      simp only [objSubhistory_cons, Event.obj_inv, complete]
      by_cases hyx : y = x
      · subst hyx
        simp only [↓reduceIte, complete]
        have hseq_p :
            IsSequential (procSubhistory pre p ++ .inv p y op :: procSubhistory rest p) := by
          have hp := hwf p
          rw [← h, procSubhistory_append, procSubhistory_cons, Event.proc_inv] at hp
          simpa only [↓reduceIte] using hp
        have hany_iff :
            ((objSubhistory rest y).any fun e => decide (e.proc = p)) =
              (rest.any fun e => decide (e.proc = p)) := by
          apply Bool.eq_iff_iff.mpr
          constructor
          · intro h1
            rw [List.any_eq_true] at h1 ⊢
            obtain ⟨e, hm, hep⟩ := h1
            exact ⟨e, (List.mem_filter.mp hm).1, hep⟩
          · intro h1
            have hne : procSubhistory rest p ≠ [] := by
              rw [List.any_eq_true] at h1
              obtain ⟨e, hm, hep⟩ := h1
              intro hnil
              have hmp : e ∈ procSubhistory rest p := List.mem_filter.mpr ⟨hm, hep⟩
              rw [hnil] at hmp
              exact List.not_mem_nil hmp
            obtain ⟨res, L₂', hL₂⟩ := isSequential_inv_suffix_resp hseq_p hne
            have hmem_p : Event.resp p y res ∈ procSubhistory rest p := by
              rw [hL₂]; exact List.mem_cons_self
            have hmem_rest : Event.resp p y res ∈ rest := (List.mem_filter.mp hmem_p).1
            rw [List.any_eq_true]
            exact ⟨.resp p y res,
              List.mem_filter.mpr ⟨hmem_rest, decide_eq_true rfl⟩, decide_eq_true rfl⟩
        rw [hany_iff]
        by_cases hany : (rest.any fun e => decide (e.proc = p)) = true
        · simp only [hany, ↓reduceIte, objSubhistory_cons, Event.obj_inv, ih]
        · have hanyf : (rest.any fun e => decide (e.proc = p)) = false :=
            Bool.eq_false_iff.mpr hany
          simp only [hanyf, Bool.false_eq_true, ↓reduceIte, ih]
      · simp only [hyx, ↓reduceIte]
        by_cases hany : (rest.any fun e => decide (e.proc = p)) = true
        · simp only [hany, ↓reduceIte, objSubhistory_cons, Event.obj_inv, hyx, ih]
        · have hanyf : (rest.any fun e => decide (e.proc = p)) = false :=
            Bool.eq_false_iff.mpr hany
          simp only [hanyf, Bool.false_eq_true, ↓reduceIte, ih]
  exact go [] H rfl

private theorem even_length_of_equivalent_complete [DecidableEq P] {H S : History P Op Resp}
    (hwf : WellFormed H) (hseq : IsSequential S) (heq : Equivalent (complete H) S) :
    S.length % 2 = 0 := by
  rcases isSequential_decomp hseq with ⟨cs, rfl⟩ | ⟨cs, p, x, op, rfl⟩
  · rw [length_flatMap_toEvents]
    omega
  · exfalso
    have hp := heq p
    rw [procSubhistory_complete] at hp
    obtain ⟨_, hev_p⟩ := complete_isSequential (hwf p)
    have hodd : (procSubhistory (cs.flatMap OpCall.toEvents ++ [.inv p x op]) p).length =
        2 * (cs.filter fun c => decide (c.proc = p)).length + 1 := by
      simp only [procSubhistory_append, procSubhistory_flatMap_toEvents, procSubhistory_cons,
        Event.proc_inv, ↓reduceIte, procSubhistory_nil, List.length_append,
        length_flatMap_toEvents, List.length_singleton]
    rw [hp, hodd] at hev_p
    omega

/-! ### Extensions by response events -/

/-- `R` consists solely of response events. -/
@[expose]
def IsRespList (R : History P Op Resp) : Prop :=
  ∀ e ∈ R, e.isResp = true

/-- `H'` is a well-formed *completion extension* of `H` obtained by appending zero or more response
events ([HerlihyWing1990], §2.2, p. 469). -/
@[expose]
def IsExtension [DecidableEq P] (H H' : History P Op Resp) : Prop :=
  ∃ R : History P Op Resp, IsRespList R ∧ H' = H ++ R ∧ WellFormed H'

theorem IsExtension.refl [DecidableEq P] {H : History P Op Resp} (hwf : WellFormed H) :
    IsExtension H H :=
  ⟨[], fun _ hm => False.elim (List.not_mem_nil hm), (List.append_nil H).symm, hwf⟩

private theorem isRespList_eq_nil_of_isSequential_even {L R : History P Op Resp}
    (hseq : IsSequential L) (heven : L.length % 2 = 0) (hresp : IsRespList R)
    (hseq_app : IsSequential (L ++ R)) : R = [] := by
  match L with
  | [] =>
    cases R with
    | nil => rfl
    | cons e rs =>
      cases e with
      | inv p x op => exact Bool.noConfusion (hresp _ List.mem_cons_self)
      | resp p x res =>
        simp only [List.nil_append] at hseq_app
        cases rs <;> exact False.elim hseq_app
  | [.inv _ _ _] =>
    simp only [List.length_singleton] at heven
    omega
  | [.resp _ _ _] => exact False.elim hseq
  | .inv _ _ _ :: .inv _ _ _ :: _ => exact False.elim hseq
  | .resp _ _ _ :: _ :: _ => exact False.elim hseq
  | .inv p₁ x₁ op :: .resp p₂ x₂ res :: rest =>
    simp only [List.length_cons] at heven
    exact isRespList_eq_nil_of_isSequential_even hseq.2.2 (by omega) hresp hseq_app.2.2

private theorem isRespList_le_one_of_isSequential {L R : History P Op Resp}
    (hseq : IsSequential L) (hresp : IsRespList R) (hseq_app : IsSequential (L ++ R)) :
    R = [] ∨ ∃ (cs : List (OpCall P Op Resp)) (p : P) (x : Obj) (op : Op x) (res : Resp x),
      L = cs.flatMap OpCall.toEvents ++ [.inv p x op] ∧ R = [.resp p x res] := by
  rcases isSequential_decomp hseq with ⟨cs, rfl⟩ | ⟨cs, p, x, op, rfl⟩
  · left
    refine isRespList_eq_nil_of_isSequential_even hseq ?_ hresp hseq_app
    rw [length_flatMap_toEvents]
    omega
  · cases R with
    | nil => exact Or.inl rfl
    | cons e rs =>
      cases e with
      | inv _ _ _ => exact Bool.noConfusion (hresp _ List.mem_cons_self)
      | resp q y res =>
        right
        have hseq' : IsSequential (cs.flatMap OpCall.toEvents ++
            (.inv p x op :: .resp q y res :: rs)) := by
          simpa only [List.append_assoc, List.singleton_append] using hseq_app
        have htail : IsSequential (.inv p x op :: .resp q y res :: rs) := by
          clear hseq hseq_app
          induction cs with
          | nil => exact hseq'
          | cons _ _ ih => exact ih hseq'.2.2
        obtain ⟨hp, hx, hrs⟩ := htail
        subst hp hx
        have hrs_nil : rs = [] := by
          cases rs with
          | nil => rfl
          | cons e' rs' =>
            cases e' with
            | inv _ _ _ =>
              exact Bool.noConfusion (hresp _ (List.mem_cons_of_mem _ List.mem_cons_self))
            | resp _ _ _ => cases rs' <;> exact False.elim hrs
        subst hrs_nil
        exact ⟨cs, p, x, op, res, rfl, rfl⟩

/-! ### Operation positions and real-time precedence `<_H` -/

/-- Position in `l` of the `n`-th element satisfying `pred` (`none` if at most `n` elements in `l`
satisfy `pred`). -/
private def nthFilterPos {α : Type*} (pred : α → Bool) : List α → ℕ → Option ℕ
  | [], _ => none
  | a :: rest, 0 =>
    if pred a then some 0 else (nthFilterPos pred rest 0).map (· + 1)
  | a :: rest, n + 1 =>
    if pred a then (nthFilterPos pred rest n).map (· + 1)
    else (nthFilterPos pred rest (n + 1)).map (· + 1)

private theorem nthFilterPos_isSome_iff {α : Type*} (pred : α → Bool) (l : List α) (n : ℕ) :
    (nthFilterPos pred l n).isSome = true ↔ n < (l.filter pred).length := by
  induction l generalizing n with
  | nil =>
    simp only [nthFilterPos, Option.isSome_none, Bool.false_eq_true, List.filter_nil,
      List.length_nil, Nat.not_lt_zero]
  | cons a rest ih =>
    cases n with
    | zero =>
      simp only [nthFilterPos, List.filter]
      cases hpa : pred a
      · simp only [Bool.false_eq_true, ↓reduceIte, Option.isSome_map, ih 0]
      · simp only [↓reduceIte, Option.isSome_some, List.length_cons, Nat.zero_lt_succ]
    | succ n =>
      simp only [nthFilterPos, List.filter]
      cases hpa : pred a
      · simp only [Bool.false_eq_true, ↓reduceIte, Option.isSome_map, ih (n + 1)]
      · simp only [↓reduceIte, Option.isSome_map, ih n, List.length_cons]
        omega

private theorem nthFilterPos_lt_length {α : Type*} {pred : α → Bool} {l : List α} {n pos : ℕ}
    (h : nthFilterPos pred l n = some pos) :
    pos < l.length ∧ l[pos]? = (l.filter pred)[n]? ∧ l[pos]?.map pred = some true := by
  induction l generalizing n pos with
  | nil => simp only [nthFilterPos, reduceCtorEq] at h
  | cons a rest ih =>
    cases n with
    | zero =>
      simp only [nthFilterPos, List.filter] at h ⊢
      cases hpa : pred a
      · simp only [hpa, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h
        obtain ⟨pos', hpos', rfl⟩ := h
        obtain ⟨hlt, hget, hpr⟩ := ih hpos'
        exact ⟨by simp only [List.length_cons]; omega,
          by simp only [List.getElem?_cons_succ, hget],
          by simp only [List.getElem?_cons_succ, hpr]⟩
      · simp only [hpa, ↓reduceIte, Option.some.injEq] at h
        subst h
        exact ⟨Nat.zero_lt_succ _, rfl,
          by simp only [List.getElem?_cons_zero, Option.map_some, hpa]⟩
    | succ n =>
      simp only [nthFilterPos, List.filter] at h ⊢
      cases hpa : pred a
      · simp only [hpa, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h
        obtain ⟨pos', hpos', rfl⟩ := h
        obtain ⟨hlt, hget, hpr⟩ := ih hpos'
        exact ⟨by simp only [List.length_cons]; omega,
          by simp only [List.getElem?_cons_succ, hget],
          by simp only [List.getElem?_cons_succ, hpr]⟩
      · simp only [hpa, ↓reduceIte, Option.map_eq_some_iff] at h
        obtain ⟨pos', hpos', rfl⟩ := h
        obtain ⟨hlt, hget, hpr⟩ := ih hpos'
        exact ⟨by simp only [List.length_cons]; omega,
          by simp only [List.getElem?_cons_succ, hget],
          by simp only [List.getElem?_cons_succ, hpr]⟩

private theorem map_eq_some_of_map_decide {α β : Type*} [DecidableEq β] {o : Option α}
    {f : α → β} {v : β} (h : o.map (fun a => decide (f a = v)) = some true) :
    o.map f = some v := by
  cases o with
  | none => simp only [Option.map_none, reduceCtorEq] at h
  | some a =>
    simp only [Option.map_some, Option.some.injEq, decide_eq_true_eq] at h ⊢
    exact h

private theorem nthFilterPos_strictMono {α : Type*} {pred : α → Bool} {l : List α}
    {m n i j : ℕ} (hmn : m < n) (hm : nthFilterPos pred l m = some i)
    (hn : nthFilterPos pred l n = some j) : i < j := by
  induction l generalizing m n i j with
  | nil => simp only [nthFilterPos, reduceCtorEq] at hm
  | cons a rest ih =>
    cases m with
    | zero =>
      cases n with
      | zero => omega
      | succ n =>
        simp only [nthFilterPos] at hm hn
        cases hpa : pred a
        · simp only [hpa, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hm hn
          obtain ⟨i', hi', rfl⟩ := hm
          obtain ⟨j', hj', rfl⟩ := hn
          have := ih (Nat.zero_lt_succ n) hi' hj'
          omega
        · simp only [hpa, ↓reduceIte, Option.some.injEq, Option.map_eq_some_iff] at hm hn
          obtain ⟨j', _, rfl⟩ := hn
          omega
    | succ m =>
      cases n with
      | zero => omega
      | succ n =>
        simp only [nthFilterPos] at hm hn
        cases hpa : pred a
        · simp only [hpa, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hm hn
          obtain ⟨i', hi', rfl⟩ := hm
          obtain ⟨j', hj', rfl⟩ := hn
          have := ih hmn hi' hj'
          omega
        · simp only [hpa, ↓reduceIte, Option.map_eq_some_iff] at hm hn
          obtain ⟨i', hi', rfl⟩ := hm
          obtain ⟨j', hj', rfl⟩ := hn
          have := ih (by omega) hi' hj'
          omega

private theorem nthFilterPos_inj {α : Type*} {pred : α → Bool} {l : List α} {u v w : ℕ}
    (hu : nthFilterPos pred l u = some w) (hv : nthFilterPos pred l v = some w) : u = v := by
  rcases Nat.lt_trichotomy u v with hlt | rfl | hgt
  · exact absurd (nthFilterPos_strictMono hlt hu hv) (Nat.lt_irrefl w)
  · rfl
  · exact absurd (nthFilterPos_strictMono hgt hv hu) (Nat.lt_irrefl w)

private theorem nthFilterPos_append_left {α : Type*} {pred : α → Bool} {l₁ : List α}
    (l₂ : List α) {n : ℕ} (hn : n < (l₁.filter pred).length) :
    nthFilterPos pred (l₁ ++ l₂) n = nthFilterPos pred l₁ n := by
  induction l₁ generalizing n with
  | nil => simp only [List.filter_nil, List.length_nil] at hn; omega
  | cons a rest ih =>
    cases n with
    | zero =>
      simp only [nthFilterPos, List.cons_append]
      cases hpa : pred a
      · simp only [List.filter, hpa] at hn
        simp only [Bool.false_eq_true, ↓reduceIte, ih hn]
      · simp only [↓reduceIte]
    | succ n =>
      simp only [nthFilterPos, List.cons_append]
      cases hpa : pred a
      · simp only [List.filter, hpa] at hn
        simp only [Bool.false_eq_true, ↓reduceIte, ih hn]
      · simp only [List.filter, hpa, List.length_cons] at hn
        simp only [↓reduceIte, ih (n := n) (by omega)]

private theorem nthFilterPos_append_right {α : Type*} {pred : α → Bool} (l₁ l₂ : List α)
    {n : ℕ} (hn : (l₁.filter pred).length ≤ n) :
    nthFilterPos pred (l₁ ++ l₂) n =
      (nthFilterPos pred l₂ (n - (l₁.filter pred).length)).map (· + l₁.length) := by
  induction l₁ generalizing n with
  | nil =>
    simp only [List.nil_append, List.filter_nil, List.length_nil, Nat.sub_zero, Nat.add_zero,
      Option.map_id']
  | cons a rest ih =>
    cases n with
    | zero =>
      have hpa : pred a = false := by
        cases hp : pred a
        · rfl
        · simp only [List.filter, hp, List.length_cons] at hn; omega
      simp only [List.filter, hpa] at hn ⊢
      simp only [List.cons_append, nthFilterPos, hpa, Bool.false_eq_true, ↓reduceIte, ih hn,
        Option.map_map, List.length_cons, Function.comp_def, Nat.add_assoc]
    | succ n =>
      simp only [List.cons_append, nthFilterPos, List.length_cons]
      cases hpa : pred a
      · simp only [List.filter, hpa] at hn ⊢
        simp only [Bool.false_eq_true, ↓reduceIte, ih hn, Option.map_map, Function.comp_def,
          Nat.add_assoc]
      · simp only [List.filter, hpa, List.length_cons] at hn ⊢
        simp only [↓reduceIte]
        rw [ih (n := n) (by omega), Option.map_map]
        have hsub : n + 1 - ((rest.filter pred).length + 1) =
            n - (rest.filter pred).length := by omega
        rw [hsub]
        simp only [Function.comp_def, Nat.add_assoc]

private theorem nthFilterPos_of_append_lt {α : Type*} {pred : α → Bool} {l₁ l₂ : List α}
    {n pos : ℕ} (h : nthFilterPos pred (l₁ ++ l₂) n = some pos) (hlt : pos < l₁.length) :
    nthFilterPos pred l₁ n = some pos := by
  by_cases hn : n < (l₁.filter pred).length
  · rwa [nthFilterPos_append_left l₂ hn] at h
  · rw [nthFilterPos_append_right l₁ l₂ (by omega), Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h
    omega

/-- Position in `H` of the `n`-th event belonging to process `p` (`none` if `p` has at most `n`
events in `H`). -/
@[expose]
def nthProcPos [DecidableEq P] (p : P) : History P Op Resp → ℕ → Option ℕ
  | [], _ => none
  | e :: rest, 0 =>
    if e.proc = p then some 0 else (nthProcPos p rest 0).map (· + 1)
  | e :: rest, n + 1 =>
    if e.proc = p then (nthProcPos p rest n).map (· + 1)
    else (nthProcPos p rest (n + 1)).map (· + 1)

/-- Position in `H` of the invocation event of operation `e = (proc, idx)`. -/
@[expose]
def invPos [DecidableEq P] (H : History P Op Resp) (e : OpId P) : Option ℕ :=
  nthProcPos e.proc H (2 * e.idx)

/-- Position in `H` of the matching response event of operation `e = (proc, idx)`. -/
@[expose]
def respPos [DecidableEq P] (H : History P Op Resp) (e : OpId P) : Option ℕ :=
  nthProcPos e.proc H (2 * e.idx + 1)

/-- `e` is a *completed operation* in `H` when its matching response is present in `H`
(`2 * e.idx + 1 < (H | e.proc).length`). -/
@[expose]
def IsCompletedOp [DecidableEq P] (H : History P Op Resp) (e : OpId P) : Prop :=
  (respPos H e).isSome = true

/-- **Real-time precedence `e₀ <_H e₁`** ([HerlihyWing1990], §2.2, p. 468): the response of `e₀`
strictly precedes the invocation of `e₁` in `H`. -/
@[expose]
def prec [DecidableEq P] (H : History P Op Resp) (e₀ e₁ : OpId P) : Prop :=
  ∃ r i, respPos H e₀ = some r ∧ invPos H e₁ = some i ∧ r < i

private theorem nthProcPos_eq_nthFilterPos [DecidableEq P] (p : P) :
    ∀ (H : History P Op Resp) (n : ℕ),
      nthProcPos p H n = nthFilterPos (fun e => decide (e.proc = p)) H n
  | [], _ => rfl
  | e :: rest, 0 => by
    simp only [nthProcPos, nthFilterPos, decide_eq_true_eq]
    by_cases hep : e.proc = p <;> simp only [hep, ↓reduceIte, nthProcPos_eq_nthFilterPos p rest 0]
  | e :: rest, n + 1 => by
    simp only [nthProcPos, nthFilterPos, decide_eq_true_eq]
    by_cases hep : e.proc = p
    · simp only [hep, ↓reduceIte, nthProcPos_eq_nthFilterPos p rest n]
    · simp only [hep, ↓reduceIte, nthProcPos_eq_nthFilterPos p rest (n + 1)]

private theorem nthProcPos_isSome_iff [DecidableEq P] (p : P) (H : History P Op Resp) (n : ℕ) :
    (nthProcPos p H n).isSome = true ↔ n < (procSubhistory H p).length := by
  rw [nthProcPos_eq_nthFilterPos]
  exact nthFilterPos_isSome_iff (fun e => decide (e.proc = p)) H n

theorem isCompletedOp_iff_lt_length [DecidableEq P] (H : History P Op Resp) (e : OpId P) :
    IsCompletedOp H e ↔ 2 * e.idx + 1 < (procSubhistory H e.proc).length :=
  nthProcPos_isSome_iff e.proc H (2 * e.idx + 1)

theorem Equivalent.isCompletedOp_iff [DecidableEq P] {H₁ H₂ : History P Op Resp}
    (heq : Equivalent H₁ H₂) (e : OpId P) :
    IsCompletedOp H₁ e ↔ IsCompletedOp H₂ e := by
  rw [isCompletedOp_iff_lt_length, isCompletedOp_iff_lt_length, heq e.proc]

private theorem nthProcPos_lt_length [DecidableEq P] {p : P} {H : History P Op Resp} {n pos : ℕ}
    (h : nthProcPos p H n = some pos) : pos < H.length ∧ H[pos]?.map Event.proc = some p := by
  rw [nthProcPos_eq_nthFilterPos] at h
  obtain ⟨hlt, _, hpr⟩ := nthFilterPos_lt_length h
  exact ⟨hlt, map_eq_some_of_map_decide hpr⟩

private theorem nthProcPos_getElem? [DecidableEq P] {p : P} {H : History P Op Resp} {n pos : ℕ}
    (h : nthProcPos p H n = some pos) : H[pos]? = (procSubhistory H p)[n]? := by
  rw [nthProcPos_eq_nthFilterPos] at h
  exact (nthFilterPos_lt_length h).2.1

private theorem nthProcPos_strictMono [DecidableEq P] {p : P} {H : History P Op Resp} {m n i j : ℕ}
    (hmn : m < n) (hm : nthProcPos p H m = some i) (hn : nthProcPos p H n = some j) : i < j := by
  rw [nthProcPos_eq_nthFilterPos] at hm hn
  exact nthFilterPos_strictMono hmn hm hn

theorem invPos_of_respPos [DecidableEq P] {H : History P Op Resp} {e : OpId P} {r : ℕ}
    (hr : respPos H e = some r) : ∃ i, invPos H e = some i ∧ i < r := by
  have hlen : 2 * e.idx + 1 < (procSubhistory H e.proc).length :=
    (nthProcPos_isSome_iff e.proc H (2 * e.idx + 1)).mp (by rw [← respPos, hr]; rfl)
  have hisome : (invPos H e).isSome = true :=
    (nthProcPos_isSome_iff e.proc H (2 * e.idx)).mpr (by omega)
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hisome
  exact ⟨i, hi, nthProcPos_strictMono (by omega) hi hr⟩

/-- Real-time precedence `<_H` is irreflexive ([HerlihyWing1990], §2.2, p. 468). -/
theorem prec_irrefl [DecidableEq P] (H : History P Op Resp) (e : OpId P) : ¬ prec H e e := by
  rintro ⟨r, i, hr, hi, hlt⟩
  have hir := nthProcPos_strictMono (by omega : 2 * e.idx < 2 * e.idx + 1) hi hr
  omega

/-- Real-time precedence `<_H` is transitive ([HerlihyWing1990], §2.2, p. 468). -/
theorem prec_trans [DecidableEq P] {H : History P Op Resp} {e₀ e₁ e₂ : OpId P}
    (h₀₁ : prec H e₀ e₁) (h₁₂ : prec H e₁ e₂) : prec H e₀ e₂ := by
  obtain ⟨r₀, i₁, hr₀, hi₁, hlt₀⟩ := h₀₁
  obtain ⟨r₁, i₂, hr₁, hi₂, hlt₁⟩ := h₁₂
  have hir₁ := nthProcPos_strictMono (by omega : 2 * e₁.idx < 2 * e₁.idx + 1) hi₁ hr₁
  exact ⟨r₀, i₂, hr₀, hi₂, by omega⟩

/-- On the subtype of completed operations of `H`, real-time precedence `<_H` forms a
`Relation.IsIntervalOrder` (`Cslib.Foundations.Relation.Defs`). -/
theorem isIntervalOrder_prec_completed [DecidableEq P] (H : History P Op Resp) :
    IsIntervalOrder (fun a b : { e : OpId P // IsCompletedOp H e } => prec H a.1 b.1) := by
  refine ⟨{ irrefl := fun a => prec_irrefl H a.1
            trans := fun _ _ _ => prec_trans }, ?_⟩
  rintro ⟨a₁, _⟩ ⟨b₁, _⟩ ⟨a₂, _⟩ ⟨b₂, _⟩ ⟨⟨r₁, i₁, hr₁, hi₁, h₁⟩, ⟨r₂, i₂, hr₂, hi₂, h₂⟩⟩
  obtain ⟨ia₂, hia₂, hlt₂⟩ := invPos_of_respPos hr₂
  by_cases hcmp : r₁ < i₂
  · exact Or.inl ⟨r₁, i₂, hr₁, hi₂, hcmp⟩
  · exact Or.inr ⟨r₂, i₁, hr₂, hi₁, by omega⟩

theorem prec_of_same_proc_lt [DecidableEq P] {H : History P Op Resp} {e₀ e₁ : OpId P}
    (hp : e₀.proc = e₁.proc) (hidx : e₀.idx < e₁.idx)
    (hc₀ : IsCompletedOp H e₀) (hc₁ : IsCompletedOp H e₁) : prec H e₀ e₁ := by
  obtain ⟨r₀, hr₀⟩ := Option.isSome_iff_exists.mp hc₀
  obtain ⟨r₁, hr₁⟩ := Option.isSome_iff_exists.mp hc₁
  obtain ⟨i₁, hi₁, _⟩ := invPos_of_respPos hr₁
  have hi₁' : nthProcPos e₀.proc H (2 * e₁.idx) = some i₁ := by rw [hp]; exact hi₁
  exact ⟨r₀, i₁, hr₀, hi₁, nthProcPos_strictMono (by omega : 2 * e₀.idx + 1 < 2 * e₁.idx) hr₀ hi₁'⟩

private theorem nthProcPos_append_left [DecidableEq P] {p : P} {H₁ : History P Op Resp}
    (H₂ : History P Op Resp) {n : ℕ} (hn : n < (procSubhistory H₁ p).length) :
    nthProcPos p (H₁ ++ H₂) n = nthProcPos p H₁ n := by
  rw [nthProcPos_eq_nthFilterPos, nthProcPos_eq_nthFilterPos]
  exact nthFilterPos_append_left H₂ hn

private theorem nthProcPos_append_right [DecidableEq P] {p : P} (H₁ H₂ : History P Op Resp) {n : ℕ}
    (hn : (procSubhistory H₁ p).length ≤ n) :
    nthProcPos p (H₁ ++ H₂) n =
      (nthProcPos p H₂ (n - (procSubhistory H₁ p).length)).map (· + H₁.length) := by
  rw [nthProcPos_eq_nthFilterPos, nthProcPos_eq_nthFilterPos]
  exact nthFilterPos_append_right H₁ H₂ hn

private theorem nthProcPos_of_append_lt [DecidableEq P] {p : P} {H₁ H₂ : History P Op Resp}
    {n pos : ℕ} (h : nthProcPos p (H₁ ++ H₂) n = some pos) (hlt : pos < H₁.length) :
    nthProcPos p H₁ n = some pos := by
  rw [nthProcPos_eq_nthFilterPos] at h ⊢
  exact nthFilterPos_of_append_lt h hlt

/-- Appending response events does not alter `<_H` on operations completed in `H ++ R`. -/
theorem prec_append_resp_iff [DecidableEq P] {H R : History P Op Resp}
    (hwf : WellFormed H) (hresp : IsRespList R) (hwf_ext : WellFormed (H ++ R))
    {e₀ e₁ : OpId P} (hc₁ : IsCompletedOp (H ++ R) e₁) :
    prec (H ++ R) e₀ e₁ ↔ prec H e₀ e₁ := by
  have hresp_p : ∀ p, IsRespList (procSubhistory R p) :=
    fun p e hm => hresp e (List.mem_filter.mp hm).1
  have hinv_in_H : 2 * e₁.idx < (procSubhistory H e₁.proc).length := by
    have hlen : 2 * e₁.idx + 1 < (procSubhistory (H ++ R) e₁.proc).length :=
      (isCompletedOp_iff_lt_length _ _).mp hc₁
    rw [procSubhistory_append, List.length_append] at hlen
    have hseq_p := hwf e₁.proc
    have hseq_ext := hwf_ext e₁.proc
    rw [procSubhistory_append] at hseq_ext
    rcases isRespList_le_one_of_isSequential hseq_p (hresp_p e₁.proc) hseq_ext with
      hnil | ⟨cs, q, x, op, res, _, hR⟩
    · rw [hnil, List.length_nil] at hlen; omega
    · rw [hR, List.length_singleton] at hlen; omega
  have hinv_eq : invPos (H ++ R) e₁ = invPos H e₁ :=
    nthProcPos_append_left R hinv_in_H
  constructor
  · rintro ⟨r, i, hr, hi, hri⟩
    rw [hinv_eq] at hi
    obtain ⟨hi_lt, _⟩ := nthProcPos_lt_length hi
    exact ⟨r, i, nthProcPos_of_append_lt hr (by omega), hi, hri⟩
  · rintro ⟨r, i, hr, hi, hri⟩
    have hr_in : 2 * e₀.idx + 1 < (procSubhistory H e₀.proc).length :=
      (nthProcPos_isSome_iff e₀.proc H (2 * e₀.idx + 1)).mp (by rw [← respPos, hr]; rfl)
    refine ⟨r, i, ?_, ?_, hri⟩
    · rw [respPos, nthProcPos_append_left R hr_in]; exact hr
    · rw [hinv_eq]; exact hi

end History

/-! ### Sequential specification, legality, linearizability, and sequential consistency -/

/-- A *sequential specification* for object `x : Obj` ([HerlihyWing1990], §2.1, p. 468): a
nonempty, prefix-closed set of single-object sequential histories on `x`. -/
structure SeqSpec (P : Type*) {Obj : Type*} (Op Resp : Obj → Type*) (x : Obj) where
  /-- Set of allowed single-object sequential histories for `x`. -/
  allowed : Set (History P Op Resp)
  /-- The empty history is allowed. -/
  nil_mem : [] ∈ allowed
  /-- Every allowed history contains only events for object `x`. -/
  obj_eq : ∀ {H}, H ∈ allowed → ∀ e ∈ H, e.obj = x
  /-- Every allowed history is sequential. -/
  isSequential : ∀ {H}, H ∈ allowed → History.IsSequential H
  /-- Prefix-closure ([HerlihyWing1990], §2.1, p. 468). -/
  prefix_closed : ∀ {H₁ H₂}, H₁ <+: H₂ → H₂ ∈ allowed → H₁ ∈ allowed

namespace SeqSpec

variable {P Obj : Type*} {Op Resp : Obj → Type*}

/-- Evaluate a single-object sequential history on `x` against a deterministic state machine
`(s, step)`, permitting an optional trailing pending invocation so the resulting set is event-wise
prefix-closed. -/
@[expose]
def evalMachine {State : Type*} (x : Obj) (step : State → Op x → State × Resp x) :
    State → History P Op Resp → Prop
  | _, [] => True
  | _, [.inv _ y _] => y = x
  | s, .inv p₁ y₁ op :: .resp p₂ y₂ res :: rest =>
    ∃ (hx₁ : y₁ = x) (hx₂ : y₂ = x),
      p₁ = p₂ ∧ (step s (hx₁ ▸ op)).2 = (hx₂ ▸ res) ∧
        evalMachine x step (step s (hx₁ ▸ op)).1 rest
  | _, _ => False

private theorem evalMachine_obj_eq {State : Type*} {x : Obj}
    {step : State → Op x → State × Resp x} {s : State} {H : History P Op Resp}
    (h : evalMachine x step s H) : ∀ e ∈ H, e.obj = x := by
  match H with
  | [] => intro _ hm; exact False.elim (List.not_mem_nil hm)
  | [.inv p y op] =>
    intro e hm
    simp only [List.mem_singleton] at hm
    subst hm
    exact h
  | [.resp _ _ _] => exact False.elim h
  | .inv _ _ _ :: .inv _ _ _ :: _ => exact False.elim h
  | .resp _ _ _ :: _ :: _ => exact False.elim h
  | .inv p₁ y₁ op :: .resp p₂ y₂ res :: rest =>
    obtain ⟨rfl, rfl, _, _, hrest⟩ := h
    intro e hm
    rcases List.mem_cons.mp hm with rfl | hm'
    · rfl
    · rcases List.mem_cons.mp hm' with rfl | hm''
      · rfl
      · exact evalMachine_obj_eq hrest e hm''

private theorem evalMachine_isSequential {State : Type*} {x : Obj}
    {step : State → Op x → State × Resp x} {s : State} {H : History P Op Resp}
    (h : evalMachine x step s H) : History.IsSequential H := by
  match H with
  | [] => trivial
  | [.inv _ _ _] => trivial
  | [.resp _ _ _] => exact False.elim h
  | .inv _ _ _ :: .inv _ _ _ :: _ => exact False.elim h
  | .resp _ _ _ :: _ :: _ => exact False.elim h
  | .inv p₁ y₁ op :: .resp p₂ y₂ res :: rest =>
    obtain ⟨rfl, rfl, hp, _, hrest⟩ := h
    exact ⟨hp, rfl, evalMachine_isSequential hrest⟩

private theorem evalMachine_prefix_closed {State : Type*} {x : Obj}
    {step : State → Op x → State × Resp x} {s : State} {H₁ H₂ : History P Op Resp}
    (hpre : H₁ <+: H₂) (h : evalMachine x step s H₂) : evalMachine x step s H₁ := by
  match H₁ with
  | [] => trivial
  | [e₁] =>
    obtain ⟨t, rfl⟩ := hpre
    cases e₁ with
    | resp _ _ _ =>
      cases t <;> exact False.elim h
    | inv p y op =>
      cases t with
      | nil => exact h
      | cons e₂ rest =>
        cases e₂ with
        | inv _ _ _ => exact False.elim h
        | resp p₂ y₂ res =>
          obtain ⟨hx₁, _, _⟩ := h
          exact hx₁
  | e₁ :: e₂ :: rest₁ =>
    obtain ⟨t, ht⟩ := hpre
    simp only [List.cons_append] at ht
    cases H₂ with
    | nil => nomatch ht
    | cons a tail =>
      injection ht with ha htail
      subst ha
      cases tail with
      | nil => nomatch htail
      | cons b rest₂ =>
        injection htail with hb hrest
        subst hb
        cases e₁ with
        | resp _ _ _ => exact False.elim h
        | inv p₁ y₁ op =>
          cases e₂ with
          | inv _ _ _ => exact False.elim h
          | resp p₂ y₂ res =>
            obtain ⟨rfl, rfl, hp, hres, hrest₂⟩ := h
            exact ⟨rfl, rfl, hp, hres, evalMachine_prefix_closed ⟨t, hrest⟩ hrest₂⟩

/-- Construct a `SeqSpec` for object `x` from a deterministic sequential state machine
`(init, step)`. -/
def ofMachine {State : Type*} (x : Obj) (init : State)
    (step : State → Op x → State × Resp x) : SeqSpec P Op Resp x where
  allowed := { H | evalMachine x step init H }
  nil_mem := trivial
  obj_eq := evalMachine_obj_eq
  isSequential := evalMachine_isSequential
  prefix_closed := evalMachine_prefix_closed

@[simp]
theorem mem_ofMachine_allowed {State : Type*} (x : Obj) (init : State)
    (step : State → Op x → State × Resp x) (H : History P Op Resp) :
    H ∈ (ofMachine x init step).allowed ↔ evalMachine x step init H :=
  Iff.rfl

/-- An operation `op : Op x` is *total* for `spec` ([HerlihyWing1990], §2.1, p. 468 & §3.2,
Theorem 2, p. 471) if every complete legal history of `x` can be extended by `op` for any invoking
process `p` with some valid response `res`. -/
@[expose]
def IsTotalOp {x : Obj} (spec : SeqSpec P Op Resp x) (op : Op x) : Prop :=
  ∀ S : History P Op Resp, S ∈ spec.allowed → S.length % 2 = 0 →
    ∀ p : P, ∃ res : Resp x, S ++ [.inv p x op, .resp p x res] ∈ spec.allowed

private theorem evalMachine_append_pair {State : Type*} (x : Obj)
    (step : State → Op x → State × Resp x) (op : Op x) (p : P) :
    ∀ (st : State) (L : History P Op Resp), evalMachine x step st L → L.length % 2 = 0 →
      ∃ res : Resp x, evalMachine x step st (L ++ [.inv p x op, .resp p x res])
  | st, [], _, _ => ⟨(step st op).2, rfl, rfl, rfl, rfl, trivial⟩
  | _, [.inv _ _ _], _, hev => by simp only [List.length_singleton] at hev; omega
  | _, [.resp _ _ _], hL, _ => False.elim hL
  | _, .inv _ _ _ :: .inv _ _ _ :: _, hL, _ => False.elim hL
  | _, .resp _ _ _ :: _ :: _, hL, _ => False.elim hL
  | st, .inv p₁ y₁ op₁ :: .resp p₂ y₂ res₁ :: rest, hL, hev => by
    obtain ⟨hx₁, hx₂, hp, hres₁, hrest⟩ := hL
    cases hx₁; cases hx₂
    simp only [List.length_cons] at hev
    obtain ⟨res, hres⟩ := evalMachine_append_pair _ step op p (step st op₁).1 rest hrest (by omega)
    exact ⟨res, rfl, rfl, hp, hres₁, hres⟩

theorem isTotalOp_ofMachine {State : Type*} (x : Obj) (init : State)
    (step : State → Op x → State × Resp x) (op : Op x) :
    (ofMachine (P := P) (Resp := Resp) x init step).IsTotalOp op :=
  fun S hS hev p => evalMachine_append_pair x step op p init S hS hev

end SeqSpec

/-- A sequential history `S` is *legal* with respect to `spec` if for every object `x`,
`History.objSubhistory S x` belongs to `(spec x).allowed` ([HerlihyWing1990], §2.1, p. 468). -/
@[expose]
def History.IsLegal {P Obj : Type*} {Op Resp : Obj → Type*} [DecidableEq Obj]
    (spec : ∀ x, SeqSpec P Op Resp x) (S : History P Op Resp) : Prop :=
  ∀ x, History.objSubhistory S x ∈ (spec x).allowed

/-- **Linearizability** ([HerlihyWing1990], §2.2, p. 469, with the amended L2 condition of
[SelaHerlihyPetrank2021], §4, Definition 4.1, p. 6): history `H` can be extended by appending zero
or more responses to a well-formed history `H'` such that:
* **L1:** `complete(H')` is equivalent to some legal sequential history `S`, and
* **L2:** real-time precedence `<_H` (`History.prec H`) on all operations completed in `H'`
  (`History.IsCompletedOp H'`, equivalently `<_{H'} ⊆ <_S` by `History.prec_append_resp_iff`) is
  preserved by `<_S`.

Unlike the literal printed L2 in [HerlihyWing1990] (which restricts `<_H` to operations already
completed in `H` and fails locality and nonblocking; see [SelaHerlihyPetrank2021], §§3.2–3.3,
pp. 5–6), `History.prec H e₀ e₁` sees invocations `e₁` pending in `H` and `IsLinearizable` enforces
precedence across all operations completed in the extension `H'`. -/
@[expose]
def IsLinearizable {P Obj : Type*} {Op Resp : Obj → Type*} [DecidableEq P] [DecidableEq Obj]
    (spec : ∀ x, SeqSpec P Op Resp x) (H : History P Op Resp) : Prop :=
  ∃ H' : History P Op Resp, History.IsExtension H H' ∧
    ∃ S : History P Op Resp, History.IsSequential S ∧ History.IsLegal spec S ∧
      History.Equivalent (History.complete H') S ∧
      ∀ e₀ e₁, History.IsCompletedOp H' e₀ → History.IsCompletedOp H' e₁ →
        History.prec H e₀ e₁ → History.prec S e₀ e₁

/-- **Sequential consistency** (extending [HerlihyWing1990], §3.3, p. 472 to incomplete histories
via `History.IsExtension` and `History.complete` in parallel with `IsLinearizable`, coinciding with
§3.3 on complete histories): history `H` can be extended by appending zero or more responses to a
well-formed history `H'` such that `complete(H')` is equivalent to some legal sequential history `S`
(preserving per-process program order without requiring cross-process real-time precedence
`<_H ⊆ <_S`). -/
@[expose]
def IsSequentiallyConsistent {P Obj : Type*} {Op Resp : Obj → Type*}
    [DecidableEq P] [DecidableEq Obj]
    (spec : ∀ x, SeqSpec P Op Resp x) (H : History P Op Resp) : Prop :=
  ∃ H' : History P Op Resp, History.IsExtension H H' ∧
    ∃ S : History P Op Resp, History.IsSequential S ∧ History.IsLegal spec S ∧
      History.Equivalent (History.complete H') S

/-- Every linearizable history is sequentially consistent (after [HerlihyWing1990], §3.3,
p. 472). -/
theorem IsLinearizable.isSequentiallyConsistent {P Obj : Type*} {Op Resp : Obj → Type*}
    [DecidableEq P] [DecidableEq Obj] {spec : ∀ x, SeqSpec P Op Resp x}
    {H : History P Op Resp} (h : IsLinearizable spec H) :
    IsSequentiallyConsistent spec H := by
  obtain ⟨H', hExt, S, hSeq, hLeg, hEq, _⟩ := h
  exact ⟨H', hExt, S, hSeq, hLeg, hEq⟩

/-! ### Interval-order acyclicity and finite topological sort -/

/-- **Algebraic interval-order cycle collapse** (core of [HerlihyWing1990], §3.1, Theorem 1,
p. 471): if `rt` is a `Relation.IsIntervalOrder` on `α`, `loc` only relates elements of the same
object (`obj a = obj b`), `loc` is a strict order (irreflexive and transitive), and `rt` restricted
to same-object pairs is contained in `loc`, then `loc ⊔ rt` is `Relation.Acyclic`. -/
theorem acyclic_sup_of_isIntervalOrder {α Obj : Type*} (obj : α → Obj)
    (loc rt : α → α → Prop)
    (hrt : IsIntervalOrder rt)
    (hloc_irrefl : ∀ a, ¬ loc a a)
    (hloc_trans : ∀ {a b c}, loc a b → loc b c → loc a c)
    (hloc_obj : ∀ {a b}, loc a b → obj a = obj b)
    (hrt_sub_loc : ∀ {a b}, obj a = obj b → rt a b → loc a b) :
    Acyclic (loc ⊔ rt) := by
  have hmid : ∀ {a b c d}, rt a b → loc b c → rt c d → rt a d := by
    intro a b c d hab hbc hcd
    rcases hrt.2 a b c d ⟨hab, hcd⟩ with had | hcb
    · exact had
    · exfalso
      have hcb_loc : loc c b := hrt_sub_loc (hloc_obj hbc).symm hcb
      exact hloc_irrefl b (hloc_trans hbc hcb_loc)
  have hrefl_trans : ∀ {a b c}, ReflGen loc a b → ReflGen loc b c → ReflGen loc a c := by
    intro a b c h₁ h₂
    cases h₁ with
    | refl => exact h₂
    | single h₁ =>
      cases h₂ with
      | refl => exact ReflGen.single h₁
      | single h₂ => exact ReflGen.single (hloc_trans h₁ h₂)
  have hcollapse : ∀ {x y}, TransGen (loc ⊔ rt) x y →
      loc x y ∨ ∃ u v, ReflGen loc x u ∧ rt u v ∧ ReflGen loc v y := by
    intro x y hxy
    induction hxy with
    | single hstep =>
      rcases hstep with hl | hr
      · exact Or.inl hl
      · exact Or.inr ⟨x, _, ReflGen.refl, hr, ReflGen.refl⟩
    | tail _ hstep ih =>
      rcases ih with hl | ⟨u, v, hxu, huv, hvy⟩
      · rcases hstep with hl₂ | hr₂
        · exact Or.inl (hloc_trans hl hl₂)
        · exact Or.inr ⟨_, _, ReflGen.single hl, hr₂, ReflGen.refl⟩
      · rcases hstep with hl₂ | hr₂
        · exact Or.inr ⟨u, v, hxu, huv, hrefl_trans hvy (ReflGen.single hl₂)⟩
        · cases hvy with
          | refl =>
            exact Or.inr ⟨u, _, hxu, hrt.1.trans _ _ _ huv hr₂, ReflGen.refl⟩
          | single hv =>
            exact Or.inr ⟨u, _, hxu, hmid huv hv hr₂, ReflGen.refl⟩
  refine ⟨fun x hxx => ?_⟩
  rcases hcollapse hxx with hl | ⟨u, v, hxu, huv, hvx⟩
  · exact hloc_irrefl x hl
  · cases hrefl_trans hvx hxu with
    | refl => exact hrt.1.irrefl u huv
    | single hvu =>
      have huv_loc : loc u v := hrt_sub_loc (hloc_obj hvu).symm huv
      exact hloc_irrefl v (hloc_trans hvu huv_loc)

private theorem filter_length_lt_of_imp_of_witness {α : Type*} (l : List α)
    (p q : α → Bool) (himp : ∀ x ∈ l, p x = true → q x = true)
    {w : α} (hw : w ∈ l) (hpw : p w = false) (hqw : q w = true) :
    (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => exact False.elim (List.not_mem_nil hw)
  | cons a rest ih =>
    have hle : ∀ m : List α, (∀ x ∈ m, p x = true → q x = true) →
        (m.filter p).length ≤ (m.filter q).length := by
      intro m hm
      induction m with
      | nil => exact Nat.le_refl 0
      | cons b bs ihb =>
        simp only [List.filter]
        have ih' := ihb (fun x hx => hm x (List.mem_cons_of_mem _ hx))
        cases hpb : p b
        · cases hqb : q b <;> simp only [List.length_cons] <;> omega
        · rw [hm b List.mem_cons_self hpb]
          simp only [List.length_cons]
          omega
    rcases List.mem_cons.mp hw with rfl | hw'
    · simp only [List.filter, hpw, hqw]
      have hrest := hle rest (fun x hx => himp x (List.mem_cons_of_mem _ hx))
      simp only [List.length_cons]
      omega
    · have ih' := ih (fun x hx => himp x (List.mem_cons_of_mem _ hx)) hw'
      simp only [List.filter]
      cases hpa : p a
      · cases hqa : q a <;> simp only [List.length_cons] <;> omega
      · rw [himp a List.mem_cons_self hpa]
        simp only [List.length_cons]
        omega

private theorem exists_minimal_of_acyclic {α : Type*} (R : α → α → Prop) (hacyc : Acyclic R)
    {elems : List α} (hne : elems ≠ []) :
    ∃ m ∈ elems, ∀ x ∈ elems, ¬ TransGen R x m := by
  classical
  let ancCount (y : α) : ℕ := (elems.filter fun x => decide (TransGen R x y)).length
  have findMin : ∀ (k : ℕ) (y : α), y ∈ elems → ancCount y ≤ k →
      ∃ m ∈ elems, ∀ x ∈ elems, ¬ TransGen R x m := by
    intro k
    induction k with
    | zero =>
      intro y hy h0
      refine ⟨y, hy, fun x hx hxy => ?_⟩
      have hpos : 0 < ancCount y := by
        have : x ∈ elems.filter fun z => decide (TransGen R z y) :=
          List.mem_filter.mpr ⟨hx, decide_eq_true hxy⟩
        exact List.length_pos_of_mem this
      omega
    | succ k ih =>
      intro y hy hk
      by_cases hmin : ∀ x ∈ elems, ¬ TransGen R x y
      · exact ⟨y, hy, hmin⟩
      · push Not at hmin
        obtain ⟨x, hx, hxy⟩ := hmin
        have hlt : ancCount x < ancCount y := by
          refine filter_length_lt_of_imp_of_witness elems
            (fun z => decide (TransGen R z x))
            (fun z => decide (TransGen R z y))
            (fun z _ hz => decide_eq_true ((decide_eq_true_eq.mp hz).trans hxy))
            hx
            (decide_eq_false_iff_not.mpr (hacyc.irrefl x))
            (decide_eq_true hxy)
        exact ih x hx (by omega)
  obtain ⟨y₀, hy₀⟩ := List.exists_mem_of_ne_nil elems hne
  exact findMin (ancCount y₀) y₀ hy₀ (Nat.le_refl _)

/-- Finite topological sort: every duplicate-free list `elems` over an acyclic relation `R` admits a
permutation `order` in which every `R`-edge points strictly forward. -/
private theorem exists_topoSort_of_acyclic {α : Type*} {R : α → α → Prop}
    (hacyc : Acyclic R) {elems : List α} (hnodup : elems.Nodup) :
    ∃ order : List α, order.Perm elems ∧ order.Nodup ∧
      ∀ i j (hi : i < order.length) (hj : j < order.length),
        TransGen R order[i] order[j] → i < j := by
  classical
  have go : ∀ n (l : List α), l.length = n → l.Nodup →
      ∃ order : List α, order.Perm l ∧ order.Nodup ∧
        ∀ i j (hi : i < order.length) (hj : j < order.length),
          TransGen R order[i] order[j] → i < j := by
    intro n
    induction n with
    | zero =>
      intro l hl _
      rw [List.length_eq_zero_iff.mp hl]
      exact ⟨[], List.Perm.nil, List.nodup_nil,
        fun _ _ hi => by simp only [List.length_nil] at hi; omega⟩
    | succ n ih =>
      intro l hl hnd
      have hne : l ≠ [] := by intro h; rw [h, List.length_nil] at hl; omega
      obtain ⟨m, hm, hmin⟩ := exists_minimal_of_acyclic R hacyc hne
      have hlen' : (l.erase m).length = n := by
        rw [List.length_erase_of_mem hm, hl]; omega
      obtain ⟨order', hperm', hnd', hord'⟩ := ih (l.erase m) hlen' (hnd.erase m)
      have hm_not : m ∉ order' := by
        intro hmem
        have hmem_er : m ∈ l.erase m := hperm'.subset hmem
        exact hnd.not_mem_erase hmem_er
      refine ⟨m :: order', (hperm'.cons m).trans (List.perm_cons_erase hm).symm,
        List.nodup_cons.mpr ⟨hm_not, hnd'⟩, ?_⟩
      intro i j hi hj hrel
      cases j with
      | zero =>
        exfalso
        simp only [List.getElem_cons_zero] at hrel
        have hmem_i : (m :: order')[i] ∈ l :=
          ((hperm'.cons m).trans (List.perm_cons_erase hm).symm).subset (List.getElem_mem hi)
        exact hmin _ hmem_i hrel
      | succ j' =>
        cases i with
        | zero => omega
        | succ i' =>
          simp only [List.length_cons] at hi hj
          simp only [List.getElem_cons_succ] at hrel
          have := hord' i' j' (by omega) (by omega) hrel
          omega
  exact go elems.length elems rfl hnodup

/-! ### Sequential call indexing and object-subhistory operation lifting -/

section LocalityInfrastructure

variable {P Obj : Type*} {Op Resp : Obj → Type*}

private def countProcCalls [DecidableEq P] (p : P) (calls : List (OpCall P Op Resp)) : ℕ :=
  (calls.filter fun c => decide (c.proc = p)).length

private theorem countProcCalls_nil [DecidableEq P] (p : P) :
    countProcCalls p ([] : List (OpCall P Op Resp)) = 0 :=
  rfl

private theorem countProcCalls_cons [DecidableEq P] (p : P) (c : OpCall P Op Resp)
    (rest : List (OpCall P Op Resp)) :
    countProcCalls p (c :: rest) =
      if c.proc = p then countProcCalls p rest + 1 else countProcCalls p rest := by
  simp only [countProcCalls, List.filter]
  by_cases h : c.proc = p <;> simp only [h, decide_true, decide_false, ↓reduceIte, List.length_cons]

private def opIdAt [DecidableEq P] (calls : List (OpCall P Op Resp)) (j : ℕ)
    (hj : j < calls.length) : OpId P :=
  ⟨calls[j].proc, countProcCalls calls[j].proc (calls.take j)⟩

private theorem nthFilterPos_flatMap_toEvents (pred : OpCall P Op Resp → Bool)
    (evPred : Event P Op Resp → Bool)
    (hinv_p : ∀ c : OpCall P Op Resp, evPred (.inv c.proc c.obj c.op) = pred c)
    (hresp_p : ∀ c : OpCall P Op Resp, evPred (.resp c.proc c.obj c.res) = pred c)
    (calls : List (OpCall P Op Resp)) (k : ℕ) (hk : k < calls.length)
    (hpk : pred calls[k] = true) :
    History.nthFilterPos evPred (calls.flatMap OpCall.toEvents)
        (2 * ((calls.take k).filter pred).length) = some (2 * k) ∧
      History.nthFilterPos evPred (calls.flatMap OpCall.toEvents)
        (2 * ((calls.take k).filter pred).length + 1) = some (2 * k + 1) := by
  induction calls generalizing k with
  | nil => simp only [List.length_nil] at hk; omega
  | cons c rest ih =>
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero] at hpk
      simp only [List.take_zero, List.filter_nil, List.length_nil, Nat.mul_zero, Nat.zero_add,
        List.flatMap_cons, OpCall.toEvents, List.cons_append, List.nil_append,
        History.nthFilterPos, hinv_p, hresp_p, hpk, ↓reduceIte, Option.map_some, and_self]
    | succ k' =>
      have hk' : k' < rest.length := by simp only [List.length_cons] at hk; omega
      simp only [List.getElem_cons_succ] at hpk
      obtain ⟨hinv, hresp⟩ := ih k' hk' hpk
      simp only [List.take_succ_cons, List.flatMap_cons, OpCall.toEvents, List.cons_append,
        List.nil_append]
      cases hpc : pred c
      · have hpc_ne : ¬ pred c = true := by simp only [hpc, Bool.false_eq_true, not_false_eq_true]
        simp only [List.filter_cons_of_neg hpc_ne]
        cases hk₁ : 2 * ((rest.take k').filter pred).length with
        | zero =>
          rw [hk₁] at hinv
          have hk₂ : 2 * ((rest.take k').filter pred).length + 1 = 1 := by omega
          rw [hk₂] at hresp
          simp only [Nat.zero_add, History.nthFilterPos, hinv_p, hresp_p, hpc,
            Bool.false_eq_true, ↓reduceIte, hinv, hresp, Option.map_some]
          exact ⟨congrArg some (by omega), congrArg some (by omega)⟩
        | succ m =>
          rw [hk₁] at hinv
          have hk₂ : 2 * ((rest.take k').filter pred).length + 1 = m + 1 + 1 := by omega
          rw [hk₂] at hresp
          simp only [History.nthFilterPos, hinv_p, hresp_p, hpc, Bool.false_eq_true,
            ↓reduceIte, hinv, hresp, Option.map_some]
          exact ⟨congrArg some (by omega), congrArg some (by omega)⟩
      · simp only [List.filter_cons_of_pos hpc, List.length_cons]
        have heq₁ : 2 * (((rest.take k').filter pred).length + 1) =
            2 * ((rest.take k').filter pred).length + 1 + 1 := by omega
        rw [heq₁]
        simp only [History.nthFilterPos, hinv_p, hresp_p, hpc, ↓reduceIte, hinv, hresp,
          Option.map_some]
        exact ⟨congrArg some (by omega), congrArg some (by omega)⟩

private theorem invPos_respPos_opIdAt [DecidableEq P] (calls : List (OpCall P Op Resp))
    (j : ℕ) (hj : j < calls.length) :
    History.invPos (calls.flatMap OpCall.toEvents) (opIdAt calls j hj) = some (2 * j) ∧
      History.respPos (calls.flatMap OpCall.toEvents) (opIdAt calls j hj) = some (2 * j + 1) := by
  simp only [History.invPos, History.respPos, opIdAt, countProcCalls,
    History.nthProcPos_eq_nthFilterPos]
  exact nthFilterPos_flatMap_toEvents
    (fun c => decide (c.proc = calls[j].proc))
    (fun e => decide (e.proc = calls[j].proc))
    (fun _ => rfl) (fun _ => rfl) calls j hj (decide_eq_true rfl)

private theorem opIdAt_injective [DecidableEq P] {calls : List (OpCall P Op Resp)}
    {j₁ j₂ : ℕ} (hj₁ : j₁ < calls.length) (hj₂ : j₂ < calls.length)
    (heq : opIdAt calls j₁ hj₁ = opIdAt calls j₂ hj₂) : j₁ = j₂ := by
  have h₁ := (invPos_respPos_opIdAt calls j₁ hj₁).1
  have h₂ := (invPos_respPos_opIdAt calls j₂ hj₂).1
  rw [heq] at h₁
  rw [h₁] at h₂
  injection h₂ with h; omega

private theorem prec_flatMap_toEvents_opIdAt_iff [DecidableEq P]
    (calls : List (OpCall P Op Resp)) {j₁ j₂ : ℕ}
    (hj₁ : j₁ < calls.length) (hj₂ : j₂ < calls.length) :
    History.prec (calls.flatMap OpCall.toEvents)
      (opIdAt calls j₁ hj₁) (opIdAt calls j₂ hj₂) ↔ j₁ < j₂ := by
  obtain ⟨_, hr₁⟩ := invPos_respPos_opIdAt calls j₁ hj₁
  obtain ⟨hi₂, _⟩ := invPos_respPos_opIdAt calls j₂ hj₂
  constructor
  · rintro ⟨r, i, hr, hi, hlt⟩
    rw [hr₁] at hr; rw [hi₂] at hi
    injection hr with hr'; injection hi with hi'
    omega
  · intro hlt
    exact ⟨2 * j₁ + 1, 2 * j₂, hr₁, hi₂, by omega⟩

private theorem exists_opIdAt_of_lt_countProcCalls [DecidableEq P]
    (calls : List (OpCall P Op Resp)) (e : OpId P) (hlt : e.idx < countProcCalls e.proc calls) :
    ∃ (j : ℕ) (hj : j < calls.length), opIdAt calls j hj = e := by
  induction calls generalizing e with
  | nil => simp only [countProcCalls_nil] at hlt; omega
  | cons c rest ih =>
    rw [countProcCalls_cons] at hlt
    by_cases hcp : c.proc = e.proc
    · simp only [hcp, ↓reduceIte] at hlt
      cases hidx : e.idx with
      | zero =>
        refine ⟨0, Nat.zero_lt_succ _, ?_⟩
        ext
        · exact hcp
        · simp only [opIdAt, List.take_zero, countProcCalls_nil, hidx]
      | succ k =>
        rw [hidx] at hlt
        obtain ⟨j', hj', heq⟩ := ih ⟨e.proc, k⟩ (by dsimp only; omega)
        refine ⟨j' + 1, Nat.succ_lt_succ hj', ?_⟩
        have hproc : rest[j'].proc = e.proc := by
          have := congrArg OpId.proc heq
          simpa only [opIdAt] using this
        have hcnt : countProcCalls rest[j'].proc (rest.take j') = k := by
          have := congrArg OpId.idx heq
          simpa only [opIdAt] using this
        ext
        · simp only [opIdAt, List.getElem_cons_succ, hproc]
        · simp only [opIdAt, List.getElem_cons_succ, List.take_succ_cons, countProcCalls_cons,
            hproc, hcp, ↓reduceIte, hidx]
          rw [← hproc, hcnt]
    · simp only [hcp, ↓reduceIte] at hlt
      obtain ⟨j', hj', heq⟩ := ih e hlt
      refine ⟨j' + 1, Nat.succ_lt_succ hj', ?_⟩
      have hproc : rest[j'].proc = e.proc := by
        have := congrArg OpId.proc heq
        simpa only [opIdAt] using this
      have hcnt : countProcCalls rest[j'].proc (rest.take j') = e.idx := by
        have := congrArg OpId.idx heq
        simpa only [opIdAt] using this
      ext
      · simp only [opIdAt, List.getElem_cons_succ, hproc]
      · simp only [opIdAt, List.getElem_cons_succ, List.take_succ_cons, countProcCalls_cons,
          hproc, hcp, ↓reduceIte]
        rw [← hproc, hcnt]

private theorem prec_strictTotal_of_isSequential_even [DecidableEq P] {S : History P Op Resp}
    (hseq : History.IsSequential S) (heven : S.length % 2 = 0)
    {e₁ e₂ : OpId P} (hc₁ : History.IsCompletedOp S e₁) (hc₂ : History.IsCompletedOp S e₂)
    (hne : e₁ ≠ e₂) : History.prec S e₁ e₂ ∨ History.prec S e₂ e₁ := by
  obtain ⟨calls, rfl⟩ := History.exists_calls_of_isSequential_even hseq heven
  have hlt₁ : e₁.idx < countProcCalls e₁.proc calls := by
    have h := (History.isCompletedOp_iff_lt_length _ e₁).mp hc₁
    rw [History.procSubhistory_flatMap_toEvents, History.length_flatMap_toEvents] at h
    simp only [countProcCalls]; omega
  have hlt₂ : e₂.idx < countProcCalls e₂.proc calls := by
    have h := (History.isCompletedOp_iff_lt_length _ e₂).mp hc₂
    rw [History.procSubhistory_flatMap_toEvents, History.length_flatMap_toEvents] at h
    simp only [countProcCalls]; omega
  obtain ⟨j₁, hj₁, rfl⟩ := exists_opIdAt_of_lt_countProcCalls calls e₁ hlt₁
  obtain ⟨j₂, hj₂, rfl⟩ := exists_opIdAt_of_lt_countProcCalls calls e₂ hlt₂
  have hjne : j₁ ≠ j₂ := fun h => by subst h; exact hne rfl
  rcases Nat.lt_or_gt_of_ne hjne with h₁₂ | h₂₁
  · exact Or.inl ((prec_flatMap_toEvents_opIdAt_iff calls hj₁ hj₂).mpr h₁₂)
  · exact Or.inr ((prec_flatMap_toEvents_opIdAt_iff calls hj₂ hj₁).mpr h₂₁)

/-- Position in `L` of the `n`-th event whose object is `x`. -/
private def nthObjPos [DecidableEq Obj] (x : Obj) (L : History P Op Resp) (n : ℕ) : Option ℕ :=
  History.nthFilterPos (fun e => decide (e.obj = x)) L n

/-- Number of events on object `x` strictly preceding index `pos` in `M`. -/
private def objProjPos [DecidableEq Obj] (x : Obj) : History P Op Resp → ℕ → ℕ
  | [], _ => 0
  | _, 0 => 0
  | e :: rest, pos + 1 =>
    if e.obj = x then objProjPos x rest pos + 1 else objProjPos x rest pos

private theorem objProjPos_lt_iff [DecidableEq Obj] (x : Obj) :
    ∀ {M : History P Op Resp} {pos₁ pos₂ : ℕ},
      pos₁ < M.length → pos₂ < M.length → M[pos₁]?.map Event.obj = some x →
      (objProjPos x M pos₁ < objProjPos x M pos₂ ↔ pos₁ < pos₂)
  | [], _, _, h₁, _, _ => by simp only [List.length_nil] at h₁; omega
  | e :: rest, 0, 0, _, _, _ => by simp only [objProjPos, Nat.lt_irrefl]
  | e :: rest, 0, p₂ + 1, _, _, hobj => by
    simp only [List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at hobj
    simp only [objProjPos, hobj, ↓reduceIte]
    omega
  | e :: rest, p₁ + 1, 0, _, _, _ => by simp only [objProjPos]; omega
  | e :: rest, p₁ + 1, p₂ + 1, h₁, h₂, hobj => by
    simp only [List.length_cons] at h₁ h₂
    simp only [List.getElem?_cons_succ] at hobj
    have ih := objProjPos_lt_iff x (pos₁ := p₁) (pos₂ := p₂) (by omega) (by omega) hobj
    simp only [objProjPos]
    by_cases hex : e.obj = x <;> simp only [hex, ↓reduceIte] <;> omega

private theorem nthObjPos_isSome_iff [DecidableEq Obj] (x : Obj) (L : History P Op Resp) (n : ℕ) :
    (nthObjPos x L n).isSome = true ↔ n < (History.objSubhistory L x).length :=
  History.nthFilterPos_isSome_iff (fun e : Event P Op Resp => decide (e.obj = x)) L n

private theorem nthObjPos_lt_length [DecidableEq Obj] {x : Obj} {L : History P Op Resp}
    {n m : ℕ} (h : nthObjPos x L n = some m) : m < L.length ∧ L[m]?.map Event.obj = some x := by
  obtain ⟨hlt, _, hpr⟩ := History.nthFilterPos_lt_length h
  exact ⟨hlt, History.map_eq_some_of_map_decide hpr⟩

private theorem nthObjPos_pair_of_isSequential [DecidableEq Obj] {x : Obj}
    {L : History P Op Resp} (hseq : History.IsSequential L) {k_x m : ℕ}
    (h : nthObjPos x L (2 * k_x + 1) = some m) :
    ∃ k : ℕ, m = 2 * k + 1 ∧ nthObjPos x L (2 * k_x) = some (2 * k) := by
  match L with
  | [] => simp only [nthObjPos, History.nthFilterPos, reduceCtorEq] at h
  | [.inv p y op] =>
    simp only [nthObjPos, History.nthFilterPos, decide_eq_true_eq] at h
    by_cases hyx : y = x <;>
      simp only [Event.obj_inv, hyx, ↓reduceIte, Option.map_none, reduceCtorEq] at h
  | [.resp _ _ _] => exact False.elim hseq
  | .inv _ _ _ :: .inv _ _ _ :: _ => exact False.elim hseq
  | .resp _ _ _ :: _ :: _ => exact False.elim hseq
  | .inv p₁ x₁ op :: .resp p₂ x₂ res :: rest =>
    obtain ⟨hp, hx, hrest⟩ := hseq
    subst hp hx
    by_cases hxx : x₁ = x
    · cases k_x with
      | zero =>
        simp only [Nat.zero_add, nthObjPos, History.nthFilterPos, decide_eq_true_eq, Event.obj_inv,
          Event.obj_resp, hxx, ↓reduceIte, Option.map_some, Option.some.injEq] at h ⊢
        exact ⟨0, h.symm, rfl⟩
      | succ k_x' =>
        have hstep₁ : 2 * (k_x' + 1) + 1 = (2 * k_x' + 1) + 1 + 1 := by omega
        have hstep₀ : 2 * (k_x' + 1) = (2 * k_x') + 1 + 1 := by omega
        rw [hstep₁] at h
        simp only [nthObjPos, History.nthFilterPos, decide_eq_true_eq, Event.obj_inv,
          Event.obj_resp, hxx, ↓reduceIte, Option.map_eq_some_iff] at h
        obtain ⟨m₁, ⟨m', hm', rfl⟩, rfl⟩ := h
        obtain ⟨k', rfl, hk₀⟩ := nthObjPos_pair_of_isSequential hrest hm'
        refine ⟨k' + 1, by omega, ?_⟩
        rw [hstep₀]
        simp only [nthObjPos, History.nthFilterPos, decide_eq_true_eq, Event.obj_inv,
          Event.obj_resp, hxx, ↓reduceIte]
        rw [← nthObjPos, hk₀, Option.map_some, Option.map_some]
        exact congrArg some (by omega)
    · simp only [nthObjPos, History.nthFilterPos, decide_eq_true_eq, Event.obj_inv, Event.obj_resp,
        hxx, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨m₁, ⟨m', hm', rfl⟩, rfl⟩ := h
      obtain ⟨k', rfl, hk₀⟩ := nthObjPos_pair_of_isSequential hrest hm'
      refine ⟨k' + 1, by omega, ?_⟩
      cases h2 : 2 * k_x with
      | zero =>
        rw [h2] at hk₀
        simp only [nthObjPos, History.nthFilterPos, decide_eq_true_eq, Event.obj_inv,
          Event.obj_resp, hxx, ↓reduceIte]
        rw [← nthObjPos, hk₀, Option.map_some, Option.map_some]
        exact congrArg some (by omega)
      | succ u =>
        rw [h2] at hk₀
        simp only [nthObjPos, History.nthFilterPos, decide_eq_true_eq, Event.obj_inv,
          Event.obj_resp, hxx, ↓reduceIte]
        rw [← nthObjPos, hk₀, Option.map_some, Option.map_some]
        exact congrArg some (by omega)

private theorem nthObjPos_complete_eq [DecidableEq P] [DecidableEq Obj] {x : Obj}
    {L : History P Op Resp} (hseq : History.IsSequential L) {n m : ℕ}
    (h : nthObjPos x (History.complete L) n = some m) :
    nthObjPos x L n = some m := by
  match L with
  | [] => exact h
  | [.inv p y op] =>
    simp only [History.complete, List.any_nil, Bool.false_eq_true, ↓reduceIte, nthObjPos,
      History.nthFilterPos, reduceCtorEq] at h
  | [.resp _ _ _] => exact False.elim hseq
  | .inv _ _ _ :: .inv _ _ _ :: _ => exact False.elim hseq
  | .resp _ _ _ :: _ :: _ => exact False.elim hseq
  | .inv p₁ x₁ op :: .resp p₂ x₂ res :: rest =>
    obtain ⟨hp, hx, hrest⟩ := hseq
    subst hp hx
    have hany : ((Event.resp p₁ x₁ res :: rest).any fun e => decide (e.proc = p₁)) = true := by
      simp only [List.any_cons, Event.proc_resp, decide_true, Bool.true_or]
    simp only [History.complete, hany, ↓reduceIte] at h
    by_cases hxx : x₁ = x
    · cases n with
      | zero =>
        simp only [nthObjPos, History.nthFilterPos, decide_eq_true_eq, Event.obj_inv, hxx,
          ↓reduceIte] at h ⊢
        exact h
      | succ n₁ =>
        cases n₁ with
        | zero =>
          simp only [nthObjPos, History.nthFilterPos, decide_eq_true_eq, Event.obj_inv,
            Event.obj_resp, hxx, ↓reduceIte] at h ⊢
          exact h
        | succ n₂ =>
          simp only [nthObjPos, History.nthFilterPos, decide_eq_true_eq, Event.obj_inv,
            Event.obj_resp, hxx, ↓reduceIte, Option.map_eq_some_iff] at h ⊢
          obtain ⟨m₁, ⟨m₂, hm₂, rfl⟩, rfl⟩ := h
          exact ⟨m₂ + 1, ⟨m₂, nthObjPos_complete_eq hrest hm₂, rfl⟩, rfl⟩
    · cases n with
      | zero =>
        simp only [nthObjPos, History.nthFilterPos, decide_eq_true_eq, Event.obj_inv,
          Event.obj_resp, hxx, ↓reduceIte, Option.map_eq_some_iff] at h ⊢
        obtain ⟨m₁, ⟨m₂, hm₂, rfl⟩, rfl⟩ := h
        exact ⟨m₂ + 1, ⟨m₂, nthObjPos_complete_eq hrest hm₂, rfl⟩, rfl⟩
      | succ n₁ =>
        simp only [nthObjPos, History.nthFilterPos, decide_eq_true_eq, Event.obj_inv,
          Event.obj_resp, hxx, ↓reduceIte, Option.map_eq_some_iff] at h ⊢
        obtain ⟨m₁, ⟨m₂, hm₂, rfl⟩, rfl⟩ := h
        exact ⟨m₂ + 1, ⟨m₂, nthObjPos_complete_eq hrest hm₂, rfl⟩, rfl⟩

private theorem nthObjPos_eq_complete_of_odd [DecidableEq P] [DecidableEq Obj] {x : Obj}
    {L : History P Op Resp} (hseq : History.IsSequential L) {k_x : ℕ} :
    nthObjPos x L (2 * k_x + 1) = nthObjPos x (History.complete L) (2 * k_x + 1) ∧
      (∀ m, nthObjPos x L (2 * k_x + 1) = some m →
        nthObjPos x L (2 * k_x) = nthObjPos x (History.complete L) (2 * k_x)) := by
  match L with
  | [] =>
    exact ⟨rfl, fun _ hm => by simp only [nthObjPos, History.nthFilterPos, reduceCtorEq] at hm⟩
  | [.inv p y op] =>
    refine ⟨?_, fun _ hm => ?_⟩
    · simp only [History.complete, List.any_nil, Bool.false_eq_true, ↓reduceIte, nthObjPos,
        History.nthFilterPos, Option.map_none, ite_self]
    · simp only [nthObjPos, History.nthFilterPos, Option.map_none, ite_self, reduceCtorEq] at hm
  | [.resp _ _ _] => exact False.elim hseq
  | .inv _ _ _ :: .inv _ _ _ :: _ => exact False.elim hseq
  | .resp _ _ _ :: _ :: _ => exact False.elim hseq
  | .inv p₁ x₁ op :: .resp p₂ x₂ res :: rest =>
    obtain ⟨hp, hx, hrest⟩ := hseq
    subst hp hx
    have hany : ((Event.resp p₁ x₁ res :: rest).any fun e => decide (e.proc = p₁)) = true := by
      simp only [List.any_cons, Event.proc_resp, decide_true, Bool.true_or]
    simp only [History.complete, hany, ↓reduceIte]
    by_cases hxx : x₁ = x
    · cases k_x with
      | zero =>
        refine ⟨?_, fun _ _ => ?_⟩
        · simp only [nthObjPos, History.nthFilterPos, decide_eq_true_eq, Event.obj_inv,
            Event.obj_resp, hxx, ↓reduceIte]
        · simp only [nthObjPos, History.nthFilterPos, decide_eq_true_eq, Event.obj_inv, hxx,
            ↓reduceIte]
      | succ k_x' =>
        obtain ⟨ih₁, ih₀⟩ := nthObjPos_eq_complete_of_odd (x := x) hrest (k_x := k_x')
        have hstep₁ : 2 * (k_x' + 1) + 1 = (2 * k_x' + 1) + 1 + 1 := by omega
        have hstep₀ : 2 * (k_x' + 1) = (2 * k_x') + 1 + 1 := by omega
        rw [hstep₁, hstep₀]
        refine ⟨?_, fun m hm => ?_⟩
        · simp only [nthObjPos, History.nthFilterPos, decide_eq_true_eq, Event.obj_inv,
            Event.obj_resp, hxx, ↓reduceIte] at ih₁ ⊢
          rw [ih₁]
        · simp only [nthObjPos, History.nthFilterPos, decide_eq_true_eq, Event.obj_inv,
            Event.obj_resp, hxx, ↓reduceIte, Option.map_eq_some_iff] at hm
          obtain ⟨m₁, ⟨m₂, hm₂, rfl⟩, rfl⟩ := hm
          have h0 := ih₀ m₂ hm₂
          simp only [nthObjPos, History.nthFilterPos, decide_eq_true_eq, Event.obj_inv,
            Event.obj_resp, hxx, ↓reduceIte] at h0 ⊢
          rw [h0]
    · obtain ⟨ih₁, ih₀⟩ := nthObjPos_eq_complete_of_odd (x := x) hrest (k_x := k_x)
      refine ⟨?_, fun m hm => ?_⟩
      · simp only [nthObjPos, History.nthFilterPos, decide_eq_true_eq, Event.obj_inv,
          Event.obj_resp, hxx, ↓reduceIte] at ih₁ ⊢
        rw [ih₁]
      · simp only [nthObjPos, History.nthFilterPos, decide_eq_true_eq, Event.obj_inv,
          Event.obj_resp, hxx, ↓reduceIte, Option.map_eq_some_iff] at hm
        obtain ⟨m₁, ⟨m₂, hm₂, rfl⟩, rfl⟩ := hm
        have h0 := ih₀ m₂ hm₂
        cases h2 : 2 * k_x with
        | zero =>
          rw [h2] at h0
          simp only [nthObjPos, History.nthFilterPos, decide_eq_true_eq, Event.obj_inv,
            Event.obj_resp, hxx, ↓reduceIte] at h0 ⊢
          rw [h0]
        | succ u =>
          rw [h2] at h0
          simp only [nthObjPos, History.nthFilterPos, decide_eq_true_eq, Event.obj_inv,
            Event.obj_resp, hxx, ↓reduceIte] at h0 ⊢
          rw [h0]

private theorem nthProcPos_objSubhistory_eq [DecidableEq P] [DecidableEq Obj]
    {p : P} {x : Obj} :
    ∀ {M : History P Op Resp} {n_x n pos : ℕ},
      nthObjPos x (History.procSubhistory M p) n_x = some n →
      History.nthProcPos p M n = some pos →
      M[pos]?.map Event.obj = some x ∧
        History.nthProcPos p (History.objSubhistory M x) n_x = some (objProjPos x M pos)
  | [], _, _, _, hobj, _ => by
    simp only [History.procSubhistory_nil, nthObjPos, History.nthFilterPos, reduceCtorEq] at hobj
  | e :: rest, n_x, n, pos, hobj, hproc => by
    by_cases hep : e.proc = p
    · simp only [History.procSubhistory_cons, hep, ↓reduceIte] at hobj
      by_cases hex : e.obj = x
      · cases n_x with
        | zero =>
          simp only [nthObjPos, History.nthFilterPos, decide_eq_true_eq, hex, ↓reduceIte,
            Option.some.injEq] at hobj
          subst hobj
          simp only [History.nthProcPos, hep, ↓reduceIte, Option.some.injEq] at hproc
          subst hproc
          simp only [List.getElem?_cons_zero, Option.map_some, hex, History.objSubhistory_cons,
            ↓reduceIte, History.nthProcPos, hep, objProjPos, and_self]
        | succ n_x' =>
          simp only [nthObjPos, History.nthFilterPos, decide_eq_true_eq, hex, ↓reduceIte,
            Option.map_eq_some_iff] at hobj
          obtain ⟨n', hn', rfl⟩ := hobj
          simp only [History.nthProcPos, hep, ↓reduceIte, Option.map_eq_some_iff] at hproc
          obtain ⟨pos', hpos', rfl⟩ := hproc
          obtain ⟨hm_obj, hm_pos⟩ := nthProcPos_objSubhistory_eq hn' hpos'
          simp only [List.getElem?_cons_succ, hm_obj, History.objSubhistory_cons, hex, ↓reduceIte,
            History.nthProcPos, hep, hm_pos, Option.map_some, objProjPos, and_self]
      · cases n_x with
        | zero =>
          simp only [nthObjPos, History.nthFilterPos, decide_eq_true_eq, hex, ↓reduceIte,
            Option.map_eq_some_iff] at hobj
          obtain ⟨n', hn', rfl⟩ := hobj
          simp only [History.nthProcPos, hep, ↓reduceIte, Option.map_eq_some_iff] at hproc
          obtain ⟨pos', hpos', rfl⟩ := hproc
          obtain ⟨hm_obj, hm_pos⟩ := nthProcPos_objSubhistory_eq hn' hpos'
          simp only [List.getElem?_cons_succ, hm_obj, History.objSubhistory_cons, hex, ↓reduceIte,
            hm_pos, objProjPos, and_self]
        | succ n_x' =>
          simp only [nthObjPos, History.nthFilterPos, decide_eq_true_eq, hex, ↓reduceIte,
            Option.map_eq_some_iff] at hobj
          obtain ⟨n', hn', rfl⟩ := hobj
          simp only [History.nthProcPos, hep, ↓reduceIte, Option.map_eq_some_iff] at hproc
          obtain ⟨pos', hpos', rfl⟩ := hproc
          obtain ⟨hm_obj, hm_pos⟩ := nthProcPos_objSubhistory_eq hn' hpos'
          simp only [List.getElem?_cons_succ, hm_obj, History.objSubhistory_cons, hex, ↓reduceIte,
            hm_pos, objProjPos, and_self]
    · simp only [History.procSubhistory_cons, hep, ↓reduceIte] at hobj
      cases n with
      | zero =>
        simp only [History.nthProcPos, hep, ↓reduceIte, Option.map_eq_some_iff] at hproc
        obtain ⟨pos', hpos', rfl⟩ := hproc
        obtain ⟨hm_obj, hm_pos⟩ := nthProcPos_objSubhistory_eq hobj hpos'
        by_cases hex : e.obj = x
        · cases n_x with
          | zero =>
            simp only [List.getElem?_cons_succ, hm_obj, History.objSubhistory_cons, hex, ↓reduceIte,
              History.nthProcPos, hep, hm_pos, Option.map_some, objProjPos, and_self]
          | succ n_x' =>
            simp only [List.getElem?_cons_succ, hm_obj, History.objSubhistory_cons, hex, ↓reduceIte,
              History.nthProcPos, hep, hm_pos, Option.map_some, objProjPos, and_self]
        · simp only [List.getElem?_cons_succ, hm_obj, History.objSubhistory_cons, hex, ↓reduceIte,
            hm_pos, objProjPos, and_self]
      | succ n' =>
        simp only [History.nthProcPos, hep, ↓reduceIte, Option.map_eq_some_iff] at hproc
        obtain ⟨pos', hpos', rfl⟩ := hproc
        obtain ⟨hm_obj, hm_pos⟩ := nthProcPos_objSubhistory_eq hobj hpos'
        by_cases hex : e.obj = x
        · cases n_x with
          | zero =>
            simp only [List.getElem?_cons_succ, hm_obj, History.objSubhistory_cons, hex, ↓reduceIte,
              History.nthProcPos, hep, hm_pos, Option.map_some, objProjPos, and_self]
          | succ n_x' =>
            simp only [List.getElem?_cons_succ, hm_obj, History.objSubhistory_cons, hex, ↓reduceIte,
              History.nthProcPos, hep, hm_pos, Option.map_some, objProjPos, and_self]
        · simp only [List.getElem?_cons_succ, hm_obj, History.objSubhistory_cons, hex, ↓reduceIte,
            hm_pos, objProjPos, and_self]

/-- Lift a local operation identifier `e_x` of `M | x` to its global `OpId P` in `M`, computed from
`complete (M | e_x.proc)` so equivalent completions induce the identical lift. -/
private def liftOp [DecidableEq P] [DecidableEq Obj] (M : History P Op Resp) (x : Obj)
    (e_x : OpId P) : OpId P :=
  match nthObjPos x (History.complete (History.procSubhistory M e_x.proc)) (2 * e_x.idx) with
  | some n => ⟨e_x.proc, n / 2⟩
  | none => e_x

private theorem liftOp_eq_of_equivalent_complete [DecidableEq P] [DecidableEq Obj]
    {M₁ M₂ : History P Op Resp} (heq : History.Equivalent (History.complete M₁) M₂)
    (hseq₂ : History.IsSequential M₂) (hwf₁ : History.WellFormed M₁) (x : Obj) (e_x : OpId P) :
    liftOp M₁ x e_x = liftOp M₂ x e_x := by
  have hev₂ := History.even_length_of_equivalent_complete hwf₁ hseq₂ heq
  have hcomp_M₂ : History.complete (History.procSubhistory M₂ e_x.proc) =
      History.procSubhistory M₂ e_x.proc := by
    rw [← History.procSubhistory_complete,
      History.complete_eq_self_of_isSequential_even hseq₂ hev₂]
  have hp := heq e_x.proc
  rw [History.procSubhistory_complete] at hp
  simp only [liftOp, hcomp_M₂, hp]

private theorem liftOp_spec [DecidableEq P] [DecidableEq Obj] {M : History P Op Resp}
    (hwf : History.WellFormed M) {x : Obj} {e_x : OpId P}
    (hc : History.IsCompletedOp (History.objSubhistory M x) e_x) :
    History.IsCompletedOp M (liftOp M x e_x) ∧
      (liftOp M x e_x).proc = e_x.proc ∧
      (∃ i, History.invPos M (liftOp M x e_x) = some i ∧ M[i]?.map Event.obj = some x ∧
        History.invPos (History.objSubhistory M x) e_x = some (objProjPos x M i)) ∧
      (∃ r, History.respPos M (liftOp M x e_x) = some r ∧ M[r]?.map Event.obj = some x ∧
        History.respPos (History.objSubhistory M x) e_x = some (objProjPos x M r)) := by
  have hlen_x : 2 * e_x.idx + 1 <
      (History.objSubhistory (History.procSubhistory M e_x.proc) x).length := by
    rw [← History.procSubhistory_objSubhistory_comm]
    exact (History.isCompletedOp_iff_lt_length _ _).mp hc
  have hsome_odd : (nthObjPos x (History.procSubhistory M e_x.proc) (2 * e_x.idx + 1)).isSome =
      true := (nthObjPos_isSome_iff x _ _).mpr hlen_x
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsome_odd
  obtain ⟨k, rfl, hk₀⟩ := nthObjPos_pair_of_isSequential (hwf e_x.proc) hm
  obtain ⟨heq_odd, heq_even_fn⟩ :=
    nthObjPos_eq_complete_of_odd (x := x) (hwf e_x.proc) (k_x := e_x.idx)
  have hk₀_comp :
      nthObjPos x (History.complete (History.procSubhistory M e_x.proc)) (2 * e_x.idx) =
        some (2 * k) := by
    rw [← heq_even_fn (2 * k + 1) hm]; exact hk₀
  have hlift : liftOp M x e_x = ⟨e_x.proc, k⟩ := by
    simp only [liftOp, hk₀_comp]
    ext
    · rfl
    · dsimp only; omega
  rw [hlift]
  obtain ⟨hm_lt, _⟩ := nthObjPos_lt_length hm
  have hc_M : History.IsCompletedOp M ⟨e_x.proc, k⟩ :=
    (History.isCompletedOp_iff_lt_length M ⟨e_x.proc, k⟩).mpr hm_lt
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hc_M
  obtain ⟨i, hi, _⟩ := History.invPos_of_respPos hr
  obtain ⟨hi_obj, hi_proj⟩ := nthProcPos_objSubhistory_eq hk₀ hi
  obtain ⟨hr_obj, hr_proj⟩ := nthProcPos_objSubhistory_eq hm hr
  exact ⟨hc_M, rfl, ⟨i, hi, hi_obj, hi_proj⟩, ⟨r, hr, hr_obj, hr_proj⟩⟩

private theorem prec_objSubhistory_iff [DecidableEq P] [DecidableEq Obj] {M : History P Op Resp}
    (hwf : History.WellFormed M) {x : Obj} {e₀ e₁ : OpId P}
    (hc₀ : History.IsCompletedOp (History.objSubhistory M x) e₀)
    (hc₁ : History.IsCompletedOp (History.objSubhistory M x) e₁) :
    History.prec (History.objSubhistory M x) e₀ e₁ ↔
      History.prec M (liftOp M x e₀) (liftOp M x e₁) := by
  obtain ⟨_, _, _, ⟨r, hr, hr_obj, hr_proj⟩⟩ := liftOp_spec hwf hc₀
  obtain ⟨_, _, ⟨i, hi, _, hi_proj⟩, _⟩ := liftOp_spec hwf hc₁
  obtain ⟨hr_lt, _⟩ := History.nthProcPos_lt_length hr
  obtain ⟨hi_lt, _⟩ := History.nthProcPos_lt_length hi
  have hlt_iff := objProjPos_lt_iff x hr_lt hi_lt hr_obj
  constructor
  · rintro ⟨rx, ix, hrx, hix, hlt⟩
    rw [hr_proj] at hrx; rw [hi_proj] at hix
    injection hrx with hrx'; injection hix with hix'
    subst hrx' hix'
    exact ⟨r, i, hr, hi, hlt_iff.mp hlt⟩
  · rintro ⟨r', i', hr', hi', hlt⟩
    rw [hr] at hr'; rw [hi] at hi'
    injection hr' with hr''; injection hi' with hi''
    subst hr'' hi''
    exact ⟨objProjPos x M r, objProjPos x M i, hr_proj, hi_proj, hlt_iff.mpr hlt⟩

end LocalityInfrastructure

/-! ### Herlihy–Wing Theorem 1 (Locality) and Theorem 2 (Nonblocking) -/

private theorem isSequential_append_left {P Obj : Type*} {Op Resp : Obj → Type*} :
    ∀ {L₁ L₂ : History P Op Resp},
      History.IsSequential (L₁ ++ L₂) → History.IsSequential L₁
  | [], _, _ => trivial
  | [.inv _ _ _], _, _ => trivial
  | [.resp _ _ _], [], h => False.elim h
  | [.resp _ _ _], _ :: _, h => False.elim h
  | .resp _ _ _ :: _ :: _, _, h => False.elim h
  | .inv _ _ _ :: .inv _ _ _ :: _, _, h => False.elim h
  | .inv _ _ _ :: .resp _ _ _ :: _, _, h => ⟨h.1, h.2.1, isSequential_append_left h.2.2⟩

private theorem complete_flatMap_append_inv {P Obj : Type*} {Op Resp : Obj → Type*}
    [DecidableEq P] (cs : List (OpCall P Op Resp)) (q : P) (y : Obj) (op : Op y) :
    History.complete (cs.flatMap OpCall.toEvents ++ [.inv q y op]) =
      cs.flatMap OpCall.toEvents := by
  induction cs with
  | nil =>
    simp only [List.flatMap_nil, List.nil_append, History.complete, List.any_nil,
      Bool.false_eq_true, ↓reduceIte]
  | cons c cs' ih =>
    simp only [List.flatMap_cons, OpCall.toEvents, List.cons_append, List.nil_append]
    have hany : ((Event.resp c.proc c.obj c.res ::
        (cs'.flatMap OpCall.toEvents ++ [.inv q y op])).any
          fun e => decide (e.proc = c.proc)) = true := by
      simp only [List.any_cons, Event.proc_resp, decide_true, Bool.true_or]
    simp only [History.complete, hany, ↓reduceIte]
    exact congrArg (fun t => .inv c.proc c.obj c.op :: .resp c.proc c.obj c.res :: t) ih

private theorem isCompletedOp_complete_iff {P Obj : Type*} {Op Resp : Obj → Type*}
    [DecidableEq P] {M : History P Op Resp} (hwf : History.WellFormed M) (e : OpId P) :
    History.IsCompletedOp (History.complete M) e ↔ History.IsCompletedOp M e := by
  rw [History.isCompletedOp_iff_lt_length, History.isCompletedOp_iff_lt_length,
    History.procSubhistory_complete]
  have hseq := hwf e.proc
  rcases History.isSequential_decomp hseq with ⟨cs, hcs⟩ | ⟨cs, q, y, op, hcs⟩
  · rw [hcs, History.complete_eq_self_of_isSequential_even (by rw [← hcs]; exact hseq)
      (by rw [History.length_flatMap_toEvents]; omega)]
  · rw [hcs, complete_flatMap_append_inv, List.length_append, History.length_flatMap_toEvents,
      List.length_singleton]
    omega

/-- Restricting a linearizable history `H` to any single object `x` preserves linearizability
("only if" direction of [HerlihyWing1990], §3.1, Theorem 1, p. 470; [SelaHerlihyPetrank2021], §5.2,
Theorem 5.1, p. 7). -/
theorem IsLinearizable.objSubhistory {P Obj : Type*} {Op Resp : Obj → Type*}
    [DecidableEq P] [DecidableEq Obj] {spec : ∀ x, SeqSpec P Op Resp x}
    {H : History P Op Resp} (hlin : IsLinearizable spec H) (x : Obj) :
    IsLinearizable spec (History.objSubhistory H x) := by
  obtain ⟨H', ⟨R, hresp, rfl, hwf'⟩, S, hseqS, hlegS, heqS, hprecS⟩ := hlin
  have hwfH : History.WellFormed H := fun p => by
    have hp := hwf' p
    rw [History.procSubhistory_append] at hp
    exact isSequential_append_left hp
  let R_x := History.objSubhistory R x
  have hresp_x : History.IsRespList R_x := fun e hm => hresp e (List.mem_filter.mp hm).1
  have hwf'_x : History.WellFormed (History.objSubhistory H x ++ R_x) := by
    rw [← History.objSubhistory_append]
    exact hwf'.objSubhistory x
  refine ⟨History.objSubhistory H x ++ R_x, ⟨R_x, hresp_x, rfl, hwf'_x⟩,
    History.objSubhistory S x, History.isSequential_objSubhistory hseqS x, ?_, ?_, ?_⟩
  · intro y
    by_cases hxy : x = y
    · subst hxy
      rw [History.objSubhistory_idem]
      exact hlegS x
    · rw [History.objSubhistory_of_ne S hxy]
      exact (spec y).nil_mem
  · rw [← History.objSubhistory_append, History.complete_objSubhistory hwf' x]
    exact heqS.objSubhistory x
  · intro e₀ e₁ hc₀ hc₁ hprec_x
    have hc₀' : History.IsCompletedOp (History.objSubhistory (H ++ R) x) e₀ := by
      rw [History.objSubhistory_append]; exact hc₀
    have hc₁' : History.IsCompletedOp (History.objSubhistory (H ++ R) x) e₁ := by
      rw [History.objSubhistory_append]; exact hc₁
    have hwf_Hx : History.WellFormed (History.objSubhistory H x) := hwfH.objSubhistory x
    have h₁ : History.prec (History.objSubhistory (H ++ R) x) e₀ e₁ := by
      rw [History.objSubhistory_append]
      exact (History.prec_append_resp_iff hwf_Hx hresp_x hwf'_x hc₁).mpr hprec_x
    have h₂ : History.prec (H ++ R) (liftOp (H ++ R) x e₀) (liftOp (H ++ R) x e₁) :=
      (prec_objSubhistory_iff hwf' hc₀' hc₁').mp h₁
    obtain ⟨hc₀_HR, _⟩ := liftOp_spec hwf' hc₀'
    obtain ⟨hc₁_HR, _⟩ := liftOp_spec hwf' hc₁'
    have h₃ : History.prec H (liftOp (H ++ R) x e₀) (liftOp (H ++ R) x e₁) :=
      (History.prec_append_resp_iff hwfH hresp hwf' hc₁_HR).mp h₂
    have h₄ : History.prec S (liftOp (H ++ R) x e₀) (liftOp (H ++ R) x e₁) :=
      hprecS _ _ hc₀_HR hc₁_HR h₃
    have hlift₀ := liftOp_eq_of_equivalent_complete heqS hseqS hwf' x e₀
    have hlift₁ := liftOp_eq_of_equivalent_complete heqS hseqS hwf' x e₁
    rw [hlift₀, hlift₁] at h₄
    have h_eq_x : History.Equivalent
        (History.complete (History.objSubhistory (H ++ R) x)) (History.objSubhistory S x) := by
      rw [History.complete_objSubhistory hwf' x]
      exact heqS.objSubhistory x
    have hc₀_Sx : History.IsCompletedOp (History.objSubhistory S x) e₀ :=
      (h_eq_x.isCompletedOp_iff e₀).mp
        ((isCompletedOp_complete_iff (hwf'.objSubhistory x) e₀).mpr hc₀')
    have hc₁_Sx : History.IsCompletedOp (History.objSubhistory S x) e₁ :=
      (h_eq_x.isCompletedOp_iff e₁).mp
        ((isCompletedOp_complete_iff (hwf'.objSubhistory x) e₁).mpr hc₁')
    have hwfS : History.WellFormed S := by
      have hevS := History.even_length_of_equivalent_complete hwf' hseqS heqS
      obtain ⟨cs, rfl⟩ := History.exists_calls_of_isSequential_even hseqS hevS
      exact History.wellFormed_flatMap_toEvents cs
    exact (prec_objSubhistory_iff hwfS hc₀_Sx hc₁_Sx).mpr h₄

section LocalityCompositionHelpers

variable {P Obj : Type*} {Op Resp : Obj → Type*}

private theorem flatMap_toEvents_injective :
    ∀ {cs₁ cs₂ : List (OpCall P Op Resp)},
      cs₁.flatMap OpCall.toEvents = cs₂.flatMap OpCall.toEvents → cs₁ = cs₂
  | [], [], _ => rfl
  | [], c :: _, h => by
    simp only [List.flatMap_nil, List.flatMap_cons, OpCall.toEvents, List.cons_append] at h
    nomatch h
  | c :: _, [], h => by
    simp only [List.flatMap_nil, List.flatMap_cons, OpCall.toEvents, List.cons_append] at h
    nomatch h
  | c₁ :: rest₁, c₂ :: rest₂, h => by
    simp only [List.flatMap_cons, OpCall.toEvents, List.cons_append, List.nil_append,
      List.cons.injEq] at h
    obtain ⟨hinv, hresp, hrest⟩ := h
    cases c₁; cases c₂
    injection hinv with hp hx hop
    subst hp hx
    cases hop
    injection hresp with _ _ hres
    cases hres
    exact congrArg _ (flatMap_toEvents_injective hrest)

private theorem filter_getElem_count_take {α : Type*} (pred : α → Bool) :
    ∀ (cs : List α) (k : ℕ) (hk : k < cs.length), pred cs[k] = true →
      ∃ hlt : ((cs.take k).filter pred).length < (cs.filter pred).length,
        (cs.filter pred)[((cs.take k).filter pred).length]'hlt = cs[k]
  | [], _, hk, _ => by simp only [List.length_nil] at hk; omega
  | c :: rest, 0, _, hpred => by
    simp only [List.getElem_cons_zero] at hpred
    rw [List.getElem_cons_zero, List.take_zero, List.filter_nil, List.length_nil,
      List.filter_cons_of_pos hpred]
    exact ⟨Nat.zero_lt_succ _, rfl⟩
  | c :: rest, k + 1, hk, hpred => by
    have hk' : k < rest.length := by simp only [List.length_cons] at hk; omega
    simp only [List.getElem_cons_succ] at hpred ⊢
    obtain ⟨hlt', heq'⟩ := filter_getElem_count_take pred rest k hk' hpred
    by_cases hpc : pred c = true
    · rw [List.take_succ_cons, List.filter_cons_of_pos hpc]
      refine ⟨by simp only [List.filter_cons_of_pos hpc, List.length_cons]; omega, ?_⟩
      simp only [List.filter_cons_of_pos hpc, List.length_cons, List.getElem_cons_succ]
      exact heq'
    · rw [List.take_succ_cons, List.filter_cons_of_neg hpc]
      refine ⟨by simp only [List.filter_cons_of_neg hpc]; exact hlt', ?_⟩
      simp only [List.filter_cons_of_neg hpc]
      exact heq'

private def countObjCalls [DecidableEq Obj] (x : Obj) (calls : List (OpCall P Op Resp)) : ℕ :=
  (calls.filter fun c => decide (c.obj = x)).length

private theorem nthObjPos_flatMap_toEvents [DecidableEq Obj] (calls : List (OpCall P Op Resp))
    (k : ℕ) (hk : k < calls.length) :
    nthObjPos calls[k].obj (calls.flatMap OpCall.toEvents)
        (2 * countObjCalls calls[k].obj (calls.take k)) = some (2 * k) ∧
      nthObjPos calls[k].obj (calls.flatMap OpCall.toEvents)
        (2 * countObjCalls calls[k].obj (calls.take k) + 1) = some (2 * k + 1) :=
  nthFilterPos_flatMap_toEvents
    (fun c => decide (c.obj = calls[k].obj))
    (fun e => decide (e.obj = calls[k].obj))
    (fun _ => rfl) (fun _ => rfl) calls k hk (decide_eq_true rfl)

private theorem strictMono_list_eq_range' :
    ∀ (m s : ℕ) (L : List ℕ),
      List.Pairwise (· < ·) L →
      (∀ x ∈ L, s ≤ x ∧ x < s + m) →
      (∀ k, s ≤ k → k < s + m → k ∈ L) →
      L = List.range' s m
  | 0, s, L, _, hbd, _ => by
    cases L with
    | nil => rfl
    | cons a _ =>
      have := hbd a List.mem_cons_self
      omega
  | m + 1, s, L, hpw, hbd, hsurj => by
    have hs_mem : s ∈ L := hsurj s (Nat.le_refl s) (by omega)
    cases L with
    | nil => exact False.elim (List.not_mem_nil hs_mem)
    | cons a tail =>
      obtain ⟨ha_tail, hpw_tail⟩ := List.pairwise_cons.mp hpw
      have has : a = s := by
        rcases List.mem_cons.mp hs_mem with rfl | htail
        · rfl
        · have hlt := ha_tail s htail
          have hge := (hbd a List.mem_cons_self).1
          omega
      subst a
      have hbd_tail : ∀ x ∈ tail, s + 1 ≤ x ∧ x < (s + 1) + m := by
        intro x hx
        have hlt := ha_tail x hx
        have hbx := hbd x (List.mem_cons_of_mem _ hx)
        omega
      have hsurj_tail : ∀ k, s + 1 ≤ k → k < (s + 1) + m → k ∈ tail := by
        intro k hk₁ hk₂
        have hkm : k ∈ s :: tail := hsurj k (by omega) (by omega)
        rcases List.mem_cons.mp hkm with rfl | hkt
        · omega
        · exact hkt
      simp only [List.range'_succ]
      exact congrArg (s :: ·)
        (strictMono_list_eq_range' m (s + 1) tail hpw_tail hbd_tail hsurj_tail)

private theorem map_eq_of_strictMono_surj {β γ : Type*} {src : List β} {dst : List γ}
    (pos : β → ℕ) (val : β → γ)
    (hvalid : ∀ b ∈ src, ∃ hlt : pos b < dst.length, val b = dst[pos b]'hlt)
    (hmono : ∀ i j (hi : i < src.length) (hj : j < src.length), i < j → pos src[i] < pos src[j])
    (hsurj : ∀ k < dst.length, ∃ b ∈ src, pos b = k) :
    src.map val = dst := by
  have hpw : List.Pairwise (· < ·) (src.map pos) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.length_map] at hi hj
    simp only [List.getElem_map]
    exact hmono i j hi hj hij
  have hbd : ∀ x ∈ src.map pos, 0 ≤ x ∧ x < 0 + dst.length := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hlt, _⟩ := hvalid b hb
    exact ⟨Nat.zero_le _, by omega⟩
  have hsurj' : ∀ k, 0 ≤ k → k < 0 + dst.length → k ∈ src.map pos := by
    intro k _ hk
    obtain ⟨b, hb, rfl⟩ := hsurj k (by omega)
    exact List.mem_map_of_mem hb
  have hrange : src.map pos = List.range dst.length := by
    rw [List.range_eq_range']
    exact strictMono_list_eq_range' dst.length 0 (src.map pos) hpw hbd hsurj'
  have hlen : src.length = dst.length := by
    have := congrArg List.length hrange
    simpa only [List.length_map, List.length_range] using this
  apply List.ext_getElem
  · rw [List.length_map, hlen]
  · intro i hi₁ hi₂
    simp only [List.length_map] at hi₁
    have hpos_i : pos src[i] = i := by
      have hget := congrArg (fun l => l[i]?) hrange
      simp only [List.getElem?_map, List.getElem?_eq_getElem hi₁, Option.map_some,
        List.getElem?_range hi₂, Option.some.injEq] at hget
      exact hget
    obtain ⟨hlt, hval⟩ := hvalid src[i] (List.getElem_mem hi₁)
    simp only [List.getElem_map, hval, hpos_i]

private theorem exists_fin_idx_of_eq {α : Type*} {l₁ l₂ l : List α} (heq : l₁ = l₂)
    (h : ∃ idx : Fin l₂.length → Fin l.length,
      (∀ i, l₂[i.1] = l[(idx i).1]) ∧ (∀ i j, i.1 < j.1 → (idx i).1 < (idx j).1)) :
    ∃ idx : Fin l₁.length → Fin l.length,
      (∀ i, l₁[i.1] = l[(idx i).1]) ∧ (∀ i j, i.1 < j.1 → (idx i).1 < (idx j).1) := by
  subst heq; exact h

private theorem filter_strictMono_indices {α : Type*} (l : List α) (pred : α → Bool) :
    ∃ idx : Fin (l.filter pred).length → Fin l.length,
      (∀ i, (l.filter pred)[i.1] = l[(idx i).1]) ∧
      (∀ i j, i.1 < j.1 → (idx i).1 < (idx j).1) := by
  induction l with
  | nil =>
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | cons a rest ih =>
    obtain ⟨idx', hval', hmono'⟩ := ih
    by_cases hpa : pred a = true
    · refine exists_fin_idx_of_eq (List.filter_cons_of_pos hpa) ?_
      refine ⟨fun i =>
          if hi0 : i.1 = 0 then ⟨0, Nat.zero_lt_succ _⟩
          else
            let i' : Fin (rest.filter pred).length :=
              ⟨i.1 - 1, by have h := i.2; simp only [List.length_cons] at h; omega⟩
            ⟨(idx' i').1 + 1, Nat.succ_lt_succ (idx' i').2⟩,
        ?_, ?_⟩
      · intro ⟨i, hi⟩
        cases i with
        | zero => simp only [↓reduceDIte, List.getElem_cons_zero]
        | succ k =>
          simp only [Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel, List.getElem_cons_succ]
          exact hval' ⟨k, by simp only [List.length_cons] at hi; omega⟩
      · intro ⟨i, hi⟩ ⟨j, hj⟩ hij
        dsimp only at hij ⊢
        cases i with
        | zero =>
          cases j with
          | zero => omega
          | succ j' =>
            simp only [↓reduceDIte, Nat.succ_ne_zero]
            omega
        | succ i' =>
          cases j with
          | zero => omega
          | succ j' =>
            simp only [Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel]
            have := hmono' ⟨i', by simp only [List.length_cons] at hi; omega⟩
              ⟨j', by simp only [List.length_cons] at hj; omega⟩ (by dsimp only; omega)
            omega
    · refine exists_fin_idx_of_eq (List.filter_cons_of_neg hpa) ?_
      refine ⟨fun i => ⟨(idx' i).1 + 1, Nat.succ_lt_succ (idx' i).2⟩, ?_, ?_⟩
      · intro i; simp only [List.getElem_cons_succ, hval' i]
      · intro i j hij; have := hmono' i j hij; dsimp only; omega

private theorem objSubhistory_flatMap_of_nodup [DecidableEq Obj] {l : List Obj} (hnd : l.Nodup)
    (f : Obj → History P Op Resp) (hobj : ∀ y ∈ l, ∀ e ∈ f y, e.obj = y) (x : Obj) :
    History.objSubhistory (l.flatMap f) x = if x ∈ l then f x else [] := by
  induction l with
  | nil => simp only [List.flatMap_nil, History.objSubhistory_nil, List.not_mem_nil, ↓reduceIte]
  | cons y rest ih =>
    obtain ⟨hynot, hnd_rest⟩ := List.nodup_cons.mp hnd
    simp only [List.flatMap_cons, History.objSubhistory_append, List.mem_cons]
    have ih' := ih hnd_rest (fun z hz => hobj z (List.mem_cons_of_mem _ hz))
    by_cases hxy : x = y
    · subst hxy
      have hxnot : x ∉ rest := hynot
      simp only [true_or, ↓reduceIte, ih', hxnot, List.append_nil]
      exact History.objSubhistory_eq_self_of_forall_obj (hobj x List.mem_cons_self)
    · have hyx : y ≠ x := Ne.symm hxy
      have hfy : History.objSubhistory (f y) x = [] :=
        History.objSubhistory_eq_nil_of_forall_ne fun e he => by
          rw [hobj y List.mem_cons_self e he]; exact hyx
      simp only [hxy, false_or, hfy, List.nil_append, ih']

private theorem procSubhistory_flatMap_eq_single [DecidableEq P] [DecidableEq Obj]
    {l : List Obj} (hnd : l.Nodup) (f : Obj → History P Op Resp) (p : P) (x₀ : Obj)
    (hother : ∀ y ∈ l, y ≠ x₀ → History.procSubhistory (f y) p = []) :
    History.procSubhistory (l.flatMap f) p =
      if x₀ ∈ l then History.procSubhistory (f x₀) p else [] := by
  induction l with
  | nil => simp only [List.flatMap_nil, History.procSubhistory_nil, List.not_mem_nil, ↓reduceIte]
  | cons y rest ih =>
    obtain ⟨hynot, hnd_rest⟩ := List.nodup_cons.mp hnd
    simp only [List.flatMap_cons, History.procSubhistory_append, List.mem_cons]
    have ih' := ih hnd_rest (fun z hz => hother z (List.mem_cons_of_mem _ hz))
    by_cases hxy : x₀ = y
    · subst hxy
      have hrest_nil : History.procSubhistory (rest.flatMap f) p = [] := by
        rw [ih']
        simp only [hynot, ↓reduceIte]
      simp only [true_or, ↓reduceIte, hrest_nil, List.append_nil]
    · have hyx : y ≠ x₀ := Ne.symm hxy
      rw [hother y List.mem_cons_self hyx, List.nil_append, ih']
      simp only [hxy, false_or]

end LocalityCompositionHelpers

/-- **Herlihy–Wing Theorem 1 (Locality / Compositionality of Linearizability)**
([HerlihyWing1990], §3.1, Theorem 1, pp. 470–471; amended L2 proof of [SelaHerlihyPetrank2021],
§5.2, Theorem 5.1, pp. 7–9): a well-formed concurrent history `H` over typed objects `Obj` is
linearizable if and only if for every object `x : Obj`, its object subhistory
`History.objSubhistory H x` (`H | x`) is linearizable. -/
theorem isLinearizable_iff_forall_obj {P Obj : Type*} {Op Resp : Obj → Type*}
    [DecidableEq P] [DecidableEq Obj] (spec : ∀ x, SeqSpec P Op Resp x)
    {H : History P Op Resp} (hwf : History.WellFormed H) :
    IsLinearizable spec H ↔ ∀ x, IsLinearizable spec (History.objSubhistory H x) := by
  refine ⟨fun hlin x => hlin.objSubhistory x, fun hall => ?_⟩
  have complete_mem_sub : ∀ {M : History P Op Resp} {e : Event P Op Resp},
      e ∈ History.complete M → e ∈ M := by
    intro M e hm
    induction M with
    | nil => exact hm
    | cons a rest ih =>
      cases a with
      | inv p y op =>
        simp only [History.complete] at hm
        split at hm
        · rcases List.mem_cons.mp hm with rfl | hm'
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih hm')
        · exact List.mem_cons_of_mem _ (ih hm)
      | resp p y res =>
        rcases List.mem_cons.mp hm with rfl | hm'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih hm')
  have hall_norm : ∀ x, ∃ (Rx Sx : History P Op Resp),
      History.IsRespList Rx ∧
      (∀ e ∈ Rx, e.obj = x) ∧
      (x ∉ H.map Event.obj → Rx = []) ∧
      History.WellFormed (History.objSubhistory H x ++ Rx) ∧
      History.IsSequential Sx ∧
      Sx ∈ (spec x).allowed ∧
      History.Equivalent (History.complete (History.objSubhistory H x ++ Rx)) Sx ∧
      (∀ e₀ e₁, History.IsCompletedOp (History.objSubhistory H x ++ Rx) e₀ →
        History.IsCompletedOp (History.objSubhistory H x ++ Rx) e₁ →
        History.prec (History.objSubhistory H x) e₀ e₁ → History.prec Sx e₀ e₁) := by
    intro x
    by_cases hx_mem : x ∈ H.map Event.obj
    · obtain ⟨H'_x, ⟨Rx, hresp_x, rfl, hwf'_x⟩, Sx, hseq_x, hleg_x, heq_x, hprec_x⟩ := hall x
      have hRx_obj : ∀ e ∈ Rx, e.obj = x := by
        intro e he
        have hp_mem : e ∈ History.procSubhistory Rx e.proc :=
          List.mem_filter.mpr ⟨he, decide_eq_true rfl⟩
        have hseq_p := (hwf.objSubhistory x) e.proc
        have hseq_ext := hwf'_x e.proc
        rw [History.procSubhistory_append] at hseq_ext
        have hresp_p : History.IsRespList (History.procSubhistory Rx e.proc) :=
          fun a ha => hresp_x a (List.mem_filter.mp ha).1
        rcases History.isRespList_le_one_of_isSequential hseq_p hresp_p hseq_ext with
          hnil | ⟨cs, q, y, op, res, hL, hR⟩
        · rw [hnil] at hp_mem; exact False.elim (List.not_mem_nil hp_mem)
        · rw [hR, List.mem_singleton] at hp_mem
          have hinv_mem : Event.inv q y op ∈ History.objSubhistory H x := by
            have hmem_p :
                Event.inv q y op ∈ History.procSubhistory (History.objSubhistory H x) e.proc := by
              rw [hL]; exact List.mem_append_right _ List.mem_cons_self
            exact (List.mem_filter.mp hmem_p).1
          have hyx : y = x := of_decide_eq_true (List.mem_filter.mp hinv_mem).2
          rw [hp_mem, Event.obj_resp, hyx]
      have hSx_obj : ∀ e ∈ Sx, e.obj = x := by
        intro e he
        have hp_mem : e ∈ History.procSubhistory Sx e.proc :=
          List.mem_filter.mpr ⟨he, decide_eq_true rfl⟩
        rw [← heq_x e.proc] at hp_mem
        have hcomp_mem : e ∈ History.complete (History.objSubhistory H x ++ Rx) :=
          (List.mem_filter.mp hp_mem).1
        rcases List.mem_append.mp (complete_mem_sub hcomp_mem) with hH | hR
        · exact of_decide_eq_true (List.mem_filter.mp hH).2
        · exact hRx_obj e hR
      have hSx_allowed : Sx ∈ (spec x).allowed := by
        have h := hleg_x x
        rwa [History.objSubhistory_eq_self_of_forall_obj hSx_obj] at h
      exact ⟨Rx, Sx, hresp_x, hRx_obj, fun hnot => absurd hx_mem hnot,
        hwf'_x, hseq_x, hSx_allowed, heq_x, hprec_x⟩
    · have hHx_nil : History.objSubhistory H x = [] :=
        History.objSubhistory_eq_nil_of_forall_ne fun e he h =>
          hx_mem (List.mem_map.mpr ⟨e, he, h⟩)
      refine ⟨[], [], fun _ hm => False.elim (List.not_mem_nil hm),
        fun _ hm => False.elim (List.not_mem_nil hm), fun _ => rfl, ?_, trivial,
        (spec x).nil_mem, ?_, ?_⟩
      · rw [hHx_nil, List.nil_append]; exact History.wellFormed_nil
      · rw [hHx_nil, List.nil_append, History.complete_nil]; exact History.Equivalent.refl []
      · intro e₀ _ hc₀ _ _
        rw [hHx_nil, List.nil_append, History.isCompletedOp_iff_lt_length,
          History.procSubhistory_nil, List.length_nil] at hc₀
        omega
  choose Rx Sx hRx_resp hRx_obj hRx_out hwf_x hSx_seq hSx_leg heq_x hprec_x using hall_norm
  let objs := (H.map Event.obj).dedup
  have hobjs_nd : objs.Nodup := List.nodup_dedup _
  let R := objs.flatMap Rx
  let H' := H ++ R
  have hR_resp : History.IsRespList R := by
    intro e hm
    obtain ⟨x, _, hex⟩ := List.mem_flatMap.mp hm
    exact hRx_resp x e hex
  have hR_obj : ∀ x, History.objSubhistory R x = Rx x := by
    intro x
    rw [objSubhistory_flatMap_of_nodup hobjs_nd Rx (fun y _ => hRx_obj y) x]
    by_cases hx : x ∈ objs
    · simp only [hx, ↓reduceIte]
    · simp only [hx, ↓reduceIte]
      have hx' : x ∉ H.map Event.obj := fun hm => hx (List.mem_dedup.mpr hm)
      exact (hRx_out x hx').symm
  have hH'_obj : ∀ x, History.objSubhistory H' x = History.objSubhistory H x ++ Rx x := by
    intro x
    simp only [H', History.objSubhistory_append, hR_obj x]
  have hwf' : History.WellFormed H' := by
    intro p
    simp only [H', History.procSubhistory_append]
    have hp_seq := hwf p
    have hRx_even_nil : ∀ y, (History.objSubhistory (History.procSubhistory H p) y).length % 2 = 0 →
        History.procSubhistory (Rx y) p = [] := by
      intro y hev_y
      have hseq_hy : History.IsSequential (History.procSubhistory (History.objSubhistory H y) p) :=
        (hwf.objSubhistory y) p
      have hev_hy : (History.procSubhistory (History.objSubhistory H y) p).length % 2 = 0 := by
        rwa [History.procSubhistory_objSubhistory_comm]
      have hseq_ext := hwf_x y p
      rw [History.procSubhistory_append] at hseq_ext
      have hresp_py : History.IsRespList (History.procSubhistory (Rx y) p) :=
        fun e hm => hRx_resp y e (List.mem_filter.mp hm).1
      exact History.isRespList_eq_nil_of_isSequential_even hseq_hy hev_hy hresp_py hseq_ext
    rcases History.isSequential_decomp hp_seq with ⟨cs, hcs⟩ | ⟨cs, q, x₀, op, hcs⟩
    · have hall_y : ∀ y, History.procSubhistory (Rx y) p = [] := by
        intro y
        apply hRx_even_nil y
        rw [hcs, History.objSubhistory_flatMap_toEvents, History.length_flatMap_toEvents]
        omega
      have hflat_nil : ∀ l : List Obj, History.procSubhistory (l.flatMap Rx) p = [] := by
        intro l
        induction l with
        | nil => exact History.procSubhistory_nil p
        | cons y ys ih =>
          rw [List.flatMap_cons, History.procSubhistory_append, hall_y y, List.nil_append, ih]
      change History.IsSequential
        (History.procSubhistory H p ++ History.procSubhistory (objs.flatMap Rx) p)
      rw [hflat_nil objs, List.append_nil]
      exact hp_seq
    · have hqp : q = p := by
        have hmem : Event.inv q x₀ op ∈ History.procSubhistory H p := by
          rw [hcs]; exact List.mem_append_right _ List.mem_cons_self
        exact of_decide_eq_true (List.mem_filter.mp hmem).2
      subst hqp
      have hother : ∀ y ∈ objs, y ≠ x₀ → History.procSubhistory (Rx y) q = [] := by
        intro y _ hyx₀
        apply hRx_even_nil y
        rw [hcs, History.objSubhistory_append, History.objSubhistory_flatMap_toEvents,
          History.objSubhistory_cons, Event.obj_inv]
        simp only [Ne.symm hyx₀, ↓reduceIte, History.objSubhistory_nil, List.append_nil,
          History.length_flatMap_toEvents]
        omega
      have hRp := procSubhistory_flatMap_eq_single hobjs_nd Rx q x₀ hother
      change History.IsSequential
        (History.procSubhistory H q ++ History.procSubhistory (objs.flatMap Rx) q)
      rw [hRp]
      by_cases hx₀ : x₀ ∈ objs
      · simp only [hx₀, ↓reduceIte]
        have hseq_ext := hwf_x x₀ q
        rw [History.procSubhistory_append] at hseq_ext
        have hresp_px₀ : History.IsRespList (History.procSubhistory (Rx x₀) q) :=
          fun e hm => hRx_resp x₀ e (List.mem_filter.mp hm).1
        rcases History.isRespList_le_one_of_isSequential ((hwf.objSubhistory x₀) q)
          hresp_px₀ hseq_ext with hnil | ⟨cs', q', y', op', res, _, hR_eq⟩
        · rw [hnil, List.append_nil]; exact hp_seq
        · have hq' : q' = q := by
            have hm : Event.resp q' y' res ∈ History.procSubhistory (Rx x₀) q := by
              rw [hR_eq]; exact List.mem_cons_self
            exact of_decide_eq_true (List.mem_filter.mp hm).2
          have hy' : y' = x₀ := by
            have hm : Event.resp q' y' res ∈ Rx x₀ := by
              have hm' : Event.resp q' y' res ∈ History.procSubhistory (Rx x₀) q := by
                rw [hR_eq]; exact List.mem_cons_self
              exact (List.mem_filter.mp hm').1
            exact hRx_obj x₀ _ hm
          subst hq' hy'
          rw [hR_eq, hcs]
          have hpair := History.isSequential_append_pair
            (History.isSequential_flatMap_toEvents cs)
            (by rw [History.length_flatMap_toEvents]; omega) q' y' op res
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using hpair
      · simp only [hx₀, ↓reduceIte, List.append_nil]; exact hp_seq
  -- Extract per-process completed call sequences of `H'`
  have hpCalls_ex : ∀ p : P, ∃ cs : List (OpCall P Op Resp),
      History.complete (History.procSubhistory H' p) = cs.flatMap OpCall.toEvents ∧
      ∀ c ∈ cs, c.proc = p := by
    intro p
    obtain ⟨hseq_cp, hev_cp⟩ := History.complete_isSequential (hwf' p)
    obtain ⟨cs, hcs⟩ := History.exists_calls_of_isSequential_even hseq_cp hev_cp
    refine ⟨cs, hcs, fun c hc => ?_⟩
    have hinv_mem : Event.inv c.proc c.obj c.op ∈ cs.flatMap OpCall.toEvents :=
      List.mem_flatMap.mpr ⟨c, hc, List.mem_cons_self⟩
    rw [← hcs] at hinv_mem
    have hmem_p := complete_mem_sub hinv_mem
    exact of_decide_eq_true (List.mem_filter.mp hmem_p).2
  choose pCalls hpCalls_eq hpCalls_proc using hpCalls_ex
  have hcomp_op_iff : ∀ e : OpId P,
      History.IsCompletedOp H' e ↔ e.idx < (pCalls e.proc).length := by
    intro e
    rw [← isCompletedOp_complete_iff hwf', History.isCompletedOp_iff_lt_length,
      History.procSubhistory_complete, hpCalls_eq e.proc, History.length_flatMap_toEvents]
    omega
  -- Extract per-object sequential call sequences of `Sx x`
  have hSxCalls_ex : ∀ x : Obj, ∃ cs : List (OpCall P Op Resp),
      Sx x = cs.flatMap OpCall.toEvents := by
    intro x
    have hev_Sx := History.even_length_of_equivalent_complete (hwf_x x) (hSx_seq x) (heq_x x)
    exact History.exists_calls_of_isSequential_even (hSx_seq x) hev_Sx
  choose callsX hSx_eq using hSxCalls_ex
  let α := { e : OpId P // History.IsCompletedOp H' e }
  let callOf : α → OpCall P Op Resp := fun a =>
    (pCalls a.1.proc)[a.1.idx]'((hcomp_op_iff a.1).mp a.2)
  have hcallOf_proc : ∀ a : α, (callOf a).proc = a.1.proc :=
    fun a => hpCalls_proc a.1.proc (callOf a) (List.getElem_mem _)
  let localOp : α → OpId P := fun a =>
    ⟨a.1.proc, countObjCalls (callOf a).obj ((pCalls a.1.proc).take a.1.idx)⟩
  have hlift_localOp : ∀ a : α,
      liftOp H' (callOf a).obj (localOp a) = a.1 ∧
      History.IsCompletedOp (History.objSubhistory H' (callOf a).obj) (localOp a) := by
    intro a
    have hk : a.1.idx < (pCalls a.1.proc).length := (hcomp_op_iff a.1).mp a.2
    obtain ⟨hno_even, hno_odd⟩ := nthObjPos_flatMap_toEvents (pCalls a.1.proc) a.1.idx hk
    rw [← hpCalls_eq a.1.proc] at hno_even hno_odd
    have hlift : liftOp H' (callOf a).obj (localOp a) = a.1 := by
      simp only [liftOp, localOp, callOf]
      rw [hno_even]
      ext
      · rfl
      · dsimp only; omega
    have hcomp_loc : History.IsCompletedOp
        (History.objSubhistory H' (callOf a).obj) (localOp a) := by
      have hodd_H' := nthObjPos_complete_eq (hwf' a.1.proc) hno_odd
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp a.2
      obtain ⟨_, hr_proj⟩ := nthProcPos_objSubhistory_eq hodd_H' hr
      simp only [History.IsCompletedOp, History.respPos, localOp, callOf]
      rw [hr_proj]; rfl
    exact ⟨hlift, hcomp_loc⟩
  have hlocalOp_Sx : ∀ a : α, History.IsCompletedOp (Sx (callOf a).obj) (localOp a) := by
    intro a
    have hc_H'x := (hlift_localOp a).2
    rw [hH'_obj] at hc_H'x
    have hc_comp := (isCompletedOp_complete_iff (hwf_x (callOf a).obj) (localOp a)).mpr hc_H'x
    exact ((heq_x (callOf a).obj).isCompletedOp_iff (localOp a)).mp hc_comp
  let rt : α → α → Prop := fun a b => History.prec H' a.1 b.1
  let loc : α → α → Prop := fun a b =>
    (callOf a).obj = (callOf b).obj ∧ History.prec (Sx (callOf a).obj) (localOp a) (localOp b)
  have hacyc : Acyclic (loc ⊔ rt) := by
    refine acyclic_sup_of_isIntervalOrder (fun a => (callOf a).obj) loc rt
      (History.isIntervalOrder_prec_completed H')
      (fun a h => History.prec_irrefl _ _ h.2)
      (fun hab hbc => ⟨hab.1.trans hbc.1,
        History.prec_trans hab.2 (by rw [hab.1]; exact hbc.2)⟩)
      (fun hab => hab.1)
      (fun {a b} hobj hrt => ⟨hobj, ?_⟩)
    obtain ⟨hlift_a, hc_ax⟩ := hlift_localOp a
    obtain ⟨hlift_b, hc_bx⟩ := hlift_localOp b
    rw [← hobj] at hlift_b hc_bx
    have hpr_H'x :
        History.prec (History.objSubhistory H' (callOf a).obj) (localOp a) (localOp b) := by
      refine (prec_objSubhistory_iff hwf' hc_ax hc_bx).mpr ?_
      rwa [hlift_a, hlift_b]
    rw [hH'_obj] at hpr_H'x hc_ax hc_bx
    have hpr_Hx : History.prec (History.objSubhistory H (callOf a).obj) (localOp a) (localOp b) :=
      (History.prec_append_resp_iff (hwf.objSubhistory (callOf a).obj) (hRx_resp _)
        (hwf_x _) hc_bx).mp hpr_H'x
    exact hprec_x (callOf a).obj (localOp a) (localOp b) hc_ax hc_bx hpr_Hx
  -- Enumerate all elements of `α` without duplicates
  let procs := (H'.map Event.proc).dedup
  have hprocs_nd : procs.Nodup := List.nodup_dedup _
  let elems : List α := procs.flatMap fun p =>
    (List.finRange (pCalls p).length).map fun k => ⟨⟨p, k.1⟩, (hcomp_op_iff ⟨p, k.1⟩).mpr k.2⟩
  have helems_mem : ∀ a : α, a ∈ elems := by
    intro a
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp a.2
    obtain ⟨hr_lt, hr_proc⟩ := History.nthProcPos_lt_length hr
    have hp_in_H' : a.1.proc ∈ H'.map Event.proc := by
      rw [List.getElem?_eq_getElem hr_lt, Option.map_some, Option.some.injEq] at hr_proc
      exact List.mem_map.mpr ⟨H'[r], List.getElem_mem hr_lt, hr_proc⟩
    have hp_in_procs : a.1.proc ∈ procs := List.mem_dedup.mpr hp_in_H'
    rw [List.mem_flatMap]
    refine ⟨a.1.proc, hp_in_procs, List.mem_map.mpr ?_⟩
    refine ⟨⟨a.1.idx, (hcomp_op_iff a.1).mp a.2⟩, List.mem_finRange _, ?_⟩
    ext <;> rfl
  have helems_nd : elems.Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun p _ => ?_, ?_⟩
    · refine List.Nodup.map ?_ (List.nodup_finRange _)
      intro k₁ k₂ h
      have hidx := congrArg (fun a : α => a.1.idx) h
      exact Fin.ext hidx
    · refine hprocs_nd.pairwise_of_forall_ne fun p₁ _ p₂ _ hpne => ?_
      dsimp only [Function.onFun]
      rw [List.disjoint_left]
      intro a ha₁ ha₂
      obtain ⟨k₁, _, rfl⟩ := List.mem_map.mp ha₁
      obtain ⟨k₂, _, heq⟩ := List.mem_map.mp ha₂
      have hp_eq := congrArg (fun x : α => x.1.proc) heq
      exact hpne hp_eq.symm
  obtain ⟨order, hperm, hord_nd, hord_rel⟩ := exists_topoSort_of_acyclic hacyc helems_nd
  have hord_mem : ∀ a : α, a ∈ order := fun a => hperm.mem_iff.mpr (helems_mem a)
  let calls := order.map callOf
  let S := calls.flatMap OpCall.toEvents
  have hS_seq : History.IsSequential S := History.isSequential_flatMap_toEvents calls
  -- Helper showing `(order.filter (proc = p)).map callOf = pCalls p`
  have hord_proc_eq : ∀ p : P,
      (order.filter fun a => decide (a.1.proc = p)).map callOf = pCalls p := by
    intro p
    let ord_p := order.filter fun a => decide (a.1.proc = p)
    obtain ⟨fidx, hfval, hfmono⟩ :=
      filter_strictMono_indices order (fun a => decide (a.1.proc = p))
    refine map_eq_of_strictMono_surj (src := ord_p) (dst := pCalls p)
      (fun a => a.1.idx) callOf ?_ ?_ ?_
    · intro a ha
      have hap : a.1.proc = p := of_decide_eq_true (List.mem_filter.mp ha).2
      have hlt : a.1.idx < (pCalls p).length := by
        rw [← hap]; exact (hcomp_op_iff a.1).mp a.2
      refine ⟨hlt, ?_⟩
      simp only [callOf]
      cases hap
      rfl
    · intro i j hi hj hij
      have hnd_p : ord_p.Nodup := hord_nd.filter _
      have hne_ij : ord_p[i] ≠ ord_p[j] := fun h => by
        have := (List.Nodup.getElem_inj_iff hnd_p).mp h
        omega
      have hp_i : ord_p[i].1.proc = p :=
        of_decide_eq_true (List.mem_filter.mp (List.getElem_mem hi)).2
      have hp_j : ord_p[j].1.proc = p :=
        of_decide_eq_true (List.mem_filter.mp (List.getElem_mem hj)).2
      have hidx_ne : ord_p[i].1.idx ≠ ord_p[j].1.idx := fun h => by
        apply hne_ij
        ext
        · exact hp_i.trans hp_j.symm
        · exact h
      rcases Nat.lt_or_gt_of_ne hidx_ne with hlt | hgt
      · exact hlt
      · exfalso
        have hrt_ji : rt ord_p[j] ord_p[i] :=
          History.prec_of_same_proc_lt (hp_j.trans hp_i.symm) hgt ord_p[j].2 ord_p[i].2
        have hval_i := hfval ⟨i, hi⟩
        have hval_j := hfval ⟨j, hj⟩
        have hrel : TransGen (loc ⊔ rt) order[(fidx ⟨j, hj⟩).1] order[(fidx ⟨i, hi⟩).1] := by
          rw [← hval_i, ← hval_j]
          exact TransGen.single (Or.inr hrt_ji)
        have hji := hord_rel _ _ (fidx ⟨j, hj⟩).2 (fidx ⟨i, hi⟩).2 hrel
        have hij' := hfmono ⟨i, hi⟩ ⟨j, hj⟩ hij
        omega
    · intro k hk
      let a : α := ⟨⟨p, k⟩, (hcomp_op_iff ⟨p, k⟩).mpr hk⟩
      exact ⟨a, List.mem_filter.mpr ⟨hord_mem a, decide_eq_true rfl⟩, rfl⟩
  have heq_S : History.Equivalent (History.complete H') S := by
    intro p
    rw [History.procSubhistory_complete, hpCalls_eq p]
    simp only [S, calls, History.procSubhistory_flatMap_toEvents]
    have hfil_map : (order.map callOf).filter (fun c => decide (c.proc = p)) =
        (order.filter fun a => decide (a.1.proc = p)).map callOf := by
      rw [List.filter_map]
      refine congrArg (fun g => (order.filter g).map callOf) (funext fun a => ?_)
      simp only [Function.comp_apply, hcallOf_proc a]
    rw [hfil_map, hord_proc_eq p]
  -- Prove `opIdAt calls j hj = order[j].1`
  have hopIdAt_order : ∀ (j : ℕ) (hj : j < order.length),
      opIdAt calls j (by simp only [calls, List.length_map]; exact hj) = order[j].1 := by
    intro j hj
    let p := order[j].1.proc
    ext
    · simp only [opIdAt, calls, List.getElem_map, hcallOf_proc]
    · simp only [opIdAt, calls, List.getElem_map, hcallOf_proc]
      -- `((order.map callOf).take j).filter (proc = p)` has length equal to the number of elements
      -- in `order.take j` with `proc = p`. Since `(order.filter (proc = p))` has `idx = 0, 1, ...`,
      -- the elements before `j` with `proc = p` are precisely those with `idx < order[j].1.idx`!
      have hcnt_eq : countProcCalls p ((order.map callOf).take j) =
          ((order.take j).filter fun a => decide (a.1.proc = p)).length := by
        simp only [countProcCalls, ← List.map_take, List.filter_map, List.length_map]
        refine congrArg (fun f => (List.filter f (order.take j)).length) (funext fun a => ?_)
        simp only [Function.comp_apply, hcallOf_proc a]
      rw [hcnt_eq]
      let predP : α → Bool := fun a => decide (a.1.proc = p)
      have hpred_j : predP order[j] = true := decide_eq_true rfl
      obtain ⟨hlt_f, hget_f⟩ := filter_getElem_count_take predP order j hj hpred_j
      have hmap_idx := congrArg (fun l => l[((order.take j).filter predP).length]?)
        (hord_proc_eq p)
      have hlen_ordp : (order.filter predP).length = (pCalls p).length := by
        have := congrArg List.length (hord_proc_eq p)
        simpa only [List.length_map] using this
      -- Even simpler: compare `.idx` on `(order.filter predP).map (·.1.idx) = List.range ...`!
      -- Wait: `(order.filter predP)[k].1.idx = k` because earlier we showed `pos src[i] = i`!
      have hidx_eq : ∀ (u : ℕ) (hu : u < (order.filter predP).length),
          (order.filter predP)[u].1.idx = u := by
        obtain ⟨fidx, hfval, hfmono⟩ := filter_strictMono_indices order predP
        have hrange : (order.filter predP).map (fun a => a.1.idx) =
            List.range (pCalls p).length := by
          rw [List.range_eq_range']
          refine strictMono_list_eq_range' (pCalls p).length 0 _ ?_ ?_ ?_
          · rw [List.pairwise_iff_getElem]
            intro i₁ i₂ hi₁ hi₂ hi₁₂
            simp only [List.length_map] at hi₁ hi₂
            simp only [List.getElem_map]
            have hnd_p : (order.filter predP).Nodup := hord_nd.filter _
            have hne_12 : (order.filter predP)[i₁] ≠ (order.filter predP)[i₂] := fun h => by
              have := (List.Nodup.getElem_inj_iff hnd_p).mp h; omega
            have hp₁ : (order.filter predP)[i₁].1.proc = p :=
              of_decide_eq_true (List.mem_filter.mp (List.getElem_mem hi₁)).2
            have hp₂ : (order.filter predP)[i₂].1.proc = p :=
              of_decide_eq_true (List.mem_filter.mp (List.getElem_mem hi₂)).2
            have hne_idx : (order.filter predP)[i₁].1.idx ≠ (order.filter predP)[i₂].1.idx :=
              fun h => hne_12 (Subtype.ext (OpId.ext (hp₁.trans hp₂.symm) h))
            rcases Nat.lt_or_gt_of_ne hne_idx with hlt | hgt
            · exact hlt
            · exfalso
              have hrt := History.prec_of_same_proc_lt (hp₂.trans hp₁.symm) hgt
                (order.filter predP)[i₂].2 (order.filter predP)[i₁].2
              have hrel : TransGen (loc ⊔ rt) order[(fidx ⟨i₂, hi₂⟩).1]
                  order[(fidx ⟨i₁, hi₁⟩).1] := by
                rw [← hfval ⟨i₁, hi₁⟩, ← hfval ⟨i₂, hi₂⟩]
                exact TransGen.single (Or.inr hrt)
              have := hord_rel _ _ (fidx ⟨i₂, hi₂⟩).2 (fidx ⟨i₁, hi₁⟩).2 hrel
              have := hfmono ⟨i₁, hi₁⟩ ⟨i₂, hi₂⟩ hi₁₂
              omega
          · intro v hv
            obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
            have hap : a.1.proc = p := of_decide_eq_true (List.mem_filter.mp ha).2
            have hlt : a.1.idx < (pCalls p).length := by
              rw [← hap]; exact (hcomp_op_iff a.1).mp a.2
            exact ⟨Nat.zero_le _, by omega⟩
          · intro k _ hk
            let a : α := ⟨⟨p, k⟩, (hcomp_op_iff ⟨p, k⟩).mpr (by dsimp only; omega)⟩
            exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hord_mem a, decide_eq_true rfl⟩)
        intro u hu
        have hget := congrArg (fun l => l[u]?) hrange
        have hu' : u < (pCalls p).length := by rw [← hlen_ordp]; exact hu
        simp only [List.getElem?_map, List.getElem?_eq_getElem hu, Option.map_some,
          List.getElem?_range hu', Option.some.injEq] at hget
        exact hget
      have h := hidx_eq ((order.take j).filter predP).length hlt_f
      rw [hget_f] at h
      exact h.symm
  -- Legality of `S`: for each object `x`, `objSubhistory S x = Sx x ∈ (spec x).allowed`
  have hS_leg : History.IsLegal spec S := by
    intro x
    have hfil_obj : History.objSubhistory S x =
        ((order.filter fun a => decide ((callOf a).obj = x)).map callOf).flatMap
          OpCall.toEvents := by
      simp only [S, calls, History.objSubhistory_flatMap_toEvents, List.filter_map]
      rfl
    rw [hfil_obj]
    let ord_x := order.filter fun a => decide ((callOf a).obj = x)
    obtain ⟨fidx, hfval, hfmono⟩ :=
      filter_strictMono_indices order (fun a => decide ((callOf a).obj = x))
    have hlocal_in_callsX : ∀ a : α, (callOf a).obj = x →
        (localOp a).idx < countProcCalls (localOp a).proc (callsX x) := by
      intro a hax
      have hc_Sx : History.IsCompletedOp (Sx x) (localOp a) := by
        rw [← hax]; exact hlocalOp_Sx a
      have hlen := (History.isCompletedOp_iff_lt_length _ (localOp a)).mp hc_Sx
      rw [hSx_eq x, History.procSubhistory_flatMap_toEvents,
        History.length_flatMap_toEvents] at hlen
      simp only [countProcCalls]; omega
    let posInSx : α → ℕ := fun a =>
      if hax : (callOf a).obj = x then
        (exists_opIdAt_of_lt_countProcCalls (callsX x) (localOp a)
          (hlocal_in_callsX a hax)).choose
      else 0
    have hposInSx_spec : ∀ a : α, (hax : (callOf a).obj = x) →
        ∃ hj : posInSx a < (callsX x).length,
          opIdAt (callsX x) (posInSx a) hj = localOp a := by
      intro a hax
      simp only [posInSx, hax, ↓reduceDIte]
      exact (exists_opIdAt_of_lt_countProcCalls (callsX x) (localOp a)
        (hlocal_in_callsX a hax)).choose_spec
    have hord_x_eq : ord_x.map callOf = callsX x := by
      refine map_eq_of_strictMono_surj (src := ord_x) (dst := callsX x)
        posInSx callOf ?_ ?_ ?_
      · intro a ha
        have hax : (callOf a).obj = x := of_decide_eq_true (List.mem_filter.mp ha).2
        obtain ⟨hj, hop_eq⟩ := hposInSx_spec a hax
        refine ⟨hj, ?_⟩
        -- Both `callOf a` and `(callsX x)[posInSx a]` equal the `(localOp a).idx`-th element of
        -- `((pCalls p).filter (obj = x)) = ((callsX x).filter (proc = p))`!
        let p := a.1.proc
        have hproc_j : (callsX x)[posInSx a].proc = p := by
          have := congrArg OpId.proc hop_eq
          simpa only [opIdAt, localOp] using this
        have hcnt_j : countProcCalls p ((callsX x).take (posInSx a)) = (localOp a).idx := by
          have := congrArg OpId.idx hop_eq
          simpa only [opIdAt, localOp, hproc_j] using this
        obtain ⟨hlt_cx, hget_cx⟩ := filter_getElem_count_take
          (fun c : OpCall P Op Resp => decide (c.proc = p)) (callsX x) (posInSx a) hj
          (decide_eq_true hproc_j)
        have hk_p : a.1.idx < (pCalls p).length := (hcomp_op_iff a.1).mp a.2
        obtain ⟨hlt_pc, hget_pc⟩ := filter_getElem_count_take
          (fun c : OpCall P Op Resp => decide (c.obj = x)) (pCalls p) a.1.idx hk_p
          (decide_eq_true hax)
        have hlists_eq :
            ((pCalls p).filter fun c => decide (c.obj = x)) =
              ((callsX x).filter fun c => decide (c.proc = p)) := by
          apply flatMap_toEvents_injective
          rw [← History.objSubhistory_flatMap_toEvents, ← hpCalls_eq p,
            ← History.procSubhistory_complete, ← History.procSubhistory_objSubhistory_comm,
            ← History.complete_objSubhistory hwf' x, hH'_obj x, heq_x x p, hSx_eq x,
            History.procSubhistory_flatMap_toEvents]
        have hidx_same :
            (((pCalls p).take a.1.idx).filter fun c => decide (c.obj = x)).length =
              (((callsX x).take (posInSx a)).filter fun c => decide (c.proc = p)).length := by
          have h₁ : (((pCalls p).take a.1.idx).filter fun c => decide (c.obj = x)).length =
              (localOp a).idx := by
            dsimp only [localOp, countObjCalls]
            rw [hax]
          have h₂ : (((callsX x).take (posInSx a)).filter fun c => decide (c.proc = p)).length =
              (localOp a).idx := hcnt_j
          exact h₁.trans h₂.symm
        have hget_opt :
            ((pCalls p).filter fun c => decide (c.obj = x))[
              (((pCalls p).take a.1.idx).filter fun c => decide (c.obj = x)).length]? =
            ((callsX x).filter fun c => decide (c.proc = p))[
              (((callsX x).take (posInSx a)).filter fun c => decide (c.proc = p)).length]? := by
          rw [hlists_eq, hidx_same]
        rw [List.getElem?_eq_getElem hlt_pc, List.getElem?_eq_getElem hlt_cx, Option.some.injEq]
          at hget_opt
        rw [hget_pc, hget_cx] at hget_opt
        exact hget_opt
      · intro i j hi hj hij
        have hnd_x : ord_x.Nodup := hord_nd.filter _
        have hne_ij : ord_x[i] ≠ ord_x[j] := fun h => by
          have := (List.Nodup.getElem_inj_iff hnd_x).mp h; omega
        have hx_i : (callOf ord_x[i]).obj = x :=
          of_decide_eq_true (List.mem_filter.mp (List.getElem_mem hi)).2
        have hx_j : (callOf ord_x[j]).obj = x :=
          of_decide_eq_true (List.mem_filter.mp (List.getElem_mem hj)).2
        obtain ⟨hj_i, hop_i⟩ := hposInSx_spec ord_x[i] hx_i
        obtain ⟨hj_j, hop_j⟩ := hposInSx_spec ord_x[j] hx_j
        have hpos_ne : posInSx ord_x[i] ≠ posInSx ord_x[j] := by
          intro hpeq
          have hloc_eq : localOp ord_x[i] = localOp ord_x[j] := by
            rw [← hop_i, ← hop_j]; congr 1
          have hlift_i := (hlift_localOp ord_x[i]).1
          have hlift_j := (hlift_localOp ord_x[j]).1
          rw [hx_i] at hlift_i; rw [hx_j, ← hloc_eq] at hlift_j
          apply hne_ij
          exact Subtype.ext (hlift_i.symm.trans hlift_j)
        rcases Nat.lt_or_gt_of_ne hpos_ne with hlt | hgt
        · exact hlt
        · exfalso
          have hpr_ji : History.prec (Sx x) (localOp ord_x[j]) (localOp ord_x[i]) := by
            rw [hSx_eq x, ← hop_j, ← hop_i]
            exact (prec_flatMap_toEvents_opIdAt_iff (callsX x) hj_j hj_i).mpr hgt
          have hloc_ji : loc ord_x[j] ord_x[i] := by
            refine ⟨hx_j.trans hx_i.symm, ?_⟩
            rwa [hx_j]
          have hrel : TransGen (loc ⊔ rt) order[(fidx ⟨j, hj⟩).1] order[(fidx ⟨i, hi⟩).1] := by
            rw [← hfval ⟨i, hi⟩, ← hfval ⟨j, hj⟩]
            exact TransGen.single (Or.inl hloc_ji)
          have hji := hord_rel _ _ (fidx ⟨j, hj⟩).2 (fidx ⟨i, hi⟩).2 hrel
          have hij' := hfmono ⟨i, hi⟩ ⟨j, hj⟩ hij
          omega
      · intro k hk
        let e_x := opIdAt (callsX x) k hk
        have hc_Sx_k : History.IsCompletedOp (Sx x) e_x := by
          rw [hSx_eq x, History.IsCompletedOp, (invPos_respPos_opIdAt (callsX x) k hk).2]
          rfl
        have hc_H'x_k : History.IsCompletedOp (History.objSubhistory H' x) e_x := by
          rw [hH'_obj x]
          exact (isCompletedOp_complete_iff (hwf_x x) e_x).mp
            (((heq_x x).isCompletedOp_iff e_x).mpr hc_Sx_k)
        obtain ⟨hc_H'_k, hproc_k, ⟨i_pos, hi_pos, hi_obj, _⟩, _⟩ := liftOp_spec hwf' hc_H'x_k
        let a : α := ⟨liftOp H' x e_x, hc_H'_k⟩
        -- Show `(callOf a).obj = x` and `localOp a = e_x`
        have hlen_x : 2 * e_x.idx + 1 <
            (History.objSubhistory (History.procSubhistory H' e_x.proc) x).length := by
          rw [← History.procSubhistory_objSubhistory_comm]
          exact (History.isCompletedOp_iff_lt_length _ _).mp hc_H'x_k
        obtain ⟨m_odd, hm_odd⟩ := Option.isSome_iff_exists.mp
          ((nthObjPos_isSome_iff x _ _).mpr hlen_x)
        obtain ⟨k_glob, rfl, hk₀_glob⟩ := nthObjPos_pair_of_isSequential (hwf' e_x.proc) hm_odd
        obtain ⟨_, heq_even_fn⟩ :=
          nthObjPos_eq_complete_of_odd (x := x) (hwf' e_x.proc) (k_x := e_x.idx)
        have hk₀_comp :
            nthObjPos x (History.complete (History.procSubhistory H' e_x.proc)) (2 * e_x.idx) =
              some (2 * k_glob) := by
          rw [← heq_even_fn (2 * k_glob + 1) hm_odd]; exact hk₀_glob
        have ha_eq : a.1 = ⟨e_x.proc, k_glob⟩ := by
          simp only [a, liftOp, hk₀_comp]
          ext
          · rfl
          · dsimp only; omega
        have ha_proc : a.1.proc = e_x.proc := by rw [ha_eq]
        have ha_idx : a.1.idx = k_glob := by rw [ha_eq]
        have hax : (callOf a).obj = x := by
          have hk_lt : k_glob < (pCalls e_x.proc).length := by
            have := (hcomp_op_iff a.1).mp a.2
            rwa [ha_eq] at this
          rw [hpCalls_eq e_x.proc] at hk₀_comp
          obtain ⟨_, hobj_2k⟩ := nthObjPos_lt_length hk₀_comp
          have hget_even : ∀ (cs : List (OpCall P Op Resp)) (kg : ℕ) (hkg : kg < cs.length),
              (cs.flatMap OpCall.toEvents)[2 * kg]? =
                some (.inv cs[kg].proc cs[kg].obj cs[kg].op) := by
            intro cs
            induction cs with
            | nil => intro _ hkg; simp only [List.length_nil] at hkg; omega
            | cons c rest ih =>
              intro kg hkg
              cases kg with
              | zero =>
                simp only [Nat.mul_zero, List.flatMap_cons, OpCall.toEvents, List.cons_append,
                  List.getElem?_cons_zero, List.getElem_cons_zero]
              | succ kg' =>
                have hkg' : kg' < rest.length := by simp only [List.length_cons] at hkg; omega
                have h2 : 2 * (kg' + 1) = (2 * kg') + 1 + 1 := by omega
                rw [h2]
                simp only [List.flatMap_cons, OpCall.toEvents, List.cons_append, List.nil_append,
                  List.getElem?_cons_succ, List.getElem_cons_succ, ih kg' hkg']
          rw [hget_even (pCalls e_x.proc) k_glob hk_lt, Option.map_some, Event.obj_inv,
            Option.some.injEq] at hobj_2k
          have hcall_eq : some (callOf a) = some (pCalls e_x.proc)[k_glob] := by
            rw [← List.getElem?_eq_getElem ((hcomp_op_iff a.1).mp a.2),
              ← List.getElem?_eq_getElem hk_lt, ha_proc, ha_idx]
          injection hcall_eq with hc_eq
          rw [hc_eq, hobj_2k]
        have hloc_eq_ex : localOp a = e_x := by
          have hk_lt : a.1.idx < (pCalls a.1.proc).length := (hcomp_op_iff a.1).mp a.2
          obtain ⟨hno_ev, _⟩ := nthObjPos_flatMap_toEvents (pCalls a.1.proc) a.1.idx hk_lt
          change nthObjPos (callOf a).obj ((pCalls a.1.proc).flatMap OpCall.toEvents)
            (2 * (localOp a).idx) = some (2 * a.1.idx) at hno_ev
          rw [hax, ← hpCalls_eq a.1.proc, ha_proc, ha_idx] at hno_ev
          have h2eq := History.nthFilterPos_inj hno_ev hk₀_comp
          ext
          · exact ha_proc
          · omega
        obtain ⟨hj_a, hop_a⟩ := hposInSx_spec a hax
        rw [hloc_eq_ex] at hop_a
        have hpos_eq : posInSx a = k := opIdAt_injective hj_a hk hop_a
        exact ⟨a, List.mem_filter.mpr ⟨hord_mem a, decide_eq_true hax⟩, hpos_eq⟩
    rw [hord_x_eq, ← hSx_eq x]
    exact hSx_leg x
  -- Finally, L2 (`H.prec e₀ e₁ → S.prec e₀ e₁`)
  refine ⟨H', ⟨R, hR_resp, rfl, hwf'⟩, S, hS_seq, hS_leg, heq_S, ?_⟩
  intro e₀ e₁ hc₀ hc₁ hpr_H
  have hpr_H' : History.prec H' e₀ e₁ :=
    (History.prec_append_resp_iff hwf hR_resp hwf' hc₁).mpr hpr_H
  let a₀ : α := ⟨e₀, hc₀⟩
  let a₁ : α := ⟨e₁, hc₁⟩
  obtain ⟨i₀, hi₀, ha₀_eq⟩ := List.getElem_of_mem (hord_mem a₀)
  obtain ⟨i₁, hi₁, ha₁_eq⟩ := List.getElem_of_mem (hord_mem a₁)
  have hrel : TransGen (loc ⊔ rt) order[i₀] order[i₁] := by
    rw [ha₀_eq, ha₁_eq]
    exact TransGen.single (Or.inr hpr_H')
  have hlt_01 : i₀ < i₁ := hord_rel i₀ i₁ hi₀ hi₁ hrel
  have hi₀_c : i₀ < calls.length := by simp only [calls, List.length_map]; exact hi₀
  have hi₁_c : i₁ < calls.length := by simp only [calls, List.length_map]; exact hi₁
  have hpr_S := (prec_flatMap_toEvents_opIdAt_iff calls hi₀_c hi₁_c).mpr hlt_01
  rw [hopIdAt_order i₀ hi₀, hopIdAt_order i₁ hi₁, ha₀_eq, ha₁_eq] at hpr_S
  exact hpr_S

/-! ### Incremental extension lemmas and Herlihy–Wing Theorem 2 (Nonblocking) -/

/-- Appending a new invocation `Event.inv p x op` for an idle process `p` (whose subhistory in `H`
consists solely of completed calls `cs_p` and has no pending response in `R`) preserves
well-formedness of `(H ++ [Event.inv p x op]) ++ R`, leaves `complete` unchanged, and preserves
real-time precedence into `S`. -/
theorem History.append_pending_inv_extension {P Obj : Type*} {Op Resp : Obj → Type*}
    [DecidableEq P] {H R S : History P Op Resp} {p : P} {x : Obj} (op : Op x)
    {cs_p : List (OpCall P Op Resp)}
    (hwf' : History.WellFormed (H ++ R))
    (heqS : History.Equivalent (History.complete (H ++ R)) S)
    (hprecS : ∀ e₀ e₁, History.IsCompletedOp (H ++ R) e₀ →
      History.IsCompletedOp (H ++ R) e₁ → History.prec H e₀ e₁ → History.prec S e₀ e₁)
    (hHp : History.procSubhistory H p = cs_p.flatMap OpCall.toEvents)
    (hRp_nil : History.procSubhistory R p = []) :
    let H₁ := H ++ [Event.inv p x op]
    History.WellFormed (H₁ ++ R) ∧
      History.Equivalent (History.complete (H₁ ++ R)) S ∧
      ∀ e₀ e₁, History.IsCompletedOp (H₁ ++ R) e₀ →
        History.IsCompletedOp (H₁ ++ R) e₁ → History.prec H₁ e₀ e₁ → History.prec S e₀ e₁ := by
  intro H₁
  have hwf_H₁R : History.WellFormed (H₁ ++ R) := by
    intro q
    simp only [H₁, List.append_assoc, History.procSubhistory_append, History.procSubhistory_cons,
      Event.proc_inv, History.procSubhistory_nil]
    by_cases hqp : p = q
    · subst hqp
      simp only [↓reduceIte, hRp_nil, List.append_nil, hHp]
      have hseq_inv : ∀ cs : List (OpCall P Op Resp),
          History.IsSequential (cs.flatMap OpCall.toEvents ++ [Event.inv p x op]) := by
        intro cs
        induction cs with
        | nil => trivial
        | cons c rest ih => exact ⟨rfl, rfl, ih⟩
      exact hseq_inv cs_p
    · simp only [hqp, ↓reduceIte, List.nil_append, ← History.procSubhistory_append]
      exact hwf' q
  have hcomp_eq : ∀ q,
      History.procSubhistory (History.complete (H₁ ++ R)) q =
        History.procSubhistory (History.complete (H ++ R)) q := by
    intro q
    rw [History.procSubhistory_complete, History.procSubhistory_complete]
    simp only [H₁, List.append_assoc, History.procSubhistory_append, History.procSubhistory_cons,
      Event.proc_inv, History.procSubhistory_nil]
    by_cases hqp : p = q
    · subst hqp
      simp only [↓reduceIte, hRp_nil, List.append_nil, hHp, complete_flatMap_append_inv]
      exact (History.complete_eq_self_of_isSequential_even
        (History.isSequential_flatMap_toEvents cs_p)
        (by rw [History.length_flatMap_toEvents]; omega)).symm
    · simp only [hqp, ↓reduceIte, List.nil_append]
  have heq_H₁ : History.Equivalent (History.complete (H₁ ++ R)) S :=
    fun q => (hcomp_eq q).trans (heqS q)
  refine ⟨hwf_H₁R, heq_H₁, fun e₀ e₁ hc₀ hc₁ hpr_H₁ => ?_⟩
  have hcomp_eqv : History.Equivalent (History.complete (H₁ ++ R)) (History.complete (H ++ R)) :=
    hcomp_eq
  have hc₀_HR : History.IsCompletedOp (H ++ R) e₀ :=
    (isCompletedOp_complete_iff hwf' e₀).mp
      ((hcomp_eqv.isCompletedOp_iff e₀).mp ((isCompletedOp_complete_iff hwf_H₁R e₀).mpr hc₀))
  have hc₁_HR : History.IsCompletedOp (H ++ R) e₁ :=
    (isCompletedOp_complete_iff hwf' e₁).mp
      ((hcomp_eqv.isCompletedOp_iff e₁).mp ((isCompletedOp_complete_iff hwf_H₁R e₁).mpr hc₁))
  obtain ⟨r₀, i₁, hr₀, hi₁, hri⟩ := hpr_H₁
  -- Show `2 * e₁.idx < (procSubhistory H e₁.proc).length`, so `i₁ < H.length` and `r₀ < H.length`.
  have hlt_i₁ : 2 * e₁.idx < (History.procSubhistory H e₁.proc).length := by
    by_cases hep : e₁.proc = p
    · have hlen := (History.isCompletedOp_iff_lt_length (H ++ R) e₁).mp hc₁_HR
      rw [hep] at hlen ⊢
      rw [History.procSubhistory_append, hRp_nil, List.append_nil] at hlen
      rw [hHp, History.length_flatMap_toEvents] at hlen ⊢
      omega
    · have hinv_some : (History.invPos H₁ e₁).isSome = true := by rw [hi₁]; rfl
      have hlen₁ := (History.nthProcPos_isSome_iff e₁.proc H₁ (2 * e₁.idx)).mp hinv_some
      simpa only [H₁, History.procSubhistory_append, History.procSubhistory_cons, Event.proc_inv,
        Ne.symm hep, ↓reduceIte, History.procSubhistory_nil, List.append_nil] using hlen₁
  have hi₁_H : History.invPos H e₁ = some i₁ := by
    rw [History.invPos, History.nthProcPos_append_left [Event.inv p x op] hlt_i₁] at hi₁
    exact hi₁
  obtain ⟨hi₁_lt_H, _⟩ := History.nthProcPos_lt_length hi₁_H
  have hr₀_H : History.respPos H e₀ = some r₀ :=
    History.nthProcPos_of_append_lt hr₀ (by omega)
  exact hprecS e₀ e₁ hc₀_HR hc₁_HR ⟨r₀, i₁, hr₀_H, hi₁_H, hri⟩

/-- Linearizing an uncompleted pending invocation `Event.inv p x op` of process `p` by appending
`Event.resp p x res` to the response extension `R` and `[Event.inv p x op, Event.resp p x res]` to
the sequential witness `S` preserves well-formedness, sequentiality, equivalence of `complete`, and
real-time precedence `<_H`. -/
theorem History.linearize_pending_in_extension {P Obj : Type*} {Op Resp : Obj → Type*}
    [DecidableEq P] {H R S : History P Op Resp} {p : P} {x : Obj} {op : Op x} (res : Resp x)
    {cs_p : List (OpCall P Op Resp)}
    (hR_resp : History.IsRespList R)
    (hwf' : History.WellFormed (H ++ R))
    (hseqS : History.IsSequential S)
    (heqS : History.Equivalent (History.complete (H ++ R)) S)
    (hprecS : ∀ e₀ e₁, History.IsCompletedOp (H ++ R) e₀ →
      History.IsCompletedOp (H ++ R) e₁ → History.prec H e₀ e₁ → History.prec S e₀ e₁)
    (hHp : History.procSubhistory H p = cs_p.flatMap OpCall.toEvents ++ [Event.inv p x op])
    (hRp_nil : History.procSubhistory R p = []) :
    let R₁ := R ++ [Event.resp p x res]
    let S' := S ++ [Event.inv p x op, Event.resp p x res]
    History.IsRespList R₁ ∧
      History.WellFormed (H ++ R₁) ∧
      History.IsSequential S' ∧
      History.Equivalent (History.complete (H ++ R₁)) S' ∧
      ∀ e₀ e₁, History.IsCompletedOp (H ++ R₁) e₀ →
        History.IsCompletedOp (H ++ R₁) e₁ → History.prec H e₀ e₁ → History.prec S' e₀ e₁ := by
  intro R₁ S'
  have hR₁_resp : History.IsRespList R₁ := by
    intro e hm
    rcases List.mem_append.mp hm with hR | hsingle
    · exact hR_resp e hR
    · simp only [List.mem_singleton] at hsingle
      subst hsingle; rfl
  have hevS := History.even_length_of_equivalent_complete hwf' hseqS heqS
  have hwf_HR₁ : History.WellFormed (H ++ R₁) := by
    intro q
    simp only [R₁, ← List.append_assoc, History.procSubhistory_append, History.procSubhistory_cons,
      Event.proc_resp, History.procSubhistory_nil]
    by_cases hqp : p = q
    · subst hqp
      simp only [↓reduceIte, hRp_nil, List.append_nil, hHp]
      have hpair := History.isSequential_append_pair
        (History.isSequential_flatMap_toEvents cs_p)
        (by rw [History.length_flatMap_toEvents]; omega) p x op res
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hpair
    · simp only [hqp, ↓reduceIte, List.append_nil, ← History.procSubhistory_append]
      exact hwf' q
  have hseqS' : History.IsSequential S' :=
    History.isSequential_append_pair hseqS hevS p x op res
  have heqS' : History.Equivalent (History.complete (H ++ R₁)) S' := by
    intro q
    rw [History.procSubhistory_complete]
    simp only [R₁, S', History.procSubhistory_append, History.procSubhistory_cons,
      Event.proc_inv, Event.proc_resp, History.procSubhistory_nil]
    by_cases hqp : p = q
    · subst hqp
      simp only [↓reduceIte, hRp_nil, List.nil_append, hHp]
      have hpair_seq : History.IsSequential
          (cs_p.flatMap OpCall.toEvents ++ [Event.inv p x op, Event.resp p x res]) := by
        have hp2 := History.isSequential_append_pair
          (History.isSequential_flatMap_toEvents cs_p)
          (by rw [History.length_flatMap_toEvents]; omega) p x op res
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using hp2
      have hpair_ev :
          (cs_p.flatMap OpCall.toEvents ++
            ([Event.inv p x op, Event.resp p x res] : History P Op Resp)).length % 2 = 0 := by
        rw [List.length_append, History.length_flatMap_toEvents, List.length_cons,
          List.length_singleton]
        omega
      have hcomp_L :
          History.complete ((cs_p.flatMap OpCall.toEvents ++ [Event.inv p x op]) ++
              [Event.resp p x res]) =
            cs_p.flatMap OpCall.toEvents ++ [Event.inv p x op, Event.resp p x res] := by
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using
          History.complete_eq_self_of_isSequential_even hpair_seq hpair_ev
      rw [hcomp_L]
      have heq_p := heqS p
      rw [History.procSubhistory_complete, History.procSubhistory_append, hRp_nil,
        List.append_nil, hHp, complete_flatMap_append_inv] at heq_p
      rw [heq_p]
    · simp only [hqp, ↓reduceIte, List.append_nil, ← History.procSubhistory_append,
        ← History.procSubhistory_complete]
      exact heqS q
  refine ⟨hR₁_resp, hwf_HR₁, hseqS', heqS', fun e₀ e₁ _ hc₁ hpr_H => ?_⟩
  obtain ⟨r₀, i₁, hr₀_H, hi₁_H, hri⟩ := hpr_H
  have hc₀_HR : History.IsCompletedOp (H ++ R) e₀ := by
    have hlen_H : 2 * e₀.idx + 1 < (History.procSubhistory H e₀.proc).length :=
      (History.nthProcPos_isSome_iff e₀.proc H (2 * e₀.idx + 1)).mp
        (by rw [← History.respPos, hr₀_H]; rfl)
    rw [History.isCompletedOp_iff_lt_length, History.procSubhistory_append, List.length_append]
    omega
  have hc₀_S : History.IsCompletedOp S e₀ :=
    (heqS.isCompletedOp_iff e₀).mp ((isCompletedOp_complete_iff hwf' e₀).mpr hc₀_HR)
  obtain ⟨rS₀, hrS₀⟩ := Option.isSome_iff_exists.mp hc₀_S
  have hrS₀_S' : History.respPos S' e₀ = some rS₀ := by
    have hlt_S : 2 * e₀.idx + 1 < (History.procSubhistory S e₀.proc).length :=
      (History.isCompletedOp_iff_lt_length S e₀).mp hc₀_S
    rw [History.respPos, History.nthProcPos_append_left _ hlt_S]
    exact hrS₀
  by_cases hc₁_HR : History.IsCompletedOp (H ++ R) e₁
  · obtain ⟨rS, iS, hrS, hiS, hltS⟩ := hprecS e₀ e₁ hc₀_HR hc₁_HR ⟨r₀, i₁, hr₀_H, hi₁_H, hri⟩
    have hc₁_S : History.IsCompletedOp S e₁ :=
      (heqS.isCompletedOp_iff e₁).mp ((isCompletedOp_complete_iff hwf' e₁).mpr hc₁_HR)
    have hlt_iS : 2 * e₁.idx < (History.procSubhistory S e₁.proc).length := by
      have := (History.isCompletedOp_iff_lt_length S e₁).mp hc₁_S; omega
    refine ⟨rS, iS, ?_, ?_, hltS⟩
    · rw [History.respPos, History.nthProcPos_append_left _
        ((History.isCompletedOp_iff_lt_length S e₀).mp hc₀_S)]
      exact hrS
    · rw [History.invPos, History.nthProcPos_append_left _ hlt_iS]
      exact hiS
  · have he₁_p : e₁.proc = p := by
      by_contra hne
      apply hc₁_HR
      rw [History.isCompletedOp_iff_lt_length] at hc₁ ⊢
      simp only [R₁, History.procSubhistory_append, History.procSubhistory_cons, Event.proc_resp,
        Ne.symm hne, ↓reduceIte, History.procSubhistory_nil, List.append_nil] at hc₁
      rwa [History.procSubhistory_append]
    have he₁_idx : e₁.idx = cs_p.length := by
      have hlen₁ := (History.isCompletedOp_iff_lt_length _ e₁).mp hc₁
      have hlen₀ : ¬ (2 * e₁.idx + 1 < (History.procSubhistory (H ++ R) e₁.proc).length) :=
        fun h => hc₁_HR ((History.isCompletedOp_iff_lt_length _ e₁).mpr h)
      rw [he₁_p, History.procSubhistory_append, hRp_nil, List.append_nil, hHp,
        List.length_append, History.length_flatMap_toEvents, List.length_singleton] at hlen₀
      simp only [R₁, he₁_p, History.procSubhistory_append, hRp_nil, List.nil_append, hHp,
        History.procSubhistory_cons, Event.proc_resp, ↓reduceIte, History.procSubhistory_nil,
        List.length_append, History.length_flatMap_toEvents, List.length_cons,
        List.length_nil] at hlen₁
      omega
    have hSp_len : (History.procSubhistory S p).length = 2 * cs_p.length := by
      rw [← heqS p, History.procSubhistory_complete, History.procSubhistory_append,
        hRp_nil, List.append_nil, hHp, complete_flatMap_append_inv,
        History.length_flatMap_toEvents]
    have hiS' : History.invPos S' e₁ = some S.length := by
      simp only [S', History.invPos, he₁_p, he₁_idx]
      rw [History.nthProcPos_append_right S _ (by rw [hSp_len]), hSp_len, Nat.sub_self]
      simp only [History.nthProcPos, Event.proc_inv, ↓reduceIte, Option.map_some, Nat.zero_add]
    obtain ⟨hrS₀_lt, _⟩ := History.nthProcPos_lt_length hrS₀
    exact ⟨rS₀, S.length, hrS₀_S', hiS', hrS₀_lt⟩

/-- Moving an already-linearized pending response `Event.resp p x res` of process `p` from the
extension `R` into `H₁ := H ++ [Event.resp p x res]` (leaving `R' := R.filter (·.proc ≠ p)`)
preserves every process subhistory of `H₁ ++ R'` and maintains real-time precedence into `S`. -/
theorem History.flush_resp_from_extension {P Obj : Type*} {Op Resp : Obj → Type*}
    [DecidableEq P] {H R S : History P Op Resp} {p : P} {x : Obj} {res : Resp x}
    (hR_resp : History.IsRespList R)
    (hwf' : History.WellFormed (H ++ R))
    (heqS : History.Equivalent (History.complete (H ++ R)) S)
    (hprecS : ∀ e₀ e₁, History.IsCompletedOp (H ++ R) e₀ →
      History.IsCompletedOp (H ++ R) e₁ → History.prec H e₀ e₁ → History.prec S e₀ e₁)
    (hRp_eq : History.procSubhistory R p = [Event.resp p x res]) :
    let H₁ := H ++ [Event.resp p x res]
    let R' := R.filter fun e => decide (e.proc ≠ p)
    History.IsRespList R' ∧
      (∀ q, History.procSubhistory (H₁ ++ R') q = History.procSubhistory (H ++ R) q) ∧
      History.WellFormed (H₁ ++ R') ∧
      History.Equivalent (History.complete (H₁ ++ R')) S ∧
      ∀ e₀ e₁, History.IsCompletedOp (H₁ ++ R') e₀ →
        History.IsCompletedOp (H₁ ++ R') e₁ → History.prec H₁ e₀ e₁ → History.prec S e₀ e₁ := by
  intro H₁ R'
  have hR'_resp : History.IsRespList R' :=
    fun e hm => hR_resp e (List.mem_filter.mp hm).1
  have hproc_eq_all : ∀ q, History.procSubhistory (H₁ ++ R') q =
      History.procSubhistory (H ++ R) q := by
    intro q
    simp only [H₁, R', List.append_assoc, History.procSubhistory_append,
      History.procSubhistory_cons, Event.proc_resp, History.procSubhistory_nil]
    by_cases hqp : p = q
    · subst hqp
      have hR'_nil : History.procSubhistory (R.filter fun e => decide (e.proc ≠ p)) p = [] := by
        rw [History.procSubhistory, List.filter_filter, List.filter_eq_nil_iff]
        intro e _ hboth
        obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hboth
        exact (of_decide_eq_true h2) (of_decide_eq_true h1)
      simp only [↓reduceIte, hR'_nil, List.append_nil, hRp_eq]
    · have hR'_q : History.procSubhistory (R.filter fun e => decide (e.proc ≠ p)) q =
          History.procSubhistory R q := by
        simp only [History.procSubhistory, List.filter_filter]
        refine congrArg (List.filter · R) (funext fun e => ?_)
        by_cases heq_q : e.proc = q
        · have hqp' : q ≠ p := Ne.symm hqp
          simp only [heq_q, decide_eq_true hqp', Bool.and_true]
        · simp only [heq_q, decide_false, Bool.false_and]
      simp only [hqp, ↓reduceIte, List.nil_append, hR'_q]
  have hwf_H₁R' : History.WellFormed (H₁ ++ R') := by
    intro q; rw [hproc_eq_all q]; exact hwf' q
  have heq_H₁R' : History.Equivalent (History.complete (H₁ ++ R')) S := by
    intro q
    rw [History.procSubhistory_complete, hproc_eq_all q, ← History.procSubhistory_complete]
    exact heqS q
  refine ⟨hR'_resp, hproc_eq_all, hwf_H₁R', heq_H₁R', fun e₀ e₁ hc₀ hc₁ hpr_H₁ => ?_⟩
  have hc₀_HR : History.IsCompletedOp (H ++ R) e₀ := by
    rw [History.isCompletedOp_iff_lt_length, ← hproc_eq_all e₀.proc]
    exact (History.isCompletedOp_iff_lt_length _ e₀).mp hc₀
  have hc₁_HR : History.IsCompletedOp (H ++ R) e₁ := by
    rw [History.isCompletedOp_iff_lt_length, ← hproc_eq_all e₁.proc]
    exact (History.isCompletedOp_iff_lt_length _ e₁).mp hc₁
  have hwf_H₁ : History.WellFormed H₁ := fun q => by
    have hq := hwf_H₁R' q
    rw [History.procSubhistory_append] at hq
    exact isSequential_append_left hq
  have hpr_H : History.prec H e₀ e₁ := by
    obtain ⟨r₀, i₁, hr₀, hi₁, hri⟩ := hpr_H₁
    have hi₁_lt : i₁ < H.length := by
      obtain ⟨hlt_H₁, _⟩ := History.nthProcPos_lt_length hi₁
      dsimp only [H₁] at hlt_H₁
      rw [List.length_append, List.length_singleton] at hlt_H₁
      by_cases heq_len : i₁ = H.length
      · exfalso
        have hget : H₁[H.length]? = some (.resp p x res) := by
          simp only [H₁, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
            List.getElem?_cons_zero]
        have hseq_q := hwf_H₁ e₁.proc
        have hev_eq := History.nthProcPos_getElem? hi₁
        rw [heq_len, hget] at hev_eq
        have his_inv : ∀ (k : ℕ) (L : History P Op Resp) (ev : Event P Op Resp),
            History.IsSequential L → L[2 * k]? = some ev → ev.isResp = false := by
          intro k
          induction k with
          | zero =>
            intro L ev hseqL hLk
            match L with
            | [] => simp only [List.getElem?_nil, reduceCtorEq] at hLk
            | [.inv _ _ _] =>
              simp only [Nat.mul_zero, List.getElem?_cons_zero, Option.some.injEq] at hLk
              rw [← hLk]; rfl
            | [.resp _ _ _] => exact False.elim hseqL
            | .inv _ _ _ :: .inv _ _ _ :: _ => exact False.elim hseqL
            | .resp _ _ _ :: _ :: _ => exact False.elim hseqL
            | .inv _ _ _ :: .resp _ _ _ :: _ =>
              simp only [Nat.mul_zero, List.getElem?_cons_zero, Option.some.injEq] at hLk
              rw [← hLk]; rfl
          | succ k' ihk =>
            intro L ev hseqL hLk
            match L with
            | [] => simp only [List.getElem?_nil, reduceCtorEq] at hLk
            | [.inv _ _ _] =>
              have h2 : 2 * (k' + 1) = (2 * k' + 1) + 1 := by omega
              rw [h2] at hLk
              simp only [List.getElem?_cons_succ, List.getElem?_nil, reduceCtorEq] at hLk
            | [.resp _ _ _] => exact False.elim hseqL
            | .inv _ _ _ :: .inv _ _ _ :: _ => exact False.elim hseqL
            | .resp _ _ _ :: _ :: _ => exact False.elim hseqL
            | .inv _ _ _ :: .resp _ _ _ :: rs =>
              have h2 : 2 * (k' + 1) = (2 * k') + 1 + 1 := by omega
              rw [h2] at hLk
              simp only [List.getElem?_cons_succ] at hLk
              exact ihk rs ev hseqL.2.2 hLk
        have hfalse := his_inv e₁.idx _ (.resp p x res) hseq_q hev_eq.symm
        exact Bool.noConfusion hfalse
      · omega
    have hr₀_lt : r₀ < H.length := by omega
    exact ⟨r₀, i₁, History.nthProcPos_of_append_lt hr₀ hr₀_lt,
      History.nthProcPos_of_append_lt hi₁ hi₁_lt, hri⟩
  exact hprecS e₀ e₁ hc₀_HR hc₁_HR hpr_H

/-- **Herlihy–Wing Theorem 2 (Nonblocking Property of Linearizability)**
([HerlihyWing1990], §3.2, Theorem 2, pp. 471–472; amended L2 proof of [SelaHerlihyPetrank2021],
§5.3, Theorem 5.2, p. 9): if process `p` has a pending invocation of a total operation `op : Op x`
in a linearizable history `H`, then there exists a response `res : Resp x` such that
`H ++ [Event.resp p x res]` is also linearizable. -/
theorem exists_linearizable_append_resp_of_total {P Obj : Type*} {Op Resp : Obj → Type*}
    [DecidableEq P] [DecidableEq Obj] {spec : ∀ y, SeqSpec P Op Resp y}
    {H : History P Op Resp} {p : P} {x : Obj} {op : Op x}
    (hlin : IsLinearizable spec H) (htot : (spec x).IsTotalOp op)
    (hpending : ∃ cs : List (OpCall P Op Resp),
      History.procSubhistory H p = cs.flatMap OpCall.toEvents ++ [.inv p x op]) :
    ∃ res : Resp x, IsLinearizable spec (H ++ [.resp p x res]) := by
  obtain ⟨cs_p, hHp⟩ := hpending
  obtain ⟨H', ⟨R, hR_resp, rfl, hwf'⟩, S, hseqS, hlegS, heqS, hprecS⟩ := hlin
  have hwfH : History.WellFormed H := fun q => by
    have hq := hwf' q
    rw [History.procSubhistory_append] at hq
    exact isSequential_append_left hq
  have hseq_ext_p := hwf' p
  rw [History.procSubhistory_append] at hseq_ext_p
  have hresp_Rp : History.IsRespList (History.procSubhistory R p) :=
    fun e hm => hR_resp e (List.mem_filter.mp hm).1
  rcases History.isRespList_le_one_of_isSequential (hwfH p) hresp_Rp hseq_ext_p with
    hRp_nil | ⟨cs', p', x', op', res, hL_eq, hRp_eq⟩
  · have hev_Sx : (History.objSubhistory S x).length % 2 = 0 := by
      have hevS := History.even_length_of_equivalent_complete hwf' hseqS heqS
      obtain ⟨csS, hcsS⟩ := History.exists_calls_of_isSequential_even hseqS hevS
      rw [hcsS, History.objSubhistory_flatMap_toEvents, History.length_flatMap_toEvents]
      omega
    obtain ⟨res, hSx_ext⟩ := htot (History.objSubhistory S x) (hlegS x) hev_Sx p
    obtain ⟨hR₁_resp, hwf_HR₁, hseqS', heqS', hprecS'⟩ :=
      History.linearize_pending_in_extension res hR_resp hwf' hseqS heqS hprecS hHp hRp_nil
    have hR₁p : History.procSubhistory (R ++ [Event.resp p x res]) p = [Event.resp p x res] := by
      simp only [History.procSubhistory_append, hRp_nil, List.nil_append,
        History.procSubhistory_cons, Event.proc_resp, ↓reduceIte, History.procSubhistory_nil]
    obtain ⟨hR'_resp, _, hwf_fl, heq_fl, hprec_fl⟩ :=
      History.flush_resp_from_extension hR₁_resp hwf_HR₁ heqS' hprecS' hR₁p
    refine ⟨res, _, ⟨_, hR'_resp, rfl, hwf_fl⟩, _, hseqS', ?_, heq_fl, hprec_fl⟩
    intro y
    simp only [History.objSubhistory_append, History.objSubhistory_cons,
      History.objSubhistory_nil, Event.obj_inv, Event.obj_resp]
    by_cases hxy : x = y
    · subst hxy; simp only [↓reduceIte]; exact hSx_ext
    · simp only [hxy, ↓reduceIte, List.append_nil]; exact hlegS y
  · have hp_eq : p' = p := by
      have hm : Event.resp p' x' res ∈ History.procSubhistory R p := by
        rw [hRp_eq]; exact List.mem_cons_self
      exact of_decide_eq_true (List.mem_filter.mp hm).2
    subst hp_eq
    have hlast : (Event.inv p' x' op' : Event P Op Resp) = Event.inv p' x op := by
      have hlen_eq :
          (cs'.flatMap OpCall.toEvents ++ ([Event.inv p' x' op'] : History P Op Resp)) =
            (cs_p.flatMap OpCall.toEvents ++ ([Event.inv p' x op] : History P Op Resp)) := by
        rw [← hL_eq, hHp]
      have hget := congrArg List.getLast? hlen_eq
      simp only [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _), List.getLast?_singleton,
        Option.some.injEq] at hget
      exact hget
    injection hlast with _ hx_eq _
    subst hx_eq
    obtain ⟨hR'_resp, _, hwf_fl, heq_fl, hprec_fl⟩ :=
      History.flush_resp_from_extension hR_resp hwf' heqS hprecS hRp_eq
    exact ⟨res, _, ⟨_, hR'_resp, rfl, hwf_fl⟩, S, hseqS, hlegS, heq_fl, hprec_fl⟩

/-! ### Atomic read/write registers and counterexamples for sequential consistency -/

/-- Operations on an atomic read/write register over value type `V`. -/
inductive RegOp (V : Type*) where
  /-- Read the current register value. -/
  | read
  /-- Write `val` to the register. -/
  | write (val : V)
  deriving @[expose] DecidableEq

/-- Responses returned by an atomic read/write register over value type `V`. -/
inductive RegResp (V : Type*) where
  /-- Return `val` from a `read`. -/
  | readRet (val : V)
  /-- Acknowledge a completed `write`. -/
  | writeAck
  deriving @[expose] DecidableEq

/-- Sequential transition function of an atomic read/write register. -/
@[expose]
def registerStep {V : Type*} (s : V) : RegOp V → V × RegResp V
  | .read => (s, .readRet s)
  | .write v => (v, .writeAck)

/-- Sequential specification of an atomic read/write register `x : Obj` initialized to `init`. -/
def registerSeqSpec {P Obj V : Type*} (x : Obj) (init : V) :
    SeqSpec P (fun _ : Obj => RegOp V) (fun _ : Obj => RegResp V) x :=
  SeqSpec.ofMachine x init registerStep

private theorem resp_ext_eq_nil_of_even_proc {P Obj : Type*} {Op Resp : Obj → Type*}
    [DecidableEq P] {H R : History P Op Resp} (hwf : History.WellFormed H)
    (hev : ∀ p : P, (History.procSubhistory H p).length % 2 = 0)
    (hrespR : History.IsRespList R) (hwf' : History.WellFormed (H ++ R)) : R = [] := by
  cases R with
  | nil => rfl
  | cons e rs =>
    cases e with
    | inv _ _ _ => exact Bool.noConfusion (hrespR _ List.mem_cons_self)
    | resp p x res =>
      have hp := hwf' p
      rw [History.procSubhistory_append] at hp
      have hresp_p : History.IsRespList (History.procSubhistory (.resp p x res :: rs) p) :=
        fun a ha => hrespR a (List.mem_filter.mp ha).1
      have hnil_p :=
        History.isRespList_eq_nil_of_isSequential_even (hwf p) (hev p) hresp_p hp
      simp only [History.procSubhistory_cons, Event.proc_resp, ↓reduceIte] at hnil_p
      nomatch hnil_p

private theorem filter_proc_bool_length_sum {Obj : Type*} {Op Resp : Obj → Type*}
    (l : List (OpCall Bool Op Resp)) :
    (l.filter fun c => decide (c.proc = false)).length +
      (l.filter fun c => decide (c.proc = true)).length = l.length := by
  have h := List.length_eq_length_filter_add (l := l) (fun c => decide (c.proc = false))
  have hnot : (fun c : OpCall Bool Op Resp => !decide (c.proc = false)) =
      fun c => decide (c.proc = true) := by
    funext c; cases c.proc <;> rfl
  rw [hnot] at h
  exact h.symm

private theorem dekker_write_not_lt_stale_read
    {c0 c1 c2 c3 : OpCall Bool (fun _ : Bool => RegOp Bool) (fun _ : Bool => RegResp Bool)}
    (reg : Bool)
    (hleg : History.objSubhistory ([c0, c1, c2, c3].flatMap OpCall.toEvents) reg ∈
      (registerSeqSpec reg false).allowed)
    {jA0 jA1 jB0 jB1 : ℕ}
    (hjA0 : jA0 < 4) (hjA1 : jA1 < 4) (hjB0 : jB0 < 4) (hjB1 : jB1 < 4)
    (hltA : jA0 < jA1) (hltB : jB0 < jB1)
    (hne00 : jA0 ≠ jB0) (hne01 : jA0 ≠ jB1) (hne10 : jA1 ≠ jB0) (hne11 : jA1 ≠ jB1)
    (eA0 : [c0, c1, c2, c3][jA0] = ⟨reg, reg, .write true, .writeAck⟩)
    (eA1 : [c0, c1, c2, c3][jA1] = ⟨reg, !reg, .read, .readRet false⟩)
    (eB0 : [c0, c1, c2, c3][jB0] = ⟨!reg, !reg, .write true, .writeAck⟩)
    (eB1 : [c0, c1, c2, c3][jB1] = ⟨!reg, reg, .read, .readRet false⟩) :
    ¬ jA0 < jB1 := by
  intro hlt
  rw [History.objSubhistory_flatMap_toEvents] at hleg
  have hne_reg : decide ((!reg) = reg) = false := by cases reg <;> rfl
  have hcases : (jA0 = 0 ∨ jA0 = 1 ∨ jA0 = 2) ∧ (jB1 = 1 ∨ jB1 = 2 ∨ jB1 = 3) ∧
      (jA1 = 1 ∨ jA1 = 2 ∨ jA1 = 3) ∧ (jB0 = 0 ∨ jB0 = 1 ∨ jB0 = 2) := by omega
  rcases hcases with ⟨rfl | rfl | rfl, rfl | rfl | rfl, rfl | rfl | rfl, rfl | rfl | rfl⟩
  all_goals first
    | omega
    | (simp only [List.getElem_cons_zero, List.getElem_cons_succ] at eA0 eA1 eB0 eB1
       rw [eA0, eA1, eB0, eB1] at hleg
       simp only [registerSeqSpec, SeqSpec.mem_ofMachine_allowed, List.filter, hne_reg,
         decide_true, List.flatMap_cons, List.flatMap_nil, OpCall.toEvents,
         List.cons_append, List.nil_append, SeqSpec.evalMachine, registerStep] at hleg
       obtain ⟨_, _, _, _, _, _, _, hbad, _⟩ := hleg
       nomatch hbad)

/-- Original explicit 2-process, 1-register history that is **sequentially consistent** (`B`'s
`read false` can be ordered before `A`'s `write true`) yet **not linearizable** (`A`'s `write true`
completed in real time before `B`'s `read false` was invoked), witnessing the single-object
separation of [HerlihyWing1990], §3.3, p. 472 (register counterpart of queue history `H_7`). -/
theorem exists_sequentiallyConsistent_not_linearizable :
    ∃ H : History Bool (fun _ : Unit => RegOp Bool) (fun _ : Unit => RegResp Bool),
      History.WellFormed H ∧
      IsSequentiallyConsistent (fun x => registerSeqSpec x false) H ∧
      ¬ IsLinearizable (fun x => registerSeqSpec x false) H := by
  let H : History Bool (fun _ : Unit => RegOp Bool) (fun _ : Unit => RegResp Bool) :=
    [.inv false () (.write true), .resp false () .writeAck,
     .inv true () .read, .resp true () (.readRet false)]
  have hwfH : History.WellFormed H := fun b => by cases b <;> trivial
  refine ⟨H, hwfH, ?_, ?_⟩
  · let S : History Bool (fun _ : Unit => RegOp Bool) (fun _ : Unit => RegResp Bool) :=
      [.inv true () .read, .resp true () (.readRet false),
       .inv false () (.write true), .resp false () .writeAck]
    refine ⟨H, History.IsExtension.refl hwfH, S, ⟨rfl, rfl, rfl, rfl, trivial⟩, ?_, ?_⟩
    · intro x; cases x
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
    · intro b; cases b <;> rfl
  · rintro ⟨H', ⟨R, hrespR, rfl, hwf'⟩, S, hseqS, hlegS, heqS, hprecS⟩
    have hR_nil : R = [] :=
      resp_ext_eq_nil_of_even_proc hwfH (fun b => by cases b <;> decide) hrespR hwf'
    subst hR_nil
    rw [List.append_nil] at hwf' heqS hprecS
    have hcF : History.IsCompletedOp H ⟨false, 0⟩ := rfl
    have hcT : History.IsCompletedOp H ⟨true, 0⟩ := rfl
    have hpr_FT : History.prec H ⟨false, 0⟩ ⟨true, 0⟩ := ⟨1, 2, rfl, rfl, by omega⟩
    have hpr_S := hprecS ⟨false, 0⟩ ⟨true, 0⟩ hcF hcT hpr_FT
    have hevS := History.even_length_of_equivalent_complete hwf' hseqS heqS
    obtain ⟨cs, rfl⟩ := History.exists_calls_of_isSequential_even hseqS hevS
    have hlen_cs : cs.length = 2 := by
      have hf := congrArg List.length (heqS false)
      have ht := congrArg List.length (heqS true)
      rw [History.procSubhistory_flatMap_toEvents, History.length_flatMap_toEvents] at hf ht
      have hp_sum := filter_proc_bool_length_sum cs
      have hf_val : (History.procSubhistory (History.complete H) false).length = 2 := rfl
      have ht_val : (History.procSubhistory (History.complete H) true).length = 2 := rfl
      rw [hf_val] at hf; rw [ht_val] at ht
      omega
    match cs, hlen_cs with
    | [c₀, c₁], _ =>
      have hleg0 := hlegS ()
      have hobj_all : ∀ e ∈ ([c₀, c₁] : List _).flatMap OpCall.toEvents, e.obj = () :=
        fun _ _ => rfl
      rw [History.objSubhistory_eq_self_of_forall_obj hobj_all] at hleg0
      cases hp₀ : c₀.proc
      · -- `c₀.proc = false`: then `c₁.proc = true`, so `c₀` writes `true` and `c₁` reads `false`
        cases hp₁ : c₁.proc
        · have ht := heqS true
          simp only [History.procSubhistory_flatMap_toEvents, List.filter, hp₀, hp₁,
            Bool.false_eq_true, decide_false, List.flatMap_nil] at ht
          nomatch ht
        · have hf_eq := heqS false
          have ht_eq := heqS true
          have hf_comp :
              History.procSubhistory (History.complete H) false =
                ([⟨false, (), .write true, .writeAck⟩] :
                  List (OpCall Bool (fun _ : Unit => RegOp Bool)
                    (fun _ : Unit => RegResp Bool))).flatMap OpCall.toEvents := rfl
          have ht_comp :
              History.procSubhistory (History.complete H) true =
                ([⟨true, (), .read, .readRet false⟩] :
                  List (OpCall Bool (fun _ : Unit => RegOp Bool)
                    (fun _ : Unit => RegResp Bool))).flatMap OpCall.toEvents := rfl
          rw [hf_comp, History.procSubhistory_flatMap_toEvents] at hf_eq
          rw [ht_comp, History.procSubhistory_flatMap_toEvents] at ht_eq
          simp only [List.filter, hp₀, hp₁, decide_true, Bool.true_eq_false,
            Bool.false_eq_true, decide_false] at hf_eq ht_eq
          have hc₀_eq := flatMap_toEvents_injective hf_eq
          have hc₁_eq := flatMap_toEvents_injective ht_eq
          injection hc₀_eq with hc₀_val
          injection hc₁_eq with hc₁_val
          rw [← hc₀_val, ← hc₁_val] at hleg0
          simp only [registerSeqSpec, SeqSpec.mem_ofMachine_allowed, List.flatMap_cons,
            List.flatMap_nil, OpCall.toEvents, List.cons_append, List.nil_append,
            SeqSpec.evalMachine, registerStep] at hleg0
          obtain ⟨_, _, _, _, _, _, _, hbad, _⟩ := hleg0
          nomatch hbad
      · -- `c₀.proc = true`: then `c₁.proc = false`, violating `hpr_S : prec S ⟨false, 0⟩ ⟨true, 0⟩`
        cases hp₁ : c₁.proc
        · obtain ⟨r, i, hr, hi, hlt⟩ := hpr_S
          simp only [History.respPos, History.invPos, List.flatMap_cons, List.flatMap_nil,
            OpCall.toEvents, List.cons_append, List.nil_append, History.nthProcPos,
            Event.proc_inv, Event.proc_resp, hp₀, hp₁, Nat.mul_zero, Nat.zero_add,
            Bool.true_eq_false, ↓reduceIte, Option.map_some,
            Option.some.injEq] at hr hi
          omega
        · have hf := heqS false
          simp only [History.procSubhistory_flatMap_toEvents, List.filter, hp₀, hp₁,
            Bool.true_eq_false, decide_false, List.flatMap_nil] at hf
          nomatch hf

/-- Original explicit 2-process, 2-register **non-locality of sequential consistency** witness
(register counterpart of two-queue history `H_8` in [HerlihyWing1990], §3.3, p. 472): there exists a
well-formed 2-process (`Bool`), 2-register (`Bool`, both initialized to `false`) history `H` such
that `History.objSubhistory H false` and `History.objSubhistory H true` are each sequentially
consistent, yet `H` itself is **not** sequentially consistent. -/
theorem exists_obj_sequentiallyConsistent_not_global :
    ∃ H : History Bool (fun _ : Bool => RegOp Bool) (fun _ : Bool => RegResp Bool),
      History.WellFormed H ∧
      (∀ x : Bool, IsSequentiallyConsistent (fun y => registerSeqSpec y false)
        (History.objSubhistory H x)) ∧
      ¬ IsSequentiallyConsistent (fun y => registerSeqSpec y false) H := by
  -- Dekker / store-buffering history:
  -- Process `false`: `reg false .write true`, then `reg true .read → false`
  -- Process `true`:  `reg true .write true`,  then `reg false .read → false`
  let H : History Bool (fun _ : Bool => RegOp Bool) (fun _ : Bool => RegResp Bool) :=
    [.inv false false (.write true), .resp false false .writeAck,
     .inv true true (.write true), .resp true true .writeAck,
     .inv false true .read, .resp false true (.readRet false),
     .inv true false .read, .resp true false (.readRet false)]
  have hwfH : History.WellFormed H := fun p => by cases p <;> trivial
  refine ⟨H, hwfH, ?_, ?_⟩
  · intro x
    cases x
    · -- Object `false`: `false` writes `true`, `true` reads `false` → order `true`'s read first!
      let S₀ : History Bool (fun _ : Bool => RegOp Bool) (fun _ : Bool => RegResp Bool) :=
        [.inv true false .read, .resp true false (.readRet false),
         .inv false false (.write true), .resp false false .writeAck]
      refine ⟨History.objSubhistory H false, History.IsExtension.refl (hwfH.objSubhistory false),
        S₀, ⟨rfl, rfl, rfl, rfl, trivial⟩, ?_, ?_⟩
      · intro y; cases y
        · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
        · trivial
      · intro p; cases p <;> rfl
    · -- Object `true`: `true` writes `true`, `false` reads `false` → order `false`'s read first!
      let S₁ : History Bool (fun _ : Bool => RegOp Bool) (fun _ : Bool => RegResp Bool) :=
        [.inv false true .read, .resp false true (.readRet false),
         .inv true true (.write true), .resp true true .writeAck]
      refine ⟨History.objSubhistory H true, History.IsExtension.refl (hwfH.objSubhistory true),
        S₁, ⟨rfl, rfl, rfl, rfl, trivial⟩, ?_, ?_⟩
      · intro y; cases y
        · trivial
        · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
      · intro p; cases p <;> rfl
  · rintro ⟨H', ⟨R, hrespR, rfl, hwf'⟩, S, hseqS, hlegS, heqS⟩
    have hR_nil : R = [] :=
      resp_ext_eq_nil_of_even_proc hwfH (fun b => by cases b <;> decide) hrespR hwf'
    subst hR_nil
    rw [List.append_nil] at hwf' heqS
    have hevS := History.even_length_of_equivalent_complete hwf' hseqS heqS
    obtain ⟨cs, rfl⟩ := History.exists_calls_of_isSequential_even hseqS hevS
    -- In `S`, the 4 operations `⟨false, 0⟩, ⟨false, 1⟩, ⟨true, 0⟩, ⟨true, 1⟩` are completed:
    have hcF0 : countProcCalls false cs = 2 := by
      have hf := congrArg List.length (heqS false)
      rw [History.procSubhistory_flatMap_toEvents, History.length_flatMap_toEvents] at hf
      have hf_val : (History.procSubhistory (History.complete H) false).length = 4 := rfl
      rw [hf_val] at hf; simp only [countProcCalls]; omega
    have hcT0 : countProcCalls true cs = 2 := by
      have ht := congrArg List.length (heqS true)
      rw [History.procSubhistory_flatMap_toEvents, History.length_flatMap_toEvents] at ht
      have ht_val : (History.procSubhistory (History.complete H) true).length = 4 := rfl
      rw [ht_val] at ht; simp only [countProcCalls]; omega
    obtain ⟨jF0, hjF0, hopF0⟩ := exists_opIdAt_of_lt_countProcCalls cs ⟨false, 0⟩
      (by dsimp only; omega)
    obtain ⟨jF1, hjF1, hopF1⟩ := exists_opIdAt_of_lt_countProcCalls cs ⟨false, 1⟩
      (by dsimp only; omega)
    obtain ⟨jT0, hjT0, hopT0⟩ := exists_opIdAt_of_lt_countProcCalls cs ⟨true, 0⟩
      (by dsimp only; omega)
    obtain ⟨jT1, hjT1, hopT1⟩ := exists_opIdAt_of_lt_countProcCalls cs ⟨true, 1⟩
      (by dsimp only; omega)
    -- Program order in `S`: `jF0 < jF1` and `jT0 < jT1`
    have hcs_F : cs.filter (fun c => decide (c.proc = false)) =
        [⟨false, false, .write true, .writeAck⟩, ⟨false, true, .read, .readRet false⟩] := by
      apply flatMap_toEvents_injective
      rw [← History.procSubhistory_flatMap_toEvents, ← heqS false]
      rfl
    have hcs_T : cs.filter (fun c => decide (c.proc = true)) =
        [⟨true, true, .write true, .writeAck⟩, ⟨true, false, .read, .readRet false⟩] := by
      apply flatMap_toEvents_injective
      rw [← History.procSubhistory_flatMap_toEvents, ← heqS true]
      rfl
    have hc_S : ∀ b i, i < 2 → History.IsCompletedOp (cs.flatMap OpCall.toEvents) ⟨b, i⟩ := by
      intro b i hi
      rw [History.isCompletedOp_iff_lt_length, History.procSubhistory_flatMap_toEvents,
        History.length_flatMap_toEvents]
      dsimp only
      cases b
      · simp only [countProcCalls] at hcF0; omega
      · simp only [countProcCalls] at hcT0; omega
    have hjF_lt : jF0 < jF1 := by
      have hpr := History.prec_of_same_proc_lt (e₀ := ⟨false, 0⟩) (e₁ := ⟨false, 1⟩) rfl
        (by dsimp only; omega) (hc_S false 0 (by omega)) (hc_S false 1 (by omega))
      rw [← hopF0, ← hopF1] at hpr
      exact (prec_flatMap_toEvents_opIdAt_iff cs hjF0 hjF1).mp hpr
    have hjT_lt : jT0 < jT1 := by
      have hpr := History.prec_of_same_proc_lt (e₀ := ⟨true, 0⟩) (e₁ := ⟨true, 1⟩) rfl
        (by dsimp only; omega) (hc_S true 0 (by omega)) (hc_S true 1 (by omega))
      rw [← hopT0, ← hopT1] at hpr
      exact (prec_flatMap_toEvents_opIdAt_iff cs hjT0 hjT1).mp hpr
    -- Identify the exact `OpCall` at `jF0, jF1, jT0, jT1`:
    have hval_at : ∀ (j : ℕ) (hj : j < cs.length) (b : Bool) (idx : ℕ),
        opIdAt cs j hj = ⟨b, idx⟩ →
          ∃ hlt : idx < (cs.filter fun c => decide (c.proc = b)).length,
            (cs.filter fun c => decide (c.proc = b))[idx]'hlt = cs[j] := by
      intro j hj b idx hop
      have hpb : cs[j].proc = b := congrArg OpId.proc hop
      have hidx : countProcCalls b (cs.take j) = idx := by
        have := congrArg OpId.idx hop
        simpa only [opIdAt, hpb] using this
      obtain ⟨hlt, hget⟩ := filter_getElem_count_take (fun c => decide (c.proc = b)) cs j hj
        (decide_eq_true hpb)
      simp only [countProcCalls] at hidx
      subst hidx
      exact ⟨hlt, hget⟩
    obtain ⟨_, hgetF0⟩ := hval_at jF0 hjF0 false 0 hopF0
    obtain ⟨_, hgetF1⟩ := hval_at jF1 hjF1 false 1 hopF1
    obtain ⟨_, hgetT0⟩ := hval_at jT0 hjT0 true 0 hopT0
    obtain ⟨_, hgetT1⟩ := hval_at jT1 hjT1 true 1 hopT1
    simp only [hcs_F, List.getElem_cons_zero, List.getElem_cons_succ] at hgetF0 hgetF1
    simp only [hcs_T, List.getElem_cons_zero, List.getElem_cons_succ] at hgetT0 hgetT1
    have hlen_cs4 : cs.length = 4 := by
      have h := filter_proc_bool_length_sum cs
      simp only [countProcCalls] at hcF0 hcT0
      omega
    obtain ⟨c0, c1, c2, c3, hcs_eq⟩ : ∃ c0 c1 c2 c3, cs = [c0, c1, c2, c3] := by
      match cs, hlen_cs4 with
      | [c0, c1, c2, c3], _ => exact ⟨c0, c1, c2, c3, rfl⟩
    subst hcs_eq
    have hne_FT00 : jF0 ≠ jT0 := fun h => by subst h; rw [hopF0] at hopT0; nomatch hopT0
    have hne_FT01 : jF0 ≠ jT1 := fun h => by subst h; rw [hopF0] at hopT1; nomatch hopT1
    have hne_FT10 : jF1 ≠ jT0 := fun h => by subst h; rw [hopF1] at hopT0; nomatch hopT0
    have hne_FT11 : jF1 ≠ jT1 := fun h => by subst h; rw [hopF1] at hopT1; nomatch hopT1
    simp only [List.length_cons, List.length_nil] at hjF0 hjF1 hjT0 hjT1
    have hnot_F0_lt_T1 : ¬ jF0 < jT1 :=
      dekker_write_not_lt_stale_read false (hlegS false) hjF0 hjF1 hjT0 hjT1 hjF_lt hjT_lt
        hne_FT00 hne_FT01 hne_FT10 hne_FT11 hgetF0.symm hgetF1.symm hgetT0.symm hgetT1.symm
    have hnot_T0_lt_F1 : ¬ jT0 < jF1 :=
      dekker_write_not_lt_stale_read true (hlegS true) hjT0 hjT1 hjF0 hjF1 hjT_lt hjF_lt
        hne_FT00.symm hne_FT10.symm hne_FT01.symm hne_FT11.symm
        hgetT0.symm hgetT1.symm hgetF0.symm hgetF1.symm
    omega

end Cslib.Distributed.ConcurrentObjects
