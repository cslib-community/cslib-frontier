/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.List.FilterPos
public import Cslib.Foundations.Relation.Basic

/-!
# Concurrent histories, real-time precedence, and linearizability definitions

Core definitions and basic structural properties for concurrent invocation/response histories over
multiple typed shared objects ([HerlihyWing1990], §§2.1–2.2, §3.3, pp. 467–472) with the amended L2
condition of [SelaHerlihyPetrank2021] (§4, Definition 4.1, p. 6).

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

## Main results

* `Cslib.Distributed.ConcurrentObjects.History.prec_irrefl`,
  `Cslib.Distributed.ConcurrentObjects.History.prec_trans`,
  `Cslib.Distributed.ConcurrentObjects.History.isIntervalOrder_prec_completed`: `<_H` is a strict
  partial order and forms a `Relation.IsIntervalOrder` on completed operations.
* `Cslib.Distributed.ConcurrentObjects.IsLinearizable.isSequentiallyConsistent`: every linearizable
  history is sequentially consistent (after [HerlihyWing1990], §3.3, p. 472).

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

/-- Process and object subhistory projections commute. -/
theorem procSubhistory_objSubhistory_comm [DecidableEq P] [DecidableEq Obj]
    (H : History P Op Resp) (p : P) (x : Obj) :
    procSubhistory (objSubhistory H x) p = objSubhistory (procSubhistory H p) x := by
  simp only [procSubhistory, objSubhistory, List.filter_filter]
  exact congrArg (List.filter · H) (funext fun _ => Bool.and_comm _ _)

/-- Object subhistory projection is idempotent. -/
theorem objSubhistory_idem [DecidableEq Obj] (H : History P Op Resp) (x : Obj) :
    objSubhistory (objSubhistory H x) x = objSubhistory H x := by
  simp only [objSubhistory, List.filter_filter, Bool.and_self]

/-- Projecting onto two distinct objects yields the empty history. -/
theorem objSubhistory_of_ne [DecidableEq Obj] (H : History P Op Resp) {x y : Obj} (hne : x ≠ y) :
    objSubhistory (objSubhistory H x) y = [] := by
  simp only [objSubhistory, List.filter_filter, List.filter_eq_nil_iff, Bool.and_eq_true,
    decide_eq_true_eq]
  rintro _ _ ⟨rfl, rfl⟩
  exact hne rfl

/-- If every event of `H` targets `x`, then `H | x = H`. -/
theorem objSubhistory_eq_self_of_forall_obj [DecidableEq Obj] {H : History P Op Resp} {x : Obj}
    (h : ∀ e ∈ H, e.obj = x) : objSubhistory H x = H :=
  List.filter_eq_self.mpr fun e hm => decide_eq_true (h e hm)

/-- If no event of `H` targets `x`, then `H | x = []`. -/
theorem objSubhistory_eq_nil_of_forall_ne [DecidableEq Obj] {H : History P Op Resp} {x : Obj}
    (h : ∀ e ∈ H, e.obj ≠ x) : objSubhistory H x = [] :=
  List.filter_eq_nil_iff.mpr fun e hm hd => h e hm (of_decide_eq_true hd)

/-- Two histories are *equivalent* if they have identical process subhistories for every process `p`
([HerlihyWing1990], §2.1, p. 467). -/
@[expose]
def Equivalent [DecidableEq P] (H₁ H₂ : History P Op Resp) : Prop :=
  ∀ p, procSubhistory H₁ p = procSubhistory H₂ p

/-- Reflexivity of `History.Equivalent`. -/
theorem Equivalent.refl [DecidableEq P] (H : History P Op Resp) : Equivalent H H :=
  fun _ => rfl

/-- Symmetry of `History.Equivalent`. -/
theorem Equivalent.symm [DecidableEq P] {H₁ H₂ : History P Op Resp} (h : Equivalent H₁ H₂) :
    Equivalent H₂ H₁ :=
  fun p => (h p).symm

/-- Transitivity of `History.Equivalent`. -/
theorem Equivalent.trans [DecidableEq P] {H₁ H₂ H₃ : History P Op Resp}
    (h₁₂ : Equivalent H₁ H₂) (h₂₃ : Equivalent H₂ H₃) : Equivalent H₁ H₃ :=
  fun p => (h₁₂ p).trans (h₂₃ p)

/-- Equivalent histories have equivalent object subhistories on every object `x`. -/
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

/-- The empty history is well-formed. -/
theorem wellFormed_nil [DecidableEq P] : WellFormed ([] : History P Op Resp) :=
  fun _ => trivial

/-- Restricting a sequential history to a single object preserves sequentiality. -/
theorem isSequential_objSubhistory [DecidableEq Obj] {H : History P Op Resp}
    (hseq : IsSequential H) (x : Obj) : IsSequential (objSubhistory H x) := by
  match H with
  | [] => trivial
  | [.inv p y op] =>
    simp only [objSubhistory_cons, objSubhistory_nil, Event.obj_inv]
    by_cases h : y = x <;> simp only [h, ↓reduceIte] <;> trivial
  | [.resp _ _ _] | .inv _ _ _ :: .inv _ _ _ :: _ | .resp _ _ _ :: _ :: _ => exact False.elim hseq
  | .inv p₁ x₁ op :: .resp p₂ x₂ res :: rest =>
    obtain ⟨rfl, rfl, hrest⟩ := hseq
    simp only [objSubhistory_cons, Event.obj_inv, Event.obj_resp]
    by_cases hxx : x₁ = x
    · simp only [hxx, ↓reduceIte]
      exact ⟨rfl, rfl, isSequential_objSubhistory hrest x⟩
    · simp only [hxx, ↓reduceIte]
      exact isSequential_objSubhistory hrest x

/-- Restricting a well-formed history to a single object preserves well-formedness. -/
theorem WellFormed.objSubhistory [DecidableEq P] [DecidableEq Obj] {H : History P Op Resp}
    (hwf : WellFormed H) (x : Obj) : WellFormed (objSubhistory H x) := by
  intro p
  rw [procSubhistory_objSubhistory_comm]
  exact isSequential_objSubhistory (hwf p) x

/-- Expanding a list of completed `OpCall`s produces a sequential history. -/
theorem isSequential_flatMap_toEvents (calls : List (OpCall P Op Resp)) :
    IsSequential (calls.flatMap OpCall.toEvents) := by
  induction calls with
  | nil => trivial
  | cons _ _ ih => exact ⟨rfl, rfl, ih⟩

/-- Expanding `calls` into `[inv, resp]` pairs doubles the list length. -/
theorem length_flatMap_toEvents (calls : List (OpCall P Op Resp)) :
    (calls.flatMap OpCall.toEvents).length = 2 * calls.length := by
  induction calls with
  | nil => rfl
  | cons _ _ ih =>
    simp only [List.flatMap_cons, OpCall.toEvents, List.cons_append, List.nil_append,
      List.length_cons, ih]
    omega

/-- Process subhistory commutes with `List.flatMap OpCall.toEvents`. -/
theorem procSubhistory_flatMap_toEvents [DecidableEq P] (calls : List (OpCall P Op Resp)) (p : P) :
    procSubhistory (calls.flatMap OpCall.toEvents) p =
      (calls.filter fun c => decide (c.proc = p)).flatMap OpCall.toEvents := by
  induction calls with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.flatMap_cons, OpCall.toEvents, List.cons_append, List.nil_append,
      procSubhistory_cons, Event.proc_inv, Event.proc_resp, List.filter]
    by_cases hcp : c.proc = p <;>
      simp only [hcp, decide_true, decide_false, ↓reduceIte, List.flatMap_cons, OpCall.toEvents,
        List.cons_append, List.nil_append, ih]

/-- Object subhistory commutes with `List.flatMap OpCall.toEvents`. -/
theorem objSubhistory_flatMap_toEvents [DecidableEq Obj] (calls : List (OpCall P Op Resp))
    (x : Obj) :
    objSubhistory (calls.flatMap OpCall.toEvents) x =
      (calls.filter fun c => decide (c.obj = x)).flatMap OpCall.toEvents := by
  induction calls with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.flatMap_cons, OpCall.toEvents, List.cons_append, List.nil_append,
      objSubhistory_cons, Event.obj_inv, Event.obj_resp, List.filter]
    by_cases hcx : c.obj = x <;>
      simp only [hcx, decide_true, decide_false, ↓reduceIte, List.flatMap_cons, OpCall.toEvents,
        List.cons_append, List.nil_append, ih]

/-- Expanding any list of completed `OpCall`s yields a well-formed history. -/
theorem wellFormed_flatMap_toEvents [DecidableEq P] (calls : List (OpCall P Op Resp)) :
    WellFormed (calls.flatMap OpCall.toEvents) := by
  intro p
  rw [procSubhistory_flatMap_toEvents]
  exact isSequential_flatMap_toEvents _

/-- Every sequential history decomposes into completed `OpCall`s optionally followed by one
trailing pending invocation. -/
theorem isSequential_decomp {S : History P Op Resp} (hseq : IsSequential S) :
    (∃ calls : List (OpCall P Op Resp), S = calls.flatMap OpCall.toEvents) ∨
      ∃ (calls : List (OpCall P Op Resp)) (p : P) (x : Obj) (op : Op x),
        S = calls.flatMap OpCall.toEvents ++ [.inv p x op] := by
  match S with
  | [] => exact Or.inl ⟨[], rfl⟩
  | [.inv p x op] => exact Or.inr ⟨[], p, x, op, rfl⟩
  | [.resp _ _ _] | .inv _ _ _ :: .inv _ _ _ :: _ | .resp _ _ _ :: _ :: _ => exact False.elim hseq
  | .inv p₁ x₁ op :: .resp p₂ x₂ res :: rest =>
    obtain ⟨rfl, rfl, hrest⟩ := hseq
    rcases isSequential_decomp hrest with ⟨cs, rfl⟩ | ⟨cs, p, x, op', rfl⟩
    · exact Or.inl ⟨⟨p₁, x₁, op, res⟩ :: cs, rfl⟩
    · exact Or.inr ⟨⟨p₁, x₁, op, res⟩ :: cs, p, x, op', rfl⟩

/-- Every even-length sequential history is the expansion of a list of completed `OpCall`s. -/
theorem exists_calls_of_isSequential_even {S : History P Op Resp}
    (hseq : IsSequential S) (heven : S.length % 2 = 0) :
    ∃ calls : List (OpCall P Op Resp), S = calls.flatMap OpCall.toEvents := by
  rcases isSequential_decomp hseq with ⟨cs, rfl⟩ | ⟨cs, p, x, op, rfl⟩
  · exact ⟨cs, rfl⟩
  · simp only [List.length_append, length_flatMap_toEvents, List.length_singleton] at heven
    omega

/-- Appending a matched `[inv, resp]` pair to an even-length sequential history preserves
sequentiality. -/
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

/-- Process subhistory commutes with `History.complete`. -/
theorem procSubhistory_complete [DecidableEq P] (H : History P Op Resp) (p : P) :
    procSubhistory (complete H) p = complete (procSubhistory H p) := by
  induction H with
  | nil => rfl
  | cons e rest ih =>
    cases e with
    | inv q x op =>
      have hany : ((procSubhistory rest q).any fun e' => decide (e'.proc = q)) =
          rest.any fun e' => decide (e'.proc = q) := by
        simp only [procSubhistory, List.any_filter, Bool.and_self]
      by_cases hqp : q = p
      · subst hqp
        simp only [complete, procSubhistory_cons, Event.proc_inv, ↓reduceIte, hany]
        cases rest.any fun e' => decide (e'.proc = q) <;>
          simp only [Bool.false_eq_true, ↓reduceIte, procSubhistory_cons, Event.proc_inv, ih]
      · simp only [complete, procSubhistory_cons, Event.proc_inv, hqp, ↓reduceIte]
        cases rest.any fun e' => decide (e'.proc = q) <;>
          simp only [Bool.false_eq_true, ↓reduceIte, procSubhistory_cons, Event.proc_inv, hqp, ih]
    | resp q x res =>
      simp only [complete, procSubhistory_cons, Event.proc_resp]
      by_cases hqp : q = p <;> simp only [hqp, ↓reduceIte, complete, ih]

/-- Completing a sequential history yields an even-length sequential history. -/
theorem complete_isSequential [DecidableEq P] {H : History P Op Resp} (hseq : IsSequential H) :
    IsSequential (complete H) ∧ (complete H).length % 2 = 0 := by
  match H with
  | [] => exact ⟨trivial, rfl⟩
  | [.inv p x op] =>
    simp only [complete, List.any_nil, Bool.false_eq_true, ↓reduceIte]
    exact ⟨trivial, rfl⟩
  | [.resp _ _ _] | .inv _ _ _ :: .inv _ _ _ :: _ | .resp _ _ _ :: _ :: _ => exact False.elim hseq
  | .inv p₁ x₁ op :: .resp p₂ x₂ res :: rest =>
    obtain ⟨rfl, rfl, hrest⟩ := hseq
    simp only [complete, List.any_cons, Event.proc_resp, decide_true, Bool.true_or, ↓reduceIte,
      List.length_cons]
    obtain ⟨hseq', hev'⟩ := complete_isSequential hrest
    exact ⟨⟨rfl, rfl, hseq'⟩, by omega⟩

/-- An even-length sequential history has no pending invocations, so `complete H = H`. -/
theorem complete_eq_self_of_isSequential_even [DecidableEq P] {H : History P Op Resp}
    (hseq : IsSequential H) (heven : H.length % 2 = 0) : complete H = H := by
  match H with
  | [] => rfl
  | [.inv _ _ _] => simp only [List.length_singleton] at heven; omega
  | [.resp _ _ _] | .inv _ _ _ :: .inv _ _ _ :: _ | .resp _ _ _ :: _ :: _ => exact False.elim hseq
  | .inv p₁ x₁ op :: .resp p₂ x₂ res :: rest =>
    obtain ⟨rfl, rfl, hrest⟩ := hseq
    simp only [List.length_cons] at heven
    simp only [complete, List.any_cons, Event.proc_resp, decide_true, Bool.true_or, ↓reduceIte]
    exact congrArg (fun t => .inv p₁ x₁ op :: .resp p₁ x₁ res :: t)
      (complete_eq_self_of_isSequential_even hrest (by omega))

/-- Completing a well-formed history preserves well-formedness. -/
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
      obtain ⟨rfl, rfl, _⟩ := hseq
      exact ⟨res, L₂', rfl⟩
  | [.resp _ _ _] | [.inv _ _ _] | .inv _ _ _ :: .inv _ _ _ :: _ | .resp _ _ _ :: _ :: _ =>
    exact False.elim hseq
  | .inv _ _ _ :: .resp _ _ _ :: _ =>
    exact isSequential_inv_suffix_resp hseq.2.2 hne

/-- On well-formed histories, `complete` commutes with object subhistory projection. -/
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
      by_cases hyx : y = x <;> simp only [hyx, ↓reduceIte, complete, ih]
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
        have hany_eq :
            ((objSubhistory rest y).any fun e => decide (e.proc = p)) =
              (rest.any fun e => decide (e.proc = p)) := by
          apply Bool.eq_iff_iff.mpr
          simp only [List.any_eq_true]
          refine ⟨fun ⟨e, hm, hep⟩ => ⟨e, (List.mem_filter.mp hm).1, hep⟩, fun ⟨e, hm, hep⟩ => ?_⟩
          obtain ⟨res, L₂', hL₂⟩ := isSequential_inv_suffix_resp hseq_p
            (List.ne_nil_of_mem (List.mem_filter.mpr ⟨hm, hep⟩))
          have hmem_p : Event.resp p y res ∈ procSubhistory rest p := hL₂ ▸ List.mem_cons_self
          exact ⟨.resp p y res,
            List.mem_filter.mpr ⟨(List.mem_filter.mp hmem_p).1, decide_eq_true rfl⟩,
            decide_eq_true rfl⟩
        rw [hany_eq]
        cases rest.any fun e => decide (e.proc = p) <;>
          simp only [Bool.false_eq_true, ↓reduceIte, objSubhistory_cons, Event.obj_inv, ih]
      · simp only [hyx, ↓reduceIte]
        cases rest.any fun e => decide (e.proc = p) <;>
          simp only [Bool.false_eq_true, ↓reduceIte, objSubhistory_cons, Event.obj_inv, hyx, ih]
  exact go [] H rfl

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

/-- Every well-formed history is a trivial extension of itself. -/
theorem IsExtension.refl [DecidableEq P] {H : History P Op Resp} (hwf : WellFormed H) :
    IsExtension H H :=
  ⟨[], fun _ hm => False.elim (List.not_mem_nil hm), (List.append_nil H).symm, hwf⟩

/-! ### Operation positions and real-time precedence `<_H` -/

/-- Position in `H` of the `n`-th event belonging to process `p` (`none` if `p` has at most `n`
events in `H`). -/
@[expose]
def nthProcPos [DecidableEq P] (p : P) (H : History P Op Resp) (n : ℕ) : Option ℕ :=
  List.nthFilterPos (fun e => decide (e.proc = p)) H n

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

/-- `e` is completed in `H` iff `2 * e.idx + 1 < (H | e.proc).length`. -/
theorem isCompletedOp_iff_lt_length [DecidableEq P] (H : History P Op Resp) (e : OpId P) :
    IsCompletedOp H e ↔ 2 * e.idx + 1 < (procSubhistory H e.proc).length := by
  dsimp only [IsCompletedOp, respPos, nthProcPos, procSubhistory]
  exact List.nthFilterPos_isSome_iff _ H _

/-- Equivalent histories have the same set of completed operations. -/
theorem Equivalent.isCompletedOp_iff [DecidableEq P] {H₁ H₂ : History P Op Resp}
    (heq : Equivalent H₁ H₂) (e : OpId P) :
    IsCompletedOp H₁ e ↔ IsCompletedOp H₂ e := by
  rw [isCompletedOp_iff_lt_length, isCompletedOp_iff_lt_length, heq e.proc]

/-- Every operation with a response at index `r` has an earlier invocation at some index `i < r`. -/
theorem invPos_of_respPos [DecidableEq P] {H : History P Op Resp} {e : OpId P} {r : ℕ}
    (hr : respPos H e = some r) : ∃ i, invPos H e = some i ∧ i < r := by
  have hr_flt :
      List.nthFilterPos (fun ev => decide (ev.proc = e.proc)) H (2 * e.idx + 1) = some r :=
    hr
  have hlen : 2 * e.idx + 1 < (H.filter fun ev => decide (ev.proc = e.proc)).length :=
    (List.nthFilterPos_isSome_iff _ H _).mp (by rw [hr_flt]; rfl)
  obtain ⟨i, hi_flt⟩ := Option.isSome_iff_exists.mp
    ((List.nthFilterPos_isSome_iff (fun ev => decide (ev.proc = e.proc)) H (2 * e.idx)).mpr
      (by omega))
  exact ⟨i, hi_flt, List.nthFilterPos_strictMono (by omega) hi_flt hr_flt⟩

/-- Real-time precedence `<_H` is irreflexive ([HerlihyWing1990], §2.2, p. 468). -/
theorem prec_irrefl [DecidableEq P] (H : History P Op Resp) (e : OpId P) : ¬ prec H e e := by
  rintro ⟨r, i, hr, hi, hlt⟩
  have hir := List.nthFilterPos_strictMono (by omega : 2 * e.idx < 2 * e.idx + 1) hi hr
  omega

/-- Real-time precedence `<_H` is transitive ([HerlihyWing1990], §2.2, p. 468). -/
theorem prec_trans [DecidableEq P] {H : History P Op Resp} {e₀ e₁ e₂ : OpId P}
    (h₀₁ : prec H e₀ e₁) (h₁₂ : prec H e₁ e₂) : prec H e₀ e₂ := by
  obtain ⟨r₀, i₁, hr₀, hi₁, hlt₀⟩ := h₀₁
  obtain ⟨r₁, i₂, hr₁, hi₂, hlt₁⟩ := h₁₂
  have hir₁ : i₁ < r₁ :=
    List.nthFilterPos_strictMono (by omega : 2 * e₁.idx < 2 * e₁.idx + 1) hi₁ hr₁
  exact ⟨r₀, i₂, hr₀, hi₂, by omega⟩

/-- On the subtype of completed operations of `H`, real-time precedence `<_H` forms a
`Relation.IsIntervalOrder` (`Cslib.Foundations.Relation.Defs`). -/
theorem isIntervalOrder_prec_completed [DecidableEq P] (H : History P Op Resp) :
    IsIntervalOrder (fun a b : { e : OpId P // IsCompletedOp H e } => prec H a.val b.val) := by
  refine ⟨{ irrefl := fun a => prec_irrefl H a.val
            trans := fun _ _ _ => prec_trans }, ?_⟩
  rintro ⟨a₁, _⟩ ⟨b₁, _⟩ ⟨a₂, _⟩ ⟨b₂, _⟩ ⟨⟨r₁, i₁, hr₁, hi₁, h₁⟩, ⟨r₂, i₂, hr₂, hi₂, h₂⟩⟩
  obtain ⟨ia₂, hia₂, hlt₂⟩ := invPos_of_respPos hr₂
  by_cases hcmp : r₁ < i₂
  · exact Or.inl ⟨r₁, i₂, hr₁, hi₂, hcmp⟩
  · exact Or.inr ⟨r₂, i₁, hr₂, hi₁, by omega⟩

/-- Completed operations of the same process are ordered in `<_H` by their invocation index. -/
theorem prec_of_same_proc_lt [DecidableEq P] {H : History P Op Resp} {e₀ e₁ : OpId P}
    (hp : e₀.proc = e₁.proc) (hidx : e₀.idx < e₁.idx)
    (hc₀ : IsCompletedOp H e₀) (hc₁ : IsCompletedOp H e₁) : prec H e₀ e₁ := by
  obtain ⟨r₀, hr₀⟩ := Option.isSome_iff_exists.mp hc₀
  obtain ⟨r₁, hr₁⟩ := Option.isSome_iff_exists.mp hc₁
  obtain ⟨i₁, hi₁, _⟩ := invPos_of_respPos hr₁
  refine ⟨r₀, i₁, hr₀, hi₁, ?_⟩
  dsimp only [respPos, invPos, nthProcPos] at hr₀ hi₁
  rw [← hp] at hi₁
  exact List.nthFilterPos_strictMono (by omega : 2 * e₀.idx + 1 < 2 * e₁.idx) hr₀ hi₁

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
  | [.inv _ _ _] =>
    intro e hm
    rw [List.mem_singleton.mp hm]
    exact h
  | [.resp _ _ _] | .inv _ _ _ :: .inv _ _ _ :: _ | .resp _ _ _ :: _ :: _ => exact False.elim h
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
  | [] | [.inv _ _ _] => trivial
  | [.resp _ _ _] | .inv _ _ _ :: .inv _ _ _ :: _ | .resp _ _ _ :: _ :: _ => exact False.elim h
  | .inv _ _ _ :: .resp _ _ _ :: _ =>
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
    | resp _ _ _ => cases t <;> exact False.elim h
    | inv _ _ _ =>
      cases t with
      | nil => exact h
      | cons e₂ _ =>
        cases e₂ with
        | inv _ _ _ => exact False.elim h
        | resp _ _ _ => exact h.1
  | e₁ :: e₂ :: rest₁ =>
    obtain ⟨t, ht⟩ := hpre
    simp only [List.cons_append] at ht
    rcases H₂ with _ | ⟨a, _ | ⟨b, rest₂⟩⟩
    · nomatch ht
    · injection ht with _ htail; nomatch htail
    · injection ht with ha htail
      injection htail with hb hrest
      subst ha hb
      cases e₁ with
      | resp _ _ _ => exact False.elim h
      | inv _ _ _ =>
        cases e₂ with
        | inv _ _ _ => exact False.elim h
        | resp _ _ _ =>
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
  | _, [.resp _ _ _], hL, _
  | _, .inv _ _ _ :: .inv _ _ _ :: _, hL, _
  | _, .resp _ _ _ :: _ :: _, hL, _ => False.elim hL
  | st, .inv _ _ op₁ :: .resp _ _ _ :: rest, hL, hev => by
    obtain ⟨hx₁, hx₂, hp, hres₁, hrest⟩ := hL
    cases hx₁; cases hx₂
    simp only [List.length_cons] at hev
    obtain ⟨res, hres⟩ := evalMachine_append_pair _ step op p (step st op₁).1 rest hrest (by omega)
    exact ⟨res, rfl, rfl, hp, hres₁, hres⟩

/-- Every operation of a deterministic total state machine `SeqSpec.ofMachine` is total. -/
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

end Cslib.Distributed.ConcurrentObjects
