/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.RelClasses
import Mathlib.Data.List.TakeDrop

/-!
# Asynchronous message-passing executions, happens-before causality, and consistent cuts

This module formalizes finite causally well-formed asynchronous point-to-point message-passing
executions over a process type `P`, Lamport's *happens-before* strict partial order [Lamport1978],
causal concurrency, executable causal-past computation, and downward-closed *consistent cuts*
[Mattern1989].

An `Execution P` records a finite sequence `steps : List (Step P)` of process steps:
* `Step.internal actor`: an internal step at process `actor`,
* `Step.send actor dest`: a point-to-point message send from `actor` to `dest`,
* `Step.recv actor sendIdx`: receipt at `actor` of the message sent at earlier trace index
  `sendIdx < i` (`recv_valid`), with at-most-once delivery per sent message (`recv_injective`).

Events `E.Event` wrap `Fin E.steps.length` so that `E.Event` carries Lamport's causal
`PartialOrder` (`≤` for `HappensBeforeLe`, `<` for `HappensBefore`) without colliding with the
linear trace-index order on `Fin`.

### Relationship to `Cslib.DistributedConsistency`

Upstream `Cslib.DistributedConsistency` (`AbstractExecution.hb`) models axiomatic replicated-data
consistency following Burckhardt (2014), taking session order and visibility relations over an
abstract event set where acyclicity (`NoCircularCausality`) is an explicit hypothesis. Here
`Execution P` models operational asynchronous message-passing traces whose happens-before relation
is unconditionally a `PartialOrder` / `IsStrictOrder` with executable `O(n²)` decidability,
supporting operational Lamport scalar clocks, Fidge–Mattern vector clocks, and Charron-Bost's
clock-dimension lower bound in companion modules.

## Main definitions

* `Cslib.Distributed.VectorClock.Step`: local, send, or receive process step.
* `Cslib.Distributed.VectorClock.Execution`: causally well-formed finite message-passing execution.
* `Cslib.Distributed.VectorClock.Execution.Event`: event of an execution carrying the causal
  `PartialOrder`.
* `Cslib.Distributed.VectorClock.Execution.ProgramOrder`,
  `Cslib.Distributed.VectorClock.Execution.MessageOrder`,
  `Cslib.Distributed.VectorClock.Execution.CausalStep`: direct same-process and send-to-receive
  causal edges.
* `Cslib.Distributed.VectorClock.Execution.HappensBefore`,
  `Cslib.Distributed.VectorClock.Execution.HappensBeforeLe`: strict and reflexive causal ordering
  on `E.Event`.
* `Cslib.Distributed.VectorClock.Execution.Concurrent`: causal incomparability on `E.Event`.
* `Cslib.Distributed.VectorClock.Execution.causalPast`,
  `Cslib.Distributed.VectorClock.Execution.causalPastLe`: computable `Finset` of causal
  predecessors of an event.
* `Cslib.Distributed.VectorClock.Execution.IsConsistentCut`: downward-closed event subsets
  (consistent global cuts).
* `Cslib.Distributed.VectorClock.Execution.ofInternal`,
  `Cslib.Distributed.VectorClock.Execution.IsValidSteps`,
  `Cslib.Distributed.VectorClock.Execution.ofValidSteps`: constructors for communication-free
  local schedules and `decide`-validated concrete step traces.
* `Cslib.Distributed.VectorClock.Execution.map`: pushforward of an execution along a process
  renaming `P → Q`.

## Main results

* `Cslib.Distributed.VectorClock.Execution.happensBefore_idx_lt`: causal precedence strictly
  respects trace indices, establishing acyclicity.
* `Cslib.Distributed.VectorClock.Execution.instPartialOrderEvent`,
  `Cslib.Distributed.VectorClock.Execution.instIsStrictOrderEventHappensBefore`: `PartialOrder` and
  `IsStrictOrder` instances on `E.Event`.
* `Cslib.Distributed.VectorClock.Execution.mem_causalPast`,
  `Cslib.Distributed.VectorClock.Execution.instDecidableHappensBefore`: exact characterization of
  the forward dynamic-programming causal-past table and decidability of `HappensBefore`.
* `Cslib.Distributed.VectorClock.Execution.causal_trichotomy`: any two events are equal, ordered by
  `HappensBefore` in one direction, or `Concurrent`.
* `Cslib.Distributed.VectorClock.Execution.IsConsistentCut.union`,
  `Cslib.Distributed.VectorClock.Execution.IsConsistentCut.inter`: consistent cuts form a
  distributive sublattice under `∪` and `∩`.
* `Cslib.Distributed.VectorClock.Execution.IsConsistentCut.send_mem_of_recv_mem`: consistent cuts
  contain no orphan message receives.
* `Cslib.Distributed.VectorClock.Execution.map_happensBeforeLe_iff`: injective process renaming
  induces an order-isomorphism on causal event posets.

## References

* [L. Lamport, *Time, Clocks, and the Ordering of Events in a Distributed System*][Lamport1978]
* [F. Mattern, *Virtual Time and Global States of Distributed Systems*][Mattern1989]
-/

public section

namespace Cslib.Distributed.VectorClock

universe u

/-- A single local or communication step in an asynchronous message-passing execution over
process type `P`. A `.recv actor sendIdx` step references the trace index `sendIdx` of the
matching `.send` step whose message is delivered. -/
inductive Step (P : Type u) where
  /-- Internal computation step at process `actor`. -/
  | internal (actor : P)
  /-- Point-to-point message send from `actor` to `dest`. -/
  | send (actor : P) (dest : P)
  /-- Receipt at `actor` of the message sent at trace index `sendIdx`. -/
  | recv (actor : P) (sendIdx : ℕ)
  deriving @[expose] DecidableEq, Repr

namespace Step

variable {P : Type u}

/-- The process executing a given `Step`. -/
@[expose] def actor : Step P → P
  | .internal p => p
  | .send p _ => p
  | .recv p _ => p

@[simp] theorem actor_internal (p : P) : (Step.internal p).actor = p := rfl
@[simp] theorem actor_send (p dest : P) : (Step.send p dest).actor = p := rfl
@[simp] theorem actor_recv (p : P) (sIdx : ℕ) : (Step.recv p sIdx).actor = p := rfl

/-- Rename process identifiers in a `Step`. -/
@[expose] def map {Q : Type*} (f : P → Q) : Step P → Step Q
  | .internal p => .internal (f p)
  | .send p dest => .send (f p) (f dest)
  | .recv p sIdx => .recv (f p) sIdx

@[simp] theorem actor_map {Q : Type*} (f : P → Q) (s : Step P) :
    (s.map f).actor = f s.actor := by
  cases s <;> rfl

end Step

/-- A finite causally well-formed asynchronous point-to-point message-passing execution over
processes `P`. Every `.recv actor sIdx` step references a strictly earlier `.send src actor`
step (`sIdx < i`), and each sent message is delivered at most once (`recv_injective`). -/
@[ext]
structure Execution (P : Type u) where
  /-- Linearly indexed sequence of steps in the execution. -/
  steps : List (Step P)
  /-- Every receive step references a strictly earlier send step addressed to the receiver. -/
  recv_valid : ∀ (i : Fin steps.length) (p : P) (sIdx : ℕ),
    steps[i] = .recv p sIdx →
    ∃ (hs : sIdx < i.val) (src : P), steps[sIdx]'(hs.trans i.isLt) = .send src p
  /-- Each sent message is received at most once along the execution. -/
  recv_injective : ∀ (i j : Fin steps.length) (p₁ p₂ : P) (sIdx : ℕ),
    steps[i] = .recv p₁ sIdx → steps[j] = .recv p₂ sIdx → i = j
  deriving @[expose] DecidableEq

namespace Execution

variable {P : Type u}

/-- The empty execution with zero events. -/
@[expose] def empty : Execution P where
  steps := []
  recv_valid i := Fin.elim0 i
  recv_injective i := Fin.elim0 i

/-- Communication-free execution consisting solely of internal steps on `procs`. -/
@[expose] def ofInternal (procs : List P) : Execution P where
  steps := procs.map Step.internal
  recv_valid := by
    intro ⟨i, hi⟩ _ _ h
    change (procs.map Step.internal)[i] = _ at h
    rw [List.getElem_map] at h
    cases h
  recv_injective := by
    intro ⟨i, hi⟩ _ _ _ _ h _
    change (procs.map Step.internal)[i] = _ at h
    rw [List.getElem_map] at h
    cases h

/-- Per-index causal well-formedness check on `steps : List (Step P)`. -/
@[expose] def isValidStepAt [DecidableEq P] (steps : List (Step P))
    (i : Fin steps.length) : Bool :=
  match steps[i] with
  | .internal _ | .send _ _ => true
  | .recv p sIdx =>
    if hs : sIdx < i.val then
      (match steps[sIdx]'(hs.trans i.isLt) with
        | .send _ dest => decide (dest = p)
        | _ => false) &&
      (List.finRange steps.length).all fun j =>
        match steps[j] with
        | .recv _ sIdx' => decide (sIdx' = sIdx → i = j)
        | _ => true
    else
      false

/-- Executable Boolean check certifying that `steps : List (Step P)` forms a causally well-formed
`Execution P` (enabling `Execution.ofValidSteps steps (by decide)` in `module` clients). -/
@[expose] def IsValidSteps [DecidableEq P] (steps : List (Step P)) : Bool :=
  (List.finRange steps.length).all (isValidStepAt steps)

/-- Construct an `Execution P` from a step list certified by `IsValidSteps steps = true`. -/
@[expose] def ofValidSteps [DecidableEq P] (steps : List (Step P))
    (h : IsValidSteps steps = true) : Execution P where
  steps := steps
  recv_valid := by
    intro i p sIdx hrecv
    have hi := List.all_eq_true.mp h i (List.mem_finRange i)
    simp only [isValidStepAt, hrecv] at hi
    by_cases hs : sIdx < i.val
    · simp only [hs, ↓reduceDIte, Bool.and_eq_true] at hi
      obtain ⟨hsend_ok, _⟩ := hi
      cases hst : steps[sIdx]'(hs.trans i.isLt) <;>
        simp only [hst, decide_eq_true_eq, Bool.false_eq_true] at hsend_ok
      subst hsend_ok
      exact ⟨hs, _, hst⟩
    · simp [hs] at hi
  recv_injective := by
    intro i j p₁ p₂ sIdx hi_eq hj_eq
    have hi := List.all_eq_true.mp h i (List.mem_finRange i)
    simp only [isValidStepAt, hi_eq] at hi
    by_cases hs : sIdx < i.val
    · simp only [hs, ↓reduceDIte, Bool.and_eq_true] at hi
      have hj := List.all_eq_true.mp hi.2 j (List.mem_finRange j)
      simp only [hj_eq, decide_eq_true_eq] at hj
      exact hj trivial
    · simp [hs] at hi

@[simp] theorem steps_ofValidSteps [DecidableEq P] (steps : List (Step P))
    (h : IsValidSteps steps = true) : (ofValidSteps steps h).steps = steps := rfl

/-- An event of execution `E`, wrapping its trace index in `E.steps` so that `E.Event` carries
Lamport's causal happens-before `PartialOrder` without conflicting with the trace-index linear
order on `Fin E.steps.length`. -/
@[ext]
structure Event (E : Execution P) where
  /-- Trace index of the event in `E.steps`. -/
  idx : Fin E.steps.length

instance instReprEvent (E : Execution P) : Repr E.Event where
  reprPrec e p := reprPrec e.idx p

instance instDecidableEqEvent (E : Execution P) : DecidableEq E.Event :=
  fun a b => decidable_of_iff (a.idx = b.idx) Event.ext_iff.symm

/-- Equivalence between `E.Event` and `Fin E.steps.length`. -/
@[expose] def Event.equivFin (E : Execution P) : E.Event ≃ Fin E.steps.length where
  toFun := Event.idx
  invFun := Event.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance instFintypeEvent (E : Execution P) : Fintype E.Event where
  elems := ⟨Multiset.ofList ((List.finRange E.steps.length).map Event.mk),
    Multiset.coe_nodup.mpr
      ((List.nodup_finRange E.steps.length).map fun _ _ h => Event.mk.inj h)⟩
  complete e := by
    simp only [Finset.mem_mk, Multiset.mem_coe, List.mem_map]
    exact ⟨e.idx, List.mem_finRange e.idx, rfl⟩

@[simp] theorem card_event (E : Execution P) : Fintype.card E.Event = E.steps.length := by
  simpa using Fintype.card_congr (Event.equivFin E)

/-- The `Step P` performed at event `e`. -/
@[expose] def Event.step {E : Execution P} (e : E.Event) : Step P :=
  E.steps[e.idx]

/-- The process at which event `e` occurs. -/
@[expose] def Event.actor {E : Execution P} (e : E.Event) : P :=
  e.step.actor

/-- Every receive event `e` has a unique earlier matching send event addressed to `e.actor`. -/
theorem recv_sendEvent {E : Execution P} {e : E.Event} {p : P} {sIdx : ℕ}
    (hrecv : e.step = .recv p sIdx) :
    ∃ eSend : E.Event, eSend.idx.val = sIdx ∧ eSend.idx < e.idx ∧
      p = e.actor ∧ ∃ src : P, eSend.step = .send src p := by
  obtain ⟨hs, src, hsend⟩ := E.recv_valid e.idx p sIdx hrecv
  exact ⟨⟨⟨sIdx, hs.trans e.idx.isLt⟩⟩, rfl, hs, by simp [Event.actor, hrecv], src, hsend⟩

/-! ### Direct causality and Lamport's happens-before poset -/

/-- Same-process program order: `e₁` and `e₂` occur at the same process with `e₁.idx < e₂.idx`. -/
@[expose] def ProgramOrder (E : Execution P) (e₁ e₂ : E.Event) : Prop :=
  e₁.actor = e₂.actor ∧ e₁.idx < e₂.idx

/-- Point-to-point message order: `e₂` receives the message sent at `e₁`. -/
@[expose] def MessageOrder (E : Execution P) (e₁ e₂ : E.Event) : Prop :=
  e₂.step = .recv e₂.actor e₁.idx.val

/-- Single-step causal precedence: either program order on the same process or message
send-to-receive order. -/
@[expose] def CausalStep (E : Execution P) (e₁ e₂ : E.Event) : Prop :=
  E.ProgramOrder e₁ e₂ ∨ E.MessageOrder e₁ e₂

/-- Lamport's strict happens-before relation ([Lamport1978]), defined as the transitive closure
of `CausalStep`. -/
@[expose] def HappensBefore (E : Execution P) (e₁ e₂ : E.Event) : Prop :=
  Relation.TransGen E.CausalStep e₁ e₂

/-- Reflexive-transitive causal ordering on events (`e₁ = e₂ ∨ E.HappensBefore e₁ e₂`). -/
@[expose] def HappensBeforeLe (E : Execution P) (e₁ e₂ : E.Event) : Prop :=
  Relation.ReflTransGen E.CausalStep e₁ e₂

/-- If `e₂.step = .recv p e₁.idx.val`, then `MessageOrder e₁ e₂` holds. -/
theorem messageOrder_of_recv {E : Execution P} {e₁ e₂ : E.Event} {p : P}
    (h : e₂.step = .recv p e₁.idx.val) : E.MessageOrder e₁ e₂ := by
  simp [MessageOrder, Event.actor, h]

/-- Direct causal steps strictly advance the execution trace index. -/
theorem causalStep_idx_lt {E : Execution P} {e₁ e₂ : E.Event} (h : E.CausalStep e₁ e₂) :
    e₁.idx < e₂.idx := by
  rcases h with ⟨_, hlt⟩ | hmsg
  · exact hlt
  · obtain ⟨eSend, hval, hlt, _⟩ := E.recv_sendEvent hmsg
    exact Event.ext (Fin.ext hval) ▸ hlt

/-- Causal precedence strictly respects trace indices (`e₁ ≺ e₂ → e₁.idx < e₂.idx`), witnessing
acyclicity of happens-before in every well-formed execution. -/
theorem happensBefore_idx_lt {E : Execution P} {e₁ e₂ : E.Event} (h : E.HappensBefore e₁ e₂) :
    e₁.idx < e₂.idx := by
  induction h with
  | single hs => exact causalStep_idx_lt hs
  | tail _ hs ih => exact ih.trans (causalStep_idx_lt hs)

/-- Reflexive causal precedence implies non-strict trace-index ordering. -/
theorem happensBeforeLe_idx_le {E : Execution P} {e₁ e₂ : E.Event} (h : E.HappensBeforeLe e₁ e₂) :
    e₁.idx ≤ e₂.idx := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp h with rfl | hlt
  · exact le_rfl
  · exact (happensBefore_idx_lt hlt).le

/-- Strict `HappensBefore` is irreflexive. -/
theorem happensBefore_irrefl (E : Execution P) (e : E.Event) : ¬ E.HappensBefore e e :=
  fun h => Nat.lt_irrefl _ (happensBefore_idx_lt h)

/-- Strict `HappensBefore` is transitive. -/
theorem HappensBefore.trans {E : Execution P} {e₁ e₂ e₃ : E.Event}
    (h₁₂ : E.HappensBefore e₁ e₂) (h₂₃ : E.HappensBefore e₂ e₃) : E.HappensBefore e₁ e₃ :=
  Relation.TransGen.trans h₁₂ h₂₃

/-- Strict `HappensBefore` is asymmetric. -/
theorem happensBefore_asymm {E : Execution P} {e₁ e₂ : E.Event}
    (h : E.HappensBefore e₁ e₂) : ¬ E.HappensBefore e₂ e₁ :=
  fun h' => E.happensBefore_irrefl e₁ (h.trans h')

/-- `HappensBeforeLe` holds iff the events are equal or related by strict `HappensBefore`. -/
theorem happensBeforeLe_iff {E : Execution P} {e₁ e₂ : E.Event} :
    E.HappensBeforeLe e₁ e₂ ↔ e₁ = e₂ ∨ E.HappensBefore e₁ e₂ := by
  simpa [HappensBeforeLe, HappensBefore, eq_comm] using
    (Relation.reflTransGen_iff_eq_or_transGen (r := E.CausalStep) (a := e₁) (b := e₂))

/-- `HappensBeforeLe` is reflexive. -/
theorem happensBeforeLe_refl (E : Execution P) (e : E.Event) : E.HappensBeforeLe e e :=
  Relation.ReflTransGen.refl

/-- `HappensBeforeLe` is transitive. -/
theorem HappensBeforeLe.trans {E : Execution P} {e₁ e₂ e₃ : E.Event}
    (h₁₂ : E.HappensBeforeLe e₁ e₂) (h₂₃ : E.HappensBeforeLe e₂ e₃) : E.HappensBeforeLe e₁ e₃ :=
  Relation.ReflTransGen.trans h₁₂ h₂₃

/-- `HappensBeforeLe` is antisymmetric. -/
theorem happensBeforeLe_antisymm {E : Execution P} {e₁ e₂ : E.Event}
    (h₁₂ : E.HappensBeforeLe e₁ e₂) (h₂₁ : E.HappensBeforeLe e₂ e₁) : e₁ = e₂ := by
  refine (happensBeforeLe_iff.mp h₁₂).elim id fun h₁ =>
    (happensBeforeLe_iff.mp h₂₁).elim Eq.symm fun h₂ => absurd h₂ (happensBefore_asymm h₁)

/-- Every strict `HappensBefore` edge implies `HappensBeforeLe`. -/
theorem HappensBefore.happensBeforeLe {E : Execution P} {e₁ e₂ : E.Event}
    (h : E.HappensBefore e₁ e₂) : E.HappensBeforeLe e₁ e₂ :=
  happensBeforeLe_iff.mpr (.inr h)

/-- Distinct events related by `HappensBeforeLe` are related by strict `HappensBefore`. -/
theorem happensBefore_of_happensBeforeLe_of_ne {E : Execution P} {e₁ e₂ : E.Event}
    (h : E.HappensBeforeLe e₁ e₂) (hne : e₁ ≠ e₂) : E.HappensBefore e₁ e₂ :=
  (happensBeforeLe_iff.mp h).resolve_left hne

/-- Same-process program order implies `HappensBefore`. -/
theorem programOrder_happensBefore {E : Execution P} {e₁ e₂ : E.Event}
    (hact : e₁.actor = e₂.actor) (hlt : e₁.idx < e₂.idx) : E.HappensBefore e₁ e₂ :=
  Relation.TransGen.single (.inl ⟨hact, hlt⟩)

/-- Non-strict same-process trace order implies `HappensBeforeLe`. -/
theorem programOrder_happensBeforeLe {E : Execution P} {e₁ e₂ : E.Event}
    (hact : e₁.actor = e₂.actor) (hle : e₁.idx ≤ e₂.idx) : E.HappensBeforeLe e₁ e₂ := by
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact (Event.ext heq) ▸ E.happensBeforeLe_refl e₁
  · exact (E.programOrder_happensBefore hact hlt).happensBeforeLe

/-- Point-to-point message order implies `HappensBefore`. -/
theorem messageOrder_happensBefore {E : Execution P} {e₁ e₂ : E.Event}
    (h : E.MessageOrder e₁ e₂) : E.HappensBefore e₁ e₂ :=
  Relation.TransGen.single (.inr h)

/-- Same-process events are ordered by `HappensBeforeLe` iff their trace indices are ordered. -/
theorem sameActor_happensBeforeLe_iff {E : Execution P} {e₁ e₂ : E.Event}
    (hact : e₁.actor = e₂.actor) : E.HappensBeforeLe e₁ e₂ ↔ e₁.idx ≤ e₂.idx :=
  ⟨happensBeforeLe_idx_le, programOrder_happensBeforeLe hact⟩

/-- Same-process events are ordered by `HappensBefore` iff their trace indices are strictly
ordered. -/
theorem sameActor_happensBefore_iff {E : Execution P} {e₁ e₂ : E.Event}
    (hact : e₁.actor = e₂.actor) : E.HappensBefore e₁ e₂ ↔ e₁.idx < e₂.idx :=
  ⟨happensBefore_idx_lt, programOrder_happensBefore hact⟩

/-- In `Execution.ofInternal procs`, causal ordering reduces purely to same-process program
order. -/
theorem ofInternal_happensBeforeLe_iff {procs : List P}
    {e₁ e₂ : (Execution.ofInternal procs).Event} :
    (Execution.ofInternal procs).HappensBeforeLe e₁ e₂ ↔
      e₁ = e₂ ∨ (e₁.actor = e₂.actor ∧ e₁.idx < e₂.idx) := by
  have hstep_iff (x y : (Execution.ofInternal procs).Event) :
      (Execution.ofInternal procs).CausalStep x y ↔ x.actor = y.actor ∧ x.idx < y.idx :=
    ⟨fun h => h.resolve_right fun hmsg => by
      simp [Execution.MessageOrder, Event.step, Execution.ofInternal] at hmsg, .inl⟩
  refine ⟨fun hle => ?_, ?_⟩
  · induction hle with
    | refl => exact .inl rfl
    | tail _ hcs ih =>
      obtain ⟨hact₂, hlt₂⟩ := (hstep_iff _ _).mp hcs
      rcases ih with rfl | ⟨hact₁, hlt₁⟩
      · exact .inr ⟨hact₂, hlt₂⟩
      · exact .inr ⟨hact₁.trans hact₂, hlt₁.trans hlt₂⟩
  · rintro (rfl | ⟨hact, hlt⟩)
    · exact (Execution.ofInternal procs).happensBeforeLe_refl _
    · exact ((Execution.ofInternal procs).programOrder_happensBefore hact hlt).happensBeforeLe

instance instIsStrictOrderEventHappensBefore (E : Execution P) :
    IsStrictOrder E.Event E.HappensBefore where
  irrefl := E.happensBefore_irrefl
  trans _ _ _ := HappensBefore.trans

instance instPartialOrderEvent (E : Execution P) : PartialOrder E.Event where
  le := E.HappensBeforeLe
  lt := E.HappensBefore
  le_refl := E.happensBeforeLe_refl
  le_trans _ _ _ := HappensBeforeLe.trans
  le_antisymm _ _ := E.happensBeforeLe_antisymm
  lt_iff_le_not_ge e₁ e₂ := by
    simp only [happensBeforeLe_iff]
    constructor
    · intro h
      refine ⟨.inr h, ?_⟩
      rintro (rfl | h')
      · exact E.happensBefore_irrefl _ h
      · exact happensBefore_asymm h h'
    · rintro ⟨rfl | h, hnot⟩
      · exact absurd (.inl rfl) hnot
      · exact h

@[simp] theorem event_le_iff {E : Execution P} {e₁ e₂ : E.Event} :
    (e₁ ≤ e₂) ↔ E.HappensBeforeLe e₁ e₂ := Iff.rfl

@[simp] theorem event_lt_iff {E : Execution P} {e₁ e₂ : E.Event} :
    (e₁ < e₂) ↔ E.HappensBefore e₁ e₂ := Iff.rfl

/-! ### Concurrency -/

/-- Two events in `E` are causally concurrent if neither happens before or equals the other. -/
@[expose] def Concurrent (E : Execution P) (e₁ e₂ : E.Event) : Prop :=
  ¬ E.HappensBeforeLe e₁ e₂ ∧ ¬ E.HappensBeforeLe e₂ e₁

/-- Concurrency is irreflexive. -/
theorem concurrent_irrefl (E : Execution P) (e : E.Event) : ¬ E.Concurrent e e :=
  fun h => h.1 (E.happensBeforeLe_refl e)

/-- Concurrent events are distinct. -/
theorem Concurrent.ne {E : Execution P} {e₁ e₂ : E.Event} (h : E.Concurrent e₁ e₂) : e₁ ≠ e₂ :=
  fun heq => E.concurrent_irrefl e₁ (heq ▸ h)

/-- Concurrency is symmetric. -/
theorem concurrent_symm {E : Execution P} {e₁ e₂ : E.Event} :
    E.Concurrent e₁ e₂ ↔ E.Concurrent e₂ e₁ :=
  and_comm

/-- Causal trichotomy: any two events in `E` are equal, strictly ordered by `HappensBefore` in one
direction, or `Concurrent`. -/
theorem causal_trichotomy (E : Execution P) (e₁ e₂ : E.Event) :
    e₁ = e₂ ∨ E.HappensBefore e₁ e₂ ∨ E.HappensBefore e₂ e₁ ∨ E.Concurrent e₁ e₂ := by
  by_cases h12 : E.HappensBeforeLe e₁ e₂
  · exact (happensBeforeLe_iff.mp h12).imp_right .inl
  · by_cases h21 : E.HappensBeforeLe e₂ e₁
    · exact (happensBeforeLe_iff.mp h21).elim (fun h => .inl h.symm) fun h => .inr (.inr (.inl h))
    · exact .inr (.inr (.inr ⟨h12, h21⟩))

/-! ### Executable causal-past dynamic programming and decidability -/

instance instDecidableProgramOrder [DecidableEq P] (E : Execution P)
    (e₁ e₂ : E.Event) : Decidable (E.ProgramOrder e₁ e₂) :=
  inferInstanceAs (Decidable (e₁.actor = e₂.actor ∧ e₁.idx < e₂.idx))

instance instDecidableMessageOrder [DecidableEq P] (E : Execution P)
    (e₁ e₂ : E.Event) : Decidable (E.MessageOrder e₁ e₂) :=
  inferInstanceAs (Decidable (e₂.step = .recv e₂.actor e₁.idx.val))

instance instDecidableCausalStep [DecidableEq P] (E : Execution P)
    (e₁ e₂ : E.Event) : Decidable (E.CausalStep e₁ e₂) :=
  inferInstanceAs (Decidable (E.ProgramOrder e₁ e₂ ∨ E.MessageOrder e₁ e₂))

/-- Single dynamic-programming step appending the reflexive causal past (as trace indices) of step
`k` to `prev`. -/
@[expose] def causalPastStep [DecidableEq P] (E : Execution P) (k : ℕ)
    (hk : k < E.steps.length) (prev : List (List ℕ)) : List (List ℕ) :=
  let ek : E.Event := ⟨⟨k, hk⟩⟩
  let preds : List ℕ :=
    (List.range k).filter fun i =>
      (List.range k).any fun j =>
        if hj : j < k then
          decide (E.CausalStep ⟨⟨j, hj.trans hk⟩⟩ ek) &&
            ((prev[j]?.getD []).contains i)
        else false
  prev ++ [k :: preds]

/-- Forward dynamic-programming table computing, for the first `k` events of `E`, the reflexive
causal-past index list of each event `< k`. Pattern-matching on the recursive list forces kernel
WHNF evaluation once per step during `decide`. -/
@[expose] def causalPastLists [DecidableEq P] (E : Execution P) :
    ℕ → List (List ℕ)
  | 0 => []
  | k + 1 =>
    if hk : k < E.steps.length then
      match E.causalPastLists k with
      | [] => E.causalPastStep k hk []
      | hd :: tl => E.causalPastStep k hk (hd :: tl)
    else
      E.causalPastLists k

private theorem causalPastLists_succ_of_lt [DecidableEq P] (E : Execution P) {k : ℕ}
    (hk : k < E.steps.length) :
    E.causalPastLists (k + 1) = E.causalPastStep k hk (E.causalPastLists k) := by
  simp only [causalPastLists, hk, ↓reduceDIte]
  cases E.causalPastLists k <;> rfl

private theorem length_causalPastLists [DecidableEq P] (E : Execution P) {k : ℕ}
    (hk : k ≤ E.steps.length) : (E.causalPastLists k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [E.causalPastLists_succ_of_lt (Nat.lt_of_succ_le hk), causalPastStep,
      ih (Nat.lt_of_succ_le hk).le]

private theorem causalPastLists_getElem?_lt [DecidableEq P] (E : Execution P) {i k : ℕ}
    (hik : i < k) (hk : k ≤ E.steps.length) :
    (E.causalPastLists k)[i]? = (E.causalPastLists (i + 1))[i]? := by
  induction k with
  | zero => omega
  | succ k ih =>
    have hlt : k < E.steps.length := Nat.lt_of_succ_le hk
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hik) with hik' | rfl
    · rw [E.causalPastLists_succ_of_lt hlt, causalPastStep,
        List.getElem?_append_left (by simpa [E.length_causalPastLists hlt.le] using hik')]
      exact ih hik' hlt.le
    · rfl

private theorem contains_causalPastLists_iff [DecidableEq P] (E : Execution P) :
    ∀ (j : ℕ) (hj : j < E.steps.length) (x : E.Event),
      (((E.causalPastLists (j + 1))[j]?.getD []).contains x.idx.val = true) ↔
        E.HappensBeforeLe x ⟨⟨j, hj⟩⟩ := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj x
    have hlen : (E.causalPastLists j).length = j := E.length_causalPastLists hj.le
    rw [E.causalPastLists_succ_of_lt hj, causalPastStep, List.getElem?_append_right hlen.le, hlen,
      Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, List.contains_eq_mem,
      List.decide_mem_cons, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, List.mem_filter,
      List.mem_range, List.any_eq_true, happensBeforeLe_iff]
    constructor
    · rintro (hxeq | ⟨_, m, hm_mem, hm_ok⟩)
      · exact .inl (Event.ext (Fin.ext hxeq))
      · have hmj : m < j := List.mem_range.mp hm_mem
        simp only [hmj, ↓reduceDIte, Bool.and_eq_true, decide_eq_true_eq] at hm_ok
        rw [E.causalPastLists_getElem?_lt hmj hj.le] at hm_ok
        exact .inr (.tail' ((ih m hmj (hmj.trans hj) x).mp hm_ok.2) hm_ok.1)
    · rintro (rfl | hhb)
      · exact .inl rfl
      · obtain ⟨em, hxem, hcstep⟩ := Relation.TransGen.tail'_iff.mp hhb
        have hmj : em.idx.val < j := E.causalStep_idx_lt hcstep
        refine .inr ⟨Nat.lt_of_le_of_lt (E.happensBeforeLe_idx_le hxem) hmj, em.idx.val,
          List.mem_range.mpr hmj, ?_⟩
        have hem_eq : (⟨⟨em.idx.val, hmj.trans hj⟩⟩ : E.Event) = em := Event.ext rfl
        simp only [hmj, ↓reduceDIte, hem_eq, hcstep, decide_true, Bool.true_and,
          E.causalPastLists_getElem?_lt hmj hj.le]
        exact (ih em.idx.val hmj em.idx.isLt x).mpr hxem

/-- Executable Boolean decision procedure for `E.HappensBeforeLe e₁ e₂`. -/
@[expose] def decideHappensBeforeLe [DecidableEq P] (E : Execution P) (e₁ e₂ : E.Event) : Bool :=
  ((E.causalPastLists (e₂.idx.val + 1))[e₂.idx.val]?.getD []).contains e₁.idx.val

/-- `decideHappensBeforeLe` returns `true` iff `HappensBeforeLe` holds. -/
theorem decideHappensBeforeLe_eq_true_iff [DecidableEq P] (E : Execution P)
    {e₁ e₂ : E.Event} :
    E.decideHappensBeforeLe e₁ e₂ = true ↔ E.HappensBeforeLe e₁ e₂ :=
  E.contains_causalPastLists_iff e₂.idx.val e₂.idx.isLt e₁

/-- The computable `Finset` of events in the reflexive causal past of `e` (`{x | x ≼ e}`). -/
@[expose] def causalPastLe [DecidableEq P] (E : Execution P) (e : E.Event) : Finset E.Event :=
  Finset.univ.filter fun x => E.decideHappensBeforeLe x e

/-- The computable `Finset` of events in the strict causal past of `e` (`{x | x ≺ e}`). -/
@[expose] def causalPast [DecidableEq P] (E : Execution P) (e : E.Event) : Finset E.Event :=
  (E.causalPastLe e).erase e

@[simp] theorem mem_causalPastLe [DecidableEq P] (E : Execution P) {x e : E.Event} :
    x ∈ E.causalPastLe e ↔ E.HappensBeforeLe x e := by
  rw [causalPastLe, Finset.mem_filter_univ]
  exact E.decideHappensBeforeLe_eq_true_iff

@[simp] theorem mem_causalPast [DecidableEq P] (E : Execution P) {x e : E.Event} :
    x ∈ E.causalPast e ↔ E.HappensBefore x e := by
  simp only [causalPast, Finset.mem_erase, mem_causalPastLe, happensBeforeLe_iff]
  exact ⟨fun ⟨hne, h⟩ => h.resolve_left hne,
    fun h => ⟨fun heq => E.happensBefore_irrefl e (heq ▸ h), .inr h⟩⟩

instance instDecidableHappensBeforeLe [DecidableEq P] (E : Execution P)
    (e₁ e₂ : E.Event) : Decidable (E.HappensBeforeLe e₁ e₂) :=
  decidable_of_iff (E.decideHappensBeforeLe e₁ e₂ = true)
    E.decideHappensBeforeLe_eq_true_iff

instance instDecidableHappensBefore [DecidableEq P] (E : Execution P)
    (e₁ e₂ : E.Event) : Decidable (E.HappensBefore e₁ e₂) :=
  decidable_of_iff (e₁ ≠ e₂ ∧ E.HappensBeforeLe e₁ e₂)
    ⟨fun ⟨hne, hle⟩ => E.happensBefore_of_happensBeforeLe_of_ne hle hne,
     fun hhb => ⟨fun heq => E.happensBefore_irrefl e₂ (heq ▸ hhb), hhb.happensBeforeLe⟩⟩

instance instDecidableLTEvent [DecidableEq P] (E : Execution P) :
    DecidableLT E.Event :=
  E.instDecidableHappensBefore

instance instDecidableLEEvent [DecidableEq P] (E : Execution P) :
    DecidableLE E.Event :=
  E.instDecidableHappensBeforeLe

instance instDecidableConcurrent [DecidableEq P] (E : Execution P)
    (e₁ e₂ : E.Event) : Decidable (E.Concurrent e₁ e₂) :=
  inferInstanceAs (Decidable (¬ E.HappensBeforeLe e₁ e₂ ∧ ¬ E.HappensBeforeLe e₂ e₁))

/-! ### Consistent cuts -/

/-- A subset of events `C : Finset E.Event` is a consistent cut ([Mattern1989]) if it is downward
closed under `HappensBefore`: whenever `e₂ ∈ C` and `e₁ ≺ e₂`, `e₁ ∈ C`. -/
@[expose] def IsConsistentCut (E : Execution P) (C : Finset E.Event) : Prop :=
  ∀ ⦃e₁ e₂ : E.Event⦄, E.HappensBefore e₁ e₂ → e₂ ∈ C → e₁ ∈ C

instance instDecidableIsConsistentCut [DecidableEq P] (E : Execution P)
    (C : Finset E.Event) : Decidable (E.IsConsistentCut C) :=
  Fintype.decidableForallFintype

/-- Characterization of consistent cuts via reflexive `HappensBeforeLe`. -/
theorem isConsistentCut_iff_happensBeforeLe {E : Execution P} {C : Finset E.Event} :
    E.IsConsistentCut C ↔ ∀ ⦃e₁ e₂ : E.Event⦄, E.HappensBeforeLe e₁ e₂ → e₂ ∈ C → e₁ ∈ C := by
  refine ⟨fun hc e₁ e₂ hle he₂ => ?_, fun hc _ _ hlt => hc hlt.happensBeforeLe⟩
  exact (happensBeforeLe_iff.mp hle).elim (fun h => h ▸ he₂) (hc · he₂)

/-- Consistent cuts are downward closed under `HappensBeforeLe`. -/
theorem IsConsistentCut.mem_of_happensBeforeLe {E : Execution P} {C : Finset E.Event}
    (hc : E.IsConsistentCut C) {e₁ e₂ : E.Event} (hle : E.HappensBeforeLe e₁ e₂)
    (he₂ : e₂ ∈ C) : e₁ ∈ C :=
  isConsistentCut_iff_happensBeforeLe.mp hc hle he₂

@[simp] theorem isConsistentCut_empty (E : Execution P) : E.IsConsistentCut ∅ := by
  intro _ _ _ hmem
  exact absurd hmem (Finset.notMem_empty _)

@[simp] theorem isConsistentCut_univ (E : Execution P) : E.IsConsistentCut Finset.univ := by
  intro _ _ _ _
  exact Finset.mem_univ _

/-- Consistent cuts are closed under binary union. -/
theorem IsConsistentCut.union {E : Execution P} {C₁ C₂ : Finset E.Event}
    (h₁ : E.IsConsistentCut C₁) (h₂ : E.IsConsistentCut C₂) :
    E.IsConsistentCut (C₁ ∪ C₂) := by
  intro e₁ e₂ hhb hmem
  rcases Finset.mem_union.mp hmem with hm₁ | hm₂
  · exact Finset.mem_union_left _ (h₁ hhb hm₁)
  · exact Finset.mem_union_right _ (h₂ hhb hm₂)

/-- Consistent cuts are closed under binary intersection. -/
theorem IsConsistentCut.inter {E : Execution P} {C₁ C₂ : Finset E.Event}
    (h₁ : E.IsConsistentCut C₁) (h₂ : E.IsConsistentCut C₂) :
    E.IsConsistentCut (C₁ ∩ C₂) := by
  intro e₁ e₂ hhb hmem
  obtain ⟨hm₁, hm₂⟩ := Finset.mem_inter.mp hmem
  exact Finset.mem_inter.mpr ⟨h₁ hhb hm₁, h₂ hhb hm₂⟩

/-- The strict causal past of any event is a consistent cut. -/
theorem isConsistentCut_causalPast [DecidableEq P] (E : Execution P) (e : E.Event) :
    E.IsConsistentCut (E.causalPast e) := by
  intro e₁ e₂ h₁₂ he₂
  rw [mem_causalPast] at he₂ ⊢
  exact h₁₂.trans he₂

/-- The reflexive causal past of any event is a consistent cut. -/
theorem isConsistentCut_causalPastLe [DecidableEq P] (E : Execution P) (e : E.Event) :
    E.IsConsistentCut (E.causalPastLe e) := by
  intro e₁ e₂ h₁₂ he₂
  rw [mem_causalPastLe] at he₂ ⊢
  exact h₁₂.happensBeforeLe.trans he₂

/-- Absence of orphan receives: if a consistent cut `C` contains a receive event `e`, it also
contains the matching earlier send event `eSend`. -/
theorem IsConsistentCut.send_mem_of_recv_mem {E : Execution P} {C : Finset E.Event}
    (hc : E.IsConsistentCut C) {e : E.Event} (he : e ∈ C) {p : P} {sIdx : ℕ}
    (hrecv : e.step = .recv p sIdx) :
    ∃ eSend ∈ C, eSend.idx.val = sIdx ∧ ∃ src : P, eSend.step = .send src p := by
  obtain ⟨eSend, hval, _, hp, src, hsend⟩ := E.recv_sendEvent hrecv
  have hmsg : E.MessageOrder eSend e := E.messageOrder_of_recv (hval.symm ▸ hrecv)
  exact ⟨eSend, hc (E.messageOrder_happensBefore hmsg) he, hval, src, hsend⟩

/-! ### Process renaming functoriality -/

/-- Push forward an execution `E : Execution P` along a process map `f : P → Q`. -/
@[expose] def map {Q : Type*} (f : P → Q) (E : Execution P) : Execution Q where
  steps := E.steps.map (Step.map f)
  recv_valid := by
    intro ⟨i, hi⟩ q sIdx hstep
    have hi' : i < E.steps.length := by simpa only [List.length_map] using hi
    change (E.steps.map (Step.map f))[i] = .recv q sIdx at hstep
    rw [List.getElem_map] at hstep
    cases hst : E.steps[i] <;> rw [hst] at hstep <;> cases hstep
    obtain ⟨hs, src, hsend⟩ := E.recv_valid ⟨i, hi'⟩ _ _ hst
    exact ⟨hs, f src, by rw [List.getElem_map, hsend]; rfl⟩
  recv_injective := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ q₁ q₂ sIdx hi_eq hj_eq
    have hi' : i < E.steps.length := by simpa only [List.length_map] using hi
    have hj' : j < E.steps.length := by simpa only [List.length_map] using hj
    change (E.steps.map (Step.map f))[i] = .recv q₁ sIdx at hi_eq
    change (E.steps.map (Step.map f))[j] = .recv q₂ sIdx at hj_eq
    rw [List.getElem_map] at hi_eq hj_eq
    cases hsti : E.steps[i] <;> rw [hsti] at hi_eq <;> cases hi_eq
    cases hstj : E.steps[j] <;> rw [hstj] at hj_eq <;> cases hj_eq
    exact Fin.ext (Fin.mk.inj (E.recv_injective ⟨i, hi'⟩ ⟨j, hj'⟩ _ _ _ hsti hstj))

/-- Transport an event of `E` to the corresponding event of `E.map f`. -/
@[expose] def mapEvent {Q : Type*} (f : P → Q) {E : Execution P} (e : E.Event) :
    (E.map f).Event :=
  ⟨⟨e.idx.val, by simp only [map, List.length_map]; exact e.idx.isLt⟩⟩

/-- Inverse event transport from `E.map f` back to `E`. -/
@[expose] def unmapEvent {Q : Type*} (f : P → Q) {E : Execution P} (e' : (E.map f).Event) :
    E.Event :=
  ⟨⟨e'.idx.val, by have h := e'.idx.isLt; simp only [map, List.length_map] at h; exact h⟩⟩

private theorem map_causalStep_iff {Q : Type*} {f : P → Q} (hf : Function.Injective f)
    {E : Execution P} {e₁ e₂ : E.Event} :
    (E.map f).CausalStep (E.mapEvent f e₁) (E.mapEvent f e₂) ↔ E.CausalStep e₁ e₂ := by
  have hstep (e : E.Event) : (E.mapEvent f e).step = e.step.map f := List.getElem_map _
  have hact (e : E.Event) : (E.mapEvent f e).actor = f e.actor := by
    simp only [Event.actor, hstep, Step.actor_map]
  have hrecv (s : Step P) (a : P) (n : ℕ) : s.map f = .recv (f a) n ↔ s = .recv a n := by
    cases s <;> simp [Step.map, hf.eq_iff]
  simp only [CausalStep, ProgramOrder, MessageOrder, hstep, hact, hf.eq_iff, hrecv, Fin.lt_def]
  rfl

/-- An injective process renaming preserves and reflects `HappensBeforeLe`. -/
theorem map_happensBeforeLe_iff {Q : Type*} {f : P → Q} (hf : Function.Injective f)
    {E : Execution P} {e₁ e₂ : E.Event} :
    (E.map f).HappensBeforeLe (E.mapEvent f e₁) (E.mapEvent f e₂) ↔
      E.HappensBeforeLe e₁ e₂ :=
  ⟨fun h => Relation.ReflTransGen.lift (r := (E.map f).CausalStep) (E.unmapEvent f)
      (fun _ _ h => (map_causalStep_iff hf).mp h) _ _ h,
    fun h => Relation.ReflTransGen.lift (E.mapEvent f)
      (fun _ _ h => (map_causalStep_iff hf).mpr h) _ _ h⟩

end Execution

end Cslib.Distributed.VectorClock
