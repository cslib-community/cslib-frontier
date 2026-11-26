/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.SharedMemory.Basic
public import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Herlihy's wait-free shared-memory consensus hierarchy (`1 < 2 < ∞`)

Different shared-memory synchronization primitives have strictly different wait-free consensus
numbers — the maximum number of asynchronous crash-prone processes for which they can solve
wait-free consensus ([Herlihy1991], §3, Definition 1, p. 130 & Figure 1, p. 126; see also prior
shared-register impossibility results in [LouiAbuAmara1987] noted in [Herlihy1991], §3.1, p. 132).
Building on the bivalence and critical-configuration engine in
`CslibFrontier/Computability/Distributed/SharedMemory/Basic.lean`, this module establishes the
three fundamental levels `1 < 2 < ∞` of Herlihy's hierarchy:

* **Level `1` — Atomic read/write registers ([Herlihy1991], §3.1, Theorem 2, pp. 131–133):**
  * `oneProcProtocol` / `solvesWaitFreeConsensus_one`: when `Fintype.card P ≤ 1`, a single-step
    protocol solves wait-free consensus over any value type and any nonempty object family.
  * `not_waitFreeConsensus_registers`: when `2 ≤ Fintype.card P`, no wait-free protocol using only
    atomic multi-reader multi-writer read/write registers (`registerObj`) solves binary consensus
    ([Herlihy1991], §3.1, Theorem 2 & Figures 3–5, pp. 131–133). At a critical configuration `c*`
    with `p ≠ q` stepping to `false`-univalent and `true`-univalent configurations, operations on
    distinct registers or two reads commute, a read followed by a write is invisible to the writer's
    solo continuation, and a write followed by a write overwrites the earlier write without
    returning the overwritten value.
  * `exists_register_consensus_iff`: binary wait-free consensus is solvable from atomic read/write
    registers if and only if `Fintype.card P ≤ 1`.

* **Level `2` — Commuting-or-overwriting read-modify-write primitives ([Herlihy1991], §3.2,
  Figure 7 & Theorem 4, p. 134):**
  * `IsCommutingOrOverwriting` captures Herlihy's "interfering" algebraic obstruction for consensus
    number `2` ([Herlihy1991], §3.2, p. 134): any two operations on the same object either commute
    on the object's state or one overwrites the other's effect on the state. Atomic registers
    (`registerObj`), `testAndSetObj`, `swapObj`, and `fetchAndAddObj` (over any `AddCommSemigroup`)
    all satisfy `IsCommutingOrOverwriting`.
  * `testAndSetProtocol` / `solvesWaitFreeConsensus_testAndSet_two`: an explicit 3-step protocol
    (write own proposal register, invoke `testAndSetObj`, read the winning process's proposal
    register) formalizing the concrete `test&set` instance of [Herlihy1991], §3.2, Figure 7
    (p. 134) solves wait-free consensus whenever `Fintype.card P ≤ 2` (Theorem 3's general
    2-process lower bound over arbitrary nontrivial RMW functions remains open in `#7199`).
  * `not_waitFreeConsensus_rmw_of_three_le`: when `3 ≤ Fintype.card P`, no wait-free protocol over
    any indexed family of commuting-or-overwriting objects (including any mix of registers,
    `TestAndSet`, `Swap`, and `FetchAndAdd`; [Herlihy1991], §3.2, Theorem 4, p. 134) solves binary
    consensus, because a third bystander process `w ∉ {p, q}` running solo cannot distinguish the
    post-critical object states.
  * `exists_testAndSet_consensus_iff`: binary wait-free consensus is solvable from `TestAndSet`
    objects and atomic registers if and only if `Fintype.card P ≤ 2`.

* **Level `∞` — `CompareAndSwap` ([Herlihy1991], §3.2, Theorem 5 & Figures 8–9, p. 135):**
  * `not_isCommutingOrOverwriting_casObj` / `not_isCommutingOrOverwriting_casObj_option`:
    `casObj` is *not* commuting-or-overwriting whenever the state type has at least three distinct
    values (such as `Option V` for `[Nontrivial V]`; note that on a 2-element domain without an
    uninitialized sentinel `none`, conditional 1-bit updates degenerate to `TestAndSet`/reset).
  * `casConsensusProtocol` / `solvesWaitFreeConsensus_cas`: a 1-step protocol over a single
    `casObj (none : Option V)` ([Herlihy1991], §3.2, Figure 9, p. 135) solves wait-free consensus
    for **every** finite process set `P` and every decidable value type `V`.

## Main definitions

* `Cslib.Distributed.SharedMemory.RegOp`, `Cslib.Distributed.SharedMemory.registerObj`: atomic
  multi-reader multi-writer read/write register specification.
* `Cslib.Distributed.SharedMemory.oneProcProtocol`: 1-step consensus protocol for `|P| ≤ 1`.
* `Cslib.Distributed.SharedMemory.IsCommutingOrOverwriting`: algebraic commuting-or-overwriting
  property of a deterministic shared object.
* `Cslib.Distributed.SharedMemory.testAndSetObj`, `Cslib.Distributed.SharedMemory.swapObj`,
  `Cslib.Distributed.SharedMemory.fetchAndAddObj`: commuting-or-overwriting RMW objects.
* `Cslib.Distributed.SharedMemory.TASRegKind`: descriptor for families combining `TestAndSet`
  objects and atomic registers.
* `Cslib.Distributed.SharedMemory.TASObjId`, `Cslib.Distributed.SharedMemory.TASState`,
  `Cslib.Distributed.SharedMemory.testAndSetProtocol`: 3-step 2-process `TestAndSet` consensus
  protocol.
* `Cslib.Distributed.SharedMemory.CASOp`, `Cslib.Distributed.SharedMemory.casObj`,
  `Cslib.Distributed.SharedMemory.casConsensusProtocol`: `CompareAndSwap` object and 1-step
  `n`-process wait-free consensus protocol.

## Main results

* `Cslib.Distributed.SharedMemory.solvesWaitFreeConsensus_one`: 1-process consensus sufficiency.
* `Cslib.Distributed.SharedMemory.not_waitFreeConsensus_registers`: 2-process impossibility for
  atomic read/write registers ([Herlihy1991], §3.1, Theorem 2).
* `Cslib.Distributed.SharedMemory.exists_register_consensus_iff`: register consensus solvable iff
  `Fintype.card P ≤ 1`.
* `Cslib.Distributed.SharedMemory.isCommutingOrOverwriting_registerObj`,
  `Cslib.Distributed.SharedMemory.isCommutingOrOverwriting_testAndSetObj`,
  `Cslib.Distributed.SharedMemory.isCommutingOrOverwriting_swapObj`,
  `Cslib.Distributed.SharedMemory.isCommutingOrOverwriting_fetchAndAddObj`: commuting-or-overwriting
  proofs for registers, `TestAndSet`, `Swap`, and `FetchAndAdd`.
* `Cslib.Distributed.SharedMemory.solvesWaitFreeConsensus_testAndSetProtocol`,
  `Cslib.Distributed.SharedMemory.solvesWaitFreeConsensus_testAndSet_two`: 2-process `TestAndSet`
  consensus sufficiency.
* `Cslib.Distributed.SharedMemory.not_waitFreeConsensus_rmw_of_three_le`: 3-process impossibility
  for any family of commuting-or-overwriting objects ([Herlihy1991]).
* `Cslib.Distributed.SharedMemory.exists_testAndSet_consensus_iff`: `TestAndSet` + registers
  consensus solvable iff `Fintype.card P ≤ 2`.
* `Cslib.Distributed.SharedMemory.not_isCommutingOrOverwriting_casObj`,
  `Cslib.Distributed.SharedMemory.not_isCommutingOrOverwriting_casObj_option`: `casObj` escapes
  the commuting-or-overwriting barrier on domains of size at least `3`.
* `Cslib.Distributed.SharedMemory.solvesWaitFreeConsensus_cas`: `n`-process wait-free consensus
  from a single `CompareAndSwap` object ([Herlihy1991]).

## References

* [M. Herlihy, *Wait-Free Synchronization*][Herlihy1991]
* [M. C. Loui, H. H. Abu-Amara, *Memory Requirements for Agreement Among Unreliable Asynchronous
  Processes*][LouiAbuAmara1987]
-/

public section

namespace Cslib.Distributed.SharedMemory

open Cslib

universe u

/-! ### Shared helpers for critical-step analysis and 1-step termination -/

section Helpers

variable {P I S V : Type*} {Op Resp ObjState : I → Type*}
  [DecidableEq P] [DecidableEq I]

/-- Apply a concrete active invocation by process `p` on object `i` to configuration `c`.
Factoring `Protocol.step` through free object indices `i` avoids dependent casts when comparing two
processes targeting the same object `i₁ = i₂`. -/
private def applyAt (objs : ∀ i, ObjSpec (Op i) (Resp i) (ObjState i))
    (p : P) (i : I) (op : Op i) (next : Resp i → S) (dec : Resp i → Option V)
    (c : Config P ObjState S V) : Config P ObjState S V :=
  let res := (objs i).step op (c.mem i)
  { mem := Function.update c.mem i res.1
    proc := Function.update c.proc p { state := next res.2, decided := dec res.2 } }

private theorem step_eq_applyAt {objs : ∀ i, ObjSpec (Op i) (Resp i) (ObjState i)}
    (π : Protocol P objs S V) {p : P} {c : Config P ObjState S V} (h : c.Active p) :
    π.step p c = applyAt objs p (π.target p (c.proc p).state) (π.op p (c.proc p).state)
      (π.next p (c.proc p).state) (π.decideVal p (c.proc p).state) c :=
  π.step_of_active h

/-- Eliminate a critical bivalent configuration by reducing to the same-object `applyAt` case:
when `p ≠ q` target distinct objects, `Protocol.step_comm_of_ne_target` immediately contradicts
opposite univalence via `p`'s solo run. -/
private theorem false_of_same_object_critical [Fintype P]
    {objs : ∀ i, ObjSpec (Op i) (Resp i) (ObjState i)}
    (π : Protocol P objs S Bool) (hcons : π.SolvesWaitFreeConsensus)
    (hcard : 2 ≤ Fintype.card P)
    (hsame : ∀ (cstar : Config P ObjState S Bool) (p q : P) (_hpq : p ≠ q)
      (i : I) (op_p : Op i) (next_p : Resp i → S) (dec_p : Resp i → Option Bool)
      (op_q : Op i) (next_q : Resp i → S) (dec_q : Resp i → Option Bool),
      Acc π.StepRel (applyAt objs p i op_p next_p dec_p cstar) →
      Acc π.StepRel (applyAt objs q i op_q next_q dec_q cstar) →
      π.IsUnivalent (applyAt objs p i op_p next_p dec_p cstar) false →
      π.IsUnivalent (applyAt objs q i op_q next_q dec_q cstar) true →
      π.lts.CanReach (applyAt objs p i op_p next_p dec_p cstar)
        (applyAt objs q i op_q next_q dec_q (applyAt objs p i op_p next_p dec_p cstar)) →
      π.lts.CanReach (applyAt objs q i op_q next_q dec_q cstar)
        (applyAt objs p i op_p next_p dec_p (applyAt objs q i op_q next_q dec_q cstar)) →
      False) : False := by
  obtain ⟨inp, hbiv_init⟩ := π.exists_bivalent_init hcons hcard
  obtain ⟨cstar, p, q, hreach_star, _, hall_act, hpq, hup, huq⟩ :=
    π.exists_critical_config hcons (π.reachable_initConfig inp) hbiv_init
  have ha_star : Acc π.StepRel cstar :=
    ((π.reachable_initConfig inp).trans hreach_star).acc hcons.waitFree
  have hp_act : cstar.Active p := hall_act p
  have hq_act : cstar.Active q := hall_act q
  have ha_p : Acc π.StepRel (π.step p cstar) := ha_star.inv ⟨p, hp_act, rfl⟩
  have ha_q : Acc π.StepRel (π.step q cstar) := ha_star.inv ⟨q, hq_act, rfl⟩
  have hqp : q ≠ p := hpq.symm
  by_cases htarget : π.target p (cstar.proc p).state = π.target q (cstar.proc q).state
  · have htwo {a b : P} (ha : cstar.Active a) (hb : cstar.Active b) (hba : b ≠ a) :
        π.step b (π.step a cstar) =
          applyAt objs b (π.target b (cstar.proc b).state) (π.op b (cstar.proc b).state)
            (π.next b (cstar.proc b).state) (π.decideVal b (cstar.proc b).state)
            (applyAt objs a (π.target a (cstar.proc a).state) (π.op a (cstar.proc a).state)
              (π.next a (cstar.proc a).state) (π.decideVal a (cstar.proc a).state) cstar) := by
      have hb' : (π.step a cstar).Active b := (π.active_step_of_ne hba).mpr hb
      rw [step_eq_applyAt π hb', π.step_proc_of_ne cstar hba, ← step_eq_applyAt π ha]
    have hr_pq := π.canReach_step q (π.step p cstar)
    have hr_qp := π.canReach_step p (π.step q cstar)
    rw [htwo hp_act hq_act hqp, step_eq_applyAt π hp_act] at hr_pq
    rw [htwo hq_act hp_act hpq, step_eq_applyAt π hq_act] at hr_qp
    rw [step_eq_applyAt π hp_act] at ha_p hup
    rw [step_eq_applyAt π hq_act] at ha_q huq
    generalize π.target p (cstar.proc p).state = i₁, π.op p (cstar.proc p).state = op_p,
      π.next p (cstar.proc p).state = next_p, π.decideVal p (cstar.proc p).state = dec_p,
      π.target q (cstar.proc q).state = i₂, π.op q (cstar.proc q).state = op_q,
      π.next q (cstar.proc q).state = next_q, π.decideVal q (cstar.proc q).state = dec_q
      at htarget ha_p ha_q hup huq hr_pq hr_qp
    subst htarget
    exact hsame cstar p q hpq i₁ op_p next_p dec_p op_q next_q dec_q ha_p ha_q hup huq hr_pq hr_qp
  · have hcomm := π.step_comm_of_ne_target hp_act hq_act hpq htarget
    exact Protocol.not_univalent_of_indistinguishable p ha_p ha_q hup huq
      (π.canReach_step q (π.step p cstar)) (π.canReach_step p (π.step q cstar))
      (congrArg Config.mem hcomm) (congrFun (congrArg Config.proc hcomm) p)

private theorem waitFree_of_decides_in_one_step [Finite P]
    {objs : ∀ i, ObjSpec (Op i) (Resp i) (ObjState i)} (π : Protocol P objs S V)
    (hdec : ∀ p s r, (π.decideVal p s r).isSome = true) : π.WaitFree := by
  let _ : Fintype P := Fintype.ofFinite P
  let activeCount : Config P ObjState S V → ℕ :=
    fun c => (Finset.univ.filter fun q => c.Active q).card
  refine Protocol.WaitFree.of_wellFounded
    (Subrelation.wf ?_ (InvImage.wf activeCount wellFounded_lt))
  rintro c' c ⟨p, hact, rfl⟩
  have hnot_act : ¬ (π.step p c).Active p := fun hact' => by
    simp only [π.step_of_active hact, Config.Active, Function.update_self] at hact'
    exact Option.ne_none_iff_isSome.mpr (hdec _ _ _) hact'
  simp only [InvImage, activeCount]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hact⟩,
      fun hm => hnot_act (Finset.mem_filter.mp hm).2⟩
  · intro q hq
    rw [Finset.mem_filter] at hq ⊢
    rcases eq_or_ne q p with rfl | hqp
    · exact absurd hq.2 hnot_act
    · exact ⟨hq.1, (π.active_step_of_ne hqp).mp hq.2⟩

end Helpers

/-! ### Level 1: Atomic read/write registers -/

/-- Operations on an atomic multi-reader multi-writer read/write register storing values of type
`α`: either `read` the current value or `write` a new value (returning no information about the
overwritten state). -/
inductive RegOp (α : Type*) where
  /-- Read the register's current value. -/
  | read
  /-- Overwrite the register with `v`. -/
  | write (v : α)
  deriving @[expose] DecidableEq

/-- Specification of an atomic multi-reader multi-writer read/write register initialized to `init`:
`read` leaves the state unchanged and returns `some s`; `write v` sets the state to `v` and returns
`none`. -/
@[expose]
def registerObj {α : Type*} (init : α) : ObjSpec (RegOp α) (Option α) α where
  init := init
  step
    | .read, s => (s, some s)
    | .write v, _ => (v, none)

/-- Trivial 1-step protocol for at most one process (`Fintype.card P ≤ 1`): each process stores its
own initial input in local state, performs one dummy invocation `op₀` on `i₀`, and decides its own
input. -/
@[expose]
def oneProcProtocol {P I V : Type*} {Op Resp ObjState : I → Type*}
    (objs : ∀ i, ObjSpec (Op i) (Resp i) (ObjState i)) (i₀ : I) (op₀ : Op i₀) :
    Protocol P objs V V where
  init _ v := v
  target _ _ := i₀
  op _ _ := op₀
  next _ s _ := s
  decideVal _ s _ := some s

/-- **1-process baseline:** when `Fintype.card P ≤ 1`, `oneProcProtocol` solves wait-free consensus
over any value type `V` and any nonempty shared-object family. -/
theorem solvesWaitFreeConsensus_one {P I V : Type*} {Op Resp ObjState : I → Type*}
    [Fintype P] [DecidableEq P] [DecidableEq I]
    (objs : ∀ i, ObjSpec (Op i) (Resp i) (ObjState i)) (i₀ : I) (op₀ : Op i₀)
    (hcard : Fintype.card P ≤ 1) :
    (oneProcProtocol (P := P) (V := V) objs i₀ op₀).SolvesWaitFreeConsensus := by
  let π := oneProcProtocol (P := P) (V := V) objs i₀ op₀
  have hsub : Subsingleton P := Fintype.card_le_one_iff_subsingleton.mp hcard
  have hwf : π.WaitFree := waitFree_of_decides_in_one_step π fun _ _ _ => rfl
  let Inv (inp : P → V) (c : Config P ObjState V V) : Prop :=
    ∀ p, (c.proc p).state = inp p ∧ ∀ v, (c.proc p).decided = some v → v = inp p
  have hinv (inp c) (hr : π.Reachable inp c) : Inv inp c := by
    refine hr.induction ?_ ?_
    · exact fun _ => ⟨rfl, fun _ hv => by simp only [Protocol.initConfig, reduceCtorEq] at hv⟩
    · intro c₁ q hinit hact_q p
      rcases eq_or_ne p q with rfl | hpq
      · rw [π.step_of_active hact_q]
        simp only [π, oneProcProtocol, Function.update_self, Option.some.injEq]
        exact ⟨(hinit p).1, fun v hv => hv.symm.trans (hinit p).1⟩
      · simpa only [π.step_proc_of_ne c₁ hpq] using hinit p
  refine ⟨hwf, ?_, ?_⟩
  · rintro inp c hr v₁ v₂ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩
    rw [(hinv inp c hr p₁).2 v₁ hp₁, (hinv inp c hr p₂).2 v₂ hp₂, Subsingleton.elim p₁ p₂]
  · rintro inp c v hr ⟨p, hp⟩
    exact ⟨p, ((hinv inp c hr p).2 v hp).symm⟩

/-- **Herlihy Level-1 register impossibility ([Herlihy1991], §3.1, Theorem 2 & Figures 3–5,
pp. 131–133):** no wait-free deterministic shared-memory protocol using only atomic multi-reader
multi-writer read/write registers solves binary consensus for `2 ≤ Fintype.card P` processes. -/
theorem not_waitFreeConsensus_registers {P I S : Type*} {Val : I → Type*}
    [Fintype P] [DecidableEq P] [DecidableEq I]
    {init : ∀ i, Val i}
    (π : Protocol P (fun i => registerObj (init i)) S Bool)
    (hcard : 2 ≤ Fintype.card P) :
    ¬ π.SolvesWaitFreeConsensus := by
  intro hcons
  refine false_of_same_object_critical π hcons hcard ?_
  intro cstar p q hpq i op_p next_p dec_p op_q next_q dec_q ha_p ha_q huf hut hr_pq hr_qp
  have hqp : q ≠ p := hpq.symm
  cases op_p <;> cases op_q
  · exact Protocol.not_univalent_of_indistinguishable q ha_p ha_q huf hut hr_pq hr_qp
      (by simp only [applyAt, registerObj, Function.update_eq_self])
      (by simp only [applyAt, registerObj, Function.update_eq_self, Function.update_self,
        Function.update_of_ne hqp])
  · exact Protocol.not_univalent_of_indistinguishable q ha_p ha_q huf hut
      hr_pq (LTS.CanReach.refl _ _)
      (by simp only [applyAt, registerObj, Function.update_eq_self])
      (by simp only [applyAt, registerObj, Function.update_self])
  · exact Protocol.not_univalent_of_indistinguishable p ha_p ha_q huf hut
      (LTS.CanReach.refl _ _) hr_qp
      (by simp only [applyAt, registerObj, Function.update_eq_self])
      (by simp only [applyAt, registerObj, Function.update_self])
  · exact Protocol.not_univalent_of_indistinguishable q ha_p ha_q huf hut
      hr_pq (LTS.CanReach.refl _ _)
      (by simp only [applyAt, registerObj, Function.update_idem])
      (by simp only [applyAt, registerObj, Function.update_self])

/-- **Sharp Level-1 consensus characterization:** wait-free binary consensus
(`SolvesWaitFreeConsensus`) is solvable using atomic multi-reader multi-writer read/write registers
if and only if `Fintype.card P ≤ 1` (trivially solvable for `0` or `1` processes via
`oneProcProtocol`, and impossible for `2 ≤ Fintype.card P` by `not_waitFreeConsensus_registers`). -/
theorem exists_register_consensus_iff {P : Type*} [Fintype P] [DecidableEq P] :
    (∃ (I : Type) (_ : DecidableEq I) (Val : I → Type) (init : ∀ i, Val i) (S : Type)
      (π : Protocol P (fun i => registerObj (init i)) S Bool),
      π.SolvesWaitFreeConsensus) ↔ Fintype.card P ≤ 1 := by
  constructor
  · rintro ⟨I, _, Val, init, S, π, hcons⟩
    by_contra hgt
    exact not_waitFreeConsensus_registers π (by omega) hcons
  · intro hle
    exact ⟨Unit, inferInstance, fun _ => Bool, fun _ => false, Bool,
      oneProcProtocol (fun _ : Unit => registerObj false) () .read,
      solvesWaitFreeConsensus_one (fun _ : Unit => registerObj false) () .read hle⟩

/-! ### Level 2: Commuting-or-overwriting read-modify-write objects -/

/-- A deterministic shared object `obj` is *commuting-or-overwriting* ("interfering" in
[Herlihy1991], §3.2, p. 134) if for every pair of operations `op₁, op₂` and every object state `s`,
either `op₁` and `op₂` drive `s` to the same object state in both orders, `op₂` overwrites `op₁`'s
effect on the object state, or `op₁` overwrites `op₂`'s effect on the object state. Formulated
pointwise on `(obj.step _ _).1` for arbitrary `ObjSpec`s, this uniformly covers both
read-modify-write primitives (`testAndSetObj`, `swapObj`, `fetchAndAddObj`) and atomic read/write
registers (`registerObj`). -/
def IsCommutingOrOverwriting {Op Resp ObjState : Type*}
    (obj : ObjSpec Op Resp ObjState) : Prop :=
  ∀ op₁ op₂ s,
    (obj.step op₂ (obj.step op₁ s).1).1 = (obj.step op₁ (obj.step op₂ s).1).1 ∨
    (obj.step op₂ (obj.step op₁ s).1).1 = (obj.step op₂ s).1 ∨
    (obj.step op₁ (obj.step op₂ s).1).1 = (obj.step op₁ s).1

/-- Every atomic read/write register is commuting-or-overwriting. -/
theorem isCommutingOrOverwriting_registerObj {α : Type*} (init : α) :
    IsCommutingOrOverwriting (registerObj init) := by
  intro op₁ op₂ s
  cases op₁ <;> cases op₂ <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl)

/-- Atomic `TestAndSet` object: starts at `false`; every invocation sets the state to `true` and
returns the previous boolean value (`false` for the unique winner, `true` for all subsequent
callers). -/
@[expose]
def testAndSetObj : ObjSpec Unit Bool Bool where
  init := false
  step _ s := (true, s)

/-- `testAndSetObj` is commuting-or-overwriting. -/
theorem isCommutingOrOverwriting_testAndSetObj :
    IsCommutingOrOverwriting testAndSetObj := fun _ _ _ => Or.inl rfl

/-- Atomic `Swap` (read-and-write / exchange) object: starts at `init`; `step v s` atomically
replaces the state with `v` and returns the previous state `s`. -/
@[expose]
def swapObj {α : Type*} (init : α) : ObjSpec α α α where
  init := init
  step v s := (v, s)

/-- `swapObj` is commuting-or-overwriting (every operation overwrites the object state). -/
theorem isCommutingOrOverwriting_swapObj {α : Type*} (init : α) :
    IsCommutingOrOverwriting (swapObj init) := fun _ _ _ => Or.inr (Or.inl rfl)

/-- Atomic `FetchAndAdd` object over an additive type `G`: starts at `init`; `step d s` atomically
updates the state to `s + d` and returns the previous state `s`. -/
@[expose]
def fetchAndAddObj {G : Type*} [Add G] (init : G) : ObjSpec G G G where
  init := init
  step d s := (s + d, s)

/-- `fetchAndAddObj` over any `AddCommSemigroup` (such as `ℕ`, `ℤ`, or `ZMod n`) is
commuting-or-overwriting because increments commute on the object state. -/
theorem isCommutingOrOverwriting_fetchAndAddObj {G : Type*} [AddCommSemigroup G] (init : G) :
    IsCommutingOrOverwriting (fetchAndAddObj init) := by
  intro d₁ d₂ s
  exact Or.inl (add_right_comm s d₁ d₂)

/-! #### Explicit 3-step 2-process `TestAndSet` consensus protocol -/

/-- Descriptor for a shared object in a `TestAndSet`-plus-registers system: either an atomic
read/write register of type `α` initialized to `init`, or a `TestAndSet` object. -/
inductive TASRegKind : Type (u + 1) where
  /-- Atomic multi-reader multi-writer read/write register storing `α`. -/
  | reg (α : Type u) (init : α)
  /-- Single-bit `TestAndSet` object initialized to `false`. -/
  | tas

namespace TASRegKind

/-- Operation type of a `TASRegKind` object. -/
abbrev Op (k : TASRegKind.{u}) : Type u :=
  match k with
  | .reg α _ => RegOp α
  | .tas => PUnit

/-- Response type of a `TASRegKind` object. -/
abbrev Resp (k : TASRegKind.{u}) : Type u :=
  match k with
  | .reg α _ => Option α
  | .tas => ULift Bool

/-- State type of a `TASRegKind` object. -/
abbrev State (k : TASRegKind.{u}) : Type u :=
  match k with
  | .reg α _ => α
  | .tas => ULift Bool

/-- `ObjSpec` corresponding to a `TASRegKind` descriptor. -/
@[expose]
def toObjSpec (k : TASRegKind.{u}) : ObjSpec k.Op k.Resp k.State :=
  match k with
  | .reg _ init => registerObj init
  | .tas =>
    { init := ULift.up false
      step := fun _ s => (ULift.up true, s) }

private theorem isCommutingOrOverwriting_toObjSpec (k : TASRegKind.{u}) :
    IsCommutingOrOverwriting k.toObjSpec := by
  cases k with
  | reg _ init => exact isCommutingOrOverwriting_registerObj init
  | tas => exact fun _ _ _ => Or.inl rfl

end TASRegKind

/-- Shared-object addresses for the 2-process `TestAndSet` consensus protocol: one atomic
read/write proposal register `propReg r` per register slot `r : R`, plus one shared `TestAndSet`
object `tas`. -/
inductive TASObjId (R : Type*) where
  /-- Proposal register indexed by `r`. -/
  | propReg (r : R)
  /-- Single `TestAndSet` object arbitrating the winning proposer. -/
  | tas
  deriving @[expose] DecidableEq

/-- `TASRegKind` assignment for `TASObjId R`: proposal registers initialized to `v₀` and one
`TestAndSet` object. -/
abbrev tasKind (R : Type*) {V : Type u} (v₀ : V) : TASObjId R → TASRegKind.{u}
  | .propReg _ => .reg V v₀
  | .tas => .tas

/-- Shared-object family for 2-process `TestAndSet` consensus: proposal registers initialized to
`v₀ : V` together with `TestAndSet`. -/
abbrev tasObjFamily (R : Type*) {V : Type u} (v₀ : V)
    (i : TASObjId R) : ObjSpec (tasKind R v₀ i).Op (tasKind R v₀ i).Resp (tasKind R v₀ i).State :=
  (tasKind R v₀ i).toObjSpec

/-- Local control state of a process in the 3-step `TestAndSet` consensus protocol:
1. `writeProp v`: write own input `v` to own proposal register;
2. `invokeTAS`: invoke `TestAndSet` to determine whether this process (`false`) or its peer
   `other p` (`true`) won;
3. `readWinner r`: read the winning process's proposal register `propReg r` and decide;
4. `done`: post-decision terminal state. -/
inductive TASState (R V : Type*) where
  /-- Step 1: write own input `v` into own proposal register. -/
  | writeProp (v : V)
  /-- Step 2: invoke `TestAndSet` to arbitrate the winner. -/
  | invokeTAS
  /-- Step 3: read proposal register `r` of the winning process and decide. -/
  | readWinner (r : R)
  /-- Post-decision local state. -/
  | done
  deriving @[expose] DecidableEq

/-- Explicit 3-step wait-free consensus protocol using one proposal register per process (`regOf`)
and one `TestAndSet` object, parameterized by a peer selector `other : P → P` (`other p` names the
unique other process when `Fintype.card P = 2`). Completely kernel-computable when `regOf` and
`other` are computable. -/
@[expose]
def testAndSetProtocol {P R : Type*} {V : Type u} (regOf : P → R) (v₀ : V) (other : P → P) :
    Protocol P (tasObjFamily R v₀) (TASState R V) V where
  init _ v := .writeProp v
  target p
    | .writeProp _ => .propReg (regOf p)
    | .invokeTAS => .tas
    | .readWinner r => .propReg r
    | .done => .tas
  op _
    | .writeProp v => .write v
    | .invokeTAS => PUnit.unit
    | .readWinner _ => .read
    | .done => PUnit.unit
  next p s resp :=
    match s, resp with
    | .writeProp _, _ => .invokeTAS
    | .invokeTAS, prev => .readWinner (if prev.down then regOf (other p) else regOf p)
    | .readWinner _, _ => .done
    | .done, _ => .done
  decideVal _ s resp :=
    match s, resp with
    | .writeProp _, _ => none
    | .invokeTAS, _ => none
    | .readWinner _, some v => some v
    | .readWinner _, none => some v₀
    | .done, _ => some v₀

private def tasStageRank {R V : Type*} : TASState R V → ℕ
  | .writeProp _ => 3
  | .invokeTAS => 2
  | .readWinner _ => 1
  | .done => 0

private def tasProcRank {R V : Type*} (ps : ProcState (TASState R V) V) : ℕ :=
  match ps.decided with
  | none => tasStageRank ps.state + 1
  | some _ => 0

private theorem waitFree_testAndSetProtocol {P R : Type*} {V : Type u}
    [Finite P] [DecidableEq P] [DecidableEq R] (regOf : P → R) (v₀ : V) (other : P → P) :
    (testAndSetProtocol regOf v₀ other).WaitFree := by
  let _ : Fintype P := Fintype.ofFinite P
  let π := testAndSetProtocol regOf v₀ other
  let measure : Config P (fun i => (tasKind R v₀ i).State) (TASState R V) V → ℕ :=
    fun c => ∑ q : P, tasProcRank (c.proc q)
  refine Protocol.WaitFree.of_wellFounded (Subrelation.wf ?_ (InvImage.wf measure wellFounded_lt))
  rintro c' c ⟨p, hact, rfl⟩
  simp only [InvImage, measure]
  have hlt_p : tasProcRank ((π.step p c).proc p) < tasProcRank (c.proc p) := by
    rw [π.step_of_active hact]
    rw [Config.Active] at hact
    simp only [Function.update_self, tasProcRank, hact]
    cases (c.proc p).state <;>
      simp only [π, testAndSetProtocol, tasStageRank, tasObjFamily, tasKind,
        TASRegKind.toObjSpec, registerObj] <;> omega
  have heq_other : ∑ q ∈ Finset.univ.erase p, tasProcRank ((π.step p c).proc q) =
      ∑ q ∈ Finset.univ.erase p, tasProcRank (c.proc q) :=
    Finset.sum_congr rfl fun q hq => by rw [π.step_proc_of_ne c (Finset.ne_of_mem_erase hq)]
  dsimp only [π] at hlt_p heq_other
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p),
    ← Finset.add_sum_erase _ (fun q => tasProcRank (c.proc q)) (Finset.mem_univ p), heq_other]
  omega

private structure TASInv {P R : Type*} {V : Type u} (regOf : P → R) (v₀ : V) (inp : P → V)
    (c : Config P (fun i => (tasKind R v₀ i).State) (TASState R V) V) : Prop where
  writeProp_eq : ∀ p v, (c.proc p).state = .writeProp v → v = inp p
  reg_eq : ∀ p, (∀ v, (c.proc p).state ≠ .writeProp v) → c.mem (.propReg (regOf p)) = inp p
  done_not_active : ∀ p, (c.proc p).state = .done → ¬ c.Active p
  tas_false : (c.mem .tas).down = false →
    ∀ p, (∀ r, (c.proc p).state ≠ .readWinner r) ∧
      (c.proc p).state ≠ .done ∧ (c.proc p).decided = none
  tas_true : (c.mem .tas).down = true →
    ∃ w : P,
      ((c.proc w).state = .readWinner (regOf w) ∨ (c.proc w).state = .done) ∧
      (∀ p r, (c.proc p).state = .readWinner r → r = regOf w) ∧
      (∀ p v, (c.proc p).decided = some v → v = inp w)

private theorem TASInv.of_proc_step {P R : Type*} {V : Type u} [DecidableEq P]
    {regOf : P → R} {v₀ : V} {inp : P → V}
    {c₁ : Config P (fun i => (tasKind R v₀ i).State) (TASState R V) V}
    (hinv : TASInv regOf v₀ inp c₁) (q : P)
    (mem' : ∀ i, (tasKind R v₀ i).State) (ps : ProcState (TASState R V) V)
    (hno_wp : ∀ v, ps.state ≠ .writeProp v)
    (hreg_q : mem' (.propReg (regOf q)) = inp q)
    (hmem_ne : ∀ p, p ≠ q → mem' (.propReg (regOf p)) = c₁.mem (.propReg (regOf p)))
    (hdone_q : ps.state = .done → ps.decided ≠ none)
    (htas_f : (mem' .tas).down = false →
      (c₁.mem .tas).down = false ∧
      (∀ r, ps.state ≠ .readWinner r) ∧ ps.state ≠ .done ∧ ps.decided = none)
    (htas_t : (mem' .tas).down = true →
      ∃ w : P,
        (if w = q then ps.state = .readWinner (regOf w) ∨ ps.state = .done
         else (c₁.proc w).state = .readWinner (regOf w) ∨ (c₁.proc w).state = .done) ∧
        (∀ r, ps.state = .readWinner r → r = regOf w) ∧
        (∀ v, ps.decided = some v → v = inp w) ∧
        (∀ p, p ≠ q → ∀ r, (c₁.proc p).state = .readWinner r → r = regOf w) ∧
        (∀ p, p ≠ q → ∀ v, (c₁.proc p).decided = some v → v = inp w)) :
    TASInv regOf v₀ inp { mem := mem', proc := Function.update c₁.proc q ps } where
  writeProp_eq p v hv := by
    rcases eq_or_ne p q with rfl | hpq
    · simp only [Function.update_self] at hv; exact absurd hv (hno_wp v)
    · simp only [Function.update_of_ne hpq] at hv; exact hinv.writeProp_eq p v hv
  reg_eq p hno := by
    rcases eq_or_ne p q with rfl | hpq
    · exact hreg_q
    · dsimp only
      rw [hmem_ne p hpq]
      exact hinv.reg_eq p fun v hv => hno v (by simpa only [Function.update_of_ne hpq] using hv)
  done_not_active p hd := by
    rcases eq_or_ne p q with rfl | hpq
    · simp only [Config.Active, Function.update_self] at hd ⊢; exact hdone_q hd
    · simp only [Config.Active, Function.update_of_ne hpq] at hd ⊢; exact hinv.done_not_active p hd
  tas_false htf p := by
    obtain ⟨htf₁, hps_f⟩ := htas_f htf
    rcases eq_or_ne p q with rfl | hpq
    · simpa only [Function.update_self] using hps_f
    · simpa only [Function.update_of_ne hpq] using hinv.tas_false htf₁ p
  tas_true htt := by
    obtain ⟨w, hw_st, hps_rw, hps_dec, horw, hodec⟩ := htas_t htt
    refine ⟨w, ?_, fun p r hpr => ?_, fun p v hpv => ?_⟩
    · rcases eq_or_ne w q with rfl | hwq
      · simpa only [↓reduceIte, Function.update_self] using hw_st
      · simpa only [hwq, ↓reduceIte, Function.update_of_ne hwq] using hw_st
    · rcases eq_or_ne p q with rfl | hpq
      · simp only [Function.update_self] at hpr; exact hps_rw r hpr
      · simp only [Function.update_of_ne hpq] at hpr; exact horw p hpq r hpr
    · rcases eq_or_ne p q with rfl | hpq
      · simp only [Function.update_self] at hpv; exact hps_dec v hpv
      · simp only [Function.update_of_ne hpq] at hpv; exact hodec p hpq v hpv

/-- **Correctness of `testAndSetProtocol`:** whenever `regOf : P → R` is injective and `other p`
names the unique peer `q ≠ p` (`∀ p q, p ≠ q → other p = q`, which holds whenever
`Fintype.card P ≤ 2`), `testAndSetProtocol` solves wait-free consensus. -/
theorem solvesWaitFreeConsensus_testAndSetProtocol {P R : Type*} {V : Type u}
    [Finite P] [DecidableEq P] [DecidableEq R]
    (regOf : P → R) (hreg : Function.Injective regOf) (v₀ : V) (other : P → P)
    (hother : ∀ p q : P, p ≠ q → other p = q) :
    (testAndSetProtocol regOf v₀ other).SolvesWaitFreeConsensus := by
  let π := testAndSetProtocol regOf v₀ other
  have hwf : π.WaitFree := waitFree_testAndSetProtocol regOf v₀ other
  have hinv_reach : ∀ inp c, π.Reachable inp c → TASInv regOf v₀ inp c := by
    intro inp c hr
    refine hr.induction ?_ ?_
    · exact
        { writeProp_eq := fun _ _ hv => (TASState.writeProp.inj hv).symm
          reg_eq := fun p hno => absurd rfl (hno (inp p))
          done_not_active := fun _ hd => (nomatch hd)
          tas_false := fun _ _ => ⟨fun _ h => (nomatch h), fun h => (nomatch h), rfl⟩
          tas_true := fun htrue => Bool.noConfusion htrue }
    · intro c₁ q hinit hact_q
      cases hsq : (c₁.proc q).state with
      | writeProp vq =>
        cases hinit.writeProp_eq q vq hsq
        rw [π.step_of_active hact_q, hsq]
        dsimp only [π, testAndSetProtocol, tasObjFamily, tasKind, TASRegKind.toObjSpec, registerObj]
        refine hinit.of_proc_step q _ _ (fun _ h => (nomatch h)) (Function.update_self ..)
          (fun p hpq => Function.update_of_ne (mt TASObjId.propReg.inj (hreg.ne hpq)) ..)
          (fun h => (nomatch h))
          (fun htf => ⟨by rwa [Function.update_of_ne (by nofun)] at htf,
            fun _ h => (nomatch h), fun h => (nomatch h), rfl⟩)
          fun htt => ?_
        rw [Function.update_of_ne (by nofun)] at htt
        obtain ⟨w, hw_st, hw_rw, hw_dec⟩ := hinit.tas_true htt
        have hwq : w ≠ q := fun h => by
          subst h; rcases hw_st with h | h <;> rw [hsq] at h <;> nomatch h
        exact ⟨w, ⟨by simp only [hwq, ↓reduceIte]; exact hw_st,
          fun _ h => (nomatch h), fun _ h => (nomatch h),
          fun p _ => hw_rw p, fun p _ => hw_dec p⟩⟩
      | invokeTAS =>
        have hreg_q : c₁.mem (.propReg (regOf q)) = inp q :=
          hinit.reg_eq q fun _ hv => by rw [hsq] at hv; exact nomatch hv
        cases htas_cell : c₁.mem .tas with
        | up btas =>
          rw [π.step_of_active hact_q, hsq]
          dsimp only [π, testAndSetProtocol, tasObjFamily, tasKind, TASRegKind.toObjSpec]
          rw [htas_cell]
          refine hinit.of_proc_step q _ _ (fun _ h => (nomatch h))
            (by rw [Function.update_of_ne (by nofun), hreg_q])
            (fun _ _ => Function.update_of_ne (by nofun) ..) (fun h => (nomatch h))
            (fun htf => by rw [Function.update_self] at htf; exact Bool.noConfusion htf) fun _ => ?_
          cases btas with
          | false =>
            have hprev_f := hinit.tas_false (by rw [htas_cell])
            exact ⟨q, ⟨by simp, fun _ h => (TASState.readWinner.inj h).symm,
              fun _ h => (nomatch h), fun p _ r h => absurd h ((hprev_f p).1 r),
              fun p _ _ h => by rw [(hprev_f p).2.2] at h; exact nomatch h⟩⟩
          | true =>
            obtain ⟨w, hw_st, hw_rw, hw_dec⟩ := hinit.tas_true (by rw [htas_cell])
            have hwq : w ≠ q := fun h => by
              subst h; rcases hw_st with h | h <;> rw [hsq] at h <;> nomatch h
            exact ⟨w, ⟨by simp only [hwq, ↓reduceIte]; exact hw_st,
              fun _ h => (TASState.readWinner.inj h).symm.trans (by simp [hother q w hwq.symm]),
              fun _ h => (nomatch h), fun p _ => hw_rw p, fun p _ => hw_dec p⟩⟩
      | readWinner r =>
        have htas_true_eq : (c₁.mem .tas).down = true := by
          cases ht : (c₁.mem .tas).down with
          | false => exact absurd hsq ((hinit.tas_false ht q).1 r)
          | true => rfl
        obtain ⟨w, hw_st, hw_rw, hw_dec⟩ := hinit.tas_true htas_true_eq
        cases hw_rw q r hsq
        have hmem_w : c₁.mem (.propReg (regOf w)) = inp w :=
          hinit.reg_eq w fun _ hv => by rcases hw_st with h | h <;> rw [h] at hv <;> nomatch hv
        rw [π.step_of_active hact_q, hsq]
        dsimp only [π, testAndSetProtocol, tasObjFamily, tasKind, TASRegKind.toObjSpec, registerObj]
        rw [Function.update_eq_self, hmem_w]
        refine hinit.of_proc_step q _ _ (fun _ h => (nomatch h))
          (hinit.reg_eq q fun _ hv => by rw [hsq] at hv; exact nomatch hv)
          (fun _ _ => rfl) (fun _ h => (nomatch h))
          (fun htf => Bool.noConfusion (htas_true_eq.symm.trans htf)) fun _ =>
          ⟨w, ⟨by split_ifs <;> [exact Or.inr rfl; exact hw_st],
            fun _ h => (nomatch h), fun _ h => (Option.some.inj h).symm,
            fun p _ => hw_rw p, fun p _ => hw_dec p⟩⟩
      | done =>
        exact absurd hact_q (hinit.done_not_active q hsq)
  refine ⟨hwf, fun inp c hr v₁ v₂ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ => ?_, fun inp c v hr ⟨p, hp⟩ => ?_⟩
  · have hinv := hinv_reach inp c hr
    cases ht : (c.mem .tas).down with
    | false => rw [(hinv.tas_false ht p₁).2.2] at hp₁; nomatch hp₁
    | true => obtain ⟨w, _, _, hw_dec⟩ := hinv.tas_true ht; rw [hw_dec p₁ v₁ hp₁, hw_dec p₂ v₂ hp₂]
  · have hinv := hinv_reach inp c hr
    cases ht : (c.mem .tas).down with
    | false => rw [(hinv.tas_false ht p).2.2] at hp; nomatch hp
    | true => obtain ⟨w, _, _, hw_dec⟩ := hinv.tas_true ht; exact ⟨w, (hw_dec p v hp).symm⟩

private theorem exists_other_of_card_le_two {P : Type*} [Fintype P]
    (hcard : Fintype.card P ≤ 2) : ∃ other : P → P, ∀ p q : P, p ≠ q → other p = q := by
  classical
  refine ⟨fun p => if h : ∃ q : P, q ≠ p then Classical.choose h else p, fun p q hpq => ?_⟩
  have hex : ∃ r : P, r ≠ p := ⟨q, hpq.symm⟩
  simp only [hex, ↓reduceDIte]
  by_contra hrq
  have := (Finset.card_eq_three.mpr ⟨p, q, _, hpq, (Classical.choose_spec hex).symm,
    Ne.symm hrq, rfl⟩).symm.trans_le (Finset.card_le_univ _)
  omega

/-- **2-process `TestAndSet` sufficiency (`test&set` instance of [Herlihy1991], §3.2, Figure 7,
p. 134):** whenever `Fintype.card P ≤ 2`, there is a 3-step `testAndSetProtocol` solving wait-free
consensus over `P` and `V` (Theorem 3's general 2-process lower bound over arbitrary nontrivial RMW
functions is outside this module). -/
theorem solvesWaitFreeConsensus_testAndSet_two {P : Type*} {V : Type u} [Fintype P] [DecidableEq P]
    (v₀ : V) (hcard : Fintype.card P ≤ 2) :
    ∃ other : P → P, (testAndSetProtocol (id : P → P) v₀ other).SolvesWaitFreeConsensus := by
  obtain ⟨other, hother⟩ := exists_other_of_card_le_two hcard
  exact ⟨other, solvesWaitFreeConsensus_testAndSetProtocol id Function.injective_id v₀ other hother⟩

/-- **Herlihy's Level-2 impossibility ([Herlihy1991], §3.2, Theorem 4, p. 134):** when
`3 ≤ Fintype.card P`, no wait-free deterministic shared-memory protocol over any indexed family of
commuting-or-overwriting shared objects (including any combination of atomic read/write registers,
`testAndSetObj`, `swapObj`, and `fetchAndAddObj`) solves binary consensus. -/
theorem not_waitFreeConsensus_rmw_of_three_le {P I S : Type*} {Op Resp ObjState : I → Type*}
    [Fintype P] [DecidableEq P] [DecidableEq I]
    {objs : ∀ i, ObjSpec (Op i) (Resp i) (ObjState i)}
    (hobj : ∀ i, IsCommutingOrOverwriting (objs i))
    (π : Protocol P objs S Bool)
    (hcard : 3 ≤ Fintype.card P) :
    ¬ π.SolvesWaitFreeConsensus := by
  intro hcons
  refine false_of_same_object_critical π hcons (by omega) ?_
  intro cstar p q _ i op_p next_p dec_p op_q next_q dec_q ha_p ha_q huf hut hr_pq hr_qp
  obtain ⟨w, hwp, hwq⟩ : ∃ w : P, w ≠ p ∧ w ≠ q := by
    obtain ⟨w, -, hw_notin⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := Finset.univ)
      (s := {p, q}) (Finset.card_le_two.trans_lt (by rw [Finset.card_univ]; omega))
    exact ⟨w, by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hw_notin⟩
  rcases hobj i op_p op_q (cstar.mem i) with hcomm | hover_q | hover_p
  · refine Protocol.not_univalent_of_indistinguishable w ha_p ha_q huf hut hr_pq hr_qp ?_ ?_
    · simp only [applyAt, Function.update_self, Function.update_idem, hcomm]
    · simp only [applyAt, Function.update_of_ne hwp, Function.update_of_ne hwq]
  · refine Protocol.not_univalent_of_indistinguishable w ha_p ha_q huf hut
      hr_pq (LTS.CanReach.refl _ _) ?_ ?_
    · simp only [applyAt, Function.update_self, Function.update_idem, hover_q]
    · simp only [applyAt, Function.update_of_ne hwp, Function.update_of_ne hwq]
  · refine Protocol.not_univalent_of_indistinguishable w ha_p ha_q huf hut
      (LTS.CanReach.refl _ _) hr_qp ?_ ?_
    · simp only [applyAt, Function.update_self, Function.update_idem, hover_p]
    · simp only [applyAt, Function.update_of_ne hwp, Function.update_of_ne hwq]

/-- **Sharp Level-2 `TestAndSet` consensus characterization ([Herlihy1991], §3.2, Figure 7 &
Theorem 4, p. 134):** wait-free binary consensus (`SolvesWaitFreeConsensus`) is solvable using
`TestAndSet` objects and atomic read/write registers if and only if `Fintype.card P ≤ 2` (solvable
for `0`, `1`, or `2` processes via `testAndSetProtocol`, and impossible for `3 ≤ Fintype.card P` by
`not_waitFreeConsensus_rmw_of_three_le`). -/
theorem exists_testAndSet_consensus_iff {P : Type*} [Fintype P] [DecidableEq P] :
    (∃ (I : Type) (_ : DecidableEq I) (kind : I → TASRegKind.{0}) (S : Type)
      (π : Protocol P (fun i => (kind i).toObjSpec) S Bool),
      π.SolvesWaitFreeConsensus) ↔ Fintype.card P ≤ 2 := by
  constructor
  · rintro ⟨I, _, kind, S, π, hcons⟩
    by_contra hgt
    exact not_waitFreeConsensus_rmw_of_three_le
      (fun i => (kind i).isCommutingOrOverwriting_toObjSpec) π (by omega) hcons
  · intro hle
    let e : P ≃ Fin (Fintype.card P) := Fintype.equivFin P
    obtain ⟨other, hother⟩ := exists_other_of_card_le_two hle
    exact ⟨TASObjId (Fin (Fintype.card P)), inferInstance,
      tasKind (Fin (Fintype.card P)) false, TASState (Fin (Fintype.card P)) Bool,
      testAndSetProtocol (fun p => e p) false other,
      solvesWaitFreeConsensus_testAndSetProtocol (fun p => e p) e.injective false other hother⟩

/-! ### Level `∞`: `CompareAndSwap` -/

/-- Operation of an atomic `CompareAndSwap` (`CAS`) object over values of type `α`: compare the
current state against `expected`, and if equal replace it with `desired`. -/
structure CASOp (α : Type*) where
  /-- Expected current value required for the update to take effect. -/
  expected : α
  /-- Desired replacement value written when the state equals `expected`. -/
  desired : α
  deriving @[expose] DecidableEq

/-- Atomic value-returning `CompareAndSwap` (`compare&swap` in [Herlihy1991]): starts at `init`;
`step ⟨expected, desired⟩ s` replaces `s` with `desired` iff `s = expected`, and returns the
previous value `s`. -/
@[expose]
def casObj {α : Type*} [DecidableEq α] (init : α) : ObjSpec (CASOp α) α α where
  init := init
  step op s := (if s = op.expected then op.desired else s, s)

/-- On any state domain containing three pairwise distinct values `a, b, c`, `casObj` is **not**
commuting-or-overwriting: from state `a`, `CAS(a, b)` and `CAS(a, c)` neither commute (`b ≠ c`)
nor overwrite one another (`b ≠ c`). -/
theorem not_isCommutingOrOverwriting_casObj {α : Type*} [DecidableEq α] (init : α)
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ IsCommutingOrOverwriting (casObj init) := by
  intro hco
  have h := hco ⟨a, b⟩ ⟨a, c⟩ a
  simp [casObj, hab.symm, hac.symm, hbc, hbc.symm] at h

/-- `casObj` over `Option V` (for any `[Nontrivial V]`, including `Option Bool`) is not
commuting-or-overwriting. -/
theorem not_isCommutingOrOverwriting_casObj_option {V : Type*} [DecidableEq V] [Nontrivial V] :
    ¬ IsCommutingOrOverwriting (casObj (none : Option V)) := by
  obtain ⟨v₀, v₁, hv⟩ := exists_pair_ne V
  exact not_isCommutingOrOverwriting_casObj (a := none) (b := some v₀) (c := some v₁) none
    (fun h => nomatch h) (fun h => nomatch h) (fun h => hv (Option.some.inj h))

/-- Herlihy's 1-step `n`-process wait-free consensus protocol using a single `CompareAndSwap`
object initialized to `none : Option V`: each process `p` stores its input `s = inp p` and invokes
`CAS(none, some s)`. If `CAS` returns `none`, `p` won and decides `s`; if `CAS` returns `some w`,
`p` adopts and decides the winner's value `w`. -/
@[expose]
def casConsensusProtocol (P V : Type*) [DecidableEq V] :
    Protocol P (fun _ : Unit => casObj (none : Option V)) V V where
  init _ v := v
  target _ _ := ()
  op _ s := { expected := none, desired := some s }
  next _ s _ := s
  decideVal _ s resp :=
    match resp with
    | none => some s
    | some w => some w

/-- **`n`-process `CompareAndSwap` consensus ([Herlihy1991], §3.2, Theorem 5 & Figures 8–9,
p. 135):** `casConsensusProtocol` solves wait-free consensus for **every** finite process set `P`
(`consensus number = ∞`) and every decidable value type `V`. -/
theorem solvesWaitFreeConsensus_cas {P V : Type*} [Finite P] [DecidableEq P] [DecidableEq V] :
    (casConsensusProtocol P V).SolvesWaitFreeConsensus := by
  let π := casConsensusProtocol P V
  have hwf : π.WaitFree := by
    refine waitFree_of_decides_in_one_step π fun _ _ r => ?_
    cases r <;> rfl
  let Inv (inp : P → V) (c : Config P (fun _ : Unit => Option V) V V) : Prop :=
    (∀ p, (c.proc p).state = inp p) ∧
      (c.mem () = none → ∀ p, (c.proc p).decided = none) ∧
      ∀ w, c.mem () = some w → (∃ q, inp q = w) ∧ ∀ p v, (c.proc p).decided = some v → v = w
  have hinv (inp c) (hr : π.Reachable inp c) : Inv inp c := by
    refine hr.induction ?_ ?_
    · exact ⟨fun _ => rfl, fun _ _ => rfl,
        fun _ hw => by simp only [Protocol.initConfig, casObj, reduceCtorEq] at hw⟩
    · intro c₁ q ⟨hst, hnone, hsome⟩ hact_q
      -- Both `CAS` outcomes install some winner `w'` and let `q` decide it.
      obtain ⟨w', hw_valid, hw_dec, hstep_c⟩ : ∃ w', (∃ q, inp q = w') ∧
          (∀ p v, (c₁.proc p).decided = some v → v = w') ∧
          π.step q c₁ =
            { mem := Function.update c₁.mem () (some w')
              proc := Function.update c₁.proc q { state := inp q, decided := some w' } } := by
        rw [π.step_of_active hact_q]
        cases hmem : c₁.mem () with
        | none =>
          refine ⟨inp q, ⟨q, rfl⟩, fun p v hpv => ?_, ?_⟩
          · rw [hnone hmem p] at hpv; exact nomatch hpv
          · simp only [π, casConsensusProtocol, casObj, hst q, ↓reduceIte]
        | some w₀ =>
          refine ⟨w₀, (hsome w₀ hmem).1, (hsome w₀ hmem).2, ?_⟩
          simp only [π, casConsensusProtocol, casObj, hst q, reduceCtorEq, ↓reduceIte]
      rw [hstep_c]
      refine ⟨fun p => ?_, ⟨fun hn => ?_, fun w hw => ?_⟩⟩
      · rcases eq_or_ne p q with rfl | hpq
        · simp only [Function.update_self]
        · simpa only [Function.update_of_ne hpq] using hst p
      · simp only [Function.update_self, reduceCtorEq] at hn
      · obtain rfl : w' = w := by simpa only [Function.update_self, Option.some.injEq] using hw
        refine ⟨hw_valid, fun p v hpv => ?_⟩
        rcases eq_or_ne p q with rfl | hpq
        · simpa only [Function.update_self, Option.some.injEq] using hpv.symm
        · exact hw_dec p v (by simpa only [Function.update_of_ne hpq] using hpv)
  have hdec_of {inp c p v} (hr : π.Reachable inp c) (hp : (c.proc p).decided = some v) :
      c.mem () = some v ∧ ∃ q, inp q = v := by
    obtain ⟨_, hnone, hsome⟩ := hinv inp c hr
    cases hm : c.mem () with
    | none =>
      rw [hnone hm p] at hp
      exact nomatch hp
    | some w =>
      obtain ⟨hq, hdec⟩ := hsome w hm
      obtain rfl := hdec p v hp
      exact ⟨rfl, hq⟩
  refine ⟨hwf, fun inp c hr v₁ v₂ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ => ?_,
    fun inp c v hr ⟨p, hp⟩ => (hdec_of hr hp).2⟩
  exact Option.some.inj ((hdec_of hr hp₁).1.symm.trans (hdec_of hr hp₂).1)

end Cslib.Distributed.SharedMemory
