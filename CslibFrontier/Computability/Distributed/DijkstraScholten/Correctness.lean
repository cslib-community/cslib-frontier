/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.DijkstraScholten.Basic
public import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Filter

/-!
# Invariants, soundness, and drain liveness of the Dijkstra–Scholten overlay

This module proves safety (no false termination) and drain liveness (guaranteed detection once the
diffusing computation ceases) for the asynchronous single-parent Dijkstra–Scholten overlay defined
in `CslibFrontier/Computability/Distributed/DijkstraScholten/Basic.lean`, as a milestone step
toward `#7286` after [DijkstraScholten1980] (inspected in author manuscript `EWD687a`,
`EWD687a - 2`–`5`, PDF pp. 5–8). General non-diffusing termination detection via message-counting
vectors or credits (see [Mattern1987] for context) and `EWD687a`'s deferred-cornet bags remain
tracked in `#7286`.

All invariants are completely ghost-free (stated purely over `active`, `deficit`, `parent`,
`basicMsgs`, and `signals`):

1. **Neutrality invariant (`Reachable.neutral_of_parent_none`):** for every `p ≠ root`,
   `parent p = none` implies `active p = false ∧ deficit p = 0` (the single-parent counterpart of
   invariant P3 in `EWD687a - 2`, PDF p. 5).
2. **Exact deficit conservation (`Reachable.deficit_eq_inFlight_add_children`):** for every `p`,
   `deficit p = inFlightBasicFrom p + inFlightSignalTo p + (children root p).card`.
3. **Engagement-tree reachability & acyclicity (`Reachable.engaged_reaches_root`,
   `Reachable.ancestor?_ne_self_of_pos`):** every `p ≠ root` with `parent p ≠ none` reaches `root`
   along `parent` links in `0 < k < Fintype.card P` hops, and `parent` pointers never form a cycle.
   Because `deficit src ≥ 1` while `⟨src, dst⟩` is in flight and while `dst` remains attached as a
   child of `src`, `src` cannot detach before `dst` either acknowledges immediately or detaches.
4. **Termination soundness (`Reachable.terminated_implies_quiescent`,
   `Reachable.terminated_iff_globalQuiescence`):** in every reachable state, `s.Terminated root`
   holds iff `s.GlobalQuiescent` holds (counterpart of Theorem 2 in `EWD687a - 5`, PDF p. 8).
5. **Drain liveness (`Reachable.quiescent_drains_to_terminated`):** from any reachable
   `ComputationIdle` state (`∀ p, active p = false` and `basicMsgs = 0`), every enabled step is a
   `recvSignal` or `detach` step reducing `drainMeasure = 2 * engagedCount + inFlightSignals` by
   `1`, and every maximal execution reaches `Terminated root` in at most
   `2 * Fintype.card P + inFlightSignals` steps (counterpart of Theorem 1 in `EWD687a - 3`,
   PDF p. 6).
6. **Sequential-polling counterexample (`exists_phantom_termination_naive_poll`):** an original
   3-role execution showing that sequential `active = false` polling without channel/deficit
   accounting reports false termination when a basic message crosses from an unpolled process to an
   already-polled process while Dijkstra–Scholten's `Terminated root` remains `false`.

## Main definitions

* `Cslib.Distributed.DijkstraScholten.State.inFlightBasicFrom`: count of in-flight basic messages
  sent by `p`.
* `Cslib.Distributed.DijkstraScholten.State.inFlightSignalTo`,
  `Cslib.Distributed.DijkstraScholten.State.inFlightSignals`: per-recipient and total in-flight
  signal counts.
* `Cslib.Distributed.DijkstraScholten.State.children`: set of non-root processes `q` with
  `parent q = some p`.
* `Cslib.Distributed.DijkstraScholten.State.engagedNodes`,
  `Cslib.Distributed.DijkstraScholten.State.engagedCount`: non-root processes currently engaged in
  the tree (`parent ≠ none`) and their count.
* `Cslib.Distributed.DijkstraScholten.State.drainMeasure`: exact potential
  `2 * engagedCount + inFlightSignals` strictly decreasing during signal/detach draining.
* `Cslib.Distributed.DijkstraScholten.State.ancestor?`: `k`-hop `parent`-pointer walk from `p`.

## Main results

* `Cslib.Distributed.DijkstraScholten.Reachable.root_parent_eq_none`: `root` never acquires a
  `parent` pointer in any reachable configuration.
* `Cslib.Distributed.DijkstraScholten.Reachable.neutral_of_parent_none`,
  `Cslib.Distributed.DijkstraScholten.Reachable.attach_iff`: detached non-root processes are idle
  with zero deficit, matching full local neutrality.
* `Cslib.Distributed.DijkstraScholten.Reachable.deficit_eq_inFlight_add_children`: exact
  per-process deficit conservation across in-flight messages, signals, and tree children.
* `Cslib.Distributed.DijkstraScholten.Reachable.engaged_reaches_root`: every engaged non-root
  process follows `parent` pointers to `root` in fewer than `Fintype.card P` steps.
* `Cslib.Distributed.DijkstraScholten.Reachable.ancestor?_ne_self_of_pos`: `parent` pointers form
  no cycles in any reachable configuration.
* `Cslib.Distributed.DijkstraScholten.Reachable.terminated_implies_quiescent`,
  `Cslib.Distributed.DijkstraScholten.Reachable.terminated_iff_globalQuiescence`: root termination
  implies (and is equivalent to) full network quiescence.
* `Cslib.Distributed.DijkstraScholten.State.ComputationIdle.step_drainMeasure`,
  `Cslib.Distributed.DijkstraScholten.State.ComputationIdle.mtr_drainMeasure`,
  `Cslib.Distributed.DijkstraScholten.Reachable.isTerminal_iff_terminated_of_computationIdle`,
  `Cslib.Distributed.DijkstraScholten.Reachable.quiescent_drains_to_terminated`: unit-drop drain
  potential, deadlock-freedom until `Terminated`, and guaranteed bounded detection within
  `2 * Fintype.card P + inFlightSignals` steps under every schedule once basic activity ceases.
* `Cslib.Distributed.DijkstraScholten.exists_phantom_termination_naive_poll`: sequential local
  `active = false` polling admits phantom termination across an in-flight basic message.

## References

* [E. W. Dijkstra, C. S. Scholten,
  *Termination Detection for Diffusing Computations*][DijkstraScholten1980]
* [F. Mattern, *Algorithms for Distributed Termination Detection*][Mattern1987]
-/

public section

namespace Cslib.Distributed.DijkstraScholten

open Cslib

namespace State

variable {P : Type*}

/-- Number of in-flight basic messages sent by `p`. -/
@[expose]
def inFlightBasicFrom [DecidableEq P] (s : State P) (p : P) : ℕ :=
  (s.basicMsgs.filter fun m => m.src = p).card

/-- Number of in-flight acknowledgement signals addressed to `p`. -/
@[expose]
def inFlightSignalTo [DecidableEq P] (s : State P) (p : P) : ℕ :=
  s.signals.count p

/-- Total number of acknowledgement signals currently in flight. -/
@[expose]
def inFlightSignals (s : State P) : ℕ :=
  s.signals.card

/-- Finite set of non-root processes `q` currently attached with `parent = some p`. -/
@[expose]
def children [Fintype P] [DecidableEq P] (s : State P) (root p : P) : Finset P :=
  Finset.univ.filter fun q => q ≠ root ∧ (s.proc q).parent = some p

/-- Finite set of non-root processes currently engaged in the tree (`parent ≠ none`). -/
@[expose]
def engagedNodes [Fintype P] [DecidableEq P] (s : State P) (root : P) : Finset P :=
  Finset.univ.filter fun p => p ≠ root ∧ (s.proc p).parent ≠ none

/-- Number of non-root processes currently engaged in the tree. -/
@[expose]
def engagedCount [Fintype P] [DecidableEq P] (s : State P) (root : P) : ℕ :=
  (s.engagedNodes root).card

/-- Strict termination potential for control-traffic draining once basic computation ceases:
each `detach` reduces `engagedCount` by `1` and emits `1` signal (net `-1`), while each
`recvSignal` consumes `1` signal (net `-1`). -/
@[expose]
def drainMeasure [Fintype P] [DecidableEq P] (s : State P) (root : P) : ℕ :=
  2 * s.engagedCount root + s.inFlightSignals

/-- Follow `parent` pointers from `p` for `k` hops, returning `none` if `parent = none` is hit
before `k` hops complete. -/
@[expose]
def ancestor? (s : State P) : ℕ → P → Option P
  | 0, p => some p
  | k + 1, p =>
    match (s.proc p).parent with
    | none => none
    | some q => s.ancestor? k q

@[simp]
theorem ancestor?_zero (s : State P) (p : P) : s.ancestor? 0 p = some p := rfl

private theorem ancestor?_add (s : State P) (a b : ℕ) (p : P) :
    s.ancestor? (a + b) p = (s.ancestor? a p).bind (s.ancestor? b) := by
  induction a generalizing p with
  | zero =>
    simp [ancestor?, Option.bind]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [ancestor?]
    cases (s.proc p).parent <;> simp [ih]

private theorem ancestor?_pos_of_parent_none {s : State P} {p : P}
    (hp : (s.proc p).parent = none) {k : ℕ} (hk : 0 < k) : s.ancestor? k p = none := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp [ancestor?, hp]

private theorem engagedCount_lt_card [Fintype P] [DecidableEq P] (s : State P) (root : P) :
    s.engagedCount root < Fintype.card P := by
  rw [engagedCount, ← Finset.card_univ]
  refine Finset.card_lt_card (Finset.ssubset_univ_iff.mpr fun h => ?_)
  exact (Finset.mem_filter.mp (h.symm ▸ Finset.mem_univ root)).2.1 rfl

private theorem drainMeasure_le [Fintype P] [DecidableEq P] (s : State P) (root : P) :
    s.drainMeasure root ≤ 2 * Fintype.card P + s.inFlightSignals := by
  have h := s.engagedCount_lt_card root
  simp only [drainMeasure]
  omega

end State

/-! ### Shared frame helpers for `children` and `engagedNodes` -/

private theorem children_congr {P : Type*} [Fintype P] [DecidableEq P] {s₁ s₂ : State P}
    (hpar : ∀ q, (s₁.proc q).parent = (s₂.proc q).parent) (root p : P) :
    s₁.children root p = s₂.children root p := by
  ext q
  simp only [State.children, Finset.mem_filter, Finset.mem_univ, true_and, hpar q]

private theorem engagedNodes_congr {P : Type*} [Fintype P] [DecidableEq P] {s₁ s₂ : State P}
    (hpar : ∀ q, (s₁.proc q).parent = (s₂.proc q).parent) (root : P) :
    s₁.engagedNodes root = s₂.engagedNodes root := by
  ext q
  simp only [State.engagedNodes, Finset.mem_filter, Finset.mem_univ, true_and, hpar q]

private theorem parent_eq_of_update_same_parent {P : Type*} [DecidableEq P] (s : State P)
    (u : P) (act : Bool) (defc : ℕ) (q : P) :
    (Function.update s.proc u { active := act, deficit := defc, parent := (s.proc u).parent }
      q).parent = (s.proc q).parent := by
  by_cases hq : q = u <;> simp [hq]

/-! ### Structural invariants: root parent, neutrality (P3), and exact deficit conservation -/

private theorem trInv_root_parent {P : Type*} [DecidableEq P] (root : P) :
    (lts root).TrInv (fun s => (s.proc root).parent = none) := by
  intro s a s' htr hinv
  cases a with
  | sendBasic src dst =>
    obtain ⟨_, rfl⟩ := tr_sendBasic_iff.mp htr
    simpa [State.sendBasicState] using
      (parent_eq_of_update_same_parent s src (s.proc src).active ((s.proc src).deficit + 1)
        root).trans hinv
  | recvBasic src dst =>
    obtain ⟨_, rfl⟩ := tr_recvBasic_iff.mp htr
    simp only [State.recvBasicState]
    split_ifs with hatt
    · have hne : root ≠ dst := Ne.symm hatt.1
      simp [Function.update_of_ne hne, hinv]
    · exact (parent_eq_of_update_same_parent s dst true (s.proc dst).deficit root).trans hinv
  | becomeIdle p =>
    obtain ⟨_, rfl⟩ := tr_becomeIdle_iff.mp htr
    exact (parent_eq_of_update_same_parent s p false (s.proc p).deficit root).trans hinv
  | recvSignal p =>
    obtain ⟨_, rfl⟩ := tr_recvSignal_iff.mp htr
    exact (parent_eq_of_update_same_parent s p (s.proc p).active ((s.proc p).deficit - 1)
      root).trans hinv
  | detach p q =>
    obtain ⟨_, rfl⟩ := tr_detach_iff.mp htr
    by_cases h : root = p <;> simp [State.detachState, h, hinv]

/-- `root` never acquires a `parent` pointer in any reachable configuration. -/
theorem Reachable.root_parent_eq_none {P : Type*} [DecidableEq P] {root : P} {s : State P}
    (hr : Reachable root s) : (s.proc root).parent = none := by
  obtain ⟨tr, hmtr⟩ := hr
  exact LTS.mtrInv_of_trInv (trInv_root_parent root) _ tr s hmtr rfl

private theorem trInv_neutral_of_parent_none {P : Type*} [DecidableEq P] (root : P) :
    (lts root).TrInv (fun s =>
      ∀ p, p ≠ root → (s.proc p).parent = none →
        (s.proc p).active = false ∧ (s.proc p).deficit = 0) := by
  intro s a s' htr hinv p hp hpar
  cases a with
  | sendBasic src dst =>
    obtain ⟨hact, rfl⟩ := tr_sendBasic_iff.mp htr
    simp only [State.sendBasicState] at hpar ⊢
    rcases eq_or_ne p src with rfl | h
    · simp [(hinv p hp (by simpa using hpar)).1] at hact
    · simpa [h] using hinv p hp (by simpa [h] using hpar)
  | recvBasic src dst =>
    obtain ⟨_, rfl⟩ := tr_recvBasic_iff.mp htr
    simp only [State.recvBasicState] at hpar ⊢
    split_ifs at hpar ⊢ with hatt <;> rcases eq_or_ne p dst with rfl | h
    · simp at hpar
    · simpa [h] using hinv p hp (by simpa [h] using hpar)
    · exact False.elim (hatt ⟨hp, by simpa using hpar⟩)
    · simpa [h] using hinv p hp (by simpa [h] using hpar)
  | becomeIdle q =>
    obtain ⟨_, rfl⟩ := tr_becomeIdle_iff.mp htr
    simp only [State.becomeIdleState] at hpar ⊢
    rcases eq_or_ne p q with rfl | h
    · simp [(hinv p hp (by simpa using hpar)).2]
    · simpa [h] using hinv p hp (by simpa [h] using hpar)
  | recvSignal q =>
    obtain ⟨_, rfl⟩ := tr_recvSignal_iff.mp htr
    simp only [State.recvSignalState] at hpar ⊢
    rcases eq_or_ne p q with rfl | h
    · obtain ⟨ha, hd⟩ := hinv p hp (by simpa using hpar)
      simp [ha, hd]
    · simpa [h] using hinv p hp (by simpa [h] using hpar)
  | detach q r =>
    obtain ⟨⟨_, hact, hdef, _⟩, rfl⟩ := tr_detach_iff.mp htr
    simp only [State.detachState] at hpar ⊢
    rcases eq_or_ne p q with rfl | h
    · simp [hact, hdef]
    · simpa [h] using hinv p hp (by simpa [h] using hpar)

/-- Single-parent counterpart of invariant P3 after [DijkstraScholten1980] (`EWD687a - 2`,
PDF p. 5) toward `#7286`: in any reachable state, every detached non-root process (`parent = none`)
is idle and has zero deficit. -/
theorem Reachable.neutral_of_parent_none {P : Type*} [DecidableEq P] {root : P} {s : State P}
    (hr : Reachable root s) {p : P} (hp : p ≠ root) (hpar : (s.proc p).parent = none) :
    (s.proc p).active = false ∧ (s.proc p).deficit = 0 := by
  obtain ⟨tr, hmtr⟩ := hr
  exact LTS.mtrInv_of_trInv (trInv_neutral_of_parent_none root) _ tr s hmtr
    (fun q hq _ => by simp [initState, hq]) p hp hpar

/-- In any reachable state, the tree-attachment check `dst ≠ root ∧ parent dst = none` is
equivalent to full local neutrality (`dst ≠ root ∧ active = false ∧ deficit = 0 ∧ parent = none`).
-/
theorem Reachable.attach_iff {P : Type*} [DecidableEq P] {root : P} {s : State P}
    (hr : Reachable root s) (dst : P) :
    (dst ≠ root ∧ (s.proc dst).parent = none) ↔
      (dst ≠ root ∧ (s.proc dst).active = false ∧ (s.proc dst).deficit = 0 ∧
        (s.proc dst).parent = none) :=
  ⟨fun ⟨hdst, hpar⟩ =>
    let ⟨ha, hd⟩ := hr.neutral_of_parent_none hdst hpar
    ⟨hdst, ha, hd, hpar⟩,
   fun ⟨hdst, _, _, hpar⟩ => ⟨hdst, hpar⟩⟩

private theorem deficit_eq_of_update_same_deficit {P : Type*} [DecidableEq P] (s : State P)
    (u : P) (act : Bool) (par : Option P) (q : P) :
    (Function.update s.proc u { active := act, deficit := (s.proc u).deficit, parent := par }
      q).deficit = (s.proc q).deficit := by
  by_cases hq : q = u <;> simp [Function.update, hq]

private theorem recvBasicState_deficit {P : Type*} [DecidableEq P] (s : State P)
    (root src dst p : P) :
    ((s.recvBasicState root src dst).proc p).deficit = (s.proc p).deficit := by
  simp only [State.recvBasicState]
  split_ifs <;> exact deficit_eq_of_update_same_deficit s dst true _ p

private theorem children_attach {P : Type*} [Fintype P] [DecidableEq P] (s : State P)
    {root dst : P} (src : P) (hdst : dst ≠ root) (hpar : (s.proc dst).parent = none) (p : P) :
    let s' : State P :=
      { proc := Function.update s.proc dst { s.proc dst with active := true, parent := some src }
        basicMsgs := s.basicMsgs.erase ⟨src, dst⟩
        signals := s.signals }
    (s'.children root p).card = (if src = p then 1 else 0) + (s.children root p).card := by
  intro s'
  have hnotMem : dst ∉ s.children root p := by simp [State.children, hpar]
  have heq : s'.children root p =
      if src = p then insert dst (s.children root p) else s.children root p := by
    ext q
    by_cases hq : q = dst <;>
      split_ifs with h <;> simp [State.children, s', hdst, hpar, h, hq]
  rw [heq]
  split_ifs <;> simp [Finset.card_insert_of_notMem hnotMem, Nat.add_comm]

private theorem children_detach {P : Type*} [Fintype P] [DecidableEq P] (s : State P)
    {root p q : P} (hp : p ≠ root) (hpar : (s.proc p).parent = some q) (r : P) :
    ((s.detachState p q).children root r).card + (if q = r then 1 else 0) =
      (s.children root r).card := by
  have heq : (s.detachState p q).children root r =
      if q = r then (s.children root r).erase p else s.children root r := by
    ext x
    by_cases hx : x = p <;>
      split_ifs with hqr <;>
        simp [State.children, State.detachState, Function.update_apply, hpar, hqr, hx]
  rw [heq]
  split_ifs with hqr
  · exact Finset.card_erase_add_one (by simp [State.children, hp, hqr ▸ hpar])
  · simp

private theorem trInv_deficit_conservation {P : Type*} [Fintype P] [DecidableEq P] (root : P) :
    (lts root).TrInv (fun s =>
      ∀ p : P, (s.proc p).deficit =
        s.inFlightBasicFrom p + s.inFlightSignalTo p + (s.children root p).card) := by
  intro s a s' htr hinv p
  cases a with
  | sendBasic src dst =>
    obtain ⟨_, rfl⟩ := tr_sendBasic_iff.mp htr
    have hcons := hinv p
    have hbasic : (s.sendBasicState src dst).inFlightBasicFrom p =
        (if src = p then 1 else 0) + s.inFlightBasicFrom p := by
      simp only [State.inFlightBasicFrom, State.sendBasicState, Multiset.filter_cons,
        Multiset.card_add, apply_ite Multiset.card, Multiset.card_singleton, Multiset.card_zero]
    have hchild : (s.sendBasicState src dst).children root p = s.children root p :=
      children_congr
        (parent_eq_of_update_same_parent s src (s.proc src).active ((s.proc src).deficit + 1))
        root p
    rw [hbasic, hchild]
    simp only [State.sendBasicState, State.inFlightSignalTo] at hcons ⊢
    rcases eq_or_ne p src with rfl | h
    · simp only [Function.update_self, ↓reduceIte]; omega
    · simp only [Function.update_of_ne h, Ne.symm h, ↓reduceIte]; omega
  | recvBasic src dst =>
    obtain ⟨hmem, rfl⟩ := tr_recvBasic_iff.mp htr
    have hcons := hinv p
    have hbasic : s.inFlightBasicFrom p =
        (if src = p then 1 else 0) +
          ((s.basicMsgs.erase ⟨src, dst⟩).filter fun m => m.src = p).card := by
      conv_lhs => rw [State.inFlightBasicFrom, ← Multiset.cons_erase hmem]
      simp only [Multiset.filter_cons, Multiset.card_add, apply_ite Multiset.card,
        Multiset.card_singleton, Multiset.card_zero]
    rw [recvBasicState_deficit]
    simp only [State.recvBasicState]
    split_ifs with hatt
    · have hch := children_attach s src hatt.1 hatt.2 p
      simp only at hch
      rw [hch]
      simp only [State.inFlightBasicFrom, State.inFlightSignalTo] at hcons hbasic ⊢
      omega
    · have hch := children_congr
        (s₁ := ⟨Function.update s.proc dst { s.proc dst with active := true },
          s.basicMsgs.erase ⟨src, dst⟩, src ::ₘ s.signals⟩)
        (parent_eq_of_update_same_parent s dst true (s.proc dst).deficit) root p
      rw [hch]
      simp only [State.inFlightBasicFrom, State.inFlightSignalTo, Multiset.count_cons,
        eq_comm (a := p)] at hcons hbasic ⊢
      omega
  | becomeIdle q =>
    obtain ⟨_, rfl⟩ := tr_becomeIdle_iff.mp htr
    rw [children_congr (parent_eq_of_update_same_parent s q false (s.proc q).deficit) root p]
    simpa only [State.becomeIdleState, State.inFlightBasicFrom, State.inFlightSignalTo,
      deficit_eq_of_update_same_deficit s q false (s.proc q).parent p] using hinv p
  | recvSignal q =>
    obtain ⟨hmem, rfl⟩ := tr_recvSignal_iff.mp htr
    have hcons := hinv p
    have hsig : s.inFlightSignalTo p =
        (s.recvSignalState q).inFlightSignalTo p + if p = q then 1 else 0 := by
      simp only [State.inFlightSignalTo, State.recvSignalState]
      conv_lhs => rw [← Multiset.cons_erase hmem, Multiset.count_cons]
    have hch : (s.recvSignalState q).children root p = s.children root p :=
      children_congr
        (parent_eq_of_update_same_parent s q (s.proc q).active ((s.proc q).deficit - 1)) root p
    rw [hch]
    rcases eq_or_ne p q with rfl | hp
    · simp only [State.recvSignalState, State.inFlightBasicFrom, Function.update_self,
        ↓reduceIte] at hcons hsig ⊢
      omega
    · simp only [State.recvSignalState, State.inFlightBasicFrom, Function.update_of_ne hp, hp,
        ↓reduceIte] at hcons hsig ⊢
      omega
  | detach q r =>
    obtain ⟨⟨hq, _, _, hpar⟩, rfl⟩ := tr_detach_iff.mp htr
    have hcons := hinv p
    have hch := children_detach s hq hpar p
    have hsig : (s.detachState q r).inFlightSignalTo p =
        s.inFlightSignalTo p + if p = r then 1 else 0 :=
      Multiset.count_cons p r s.signals
    have hdef : ((s.detachState q r).proc p).deficit = (s.proc p).deficit :=
      deficit_eq_of_update_same_deficit s q (s.proc q).active none p
    change _ = s.inFlightBasicFrom p + _ + _
    rw [hdef, hsig]
    simp only [eq_comm (a := p)]
    omega

/-- Exact per-process deficit conservation for the single-parent asynchronous overlay after
[DijkstraScholten1980] (`EWD687a - 1`–`5`, PDF pp. 4–8) toward `#7286`: in every reachable
configuration, `deficit p` equals the sum of in-flight basic messages from `p`, in-flight signals
to `p`, and non-root children currently holding `parent = some p`. -/
theorem Reachable.deficit_eq_inFlight_add_children {P : Type*} [Fintype P] [DecidableEq P]
    {root : P} {s : State P} (hr : Reachable root s) (p : P) :
    (s.proc p).deficit =
      s.inFlightBasicFrom p + s.inFlightSignalTo p + (s.children root p).card := by
  obtain ⟨tr, hmtr⟩ := hr
  refine LTS.mtrInv_of_trInv (trInv_deficit_conservation root) _ tr s hmtr (fun q => ?_) p
  simp [State.inFlightBasicFrom, State.inFlightSignalTo, State.children, initState]

/-! ### Engagement-tree reachability to `root` and acyclicity (P4) -/

private theorem ancestor?_eq_root_unique {P : Type*} {s : State P} {root p : P}
    (hroot : (s.proc root).parent = none) {k₁ k₂ : ℕ}
    (h₁ : s.ancestor? k₁ p = some root) (h₂ : s.ancestor? k₂ p = some root) : k₁ = k₂ := by
  wlog hle : k₁ ≤ k₂ generalizing k₁ k₂
  · exact (this (k₁ := k₂) (k₂ := k₁) h₂ h₁ (by omega)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rfl
  · rw [State.ancestor?_add, h₁] at h₂
    simp [Option.bind, State.ancestor?_pos_of_parent_none hroot hd] at h₂

private theorem lt_card_of_ancestor?_eq_root {P : Type*} [Fintype P] {s : State P} {root p : P}
    (hroot : (s.proc root).parent = none) {k : ℕ} (hk : s.ancestor? k p = some root) :
    k < Fintype.card P := by
  have hbind (i : Fin (k + 1)) :
      some root = (s.ancestor? i.val p).bind (s.ancestor? (k - i.val)) := by
    rw [← State.ancestor?_add, Nat.add_sub_cancel' (Nat.le_of_lt_succ i.isLt), hk]
  have hsome (i : Fin (k + 1)) : (s.ancestor? i.val p).isSome := by
    have := hbind i
    cases hval : s.ancestor? i.val p <;> simp [hval] at this ⊢
  let f : Fin (k + 1) → P := fun i => (s.ancestor? i.val p).get (hsome i)
  have hrest (i : Fin (k + 1)) : s.ancestor? (k - i.val) (f i) = some root := by
    have := (hbind i).symm
    rwa [← Option.some_get (hsome i)] at this
  have hinj : Function.Injective f := fun i j hij => by
    have := ancestor?_eq_root_unique hroot (hrest i)
      ((congrArg (s.ancestor? (k - j.val)) hij).trans (hrest j))
    ext
    omega
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hcard
  omega

private theorem ancestor?_congr_of_parent_eq {P : Type*} {s s' : State P}
    (hpar : ∀ x, (s'.proc x).parent = (s.proc x).parent) (k : ℕ) (p : P) :
    s'.ancestor? k p = s.ancestor? k p := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    simp only [State.ancestor?, hpar p]
    cases (s.proc p).parent <;> simp [ih]

private theorem ancestor?_preserve_of_attach {P : Type*} {s s' : State P} {root u : P}
    (hu_none : (s.proc u).parent = none)
    (hpar : ∀ x, x ≠ u → (s'.proc x).parent = (s.proc x).parent) :
    ∀ k p, s.ancestor? k p = some root → s'.ancestor? k p = some root := by
  intro k
  induction k with
  | zero => exact fun _ hp => hp
  | succ k ih =>
    intro p hp
    have hpu : p ≠ u := by
      rintro rfl
      simp [State.ancestor?, hu_none] at hp
    simp only [State.ancestor?, hpar p hpu] at hp ⊢
    cases hq : (s.proc p).parent with
    | none => simp [hq] at hp
    | some q => rw [hq] at hp; exact ih q hp

private theorem ancestor?_preserve_of_detach {P : Type*} {s s' : State P} {root u : P}
    (hleaf : ∀ c, (s.proc c).parent ≠ some u)
    (hpar : ∀ x, x ≠ u → (s'.proc x).parent = (s.proc x).parent) :
    ∀ k p, p ≠ u → s.ancestor? k p = some root → s'.ancestor? k p = some root := by
  intro k
  induction k with
  | zero => exact fun _ _ hp => hp
  | succ k ih =>
    intro p hpu hp
    simp only [State.ancestor?, hpar p hpu] at hp ⊢
    cases hq : (s.proc p).parent with
    | none => simp [hq] at hp
    | some q => rw [hq] at hp; exact ih q (by rintro rfl; exact hleaf p hq) hp

private theorem mtr_reaches_root {P : Type*} [Finite P] [DecidableEq P] (root : P)
    {tr : List (Action P)} {s : State P} (hmtr : (lts root).MTr (initState root) tr s) :
    ∀ p, p = root ∨ (s.proc p).parent ≠ none → ∃ k, s.ancestor? k p = some root := by
  cases nonempty_fintype P
  induction tr using List.reverseRecOn generalizing s with
  | nil =>
    obtain rfl := LTS.MTr.nil_eq (lts root) hmtr
    rintro p (rfl | hpar)
    · exact ⟨0, rfl⟩
    · simp [initState] at hpar
  | append_singleton tr a ih =>
    obtain ⟨s₀, hmtr₀, htr⟩ := (LTS.MTr.append_iff (lts root)).mp hmtr
    have hstep : (lts root).Tr s₀ a s := (LTS.MTr.singleton_iff (lts root) s₀ a s).mp htr
    have hr₀ : Reachable root s₀ := ⟨tr, hmtr₀⟩
    have ih₀ := ih hmtr₀
    have of_same_parent : ∀ {s' : State P},
        (∀ x, (s'.proc x).parent = (s₀.proc x).parent) →
        ∀ p, p = root ∨ (s'.proc p).parent ≠ none → ∃ k, s'.ancestor? k p = some root := by
      intro s' hpar p hp
      rw [hpar p] at hp
      obtain ⟨k, hk⟩ := ih₀ p hp
      exact ⟨k, (ancestor?_congr_of_parent_eq hpar k p).trans hk⟩
    cases a with
    | sendBasic src dst =>
      obtain ⟨_, rfl⟩ := tr_sendBasic_iff.mp hstep
      exact of_same_parent
        (parent_eq_of_update_same_parent s₀ src (s₀.proc src).active ((s₀.proc src).deficit + 1))
    | recvBasic src dst =>
      obtain ⟨hmem, rfl⟩ := tr_recvBasic_iff.mp hstep
      simp only [State.recvBasicState]
      split_ifs with hatt
      · let s' : State P :=
          { proc := Function.update s₀.proc dst
              { s₀.proc dst with active := true, parent := some src }
            basicMsgs := s₀.basicMsgs.erase ⟨src, dst⟩
            signals := s₀.signals }
        have hpar_ne : ∀ x, x ≠ dst → (s'.proc x).parent = (s₀.proc x).parent := fun x hx =>
          Function.update_of_ne hx _ s₀.proc ▸ rfl
        have hsrc_eng : src = root ∨ (s₀.proc src).parent ≠ none :=
          or_iff_not_imp_left.mpr fun hsr hnone => by
            have hd0 := (hr₀.neutral_of_parent_none hsr hnone).2
            have hpos : 0 < s₀.inFlightBasicFrom src :=
              Multiset.card_pos_iff_exists_mem.mpr ⟨_, Multiset.mem_filter.mpr ⟨hmem, rfl⟩⟩
            have hcons := hr₀.deficit_eq_inFlight_add_children src
            omega
        obtain ⟨k_src, hk_src⟩ := ih₀ src hsrc_eng
        have hk_src' : s'.ancestor? k_src src = some root :=
          ancestor?_preserve_of_attach hatt.2 hpar_ne k_src src hk_src
        intro p hp
        by_cases hpd : p = dst
        · subst hpd
          exact ⟨k_src + 1, by simp [State.ancestor?, s', hk_src']⟩
        · have hp₀ : p = root ∨ (s₀.proc p).parent ≠ none :=
            hp.imp id (fun hpar' => hpar_ne p hpd ▸ hpar')
          obtain ⟨k, hk⟩ := ih₀ p hp₀
          exact ⟨k, ancestor?_preserve_of_attach hatt.2 hpar_ne k p hk⟩
      · exact of_same_parent (parent_eq_of_update_same_parent s₀ dst true (s₀.proc dst).deficit)
    | becomeIdle q =>
      obtain ⟨_, rfl⟩ := tr_becomeIdle_iff.mp hstep
      exact of_same_parent (parent_eq_of_update_same_parent s₀ q false (s₀.proc q).deficit)
    | recvSignal q =>
      obtain ⟨_, rfl⟩ := tr_recvSignal_iff.mp hstep
      exact of_same_parent
        (parent_eq_of_update_same_parent s₀ q (s₀.proc q).active ((s₀.proc q).deficit - 1))
    | detach q r =>
      obtain ⟨⟨hq_ne, _, hdef0, _⟩, rfl⟩ := tr_detach_iff.mp hstep
      have hleaf (c : P) (hc : (s₀.proc c).parent = some q) : False := by
        rcases eq_or_ne c root with rfl | hcr
        · simp [hr₀.root_parent_eq_none] at hc
        · have hpos : 0 < (s₀.children root q).card :=
            Finset.card_pos.mpr ⟨c, by simp [State.children, hcr, hc]⟩
          have hcons := hr₀.deficit_eq_inFlight_add_children q
          omega
      have hpar_ne : ∀ x, x ≠ q → ((s₀.detachState q r).proc x).parent = (s₀.proc x).parent :=
        fun x hx => by simp [State.detachState, Function.update_of_ne hx]
      intro p hp
      have hpq : p ≠ q := by
        rintro rfl
        rcases hp with rfl | hpar'
        exacts [hq_ne rfl, hpar' (by simp [State.detachState])]
      obtain ⟨k, hk⟩ := ih₀ p (hp.imp id fun hpar' => hpar_ne p hpq ▸ hpar')
      exact ⟨k, ancestor?_preserve_of_detach hleaf hpar_ne k p hpq hk⟩

/-- Engagement-tree invariant for the single-parent asynchronous overlay after
[DijkstraScholten1980] (`EWD687a - 4`–`5`, observations a)–c), PDF pp. 7–8) toward `#7286`: in
every reachable configuration, every engaged non-root process follows `parent` pointers to `root`
in `0 < k < Fintype.card P` hops. -/
theorem Reachable.engaged_reaches_root {P : Type*} [Fintype P] [DecidableEq P] {root : P}
    {s : State P} (hr : Reachable root s) {p : P} (hp : p ≠ root)
    (hpar : (s.proc p).parent ≠ none) :
    ∃ k < Fintype.card P, 0 < k ∧ s.ancestor? k p = some root := by
  obtain ⟨tr, hmtr⟩ := hr
  obtain ⟨k, hk⟩ := mtr_reaches_root root hmtr p (Or.inr hpar)
  have hlt := lt_card_of_ancestor?_eq_root (Reachable.root_parent_eq_none ⟨tr, hmtr⟩) hk
  exact ⟨k, hlt, Nat.pos_of_ne_zero fun h => hp (by simpa [h] using hk), hk⟩

/-- Acyclicity of `parent` pointers across the entire network after [DijkstraScholten1980]
(`EWD687a - 5`, observation b), PDF p. 8) toward `#7286`: no process returns to itself along any
positive number of `parent` hops in a reachable configuration. -/
theorem Reachable.ancestor?_ne_self_of_pos {P : Type*} [Finite P] [DecidableEq P] {root : P}
    {s : State P} (hr : Reachable root s) (p : P) {m : ℕ} (hm : 0 < m) :
    s.ancestor? m p ≠ some p := by
  cases nonempty_fintype P
  intro hcyc
  have hpar : (s.proc p).parent ≠ none := fun hnone => by
    simp [State.ancestor?_pos_of_parent_none hnone hm] at hcyc
  obtain ⟨k, _, _, hk⟩ := hr.engaged_reaches_root
    (by rintro rfl; exact hpar hr.root_parent_eq_none) hpar
  have hmk : s.ancestor? (m + k) p = some root := by rw [State.ancestor?_add, hcyc]; exact hk
  have heq := ancestor?_eq_root_unique hr.root_parent_eq_none hmk hk
  omega

/-! ### Termination soundness: zero false positives (`Terminated ↔ GlobalQuiescent`) -/

/-- Termination soundness for the single-parent asynchronous overlay after [DijkstraScholten1980]
(counterpart of Theorem 2 in `EWD687a - 5`, PDF p. 8) toward `#7286`: in any reachable
configuration, if `root` is idle with `deficit = 0`, then every process is idle with zero deficit
and `parent = none`, and all basic and signal channels are empty. -/
theorem Reachable.terminated_implies_quiescent {P : Type*} [Finite P] [DecidableEq P] {root : P}
    {s : State P} (hr : Reachable root s) (ht : s.Terminated root) :
    s.GlobalQuiescent := by
  cases nonempty_fintype P
  have hpar_all : ∀ p : P, (s.proc p).parent = none := by
    intro p
    by_cases hpr : p = root
    · subst hpr; exact hr.root_parent_eq_none
    · by_contra hpar
      obtain ⟨k, _, hk_pos, hk⟩ := hr.engaged_reaches_root hpr hpar
      rw [show k = (k - 1) + 1 by omega, State.ancestor?_add, Option.bind_eq_some_iff] at hk
      obtain ⟨c, -, hstep_c⟩ := hk
      cases hcp : (s.proc c).parent with
      | none => simp [State.ancestor?, hcp] at hstep_c
      | some q =>
        simp only [State.ancestor?, hcp, Option.some.injEq] at hstep_c
        subst q
        have hcr : c ≠ root := fun h => by rw [h, hr.root_parent_eq_none] at hcp; cases hcp
        have hpos : 0 < (s.children root root).card :=
          Finset.card_pos.mpr ⟨c, by simp [State.children, hcr, hcp]⟩
        have hcons := hr.deficit_eq_inFlight_add_children root
        have hd0 := ht.2
        omega
  have hproc : ∀ p : P,
      (s.proc p).active = false ∧ (s.proc p).deficit = 0 ∧ (s.proc p).parent = none := by
    intro p
    by_cases hpr : p = root
    · subst hpr; exact ⟨ht.1, ht.2, hr.root_parent_eq_none⟩
    · obtain ⟨ha, hd⟩ := hr.neutral_of_parent_none hpr (hpar_all p)
      exact ⟨ha, hd, hpar_all p⟩
  have hbasic : s.basicMsgs = 0 := by
    refine Multiset.eq_zero_of_forall_notMem fun m hm => ?_
    have hpos : 0 < s.inFlightBasicFrom m.src :=
      Multiset.card_pos_iff_exists_mem.mpr ⟨m, Multiset.mem_filter.mpr ⟨hm, rfl⟩⟩
    have hcons := hr.deficit_eq_inFlight_add_children m.src
    have hd0 := (hproc m.src).2.1
    omega
  have hsig : s.signals = 0 := by
    refine Multiset.eq_zero_of_forall_notMem fun q hq => ?_
    have hpos : 0 < s.inFlightSignalTo q := Multiset.count_pos.mpr hq
    have hcons := hr.deficit_eq_inFlight_add_children q
    have hd0 := (hproc q).2.1
    omega
  exact ⟨hproc, hbasic, hsig⟩

/-- In any reachable configuration of the single-parent asynchronous overlay after
[DijkstraScholten1980] (`EWD687a - 5`, Theorem 2, PDF p. 8) toward `#7286`, local root termination
coincides with global network quiescence. -/
theorem Reachable.terminated_iff_globalQuiescence {P : Type*} [Finite P] [DecidableEq P]
    {root : P} {s : State P} (hr : Reachable root s) :
    s.Terminated root ↔ s.GlobalQuiescent :=
  ⟨hr.terminated_implies_quiescent, fun hq => hq.terminated root⟩

/-! ### Drain liveness: strict potential decrease and guaranteed bounded detection -/

/-- From any `ComputationIdle` configuration, every enabled transition in `lts root` is either a
`recvSignal` or `detach` control step, preserves `ComputationIdle`, and decreases `drainMeasure` by
`1`. -/
theorem State.ComputationIdle.step_drainMeasure {P : Type*} [Fintype P] [DecidableEq P] {root : P}
    {s s' : State P} {a : Action P} (hidle : s.ComputationIdle) (htr : (lts root).Tr s a s') :
    ((∃ p, a = .recvSignal p) ∨ (∃ p q, a = .detach p q)) ∧
      s'.ComputationIdle ∧ s'.drainMeasure root + 1 = s.drainMeasure root := by
  cases a with
  | sendBasic src dst =>
    obtain ⟨hact, _⟩ := tr_sendBasic_iff.mp htr
    simp [hidle.1 src] at hact
  | recvBasic src dst =>
    obtain ⟨hmem, _⟩ := tr_recvBasic_iff.mp htr
    simp [hidle.2] at hmem
  | becomeIdle p =>
    obtain ⟨hact, _⟩ := tr_becomeIdle_iff.mp htr
    simp [hidle.1 p] at hact
  | recvSignal p =>
    obtain ⟨hmem, rfl⟩ := tr_recvSignal_iff.mp htr
    set s₁ := s.recvSignalState p
    refine ⟨Or.inl ⟨p, rfl⟩, ?_, ?_⟩
    · refine ⟨fun q => ?_, hidle.2⟩
      simp only [s₁, State.recvSignalState]
      by_cases hq : q = p <;> simp [hq, hidle.1]
    · have heng : s₁.engagedNodes root = s.engagedNodes root :=
        engagedNodes_congr
          (parent_eq_of_update_same_parent s p (s.proc p).active ((s.proc p).deficit - 1)) root
      have hcard : s₁.inFlightSignals + 1 = s.inFlightSignals := by
        simp only [State.inFlightSignals, s₁, State.recvSignalState]
        conv_rhs => rw [← Multiset.cons_erase hmem]
        simp
      simp only [State.drainMeasure, State.engagedCount, heng]
      omega
  | detach p q =>
    obtain ⟨⟨hp_ne, _, _, hpar⟩, rfl⟩ := tr_detach_iff.mp htr
    set s₁ := s.detachState p q
    refine ⟨Or.inr ⟨p, q, rfl⟩, ?_, ?_⟩
    · refine ⟨fun x => ?_, hidle.2⟩
      simp only [s₁, State.detachState]
      by_cases hx : x = p <;> simp [hx, hidle.1]
    · have hmem : p ∈ s.engagedNodes root := by
        simp [State.engagedNodes, hp_ne, hpar]
      have heng : s₁.engagedNodes root = (s.engagedNodes root).erase p := by
        ext x
        by_cases hx : x = p <;> simp [State.engagedNodes, s₁, State.detachState, hx]
      have hcard_eng : (s₁.engagedNodes root).card + 1 = (s.engagedNodes root).card := by
        rw [heng, Finset.card_erase_add_one hmem]
      have hsig : s₁.inFlightSignals = s.inFlightSignals + 1 := by
        simp [State.inFlightSignals, s₁, State.detachState]
      simp only [State.drainMeasure, State.engagedCount]
      omega

/-- Multi-step drain accounting: every trace from a `ComputationIdle` configuration preserves
`ComputationIdle` and satisfies `s'.drainMeasure root + tr.length = s.drainMeasure root`. -/
theorem State.ComputationIdle.mtr_drainMeasure {P : Type*} [Fintype P] [DecidableEq P] {root : P}
    {s s' : State P} {tr : List (Action P)} (hidle : s.ComputationIdle)
    (hmtr : (lts root).MTr s tr s') :
    s'.ComputationIdle ∧ s'.drainMeasure root + tr.length = s.drainMeasure root := by
  induction hmtr with
  | refl => exact ⟨hidle, Nat.add_zero _⟩
  | stepL htr _ ih =>
    obtain ⟨_, hidle₁, hstep⟩ := hidle.step_drainMeasure htr
    obtain ⟨hidle₂, hrest⟩ := ih hidle₁
    exact ⟨hidle₂, by simp only [List.length_cons]; omega⟩

/-- Deadlock-freedom during draining: a reachable `ComputationIdle` configuration has no enabled
transitions in `lts root` iff `root` has already detected `Terminated`. -/
theorem Reachable.isTerminal_iff_terminated_of_computationIdle {P : Type*} [Finite P]
    [DecidableEq P] {root : P} {s : State P} (hr : Reachable root s)
    (hidle : s.ComputationIdle) :
    (lts root).IsTerminal s ↔ s.Terminated root := by
  cases nonempty_fintype P
  constructor
  · intro hterm
    by_contra hnotTerm
    by_cases hsig : s.signals = 0
    · have hroot_def : 0 < (s.proc root).deficit :=
        Nat.pos_of_ne_zero fun h0 => hnotTerm ⟨hidle.1 root, h0⟩
      have hdef_eq (x : P) : (s.proc x).deficit = (s.children root x).card := by
        have hcons := hr.deficit_eq_inFlight_add_children x
        simp only [State.inFlightBasicFrom, hidle.2, Multiset.filter_zero, Multiset.card_zero,
          State.inFlightSignalTo, hsig, Multiset.count_zero, Nat.zero_add] at hcons
        exact hcons
      have hchild_eng {x c : P} (hc : c ∈ s.children root x) : c ∈ s.engagedNodes root := by
        simp only [State.children, Finset.mem_filter, Finset.mem_univ, true_and] at hc
        simp [State.engagedNodes, hc.1, hc.2]
      obtain ⟨c₀, hc₀⟩ := Finset.card_pos.mp (hroot_def.trans_eq (hdef_eq root))
      have hex (x : P) (hx : x ∈ s.engagedNodes root) : ∃ k, s.ancestor? k x = some root := by
        simp only [State.engagedNodes, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        exact (hr.engaged_reaches_root hx.1 hx.2).imp fun _ h => h.2.2
      let dist : P → ℕ := fun x => if hx : x ∈ s.engagedNodes root then Nat.find (hex x hx) else 0
      have hdist (x : P) (hx : x ∈ s.engagedNodes root) : s.ancestor? (dist x) x = some root := by
        simpa [dist, hx] using Nat.find_spec (hex x hx)
      obtain ⟨p, hp_mem, hp_max⟩ :=
        (s.engagedNodes root).exists_max_image dist ⟨c₀, hchild_eng hc₀⟩
      have hp_eng := hp_mem
      simp only [State.engagedNodes, Finset.mem_filter, Finset.mem_univ, true_and] at hp_eng
      have hp_leaf : s.children root p = ∅ := by
        refine Finset.eq_empty_iff_forall_notMem.mpr fun c hc => ?_
        have hc_mem := hchild_eng hc
        have hc_anc := hdist c hc_mem
        have hp_anc := hdist p hp_mem
        simp only [State.children, Finset.mem_filter, Finset.mem_univ, true_and] at hc
        have hc_step : s.ancestor? (dist p + 1) c = some root := by
          simp [State.ancestor?, hc.2, hp_anc]
        have heq := ancestor?_eq_root_unique hr.root_parent_eq_none hc_anc hc_step
        have hle := hp_max c hc_mem
        omega
      have hp_def0 : (s.proc p).deficit = 0 := by
        rw [hdef_eq p, hp_leaf, Finset.card_empty]
      cases hq : (s.proc p).parent with
      | none => exact hp_eng.2 hq
      | some q =>
        have hstep : (lts root).Tr s (.detach p q) (s.detachState p q) :=
          tr_detach_iff.mpr ⟨⟨hp_eng.1, hidle.1 p, hp_def0, hq⟩, rfl⟩
        exact hterm (.detach p q) (s.detachState p q) hstep
    · obtain ⟨p, hp⟩ := Multiset.exists_mem_of_ne_zero hsig
      have hstep : (lts root).Tr s (.recvSignal p) (s.recvSignalState p) :=
        tr_recvSignal_iff.mpr ⟨hp, rfl⟩
      exact hterm (.recvSignal p) (s.recvSignalState p) hstep
  · intro ht a s' htr
    have hq := hr.terminated_implies_quiescent ht
    cases a with
    | sendBasic src _ => exact absurd (tr_sendBasic_iff.mp htr).1 (by simp [(hq.1 src).1])
    | recvBasic _ _ => exact absurd (tr_recvBasic_iff.mp htr).1 (by simp [hq.2.1])
    | becomeIdle p => exact absurd (tr_becomeIdle_iff.mp htr).1 (by simp [(hq.1 p).1])
    | recvSignal _ => exact absurd (tr_recvSignal_iff.mp htr).1 (by simp [hq.2.2])
    | detach p _ => exact absurd (tr_detach_iff.mp htr).1.2.2.2 (by simp [(hq.1 p).2.2])

private theorem exists_drain_mtr {P : Type*} [Fintype P] [DecidableEq P] {root : P} :
    ∀ m : ℕ, ∀ {s : State P}, Reachable root s → s.ComputationIdle → s.drainMeasure root = m →
      ∃ tr s', (lts root).MTr s tr s' ∧ s'.Terminated root ∧ tr.length = m := by
  intro m
  induction m with
  | zero =>
    intro s hr hidle hm
    by_cases ht : s.Terminated root
    · exact ⟨[], s, .refl, ht, rfl⟩
    · obtain ⟨a, s₁, hstep⟩ : ∃ a s₁, (lts root).Tr s a s₁ := by
        simpa [LTS.IsTerminal] using
          mt (hr.isTerminal_iff_terminated_of_computationIdle hidle).mp ht
      have hdec := (hidle.step_drainMeasure hstep).2.2
      omega
  | succ m ih =>
    intro s hr hidle hm
    by_cases ht : s.Terminated root
    · have hq := hr.terminated_implies_quiescent ht
      have hpar (p : P) : (s.proc p).parent = none := (hq.1 p).2.2
      simp [State.drainMeasure, State.engagedCount, State.engagedNodes, State.inFlightSignals,
        hpar, hq.2.2] at hm
    · obtain ⟨a, s₁, hstep⟩ : ∃ a s₁, (lts root).Tr s a s₁ := by
        simpa [LTS.IsTerminal] using
          mt (hr.isTerminal_iff_terminated_of_computationIdle hidle).mp ht
      obtain ⟨_, hidle₁, hdec⟩ := hidle.step_drainMeasure hstep
      obtain ⟨tr, s', hmtr, ht', hlen⟩ := ih (hr.step hstep) hidle₁ (by omega)
      exact ⟨a :: tr, s', .stepL hstep hmtr, ht', by simp [hlen]⟩

/-- Drain liveness for the single-parent asynchronous overlay after [DijkstraScholten1980]
(counterpart of Theorem 1 in `EWD687a - 3`, PDF p. 6) toward `#7286`: from any reachable
`ComputationIdle` configuration, a terminating control drain exists within
`2 * Fintype.card P + s.inFlightSignals` steps, AND every execution schedule is bounded by
`2 * Fintype.card P + s.inFlightSignals` steps and stops only at `Terminated root`. -/
theorem Reachable.quiescent_drains_to_terminated {P : Type*} [Fintype P] [DecidableEq P]
    {root : P} {s : State P} (hr : Reachable root s) (hidle : s.ComputationIdle) :
    (∃ tr s', (lts root).MTr s tr s' ∧ s'.Terminated root ∧
        tr.length ≤ 2 * Fintype.card P + s.inFlightSignals) ∧
      (∀ tr s', (lts root).MTr s tr s' →
        tr.length ≤ 2 * Fintype.card P + s.inFlightSignals ∧
          ((lts root).IsTerminal s' → s'.Terminated root)) := by
  have hbound := s.drainMeasure_le root
  refine ⟨?_, ?_⟩
  · obtain ⟨tr, s', hmtr, ht, hlen⟩ := exists_drain_mtr (s.drainMeasure root) hr hidle rfl
    exact ⟨tr, s', hmtr, ht, by omega⟩
  · intro tr s' hmtr
    obtain ⟨hidle', hlen⟩ := hidle.mtr_drainMeasure hmtr
    refine ⟨by omega, fun hterm => ?_⟩
    exact ((hr.mtr hmtr).isTerminal_iff_terminated_of_computationIdle hidle').mp hterm

/-! ### Sequential-polling phantom termination counterexample -/

/-- Original counterexample showing why sequential local `active = false` polling without channel
or deficit accounting suffers phantom termination: for any process type `P` with `r ≠ root` and
`q ≠ r`, there is a reachable diffusing execution `initState root →* s₁ →* s₂ →* s₃ → s₄` where:
1. `root` is polled idle at `s₁`;
2. every `p ≠ r` (including `q`) is polled idle at `s₂` while `r` is actively computing;
3. `r` sends basic message `⟨r, q⟩` to already-polled `q`, turns idle, and is polled idle at `s₃`
   (completing an all-`false` sequential poll across the entire system);
4. `⟨r, q⟩` arrives at `s₄` to re-activate `q`, while Dijkstra–Scholten's `Terminated root`
   remains `false` throughout `s₁, s₂, s₃, s₄`. -/
theorem exists_phantom_termination_naive_poll {P : Type*} [DecidableEq P] (root q r : P)
    (hr : r ≠ root) (hqr : q ≠ r) :
    ∃ (tr₁ tr₂ tr₃ : List (Action P)) (s₁ s₂ s₃ s₄ : State P),
      (lts root).MTr (initState root) tr₁ s₁ ∧
      (lts root).MTr s₁ tr₂ s₂ ∧
      (lts root).MTr s₂ tr₃ s₃ ∧
      (lts root).Tr s₃ (.recvBasic r q) s₄ ∧
      (s₁.proc root).active = false ∧
      (s₂.proc q).active = false ∧
      (∀ p : P, p ≠ r → (s₂.proc p).active = false) ∧
      (s₂.proc r).active = true ∧
      (s₃.proc r).active = false ∧
      ⟨r, q⟩ ∈ s₃.basicMsgs ∧
      (s₄.proc q).active = true ∧
      ¬ s₁.Terminated root ∧ ¬ s₂.Terminated root ∧
      ¬ s₃.Terminated root ∧ ¬ s₄.Terminated root := by
  let s₀ := initState root
  let s₀₁ := s₀.sendBasicState root r
  let s₁ := s₀₁.becomeIdleState root
  let s₂ := s₁.recvBasicState root root r
  let s₂₁ := s₂.sendBasicState r q
  let s₃ := s₂₁.becomeIdleState r
  let s₄ := s₃.recvBasicState root r q
  have htr₀₁ : (lts root).Tr s₀ (.sendBasic root r) s₀₁ :=
    tr_sendBasic_iff.mpr ⟨by simp [s₀, initState], rfl⟩
  have htr₁ : (lts root).Tr s₀₁ (.becomeIdle root) s₁ :=
    tr_becomeIdle_iff.mpr ⟨by simp [s₀₁, State.sendBasicState, s₀, initState], rfl⟩
  have hmtr₁ : (lts root).MTr s₀ [.sendBasic root r, .becomeIdle root] s₁ :=
    .stepL htr₀₁ (.stepL htr₁ .refl)
  have htr₂ : (lts root).Tr s₁ (.recvBasic root r) s₂ :=
    tr_recvBasic_iff.mpr ⟨by simp [s₁, s₀₁, State.becomeIdleState, State.sendBasicState], rfl⟩
  have hmtr₂ : (lts root).MTr s₁ [.recvBasic root r] s₂ := .single (lts root) htr₂
  have hs₁_par_r : (s₁.proc r).parent = none := by
    simp [s₁, s₀₁, s₀, State.becomeIdleState, hr, State.sendBasicState, initState]
  have hs₂_r_act : (s₂.proc r).active = true := by
    simp [s₂, State.recvBasicState, hr, hs₁_par_r]
  have htr₂₁ : (lts root).Tr s₂ (.sendBasic r q) s₂₁ :=
    tr_sendBasic_iff.mpr ⟨hs₂_r_act, rfl⟩
  have htr₃ : (lts root).Tr s₂₁ (.becomeIdle r) s₃ :=
    tr_becomeIdle_iff.mpr ⟨by simp [s₂₁, State.sendBasicState, hs₂_r_act], rfl⟩
  have hmtr₃ : (lts root).MTr s₂ [.sendBasic r q, .becomeIdle r] s₃ :=
    .stepL htr₂₁ (.stepL htr₃ .refl)
  have hmem₃ : ⟨r, q⟩ ∈ s₃.basicMsgs := by
    simp [s₃, s₂₁, State.becomeIdleState, State.sendBasicState]
  have htr₄ : (lts root).Tr s₃ (.recvBasic r q) s₄ :=
    tr_recvBasic_iff.mpr ⟨hmem₃, rfl⟩
  have hs₁_root_idle : (s₁.proc root).active = false := by
    simp [s₁, State.becomeIdleState]
  have hs₂_idle : ∀ p : P, p ≠ r → (s₂.proc p).active = false := by
    intro p hpr
    have hs₁_p : (s₁.proc p).active = false := by
      by_cases hproot : p = root
      · subst hproot; exact hs₁_root_idle
      · simp [s₁, s₀₁, s₀, State.becomeIdleState, hproot, State.sendBasicState, initState]
    simp [s₂, State.recvBasicState, hr, hs₁_par_r, Function.update_of_ne hpr, hs₁_p]
  have hs₃_r_idle : (s₃.proc r).active = false := by
    simp [s₃, State.becomeIdleState]
  have hs₄_q_act : (s₄.proc q).active = true := by
    simp only [s₄, State.recvBasicState]
    split_ifs <;> simp
  have hd₁ : (s₁.proc root).deficit = 1 := by
    simp [s₁, s₀₁, s₀, State.becomeIdleState, State.sendBasicState, initState]
  have hd₂ : (s₂.proc root).deficit = 1 := (recvBasicState_deficit s₁ root root r root).trans hd₁
  have hd₃ : (s₃.proc root).deficit = 1 := by
    simp [s₃, s₂₁, State.becomeIdleState, Ne.symm hr, State.sendBasicState, hd₂]
  have hd₄ : (s₄.proc root).deficit = 1 := (recvBasicState_deficit s₃ root r q root).trans hd₃
  refine ⟨[.sendBasic root r, .becomeIdle root], [.recvBasic root r],
    [.sendBasic r q, .becomeIdle r], s₁, s₂, s₃, s₄, hmtr₁, hmtr₂, hmtr₃, htr₄,
    hs₁_root_idle, hs₂_idle q hqr, hs₂_idle, hs₂_r_act, hs₃_r_idle, hmem₃, hs₄_q_act,
    ?_, ?_, ?_, ?_⟩ <;> (intro ht; have := ht.2; omega)

end Cslib.Distributed.DijkstraScholten
