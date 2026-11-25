/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.MaxFlow.PushRelabel
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Goldberg–Tarjan Relabel-to-Front Scheduler and Operation Bounds

Formalizes the **relabel-to-front** topological list maximum-flow scheduler ([CLRS2009], Section
26.5) on the push–relabel and current-arc discharge framework of Goldberg and Tarjan
([GoldbergTarjan1988]; [CLRS2009], Section 26.4), with its `O(|V|³)` push/relabel operation,
discharge, and current-arc pointer-advance count bounds, on the integral networks of
`CslibFrontier.Algorithms.Lean.MaxFlow.Basic`.

## Model and source mapping

* **Adjacency coverage (`IsAdjacency`):** neighbor lists `adj : V → List V` covering every non-loop
  pair `(u, v)` with `0 < N.cap u v + N.cap v u` (matching `AdjValid` on `Fin n`).
* **Current-arc state (`CAState`, `CurrentArcInv`):** pairs a `PushRelabel.State N` with a
  remaining neighbor suffix `cur u` of `adj u` for each vertex `u`. Every already-scanned neighbor
  before `cur u` is non-admissible (`¬ (0 < resCap u w ∧ height u = height w + 1)`).
* **Discharge (`dischargeLoop`, `discharge`):** repeatedly pushes along the head of `cur u` when
  admissible, advances `cur u` otherwise, or relabels `u` and resets `cur u := adj u` when
  `cur u = []`, until `u` is no longer active.
* **Relabel-to-front (`RTFState`, `rtfLoop`, `relabelToFrontWith`):** maintains a duplicate-free
  list `done ++ todo` of all vertices other than `N.s` and `N.t` in topological order of the
  admissible network (`TopoOrder`), with every vertex in `done` inactive. Discharging the head `u`
  of `todo` moves `u` to the front (`done' = [u]`, `todo' = done ++ rest`) if `u` was relabeled, and
  otherwise advances past `u` (`done' = done ++ [u]`, `todo' = rest`).

## Main definitions

* `Cslib.Algorithms.Lean.MaxFlow.Network.RelabelToFront.IsAdjacency`, `exactAdj`.
* `Cslib.Algorithms.Lean.MaxFlow.Network.RelabelToFront.CAState`, `CAState.init`,
  `CurrentArcInv`, `CAInv`, `DischargeOutput`, `dischargeFuel`, `dischargeLoop`, `discharge`.
* `Cslib.Algorithms.Lean.MaxFlow.Network.RelabelToFront.Before`, `TopoOrder`, `RTFState`,
  `RTFState.init`, `RTFInv`, `rtfFuel`, `rtfLoop`.
* `Cslib.Algorithms.Lean.MaxFlow.RelabelToFrontOutput`, `relabelToFrontWith`,
  `relabelToFront`, `relabelToFrontDense`, `relabelToFrontExact`, `tabulateCA`, `tabulateRTF`,
  `nonTermFin`.

## Main results

* `Cslib.Algorithms.Lean.MaxFlow.Network.RelabelToFront.discharge_spec`: `discharge` preserves
  `CAInv`, produces a valid `PushRelabel.State.IsRun`, renders `u` inactive, performs at most one
  nonsaturating push, preserves admissible arcs and heights when `relabeled = false` and leaves no
  incoming admissible arcs at `u` when `relabeled = true`, and accounts for current-arc advances
  against relabels of `u`.
* `Cslib.Algorithms.Lean.MaxFlow.relabelToFrontWith_correct`: for `N.s ≠ N.t`, valid neighbor lists
  `adj`, and a duplicate-free list `vs` of `V \ {N.s, N.t}`, `relabelToFrontWith` produces a valid
  `PushRelabel.State.IsRun` ending in a maximum flow and minimum gap cut of equal value, with
  `out.discharges ≤ (|V| - 2) * ((|V| - 2) * (2 * |V| - 1) + 1)`, at most `out.discharges`
  nonsaturating pushes, and `out.advances ≤ 2 * |V| * ∑ v ∈ S, (adj v).length` over
  `S = (univ.erase N.s).erase N.t`.
* `Cslib.Algorithms.Lean.MaxFlow.relabelToFrontWith_bounds`,
  `relabelToFrontWith_totalSteps_le`: the `O(|V|²)` relabel (`≤ 2|V|²`), `O(|V||E|)`
  saturating-push (`≤ 2|V||E|`), and `O(|V|³)` discharge, nonsaturating-push, push/relabel
  operation, and combined operation/discharge/advance count bounds (`≤ 2|V|³ ≤ 4|V|³` discharges
  and nonsaturating pushes, `≤ 4|V|³` push/relabel operations, and
  `≤ 6|V|³ + 2|V| ∑ v, (adj v).length` combined `discharges + ops.length + advances`, or `≤ 8|V|³`
  when `adj` has no duplicates).
* `Cslib.Algorithms.Lean.MaxFlow.relabelToFront_correct`, `relabelToFrontDense_correct`,
  `relabelToFrontExact_correct`: executable `Fin n` endpoints (`relabelToFrontExact` also bounds
  current-arc advances by `2 * n * N.symArcs.card ≤ 4 * n * N.posArcs.card` and combined
  `discharges + ops.length + advances` by `8 * n ^ 3`).

## Limitations

This module provides pure Lean functions counting push/relabel operations, discharge calls, and
current-arc advances; no Word-RAM compilation (`Program.ComputesInTime`) is provided here
(`#3373`). FIFO and highest-label selection, gap and global-relabelling heuristics, and dynamic
trees are not formalized.

## References

* [A. V. Goldberg and R. E. Tarjan,
  *A New Approach to the Maximum-Flow Problem*][GoldbergTarjan1988]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow

namespace Network

namespace RelabelToFront

open Preflow PushRelabel

/-! ### Adjacency coverage -/

section Adjacency

variable {V : Type*}

/-- Candidate neighbour lists `adj` cover every non-loop pair `(u, v)` that can ever carry
positive residual capacity in `N`. -/
@[expose] def IsAdjacency (N : Network V) (adj : V → List V) : Prop :=
  ∀ u v, u ≠ v → 0 < N.cap u v + N.cap v u → v ∈ adj u

theorem isAdjacency_iff_adjValid {n : ℕ} {N : Network (Fin n)} {adj : Fin n → List (Fin n)} :
    IsAdjacency N adj ↔ AdjValid N adj :=
  Iff.rfl

/-- Exact neighbour lists of `N : Network (Fin n)`: all `v ≠ u` with `0 < N.cap u v + N.cap v u`. -/
@[expose] def exactAdj {n : ℕ} (N : Network (Fin n)) (u : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun v => decide (u ≠ v ∧ 0 < N.cap u v + N.cap v u)

theorem isAdjacency_exactAdj {n : ℕ} (N : Network (Fin n)) : IsAdjacency N (exactAdj N) :=
  fun _ _ huv hpos => by simp [exactAdj, huv]; omega

theorem nodup_exactAdj {n : ℕ} (N : Network (Fin n)) (u : Fin n) : (exactAdj N u).Nodup :=
  (List.nodup_finRange n).filter _

theorem adjSteps_exactAdj_eq {n : ℕ} (N : Network (Fin n)) :
    adjSteps (exactAdj N) = N.symArcs.card := by
  have hsub (u : Fin n) :
      (exactAdj N u).length = (Finset.univ.filter fun v => (u, v) ∈ N.symArcs).card := by
    rw [← List.toFinset_card_of_nodup (nodup_exactAdj N u)]
    congr 1
    ext v
    simp [exactAdj, Network.symArcs]
  simp only [adjSteps, hsub]
  have hpart :
      N.symArcs = Finset.univ.biUnion fun u : Fin n =>
        (Finset.univ.filter fun v => (u, v) ∈ N.symArcs).image (Prod.mk u) := by
    ext ⟨u, v⟩
    simp
  conv_rhs => rw [hpart, Finset.card_biUnion (fun a _ b _ hab =>
    Finset.disjoint_left.mpr fun x hx hy => by
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨_, _, heq⟩ := Finset.mem_image.mp hy
      exact hab (Prod.mk.inj heq).1.symm)]
  exact Finset.sum_congr rfl fun u _ =>
    (Finset.card_image_of_injective _ fun _ _ h => (Prod.mk.inj h).2).symm

end Adjacency

/-! ### Current-arc state and `discharge` -/

section CurrentArc

variable {V : Type*} [Fintype V] {N : Network V}

variable (N) in
/-- State of the current-arc push–relabel machine: a `PushRelabel.State N` together with the
unscanned suffix `cur u` of `adj u` at every vertex `u`. -/
structure CAState where
  /-- The underlying preflow and height function. -/
  pr : PushRelabel.State N
  /-- Unscanned suffix of `adj u` at each vertex `u`. -/
  cur : V → List V

variable (N) in
/-- Initial current-arc state from `PushRelabel.init N` and full neighbor lists `adj`. -/
@[expose] def CAState.init [DecidableEq V] (adj : V → List V) : CAState N :=
  ⟨PushRelabel.init N, adj⟩

/-- Current-arc invariant: every `cur u` is a suffix of `adj u` whose already-scanned prefix
contains no admissible out-neighbor. -/
def CurrentArcInv (adj : V → List V) (σ : PushRelabel.State N) (cur : V → List V) : Prop :=
  ∀ u, ∃ pre : List V, adj u = pre ++ cur u ∧
    ∀ w ∈ pre, ¬ (0 < σ.flow.resCap u w ∧ σ.height u = σ.height w + 1)

/-- Invariant of `CAState`: valid height-bounded preflow/labeling together with `CurrentArcInv`. -/
structure CAInv (adj : V → List V) (s : CAState N) : Prop where
  /-- Underlying generic push–relabel invariant. -/
  prInv : s.pr.Inv
  /-- Current-arc prefix has no admissible arcs. -/
  curInv : CurrentArcInv adj s.pr s.cur

theorem caInv_init [DecidableEq V] {adj : V → List V} (hst : N.s ≠ N.t) :
    CAInv adj (CAState.init N adj) :=
  ⟨inv_init hst, fun u => ⟨[], rfl, by simp⟩⟩

private theorem canRelabel_of_cur_nil {adj : V → List V} (hadj : IsAdjacency N adj)
    {s : CAState N} (hs : CAInv adj s) {u : V} (hact : s.pr.flow.IsActive u)
    (hnil : s.cur u = []) : s.pr.flow.CanRelabel s.pr.height u := by
  refine ⟨hact, fun v hpos => ?_⟩
  by_cases huv : u = v
  · subst huv; exact le_rfl
  · obtain ⟨pre, hpre, hno⟩ := hs.curInv u
    rw [hnil, List.append_nil] at hpre
    have h1 := hs.prInv.valid.le_add_one u v hpos
    have h2 := hno v (hpre ▸ hadj u v huv (by have := s.pr.flow.resCap_le_cap_add_cap u v; omega))
    omega

private def isHeadAdmissible (s : CAState N) (u : V) : Prop :=
  match s.cur u with
  | [] => False
  | v :: _ => 0 < s.pr.flow.resCap u v ∧ s.pr.height u = s.pr.height v + 1

private instance (s : CAState N) (u : V) : Decidable (isHeadAdmissible s u) := by
  unfold isHeadAdmissible
  cases s.cur u <;> infer_instance

/-- Fuel sufficient for `dischargeLoop` to drain `u` completely from any `CAInv` state. -/
@[expose] def dischargeFuel (adj : V → List V) (u : V) : ℕ :=
  2 * Fintype.card V * (2 * (adj u).length + 2)

private def dischargeMeasure (adj : V → List V) (u : V) (s : CAState N) : ℕ :=
  (2 * Fintype.card V - 1 - s.pr.height u) * (2 * (adj u).length + 2) +
    (2 * (s.cur u).length + if isHeadAdmissible s u then 1 else 0)

private theorem dischargeMeasure_le_fuel {adj : V → List V} {u : V} {s : CAState N}
    (hcur : CurrentArcInv adj s.pr s.cur) (hn : 0 < Fintype.card V) :
    dischargeMeasure adj u s ≤ dischargeFuel adj u := by
  obtain ⟨pre, hpre, _⟩ := hcur u
  have hlen : (s.cur u).length ≤ (adj u).length := by simp [hpre]
  unfold dischargeMeasure dischargeFuel
  have h2 := Nat.mul_le_mul_right (2 * (adj u).length + 2)
    (Nat.sub_le (2 * Fintype.card V - 1) (s.pr.height u))
  have h3 : 2 * (s.cur u).length + (if isHeadAdmissible s u then 1 else 0) ≤
      2 * (adj u).length + 1 := by
    split_ifs <;> omega
  have h4 : (2 * Fintype.card V - 1) * (2 * (adj u).length + 2) + (2 * (adj u).length + 2) =
      2 * Fintype.card V * (2 * (adj u).length + 2) := by
    rw [← Nat.add_one_mul, Nat.sub_add_cancel (by omega)]
  omega

section Decidable

variable [DecidableEq V]

private theorem relabel_height_self_lt {σ : PushRelabel.State N} {u : V}
    (hr : σ.flow.CanRelabel σ.height u) : σ.height u < (σ.apply (.relabel u)).height u := by
  simpa [State.apply_relabel_height, Preflow.relabel_self] using hr.lt_relabelHeight

private theorem relabel_height_of_ne (σ : PushRelabel.State N) {u x : V} (hx : x ≠ u) :
    (σ.apply (.relabel u)).height x = σ.height x :=
  Preflow.relabel_of_ne _ _ hx

private theorem currentArcInv_advance {adj : V → List V} {σ : PushRelabel.State N}
    {cur : V → List V} (hcur : CurrentArcInv adj σ cur) {u v : V} {vs : List V}
    (hcu : cur u = v :: vs) (hnon : ¬ (0 < σ.flow.resCap u v ∧ σ.height u = σ.height v + 1)) :
    CurrentArcInv adj σ (Function.update cur u vs) := by
  intro x
  obtain ⟨pre, hpre, hno⟩ := hcur x
  by_cases hxu : x = u
  · subst hxu
    refine ⟨pre ++ [v], by simp [hpre, hcu], fun w hw => ?_⟩
    rcases List.mem_append.mp hw with hw' | hw'
    · exact hno w hw'
    · exact List.mem_singleton.mp hw' ▸ hnon
  · rw [Function.update_of_ne hxu]
    exact ⟨pre, hpre, hno⟩

private theorem currentArcInv_push {adj : V → List V} {σ : PushRelabel.State N}
    {cur : V → List V} (hcur : CurrentArcInv adj σ cur) {u v : V}
    (hp : σ.flow.CanPush σ.height u v) : CurrentArcInv adj (σ.apply (.push u v)) cur := by
  intro x
  obtain ⟨pre, hpre, hno⟩ := hcur x
  refine ⟨pre, hpre, fun w hw ⟨hpos, heq⟩ => hno w hw ?_⟩
  simp only [State.apply_push_flow, State.apply_push_height] at hpos heq
  by_cases h1 : x = u ∧ w = v
  · obtain ⟨rfl, rfl⟩ := h1
    rw [σ.flow.resCap_push_self hp.ne] at hpos
    exact ⟨by omega, heq⟩
  · by_cases h2 : x = v ∧ w = u
    · obtain ⟨rfl, rfl⟩ := h2
      have := hp.height_eq
      omega
    · exact ⟨by rwa [σ.flow.resCap_push_of_ne h1 h2] at hpos, heq⟩

private theorem currentArcInv_relabel {adj : V → List V} {σ : PushRelabel.State N}
    {cur : V → List V} (hvalid : σ.flow.IsValidLabeling σ.height)
    (hcur : CurrentArcInv adj σ cur) {u : V} (hr : σ.flow.CanRelabel σ.height u) :
    CurrentArcInv adj (σ.apply (.relabel u)) (Function.update cur u (adj u)) := by
  intro x
  by_cases hxu : x = u
  · exact hxu ▸ ⟨[], by simp, by simp⟩
  · rw [Function.update_of_ne hxu]
    obtain ⟨pre, hpre, hno⟩ := hcur x
    refine ⟨pre, hpre, fun w hw ⟨hpos, heq⟩ => hno w hw ⟨hpos, ?_⟩⟩
    rw [relabel_height_of_ne σ hxu] at heq
    by_cases hwu : w = u
    · subst hwu
      have := hvalid.le_add_one x w hpos
      have := relabel_height_self_lt hr
      omega
    · rwa [relabel_height_of_ne σ hwu] at heq

/-- Result of discharging a single vertex `u`. -/
structure DischargeOutput {V : Type*} [Fintype V] (N : Network V) where
  /-- Push and relabel operations performed during the discharge. -/
  ops : List (Op V)
  /-- Final current-arc state after the discharge. -/
  ca : CAState N
  /-- Number of current-arc pointer advances performed. -/
  advances : ℕ
  /-- Whether at least one relabel occurred during the discharge. -/
  relabeled : Bool

/-- Discharge loop on vertex `u` with fuel `fuel`, normalizing states with `norm` after each step:
while `u` is active, push along `cur u`'s head if admissible, advance `cur u` otherwise, or relabel
`u` and reset `cur u := adj u` at `[]`. -/
@[expose] def dischargeLoop (adj : V → List V) (norm : CAState N → CAState N) (u : V) :
    ℕ → CAState N → DischargeOutput N
  | fuel, s =>
    if s.pr.flow.IsActive u then
      match fuel with
      | 0 => ⟨[], s, 0, false⟩
      | fuel + 1 =>
        match s.cur u with
        | [] =>
          let o : Op V := .relabel u
          let s' := norm ⟨s.pr.apply o, Function.update s.cur u (adj u)⟩
          let r := dischargeLoop adj norm u fuel s'
          ⟨o :: r.ops, r.ca, r.advances, true⟩
        | v :: vs =>
          if 0 < s.pr.flow.resCap u v ∧ s.pr.height u = s.pr.height v + 1 then
            let o : Op V := .push u v
            let s' := norm ⟨s.pr.apply o, s.cur⟩
            let r := dischargeLoop adj norm u fuel s'
            ⟨o :: r.ops, r.ca, r.advances, r.relabeled⟩
          else
            let s' := norm ⟨s.pr, Function.update s.cur u vs⟩
            let r := dischargeLoop adj norm u fuel s'
            ⟨r.ops, r.ca, r.advances + 1, r.relabeled⟩
    else ⟨[], s, 0, false⟩

/-- Discharge `u` with fuel `dischargeFuel adj u` ([CLRS2009], Section 26.5, `DISCHARGE`). -/
@[expose] def discharge (adj : V → List V) (norm : CAState N → CAState N) (u : V)
    (s : CAState N) : DischargeOutput N :=
  dischargeLoop adj norm u (dischargeFuel adj u) s

private theorem push_preserves_admissible_backward {σ : PushRelabel.State N} {u v : V}
    (hp : σ.flow.CanPush σ.height u v) {x y : V}
    (hadm : 0 < (σ.apply (.push u v)).flow.resCap x y ∧
      (σ.apply (.push u v)).height x = (σ.apply (.push u v)).height y + 1) :
    0 < σ.flow.resCap x y ∧ σ.height x = σ.height y + 1 := by
  simp only [State.apply_push_height, State.apply_push_flow] at hadm
  refine ⟨?_, hadm.2⟩
  by_cases h1 : x = u ∧ y = v
  · obtain ⟨rfl, rfl⟩ := h1
    rw [σ.flow.resCap_push_self hp.ne] at hadm; omega
  · by_cases h2 : x = v ∧ y = u
    · obtain ⟨rfl, rfl⟩ := h2
      have := hp.height_eq
      omega
    · rw [σ.flow.resCap_push_of_ne h1 h2] at hadm
      exact hadm.1

private theorem numRelabels_push_cons (σ : PushRelabel.State N) (u v : V) (os : List (Op V)) :
    σ.numRelabels (.push u v :: os) = (σ.apply (.push u v)).numRelabels os := by
  rw [State.numRelabels_cons, ite_eq_right (show ¬ (Op.push u v : Op V).IsRelabel from id),
    Nat.zero_add]

private theorem dischargeLoop_of_not_isActive {adj : V → List V} {norm : CAState N → CAState N}
    {u : V} {fuel : ℕ} {s : CAState N} (hact : ¬ s.pr.flow.IsActive u) :
    dischargeLoop adj norm u fuel s = ⟨[], s, 0, false⟩ := by
  rw [dischargeLoop.eq_def]
  exact ite_eq_right hact

private theorem dischargeLoop_relabel {adj : V → List V} {norm : CAState N → CAState N}
    (hnorm : ∀ s, norm s = s) {u : V} {fuel : ℕ} {s : CAState N}
    (hact : s.pr.flow.IsActive u) (hcu : s.cur u = []) :
    dischargeLoop adj norm u (fuel + 1) s =
      let r := dischargeLoop adj norm u fuel
        ⟨s.pr.apply (.relabel u), Function.update s.cur u (adj u)⟩
      ⟨.relabel u :: r.ops, r.ca, r.advances, true⟩ := by
  simp only [dischargeLoop, hact, ↓reduceIte, hcu, hnorm]

private theorem dischargeLoop_push {adj : V → List V} {norm : CAState N → CAState N}
    (hnorm : ∀ s, norm s = s) {u v : V} {vs : List V} {fuel : ℕ} {s : CAState N}
    (hact : s.pr.flow.IsActive u) (hcu : s.cur u = v :: vs)
    (hadm : 0 < s.pr.flow.resCap u v ∧ s.pr.height u = s.pr.height v + 1) :
    dischargeLoop adj norm u (fuel + 1) s =
      let r := dischargeLoop adj norm u fuel ⟨s.pr.apply (.push u v), s.cur⟩
      ⟨.push u v :: r.ops, r.ca, r.advances, r.relabeled⟩ := by
  simp only [dischargeLoop, hact, ↓reduceIte, hcu, hadm, and_self, hnorm]

private theorem dischargeLoop_advance {adj : V → List V} {norm : CAState N → CAState N}
    (hnorm : ∀ s, norm s = s) {u v : V} {vs : List V} {fuel : ℕ} {s : CAState N}
    (hact : s.pr.flow.IsActive u) (hcu : s.cur u = v :: vs)
    (hadm : ¬ (0 < s.pr.flow.resCap u v ∧ s.pr.height u = s.pr.height v + 1)) :
    dischargeLoop adj norm u (fuel + 1) s =
      let r := dischargeLoop adj norm u fuel ⟨s.pr, Function.update s.cur u vs⟩
      ⟨r.ops, r.ca, r.advances + 1, r.relabeled⟩ := by
  simp only [dischargeLoop, hact, ↓reduceIte, hcu, hadm, hnorm]

omit [DecidableEq V] in
private theorem dischargeMeasure_pos_of_isActive {adj : V → List V} (hadj : IsAdjacency N adj)
    {u : V} {s : CAState N} (hs : CAInv adj s) (hact : s.pr.flow.IsActive u) :
    0 < dischargeMeasure adj u s := by
  classical
  unfold dischargeMeasure
  cases hcu : s.cur u with
  | nil =>
    have hr := canRelabel_of_cur_nil hadj hs hact hcu
    have hlt := relabel_height_self_lt hr
    have hle := (hs.prInv.apply (o := .relabel u) hr).height_le u
    have := Nat.mul_pos (Nat.sub_pos_of_lt (hlt.trans_le hle))
      (by omega : 0 < 2 * (adj u).length + 2)
    omega
  | cons _ _ =>
    rw [List.length_cons]
    omega

private theorem dischargeMeasure_relabel_step {adj : V → List V} (hadj : IsAdjacency N adj)
    {u : V} {s : CAState N} (hs : CAInv adj s) (hact : s.pr.flow.IsActive u)
    (hcu : s.cur u = []) :
    let s' : CAState N := ⟨s.pr.apply (.relabel u), Function.update s.cur u (adj u)⟩
    CAInv adj s' ∧ dischargeMeasure adj u s' + 1 ≤ dischargeMeasure adj u s := by
  intro s'
  have hr := canRelabel_of_cur_nil hadj hs hact hcu
  have hs' : CAInv adj s' :=
    ⟨hs.prInv.apply (o := .relabel u) hr, currentArcInv_relabel hs.prInv.valid hs.curInv hr⟩
  refine ⟨hs', ?_⟩
  have hlt : s.pr.height u < s'.pr.height u := relabel_height_self_lt hr
  have hle : s'.pr.height u ≤ 2 * Fintype.card V - 1 := hs'.prInv.height_le u
  unfold dischargeMeasure
  have had : (s'.cur u).length = (adj u).length := by simp [s']
  have his : (if isHeadAdmissible s' u then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have h2 := Nat.mul_le_mul_right (2 * (adj u).length + 2)
    (show 2 * Fintype.card V - 1 - s'.pr.height u + 1 ≤ 2 * Fintype.card V - 1 - s.pr.height u
      by omega)
  rw [Nat.add_mul, Nat.one_mul] at h2
  rw [hcu, List.length_nil]
  omega

private theorem dischargeMeasure_satPush_step (adj : V → List V) {u v : V} {vs : List V}
    {s : CAState N} (hp : s.pr.flow.CanPush s.pr.height u v) (hcu : s.cur u = v :: vs)
    (hadm : 0 < s.pr.flow.resCap u v ∧ s.pr.height u = s.pr.height v + 1)
    (hsat : s.pr.IsSatPush (.push u v)) :
    let s' : CAState N := ⟨s.pr.apply (.push u v), s.cur⟩
    dischargeMeasure adj u s' + 1 ≤ dischargeMeasure adj u s := by
  intro s'
  have hhead : isHeadAdmissible s u := by simp [isHeadAdmissible, hcu, hadm]
  have hhead' : ¬ isHeadAdmissible s' u := by
    simp only [isHeadAdmissible, s', State.apply_push_flow, hcu]
    rw [s.pr.flow.resCap_push_self hp.ne]
    have hsat' : s.pr.flow.pushAmount u v = s.pr.flow.resCap u v := hsat
    omega
  unfold dischargeMeasure
  rw [ite_eq_left hhead, ite_eq_right hhead']
  change (2 * Fintype.card V - 1 - s.pr.height u) * _ + (2 * (s.cur u).length + 0) + 1 ≤ _
  omega

private theorem not_isActive_of_nonsatPush {u v : V} {s : CAState N}
    (hp : s.pr.flow.CanPush s.pr.height u v) (hsat : ¬ s.pr.IsSatPush (.push u v)) :
    ¬ (⟨s.pr.apply (.push u v), s.cur⟩ : CAState N).pr.flow.IsActive u := fun h => by
  have hex_pos : 0 < s.pr.flow.excess u := hp.active.2.2
  have hamt : (s.pr.flow.pushAmount u v : ℤ) = s.pr.flow.excess u := by
    have h1 : s.pr.flow.pushAmount u v ≠ s.pr.flow.resCap u v := hsat
    rcases le_total (s.pr.flow.excess u).toNat (s.pr.flow.resCap u v) with hle | hlt
    · simp only [Preflow.pushAmount, min_eq_left hle]; omega
    · exfalso; exact h1 (by simp [Preflow.pushAmount, min_eq_right hlt])
  have hex := s.pr.flow.excess_push_self hp.ne
  have h2 := h.2.2
  change 0 < (s.pr.flow.push u v).excess u at h2
  omega

private theorem dischargeMeasure_advance_step {adj : V → List V} {u v : V} {vs : List V}
    {s : CAState N} (hs : CAInv adj s) (hcu : s.cur u = v :: vs)
    (hadm : ¬ (0 < s.pr.flow.resCap u v ∧ s.pr.height u = s.pr.height v + 1)) :
    let s' : CAState N := ⟨s.pr, Function.update s.cur u vs⟩
    CAInv adj s' ∧ dischargeMeasure adj u s' + 1 ≤ dischargeMeasure adj u s := by
  intro s'
  refine ⟨⟨hs.prInv, currentArcInv_advance hs.curInv hcu hadm⟩, ?_⟩
  have hhead : ¬ isHeadAdmissible s u := by simp [isHeadAdmissible, hcu, hadm]
  unfold dischargeMeasure
  rw [ite_eq_right hhead]
  have hlen : (s'.cur u).length = vs.length := by simp [s']
  have hht : s'.pr.height u = s.pr.height u := rfl
  have his : (if isHeadAdmissible s' u then 1 else 0) ≤ 1 := by split_ifs <;> omega
  rw [hlen, hht, hcu, List.length_cons]
  omega


private theorem dischargeLoop_spec {adj : V → List V} (hadj : IsAdjacency N adj)
    {norm : CAState N → CAState N} (hnorm : ∀ s, norm s = s) (u : V) :
    ∀ (fuel : ℕ) (s : CAState N),
      CAInv adj s → dischargeMeasure adj u s ≤ fuel →
      let r := dischargeLoop adj norm u fuel s
      CAInv adj r.ca ∧
      s.pr.IsRun r.ops ∧
      r.ca.pr = s.pr.run r.ops ∧
      ¬ r.ca.pr.flow.IsActive u ∧
      s.pr.numNonsatPushes r.ops ≤ 1 ∧
      (r.relabeled = true ↔ 0 < s.pr.numRelabels r.ops) ∧
      (∀ x, x ≠ u → r.ca.cur x = s.cur x ∧ r.ca.pr.height x = s.pr.height x) ∧
      s.pr.height u + s.pr.numRelabels r.ops ≤ r.ca.pr.height u ∧
      r.advances + (r.ca.cur u).length =
        (s.cur u).length + s.pr.numRelabels r.ops * (adj u).length ∧
      (r.relabeled = false → r.ca.pr.height = s.pr.height) ∧
      (r.relabeled = false → ∀ x y,
        (0 < r.ca.pr.flow.resCap x y ∧ r.ca.pr.height x = r.ca.pr.height y + 1) →
          0 < s.pr.flow.resCap x y ∧ s.pr.height x = s.pr.height y + 1) ∧
      (r.relabeled = false → ∀ w, w ≠ u →
        ¬ (0 < s.pr.flow.resCap u w ∧ s.pr.height u = s.pr.height w + 1) →
        r.ca.pr.flow.excess w = s.pr.flow.excess w) ∧
      (r.relabeled = true → ∀ w, w ≠ u →
        ¬ (0 < r.ca.pr.flow.resCap w u ∧ r.ca.pr.height w = r.ca.pr.height u + 1)) ∧
      (∀ x y, x ≠ u → y ≠ u → r.ca.pr.flow.resCap x y = s.pr.flow.resCap x y)
  | fuel, s, hs, hmeas => by
    by_cases hact : s.pr.flow.IsActive u
    swap
    · rw [dischargeLoop_of_not_isActive hact]
      exact ⟨hs, trivial, rfl, hact, by simp [State.numNonsatPushes, State.countOps],
        by simp [State.numRelabels, State.countOps], fun _ _ => ⟨rfl, rfl⟩,
        by simp [State.numRelabels, State.countOps],
        by simp [State.numRelabels, State.countOps],
        fun _ => rfl, fun _ _ _ h => h, fun _ _ _ _ => rfl, nofun, fun _ _ _ _ => rfl⟩
    have hpos := dischargeMeasure_pos_of_isActive hadj hs hact
    obtain ⟨fuel, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ fuel by omega)
    cases hcu : s.cur u with
    | nil =>
      have hr := canRelabel_of_cur_nil hadj hs hact hcu
      have hlt := relabel_height_self_lt hr
      obtain ⟨hs', hstep⟩ := dischargeMeasure_relabel_step hadj hs hact hcu
      have ih := dischargeLoop_spec hadj hnorm u fuel _ hs' (by omega)
      rw [dischargeLoop_relabel hnorm hact hcu]
      generalize dischargeLoop adj norm u fuel
        ⟨s.pr.apply (.relabel u), Function.update s.cur u (adj u)⟩ = r at ih ⊢
      dsimp only at ih ⊢
      obtain ⟨ihInv, ihRun, ihPr, ihAct, ihNs, ihRel, ihNe, ihH, ihAdv, -, ihBk, -, ihIn, ihRes⟩ :=
        ih
      rw [Function.update_self] at ihAdv
      rw [State.numRelabels_cons, ite_eq_left (show (Op.relabel u : Op V).IsRelabel from trivial),
        Nat.add_comm]
      refine ⟨ihInv, ⟨hr, ihRun⟩, ihPr, ihAct, ?_, ⟨fun _ => by omega, fun _ => rfl⟩,
        fun x hx => ⟨(ihNe x hx).1.trans (Function.update_of_ne hx _ _),
          (ihNe x hx).2.trans (relabel_height_of_ne _ hx)⟩, by omega, ?_, nofun, nofun, nofun,
        fun _ w hw hadm => ?_, ihRes⟩
      · rwa [State.numNonsatPushes_cons, ite_eq_right fun h => h.1, Nat.zero_add]
      · rw [List.length_nil, add_one_mul]
        omega
      · cases hrel : r.relabeled
        · have h1 := hs.prInv.valid.le_add_one w u (ihBk hrel w u hadm).1
          have h2 := (ihBk hrel w u hadm).2
          rw [relabel_height_of_ne _ hw] at h2
          omega
        · exact ihIn hrel w hw hadm
    | cons v vs =>
      by_cases hadm : 0 < s.pr.flow.resCap u v ∧ s.pr.height u = s.pr.height v + 1
      swap
      · -- Advance current-arc pointer
        obtain ⟨hs', hstep⟩ := dischargeMeasure_advance_step hs hcu hadm
        have ih := dischargeLoop_spec hadj hnorm u fuel _ hs' (by omega)
        rw [dischargeLoop_advance hnorm hact hcu hadm]
        generalize dischargeLoop adj norm u fuel ⟨s.pr, Function.update s.cur u vs⟩ = r at ih ⊢
        dsimp only at ih ⊢
        obtain ⟨ihInv, ihRun, ihPr, ihAct, ihNs, ihRel, ihNe, ihH, ihAdv, ihHeq, ihBk, ihEx, ihIn,
          ihRes⟩ := ih
        rw [Function.update_self] at ihAdv
        refine ⟨ihInv, ihRun, ihPr, ihAct, ihNs, ihRel,
          fun x hx => ⟨(ihNe x hx).1.trans (Function.update_of_ne hx _ _), (ihNe x hx).2⟩, ihH, ?_,
          ihHeq, ihBk, ihEx, ihIn, ihRes⟩
        rw [List.length_cons]
        omega
      have hp : s.pr.flow.CanPush s.pr.height u v := ⟨hact, hadm.1, hadm.2⟩
      have hs' : CAInv adj ⟨s.pr.apply (.push u v), s.cur⟩ :=
        ⟨hs.prInv.apply (o := .push u v) hp, currentArcInv_push hs.curInv hp⟩
      have hex (w : V) (hwu : w ≠ u)
          (hnon : ¬ (0 < s.pr.flow.resCap u w ∧ s.pr.height u = s.pr.height w + 1)) :
          (s.pr.apply (.push u v)).flow.excess w = s.pr.flow.excess w :=
        s.pr.flow.excess_push_of_ne hwu <| by
          rintro rfl
          exact hnon hadm
      have hres (x y : V) (hx : x ≠ u) (hy : y ≠ u) :
          (s.pr.apply (.push u v)).flow.resCap x y = s.pr.flow.resCap x y :=
        s.pr.flow.resCap_push_of_ne (fun h => hx h.1) (fun h => hy h.2)
      rw [dischargeLoop_push hnorm hact hcu hadm]
      by_cases hsat : s.pr.IsSatPush (.push u v)
      · have ih := dischargeLoop_spec hadj hnorm u fuel _ hs'
          (by have := dischargeMeasure_satPush_step adj hp hcu hadm hsat; omega)
        generalize dischargeLoop adj norm u fuel ⟨s.pr.apply (.push u v), s.cur⟩ = r at ih ⊢
        dsimp only at ih ⊢
        rw [numRelabels_push_cons]
        obtain ⟨ihInv, ihRun, ihPr, ihAct, ihNs, ihRel, ihNe, ihH, ihAdv, ihHeq, ihBk, ihEx, ihIn,
          ihRes⟩ := ih
        rw [hcu] at ihAdv
        refine ⟨ihInv, ⟨hp, ihRun⟩, ihPr, ihAct, ?_, ihRel, ihNe, ihH, ihAdv, ihHeq,
          fun hrel x y hxy => push_preserves_admissible_backward hp (ihBk hrel x y hxy),
          fun hrel w hwu hnon => (ihEx hrel w hwu fun h =>
            hnon (push_preserves_admissible_backward hp h)).trans (hex w hwu hnon),
          ihIn, fun x y hx hy => (ihRes x y hx hy).trans (hres x y hx hy)⟩
        rwa [State.numNonsatPushes_cons, ite_eq_right fun h => h.2 hsat, Nat.zero_add]
      · -- Nonsaturating push: `u` becomes inactive and `dischargeLoop` returns at once.
        have hnact' := not_isActive_of_nonsatPush hp hsat
        rw [dischargeLoop_of_not_isActive hnact']
        dsimp only
        rw [numRelabels_push_cons]
        refine ⟨hs', ⟨hp, trivial⟩, rfl, hnact', ?_, ?_, fun _ _ => ⟨rfl, rfl⟩, ?_, ?_,
          fun _ => rfl, fun _ x y hxy => push_preserves_admissible_backward hp hxy,
          fun _ w hwu hnon => hex w hwu hnon, nofun, hres⟩
        · rw [State.numNonsatPushes_cons, ite_eq_left ⟨trivial, hsat⟩]
          simp [State.numNonsatPushes, State.countOps]
        all_goals simp [State.numRelabels, State.countOps, hcu]


/-- **Specification of `discharge`** ([CLRS2009], Section 26.5): discharging `u` from any `CAInv`
state executes a valid run of `PushRelabel` operations, preserves `CAInv`, renders `u` inactive,
performs at most one nonsaturating push, tracks relabels and current-arc pointer advances, preserves
heights and admissible arcs when not relabeling, and leaves no incoming admissible arcs at `u` when
relabeling. -/
theorem discharge_spec {adj : V → List V} (hadj : IsAdjacency N adj)
    {norm : CAState N → CAState N} (hnorm : ∀ s, norm s = s) (u : V) {s : CAState N}
    (hs : CAInv adj s) :
    let r := discharge adj norm u s
    CAInv adj r.ca ∧
    s.pr.IsRun r.ops ∧
    r.ca.pr = s.pr.run r.ops ∧
    ¬ r.ca.pr.flow.IsActive u ∧
    s.pr.numNonsatPushes r.ops ≤ 1 ∧
    (r.relabeled = true ↔ 0 < s.pr.numRelabels r.ops) ∧
    (∀ x, x ≠ u → r.ca.cur x = s.cur x ∧ r.ca.pr.height x = s.pr.height x) ∧
    s.pr.height u + s.pr.numRelabels r.ops ≤ r.ca.pr.height u ∧
    r.advances + (r.ca.cur u).length =
      (s.cur u).length + s.pr.numRelabels r.ops * (adj u).length ∧
    (r.relabeled = false → r.ca.pr.height = s.pr.height) ∧
    (r.relabeled = false → ∀ x y,
      (0 < r.ca.pr.flow.resCap x y ∧ r.ca.pr.height x = r.ca.pr.height y + 1) →
        0 < s.pr.flow.resCap x y ∧ s.pr.height x = s.pr.height y + 1) ∧
    (r.relabeled = false → ∀ w, w ≠ u →
      ¬ (0 < s.pr.flow.resCap u w ∧ s.pr.height u = s.pr.height w + 1) →
      r.ca.pr.flow.excess w = s.pr.flow.excess w) ∧
    (r.relabeled = true → ∀ w, w ≠ u →
      ¬ (0 < r.ca.pr.flow.resCap w u ∧ r.ca.pr.height w = r.ca.pr.height u + 1)) ∧
    (∀ x y, x ≠ u → y ≠ u → r.ca.pr.flow.resCap x y = s.pr.flow.resCap x y) :=
  dischargeLoop_spec hadj hnorm u (dischargeFuel adj u) s hs
    (dischargeMeasure_le_fuel hs.curInv (Fintype.card_pos_iff.mpr ⟨u⟩))

omit [DecidableEq V] in
private theorem dischargeFuel_pos (adj : V → List V) (u : V) : 0 < dischargeFuel adj u := by
  unfold dischargeFuel
  exact Nat.mul_pos (Nat.mul_pos (by omega) (Fintype.card_pos_iff.mpr ⟨u⟩)) (by omega)

private theorem dischargeLoop_eq_of_le {adj : V → List V} (hadj : IsAdjacency N adj) (u : V) :
    ∀ (m fuel₁ fuel₂ : ℕ) (s : CAState N),
      CAInv adj s → dischargeMeasure adj u s ≤ m →
      dischargeMeasure adj u s ≤ fuel₁ → dischargeMeasure adj u s ≤ fuel₂ →
      dischargeLoop adj id u fuel₁ s = dischargeLoop adj id u fuel₂ s
  | m, fuel₁, fuel₂, s, hs, hm, hf₁, hf₂ => by
    by_cases hact : s.pr.flow.IsActive u
    swap
    · rw [dischargeLoop_of_not_isActive hact, dischargeLoop_of_not_isActive hact]
    have hpos := dischargeMeasure_pos_of_isActive hadj hs hact
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ m by omega)
    obtain ⟨fuel₁, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ fuel₁ by omega)
    obtain ⟨fuel₂, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ fuel₂ by omega)
    have hid : ∀ s : CAState N, id s = s := fun _ => rfl
    cases hcu : s.cur u with
    | nil =>
      obtain ⟨hs', hstep⟩ := dischargeMeasure_relabel_step hadj hs hact hcu
      rw [dischargeLoop_relabel hid hact hcu, dischargeLoop_relabel hid hact hcu,
        dischargeLoop_eq_of_le hadj u m fuel₁ fuel₂ _ hs' (by omega) (by omega) (by omega)]
    | cons v vs =>
      by_cases hadm : 0 < s.pr.flow.resCap u v ∧ s.pr.height u = s.pr.height v + 1
      · have hp : s.pr.flow.CanPush s.pr.height u v := ⟨hact, hadm.1, hadm.2⟩
        rw [dischargeLoop_push hid hact hcu hadm, dischargeLoop_push hid hact hcu hadm]
        by_cases hsat : s.pr.IsSatPush (.push u v)
        · have hstep := dischargeMeasure_satPush_step adj hp hcu hadm hsat
          rw [dischargeLoop_eq_of_le hadj u m fuel₁ fuel₂ _
            ⟨hs.prInv.apply (o := .push u v) hp, currentArcInv_push hs.curInv hp⟩
            (by omega) (by omega) (by omega)]
        · have hnact' := not_isActive_of_nonsatPush hp hsat
          rw [dischargeLoop_of_not_isActive hnact', dischargeLoop_of_not_isActive hnact']
      · obtain ⟨hs', hstep⟩ := dischargeMeasure_advance_step hs hcu hadm
        rw [dischargeLoop_advance hid hact hcu hadm, dischargeLoop_advance hid hact hcu hadm,
          dischargeLoop_eq_of_le hadj u m fuel₁ fuel₂ _ hs' (by omega) (by omega) (by omega)]

private theorem dischargeLoop_pred_fuel_eq {adj : V → List V} (hadj : IsAdjacency N adj) {u : V}
    {s s' : CAState N} (hs : CAInv adj s) (hs' : CAInv adj s')
    (hstep : dischargeMeasure adj u s' + 1 ≤ dischargeMeasure adj u s) :
    let f := dischargeFuel adj u - 1
    dischargeFuel adj u = f + 1 ∧ dischargeLoop adj id u f s' = discharge adj id u s' := by
  have hpos := dischargeFuel_pos adj u
  have hm := dischargeMeasure_le_fuel (u := u) hs.curInv (Fintype.card_pos_iff.mpr ⟨u⟩)
  have hm' := dischargeMeasure_le_fuel (u := u) hs'.curInv (Fintype.card_pos_iff.mpr ⟨u⟩)
  exact ⟨by omega, dischargeLoop_eq_of_le hadj u (dischargeFuel adj u) _ _ s' hs' hm'
    (by omega) hm'⟩

/-- Evaluating `discharge` on an inactive vertex returns the trivial empty output. -/
theorem discharge_eq_of_not_isActive {adj : V → List V} (norm : CAState N → CAState N)
    {u : V} {s : CAState N} (hact : ¬ s.pr.flow.IsActive u) :
    discharge adj norm u s = ⟨[], s, 0, false⟩ :=
  dischargeLoop_of_not_isActive hact

/-- One relabel step of `discharge adj id u s` when `s.cur u = []` (`CAInv adj s` preserved). -/
theorem discharge_relabel_step {adj : V → List V} (hadj : IsAdjacency N adj) {u : V}
    {s : CAState N} (hs : CAInv adj s) (hact : s.pr.flow.IsActive u) (hcu : s.cur u = []) :
    let s' : CAState N := ⟨s.pr.apply (.relabel u), Function.update s.cur u (adj u)⟩
    let r' := discharge adj id u s'
    CAInv adj s' ∧ discharge adj id u s = ⟨.relabel u :: r'.ops, r'.ca, r'.advances, true⟩ := by
  obtain ⟨hs', hmeas'⟩ := dischargeMeasure_relabel_step hadj hs hact hcu
  obtain ⟨hf, heq⟩ := dischargeLoop_pred_fuel_eq hadj hs hs' hmeas'
  refine ⟨hs', ?_⟩
  rw [discharge, hf, dischargeLoop_relabel (norm := id) (fun _ => rfl) hact hcu, heq]

/-- One push step of `discharge adj id u s` when `s.cur u = v :: vs` is admissible. -/
theorem discharge_push_step {adj : V → List V} (hadj : IsAdjacency N adj) {u v : V}
    {vs : List V} {s : CAState N} (hs : CAInv adj s) (hact : s.pr.flow.IsActive u)
    (hcu : s.cur u = v :: vs)
    (hadm : 0 < s.pr.flow.resCap u v ∧ s.pr.height u = s.pr.height v + 1) :
    let s' : CAState N := ⟨s.pr.apply (.push u v), s.cur⟩
    let r' := discharge adj id u s'
    CAInv adj s' ∧
      discharge adj id u s = ⟨.push u v :: r'.ops, r'.ca, r'.advances, r'.relabeled⟩ := by
  have hp : s.pr.flow.CanPush s.pr.height u v := ⟨hact, hadm.1, hadm.2⟩
  have hs' : CAInv adj ⟨s.pr.apply (.push u v), s.cur⟩ :=
    ⟨hs.prInv.apply (o := .push u v) hp, currentArcInv_push hs.curInv hp⟩
  refine ⟨hs', ?_⟩
  have hf : dischargeFuel adj u = dischargeFuel adj u - 1 + 1 := by
    have := dischargeFuel_pos adj u
    omega
  rw [discharge, hf, dischargeLoop_push (norm := id) (fun _ => rfl) hact hcu hadm]
  by_cases hsat : s.pr.IsSatPush (.push u v)
  · rw [(dischargeLoop_pred_fuel_eq hadj hs hs'
      (dischargeMeasure_satPush_step adj hp hcu hadm hsat)).2]
  · have hnact' := not_isActive_of_nonsatPush hp hsat
    rw [dischargeLoop_of_not_isActive hnact', discharge_eq_of_not_isActive id hnact']

/-- One current-arc advance step of `discharge adj id u s` when `s.cur u = v :: vs` is
non-admissible. -/
theorem discharge_advance_step {adj : V → List V} (hadj : IsAdjacency N adj) {u v : V}
    {vs : List V} {s : CAState N} (hs : CAInv adj s) (hact : s.pr.flow.IsActive u)
    (hcu : s.cur u = v :: vs)
    (hadm : ¬ (0 < s.pr.flow.resCap u v ∧ s.pr.height u = s.pr.height v + 1)) :
    let s' : CAState N := ⟨s.pr, Function.update s.cur u vs⟩
    let r' := discharge adj id u s'
    CAInv adj s' ∧ discharge adj id u s = ⟨r'.ops, r'.ca, r'.advances + 1, r'.relabeled⟩ := by
  obtain ⟨hs', hmeas'⟩ := dischargeMeasure_advance_step hs hcu hadm
  obtain ⟨hf, heq⟩ := dischargeLoop_pred_fuel_eq hadj hs hs' hmeas'
  refine ⟨hs', ?_⟩
  rw [discharge, hf, dischargeLoop_advance (norm := id) (fun _ => rfl) hact hcu hadm, heq]

end Decidable

end CurrentArc

/-! ### Topological ordering and relabel-to-front -/

section RelabelToFrontSection

/-- `Before u v l` holds when `u` appears strictly before `v` in `l`. -/
inductive Before {α : Type*} (u v : α) : List α → Prop
  | head {xs : List α} : v ∈ xs → Before u v (u :: xs)
  | tail {x : α} {xs : List α} : Before u v xs → Before u v (x :: xs)

private theorem Before.mem_right {α : Type*} {u v : α} : ∀ {xs : List α}, Before u v xs → v ∈ xs
  | _, .head hv => List.mem_cons_of_mem _ hv
  | _, .tail hb => List.mem_cons_of_mem _ hb.mem_right

private theorem before_append_cons {α : Type*} {u v : α} :
    ∀ {done rest : List α}, u ∉ done → Before u v (done ++ u :: rest) → v ∈ rest
  | [], _, _, hb => by
    cases hb with
    | head hm => exact hm
    | tail htail => exact htail.mem_right
  | _ :: _, _, hu, hb => by
    cases hb with
    | head _ => exact absurd List.mem_cons_self hu
    | tail htail => exact before_append_cons (fun h => hu (List.mem_cons_of_mem _ h)) htail

private theorem not_before_of_nodup_append {α : Type*} {u v : α} {done rest : List α}
    (hnd : (done ++ u :: rest).Nodup) (hv : v ∈ done) : ¬ Before u v (done ++ u :: rest) := by
  intro hb
  have hdisj := (List.nodup_append.mp hnd).2.2
  have hv_rest := before_append_cons (fun h => hdisj u h u List.mem_cons_self rfl) hb
  exact hdisj v hv v (List.mem_cons_of_mem _ hv_rest) rfl

private theorem before_erase_cons {α : Type*} {x y u : α} (hx : x ≠ u) (hy : y ≠ u) :
    ∀ {done rest : List α}, Before x y (done ++ u :: rest) → Before x y (done ++ rest)
  | [], _, hb => by
    cases hb with
    | head _ => exact absurd rfl hx.symm
    | tail htail => exact htail
  | _ :: _, _, hb => by
    cases hb with
    | head hmem =>
      refine .head ?_
      rcases List.mem_append.mp hmem with hm | hm
      · exact List.mem_append_left _ hm
      · exact List.mem_append_right _ ((List.mem_cons.mp hm).resolve_left hy)
    | tail htail => exact .tail (before_erase_cons hx hy htail)

variable {V : Type*} [Fintype V] [DecidableEq V] {N : Network V}

/-- Topological order of a vertex list `L` with respect to the admissible network of `σ`
([CLRS2009], Section 26.5): every admissible arc between vertices of `L` points forward in `L`. -/
@[expose] def TopoOrder (σ : PushRelabel.State N) (L : List V) : Prop :=
  ∀ u ∈ L, ∀ v ∈ L, 0 < σ.flow.resCap u v → σ.height u = σ.height v + 1 → Before u v L

variable (N) in
/-- State of the relabel-to-front algorithm: current-arc state, scanned prefix `done`, remaining
suffix `todo`, total `discharge` calls, and total current-arc pointer advances. -/
structure RTFState where
  /-- Current preflow, heights, and current-arc cursors. -/
  ca : CAState N
  /-- Vertices already scanned without relabel since the last move-to-front. -/
  done : List V
  /-- Remaining vertices in the list after the cursor. -/
  todo : List V
  /-- Total number of `discharge` calls executed so far. -/
  discharges : ℕ
  /-- Total number of current-arc pointer advances executed so far. -/
  advances : ℕ

variable (N) in
/-- Initial state of relabel-to-front from vertex list `vs` and neighbor lists `adj`. -/
@[expose] def RTFState.init (adj : V → List V) (vs : List V) : RTFState N :=
  ⟨CAState.init N adj, [], vs, 0, 0⟩

/-- Invariant of `RTFState` ([CLRS2009], Section 26.5): `CAInv`, `done ++ todo` is a duplicate-free
enumeration of `V \ {N.s, N.t}` in topological order of the admissible network, and every vertex in
`done` is inactive. -/
structure RTFInv (adj : V → List V) (st : RTFState N) : Prop where
  /-- Current-arc invariant. -/
  caInv : CAInv adj st.ca
  /-- `done ++ todo` has no duplicates. -/
  nodup : (st.done ++ st.todo).Nodup
  /-- `done ++ todo` contains exactly `V \ {N.s, N.t}`. -/
  mem_iff : ∀ v, v ∈ st.done ++ st.todo ↔ v ≠ N.s ∧ v ≠ N.t
  /-- `done ++ todo` is a topological order of the admissible network. -/
  topo : TopoOrder st.ca.pr (st.done ++ st.todo)
  /-- Every vertex strictly before the cursor is inactive. -/
  done_inactive : ∀ w ∈ st.done, ¬ st.ca.pr.flow.IsActive w

theorem rtfInv_init {adj : V → List V} {vs : List V} (hst : N.s ≠ N.t) (hnodup : vs.Nodup)
    (hmem : ∀ v, v ∈ vs ↔ v ≠ N.s ∧ v ≠ N.t) : RTFInv adj (RTFState.init N adj vs) := by
  refine ⟨caInv_init hst, hnodup, hmem, fun u hu v _ _ heq => ?_, by simp [RTFState.init]⟩
  have hu' := (hmem u).mp hu
  change Preflow.initialHeight N u = Preflow.initialHeight N v + 1 at heq
  simp only [Preflow.initialHeight, hu'.1, ↓reduceIte] at heq
  split_ifs at heq

/-- Outer fuel for `rtfLoop`: `(|V| - 2) * ((|V| - 2) * (2 * |V| - 1) + 1) + 1`. -/
@[expose] def rtfFuel (V : Type*) [Fintype V] : ℕ :=
  (Fintype.card V - 2) * ((Fintype.card V - 2) * (2 * Fintype.card V - 1) + 1) + 1

/-- Relabel-to-front outer loop with fuel `fuel`, normalizing `CAState` with `caNorm` and `RTFState`
with `stNorm`. Returns `(ops, finalState)`. -/
@[expose] def rtfLoop (adj : V → List V) (caNorm : CAState N → CAState N)
    (stNorm : RTFState N → RTFState N) : ℕ → RTFState N → List (Op V) × RTFState N
  | fuel, st =>
    match st.todo with
    | [] => ([], st)
    | u :: rest =>
      match fuel with
      | 0 => ([], st)
      | fuel + 1 =>
        let d := discharge adj caNorm u st.ca
        let st' : RTFState N :=
          if d.relabeled then
            { ca := d.ca
              done := [u]
              todo := st.done ++ rest
              discharges := st.discharges + 1
              advances := st.advances + d.advances }
          else
            { ca := d.ca
              done := st.done ++ [u]
              todo := rest
              discharges := st.discharges + 1
              advances := st.advances + d.advances }
        let r := rtfLoop adj caNorm stNorm fuel (stNorm st')
        (d.ops ++ r.1, r.2)

private def sumHeightMax (V : Type*) [Fintype V] : ℕ :=
  Fintype.card V + (Fintype.card V - 2) * (2 * Fintype.card V - 1)

private def rtfMeasure (V : Type*) [Fintype V] {N : Network V} (st : RTFState N) : ℕ :=
  (sumHeightMax V - ∑ v, st.ca.pr.height v) * (Fintype.card V - 2) + st.todo.length

private def advPotential (adj : V → List V) (ca : CAState N) : ℕ :=
  ∑ u ∈ (Finset.univ.erase N.s).erase N.t,
    ((2 * Fintype.card V - 1 - ca.pr.height u) * (adj u).length + (ca.cur u).length)

private theorem advPotential_init (adj : V → List V) :
    advPotential adj (CAState.init N adj) =
      2 * Fintype.card V * ∑ u ∈ (Finset.univ.erase N.s).erase N.t, (adj u).length := by
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨N.s⟩
  unfold advPotential
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hus : u ≠ N.s := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hu)
  have hh : (CAState.init N adj).pr.height u = 0 := by
    change Preflow.initialHeight N u = 0
    simp [Preflow.initialHeight, hus]
  have hcur : ((CAState.init N adj).cur u).length = (adj u).length := rfl
  rw [hh, hcur, Nat.sub_zero]
  have h2 : 2 * Fintype.card V - 1 + 1 = 2 * Fintype.card V := by omega
  calc (2 * Fintype.card V - 1) * (adj u).length + (adj u).length
      = (2 * Fintype.card V - 1 + 1) * (adj u).length := by ring
    _ = 2 * Fintype.card V * (adj u).length := by rw [h2]

private theorem advPotential_discharge {adj : V → List V} {s : CAState N} {r : DischargeOutput N}
    {u : V} (hus : u ≠ N.s) (hut : u ≠ N.t) (hs : CAInv adj s) (hr : CAInv adj r.ca)
    (hne : ∀ x, x ≠ u → r.ca.cur x = s.cur x ∧ r.ca.pr.height x = s.pr.height x)
    (hheight : s.pr.height u + s.pr.numRelabels r.ops ≤ r.ca.pr.height u)
    (hadv : r.advances + (r.ca.cur u).length =
      (s.cur u).length + s.pr.numRelabels r.ops * (adj u).length) :
    r.advances + advPotential adj r.ca ≤ advPotential adj s := by
  let S := (Finset.univ.erase N.s).erase N.t
  have huS : u ∈ S := Finset.mem_erase.mpr ⟨hut, Finset.mem_erase.mpr ⟨hus, Finset.mem_univ u⟩⟩
  unfold advPotential
  rw [← Finset.add_sum_erase _ _ huS, ← Finset.add_sum_erase _ _ huS]
  have hrest :
      ∑ x ∈ S.erase u, ((2 * Fintype.card V - 1 - r.ca.pr.height x) * (adj x).length +
        (r.ca.cur x).length) =
      ∑ x ∈ S.erase u, ((2 * Fintype.card V - 1 - s.pr.height x) * (adj x).length +
        (s.cur x).length) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    obtain ⟨hcx, hhx⟩ := hne x (Finset.ne_of_mem_erase hx)
    rw [hcx, hhx]
  rw [hrest]
  have hr_le : r.ca.pr.height u ≤ 2 * Fintype.card V - 1 := hr.prInv.height_le u
  have hs_le : s.pr.height u ≤ 2 * Fintype.card V - 1 := hs.prInv.height_le u
  have h1 : 2 * Fintype.card V - 1 - r.ca.pr.height u + s.pr.numRelabels r.ops ≤
      2 * Fintype.card V - 1 - s.pr.height u := by omega
  have h2 : (2 * Fintype.card V - 1 - r.ca.pr.height u + s.pr.numRelabels r.ops) * (adj u).length ≤
      (2 * Fintype.card V - 1 - s.pr.height u) * (adj u).length := Nat.mul_le_mul_right _ h1
  rw [Nat.add_mul] at h2
  omega

omit [DecidableEq V] in
private theorem list_nodup_length_eq_card_sub_two {ls : List V} (hnodup : ls.Nodup)
    (hmem : ∀ v, v ∈ ls ↔ v ≠ N.s ∧ v ≠ N.t) (hst : N.s ≠ N.t) :
    ls.length = Fintype.card V - 2 := by
  classical
  have hfs : ls.toFinset = (Finset.univ.erase N.s).erase N.t := by
    ext v
    simp [hmem v, and_comm]
  rw [← List.toFinset_card_of_nodup hnodup, hfs,
    Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hst.symm, Finset.mem_univ _⟩),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  omega

omit [DecidableEq V] in
private theorem rtfInv_relabel {adj : V → List V} {st : RTFState N} (hinv : RTFInv adj st)
    {u : V} {rest : List V} (htodo : st.todo = u :: rest) {d : DischargeOutput N} (a b : ℕ)
    (hdInv : CAInv adj d.ca) (hdAct : ¬ d.ca.pr.flow.IsActive u)
    (hdNe : ∀ x, x ≠ u → d.ca.cur x = st.ca.cur x ∧ d.ca.pr.height x = st.ca.pr.height x)
    (hdIn : ∀ w, w ≠ u →
      ¬ (0 < d.ca.pr.flow.resCap w u ∧ d.ca.pr.height w = d.ca.pr.height u + 1))
    (hdRes : ∀ x y, x ≠ u → y ≠ u → d.ca.pr.flow.resCap x y = st.ca.pr.flow.resCap x y) :
    RTFInv adj
      { ca := d.ca, done := [u], todo := st.done ++ rest, discharges := a, advances := b } := by
  have hperm : (st.done ++ st.todo).Perm (u :: (st.done ++ rest)) := by
    rw [htodo]
    exact List.perm_middle
  have hnd := hperm.nodup_iff.mp hinv.nodup
  refine ⟨hdInv, hnd, fun v => hperm.mem_iff.symm.trans (hinv.mem_iff v),
    fun x hx y hy hpos heq => ?_, fun w hw => List.mem_singleton.mp hw ▸ hdAct⟩
  rcases List.mem_cons.mp hx with rfl | hx'
  · rcases List.mem_cons.mp hy with rfl | hy'
    · omega
    · exact .head hy'
  have hxu : x ≠ u := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hx')
  rcases List.mem_cons.mp hy with rfl | hy'
  · exact absurd ⟨hpos, heq⟩ (hdIn x hxu)
  have hyu : y ≠ u := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hy')
  have hb := hinv.topo x (hperm.mem_iff.mpr (List.mem_cons_of_mem _ hx'))
    y (hperm.mem_iff.mpr (List.mem_cons_of_mem _ hy'))
    (hdRes x y hxu hyu ▸ hpos) ((hdNe x hxu).2 ▸ (hdNe y hyu).2 ▸ heq)
  rw [htodo] at hb
  exact .tail (before_erase_cons (done := st.done) (rest := rest) hxu hyu hb)

omit [DecidableEq V] in
private theorem rtfInv_noRelabel {adj : V → List V} {st : RTFState N} (hinv : RTFInv adj st)
    {u : V} {rest : List V} (htodo : st.todo = u :: rest) {d : DischargeOutput N} (a b : ℕ)
    (hdInv : CAInv adj d.ca) (hdAct : ¬ d.ca.pr.flow.IsActive u)
    (hdBk : ∀ x y, (0 < d.ca.pr.flow.resCap x y ∧ d.ca.pr.height x = d.ca.pr.height y + 1) →
      0 < st.ca.pr.flow.resCap x y ∧ st.ca.pr.height x = st.ca.pr.height y + 1)
    (hdEx : ∀ w, w ≠ u →
      ¬ (0 < st.ca.pr.flow.resCap u w ∧ st.ca.pr.height u = st.ca.pr.height w + 1) →
      d.ca.pr.flow.excess w = st.ca.pr.flow.excess w) :
    RTFInv adj
      { ca := d.ca, done := st.done ++ [u], todo := rest, discharges := a, advances := b } := by
  have hassoc : st.done ++ st.todo = (st.done ++ [u]) ++ rest := by simp [htodo]
  refine ⟨hdInv, hassoc ▸ hinv.nodup, fun v => hassoc ▸ hinv.mem_iff v,
    fun x hx y hy hpos heq => ?_, fun w hw => ?_⟩
  · obtain ⟨hpos0, heq0⟩ := hdBk x y ⟨hpos, heq⟩
    exact hassoc ▸ hinv.topo x (hassoc ▸ hx) y (hassoc ▸ hy) hpos0 heq0
  rcases List.mem_append.mp hw with hw' | hw'
  · have hnodup0 : (st.done ++ u :: rest).Nodup := htodo ▸ hinv.nodup
    have hwu : w ≠ u := fun h => (List.nodup_append.mp hnodup0).2.2 w hw' u List.mem_cons_self h
    have hnon : ¬ (0 < st.ca.pr.flow.resCap u w ∧
        st.ca.pr.height u = st.ca.pr.height w + 1) := by
      rintro ⟨hpos, heq⟩
      have hb := hinv.topo u (by simp [htodo]) w (List.mem_append_left _ hw') hpos heq
      rw [htodo] at hb
      exact not_before_of_nodup_append hnodup0 hw' hb
    have hinact := hinv.done_inactive w hw'
    unfold Preflow.IsActive at hinact ⊢
    rwa [hdEx w hwu hnon]
  · exact List.mem_singleton.mp hw' ▸ hdAct

/-- One outer step of `rtfLoop` (with arbitrary counter fields `a`, `b`) preserves `RTFInv` and
decreases `rtfMeasure`. -/
private theorem rtfNext_spec {adj : V → List V} (hadj : IsAdjacency N adj)
    {norm : CAState N → CAState N} (hnorm : ∀ s, norm s = s) (hst : N.s ≠ N.t)
    {st : RTFState N} (hinv : RTFInv adj st) {u : V} {rest : List V}
    (htodo : st.todo = u :: rest) (a b : ℕ) :
    let d := discharge adj norm u st.ca
    let st' : RTFState N :=
      if d.relabeled then
        { ca := d.ca, done := [u], todo := st.done ++ rest, discharges := a, advances := b }
      else
        { ca := d.ca, done := st.done ++ [u], todo := rest, discharges := a, advances := b }
    RTFInv adj st' ∧ rtfMeasure V st' + 1 ≤ rtfMeasure V st := by
  obtain ⟨hdInv, hdRun, hdPr, hdAct, -, hdRel, hdNe, -, -, hdHeq, hdBk, hdEx, hdIn, hdRes⟩ :=
    discharge_spec hadj hnorm u hinv.caInv
  generalize discharge adj norm u st.ca = d at *
  have hlen : (st.done ++ u :: rest).length = Fintype.card V - 2 :=
    list_nodup_length_eq_card_sub_two (htodo ▸ hinv.nodup) (htodo ▸ hinv.mem_iff) hst
  rw [List.length_append, List.length_cons] at hlen
  have hsum_d : st.ca.pr.numRelabels d.ops + ∑ v, st.ca.pr.height v ≤ ∑ v, d.ca.pr.height v := by
    rw [hdPr]
    exact State.numRelabels_add_sum_le hdRun
  have hsum_le : ∑ v, d.ca.pr.height v ≤ sumHeightMax V := State.sum_height_le hdInv.prInv
  cases hrel : d.relabeled
  · simp only [hrel, Bool.false_eq_true, ↓reduceIte]
    refine ⟨rtfInv_noRelabel hinv htodo a b hdInv hdAct (hdBk hrel) (hdEx hrel), ?_⟩
    unfold rtfMeasure
    dsimp only
    rw [htodo, hdHeq hrel, List.length_cons]
    omega
  · have hpos := hdRel.mp hrel
    simp only [hrel, ↓reduceIte]
    refine ⟨rtfInv_relabel hinv htodo a b hdInv hdAct hdNe (hdIn hrel) hdRes, ?_⟩
    have h2 := Nat.mul_le_mul_right (Fintype.card V - 2)
      (show sumHeightMax V - ∑ v, d.ca.pr.height v + 1 ≤ sumHeightMax V - ∑ v, st.ca.pr.height v
        by omega)
    rw [Nat.add_mul, Nat.one_mul] at h2
    unfold rtfMeasure
    dsimp only
    rw [htodo, List.length_append, List.length_cons]
    omega

private theorem rtfLoop_spec {adj : V → List V} (hadj : IsAdjacency N adj)
    {caNorm : CAState N → CAState N} (hcaNorm : ∀ s, caNorm s = s)
    {stNorm : RTFState N → RTFState N} (hstNorm : ∀ st, stNorm st = st) (hst : N.s ≠ N.t) :
    ∀ (fuel : ℕ) (st : RTFState N),
      RTFInv adj st → rtfMeasure V st < fuel →
      let res := rtfLoop adj caNorm stNorm fuel st
      RTFInv adj res.2 ∧
      res.2.todo = [] ∧
      st.ca.pr.IsRun res.1 ∧
      res.2.ca.pr = st.ca.pr.run res.1 ∧
      st.ca.pr.numNonsatPushes res.1 ≤ res.2.discharges - st.discharges ∧
      st.discharges ≤ res.2.discharges ∧
      res.2.discharges ≤ st.discharges + rtfMeasure V st ∧
      res.2.advances + advPotential adj res.2.ca ≤ st.advances + advPotential adj st.ca
  | fuel, st, hinv, hmeas => by
    cases htodo : st.todo with
    | nil =>
      rw [rtfLoop]
      dsimp only
      rw [htodo]
      refine ⟨hinv, htodo, trivial, rfl, by simp [State.numNonsatPushes, State.countOps],
        le_rfl, Nat.le_add_right _ _, le_rfl⟩
    | cons u rest =>
      cases fuel with
      | zero => exact absurd hmeas (Nat.not_lt_zero _)
      | succ fuel =>
        have hu_ne : u ≠ N.s ∧ u ≠ N.t := (hinv.mem_iff u).mp (by simp [htodo])
        have hd := discharge_spec hadj hcaNorm u hinv.caInv
        have hnext := rtfNext_spec hadj hcaNorm hst hinv htodo (st.discharges + 1)
          (st.advances + (discharge adj caNorm u st.ca).advances)
        generalize hd_eq : discharge adj caNorm u st.ca = d at hd hnext ⊢
        obtain ⟨hdInv, hdRun, hdPr, -, hdNs, -, hdNe, hdH, hdAdv, -⟩ := hd
        have hadv_d : d.advances + advPotential adj d.ca ≤ advPotential adj st.ca :=
          advPotential_discharge hu_ne.1 hu_ne.2 hinv.caInv hdInv hdNe hdH hdAdv
        let st' : RTFState N :=
          if d.relabeled then
            { ca := d.ca, done := [u], todo := st.done ++ rest,
              discharges := st.discharges + 1, advances := st.advances + d.advances }
          else
            { ca := d.ca, done := st.done ++ [u], todo := rest,
              discharges := st.discharges + 1, advances := st.advances + d.advances }
        obtain ⟨hinv', hmeas'⟩ : RTFInv adj st' ∧ rtfMeasure V st' + 1 ≤ rtfMeasure V st := hnext
        obtain ⟨hca_eq, hdis_eq, hadv_eq⟩ : st'.ca = d.ca ∧ st'.discharges = st.discharges + 1 ∧
            st'.advances = st.advances + d.advances := by
          dsimp only [st']
          split_ifs <;> exact ⟨rfl, rfl, rfl⟩
        have hloop_eq : rtfLoop adj caNorm stNorm (fuel + 1) st =
            let r := rtfLoop adj caNorm stNorm fuel st'
            (d.ops ++ r.1, r.2) := by
          rw [rtfLoop]
          dsimp only
          rw [htodo]
          dsimp only
          rw [hd_eq, hstNorm]
        rw [hloop_eq]
        dsimp only
        obtain ⟨ihInv, ihTodo, ihRun, ihPr, ihNs, ihDisLe, ihDis, ihAdv⟩ :=
          rtfLoop_spec hadj hcaNorm hstNorm hst fuel st' hinv' (by omega)
        rw [hca_eq, hdPr] at ihRun ihPr ihNs
        rw [hadv_eq, hca_eq] at ihAdv
        refine ⟨ihInv, ihTodo, State.isRun_append hdRun ihRun, ?_, ?_, by omega, by omega,
          by omega⟩
        · rw [State.run_append]
          exact ihPr
        · rw [State.numNonsatPushes_append]
          omega

omit [DecidableEq V] in
private theorem rtfMeasure_lt_rtfFuel {adj : V → List V} {st : RTFState N} (hinv : RTFInv adj st)
    (hst : N.s ≠ N.t) : rtfMeasure V st < rtfFuel V := by
  classical
  have hlen : (st.done ++ st.todo).length = Fintype.card V - 2 :=
    list_nodup_length_eq_card_sub_two hinv.nodup hinv.mem_iff hst
  have htodo : st.todo.length ≤ Fintype.card V - 2 := by
    rw [List.length_append] at hlen
    omega
  have h2n : 2 ≤ Fintype.card V := by
    have hcard : ({N.s, N.t} : Finset V).card ≤ Fintype.card V := Finset.card_le_univ _
    rw [Finset.card_pair hst] at hcard
    exact hcard
  have hsum_le : ∑ v, st.ca.pr.height v ≤ sumHeightMax V := State.sum_height_le hinv.caInv.prInv
  have hsum_ge : Fintype.card V ≤ ∑ v, st.ca.pr.height v := by
    have hs : st.ca.pr.height N.s = Fintype.card V := hinv.caInv.prInv.valid.source
    have hsing := Finset.single_le_sum (fun v _ => Nat.zero_le (st.ca.pr.height v))
      (Finset.mem_univ N.s)
    omega
  have h1 :
      sumHeightMax V - ∑ v, st.ca.pr.height v ≤
        (Fintype.card V - 2) * (2 * Fintype.card V - 1) := by
    unfold sumHeightMax
    omega
  have h2 := Nat.mul_le_mul_right (Fintype.card V - 2) h1
  have hmul :
      (Fintype.card V - 2) * (2 * Fintype.card V - 1) * (Fintype.card V - 2) =
        (Fintype.card V - 2) * ((Fintype.card V - 2) * (2 * Fintype.card V - 1)) := by
    ring
  rw [hmul] at h2
  unfold rtfMeasure rtfFuel
  rw [Nat.mul_add, Nat.mul_one]
  omega

private theorem rtfLoop_eq_of_lt {adj : V → List V} (hadj : IsAdjacency N adj) (hst : N.s ≠ N.t) :
    ∀ (m fuel₁ fuel₂ : ℕ) (st : RTFState N),
      RTFInv adj st → rtfMeasure V st < m → rtfMeasure V st < fuel₁ → rtfMeasure V st < fuel₂ →
      rtfLoop adj id id fuel₁ st = rtfLoop adj id id fuel₂ st
  | m, fuel₁, fuel₂, st, hinv, hm, hf₁, hf₂ => by
    cases htodo : st.todo with
    | nil =>
      rw [rtfLoop.eq_def, rtfLoop.eq_def]
      dsimp only
      rw [htodo]
    | cons u rest =>
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ m by omega)
      obtain ⟨fuel₁, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ fuel₁ by omega)
      obtain ⟨fuel₂, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ fuel₂ by omega)
      obtain ⟨hinv', hmeas'⟩ := rtfNext_spec hadj (norm := id) (fun _ => rfl) hst hinv htodo
        (st.discharges + 1) (st.advances + (discharge adj id u st.ca).advances)
      rw [rtfLoop.eq_def, rtfLoop.eq_def]
      dsimp only
      rw [htodo]
      dsimp only
      simp only [id_eq]
      rw [rtfLoop_eq_of_lt hadj hst m fuel₁ fuel₂ _ hinv' (by omega) (by omega) (by omega)]

/-- Shifting the counter fields `(discharges, advances)` of an `RTFState` shifts the final
`rtfLoop` output counters identically without altering operations or `ca`/`done`/`todo`. -/
private theorem rtfLoop_shift_counters {adj : V → List V} :
    ∀ (fuel : ℕ) (st : RTFState N) (a b : ℕ),
      let r := rtfLoop adj id id fuel { st with discharges := 0, advances := 0 }
      rtfLoop adj id id fuel { st with discharges := a, advances := b } =
        (r.1, { r.2 with discharges := a + r.2.discharges, advances := b + r.2.advances })
  | fuel, st, a, b => by
    cases htodo : st.todo with
    | nil =>
      rw [rtfLoop.eq_def, rtfLoop.eq_def]
      rfl
    | cons u rest =>
      cases fuel with
      | zero =>
        rw [rtfLoop.eq_def, rtfLoop.eq_def]
        rfl
      | succ fuel =>
        rw [rtfLoop.eq_def, rtfLoop.eq_def]
        simp only [id_eq]
        let d := discharge adj id u st.ca
        let st'₀ : RTFState N :=
          if d.relabeled then
            { ca := d.ca, done := [u], todo := st.done ++ rest, discharges := 0, advances := 0 }
          else
            { ca := d.ca, done := st.done ++ [u], todo := rest, discharges := 0, advances := 0 }
        have h1 :
            (if d.relabeled then
              { ca := d.ca, done := [u], todo := st.done ++ rest,
                discharges := a + 1, advances := b + d.advances }
            else
              { ca := d.ca, done := st.done ++ [u], todo := rest,
                discharges := a + 1, advances := b + d.advances } : RTFState N) =
            { st'₀ with discharges := a + 1, advances := b + d.advances } := by
          dsimp only [st'₀]; split_ifs <;> rfl
        have h2 :
            (if d.relabeled then
              { ca := d.ca, done := [u], todo := st.done ++ rest,
                discharges := 0 + 1, advances := 0 + d.advances }
            else
              { ca := d.ca, done := st.done ++ [u], todo := rest,
                discharges := 0 + 1, advances := 0 + d.advances } : RTFState N) =
            { st'₀ with discharges := 1, advances := d.advances } := by
          dsimp only [st'₀]; split_ifs <;> simp
        have h0 : ({ st'₀ with discharges := 0, advances := 0 } : RTFState N) = st'₀ := by
          dsimp only [st'₀]; split_ifs <;> rfl
        have ih1 := rtfLoop_shift_counters (adj := adj) fuel st'₀ (a + 1) (b + d.advances)
        have ih2 := rtfLoop_shift_counters (adj := adj) fuel st'₀ 1 d.advances
        rw [h0] at ih1 ih2
        change (let r := rtfLoop adj id id fuel _; (d.ops ++ r.1, r.2)) = _
        rw [h1, h2, ih1, ih2]
        dsimp only
        simp only [Nat.add_assoc]
        rfl

/-- One outer iteration of `rtfLoop adj id id (rtfFuel V) st` when `st.todo = u :: rest`. -/
theorem rtfLoop_step {adj : V → List V} (hadj : IsAdjacency N adj) {st : RTFState N}
    (hinv : RTFInv adj st) {u : V} {rest : List V} (htodo : st.todo = u :: rest)
    (hst : N.s ≠ N.t) :
    let d := discharge adj id u st.ca
    let st' : RTFState N :=
      if d.relabeled then
        { ca := d.ca, done := [u], todo := st.done ++ rest, discharges := 0, advances := 0 }
      else
        { ca := d.ca, done := st.done ++ [u], todo := rest, discharges := 0, advances := 0 }
    let r := rtfLoop adj id id (rtfFuel V) st
    let r' := rtfLoop adj id id (rtfFuel V) st'
    RTFInv adj st' ∧ r.1 = d.ops ++ r'.1 ∧
      r.2.discharges = st.discharges + 1 + r'.2.discharges ∧
      r.2.advances = st.advances + d.advances + r'.2.advances ∧
      r.2.ca = r'.2.ca ∧ r.2.done = r'.2.done ∧ r.2.todo = r'.2.todo := by
  intro d st' r r'
  have hlt : rtfMeasure V st < rtfFuel V := rtfMeasure_lt_rtfFuel hinv hst
  obtain ⟨hinv', hmeas'⟩ : RTFInv adj st' ∧ rtfMeasure V st' + 1 ≤ rtfMeasure V st :=
    rtfNext_spec hadj (norm := id) (fun _ => rfl) hst hinv htodo 0 0
  obtain ⟨f, hf⟩ : ∃ f, rtfFuel V = f + 1 :=
    ⟨rtfFuel V - 1, by
      unfold rtfFuel
      omega⟩
  have hsub : rtfLoop adj id id f st' = r' :=
    rtfLoop_eq_of_lt hadj hst (rtfFuel V) f (rtfFuel V) st' hinv'
      (by omega) (by omega) (by omega)
  have hnext :
      (if d.relabeled then
        { ca := d.ca, done := [u], todo := st.done ++ rest,
          discharges := st.discharges + 1, advances := st.advances + d.advances }
      else
        { ca := d.ca, done := st.done ++ [u], todo := rest,
          discharges := st.discharges + 1, advances := st.advances + d.advances } : RTFState N) =
      { st' with discharges := st.discharges + 1, advances := st.advances + d.advances } := by
    dsimp only [st']; split_ifs <;> rfl
  have hshift :=
    rtfLoop_shift_counters (adj := adj) f st' (st.discharges + 1) (st.advances + d.advances)
  have h0 : ({ st' with discharges := 0, advances := 0 } : RTFState N) = st' := by
    dsimp only [st']; split_ifs <;> rfl
  rw [h0, hsub] at hshift
  have hr : r = (d.ops ++ r'.1,
      { r'.2 with
        discharges := st.discharges + 1 + r'.2.discharges,
        advances := st.advances + d.advances + r'.2.advances }) := by
    dsimp only [r]
    rw [hf, rtfLoop.eq_def]
    dsimp only
    rw [htodo]
    dsimp only
    simp only [id_eq]
    change (let s := rtfLoop adj id id f _; (d.ops ++ s.1, s.2)) = _
    rw [hnext, hshift]
  rw [hr]
  exact ⟨hinv', rfl, rfl, rfl, rfl, rfl, rfl⟩

end RelabelToFrontSection

end RelabelToFront

namespace PushRelabel

namespace State

/-- Relabel-operation count is additive along concatenated operation lists. -/
theorem numRelabels_append {V : Type*} [Fintype V] [DecidableEq V] {N : Network V}
    (σ : State N) :
    ∀ (os₁ os₂ : List (Op V)),
      σ.numRelabels (os₁ ++ os₂) = σ.numRelabels os₁ + (σ.run os₁).numRelabels os₂
  | [], _ => by simp [numRelabels, countOps]
  | _ :: _, _ => by
    simp only [List.cons_append, numRelabels_cons, run_cons,
      numRelabels_append (σ.apply _) _ _]
    omega

end State

end PushRelabel

end Network

/-! ### Relabel-to-front scheduler, operation/advance count bounds, and `Fin n` solvers -/

section Executable

open Network Network.Preflow Network.PushRelabel Network.RelabelToFront

variable {V : Type*} [Fintype V] [DecidableEq V] {N : Network V}

/-- Output of `relabelToFrontWith`. -/
structure RelabelToFrontOutput (N : Network V) where
  /-- The push and relabel operations performed, in order. -/
  ops : List (Op V)
  /-- The final flow. -/
  flow : N.Flow
  /-- The gap cut of the final labeling. -/
  cut : Finset V
  /-- Total number of `discharge` calls executed. -/
  discharges : ℕ
  /-- Total number of current-arc pointer advances executed. -/
  advances : ℕ

/-- The output read off a final `RTFState`: its preflow as a flow when every excess off `N.s`,
`N.t` vanishes (the zero flow otherwise), its gap cut, and its discharge and advance counts. -/
@[expose] def RelabelToFrontOutput.ofState (ops : List (Op V)) (st : RTFState N) :
    RelabelToFrontOutput N where
  ops := ops
  flow := if hz : ∀ v, v ≠ N.s → v ≠ N.t → st.ca.pr.flow.excess v = 0 then
      st.ca.pr.flow.toFlow hz
    else Flow.zero N
  cut := gapCut st.ca.pr.height
  discharges := st.discharges
  advances := st.advances

/-- The **relabel-to-front** maximum-flow scheduler ([GoldbergTarjan1988]; [CLRS2009], Section
26.5), with initial vertex order `vs`, neighbor lists `adj`, and normalizers `caNorm` / `stNorm`. -/
@[expose] def relabelToFrontWith (N : Network V) (vs : List V) (adj : V → List V)
    (caNorm : CAState N → CAState N) (stNorm : RTFState N → RTFState N) :
    RelabelToFrontOutput N :=
  if N.s = N.t then ⟨[], Flow.zero N, ∅, 0, 0⟩ else
    let r := rtfLoop adj caNorm stNorm (rtfFuel V) (RTFState.init N adj vs)
    RelabelToFrontOutput.ofState r.1 r.2

/-- **Correctness and sharp discharge and current-arc advance count bounds for
`relabelToFrontWith`** ([GoldbergTarjan1988]; [CLRS2009], Section 26.5): for
`N.s ≠ N.t`, valid neighbor lists `adj`, a duplicate-free list `vs` of `V \ {N.s, N.t}`, and
identity normalizers, `relabelToFrontWith` performs a valid run of `PushRelabel` operations ending
in a maximum flow and a minimum cut of equal value, with at most
`(|V| - 2) * ((|V| - 2) * (2 * |V| - 1) + 1)` discharge calls, at most `out.discharges`
nonsaturating pushes, and at most
`2 * |V| * ∑ v ∈ (Finset.univ.erase N.s).erase N.t, (adj v).length` current-arc advances. -/
theorem relabelToFrontWith_correct {vs : List V} (hnodup : vs.Nodup)
    (hmem : ∀ v, v ∈ vs ↔ v ≠ N.s ∧ v ≠ N.t) {adj : V → List V} (hadj : IsAdjacency N adj)
    {caNorm : CAState N → CAState N} (hcaNorm : ∀ s, caNorm s = s)
    {stNorm : RTFState N → RTFState N} (hstNorm : ∀ st, stNorm st = st) (hst : N.s ≠ N.t) :
    let out := relabelToFrontWith N vs adj caNorm stNorm
    out.flow.IsMaxFlow ∧ N.IsMinCut out.cut ∧ out.flow.value = (N.cutCapacity out.cut : ℤ) ∧
      (PushRelabel.init N).IsRun out.ops ∧
      out.discharges ≤
        (Fintype.card V - 2) * ((Fintype.card V - 2) * (2 * Fintype.card V - 1) + 1) ∧
      (PushRelabel.init N).numNonsatPushes out.ops ≤ out.discharges ∧
      out.advances ≤
        2 * Fintype.card V * ∑ v ∈ (Finset.univ.erase N.s).erase N.t, (adj v).length := by
  have hlen : vs.length = Fintype.card V - 2 :=
    list_nodup_length_eq_card_sub_two hnodup hmem hst
  have hmeas0 : rtfMeasure V (RTFState.init N adj vs) =
      (Fintype.card V - 2) * ((Fintype.card V - 2) * (2 * Fintype.card V - 1) + 1) := by
    unfold rtfMeasure sumHeightMax
    change (Fintype.card V + (Fintype.card V - 2) * (2 * Fintype.card V - 1) -
        ∑ v, (PushRelabel.init N).height v) * (Fintype.card V - 2) + vs.length = _
    rw [sum_height_init, hlen, Nat.add_sub_cancel_left]
    ring
  have hlt_fuel : rtfMeasure V (RTFState.init N adj vs) < rtfFuel V := by simp [hmeas0, rtfFuel]
  obtain ⟨hfinInv, htodo, hrun, _, hns, _, hdis, hadv⟩ :=
    rtfLoop_spec hadj hcaNorm hstNorm hst (rtfFuel V) (RTFState.init N adj vs)
      (rtfInv_init hst hnodup hmem) hlt_fuel
  have hnot_act : ∀ v, ¬ (rtfLoop adj caNorm stNorm (rtfFuel V)
      (RTFState.init N adj vs)).2.ca.pr.flow.IsActive v := fun v hv =>
    hfinInv.done_inactive v (by simpa [htodo] using (hfinInv.mem_iff v).mpr ⟨hv.1, hv.2.1⟩) hv
  have hz := excess_eq_zero_of_forall_not_isActive _ hnot_act
  have hmax := hfinInv.caInv.prInv.valid.isMaxFlow_toFlow hz
  obtain ⟨hmin, hval⟩ := hfinInv.caInv.prInv.valid.isMinCut_gapCut hz
  unfold relabelToFrontWith
  rw [ite_eq_right hst]
  simp only [RelabelToFrontOutput.ofState]
  rw [dite_eq_left hz]
  exact ⟨hmax, hmin, hval, hrun, hdis.trans_eq ((Nat.zero_add _).trans hmeas0),
    hns.trans_eq (Nat.sub_zero _), (Nat.le_add_right _ _).trans
      (hadv.trans_eq ((Nat.zero_add _).trans (advPotential_init adj)))⟩

private theorem card_sub_two_bound (n : ℕ) (hn : 2 ≤ n) :
    (n - 2) * ((n - 2) * (2 * n - 1) + 1) ≤ 2 * n ^ 3 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [Nat.add_sub_cancel_right, show 2 * (k + 2) - 1 = 2 * k + 3 by omega]
  have hsum :
      2 * (k + 2) ^ 3 = k * (k * (2 * k + 3) + 1) + (9 * k ^ 2 + 23 * k + 16) := by ring
  omega

private theorem ops_sum_bound (n : ℕ) (hn : 2 ≤ n) :
    (n - 2) * (2 * n - 1) + n * (n * (n - 1)) +
      (n - 2) * ((n - 2) * (2 * n - 1) + 1) ≤ 4 * n ^ 3 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [Nat.add_sub_cancel_right, show 2 * (k + 2) - 1 = 2 * k + 3 by omega,
    show k + 2 - 1 = k + 1 by omega]
  have hsum :
      4 * (k + 2) ^ 3 =
        k * (2 * k + 3) + (k + 2) * ((k + 2) * (k + 1)) + k * (k * (2 * k + 3) + 1) +
          (k ^ 3 + 14 * k ^ 2 + 36 * k + 28) := by ring
  omega

/-- **`O(|V|³)` push/relabel and discharge count bounds for `relabelToFrontWith`**
([GoldbergTarjan1988]; [CLRS2009], Sections 26.4–26.5): at most `2|V|²` relabels,
`2|V||E|` saturating pushes, `2|V|³` discharge calls, `2|V|³` (hence `≤ 4|V|³`) nonsaturating
pushes, and `4|V|³` total push/relabel operations. -/
theorem relabelToFrontWith_bounds {vs : List V} (hnodup : vs.Nodup)
    (hmem : ∀ v, v ∈ vs ↔ v ≠ N.s ∧ v ≠ N.t) {adj : V → List V} (hadj : IsAdjacency N adj)
    {caNorm : CAState N → CAState N} (hcaNorm : ∀ s, caNorm s = s)
    {stNorm : RTFState N → RTFState N} (hstNorm : ∀ st, stNorm st = st) (hst : N.s ≠ N.t) :
    let out := relabelToFrontWith N vs adj caNorm stNorm
    (PushRelabel.init N).numRelabels out.ops ≤ 2 * Fintype.card V ^ 2 ∧
      (PushRelabel.init N).numSatPushes out.ops ≤ 2 * Fintype.card V * N.posArcs.card ∧
      out.discharges ≤ 2 * Fintype.card V ^ 3 ∧
      (PushRelabel.init N).numNonsatPushes out.ops ≤ 4 * Fintype.card V ^ 3 ∧
      out.ops.length ≤ 4 * Fintype.card V ^ 3 := by
  obtain ⟨_, _, _, hrun, hdis, hns, _⟩ :=
    relabelToFrontWith_correct hnodup hmem hadj hcaNorm hstNorm hst
  have h2n : 2 ≤ Fintype.card V := Finset.card_pair hst ▸ Finset.card_le_univ {N.s, N.t}
  have hrel := numRelabels_lt hst hrun
  have hrel_sharp := numRelabels_le hst hrun
  have hsat := numSatPushes_le_posArcs hst hrun
  have hsat_sharp := numSatPushes_le hst hrun
  have hdis_cube : (relabelToFrontWith N vs adj caNorm stNorm).discharges ≤
      2 * Fintype.card V ^ 3 :=
    hdis.trans (card_sub_two_bound (Fintype.card V) h2n)
  have hlen : (relabelToFrontWith N vs adj caNorm stNorm).ops.length ≤ 4 * Fintype.card V ^ 3 := by
    rw [State.length_eq (PushRelabel.init N)]
    have hsat_v : Fintype.card V * N.symArcs.card ≤
        Fintype.card V * (Fintype.card V * (Fintype.card V - 1)) :=
      Nat.mul_le_mul_left _ N.card_symArcs_le_mul_pred
    have hsum := ops_sum_bound (Fintype.card V) h2n
    omega
  exact ⟨hrel.le, hsat, hdis_cube, by omega, hlen⟩

/-- **Combined discharge, push/relabel operation, and current-arc advance count bound
(`discharges + ops.length + advances`):** at most `6|V|³ + 2|V| ∑ v, (adj v).length` in general,
and at most `8|V|³` whenever every neighbor list `adj v` is duplicate-free (hence
`∑ v, (adj v).length ≤ |V|²`). -/
theorem relabelToFrontWith_totalSteps_le {vs : List V} (hnodup : vs.Nodup)
    (hmem : ∀ v, v ∈ vs ↔ v ≠ N.s ∧ v ≠ N.t) {adj : V → List V} (hadj : IsAdjacency N adj)
    {caNorm : CAState N → CAState N} (hcaNorm : ∀ s, caNorm s = s)
    {stNorm : RTFState N → RTFState N} (hstNorm : ∀ st, stNorm st = st) (hst : N.s ≠ N.t) :
    let out := relabelToFrontWith N vs adj caNorm stNorm
    out.discharges + out.ops.length + out.advances ≤
      6 * Fintype.card V ^ 3 + 2 * Fintype.card V * ∑ v, (adj v).length ∧
      ((∀ v, (adj v).Nodup) →
        out.discharges + out.ops.length + out.advances ≤ 8 * Fintype.card V ^ 3) := by
  obtain ⟨_, _, _, _, _, _, hadv⟩ :=
    relabelToFrontWith_correct hnodup hmem hadj hcaNorm hstNorm hst
  obtain ⟨_, _, hdis, _, hlen⟩ :=
    relabelToFrontWith_bounds hnodup hmem hadj hcaNorm hstNorm hst
  have hsub : ∑ v ∈ (Finset.univ.erase N.s).erase N.t, (adj v).length ≤ ∑ v, (adj v).length :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hadv' : (relabelToFrontWith N vs adj caNorm stNorm).advances ≤
      2 * Fintype.card V * ∑ v, (adj v).length :=
    hadv.trans (Nat.mul_le_mul_left _ hsub)
  refine ⟨by omega, fun hnd => ?_⟩
  have hsum_le : ∑ v, (adj v).length ≤ Fintype.card V * Fintype.card V := by
    have h1 : ∀ v : V, (adj v).length ≤ Fintype.card V := fun v => (hnd v).length_le_card
    calc ∑ v : V, (adj v).length
        ≤ ∑ _ : V, Fintype.card V := Finset.sum_le_sum fun v _ => h1 v
      _ = Fintype.card V * Fintype.card V := by simp [Finset.sum_const]
  have hmul : 2 * Fintype.card V * ∑ v, (adj v).length ≤ 2 * Fintype.card V ^ 3 := by
    have : 2 * Fintype.card V * (Fintype.card V * Fintype.card V) = 2 * Fintype.card V ^ 3 := by
      ring
    calc 2 * Fintype.card V * ∑ v, (adj v).length
        ≤ 2 * Fintype.card V * (Fintype.card V * Fintype.card V) := Nat.mul_le_mul_left _ hsum_le
      _ = 2 * Fintype.card V ^ 3 := this
  omega

/-! ### Executable tabulated instances on `Fin n` -/

/-- Tabulate a `CAState` on `Fin n`: tabulated preflow/heights together with a `Vector` of current
neighbor suffixes. -/
@[expose] def tabulateCA {n : ℕ} {N : Network (Fin n)} (s : CAState N) : CAState N :=
  let curs : Vector (List (Fin n)) n := Vector.ofFn s.cur
  ⟨PushRelabel.tabulate s.pr, vget curs⟩

theorem tabulateCA_eq {n : ℕ} {N : Network (Fin n)} (s : CAState N) : tabulateCA s = s := by
  obtain ⟨pr, cur⟩ := s
  simp only [tabulateCA, tabulate_eq, CAState.mk.injEq, true_and]
  funext v
  simp [vget]

/-- Tabulate an `RTFState` on `Fin n` by tabulating its underlying `CAState`. -/
@[expose] def tabulateRTF {n : ℕ} {N : Network (Fin n)} (st : RTFState N) : RTFState N :=
  { st with ca := tabulateCA st.ca }

theorem tabulateRTF_eq {n : ℕ} {N : Network (Fin n)} (st : RTFState N) : tabulateRTF st = st := by
  cases st
  simp [tabulateRTF, tabulateCA_eq]

/-- Canonical duplicate-free list of non-terminal vertices `v ≠ N.s, N.t` on `Fin n`. -/
@[expose] def nonTermFin {n : ℕ} (N : Network (Fin n)) : List (Fin n) :=
  (List.finRange n).filter fun v => decide (v ≠ N.s ∧ v ≠ N.t)

theorem nodup_nonTermFin {n : ℕ} (N : Network (Fin n)) : (nonTermFin N).Nodup :=
  (List.nodup_finRange n).filter _

theorem mem_nonTermFin {n : ℕ} (N : Network (Fin n)) (v : Fin n) :
    v ∈ nonTermFin N ↔ v ≠ N.s ∧ v ≠ N.t := by
  simp [nonTermFin]

/-- Executable relabel-to-front solver on `Network (Fin n)` with candidate neighbor lists `adj`,
tabulating state after every step so kernel evaluation (`decide`) avoids stacked updates. -/
@[expose] def relabelToFront {n : ℕ} (N : Network (Fin n)) (adj : Fin n → List (Fin n)) :
    RelabelToFrontOutput N :=
  relabelToFrontWith N (nonTermFin N) adj tabulateCA tabulateRTF

/-- Dense relabel-to-front solver on `Network (Fin n)` scanning `defaultAdj n` (`List.finRange n`)
at every vertex. -/
@[expose] def relabelToFrontDense {n : ℕ} (N : Network (Fin n)) : RelabelToFrontOutput N :=
  relabelToFront N (defaultAdj n)

/-- Exact-adjacency relabel-to-front solver on `Network (Fin n)` scanning `exactAdj N` at every
vertex, achieving `O(n |E|)` current-arc advances and `O(n³)` push/relabel operations, discharges,
and current-arc advances. -/
@[expose] def relabelToFrontExact {n : ℕ} (N : Network (Fin n)) : RelabelToFrontOutput N :=
  relabelToFront N (exactAdj N)

/-- **Correctness and `O(n³)` push/relabel operation, discharge, and current-arc advance count
bounds for `relabelToFront`** ([GoldbergTarjan1988]; [CLRS2009], Section 26.5). -/
theorem relabelToFront_correct {n : ℕ} {N : Network (Fin n)} {adj : Fin n → List (Fin n)}
    (hadj : AdjValid N adj) (hst : N.s ≠ N.t) :
    let out := relabelToFront N adj
    out.flow.IsMaxFlow ∧ N.IsMinCut out.cut ∧ out.flow.value = (N.cutCapacity out.cut : ℤ) ∧
      (PushRelabel.init N).IsRun out.ops ∧
      (PushRelabel.init N).numRelabels out.ops ≤ 2 * n ^ 2 ∧
      (PushRelabel.init N).numSatPushes out.ops ≤ 2 * n * N.posArcs.card ∧
      out.discharges ≤ 2 * n ^ 3 ∧
      (PushRelabel.init N).numNonsatPushes out.ops ≤ 4 * n ^ 3 ∧
      out.ops.length ≤ 4 * n ^ 3 ∧
      out.advances ≤ 2 * n * adjSteps adj ∧
      ((∀ v, (adj v).Nodup) →
        out.discharges + out.ops.length + out.advances ≤ 8 * n ^ 3) := by
  have h1 := relabelToFrontWith_correct (nodup_nonTermFin N) (mem_nonTermFin N)
    hadj tabulateCA_eq tabulateRTF_eq hst
  have h2 := relabelToFrontWith_bounds (nodup_nonTermFin N) (mem_nonTermFin N)
    hadj tabulateCA_eq tabulateRTF_eq hst
  have ht := (relabelToFrontWith_totalSteps_le (nodup_nonTermFin N) (mem_nonTermFin N)
    hadj tabulateCA_eq tabulateRTF_eq hst).2
  simp only [Fintype.card_fin] at h1 h2 ht
  have hsub : ∑ v ∈ (Finset.univ.erase N.s).erase N.t, (adj v).length ≤ adjSteps adj :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2,
    h1.2.2.2.2.2.2.trans (Nat.mul_le_mul_left _ hsub), ht⟩

/-- **Correctness and `O(n³)` push/relabel operation, discharge, and current-arc advance count
bounds for `relabelToFrontDense`.** -/
theorem relabelToFrontDense_correct {n : ℕ} {N : Network (Fin n)} (hst : N.s ≠ N.t) :
    let out := relabelToFrontDense N
    out.flow.IsMaxFlow ∧ N.IsMinCut out.cut ∧ out.flow.value = (N.cutCapacity out.cut : ℤ) ∧
      (PushRelabel.init N).IsRun out.ops ∧
      (PushRelabel.init N).numRelabels out.ops ≤ 2 * n ^ 2 ∧
      (PushRelabel.init N).numSatPushes out.ops ≤ 2 * n * N.posArcs.card ∧
      out.discharges ≤ 2 * n ^ 3 ∧
      (PushRelabel.init N).numNonsatPushes out.ops ≤ 4 * n ^ 3 ∧
      out.ops.length ≤ 4 * n ^ 3 ∧
      out.discharges + out.ops.length + out.advances ≤ 8 * n ^ 3 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, _, h11⟩ :=
    relabelToFront_correct (adjValid_defaultAdj N) hst
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h11 fun _ => List.nodup_finRange n⟩

/-- **Correctness, `O(n |E|)` current-arc advance count bound, and `O(n³)`
operation/discharge/advance count bounds for `relabelToFrontExact`.** -/
theorem relabelToFrontExact_correct {n : ℕ} {N : Network (Fin n)} (hst : N.s ≠ N.t) :
    let out := relabelToFrontExact N
    out.flow.IsMaxFlow ∧ N.IsMinCut out.cut ∧ out.flow.value = (N.cutCapacity out.cut : ℤ) ∧
      (PushRelabel.init N).IsRun out.ops ∧
      (PushRelabel.init N).numRelabels out.ops ≤ 2 * n ^ 2 ∧
      (PushRelabel.init N).numSatPushes out.ops ≤ 2 * n * N.posArcs.card ∧
      out.discharges ≤ 2 * n ^ 3 ∧
      (PushRelabel.init N).numNonsatPushes out.ops ≤ 4 * n ^ 3 ∧
      out.ops.length ≤ 4 * n ^ 3 ∧
      out.advances ≤ 4 * n * N.posArcs.card ∧
      out.discharges + out.ops.length + out.advances ≤ 8 * n ^ 3 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    relabelToFront_correct (isAdjacency_exactAdj N) hst
  have hadv : (relabelToFrontExact N).advances ≤ 4 * n * N.posArcs.card := by
    rw [adjSteps_exactAdj_eq N] at h10
    have h2 := Nat.mul_le_mul_left (2 * n) N.card_symArcs_le_two_mul_posArcs
    calc (relabelToFrontExact N).advances
        ≤ 2 * n * N.symArcs.card := h10
      _ ≤ 2 * n * (2 * N.posArcs.card) := h2
      _ = 4 * n * N.posArcs.card := by ring
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hadv, h11 (nodup_exactAdj N)⟩

end Executable

end Cslib.Algorithms.Lean.MaxFlow
