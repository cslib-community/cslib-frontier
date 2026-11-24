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

theorem isAdjacency_exactAdj {n : ℕ} (N : Network (Fin n)) : IsAdjacency N (exactAdj N) := by
  intro u v huv hpos
  simp only [exactAdj, List.mem_filter, List.mem_finRange, decide_eq_true_eq, true_and]
  exact ⟨huv, hpos⟩

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
    simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, Finset.mem_filter, true_and]
    constructor
    · intro h
      exact ⟨u, v, h, rfl⟩
    · rintro ⟨a, b, hb, hab⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hab
      exact hb
  conv_rhs => rw [hpart, Finset.card_biUnion (fun a _ b _ hab =>
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      obtain ⟨_, _, rfl⟩ := hx
      obtain ⟨_, _, heq⟩ := hy
      exact hab (Prod.mk.inj heq).1.symm)]
  refine Finset.sum_congr rfl fun u _ => ?_
  exact (Finset.card_image_of_injective _ fun _ _ h => (Prod.mk.inj h).2).symm

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
    have hcap := s.pr.flow.resCap_le_cap_add_cap u v
    have hmem : v ∈ pre := hpre ▸ hadj u v huv (by omega)
    have h1 := hs.prInv.valid.le_add_one u v hpos
    have h2 : ¬ (0 < s.pr.flow.resCap u v ∧ s.pr.height u = s.pr.height v + 1) := hno v hmem
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
  have hlen : (s.cur u).length ≤ (adj u).length := by
    have := congrArg List.length hpre
    rw [List.length_append] at this
    omega
  unfold dischargeMeasure dischargeFuel
  have h1 : 2 * Fintype.card V - 1 - s.pr.height u ≤ 2 * Fintype.card V - 1 := Nat.sub_le _ _
  have h2 : (2 * Fintype.card V - 1 - s.pr.height u) * (2 * (adj u).length + 2) ≤
      (2 * Fintype.card V - 1) * (2 * (adj u).length + 2) := Nat.mul_le_mul_right _ h1
  have h3 : 2 * (s.cur u).length + (if isHeadAdmissible s u then 1 else 0) ≤
      2 * (adj u).length + 1 := by
    split_ifs <;> omega
  have h4 : (2 * Fintype.card V - 1) * (2 * (adj u).length + 2) + (2 * (adj u).length + 2) =
      2 * Fintype.card V * (2 * (adj u).length + 2) := by
    rw [← Nat.succ_mul]
    congr 1
    omega
  omega

section Decidable

variable [DecidableEq V]

private theorem currentArcInv_advance {adj : V → List V} {σ : PushRelabel.State N}
    {cur : V → List V} (hcur : CurrentArcInv adj σ cur) {u v : V} {vs : List V}
    (hcu : cur u = v :: vs) (hnon : ¬ (0 < σ.flow.resCap u v ∧ σ.height u = σ.height v + 1)) :
    CurrentArcInv adj σ (Function.update cur u vs) := by
  intro x
  by_cases hxu : x = u
  · subst hxu
    obtain ⟨pre, hpre, hno⟩ := hcur x
    refine ⟨pre ++ [v], ?_, fun w hw => ?_⟩
    · rw [Function.update_self, hpre, hcu, List.append_assoc, List.singleton_append]
    · rcases List.mem_append.mp hw with hw' | hw'
      · exact hno w hw'
      · rw [List.mem_singleton.mp hw']
        exact hnon
  · obtain ⟨pre, hpre, hno⟩ := hcur x
    rw [Function.update_of_ne hxu]
    exact ⟨pre, hpre, hno⟩

private theorem currentArcInv_push {adj : V → List V} {σ : PushRelabel.State N}
    {cur : V → List V} (hcur : CurrentArcInv adj σ cur) {u v : V}
    (hp : σ.flow.CanPush σ.height u v) : CurrentArcInv adj (σ.apply (.push u v)) cur := by
  intro x
  obtain ⟨pre, hpre, hno⟩ := hcur x
  refine ⟨pre, hpre, fun w hw ⟨hpos, heq⟩ => ?_⟩
  apply hno w hw
  have huv := hp.ne
  rw [State.apply_push_flow] at hpos
  rw [State.apply_push_height] at heq
  by_cases h1 : x = u ∧ w = v
  · obtain ⟨rfl, rfl⟩ := h1
    rw [σ.flow.resCap_push_self huv] at hpos
    exact ⟨by omega, heq⟩
  · by_cases h2 : x = v ∧ w = u
    · obtain ⟨rfl, rfl⟩ := h2
      have hpeq := hp.height_eq
      change σ.height x = σ.height w + 1 at heq
      omega
    · rw [σ.flow.resCap_push_of_ne h1 h2] at hpos
      exact ⟨hpos, heq⟩

private theorem currentArcInv_relabel {adj : V → List V} {σ : PushRelabel.State N}
    {cur : V → List V} (hvalid : σ.flow.IsValidLabeling σ.height)
    (hcur : CurrentArcInv adj σ cur) {u : V} (hr : σ.flow.CanRelabel σ.height u) :
    CurrentArcInv adj (σ.apply (.relabel u)) (Function.update cur u (adj u)) := by
  intro x
  by_cases hxu : x = u
  · subst hxu
    rw [Function.update_self]
    exact ⟨[], rfl, by simp⟩
  · rw [Function.update_of_ne hxu]
    obtain ⟨pre, hpre, hno⟩ := hcur x
    refine ⟨pre, hpre, fun w hw ⟨hpos, heq⟩ => ?_⟩
    apply hno w hw
    rw [State.apply_relabel_flow] at hpos
    refine ⟨hpos, ?_⟩
    by_cases hwu : w = u
    · subst hwu
      have h1 := hvalid.le_add_one x w hpos
      have h2 : σ.height w < (σ.apply (.relabel w)).height w := by
        change σ.height w < σ.flow.relabel σ.height w w
        rw [Preflow.relabel_self]
        exact hr.lt_relabelHeight
      have hx : (σ.apply (.relabel w)).height x = σ.height x := by
        change σ.flow.relabel σ.height w x = σ.height x
        exact Preflow.relabel_of_ne _ _ hxu
      rw [hx] at heq
      omega
    · have hx : (σ.apply (.relabel u)).height x = σ.height x := by
        change σ.flow.relabel σ.height u x = σ.height x
        exact Preflow.relabel_of_ne _ _ hxu
      have hw' : (σ.apply (.relabel u)).height w = σ.height w := by
        change σ.flow.relabel σ.height u w = σ.height w
        exact Preflow.relabel_of_ne _ _ hwu
      rw [hx, hw'] at heq
      exact heq

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
  rw [State.apply_push_height] at hadm
  rw [State.apply_push_flow] at hadm
  refine ⟨?_, hadm.2⟩
  by_cases h1 : x = u ∧ y = v
  · obtain ⟨rfl, rfl⟩ := h1
    rw [σ.flow.resCap_push_self hp.ne] at hadm
    omega
  · by_cases h2 : x = v ∧ y = u
    · obtain ⟨rfl, rfl⟩ := h2
      have := hp.height_eq
      omega
    · rw [σ.flow.resCap_push_of_ne h1 h2] at hadm
      exact hadm.1

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
    · cases fuel with
      | zero =>
        cases hcu : s.cur u with
        | nil =>
          have hr := canRelabel_of_cur_nil hadj hs hact hcu
          have hlt := hr.lt_relabelHeight
          have hle := (hs.prInv.apply (o := .relabel u) hr).height_le u
          change s.pr.flow.relabel s.pr.height u u ≤ 2 * Fintype.card V - 1 at hle
          rw [Preflow.relabel_self] at hle
          unfold dischargeMeasure at hmeas
          have hmul0 : (2 * Fintype.card V - 1 - s.pr.height u) * (2 * (adj u).length + 2) = 0 := by
            omega
          rcases Nat.mul_eq_zero.mp hmul0 with h0 | h0
          · omega
          · omega
        | cons v vs =>
          unfold dischargeMeasure at hmeas
          rw [hcu] at hmeas
          simp only [List.length_cons] at hmeas
          omega
      | succ fuel =>
        cases hcu : s.cur u with
        | nil =>
          have hr : s.pr.flow.CanRelabel s.pr.height u := canRelabel_of_cur_nil hadj hs hact hcu
          let o : Op V := .relabel u
          let s' : CAState N := ⟨s.pr.apply o, Function.update s.cur u (adj u)⟩
          have hs' : CAInv adj s' :=
            ⟨hs.prInv.apply (o := .relabel u) hr,
              currentArcInv_relabel hs.prInv.valid hs.curInv hr⟩
          have hlt : s.pr.height u < s'.pr.height u := by
            change s.pr.height u < s.pr.flow.relabel s.pr.height u u
            rw [Preflow.relabel_self]
            exact hr.lt_relabelHeight
          have hle : s'.pr.height u ≤ 2 * Fintype.card V - 1 := hs'.prInv.height_le u
          have hmeas' : dischargeMeasure adj u s' ≤ fuel := by
            unfold dischargeMeasure at hmeas ⊢
            have had : (s'.cur u).length = (adj u).length := by simp [s']
            have his : (if isHeadAdmissible s' u then 1 else 0) ≤ 1 := by split_ifs <;> omega
            have h1 : 2 * Fintype.card V - 1 - s'.pr.height u + 1 ≤
                2 * Fintype.card V - 1 - s.pr.height u := by omega
            have h2 : (2 * Fintype.card V - 1 - s'.pr.height u + 1) * (2 * (adj u).length + 2) ≤
                (2 * Fintype.card V - 1 - s.pr.height u) * (2 * (adj u).length + 2) :=
              Nat.mul_le_mul_right _ h1
            rw [Nat.add_mul, Nat.one_mul] at h2
            omega
          have ih := dischargeLoop_spec hadj hnorm u fuel s' hs' hmeas'
          have hnorm' : norm ⟨s.pr.apply o, Function.update s.cur u (adj u)⟩ = s' :=
            hnorm ⟨s.pr.apply o, Function.update s.cur u (adj u)⟩
          rw [dischargeLoop, ite_eq_left hact]
          dsimp only
          rw [hcu]
          dsimp only
          rw [hnorm']
          obtain ⟨ihInv, ihRun, ihPr, ihAct, ihNs, ihRel, ihNe, ihH, ihAdv, _, ihBk, _, ihIn,
            ihRes⟩ := ih
          refine ⟨ihInv, ⟨hr, ihRun⟩, ihPr, ihAct, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [State.numNonsatPushes_cons]
            have hno : ¬ (Op.IsPush (o : Op V) ∧ ¬ s.pr.IsSatPush o) := fun h => h.1
            rw [ite_eq_right hno, Nat.zero_add]
            exact ihNs
          · constructor
            · intro _
              rw [State.numRelabels_cons, ite_eq_left (show (o : Op V).IsRelabel from trivial)]
              omega
            · intro _; rfl
          · intro x hx
            obtain ⟨hcx, hhx⟩ := ihNe x hx
            refine ⟨hcx.trans (Function.update_of_ne hx _ _), hhx.trans ?_⟩
            change s.pr.flow.relabel s.pr.height u x = s.pr.height x
            exact Preflow.relabel_of_ne _ _ hx
          · have hr_eq : (s.pr.apply o).numRelabels (dischargeLoop adj norm u fuel s').ops =
                s'.pr.numRelabels (dischargeLoop adj norm u fuel s').ops := rfl
            rw [State.numRelabels_cons, ite_eq_left (show (o : Op V).IsRelabel from trivial),
              hr_eq]
            omega
          · have hr_eq : (s.pr.apply o).numRelabels (dischargeLoop adj norm u fuel s').ops =
                s'.pr.numRelabels (dischargeLoop adj norm u fuel s').ops := rfl
            rw [State.numRelabels_cons, ite_eq_left (show (o : Op V).IsRelabel from trivial),
              hr_eq, Nat.add_mul, Nat.one_mul, List.length_nil, Nat.zero_add]
            have hsu : (s'.cur u).length = (adj u).length := by simp [s']
            omega
          · intro h; simp at h
          · intro h; simp at h
          · intro h; simp at h
          · intro _ w hw ⟨hpos, heq⟩
            by_cases hrel : (dischargeLoop adj norm u fuel s').relabeled = true
            · exact ihIn hrel w hw ⟨hpos, heq⟩
            · have hrel_f : (dischargeLoop adj norm u fuel s').relabeled = false :=
                Bool.eq_false_iff.mpr hrel
              have hadm' := ihBk hrel_f w u ⟨hpos, heq⟩
              have hwx : s'.pr.flow.resCap w u = s.pr.flow.resCap w u := rfl
              have h1 := hs.prInv.valid.le_add_one w u (hwx ▸ hadm'.1)
              have h2 : s'.pr.height w = s.pr.height w := by
                change s.pr.flow.relabel s.pr.height u w = s.pr.height w
                exact Preflow.relabel_of_ne _ _ hw
              omega
          · intro x y hx hy
            exact ihRes x y hx hy
        | cons v vs =>
          by_cases hadm : 0 < s.pr.flow.resCap u v ∧ s.pr.height u = s.pr.height v + 1
          · have hp : s.pr.flow.CanPush s.pr.height u v := ⟨hact, hadm.1, hadm.2⟩
            let o : Op V := .push u v
            let s' : CAState N := ⟨s.pr.apply o, s.cur⟩
            have hs' : CAInv adj s' :=
              ⟨hs.prInv.apply (o := .push u v) hp, currentArcInv_push hs.curInv hp⟩
            have hnorm' : norm ⟨s.pr.apply o, s.cur⟩ = s' := hnorm ⟨s.pr.apply o, s.cur⟩
            by_cases hsat : s.pr.IsSatPush o
            · have hhead : isHeadAdmissible s u := by simp [isHeadAdmissible, hcu, hadm]
              have hhead' : ¬ isHeadAdmissible s' u := by
                simp only [isHeadAdmissible, s', o, State.apply_push_flow, hcu]
                rw [s.pr.flow.resCap_push_self hp.ne]
                have hsat' : s.pr.flow.pushAmount u v = s.pr.flow.resCap u v := hsat
                omega
              have hmeas' : dischargeMeasure adj u s' ≤ fuel := by
                unfold dischargeMeasure at hmeas ⊢
                rw [ite_eq_left hhead] at hmeas
                rw [ite_eq_right hhead']
                have hlen : (s'.cur u).length = (s.cur u).length := rfl
                have hht : s'.pr.height u = s.pr.height u := rfl
                rw [hlen, hht]
                omega
              have ih := dischargeLoop_spec hadj hnorm u fuel s' hs' hmeas'
              rw [dischargeLoop, ite_eq_left hact]
              dsimp only
              rw [hcu]
              dsimp only
              rw [ite_eq_left hadm]
              dsimp only
              rw [hnorm']
              obtain ⟨ihInv, ihRun, ihPr, ihAct, ihNs, ihRel, ihNe, ihH, ihAdv, ihHeq, ihBk,
                ihEx, ihIn, ihRes⟩ := ih
              refine ⟨ihInv, ⟨hp, ihRun⟩, ihPr, ihAct, ?_, ?_, ihNe, ?_, ?_, ihHeq, ?_, ?_,
                ihIn, ?_⟩
              · rw [State.numNonsatPushes_cons]
                have hno : ¬ (Op.IsPush o ∧ ¬ s.pr.IsSatPush o) := fun h => h.2 hsat
                rw [ite_eq_right hno, Nat.zero_add]
                exact ihNs
              · rw [State.numRelabels_cons, ite_eq_right (show ¬ (o : Op V).IsRelabel from id),
                  Nat.zero_add]
                exact ihRel
              · rw [State.numRelabels_cons, ite_eq_right (show ¬ (o : Op V).IsRelabel from id),
                  Nat.zero_add]
                exact ihH
              · rw [State.numRelabels_cons, ite_eq_right (show ¬ (o : Op V).IsRelabel from id),
                  Nat.zero_add]
                have hsc : s'.cur u = v :: vs := hcu
                have hr_eq : (s.pr.apply o).numRelabels (dischargeLoop adj norm u fuel s').ops =
                    s'.pr.numRelabels (dischargeLoop adj norm u fuel s').ops := rfl
                rw [hsc, hr_eq] at ihAdv
                exact ihAdv
              · intro hrel x y hxy
                exact push_preserves_admissible_backward hp (ihBk hrel x y hxy)
              · intro hrel w hwu hnon
                rw [ihEx hrel w hwu (fun h => hnon (push_preserves_admissible_backward hp h))]
                by_cases hwv : w = v
                · subst hwv
                  exfalso
                  exact hnon ⟨hp.resCap_pos, hp.height_eq⟩
                · exact s.pr.flow.excess_push_of_ne hwu hwv
              · intro x y hx hy
                have h1 : ¬ (x = u ∧ y = v) := fun h => hx h.1
                have h2 : ¬ (x = v ∧ y = u) := fun h => hy h.2
                exact (ihRes x y hx hy).trans (s.pr.flow.resCap_push_of_ne h1 h2)
            · -- Nonsaturating push: `u` becomes inactive and `dischargeLoop` returns at once.
              have hamt : (s.pr.flow.pushAmount u v : ℤ) = s.pr.flow.excess u := by
                have hex_pos : 0 < s.pr.flow.excess u := hact.2.2
                have h1 : s.pr.flow.pushAmount u v ≠ s.pr.flow.resCap u v := hsat
                rcases le_total (s.pr.flow.excess u).toNat (s.pr.flow.resCap u v) with hle | hlt
                · simp only [Preflow.pushAmount, min_eq_left hle]
                  omega
                · exfalso
                  exact h1 (by simp [Preflow.pushAmount, min_eq_right hlt])
              have hnact' : ¬ s'.pr.flow.IsActive u := fun h => by
                have hex := s.pr.flow.excess_push_self hp.ne
                have h2 := h.2.2
                change 0 < (s.pr.flow.push u v).excess u at h2
                omega
              have hstop : dischargeLoop adj norm u fuel s' = ⟨[], s', 0, false⟩ := by
                rw [dischargeLoop.eq_def]
                dsimp only
                rw [ite_eq_right hnact']
              rw [dischargeLoop, ite_eq_left hact]
              dsimp only
              rw [hcu]
              dsimp only
              rw [ite_eq_left hadm]
              dsimp only
              rw [hnorm', hstop]
              refine ⟨hs', ⟨hp, trivial⟩, rfl, hnact', ?_, ?_, fun _ _ => ⟨rfl, rfl⟩,
                ?_, ?_, fun _ => rfl, ?_, ?_, fun h => by simp at h, ?_⟩
              · rw [State.numNonsatPushes_cons]
                have hns : Op.IsPush o ∧ ¬ s.pr.IsSatPush o := ⟨trivial, hsat⟩
                rw [ite_eq_left hns]
                simp [State.numNonsatPushes, State.countOps]
              · rw [State.numRelabels_cons, ite_eq_right (show ¬ (o : Op V).IsRelabel from id)]
                simp [State.numRelabels, State.countOps]
              · rw [State.numRelabels_cons, ite_eq_right (show ¬ (o : Op V).IsRelabel from id)]
                have hht : s'.pr.height u = s.pr.height u := rfl
                simp [State.numRelabels, State.countOps, hht]
              · rw [State.numRelabels_cons, ite_eq_right (show ¬ (o : Op V).IsRelabel from id)]
                have hsc : s'.cur u = v :: vs := hcu
                simp [State.numRelabels, State.countOps, hsc]
              · intro _ x y hxy
                exact push_preserves_admissible_backward hp hxy
              · intro _ w hwu hnon
                by_cases hwv : w = v
                · subst hwv
                  exfalso
                  exact hnon ⟨hp.resCap_pos, hp.height_eq⟩
                · exact s.pr.flow.excess_push_of_ne hwu hwv
              · intro x y hx hy
                have h1 : ¬ (x = u ∧ y = v) := fun h => hx h.1
                have h2 : ¬ (x = v ∧ y = u) := fun h => hy h.2
                exact s.pr.flow.resCap_push_of_ne h1 h2
          · -- Advance current-arc pointer
            let s' : CAState N := ⟨s.pr, Function.update s.cur u vs⟩
            have hs' : CAInv adj s' := ⟨hs.prInv, currentArcInv_advance hs.curInv hcu hadm⟩
            have hhead : ¬ isHeadAdmissible s u := by simp [isHeadAdmissible, hcu, hadm]
            have hmeas' : dischargeMeasure adj u s' ≤ fuel := by
              unfold dischargeMeasure at hmeas ⊢
              rw [ite_eq_right hhead] at hmeas
              have hlen : (s'.cur u).length = vs.length := by simp [s']
              have hlen0 : (s.cur u).length = vs.length + 1 := by simp [hcu]
              have hht : s'.pr.height u = s.pr.height u := rfl
              have his : (if isHeadAdmissible s' u then 1 else 0) ≤ 1 := by split_ifs <;> omega
              rw [hlen, hht]
              rw [hlen0] at hmeas
              omega
            have ih := dischargeLoop_spec hadj hnorm u fuel s' hs' hmeas'
            have hnorm' : norm ⟨s.pr, Function.update s.cur u vs⟩ = s' :=
              hnorm ⟨s.pr, Function.update s.cur u vs⟩
            rw [dischargeLoop, ite_eq_left hact]
            dsimp only
            rw [hcu]
            dsimp only
            rw [ite_eq_right hadm]
            dsimp only
            rw [hnorm']
            obtain ⟨ihInv, ihRun, ihPr, ihAct, ihNs, ihRel, ihNe, ihH, ihAdv, ihHeq, ihBk,
              ihEx, ihIn, ihRes⟩ := ih
            refine ⟨ihInv, ihRun, ihPr, ihAct, ihNs, ihRel, fun x hx => ?_, ihH, ?_, ihHeq,
              ihBk, ihEx, ihIn, ihRes⟩
            · obtain ⟨hcx, hhx⟩ := ihNe x hx
              exact ⟨hcx.trans (Function.update_of_ne hx _ _), hhx⟩
            · have hlen : (s'.cur u).length = vs.length := by simp [s']
              have hpr_eq : s'.pr = s.pr := rfl
              rw [hlen, hpr_eq] at ihAdv
              rw [List.length_cons]
              omega
    · rw [dischargeLoop.eq_def]
      dsimp only
      rw [ite_eq_right hact]
      refine ⟨hs, trivial, rfl, hact, by simp [State.numNonsatPushes, State.countOps],
        by simp [State.numRelabels, State.countOps], fun _ _ => ⟨rfl, rfl⟩,
        by simp [State.numRelabels, State.countOps],
        by simp [State.numRelabels, State.countOps],
        fun _ => rfl, fun _ _ _ h => h, fun _ _ _ _ => rfl, fun h => by simp at h,
        fun _ _ _ _ => rfl⟩

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
  | a :: ds, rest, hu, hb => by
    have hau : a ≠ u := fun h => hu (h ▸ List.mem_cons_self)
    have hu' : u ∉ ds := fun h => hu (List.mem_cons_of_mem _ h)
    cases hb with
    | head _ => exact absurd rfl hau.symm
    | tail htail => exact before_append_cons hu' htail

private theorem not_before_of_nodup_append {α : Type*} {u v : α} {done rest : List α}
    (hnd : (done ++ u :: rest).Nodup) (hv : v ∈ done) : ¬ Before u v (done ++ u :: rest) := by
  intro hb
  have hdisj := (List.nodup_append.mp hnd).2.2
  have hu : u ∉ done := fun h => hdisj u h u List.mem_cons_self rfl
  have hv_rest : v ∈ rest := before_append_cons hu hb
  exact hdisj v hv v (List.mem_cons_of_mem _ hv_rest) rfl

private theorem before_erase_cons {α : Type*} {x y u : α} (hx : x ≠ u) (hy : y ≠ u) :
    ∀ {done rest : List α}, Before x y (done ++ u :: rest) → Before x y (done ++ rest)
  | [], rest, hb => by
    cases hb with
    | head _ => exact absurd rfl hx.symm
    | tail htail => exact htail
  | a :: ds, rest, hb => by
    simp only [List.cons_append] at hb ⊢
    cases hb with
    | head hmem =>
      refine .head ?_
      rcases List.mem_append.mp hmem with hm | hm
      · exact List.mem_append_left _ hm
      · rcases List.mem_cons.mp hm with rfl | hm'
        · exact absurd rfl hy
        · exact List.mem_append_right _ hm'
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
    {u : V} {rest : List V} (htodo : st.todo = u :: rest) {d : DischargeOutput N}
    (hdInv : CAInv adj d.ca) (hdAct : ¬ d.ca.pr.flow.IsActive u)
    (hdNe : ∀ x, x ≠ u → d.ca.cur x = st.ca.cur x ∧ d.ca.pr.height x = st.ca.pr.height x)
    (hdIn : ∀ w, w ≠ u →
      ¬ (0 < d.ca.pr.flow.resCap w u ∧ d.ca.pr.height w = d.ca.pr.height u + 1))
    (hdRes : ∀ x y, x ≠ u → y ≠ u → d.ca.pr.flow.resCap x y = st.ca.pr.flow.resCap x y) :
    RTFInv adj
      { ca := d.ca
        done := [u]
        todo := st.done ++ rest
        discharges := st.discharges + 1
        advances := st.advances + d.advances } := by
  have hnodup0 : (st.done ++ u :: rest).Nodup := htodo ▸ hinv.nodup
  have hdisj := (List.nodup_append.mp hnodup0).2.2
  have hu_done : u ∉ st.done := fun h => hdisj u h u List.mem_cons_self rfl
  have hu_rest : u ∉ rest := (List.nodup_cons.mp (List.nodup_append.mp hnodup0).2.1).1
  have hnodup' : ([u] ++ (st.done ++ rest)).Nodup := by
    rw [List.singleton_append, List.nodup_cons]
    refine ⟨fun h => ?_, ?_⟩
    · rcases List.mem_append.mp h with h1 | h1
      · exact hu_done h1
      · exact hu_rest h1
    · rw [List.nodup_append]
      refine ⟨(List.nodup_append.mp hnodup0).1,
        (List.nodup_cons.mp (List.nodup_append.mp hnodup0).2.1).2, fun a ha b hb hab => ?_⟩
      exact hdisj a ha b (List.mem_cons_of_mem u hb) hab
  have hmem' : ∀ v, v ∈ [u] ++ (st.done ++ rest) ↔ v ≠ N.s ∧ v ≠ N.t := fun v => by
    have hm0 := hinv.mem_iff v
    rw [htodo] at hm0
    rw [← hm0]
    simp only [List.singleton_append, List.mem_cons, List.mem_append, or_left_comm]
  have htopo' : TopoOrder d.ca.pr ([u] ++ (st.done ++ rest)) := by
    intro x hx y hy hpos heq
    simp only [List.singleton_append, List.mem_cons] at hx hy
    rcases hx with rfl | hx'
    · rcases hy with rfl | hy'
      · omega
      · exact .head hy'
    · rcases hy with hyu | hy'
      · exfalso
        have hxu : x ≠ u := fun h => (List.nodup_cons.mp hnodup').1 (h ▸ hx')
        rw [hyu] at hpos heq
        exact hdIn x hxu ⟨hpos, heq⟩
      · have hxu : x ≠ u := fun h => (List.nodup_cons.mp hnodup').1 (h ▸ hx')
        have hyu : y ≠ u := fun h => (List.nodup_cons.mp hnodup').1 (h ▸ hy')
        have hres_eq : d.ca.pr.flow.resCap x y = st.ca.pr.flow.resCap x y := hdRes x y hxu hyu
        have hhx : d.ca.pr.height x = st.ca.pr.height x := (hdNe x hxu).2
        have hhy : d.ca.pr.height y = st.ca.pr.height y := (hdNe y hyu).2
        have hx0 : x ∈ st.done ++ u :: rest := by
          rcases List.mem_append.mp hx' with h | h
          · exact List.mem_append_left _ h
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
        have hy0 : y ∈ st.done ++ u :: rest := by
          rcases List.mem_append.mp hy' with h | h
          · exact List.mem_append_left _ h
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
        have hb := hinv.topo x (htodo ▸ hx0) y (htodo ▸ hy0)
          (hres_eq ▸ hpos) (hhx ▸ hhy ▸ heq)
        rw [htodo] at hb
        exact .tail (before_erase_cons (done := st.done) (rest := rest) hxu hyu hb)
  refine ⟨hdInv, hnodup', hmem', htopo', fun w hw => ?_⟩
  rw [List.mem_singleton.mp hw]
  exact hdAct

omit [DecidableEq V] in
private theorem rtfInv_noRelabel {adj : V → List V} {st : RTFState N} (hinv : RTFInv adj st)
    {u : V} {rest : List V} (htodo : st.todo = u :: rest) {d : DischargeOutput N}
    (hdInv : CAInv adj d.ca) (hdAct : ¬ d.ca.pr.flow.IsActive u)
    (hdBk : ∀ x y, (0 < d.ca.pr.flow.resCap x y ∧ d.ca.pr.height x = d.ca.pr.height y + 1) →
      0 < st.ca.pr.flow.resCap x y ∧ st.ca.pr.height x = st.ca.pr.height y + 1)
    (hdEx : ∀ w, w ≠ u →
      ¬ (0 < st.ca.pr.flow.resCap u w ∧ st.ca.pr.height u = st.ca.pr.height w + 1) →
      d.ca.pr.flow.excess w = st.ca.pr.flow.excess w) :
    RTFInv adj
      { ca := d.ca
        done := st.done ++ [u]
        todo := rest
        discharges := st.discharges + 1
        advances := st.advances + d.advances } := by
  have hu_mem : u ∈ st.done ++ u :: rest := List.mem_append_right _ List.mem_cons_self
  have hassoc : (st.done ++ [u]) ++ rest = st.done ++ u :: rest := by simp [List.append_assoc]
  have hnodup' : ((st.done ++ [u]) ++ rest).Nodup := hassoc ▸ htodo ▸ hinv.nodup
  have hmem' : ∀ v, v ∈ (st.done ++ [u]) ++ rest ↔ v ≠ N.s ∧ v ≠ N.t :=
    fun v => hassoc ▸ htodo ▸ hinv.mem_iff v
  have htopo' : TopoOrder d.ca.pr ((st.done ++ [u]) ++ rest) := by
    intro x hx y hy hpos heq
    have hx0 : x ∈ st.done ++ u :: rest := hassoc ▸ hx
    have hy0 : y ∈ st.done ++ u :: rest := hassoc ▸ hy
    obtain ⟨hpos0, heq0⟩ := hdBk x y ⟨hpos, heq⟩
    have hb := hinv.topo x (htodo ▸ hx0) y (htodo ▸ hy0) hpos0 heq0
    exact hassoc ▸ htodo ▸ hb
  refine ⟨hdInv, hnodup', hmem', htopo', fun w hw => ?_⟩
  rcases List.mem_append.mp hw with hw' | hw'
  · have hnodup0 : (st.done ++ u :: rest).Nodup := htodo ▸ hinv.nodup
    have hdisj := (List.nodup_append.mp hnodup0).2.2
    have hwu : w ≠ u := fun h => hdisj w hw' u List.mem_cons_self h
    have hnon : ¬ (0 < st.ca.pr.flow.resCap u w ∧
        st.ca.pr.height u = st.ca.pr.height w + 1) := by
      rintro ⟨hpos, heq⟩
      have hw0 : w ∈ st.done ++ u :: rest := List.mem_append_left _ hw'
      have hb := hinv.topo u (htodo ▸ hu_mem) w (htodo ▸ hw0) hpos heq
      rw [htodo] at hb
      exact not_before_of_nodup_append hnodup0 hw' hb
    have hex_eq := hdEx w hwu hnon
    have hinact := hinv.done_inactive w hw'
    unfold Preflow.IsActive at hinact ⊢
    rw [hex_eq]
    exact hinact
  · rw [List.mem_singleton.mp hw']
    exact hdAct

private theorem rtfMeasure_step {adj : V → List V} {st : RTFState N}
    {u : V} {rest : List V} (htodo : st.todo = u :: rest)
    (hlen : (st.done ++ u :: rest).length = Fintype.card V - 2)
    {d : DischargeOutput N} (hdInv : CAInv adj d.ca) (hdRun : st.ca.pr.IsRun d.ops)
    (hdPr : d.ca.pr = st.ca.pr.run d.ops)
    (hdRel : d.relabeled = true ↔ 0 < st.ca.pr.numRelabels d.ops)
    (hdHeq : d.relabeled = false → d.ca.pr.height = st.ca.pr.height) :
    let st' : RTFState N :=
      if d.relabeled then
        { ca := d.ca, done := [u], todo := st.done ++ rest,
          discharges := st.discharges + 1, advances := st.advances + d.advances }
      else
        { ca := d.ca, done := st.done ++ [u], todo := rest,
          discharges := st.discharges + 1, advances := st.advances + d.advances }
    rtfMeasure V st' + 1 ≤ rtfMeasure V st := by
  intro st'
  have hsum_d : st.ca.pr.numRelabels d.ops + ∑ v, st.ca.pr.height v ≤ ∑ v, d.ca.pr.height v := by
    rw [hdPr]
    exact State.numRelabels_add_sum_le hdRun
  have hsum_le : ∑ v, d.ca.pr.height v ≤ sumHeightMax V := State.sum_height_le hdInv.prInv
  have hcard2 : 1 ≤ Fintype.card V - 2 := by
    rw [← hlen, List.length_append, List.length_cons]
    omega
  have hst'_ca : st'.ca = d.ca := by
    dsimp only [st']
    split_ifs <;> rfl
  by_cases hrel : d.relabeled = true
  · have hrel_pos : 0 < st.ca.pr.numRelabels d.ops := hdRel.mp hrel
    have htodo' : st'.todo.length = (st.done ++ rest).length := by simp [st', hrel]
    have htodo_le : st'.todo.length + 1 ≤ Fintype.card V - 2 := by
      rw [htodo', List.length_append]
      rw [List.length_append, List.length_cons] at hlen
      omega
    unfold rtfMeasure
    rw [htodo, htodo', hst'_ca]
    have h1 : sumHeightMax V - ∑ v, d.ca.pr.height v + 1 ≤
        sumHeightMax V - ∑ v, st.ca.pr.height v := by omega
    have h2 : (sumHeightMax V - ∑ v, d.ca.pr.height v + 1) * (Fintype.card V - 2) ≤
        (sumHeightMax V - ∑ v, st.ca.pr.height v) * (Fintype.card V - 2) :=
      Nat.mul_le_mul_right _ h1
    rw [Nat.add_mul, Nat.one_mul] at h2
    omega
  · have hrel_f : d.relabeled = false := Bool.eq_false_iff.mpr hrel
    have htodo' : st'.todo.length = rest.length := by simp [st', hrel_f]
    have hht : st'.ca.pr.height = st.ca.pr.height := by
      rw [hst'_ca]
      exact hdHeq hrel_f
    unfold rtfMeasure
    rw [htodo, htodo', hht]
    simp only [List.length_cons]
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
        have hlen : (st.done ++ u :: rest).length = Fintype.card V - 2 :=
          list_nodup_length_eq_card_sub_two (htodo ▸ hinv.nodup) (htodo ▸ hinv.mem_iff) hst
        have hu_mem : u ∈ st.done ++ u :: rest := List.mem_append_right _ List.mem_cons_self
        have hu_ne : u ≠ N.s ∧ u ≠ N.t := (htodo ▸ hinv.mem_iff u).mp hu_mem
        have hd := discharge_spec hadj hcaNorm u hinv.caInv
        generalize hd_eq : discharge adj caNorm u st.ca = d at hd ⊢
        obtain ⟨hdInv, hdRun, hdPr, hdAct, hdNs, hdRel, hdNe, hdH, hdAdv, hdHeq, hdBk, hdEx,
          hdIn, hdRes⟩ := hd
        have hadv_d : d.advances + advPotential adj d.ca ≤ advPotential adj st.ca :=
          advPotential_discharge hu_ne.1 hu_ne.2 hinv.caInv hdInv hdNe hdH hdAdv
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
        have hinv' : RTFInv adj st' := by
          by_cases hrel : d.relabeled = true
          · simpa only [st', hrel, ↓reduceIte] using
              rtfInv_relabel hinv htodo hdInv hdAct hdNe (hdIn hrel) hdRes
          · have hrel_f : d.relabeled = false := Bool.eq_false_iff.mpr hrel
            simpa only [st', hrel_f, Bool.false_eq_true, ↓reduceIte] using
              rtfInv_noRelabel hinv htodo hdInv hdAct (hdBk hrel_f) (hdEx hrel_f)
        have hmeas' : rtfMeasure V st' + 1 ≤ rtfMeasure V st :=
          rtfMeasure_step htodo hlen hdInv hdRun hdPr hdRel hdHeq
        have ih := rtfLoop_spec hadj hcaNorm hstNorm hst fuel st' hinv' (by omega)
        have hst_norm : stNorm st' = st' := hstNorm st'
        have hca_eq : st'.ca = d.ca := by
          dsimp only [st']
          split_ifs <;> rfl
        have hdis_eq : st'.discharges = st.discharges + 1 := by
          dsimp only [st']
          split_ifs <;> rfl
        have hadv_eq : st'.advances = st.advances + d.advances := by
          dsimp only [st']
          split_ifs <;> rfl
        have hloop_eq : rtfLoop adj caNorm stNorm (fuel + 1) st =
            let r := rtfLoop adj caNorm stNorm fuel st'
            (d.ops ++ r.1, r.2) := by
          rw [rtfLoop]
          dsimp only
          rw [htodo]
          dsimp only
          rw [hd_eq]
          change let r := rtfLoop adj caNorm stNorm fuel (stNorm st'); (d.ops ++ r.1, r.2) = _
          rw [hst_norm]
        rw [hloop_eq]
        dsimp only
        obtain ⟨ihInv, ihTodo, ihRun, ihPr, ihNs, ihDisLe, ihDis, ihAdv⟩ := ih
        rw [hca_eq, hdPr] at ihRun ihPr ihNs
        refine ⟨ihInv, ihTodo, State.isRun_append hdRun ihRun, ?_, ?_, ?_, ?_, ?_⟩
        · rw [State.run_append]
          exact ihPr
        · rw [State.numNonsatPushes_append]
          omega
        · omega
        · omega
        · rw [hadv_eq, hca_eq] at ihAdv
          omega

end RelabelToFrontSection

end RelabelToFront

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
    rw [sum_height_init, hlen]
    have h1 : Fintype.card V + (Fintype.card V - 2) * (2 * Fintype.card V - 1) -
        Fintype.card V = (Fintype.card V - 2) * (2 * Fintype.card V - 1) := by omega
    rw [h1]
    ring
  have hlt_fuel : rtfMeasure V (RTFState.init N adj vs) < rtfFuel V := by
    rw [hmeas0]
    unfold rtfFuel
    omega
  obtain ⟨hfinInv, htodo, hrun, _, hns, _, hdis, hadv⟩ :=
    rtfLoop_spec hadj hcaNorm hstNorm hst (rtfFuel V) (RTFState.init N adj vs)
      (rtfInv_init hst hnodup hmem) hlt_fuel
  have hnot_act : ∀ v, ¬ (rtfLoop adj caNorm stNorm (rtfFuel V)
      (RTFState.init N adj vs)).2.ca.pr.flow.IsActive v := fun v hv => by
    have hv' : v ∈ (rtfLoop adj caNorm stNorm (rtfFuel V)
        (RTFState.init N adj vs)).2.done := by
      have hm := (hfinInv.mem_iff v).mpr ⟨hv.1, hv.2.1⟩
      rw [htodo, List.append_nil] at hm
      exact hm
    exact hfinInv.done_inactive v hv' hv
  have hz := excess_eq_zero_of_forall_not_isActive _ hnot_act
  have hmax := hfinInv.caInv.prInv.valid.isMaxFlow_toFlow hz
  obtain ⟨hmin, hval⟩ := hfinInv.caInv.prInv.valid.isMinCut_gapCut hz
  have hdis_le : (rtfLoop adj caNorm stNorm (rtfFuel V)
      (RTFState.init N adj vs)).2.discharges ≤
      (Fintype.card V - 2) * ((Fintype.card V - 2) * (2 * Fintype.card V - 1) + 1) := by
    have hinit : (RTFState.init N adj vs).discharges = 0 := rfl
    rw [hinit, Nat.zero_add, hmeas0] at hdis
    exact hdis
  have hadv_le : (rtfLoop adj caNorm stNorm (rtfFuel V)
      (RTFState.init N adj vs)).2.advances ≤
      2 * Fintype.card V * ∑ v ∈ (Finset.univ.erase N.s).erase N.t, (adj v).length := by
    have h1 := (Nat.le_add_right _ _).trans hadv
    have hinit : (RTFState.init N adj vs).advances = 0 := rfl
    have hca : (RTFState.init N adj vs).ca = CAState.init N adj := rfl
    rw [hinit, hca, Nat.zero_add, advPotential_init adj] at h1
    exact h1
  have hns_le : (PushRelabel.init N).numNonsatPushes
      (rtfLoop adj caNorm stNorm (rtfFuel V) (RTFState.init N adj vs)).1 ≤
      (rtfLoop adj caNorm stNorm (rtfFuel V) (RTFState.init N adj vs)).2.discharges := by
    have hpr : (RTFState.init N adj vs).ca.pr = PushRelabel.init N := rfl
    have hinit : (RTFState.init N adj vs).discharges = 0 := rfl
    rw [hpr, hinit, Nat.sub_zero] at hns
    exact hns
  unfold relabelToFrontWith
  rw [ite_eq_right hst]
  simp only [RelabelToFrontOutput.ofState]
  rw [dite_eq_left hz]
  exact ⟨hmax, hmin, hval, hrun, hdis_le, hns_le, hadv_le⟩

private theorem card_sub_two_bound (n : ℕ) (hn : 2 ≤ n) :
    (n - 2) * ((n - 2) * (2 * n - 1) + 1) ≤ 2 * n ^ 3 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have h1 : k + 2 - 2 = k := by omega
  have h2 : 2 * (k + 2) - 1 = 2 * k + 3 := by omega
  rw [h1, h2]
  have hsum :
      2 * (k + 2) ^ 3 = k * (k * (2 * k + 3) + 1) + (9 * k ^ 2 + 23 * k + 16) := by ring
  omega

private theorem ops_sum_bound (n : ℕ) (hn : 2 ≤ n) :
    (n - 2) * (2 * n - 1) + n * (n * (n - 1)) +
      (n - 2) * ((n - 2) * (2 * n - 1) + 1) ≤ 4 * n ^ 3 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have h1 : k + 2 - 2 = k := by omega
  have h2 : 2 * (k + 2) - 1 = 2 * k + 3 := by omega
  have h3 : k + 2 - 1 = k + 1 := by omega
  rw [h1, h2, h3]
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
  have h2n : 2 ≤ Fintype.card V := by
    have hcard : ({N.s, N.t} : Finset V).card ≤ Fintype.card V := Finset.card_le_univ _
    rw [Finset.card_pair hst] at hcard
    exact hcard
  have hrel := numRelabels_lt hst hrun
  have hrel_sharp := numRelabels_le hst hrun
  have hsat := numSatPushes_le_posArcs hst hrun
  have hsat_sharp := numSatPushes_le hst hrun
  have hdis_cube : (relabelToFrontWith N vs adj caNorm stNorm).discharges ≤
      2 * Fintype.card V ^ 3 :=
    hdis.trans (card_sub_two_bound (Fintype.card V) h2n)
  have hns_cube : (PushRelabel.init N).numNonsatPushes
      (relabelToFrontWith N vs adj caNorm stNorm).ops ≤ 4 * Fintype.card V ^ 3 := by
    have : 2 * Fintype.card V ^ 3 ≤ 4 * Fintype.card V ^ 3 := by omega
    exact hns.trans (hdis_cube.trans this)
  have hlen : (relabelToFrontWith N vs adj caNorm stNorm).ops.length ≤ 4 * Fintype.card V ^ 3 := by
    rw [State.length_eq (PushRelabel.init N)]
    have hsat_v : Fintype.card V * N.symArcs.card ≤
        Fintype.card V * (Fintype.card V * (Fintype.card V - 1)) :=
      Nat.mul_le_mul_left _ N.card_symArcs_le_mul_pred
    have hsum := ops_sum_bound (Fintype.card V) h2n
    omega
  exact ⟨hrel.le, hsat, hdis_cube, hns_cube, hlen⟩

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
