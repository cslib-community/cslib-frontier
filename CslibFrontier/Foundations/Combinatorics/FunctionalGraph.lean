/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Card
public import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Data.Nat.ModEq

/-!
# Orbits in finite functional graphs

Iterating `f : α → α` from a state `x` traces a path in the functional graph of `f`. On a finite
type every orbit eventually enters a cycle: its *transient depth* is the first time it reaches a
periodic point, and its *cycle length* is the minimal period of that point. The transient and
one complete cycle contain no repeated state (`orbit_prefix_injective`), so their total length
is at most the number of states (`transientDepth_add_cycleLength_le_card`).

A repeat `f^[i] x = f^[j] x` with `i < j` makes `f^[i] x` periodic with period `j - i` and reduces
every later time modulo `j - i` (`iterate_add_mod_sub`). Consequently every reachable target has
a first visit before the number of states (`exists_first_visit`), and the map that stops at a
target finds it after that many steps (`absorb_iterate_card`).

The state type may live in any universe. Finiteness is required only where stated.

## Main definitions

* `Cslib.FunctionalGraph.absorb`: stop at states satisfying a predicate.
* `Cslib.FunctionalGraph.transientDepth`: the first time an orbit is periodic.
* `Cslib.FunctionalGraph.cycleLength`: the period of the eventual cycle.

## Main results

* `Cslib.FunctionalGraph.exists_first_visit`: first visits occur before the state count.
* `Cslib.FunctionalGraph.absorb_iterate_card_eq_iff`: the absorbing map decides reachability.
* `Cslib.FunctionalGraph.iterate_mem_periodicPts_iff`: periodicity begins exactly at the
  transient depth.
* `Cslib.FunctionalGraph.orbit_prefix_injective`: the transient and one cycle are repeat-free.
* `Cslib.FunctionalGraph.exists_iterate_eq_iff_of_not_mem_periodicPts`: a transient target is
  reached only at the difference of transient depths.

## References

* Adapted from lean/Proofs/{Reconstruction,FiniteOrbit,OrbitStructure}.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.FunctionalGraph

open Function

universe u

variable {α : Type u} (f : α → α)

/-! ### Repeats -/

variable {f} in
/-- A repeat `f^[i] x = f^[j] x` with `i ≤ j` makes `f^[i] x` periodic with period `j - i`. -/
theorem isPeriodicPt_of_iterate_eq {x : α} {i j : ℕ} (hij : i ≤ j) (heq : f^[i] x = f^[j] x) :
    IsPeriodicPt f (j - i) (f^[i] x) := by
  rw [IsPeriodicPt, IsFixedPt, ← iterate_add_apply, Nat.sub_add_cancel hij, heq]

variable {f} in
/-- After a repeat, every later time can be reduced modulo the repeat interval. -/
theorem iterate_add_mod_sub {x : α} {i j T : ℕ} (hij : i ≤ j) (heq : f^[i] x = f^[j] x)
    (hT : i ≤ T) : f^[i + (T - i) % (j - i)] x = f^[T] x := by
  rw [Nat.add_comm i, iterate_add_apply, (isPeriodicPt_of_iterate_eq hij heq).iterate_mod_apply,
    ← iterate_add_apply, Nat.sub_add_cancel hT]

variable {f} in
/-- After a repeat, two later times that agree modulo the repeat interval give the same state. -/
theorem iterate_eq_iterate_of_mod_eq {x : α} {i j r T : ℕ} (hij : i ≤ j)
    (heq : f^[i] x = f^[j] x) (hr : i ≤ r) (hT : i ≤ T) (hmod : r % (j - i) = T % (j - i)) :
    f^[r] x = f^[T] x := by
  have hsub : (r - i) % (j - i) = (T - i) % (j - i) :=
    Nat.ModEq.add_right_cancel' i (by
      simpa only [Nat.ModEq, Nat.sub_add_cancel hr, Nat.sub_add_cancel hT] using hmod)
  rw [← iterate_add_mod_sub hij heq hr, ← iterate_add_mod_sub hij heq hT, hsub]

/-! ### First visits -/

/-- Every reachable target has a first visit before the number of states. -/
theorem exists_first_visit [Fintype α] (P : α → Prop) (x : α) (h : ∃ t, P (f^[t] x)) :
    ∃ t < Fintype.card α, P (f^[t] x) ∧ ∀ k < t, ¬P (f^[k] x) := by
  classical
  set t := Nat.find h
  have hP : P (f^[t] x) := Nat.find_spec h
  have hmin : ∀ k < t, ¬P (f^[k] x) := fun k hk => Nat.find_min h hk
  have key (a b : ℕ) (hab : a < b) (hbt : b ≤ t) (heq : f^[a] x = f^[b] x) : False := by
    have hr := iterate_add_mod_sub hab.le heq (by omega : a ≤ t)
    have := Nat.mod_lt (t - a) (Nat.sub_pos_of_lt hab)
    exact hmin _ (by omega) (hr ▸ hP)
  have hc : t + 1 ≤ Fintype.card α := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective (fun i : Fin (t + 1) =>
      f^[i.val] x) fun i j he => Fin.ext <| by_contra fun hne =>
        (lt_or_gt_of_ne hne).elim (fun hij => key i j hij (by omega) he)
          fun hji => key j i hji (by omega) he.symm
  exact ⟨t, by omega, hP, hmin⟩

/-- The map that stops at states satisfying `P` and otherwise applies `f`. -/
def absorb (P : α → Prop) [DecidablePred P] (x : α) : α :=
  if P x then x else f x

/-- Before any visit to `P`, the absorbing map agrees with `f`: if no `f^[j] x` with `j < t`
satisfies `P`, then `(absorb f P)^[t] x = f^[t] x`. -/
theorem absorb_iterate_of_forall_not (P : α → Prop) [DecidablePred P] (x : α) (t : ℕ)
    (h : ∀ j < t, ¬P (f^[j] x)) : (absorb f P)^[t] x = f^[t] x := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ih fun j hj => h j (by omega)]
    simp [absorb, h t (by omega)]

/-- The absorbing map fixes every state satisfying `P`, under any number of iterations. -/
theorem absorb_iterate_of_pos (P : α → Prop) [DecidablePred P] {x : α} (hx : P x) (t : ℕ) :
    (absorb f P)^[t] x = x := by
  induction t with
  | zero => rfl
  | succ t ih => simp [iterate_succ_apply', ih, absorb, hx]

/-- After the first visit at time `t`, the absorbing map stays at the target. -/
theorem absorb_iterate_of_first_visit (P : α → Prop) [DecidablePred P] (x : α) {t T : ℕ}
    (ht : P (f^[t] x)) (hfirst : ∀ j < t, ¬P (f^[j] x)) (hle : t ≤ T) :
    (absorb f P)^[T] x = f^[t] x := by
  rw [show T = (T - t) + t by omega, iterate_add_apply,
    absorb_iterate_of_forall_not f P x t hfirst, absorb_iterate_of_pos f P ht]

/-- Iterating the absorbing map as many times as there are states returns the first visit. -/
theorem absorb_iterate_card [Fintype α] (P : α → Prop) [DecidablePred P] (x : α)
    (h : ∃ t, P (f^[t] x)) :
    ∃ t < Fintype.card α, P (f^[t] x) ∧ (∀ j < t, ¬P (f^[j] x)) ∧
      (absorb f P)^[Fintype.card α] x = f^[t] x :=
  let ⟨t, ht, hp, hfirst⟩ := exists_first_visit f P x h
  ⟨t, ht, hp, hfirst, absorb_iterate_of_first_visit f P x hp hfirst ht.le⟩

/-- The absorbing map decides reachability after as many steps as there are states. -/
theorem absorb_iterate_card_eq_iff [Fintype α] (P : α → Prop) [DecidablePred P] (x : α) :
    P ((absorb f P)^[Fintype.card α] x) ↔ ∃ t, P (f^[t] x) :=
  ⟨fun hp => by_contra fun h =>
      h ⟨_, absorb_iterate_of_forall_not f P x _ (fun j _ hj => h ⟨j, hj⟩) ▸ hp⟩,
    fun h => let ⟨_, _, ht, _, he⟩ := absorb_iterate_card f P x h; he.symm ▸ ht⟩

/-! ### Transient depth and cycle length -/

section Finite

variable [Finite α]

/-- Every orbit of a map on a finite type reaches a periodic point. -/
theorem exists_iterate_mem_periodicPts (x : α) : ∃ t, f^[t] x ∈ periodicPts f :=
  let ⟨i, j, he, hne⟩ := not_injective_iff.mp (not_injective_infinite_finite fun i : ℕ => f^[i] x)
  (lt_or_gt_of_ne hne).elim
    (fun h => ⟨i, mk_mem_periodicPts (by omega) (isPeriodicPt_of_iterate_eq h.le he)⟩)
    fun h => ⟨j, mk_mem_periodicPts (by omega) (isPeriodicPt_of_iterate_eq h.le he.symm)⟩

open scoped Classical in
/-- The transient depth of `x`: the first time its orbit is periodic. -/
noncomputable def transientDepth (x : α) : ℕ :=
  Nat.find (exists_iterate_mem_periodicPts f x)

/-- The orbit of `x` is at a periodic point at its transient depth. -/
theorem iterate_transientDepth_mem_periodicPts (x : α) :
    f^[transientDepth f x] x ∈ periodicPts f := by
  classical
  exact Nat.find_spec (exists_iterate_mem_periodicPts f x)

/-- Periodicity begins exactly at the transient depth. -/
theorem iterate_mem_periodicPts_iff (x : α) (t : ℕ) :
    f^[t] x ∈ periodicPts f ↔ transientDepth f x ≤ t := by
  classical
  refine ⟨Nat.find_min' (exists_iterate_mem_periodicPts f x), fun ht => ?_⟩
  obtain ⟨p, hp, hperiod⟩ := mem_periodicPts.mp (iterate_transientDepth_mem_periodicPts f x)
  have h := mk_mem_periodicPts hp (hperiod.apply_iterate (t - transientDepth f x))
  rwa [← iterate_add_apply, Nat.sub_add_cancel ht] at h

/-- The transient depth of `x` is zero exactly when `x` is periodic. -/
@[simp] theorem transientDepth_eq_zero_iff (x : α) :
    transientDepth f x = 0 ↔ x ∈ periodicPts f := by
  simpa using (iterate_mem_periodicPts_iff f x 0).symm

/-- For a periodic state, the transient depth is zero. -/
theorem transientDepth_eq_zero_of_mem_periodicPts {x : α} (hx : x ∈ periodicPts f) :
    transientDepth f x = 0 :=
  (transientDepth_eq_zero_iff f x).mpr hx

/-- The transient depth is less than the number of states. -/
theorem transientDepth_lt_card [Fintype α] (x : α) : transientDepth f x < Fintype.card α :=
  let ⟨t, ht, hp, _⟩ := exists_first_visit f (· ∈ periodicPts f) x
    (exists_iterate_mem_periodicPts f x)
  ((iterate_mem_periodicPts_iff f x t).mp hp).trans_lt ht

/-- Advancing `t` steps lowers the transient depth by `t`, truncated at zero. -/
@[simp] theorem transientDepth_iterate (x : α) (t : ℕ) :
    transientDepth f (f^[t] x) = transientDepth f x - t := by
  have h := iterate_transientDepth_mem_periodicPts f (f^[t] x)
  rw [← iterate_add_apply, iterate_mem_periodicPts_iff] at h
  have hle : transientDepth f (f^[t] x) ≤ transientDepth f x - t :=
    (iterate_mem_periodicPts_iff f (f^[t] x) _).mp <| by
      rw [← iterate_add_apply, iterate_mem_periodicPts_iff]; omega
  omega

/-- The cycle length of `x`: the minimal period of its eventual cycle. -/
noncomputable def cycleLength (x : α) : ℕ :=
  minimalPeriod f (f^[transientDepth f x] x)

/-- For a periodic state, the cycle length is the minimal period. -/
theorem cycleLength_eq_minimalPeriod_of_mem_periodicPts {x : α} (hx : x ∈ periodicPts f) :
    cycleLength f x = minimalPeriod f x := by
  simp [cycleLength, transientDepth_eq_zero_of_mem_periodicPts f hx]

/-- The cycle length is positive. -/
theorem cycleLength_pos (x : α) : 0 < cycleLength f x :=
  minimalPeriod_pos_of_mem_periodicPts (iterate_transientDepth_mem_periodicPts f x)

/-- The state at the transient depth is periodic with period the cycle length. -/
theorem isPeriodicPt_cycleLength (x : α) :
    IsPeriodicPt f (cycleLength f x) (f^[transientDepth f x] x) :=
  isPeriodicPt_minimalPeriod _ _

/-- Past the transient, every state has the cycle length as exact period. -/
theorem minimalPeriod_iterate (x : α) {a : ℕ} (ha : transientDepth f x ≤ a) :
    minimalPeriod f (f^[a] x) = cycleLength f x := by
  have h := minimalPeriod_apply_iterate (iterate_transientDepth_mem_periodicPts f x)
    (a - transientDepth f x)
  rwa [← iterate_add_apply, Nat.sub_add_cancel ha] at h

/-- Two times give the same state exactly when the earlier is past the transient and their
difference is a multiple of the cycle length. -/
theorem iterate_apply_eq_iterate_apply_iff (x : α) {a b : ℕ} (hab : a < b) :
    f^[a] x = f^[b] x ↔ transientDepth f x ≤ a ∧ cycleLength f x ∣ b - a :=
  ⟨fun he =>
      let hper := isPeriodicPt_of_iterate_eq hab.le he
      let ha := (iterate_mem_periodicPts_iff f x a).mp (mk_mem_periodicPts (by omega) hper)
      ⟨ha, minimalPeriod_iterate f x ha ▸ hper.minimalPeriod_dvd⟩,
    fun ⟨ha, hd⟩ => by
      have hp : IsPeriodicPt f (b - a) (f^[a] x) :=
        isPeriodicPt_iff_minimalPeriod_dvd.mpr (minimalPeriod_iterate f x ha ▸ hd)
      rw [← hp.eq, ← iterate_add_apply, Nat.sub_add_cancel hab.le]⟩

/-- The transient and one complete cycle contain no repeated state. -/
theorem orbit_prefix_injective (x : α) :
    Injective (fun i : Fin (transientDepth f x + cycleLength f x) => f^[i.val] x) := by
  have key (a b : ℕ) (hab : a < b) (hb : b < transientDepth f x + cycleLength f x)
      (he : f^[a] x = f^[b] x) : False := by
    obtain ⟨_, hd⟩ := (iterate_apply_eq_iterate_apply_iff f x hab).mp he
    have := Nat.le_of_dvd (by omega) hd; omega
  exact fun i j he => Fin.ext <| by_contra fun hne =>
    (lt_or_gt_of_ne hne).elim (fun h => key i j h j.isLt he) fun h => key j i h i.isLt he.symm

/-- The transient depth plus the cycle length is at most the number of states. -/
theorem transientDepth_add_cycleLength_le_card [Fintype α] (x : α) :
    transientDepth f x + cycleLength f x ≤ Fintype.card α := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ (orbit_prefix_injective f x)

/-- A repeat within a prefix bounds the transient depth plus the cycle length. -/
theorem transientDepth_add_cycleLength_le_of_iterate_eq (x : α) {i j : ℕ} (hij : i < j)
    (he : f^[i] x = f^[j] x) : transientDepth f x + cycleLength f x ≤ j := by
  obtain ⟨_, hd⟩ := (iterate_apply_eq_iterate_apply_iff f x hij).mp he
  have := Nat.le_of_dvd (by omega) hd; omega

/-- A transient target can only be reached at the difference of the transient depths. -/
theorem exists_iterate_eq_iff_of_not_mem_periodicPts (x y : α) (hy : y ∉ periodicPts f) :
    (∃ t, f^[t] x = y) ↔
      transientDepth f y ≤ transientDepth f x ∧
        f^[transientDepth f x - transientDepth f y] x = y := by
  have hpos : 0 < transientDepth f y :=
    Nat.pos_of_ne_zero ((transientDepth_eq_zero_iff f y).not.mpr hy)
  exact ⟨fun ⟨t, ht⟩ => by
      subst ht
      rw [transientDepth_iterate] at hpos ⊢
      exact ⟨Nat.sub_le _ _, by congr 1; omega⟩,
    fun ⟨_, ht⟩ => ⟨_, ht⟩⟩

end Finite

end Cslib.FunctionalGraph
