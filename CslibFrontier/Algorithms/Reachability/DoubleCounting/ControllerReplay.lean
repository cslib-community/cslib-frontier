/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.DoubleCounting.Controller
public import CslibFrontier.Algorithms.Reachability.DoubleCounting.Scan
import Mathlib.Data.Set.Finite.List

/-!
# Successful typed replays of the double-counting controller

The list semantics records one entry for each successful typed membership replay.
The scan's transcript equivalence makes this list a singleton whenever the current
round has unique shortest walks. The controller can therefore use this callback
without losing multiplicity information about successful replays.

The enumeration is proof-level. It does not provide a native execution or a space bound.
-/

public section

namespace Cslib.DoubleCounting
open Relation

variable {n : ℕ}

private abbrev Successful (edge : Fin n → Fin n → Bool) (s v : Fin n) (k : ℕ) :=
  {b : Scan.Branch n // (Scan.run edge s v k (expected (fun u w => edge u w = true) s k) b).isSome}

private theorem finite_successful (edge : Fin n → Fin n → Bool) (s v : Fin n) (k : ℕ) :
    Finite (Successful edge s v k) := by
  have : Finite {p : List (Fin n) // p.length ≤ k} := (List.finite_length_le _ _).to_subtype
  let embed (b : Successful edge s v k) (u : Fin n) :
      Option {p : List (Fin n) // p.length ≤ k} :=
    (b.val u).pmap Subtype.mk fun p hp => by
      obtain ⟨hit, hh⟩ := Option.isSome_iff_exists.mp b.property
      exact Scan.bounded_of_passes s k b.val
        ((Scan.run_eq_some_iff edge s v k b hit).mp hh).1 u p (Option.mem_def.mp hp)
  refine Finite.of_injective embed fun b₁ b₂ h => Subtype.ext (funext fun u => ?_)
  have he := congrArg (Option.map Subtype.val) (congrFun h u)
  cases h₁ : b₁.val u <;> cases h₂ : b₂.val u <;> simp_all [embed]

/-- List a successful answer once per bounded typed branch at the exact round tally.
Off-contract tallies have no entries. -/
noncomputable def replayMembership (edge : Fin n → Fin n → Bool) (s : Fin n) :
    MembershipScan List n := fun k tally v => by
  classical
  let _ := finite_successful edge s v k
  let _ := Fintype.ofFinite (Successful edge s v k)
  exact if tally = expected (fun u w => edge u w = true) s k then
    (Finset.univ : Finset (Successful edge s v k)).toList.map fun b => (b.val v).isSome
    else []

/-- Each exact round with unique shortest walks gives one typed replay and the correct bit. -/
theorem replayMembership_eq_singleton (edge : Fin n → Fin n → Bool) (s v : Fin n) (k : ℕ)
    (h : ∃! w, Passes (fun u w => edge u w = true) s k w) :
    replayMembership edge s k (expected (fun u w => edge u w = true) s k) v =
      [by classical exact decide (v ∈ round (fun u w => edge u w = true) s k)] := by
  classical
  obtain ⟨branch, hbranch, hunique⟩ := Scan.existsUnique_successful_branch edge s v k h
  let b : Successful edge s v k := ⟨branch, hbranch⟩
  let _ := finite_successful edge s v k
  let _ := Fintype.ofFinite (Successful edge s v k)
  unfold replayMembership
  have huniv : (Finset.univ : Finset (Successful edge s v k)) = {b} := by
    ext x
    have hx : x = b := Subtype.ext (hunique x.val x.property)
    simp [hx]
  rw [ite_eq_left rfl, huniv]
  simp only [Finset.toList_singleton, List.map_singleton, List.cons.injEq, and_true]
  obtain ⟨hit, hhit⟩ := Option.isSome_iff_exists.mp b.property
  have hpass := ((Scan.run_eq_some_iff edge s v k b hit).mp hhit).1
  apply Bool.eq_iff_iff.mpr
  simpa only [Scan.transcript, Option.isSome_map, decide_eq_true_eq, mem_round] using
    isSome_iff (v := v) hpass

/-- The bounded scan instantiates the controller's singleton callback contract in the list
semantics, retaining one successful outcome with multiplicity. -/
theorem runController_replay_correct (edge : Fin n → Fin n → Bool) (s v : Fin n) :
    ∃ verdict,
      runController (m := List) (fun u w => pure (edge u w)) (replayMembership edge s) v =
        [some verdict] ∧
      verdict.Correct (fun u w => edge u w = true) s v := by
  exact runController_correct (r := fun u w => edge u w = true)
    (fun u w => by cases edge u w <;> simp)
    fun k hk target => replayMembership_eq_singleton edge s target k hk

end Cslib.DoubleCounting
