/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.Sort.LEQuery.Fooling
import Mathlib.SetTheory.Cardinal.Order

/-!
# Realizing an adaptive comparison adversary

An adversary may change its current linear order when a program asks a new query, provided it
keeps every answer already given. One linear order then realizes the whole run and its transcript
satisfies the adversary's invariant. This allows comparison lower bounds to reason about a single
query at a time.
-/

public section

namespace Cslib.Query

open Classical in
/-- If an invariant of a linear order and its transcript can be maintained by answering any next
query consistently with the earlier answers, it holds on a run against a single linear order. -/
theorem LEQuery.exists_adversary_run {α γ : Type} (p : FreeM (LEQuery α) γ)
    (Inv : (α → α → Prop) → List (α × α) → Prop)
    (initial : ∀ r, IsLinearOrder α r → Inv r [])
    (step : ∀ r, IsLinearOrder α r → ∀ T, Inv r T → ∀ a b,
      ∃ s, IsLinearOrder α s ∧ AgreeOn r s T ∧ Inv s (T ++ [(a, b)])) :
    ∃ f : α → α → Bool, IsLinearOrder α (fun a b => f a b = true) ∧
      Inv (fun a b => f a b = true) (LEQuery.queriedPairs (LEQuery.oracleOf f) p) := by
  suffices go : ∀ (q : FreeM (LEQuery α) γ) T r, IsLinearOrder α r → Inv r T →
      ∃ s, IsLinearOrder α s ∧ AgreeOn r s T ∧ Inv s (T ++ LEQuery.queriedPairs
        (LEQuery.oracleOf fun a b => decide (s a b)) q) by
    let := (exists_wellFoundedLT α).choose
    obtain ⟨s, hs, -, h⟩ := go p [] (· ≤ ·) inferInstance (initial _ inferInstance)
    let f a b := decide (s a b)
    have hf : (fun a b => f a b = true) = s := by funext a b; simp [f]
    refine ⟨f, hf.symm ▸ hs, ?_⟩
    rw [hf]
    simpa using h
  intro q
  induction q with
  | pure x => exact fun T r hr hT => ⟨r, hr, AgreeOn.refl r T, by simpa using hT⟩
  | lift_bind op cont ih =>
    cases op with
    | le a b =>
      intro T r hr hT
      obtain ⟨s, hs, hkeep, hstep⟩ := step r hr T hT a b
      obtain ⟨u, hu, hfinal, hrun⟩ := ih (decide (s a b)) _ _ hs hstep
      refine ⟨u, hu, hkeep.trans (hfinal.mono fun _ h => List.mem_append_left _ h), ?_⟩
      have hans : decide (u a b) = decide (s a b) := decide_eq_decide.mpr
        (hfinal.iff (List.mem_append_right _ (List.mem_singleton_self _))).symm
      rw [FreeM.bind_eq_bind, LEQuery.queriedPairs_liftBind, LEQuery.oracleOf_le, hans]
      simpa only [List.append_assoc, List.singleton_append] using hrun

end Cslib.Query
