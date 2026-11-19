/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.IID
import Batteries.Data.Fin.Lemmas

/-!
# The first successful IID trial

Map `Fin.findSome?` over a finite tuple of independent `Option`-valued trials. Failure means that
every trial returned `none`, so its mass is the one-trial failure mass raised to the tuple length.

## Main definitions

This module adds no definitions; it composes `PMF.iid` with `Fin.findSome?`.

## Main results

* `Cslib.Probability.PMF.iid_map_findSome` identifies the whole first-answer law with an on-demand
  search through the same number of trials.
* `Cslib.Probability.PMF.map_findSome_iid_apply_none`: exact failure mass of the first-success
  map over IID trials.

## References

The identity is the elementary product rule for independent failures.
-/

public section

namespace Cslib.Probability.PMF

variable {α : Type*}

/-- The first-success map over `K` IID `Option`-valued trials fails with mass `μ none ^ K`. -/
theorem map_findSome_iid_apply_none (μ : PMF (Option α)) (K : ℕ) :
    (iid μ K).map Fin.findSome? none = (μ none) ^ K := by
  rw [PMF.map_apply, tsum_eq_single (fun _ : Fin K => (none : Option α))]
  · rw [ite_eq_left (Fin.findSome?_eq_none_iff.mpr (fun _ => rfl)).symm, iid_apply]
    simp
  · intro attempts hne
    split_ifs with h
    · exact (hne (funext (Fin.findSome?_eq_none_iff.mp h.symm))).elim
    · rfl

/-- Searching an IID tape gives the same first terminal answer as drawing on demand and stopping. -/
theorem iid_map_findSome {α β ι : Type} (p : PMF α) (finish : α → Option β) (xs : List ι) :
    (iid p xs.length).map (fun v => Fin.findSome? fun i => finish (v i)) =
      xs.findSomeM? (fun _ => p.map finish) := by
  induction xs with
  | nil => simp [PMF.iid]
  | cons x xs ih =>
    simp only [List.length_cons, PMF.iid, PMF.monad_bind_eq_bind, PMF.map_bind,
      List.findSomeM?_cons, PMF.bind_map, Function.comp_def, PMF.map_comp]
    apply congrArg (PMF.bind p)
    funext v
    simp only [Fin.findSome?_succ, Fin.cons_zero, Fin.cons_succ]
    cases h : finish v with
    | none => simpa only [Option.none_or] using ih
    | some a => exact PMF.map_const _ (some a)

end Cslib.Probability.PMF
