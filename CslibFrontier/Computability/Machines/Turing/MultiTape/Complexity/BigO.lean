/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- vendored: use core's fold homomorphism law for the captured-parameter identity.
-- vendored: retire superseded tidy list combinators; plain rules live in BigO/Lists.

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OLoops
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists

/-!
# Charged bounds up to constants

The plain calculus preserves independent time and charged workspace bounds. `listMax` bounds
round costs over a list. Machine normalization is confined to the internal construction proofs.
-/

namespace Turing.MultiTapeTM

/-- The largest value of `f` on the elements of `l`, or `0`. -/
@[expose] public def listMax {α : Type*} (f : α → ℕ) (l : List α) : ℕ := (l.map f).foldr max 0

public lemma le_listMax {α : Type*} {f : α → ℕ} {l : List α} {a : α} (ha : a ∈ l) :
    f a ≤ listMax f l := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_max_left _ _
    · exact (ih ha).trans (le_max_right _ _)

public lemma listMax_le {α : Type*} {f : α → ℕ} {l : List α} {b : ℕ} (h : ∀ a ∈ l, f a ≤ b) :
    listMax f l ≤ b := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    exact max_le (h a (List.mem_cons_self ..)) (ih fun a ha => h a (List.mem_cons_of_mem _ ha))

end Turing.MultiTapeTM
