/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Logic.Relation

/-!
# Reconfiguration of words over a fixed digraph

An `H`-word is a directed walk in the fixed finite digraph `H`. A move changes one position
and preserves this condition, including at the two endpoints.

## Main definitions

* `HWord.Legal`: adjacent positions carry adjacent symbols of `H`.
* `HWord.Step`, `HWord.Reachable`: single-position moves and finite reconfiguration paths.

## Main results

* `HWord.reachable_of_eq_off`: two legal words agreeing away from one position are reachable.

## References

* [M. Wrochna, *Reconfiguration in bounded bandwidth and treedepth*][Wrochna2014], Section 3.
* [T. C. van der Zanden, *Parameterized Complexity of Graph Constraint Logic*]
  [VanDerZanden2015], Definition 2.
-/

public section

namespace Cslib.Complexity.NCL.HWord

variable {q n : ℕ} (H : Digraph (Fin q))

/-- A word whose consecutive symbols follow the fixed directed compatibility relation. -/
@[expose] def Legal (s : Fin n → Fin q) : Prop :=
  ∀ i j, i.val + 1 = j.val → H.Adj (s i) (s j)

instance [DecidableRel H.Adj] (s : Fin n → Fin q) : Decidable (Legal H s) :=
  inferInstanceAs (Decidable (∀ i j, i.val + 1 = j.val → H.Adj (s i) (s j)))

/-- Change exactly one position while preserving compatibility. -/
@[expose] def Step (s t : Fin n → Fin q) : Prop :=
  Legal H s ∧ Legal H t ∧ ∃ i, s i ≠ t i ∧ ∀ j, j ≠ i → s j = t j

theorem Step.legal_left {s t : Fin n → Fin q} (h : Step H s t) : Legal H s := h.1

theorem Step.legal_right {s t : Fin n → Fin q} (h : Step H s t) : Legal H t := h.2.1

instance : Std.Symm (Step H (n := n)) where
  symm s t h := by
    obtain ⟨hs, ht, i, hi, he⟩ := h
    exact ⟨ht, hs, i, hi.symm, fun j hj => (he j hj).symm⟩

/-- Any finite sequence of legal single-position changes. -/
abbrev Reachable := Relation.ReflTransGen (Step H (n := n))

variable {H} {s t : Fin n → Fin q}

/-- A path starting at a legal word ends at a legal word, including a zero-step path. -/
theorem Reachable.legal (hr : Reachable H s t) (hs : Legal H s) : Legal H t := by
  induction hr with
  | refl => exact hs
  | tail _ h _ => exact h.2.1

/-- Two legal words differing at most at one specified position are reachable. -/
theorem reachable_of_eq_off (hs : Legal H s) (ht : Legal H t) (i : Fin n)
    (heq : ∀ j, j ≠ i → s j = t j) : Reachable H s t := by
  by_cases hi : s i = t i
  · have hst : s = t := funext fun j => if hj : j = i then hj ▸ hi else heq j hj
    exact hst ▸ Relation.ReflTransGen.refl
  · exact .single ⟨hs, ht, i, hi, heq⟩

end Cslib.Complexity.NCL.HWord
