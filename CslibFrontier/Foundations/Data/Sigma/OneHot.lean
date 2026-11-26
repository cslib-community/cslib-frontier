/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, beside `Mathlib.Data.Sigma.Basic`)

public import CslibFrontier.Init
public import Mathlib.Data.Sigma.Basic
import Mathlib.Tactic.Common

/-!
# One-hot encodings of dependent functions

The one-hot encoding of a function `g : ∀ d, E d` is the family of bits indexed by the pairs
`⟨d, e⟩`, with bit `⟨d, e⟩` set exactly when `g d = e` (`Pi.oneHot`). It is injective
(`Pi.oneHot_injective`), and its range consists of the families with exactly one set bit over
each point (`Pi.exists_oneHot_eq_iff`).

## Main definitions

* `Pi.oneHot`.

## Main results

* `Pi.oneHot_injective`, `Pi.exists_oneHot_eq_iff`.
-/

public section

namespace Pi

variable {D : Type*} {E : D → Type*} [∀ d, DecidableEq (E d)]

/-- The one-hot encoding of `g`: the bit at `⟨d, e⟩` is set exactly when `g d = e`. -/
@[expose] def oneHot (g : ∀ d, E d) (p : Σ d, E d) : Bool := decide (g p.1 = p.2)

@[simp] theorem oneHot_apply (g : ∀ d, E d) (d : D) (e : E d) :
    oneHot g ⟨d, e⟩ = decide (g d = e) := rfl

theorem oneHot_injective : Function.Injective (oneHot (E := E)) := by
  intro g g' h
  refine funext fun d => Eq.symm ?_
  simpa only [oneHot_apply, decide_true, decide_eq_true_eq] using (congrFun h ⟨d, g d⟩).symm

/-- A family of bits is a one-hot encoding exactly when every point has one set bit. -/
theorem exists_oneHot_eq_iff (a : (Σ d, E d) → Bool) :
    (∃ g, oneHot g = a) ↔ ∀ d, ∃! e, a ⟨d, e⟩ = true := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨g, rfl⟩ d
    exact ⟨g d, by simp, fun e he => by simpa [eq_comm] using he⟩
  · choose g hg hu using h
    refine ⟨g, funext fun ⟨d, e⟩ => ?_⟩
    rw [oneHot_apply]
    cases he : a ⟨d, e⟩
    · exact decide_eq_false fun h' => Bool.false_ne_true (he.symm.trans (h' ▸ hg d))
    · exact decide_eq_true (hu d e he).symm

end Pi
