/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.ComponentBounds

/-! Regression cases for opt-in component bounds, including membership discharge and transport. -/

open Turing.MultiTapeTM

example {α β : Type} (ea : α ↪ List Bool) (eb : β ↪ List Bool)
    (xs : List α) (b : β) (a : α) (ha : a ∈ xs) :
    (ea a).length ≤ (encPair (encList ea) eb (xs, b)).length := by
  have he : (ea a).length ≤ (encList ea xs).length := by
    simp only [enc_component, ha]
  exact he.trans (by simp only [enc_component])

example (xs : List Bool) (i : ℕ) :
    (encBits (xs.drop i)).length ≤ (encBits xs).length := by
  simp only [enc_component]

example {α : Type} (ea : α ↪ List Bool) (xs : List α) :
    xs.length ≤ (encList ea xs).length := by
  simp only [enc_component]

example {Index Value : Type} [Fintype Index] (enc : Value ↪ List Bool)
    (values : Index → Value) (i : Index) :
    (enc (values i)).length ≤ (encPi enc values).length := by
  simp only [enc_component]
