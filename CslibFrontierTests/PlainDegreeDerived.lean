/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (regression tests)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists

/-! # Ordinary-import clients for independent degree certificates -/

open Turing.MultiTapeTM

assert_not_exists Turing.MultiTapeTM.ComputableTidilyInDegree
assert_not_exists Turing.MultiTapeTM.ComputableTidilyInDegree.foldl'
assert_not_exists Turing.MultiTapeTM.ComputableTidilyInDegree.findWith

-- Composition keeps degree zero instead of silently raising the output degree to one.
example {α β γ : Type} {i : α ↪ List Bool} {m : β ↪ List Bool}
    {o : γ ↪ List Bool} {f : β → γ} {g : α → β}
    (hf : ComputableInDegree f m o 0 0) (hg : ComputableInDegree g i m 0 0) :
    ComputableInDegree (fun a => f (g a)) i o 0 0 := by
  simpa only [Function.comp_def, Nat.mul_zero, max_self] using hf.comp hg

-- A genuine fold client has constant output, independently of its linear resource bound.
example : ComputableInDegree (fun _ : List Bool => false) encBits encBool 1 0 := by
  have h := ComputableInDegree.foldl' (encIn := encBits) (encA := encBool) (encL := encBits)
    (list := fun _ : List Bool => []) (init := fun _ => false) (step := fun b _ => b)
    (ComputableInDegree.const []) (ComputableInDegree.const false)
    (ComputableInDegree.fst encBool encBool) (b := 0) (B := fun _ => 1)
    (DegreeBounded.const 1) (fun _ _ _ => by simp)
  simpa using h

-- The list client composes a migrated operation with an existing projection provider.
example : ComputableInDegree (fun p : (ℕ × Bool) × Bool => List.replicate p.1.1 p.1.2)
    (encPair (encPair encUnary encBool) encBool) (encList encBool) 3 2 := by
  simpa [Function.comp_def] using (ComputableInDegree.replicate encBool).comp
    (ComputableInDegree.fst (encPair encUnary encBool) encBool)

-- A nonempty left fold records the last bit. Reversing traversal changes this result.
example : ComputableInDegree
    (fun _ : List Bool => ([true, false] : List Bool).foldl (fun _ b => b) true)
    encBits encBool 1 0 := by
  have h := ComputableInDegree.foldl' (encIn := encBits) (encA := encBool) (encL := encBits)
    (list := fun _ : List Bool => [true, false]) (init := fun _ => true)
    (step := fun _ b => b)
    (ComputableInDegree.const [true, false]) (ComputableInDegree.const true)
    (ComputableInDegree.snd encBool encBool) (b := 0) (B := fun _ => 1)
    (DegreeBounded.const 1) (fun _ _ _ => by simp)
  simpa using h

example : ([true, false] : List Bool).foldl (fun _ b => b) true = false := rfl
example : ([true, false] : List Bool).reverse.foldl (fun _ b => b) true = true := rfl

-- Ordinary list clients use the first match and preserve the surviving elements' order.
example : ComputableInDegree
    (fun l : List Bool => l.find? fun b => b) (encList encBool) (encOption encBool) 2 1 := by
  simpa using ComputableInDegree.findWith
    (ComputableInDegree.snd encBool encBool) (ComputableInDegree.const false)
    (ComputableInDegree.of_eq (encIn := encList encBool) fun _ => rfl)

example : ComputableInDegree
    (fun l : List Bool => l.filter fun b => b) (encList encBool) (encList encBool) 2 1 := by
  simpa using ComputableInDegree.filterWith
    (ComputableInDegree.snd encBool encBool) (ComputableInDegree.const false)
    (ComputableInDegree.of_eq (encIn := encList encBool) fun _ => rfl)

example : ComputableInDegree
    (fun l : List Bool => l.map fun b => b) (encList encBool) (encList encBool) 3 2 := by
  simpa using ComputableInDegree.mapWith
    (ComputableInDegree.snd encBool encBool)
    ((ComputableInDegree.const false).mono (d' := 1) (e' := 1) (by omega) (by omega))
    (ComputableInDegree.of_eq (encIn := encList encBool) fun _ => rfl)

example : ([false, true, false] : List Bool).find? (fun _ => true) = some false := rfl
example : ([false, true, false] : List Bool).filter (fun _ => true) = [false, true, false] := rfl
example : ([false, true, false] : List Bool).map (fun b => b) = [false, true, false] := rfl
