/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Tactic.LogSpace
import CslibFrontierTests.LogSpaceCertificates
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Words

/-! # Bounded logspace automation and its resource boundary -/

namespace CslibFrontierTests.LogSpaceTactic

open Turing.MultiTapeTM

-- Existing compositional coverage remains available.
example : ComputableInLogSpace (fun p : List Bool × List Bool => p.2 ++ p.1)
    (encPair encBits encBits) encBits := by
  logspace

-- The constant bound selects a recipe which fun_prop alone does not provide.
example {α : Type} {enc : α ↪ List Bool} {r : α → ℕ} {f : α × ℕ → Bool}
    (k : ℕ) (hr : ComputableInLogSpace r enc encUnary) (hk : ∀ a, r a ≤ k)
    (hf : ComputableInLogSpace f (encPair enc encUnary) encBool) :
    ComputableInLogSpace (fun a => (List.range (r a)).map fun i => f (a, i)) enc encBits := by
  fail_if_success fun_prop
  logspace

-- A callback can itself call a supplied routine on computed arguments.
example {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {r : α → ℕ} {q : α × ℕ → β} {f : β → Bool} (k : ℕ)
    (hr : ComputableInLogSpace r encA encUnary) (hk : ∀ a, r a ≤ k)
    (hq : ComputableInLogSpace q (encPair encA encUnary) encB)
    (hf : ComputableInLogSpace f encB encBool) :
    ComputableInLogSpace (fun a => (List.range (r a)).map fun i => f (q (a, i)))
      encA encBits := by
  logspace

-- Nested bounded construction prepares an evaluator's tuple without a hand-built chain.
example {α : Type} {enc : α ↪ List Bool} {r : α → ℕ}
    {f : α × ℕ → Bool} {d : α × List Bool → Bool} (k : ℕ)
    (hr : ComputableInLogSpace r enc encUnary) (hk : ∀ a, r a ≤ k)
    (hf : ComputableInLogSpace f (encPair enc encUnary) encBool)
    (hd : ComputableInLogSpace d (encPair enc encBits) encBool) :
    ComputableInLogSpace (fun a => d (a, (List.range (r a)).map fun i => f (a, i)))
      enc encBool := by
  logspace

-- A closed instance: three copies of the first input bit, including on the empty word.
example : ComputableInLogSpace
    (fun a : List Bool => (List.range 3).map fun _ => a.headD false) encBits encBits := by
  logspace

-- Framed outputs retain the element encoding, and specialize a count bound to a projection.
example {α β : Type} {enc : α ↪ List Bool} {encOut : β ↪ List Bool}
    {r : α → ℕ} {f : (α × List Bool) × ℕ → β} (k : ℕ)
    (hr : ComputableInLogSpace r enc encUnary) (hk : ∀ a, r a ≤ k)
    (hf : ComputableInLogSpace f (encPair (encPair enc encBits) encUnary) encOut) :
    ComputableInLogSpace
      (fun p : α × List Bool => (List.range (r p.1)).map fun i => f (p, i))
      (encPair enc encBits) (encList encOut) := by
  logspace

-- An input-independent count can be a parameter, and need not be a literal or a local bound.
example {α β : Type} {enc : α ↪ List Bool} {encOut : β ↪ List Bool}
    {f : α × ℕ → β} (k : ℕ)
    (hf : ComputableInLogSpace f (encPair enc encUnary) encOut) :
    ComputableInLogSpace (fun a => (List.range k).map fun i => f (a, i))
      enc (encList encOut) := by
  logspace

-- Shared preparation exposes bundled certificates and local encoding aliases before search.
example {α β : Type} {enc : α ↪ List Bool} {encOut : β ↪ List Bool}
    {r : α → ℕ} {f : α × ℕ → β} (k : ℕ) (hk : ∀ a, r a ≤ k)
    (h : ComputableInLogSpace r enc encUnary ∧
      ComputableInLogSpace f (encPair enc encUnary) encOut) :
    ComputableInLogSpace (fun a => (List.range (r a)).map fun i => f (a, i))
      enc (encList encOut) := by
  let input := enc
  change ComputableInLogSpace _ input _
  let collect (a : α) := (List.range (r a)).map fun i => f (a, i)
  change ComputableInLogSpace collect input _
  logspace [collect]

-- A bound varying with the input cannot be used as a constant, even when stated uniformly.
example {α β : Type} {enc : α ↪ List Bool} {encOut : β ↪ List Bool}
    {r s : α → ℕ} {f : α × ℕ → β} (_hk : ∀ a, r a ≤ s a)
    (_hr : ComputableInLogSpace r enc encUnary)
    (_hf : ComputableInLogSpace f (encPair enc encUnary) encOut)
    (h : ComputableInLogSpace (fun a => (List.range (r a)).map fun i => f (a, i))
      enc (encList encOut)) :
    ComputableInLogSpace (fun a => (List.range (r a)).map fun i => f (a, i))
      enc (encList encOut) := by
  fail_if_success (clear h; logspace)
  exact h

-- Unrelated bounds must not commit search to the wrong count function.
example {α : Type} {enc : α ↪ List Bool} {r s : α → ℕ} {f : α × ℕ → Bool}
    (k j : ℕ) (_hs : ∀ a, s a ≤ j)
    (hr : ComputableInLogSpace r enc encUnary) (hk : ∀ a, r a ≤ k)
    (hf : ComputableInLogSpace f (encPair enc encUnary) encBool) :
    ComputableInLogSpace (fun a => (List.range (r a)).map fun i => f (a, i)) enc encBits := by
  logspace

-- Bounds are essential. Failure leaves the original goal available for an explicit proof.
example {α : Type} {enc : α ↪ List Bool} {r : α → ℕ} {f : α × ℕ → Bool}
    (_hr : ComputableInLogSpace r enc encUnary)
    (_hf : ComputableInLogSpace f (encPair enc encUnary) encBool)
    (h : ComputableInLogSpace (fun a => (List.range (r a)).map fun i => f (a, i)) enc encBits) :
    ComputableInLogSpace (fun a => (List.range (r a)).map fun i => f (a, i)) enc encBits := by
  fail_if_success (clear h; logspace)
  exact h

-- The indexed callback must use unary indices; an unrelated encoding is insufficient.
example {α : Type} {enc : α ↪ List Bool} {indexEncoding : ℕ ↪ List Bool}
    {r : α → ℕ} {f : α × ℕ → Bool} (k : ℕ)
    (_hr : ComputableInLogSpace r enc encUnary) (_hk : ∀ a, r a ≤ k)
    (_hf : ComputableInLogSpace f (encPair enc indexEncoding) encBool)
    (h : ComputableInLogSpace (fun a => (List.range (r a)).map fun i => f (a, i)) enc encBits) :
    ComputableInLogSpace (fun a => (List.range (r a)).map fun i => f (a, i)) enc encBits := by
  fail_if_success (clear h; logspace)
  exact h

-- The existing inclusion remains one-way, even with the tactic imported.
example {f : List Bool → Bool} (_hf : ComputableInPolyTime f encBits encBool)
    (h : ComputableInLogSpace f encBits encBool) :
    ComputableInLogSpace f encBits encBool := by
  fail_if_success (clear h; logspace)
  exact h

example {f : List Bool → Bool} (hf : ComputableInLogSpace f encBits encBool) :
    ComputableInPolyTime (fun p : List Bool × List Bool => f (p.1 ++ p.2))
      (encPair encBits encBits) encBool := by
  fail_if_success logspace
  fun_prop

open CslibFrontierTests.LogSpaceCertificates

-- An imported opaque routine has an eager premise requiring the bounded logspace recipe.
example : ComputableInLogSpace
    (runNamed (fun a : List Bool => (List.range 3).map fun _ => a.headD false))
      encBits encBits := by
  fail_if_success fun_prop
  logspace

-- The imported opaque program really constructs the three first-bit answers, including empty input.
example : runNamed (fun a : List Bool => (List.range 3).map fun _ => a.headD false) [] =
    [false, false, false] := by rw [runNamed_apply]; rfl

example : runNamed (fun a : List Bool => (List.range 3).map fun _ => a.headD false) [true, false] =
    [true, true, true] := by rw [runNamed_apply]; rfl

-- A named certificate also composes inside a larger ordinary functional expression.
example (f : List Bool → List Bool) (hf : ComputableInLogSpace f encBits encBits) :
    ComputableInLogSpace (fun w => (runNamed f w).headD false) encBits encBool := by
  fun_prop

-- Neither an unavailable constant bound nor a polynomial-time callback is inferred.
example {r : List Bool → ℕ} (_hr : ComputableInLogSpace r encBits encUnary)
    (h : ComputableInLogSpace
      (runNamed (fun a => (List.range (r a)).map fun _ => a.headD false)) encBits encBits) :
    ComputableInLogSpace
      (runNamed (fun a => (List.range (r a)).map fun _ => a.headD false)) encBits encBits := by
  fail_if_success (clear h; logspace)
  exact h

example {f : List Bool → List Bool} (_hf : ComputableInPolyTime f encBits encBits)
    (h : ComputableInLogSpace (runNamed f) encBits encBits) :
    ComputableInLogSpace (runNamed f) encBits encBits := by
  fail_if_success (clear h; logspace)
  exact h

example {f : List Bool → List Bool} {other : List Bool ↪ List Bool}
    (_hf : ComputableInLogSpace f other encBits)
    (h : ComputableInLogSpace (runNamed f) encBits encBits) :
    ComputableInLogSpace (runNamed f) encBits encBits := by
  fail_if_success (clear h; logspace)
  exact h

section
attribute [local program_certificate hf] localNamed_logspace

example (f : List Bool → List Bool) (hf : ComputableInLogSpace f encBits encBits) :
    ComputableInLogSpace (localNamed f) encBits encBits := by logspace
end

-- The local registration cannot escape its section.
example {f : List Bool → List Bool} (_hf : ComputableInLogSpace f encBits encBits)
    (h : ComputableInLogSpace (localNamed f) encBits encBits) :
    ComputableInLogSpace (localNamed f) encBits encBits := by
  fail_if_success (clear h; logspace)
  exact h

open scoped CslibFrontierTests.LogSpaceCertificates.Scoped in
example (f : List Bool → List Bool) (hf : ComputableInLogSpace f encBits encBits) :
    ComputableInLogSpace (Scoped.scopedNamed f) encBits encBits := by logspace

-- Opening a scope for one declaration does not change subsequent search.
example {f : List Bool → List Bool} (_hf : ComputableInLogSpace f encBits encBits)
    (h : ComputableInLogSpace (Scoped.scopedNamed f) encBits encBits) :
    ComputableInLogSpace (Scoped.scopedNamed f) encBits encBits := by
  fail_if_success (clear h; logspace)
  exact h

end CslibFrontierTests.LogSpaceTactic
