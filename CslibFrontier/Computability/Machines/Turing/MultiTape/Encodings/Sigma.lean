/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate
-- vendored: layout-preserving alias of Cslib.Encoding.encSigma (#1213); views remain local.

public import CslibFrontier.Computability.Encoding.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair

/-!
# The framed encoding of dependent pairs

`encSigma enc₁ enc₂` encodes `⟨a, b⟩ : (a : α) × β a` as the framed first component `enc₁ a`
followed by `enc₂ a b`, the encoding of the second component selected by the first. It is
`Cslib.Encoding.encSigma`, the dependent version of `Turing.MultiTapeTM.encPair`, with the same
layout; a product is the dependent pair with a constant family
(`Cslib.Encoding.encProd_eq_encSigma`).

A family of encodings is usually *uniform*: each `enc₂ a` is a fixed encoding `e` of a common type
after a map `code a` selected by the first component. Then `encSigma enc₁ enc₂ ⟨a, b⟩` is the word
of the plain pair `(a, code a b)` under `encPair enc₁ e` (`encSigma_eq_encPair`), so the
polynomial-time certificates for pairs apply to its view as a pair
(`Turing.MultiTapeTM.ComputableInPolyTime.sigmaView`).

## Main definitions

* `Turing.MultiTapeTM.encSigma`: the framed encoding of dependent pairs.

## Main results

* `Turing.MultiTapeTM.encSigma_eq_encPair`: a uniform family encodes a dependent pair as the plain
  pair of its first component and code.
-/

namespace Turing.MultiTapeTM

universe u v

variable {α : Type u} {β : α → Type v}

/-- Dependent pairs encoded as the framed first component followed by the second component,
encoded by the encoding that the first component selects (`Cslib.Encoding.encSigma`). -/
public abbrev encSigma (enc₁ : α ↪ List Bool) (enc₂ : ∀ a, β a ↪ List Bool) :
    (a : α) × β a ↪ List Bool :=
  Cslib.Encoding.encSigma enc₁ enc₂

variable {enc₁ : α ↪ List Bool} {enc₂ : ∀ a, β a ↪ List Bool}

public lemma length_le_encSigma_fst (enc₁ : α ↪ List Bool) (enc₂ : ∀ a, β a ↪ List Bool)
    (x : (a : α) × β a) : (enc₁ x.1).length ≤ (encSigma enc₁ enc₂ x).length := by
  rw [Cslib.Encoding.length_encSigma]; omega

public lemma length_le_encSigma_snd (enc₁ : α ↪ List Bool) (enc₂ : ∀ a, β a ↪ List Bool)
    (x : (a : α) × β a) : (enc₂ x.1 x.2).length ≤ (encSigma enc₁ enc₂ x).length := by
  rw [Cslib.Encoding.length_encSigma]; omega

/-- A uniform family of encodings, `enc₂ a = e ∘ code a`, encodes a dependent pair as the plain
pair of its first component and code. -/
public theorem encSigma_eq_encPair {γ : Type u} (e : γ ↪ List Bool) (code : ∀ a, β a → γ)
    (h : ∀ a b, enc₂ a b = e (code a b)) (x : (a : α) × β a) :
    encSigma enc₁ enc₂ x = encPair enc₁ e (x.1, code x.1 x.2) := by
  simp [h]

end Turing.MultiTapeTM
