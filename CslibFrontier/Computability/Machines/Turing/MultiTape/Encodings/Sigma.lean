/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair

/-!
# The framed encoding of dependent pairs

`encSigma encI enc` encodes `⟨i, b⟩ : Σ i, β i` as the framed index `encI i` followed by
`enc i b`, the encoding of the second component chosen by the index. It is the dependent version of
`Turing.MultiTapeTM.encPair`, with the same layout.

A family of encodings is usually *uniform*: each `enc i` is a fixed encoding `e` of a common type
after an index-dependent map `code i`. Then `encSigma encI enc ⟨i, b⟩` is the word of the plain
pair `(i, code i b)` under `encPair encI e` (`encSigma_eq_encPair`), so the polynomial-time
certificates for pairs apply to its view as a pair
(`Turing.MultiTapeTM.ComputableInPolyTime.sigmaView`). Conversely, a plain pair is a dependent
pair with a constant family (`encPair_eq_encSigma`).

The layout is that of `Cslib.Encoding.encSigma` in leanprover/cslib#1213, which frames the index
with `delimit`, the same map as `frame`.

## Main definitions

* `Turing.MultiTapeTM.encSigma`: the framed encoding of dependent pairs.

## Main results

* `Turing.MultiTapeTM.encSigma_eq_encPair`: a uniform family encodes a dependent pair as the plain
  pair of its index and code.
* `Turing.MultiTapeTM.encPair_eq_encSigma`: a plain pair is a dependent pair with a constant family.
-/

namespace Turing.MultiTapeTM

universe u v w

variable {ι : Type u} {β : ι → Type v}

/-- Dependent pairs encoded as the framed index followed by the second component, encoded by the
encoding that the index selects. -/
@[expose] public def encSigma (encI : ι ↪ List Bool) (enc : ∀ i, β i ↪ List Bool) :
    (Σ i, β i) ↪ List Bool :=
  ⟨fun x => frame (encI x.1) ++ enc x.1 x.2, by
    rintro ⟨i, b⟩ ⟨j, b'⟩ h
    obtain ⟨hi, hb⟩ := frame_append_inj h
    obtain rfl : i = j := encI.injective hi
    exact congrArg (Sigma.mk i) ((enc i).injective hb)⟩

variable {encI : ι ↪ List Bool} {enc : ∀ i, β i ↪ List Bool}

@[simp]
public lemma encSigma_apply (x : Σ i, β i) :
    encSigma encI enc x = frame (encI x.1) ++ enc x.1 x.2 :=
  rfl

public lemma length_encSigma (x : Σ i, β i) :
    (encSigma encI enc x).length = 2 * (encI x.1).length + 1 + (enc x.1 x.2).length := by
  simp

public lemma length_le_encSigma_fst (encI : ι ↪ List Bool) (enc : ∀ i, β i ↪ List Bool)
    (x : Σ i, β i) : (encI x.1).length ≤ (encSigma encI enc x).length := by
  rw [length_encSigma]; omega

public lemma length_le_encSigma_snd (encI : ι ↪ List Bool) (enc : ∀ i, β i ↪ List Bool)
    (x : Σ i, β i) : (enc x.1 x.2).length ≤ (encSigma encI enc x).length := by
  rw [length_encSigma]; omega

/-- A uniform family of encodings, `enc i = e ∘ code i`, encodes a dependent pair as the plain pair
of its index and code. -/
public theorem encSigma_eq_encPair {γ : Type w} (e : γ ↪ List Bool) (code : ∀ i, β i → γ)
    (h : ∀ i b, enc i b = e (code i b)) (x : Σ i, β i) :
    encSigma encI enc x = encPair encI e (x.1, code x.1 x.2) := by
  simp [h]

/-- A plain pair is a dependent pair with a constant family of encodings. -/
public theorem encPair_eq_encSigma {γ : Type v} (encI : ι ↪ List Bool) (e : γ ↪ List Bool)
    (p : ι × γ) : encPair encI e p = encSigma encI (fun _ => e) ⟨p.1, p.2⟩ :=
  rfl

end Turing.MultiTapeTM
