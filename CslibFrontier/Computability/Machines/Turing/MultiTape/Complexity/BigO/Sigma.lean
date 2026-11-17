/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sigma
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp

/-!
# Linear views of dependent pairs

An `encSigma` word under a uniform family `enc₂ a = e ∘ code a` is the `encPair` word of the plain
pair `(a, code a b)`, so reading it as that pair copies the input (`sigmaView_deg`), and the pair
projections then read the first component and the code. The first component can be read under any
family (`sigmaFst_deg`).

## Main results

* `Turing.MultiTapeTM.ComputableInO.sigmaView_deg`: a dependent pair as the plain pair of its first
  component and code.
* `Turing.MultiTapeTM.ComputableInO.sigmaFst_deg`: the first component of a dependent pair.
-/

public section

namespace Turing.MultiTapeTM.ComputableInO

variable {α γ : Type} {β : α → Type} {enc₂ : ∀ a, β a ↪ List Bool}

/-- Read a dependent pair, encoded by a uniform family `enc₂ a = e ∘ code a`, as the plain pair of
its first component and code. The encoded words are the same. -/
theorem sigmaView_deg (enc₁ : α ↪ List Bool) (e : γ ↪ List Bool) (code : ∀ a, β a → γ)
    (h : ∀ a b, enc₂ a b = e (code a b)) :
    ComputableInDegree (fun x : (a : α) × β a => (x.1, code x.1 x.2)) (encSigma enc₁ enc₂)
      (encPair enc₁ e) 1 1 :=
  .of_eq fun x => (encSigma_eq_encPair e code h x).symm

/-- The first component of a dependent pair, under any family of encodings, takes linear time. -/
@[fun_prop]
theorem sigmaFst_deg (enc₁ : α ↪ List Bool) (enc₂ : ∀ a, β a ↪ List Bool) :
    ComputableInDegree (Sigma.fst (β := β)) (encSigma enc₁ enc₂) enc₁ 1 1 :=
  (sigmaView_deg enc₁ encBits (fun a => enc₂ a) fun _ _ => rfl).fst'

end Turing.MultiTapeTM.ComputableInO
