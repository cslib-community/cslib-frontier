/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sigma
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Polynomial-time views of dependent pairs

The polynomial-time forms of the linear views in
`CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sigma`: a dependent pair
under a uniform family `enc₂ a = e ∘ code a` read as the plain pair of its first component and code
(`sigmaView`), after which the pair projections read either part, and the first component under any
family (`sigmaFst`).

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.sigmaView`: a dependent pair as the plain pair of its
  first component and code.
* `Turing.MultiTapeTM.ComputableInPolyTime.sigmaFst`: the first component of a dependent pair.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {α γ : Type} {β : α → Type} {enc₂ : ∀ a, β a ↪ List Bool}

/-- Read a dependent pair, encoded by a uniform family `enc₂ a = e ∘ code a`, as the plain pair of
its first component and code. The encoded words are the same. -/
theorem sigmaView (enc₁ : α ↪ List Bool) (e : γ ↪ List Bool) (code : ∀ a, β a → γ)
    (h : ∀ a b, enc₂ a b = e (code a b)) :
    ComputableInPolyTime (fun x : (a : α) × β a => (x.1, code x.1 x.2)) (encSigma enc₁ enc₂)
      (encPair enc₁ e) :=
  (ComputableInO.sigmaView_deg enc₁ e code h).computableInPolyTime

/-- The first component of a dependent pair, under any family of encodings. -/
@[fun_prop]
theorem sigmaFst (enc₁ : α ↪ List Bool) (enc₂ : ∀ a, β a ↪ List Bool) :
    ComputableInPolyTime (Sigma.fst (β := β)) (encSigma enc₁ enc₂) enc₁ :=
  (ComputableInO.sigmaFst_deg enc₁ enc₂).computableInPolyTime

end Turing.MultiTapeTM.ComputableInPolyTime
