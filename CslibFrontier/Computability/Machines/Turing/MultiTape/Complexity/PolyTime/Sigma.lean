/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sigma
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Sigma
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds

/-!
# Polynomial-time views of dependent pairs

The polynomial-time forms of the degree-one views in
`CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Sigma`: a dependent
pair under a uniform family `enc i = e ∘ code i` read as the plain pair of its index and code
(`sigmaView`), after which the pair projections read either part, and the index under any family
(`sigmaFst`).

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.sigmaView`: a dependent pair as the plain pair of its
  index and code.
* `Turing.MultiTapeTM.ComputableInPolyTime.sigmaFst`: the index of a dependent pair.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {ι γ : Type} {β : ι → Type} {enc : ∀ i, β i ↪ List Bool}

/-- Read a dependent pair, encoded by a uniform family `enc i = e ∘ code i`, as the plain pair of
its index and code. The encoded words are the same. -/
theorem sigmaView (encI : ι ↪ List Bool) (e : γ ↪ List Bool) (code : ∀ i, β i → γ)
    (h : ∀ i b, enc i b = e (code i b)) :
    ComputableInPolyTime (fun x : Σ i, β i => (x.1, code x.1 x.2)) (encSigma encI enc)
      (encPair encI e) :=
  (ComputableInDegree.sigmaView encI e code h).computableInPolyTime

/-- The index of a dependent pair, under any family of encodings. -/
@[fun_prop]
theorem sigmaFst (encI : ι ↪ List Bool) (enc : ∀ i, β i ↪ List Bool) :
    ComputableInPolyTime (Sigma.fst (β := β)) (encSigma encI enc) encI :=
  (ComputableInDegree.sigmaFst encI enc).computableInPolyTime

end Turing.MultiTapeTM.ComputableInPolyTime
