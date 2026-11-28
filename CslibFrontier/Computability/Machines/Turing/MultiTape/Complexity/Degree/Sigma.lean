/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sigma
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Primitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreePrimitives

/-!
# Degree-one views of dependent pairs

An `encSigma` word under a uniform family `enc i = e ∘ code i` is the `encPair` word of the plain
pair `(i, code i b)`, so reading it as that pair copies the input (`sigmaView`), and the pair
projections then read the index and the code. The index can be read under any family
(`sigmaFst`).

## Main results

* `Turing.MultiTapeTM.ComputableInDegree.sigmaView`: a dependent pair as the plain pair of its index
  and code.
* `Turing.MultiTapeTM.ComputableInDegree.sigmaFst`: the index of a dependent pair.
-/

public section

namespace Turing.MultiTapeTM.ComputableInDegree

variable {ι γ : Type} {β : ι → Type} {enc : ∀ i, β i ↪ List Bool}

/-- Read a dependent pair, encoded by a uniform family `enc i = e ∘ code i`, as the plain pair of
its index and code. The encoded words are the same. -/
theorem sigmaView (encI : ι ↪ List Bool) (e : γ ↪ List Bool) (code : ∀ i, β i → γ)
    (h : ∀ i b, enc i b = e (code i b)) :
    ComputableInDegree (fun x : Σ i, β i => (x.1, code x.1 x.2)) (encSigma encI enc)
      (encPair encI e) 1 1 :=
  .of_eq fun x => (encSigma_eq_encPair e code h x).symm

/-- The index of a dependent pair, under any family of encodings, has degree one. -/
@[fun_prop]
theorem sigmaFst (encI : ι ↪ List Bool) (enc : ∀ i, β i ↪ List Bool) :
    ComputableInDegree (Sigma.fst (β := β)) (encSigma encI enc) encI 1 1 :=
  (sigmaView encI encBits (fun i => enc i) fun _ _ => rfl).fst'

end Turing.MultiTapeTM.ComputableInDegree
