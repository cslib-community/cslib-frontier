/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Init
import CslibFrontier.Crypto.Computational.DiffieHellman
import CslibFrontier.Tactic.PPT

/-!
# Group-family polynomial-time and PPT tactic automation tests

Checks across a `module` boundary that:
1. Composed `PrimeOrderGroupFamily` word operations (`order`, `encode _ (generator _)`, `add`,
   `smul`) are discharged by `fun_prop`.
2. `PrimeOrderGroupFamily.sampleExp` is automatically found by `ppt` via `@[program_certificate]`
   inside multi-sample `do`-blocks together with word-level group operations.
3. Closed `IsPPTOn` goals binding an encoded sampler `(enc i <$> sample i) >>= k i` discharge via
   `ppt` without simp rewriting `f <$> x >>= g` out of its encoded-output form, including when a
   simplifiable local hypothesis (`id ...`) is rewritten under an unassigned metavariable.
-/

-- This regression module tests tactics and exports no API.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.GroupPPTAutomation

open Cslib Cslib.Probability Cslib.Crypto Turing.MultiTapeTM

section GroupFunProp

variable (F : PrimeOrderGroupFamily)

example :
    ComputableInPolyTime (fun p : ℕ × F.Desc => F.order p.2)
      (encPair encUnary F.encDesc) encNat := by
  fun_prop

example :
    ComputableInPolyTime (fun p : ℕ × F.Desc => F.encode p.2 (F.generator p.2))
      (encPair encUnary F.encDesc) encBits := by
  fun_prop

example :
    ComputableInPolyTime (fun p : F.Desc × List Bool × List Bool => F.add (p.1, p.2.1, p.2.2))
      (encPair F.encDesc (encPair encBits encBits)) encBits := by
  fun_prop

example :
    ComputableInPolyTime (fun p : F.Desc × ℕ × List Bool => F.smul (p.1, p.2.1, p.2.2))
      (encPair F.encDesc (encPair encNat encBits)) encBits := by
  fun_prop

example :
    ComputableInPolyTime
      (fun p : F.Desc × ℕ =>
        F.add (p.1,
          F.smul (p.1, p.2, F.encode p.1 (F.generator p.1)),
          F.smul (p.1, F.order p.1, F.encode p.1 (F.generator p.1))))
      (encPair F.encDesc encNat) encBits := by
  fun_prop

end GroupFunProp

section GroupPPT

variable (F : PrimeOrderGroupFamily)

example :
    IsPPTOn (encPair encUnary F.encDesc) encNat fun input =>
      F.sampleExp input.1 input.2 := by
  ppt

example :
    IsPPTOn (encPair encUnary F.encDesc) encBits fun input => do
      let a ← F.sampleExp input.1 input.2
      let b ← F.sampleExp input.1 input.2
      return F.add (input.2,
        F.smul (input.2, a, F.encode input.2 (F.generator input.2)),
        F.smul (input.2, F.order input.2,
          F.smul (input.2, b, F.encode input.2 (F.generator input.2)))) := by
  ppt

example {I : Type} {C : I → Type} {encIn : I ↪ List Bool}
    (enc : ∀ i, C i ↪ List Bool) (sample : ∀ i, ProbComp (C i))
    (k : I → List Bool → ProbComp (List Bool))
    (hsample : IsPPTOn encIn encBits fun i => enc i <$> sample i)
    (hk : IsPPTOn (encPair encIn encBits) encBits fun p => k p.1 p.2) :
    IsPPTOn encIn encBits fun i => (enc i <$> sample i) >>= k i := by
  ppt

example {I : Type} {C : I → Type} {encIn : I ↪ List Bool}
    (enc : ∀ i, C i ↪ List Bool) (sample : ∀ i, ProbComp (C i))
    (post : I → List Bool → List Bool)
    (hsample : IsPPTOn encIn encBits fun i => enc i <$> sample i)
    (hpost : ComputableInPolyTime (fun p : I × List Bool => post p.1 p.2)
      (encPair encIn encBits) encBits) :
    IsPPTOn encIn encBits fun i => do
      let x ← enc i <$> sample i
      let y ← enc i <$> sample i
      return post i (x ++ y) := by
  ppt

example {I : Type} {C : I → Type} {encIn : I ↪ List Bool}
    (enc : ∀ i, C i ↪ List Bool) (sample : ∀ i, ProbComp (C i))
    (k : I → List Bool → ProbComp (List Bool))
    (hsample : IsPPTOn encIn encBits fun i => id (enc i <$> sample i))
    (hk : IsPPTOn (encPair encIn encBits) encBits fun p => k p.1 p.2) :
    IsPPTOn encIn encBits fun i => (enc i <$> sample i) >>= k i := by
  ppt

end GroupPPT

end CslibFrontierTests.Crypto.GroupPPTAutomation
