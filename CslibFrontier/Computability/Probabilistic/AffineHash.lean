/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.LinearHash
public import CslibFrontier.Probability.BitString.AffineHash.ThreeWise
public import CslibFrontier.Probability.BitString.AffineHash.Word
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString.Dot
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Probabilistic.Sampling

/-!
# Plain polynomial-time Boolean affine hashing and prefix-collision conditioning

This module certifies `Cslib.BitString.LinearHash.wordAffineHash`,
`Cslib.BitString.LinearHash.wordAdjustAffineSeed` and the zero test
`Cslib.BitString.LinearHash.hashZero` directly in the plain `ComputableInPolyTime`
calculus, together with uniform strict-PPT sampling of prefix-colliding affine seeds.

## Main results

* `Cslib.BitString.LinearHash.computableInPolyTime_wordAffineHash`: plain polynomial-time
  certificate for `wordAffineHash`.
* `Cslib.BitString.LinearHash.computableInPolyTime_wordAdjustAffineSeed`: plain polynomial-time
  certificate for `wordAdjustAffineSeed`.
* `Cslib.BitString.LinearHash.isPPTOn_sampleAdjustedAffineSeed`: uniform strict-PPT sampler
  drawing a fresh `(k * n + k)`-bit affine seed and projecting it onto prefix collisions of `y` and
  `y₀`.
* `Cslib.BitString.LinearHash.computableInPolyTime_hashZero`: plain polynomial-time
  certificate for `hashZero`.

## References

* [I. Haitner, T. Holenstein, O. Reingold, S. Vadhan, H. Wee, *Inaccessible Entropy II: IE
  Functions and Universal One-Way Hashing*, Section 4.2, Theorem 4.5, pp. 21–25][HHRVW2020]
-/

public section

namespace Cslib.BitString.LinearHash

open Cslib.Probability Turing.MultiTapeTM

/-- Evaluate `wordAffineHash` in plain polynomial time, with output dimension supplied in unary. -/
@[fun_prop]
theorem computableInPolyTime_wordAffineHash {α : Type} {encode : α ↪ List Bool}
    {count : α → ℕ} {seed input : α → List Bool}
    (hcount : ComputableInPolyTime count encode encUnary)
    (hseed : ComputableInPolyTime seed encode encBits)
    (hinput : ComputableInPolyTime input encode encBits) :
    ComputableInPolyTime (fun a => wordAffineHash (count a) (seed a) (input a))
      encode encBits := by
  fun_prop [wordAffineHash]

/-- Project an affine seed onto the prefix-collision subgroup in plain polynomial time, with
dimensions `k`, `n`, and `r` supplied in unary. -/
@[fun_prop]
theorem computableInPolyTime_wordAdjustAffineSeed {α : Type} {encode : α ↪ List Bool}
    {k n r : α → ℕ} {y y₀ seed : α → List Bool}
    (hk : ComputableInPolyTime k encode encUnary)
    (hn : ComputableInPolyTime n encode encUnary)
    (hr : ComputableInPolyTime r encode encUnary)
    (hy : ComputableInPolyTime y encode encBits)
    (hy₀ : ComputableInPolyTime y₀ encode encBits)
    (hseed : ComputableInPolyTime seed encode encBits) :
    ComputableInPolyTime
      (fun a => wordAdjustAffineSeed (k a) (n a) (r a) (y a) (y₀ a) (seed a))
      encode encBits := by
  fun_prop [wordAdjustAffineSeed]

/-- Sample a fresh `(k * n + k)`-bit affine seed and project it onto the prefix-collision subgroup
of `y` and `y₀` in uniform strict polynomial time. -/
theorem isPPTOn_sampleAdjustedAffineSeed {α : Type} {encode : α ↪ List Bool}
    {k n r : α → ℕ} {y y₀ : α → List Bool}
    (hk : ComputableInPolyTime k encode encUnary)
    (hn : ComputableInPolyTime n encode encUnary)
    (hr : ComputableInPolyTime r encode encUnary)
    (hy : ComputableInPolyTime y encode encBits)
    (hy₀ : ComputableInPolyTime y₀ encode encBits) :
    IsPPTOn encode encBits (fun a => do
      let rawSeed ← sampleList (k a * n a + k a)
      return wordAdjustAffineSeed (k a) (n a) (r a) (y a) (y₀ a) rawSeed) := by
  have hseedLen : ComputableInPolyTime (fun a => k a * n a + k a) encode encUnary :=
    ComputableInPolyTime.unary_add.comp
      ((ComputableInPolyTime.unary_mul.comp (hk.prod hn)).prod hk)
  have hfst := ComputableInPolyTime.fst encode encBits
  have hsnd := ComputableInPolyTime.snd encode encBits
  have hcallback := computableInPolyTime_wordAdjustAffineSeed
    (hk.comp hfst) (hn.comp hfst) (hr.comp hfst) (hy.comp hfst) (hy₀.comp hfst) hsnd
  simpa only [bind_pure_comp, Function.comp_def] using IsPPTOn.of_seeded hseedLen hcallback

/-- Decide `hashZero` in plain polynomial time, with dimensions `k` and `n` supplied in unary. -/
@[fun_prop]
theorem computableInPolyTime_hashZero {α : Type} {encode : α ↪ List Bool}
    {k n : α → ℕ} {seed x : α → List Bool}
    (hk : ComputableInPolyTime k encode encUnary)
    (hn : ComputableInPolyTime n encode encUnary)
    (hseed : ComputableInPolyTime seed encode encBits)
    (hx : ComputableInPolyTime x encode encBits) :
    ComputableInPolyTime (fun a => hashZero (k a) (n a) (seed a) (x a)) encode encBool := by
  unfold hashZero
  fun_prop

end Cslib.BitString.LinearHash
