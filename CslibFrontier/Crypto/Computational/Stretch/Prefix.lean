/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Stretch
import CslibFrontier.Probability.PMF.Map

/-!
# Prefixes of the emitted PRG stream

`forwardIterate` appends a reversed final seed after its emitted bits. Under the global one-bit
expansion promise, taking exactly the number of rounds discards that seed. These emitted prefixes
have exact length and agree across different stopping times. The complete `forwardIterate` output
is not claimed to be prefix-consistent.

## Main results

* `PRGStretch.length_take_forwardIterate`: exactly one emitted bit per round.
* `PRGStretch.take_forwardIterate_prefix`: increasing the round count preserves emitted prefixes.
* `PRGStretch.polyTime_take_forwardIterate`: native computation on a seed and unary round count.
* `PRGStretch.indistinguishable_take_forwardIterate`: any native polynomial-length emitted prefix
  is computationally indistinguishable from a uniform word of that length.
* `PRGStretch.take_forwardIterate_eq_flatten_emitBit`: the emitted prefix is the sequence of last
  bits `σ₁ ⋯ σ_count` of Goldreich's Construction 8.7.
* `PRGStretch.pseudorandomGenerator_take_forwardIterate`: that construction is a pseudorandom
  generator of every efficiently computed stretch ([Goldreich2007DraftR4], Proposition 8.8).

## References

These are consequences of the existing stretch construction and security theorem. The emitted
prefix is the pad used by the stream-cipher construction in [BonehShoup2023], Section 3.2,
Theorem 3.1, printed pp. 48–51. This module supplies the prefix prerequisite, not a cipher-security
theorem or a message-domain extension.

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, March 2007 draft
  `r4.pdf`][Goldreich2007DraftR4], Construction 8.7 and Proposition 8.8 (printed p. 328,
  PDF p. 64).
-/

public section

namespace Cslib.Crypto.PRGStretch

open Probability BitString Turing.MultiTapeTM

/-- Taking the emitted portion discards the final seed, including at zero seed width or rounds. -/
theorem length_take_forwardIterate {generator : List Bool → List Bool}
    (hlen : ∀ s, (generator s).length = s.length + 1) (seed : List Bool) (count : ℕ) :
    ((forwardIterate generator count seed).take count).length = count := by
  rw [List.length_take, length_forwardIterate_of_forall hlen]
  exact Nat.min_eq_left (by omega)

private theorem length_emitted {generator : List Bool → List Bool}
    (hlen : ∀ s, (generator s).length = s.length + 1) (seed : List Bool) (count : ℕ) :
    (((List.range count).map fun i => emitBit generator (seedAt generator seed i)).flatten).length =
      count := by
  have hbit (s : List Bool) : (emitBit generator s).length = 1 :=
    length_emitBit_of_eq (fun t ht => by rw [hlen, ht]) rfl
  simp [List.length_flatten, List.map_map, Function.comp_def, hbit]

/-- The emitted prefix is the output `σ₁ σ₂ ⋯ σ_count` of [Goldreich2007DraftR4], Construction 8.7
(Eq. (8.8)): starting from `x₀ = seed`, `σᵢ₊₁` is the last bit of `generator xᵢ` (`emitBit`) and
`xᵢ₊₁` is the rest of that output (`seedStep`, so `xᵢ = seedAt generator seed i`). -/
theorem take_forwardIterate_eq_flatten_emitBit {generator : List Bool → List Bool}
    (hlen : ∀ s, (generator s).length = s.length + 1) (seed : List Bool) (count : ℕ) :
    (forwardIterate generator count seed).take count =
      ((List.range count).map fun i => emitBit generator (seedAt generator seed i)).flatten := by
  rw [forwardIterate_eq]
  exact List.take_left' (length_emitted hlen seed count)

/-- Only the emitted prefix is consistent across stopping times; the final seed is excluded. -/
theorem take_forwardIterate_prefix {generator : List Bool → List Bool}
    (hlen : ∀ s, (generator s).length = s.length + 1) (seed : List Bool)
    {count total : ℕ} (hle : count ≤ total) :
    (forwardIterate generator total seed).take count =
      (forwardIterate generator count seed).take count := by
  rw [take_forwardIterate_eq_flatten_emitBit hlen, forwardIterate_eq]
  rw [show total = count + (total - count) by omega, List.range_add,
    List.map_append, List.flatten_append, List.append_assoc]
  exact List.take_left' (length_emitted hlen seed count)

/-- The number of rounds is supplied in unary independently of the seed width. -/
@[fun_prop]
theorem polyTime_take_forwardIterate {generator : List Bool → List Bool}
    (hgenerator : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = s.length + 1) :
    ComputableInPolyTime
      (fun p : List Bool × ℕ => (forwardIterate generator p.2 p.1).take p.2)
      (encPair encBits encUnary) encBits := by
  have hi : ComputableInPolyTime
      (fun p : List Bool × ℕ => iterate generator p.1.length p.2 p.1)
      (encPair encBits encUnary) encBits :=
    polyTime_iterate (hgenerator.comp (ComputableInPolyTime.snd _ _))
      (by fun_prop) (by fun_prop) (by fun_prop)
  have heq (seed : List Bool) (count : ℕ) :
      forwardIterate generator count seed = (iterate generator seed.length count seed).reverse := by
    rw [← reverse_forwardIterate_eq_iterate_of_forall hlen, List.reverse_reverse]
  simp_rw [heq]
  fun_prop

/-- Polynomially many emitted bits are pseudorandom at the original seed/security parameter.
The length schedule is uniform and may be zero; no new generator-security notion is used. -/
theorem indistinguishable_take_forwardIterate {generator : List Bool → List Bool}
    (hgenerator : PseudorandomGenerator generator (fun n => n + 1)) {count : ℕ → ℕ}
    (hcount : ComputableInPolyTime count encUnary encUnary) :
    ComputationallyIndistinguishable
      (fun n => (uniformList n).map
        (fun seed => (forwardIterate generator (count n) seed).take (count n)))
      (fun n => uniformList (count n)) := by
  have h := (indistinguishable hgenerator hcount).map
    (f := fun n word => word.reverse.take (count n)) (by fun_prop)
  convert h using 1
  · funext n
    simp only [generatorEnsemble, PMF.map_comp, Function.comp_def]
    apply PMF.map_congr_on_support
    intro seed hseed
    have hs := length_of_mem_support_uniformList hseed
    simp only [stretch, hs]
    have heq := reverse_forwardIterate_eq_iterate_of_forall hgenerator.length_eq seed (count n)
    rw [hs] at heq
    rw [← heq, List.reverse_reverse]
  · funext n
    symm
    change (uniformList (n + count n)).map ((List.take (count n)) ∘ List.reverse) = _
    rw [← PMF.map_comp,
      uniformList_map_of_bijective List.reverse List.reverse_involutive.bijective
        (fun _ => List.length_reverse), uniformList_take (by omega)]

/-- **Stretch amplification by emitted last bits** ([Goldreich2007DraftR4], Proposition 8.8):
for a pseudorandom generator `generator` of stretch `k + 1` and a stretch function `ℓ`
(`n < ℓ n`) computable in polynomial time in unary, the generator of Construction 8.7, which
outputs the last bits `σ₁ ⋯ σ_ℓ(|s|)` of `ℓ(|s|)` successive expansions of the seed `s`
(`take_forwardIterate_eq_flatten_emitBit`), is a pseudorandom generator of stretch `ℓ`.

`PseudorandomGenerator` asks for one deterministic polynomial-time machine, exact output length
`ℓ(|s|)`, and indistinguishability from uniform for uniform probabilistic polynomial-time tests.
Its tests (`prgRealGame`, `prgIdealGame`) also receive the seed length `n` in unary, while the
tests of Definition 8.1 (Eq. (8.2)) see only the challenge word. This does not change the
implication: on the premise, a challenge-only test recovers `n = |word| - 1` from the one-bit
stretch and can simulate a test that receives `n`; on the conclusion, a test that receives `n`
may ignore it. So the source implication follows even when `ℓ` does not determine the seed
length. The source's "polynomially bounded" stretch follows from computing `ℓ` in unary in
polynomial time. -/
theorem pseudorandomGenerator_take_forwardIterate {generator : List Bool → List Bool}
    (hgenerator : PseudorandomGenerator generator (fun n => n + 1)) {ℓ : ℕ → ℕ}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) (hstretch : ∀ n, n < ℓ n) :
    PseudorandomGenerator
      (fun seed => (forwardIterate generator (ℓ seed.length) seed).take (ℓ seed.length)) ℓ := by
  have hpoly := polyTime_take_forwardIterate hgenerator.polyTime hgenerator.length_eq
  have hinput : ComputableInPolyTime (fun seed : List Bool => (seed, ℓ seed.length))
      encBits (encPair encBits encUnary) := by fun_prop
  refine PseudorandomGenerator.of_indistinguishable (hpoly.comp hinput)
    (fun seed => length_take_forwardIterate hgenerator.length_eq seed _) hstretch ?_
  convert indistinguishable_take_forwardIterate hgenerator hℓ using 1
  funext n
  exact (generatorEnsemble_postprocess id
    (fun n seed => (forwardIterate generator (ℓ n) seed).take (ℓ n)) n).trans
    (by rw [generatorEnsemble, PMF.map_id])

end Cslib.Crypto.PRGStretch
