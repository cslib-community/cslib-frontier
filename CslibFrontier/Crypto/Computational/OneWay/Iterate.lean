/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.OneWay
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.NthRoot
import CslibFrontier.Probability.PMF.Bind

/-!
# Iterates of a one-way permutation

Applying a one-way permutation `f` to an `n`-bit word `k n` times, for a polynomial-time
computable `k` that is eventually positive, gives a one-way permutation again
([AroraBarak07], Chapter 10, Exercise 3, with `k n = n ^ c`). For a rational exponent
`c = p / q` the count `⌈n ^ c⌉` is polynomial-time computable in unary
(`Turing.MultiTapeTM.ComputableInPolyTime.unary_ceil_rpow`), so the exercise holds for every
rational `c`, and for every other exponent whose rounded count has such a certificate. No uniform
algorithm is claimed for an arbitrary real exponent.

The theorem is asymptotic: uniform strict-PPT inverters and negligible success, rather than the
draft's concrete time and success bounds (Definition 10.1). Since the reduction is exact, a
concrete bound transfers with up to `k n - 1` extra evaluations of `f`.

The reduction is exact. The iterate permutes the words of each length, so its image of a uniform
`n`-bit word is uniform. An inverter for the iterate, given `f x`, applies `f` another `k n - 1`
times and returns the inverter's answer: whenever that answer is a preimage of `f^[k n] x`, it
is `x` itself. The two inversion experiments therefore have the same success probability at every
length with `k n ≠ 0`.

## Main definitions

* `Cslib.Crypto.iterateByLength`: apply `f` to `x` exactly `k |x|` times.
* `Cslib.Crypto.iterateInverter`: the inverter for `f` built from an inverter for the iterate.

## Main results

* `Cslib.Crypto.eval_inversionGame_iterateByLength`: the two inversion experiments agree at
  every length `n` with `k n ≠ 0`.
* `Cslib.Crypto.OneWayPermutation.iterateByLength`: the iterate of a one-way permutation is a
  one-way permutation.
* `Cslib.Crypto.OneWayPermutation.iterate_ceil_rpow`: the exercise for `k n = ⌈n ^ c⌉` with
  rational `c`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft
  2007-01-08][AroraBarak07], Chapter 10, Exercise 3, printed p. 204 (PDF p. 220).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- Apply `f` to `x` exactly `k |x|` times. -/
def iterateByLength (f : List Bool → List Bool) (k : ℕ → ℕ) (x : List Bool) : List Bool :=
  f^[k x.length] x

/-- The inverter for `f` built from an inverter for its iterate: on the challenge `y` at length
`n`, apply `f` another `k n - 1` times and pass the result on. -/
def iterateInverter (f : List Bool → List Bool) (k : ℕ → ℕ) (adversary : Inverter) : Inverter :=
  fun n y => adversary n (f^[k n - 1] y)

variable {f : List Bool → List Bool} {k : ℕ → ℕ}

/-- Iterating a length-preserving function preserves length (`Function.iterate_invariant`). -/
private theorem length_iterate (hlen : ∀ word, (f word).length = word.length) (i : ℕ)
    (x : List Bool) : (f^[i] x).length = x.length :=
  congrFun (Function.iterate_invariant (g := List.length) (funext hlen) i) x

/-- The iterate of a length-preserving bijection is a length-preserving bijection. -/
theorem bijective_iterateByLength (hlen : ∀ word, (f word).length = word.length)
    (hf : Function.Bijective f) (k : ℕ → ℕ) : Function.Bijective (iterateByLength f k) := by
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · have hlength : x.length = y.length := by
      simpa only [iterateByLength, length_iterate hlen] using congrArg List.length hxy
    simp only [iterateByLength, hlength] at hxy
    exact (hf.iterate _).injective hxy
  · obtain ⟨x, hx⟩ := (hf.iterate (k y.length)).surjective y
    refine ⟨x, ?_⟩
    have hlength : x.length = y.length := by
      rw [← hx, length_iterate hlen]
    simpa only [iterateByLength, hlength] using hx

/-- A length-preserving polynomial-time function iterated a polynomial-time number of times, the
count computed from the input length, is polynomial time. -/
theorem computableInPolyTime_iterateByLength (hf : ComputableInPolyTime f encBits encBits)
    (hlen : ∀ word, (f word).length = word.length)
    (hk : ComputableInPolyTime k encUnary encUnary) :
    ComputableInPolyTime (iterateByLength f k) encBits encBits := by
  have hcount : ComputableInPolyTime (fun x : List Bool => k x.length) encBits encUnary :=
    hk.comp ComputableInPolyTime.length_bits
  exact (ComputableInPolyTime.iterate_of_bounded_growth (growth := 0) hcount
    ComputableInPolyTime.id' hf fun state => by
      simp [encBits, hlen])

/-- The derived inverter is uniform strict PPT when the iterate's inverter is. -/
theorem isPPT_iterateInverter (hf : ComputableInPolyTime f encBits encBits)
    (hlen : ∀ word, (f word).length = word.length)
    (hk : ComputableInPolyTime k encUnary encUnary) {adversary : Inverter}
    (hadversary : IsPPT encBits adversary) : IsPPT encBits (iterateInverter f k adversary) := by
  have hcount : ComputableInPolyTime (fun p : ℕ × List Bool => k p.1 - 1)
      (encPair encUnary encBits) encUnary := by fun_prop
  have hiterate : ComputableInPolyTime (fun p : ℕ × List Bool => f^[k p.1 - 1] p.2)
      (encPair encUnary encBits) encBits :=
    ComputableInPolyTime.iterate_of_bounded_growth (growth := 0) hcount
      (ComputableInPolyTime.snd encUnary encBits) hf fun state => by simp [encBits, hlen]
  exact hadversary.preprocess (ComputableInPolyTime.fst encUnary encBits)
    hiterate

/-- **The reduction is exact.** At every length `n` with `k n ≠ 0`, the derived inverter inverts
`f` exactly as often as the given inverter inverts the iterate. -/
theorem eval_inversionGame_iterateByLength (hlen : ∀ word, (f word).length = word.length)
    (hf : Function.Bijective f) (adversary : Inverter) {n : ℕ} (hn : k n ≠ 0) :
    ProbComp.eval (inversionGame (iterateByLength f k) adversary n) =
      ProbComp.eval (inversionGame f (iterateInverter f k adversary) n) := by
  rw [inversionGame_eq_of_injective _ (bijective_iterateByLength hlen hf k).injective,
    inversionGame_eq_of_injective _ hf.injective]
  simp only [ProbComp.eval_bind, BitString.eval_sampleList]
  refine PMF.bind_congr_on_support _ _ _ fun x hx => ?_
  have hx : x.length = n := BitString.length_of_mem_support_uniformList hx
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simp only [iterateByLength, iterateInverter, hx, hm, Nat.succ_sub_one,
    Function.iterate_succ_apply]

/-- **Iterates of a one-way permutation are one-way** ([AroraBarak07], Chapter 10, Exercise 3).
For a one-way permutation `f` and a polynomial-time computable `k` (unary in, unary out) with
`k n ≠ 0` for all large `n`, the map `x ↦ f^[k |x|] x` is a one-way permutation. The exercise's
count `n ^ c` is the instance `k n = ⌈n ^ c⌉`, which `OneWayPermutation.iterate_ceil_rpow`
supplies for every rational `c`. -/
theorem OneWayPermutation.iterateByLength (hf : OneWayPermutation f)
    (hk : ComputableInPolyTime k encUnary encUnary) (hpos : ∀ᶠ n in Filter.atTop, k n ≠ 0) :
    OneWayPermutation (iterateByLength f k) := by
  have hpoly := hf.oneWay.polyTime
  refine ⟨.of_inversion_negligible (computableInPolyTime_iterateByLength hpoly hf.length_eq hk)
      fun adversary hadversary => ?_, fun x => ?_, bijective_iterateByLength hf.length_eq
      hf.bijective k⟩
  · refine (hf.oneWay.inversion_negligible _
      (isPPT_iterateInverter hpoly hf.length_eq hk hadversary)).congr' ?_
    filter_upwards [hpos] with n hn
    rw [eval_inversionGame_iterateByLength hf.length_eq hf.bijective adversary hn]
  · exact length_iterate hf.length_eq _ x

/-- **The exercise for rational exponents** ([AroraBarak07], Chapter 10, Exercise 3): for a
one-way permutation `f` and naturals `p` and `q ≠ 0`, the map `x ↦ f^[⌈|x| ^ (p / q)⌉] x` is a
one-way permutation. -/
theorem OneWayPermutation.iterate_ceil_rpow (hf : OneWayPermutation f) (p q : ℕ) (hq : q ≠ 0) :
    OneWayPermutation (fun x => f^[⌈(x.length : ℝ) ^ ((p : ℝ) / q)⌉₊] x) :=
  hf.iterateByLength (k := fun n => ⌈(n : ℝ) ^ ((p : ℝ) / q)⌉₊)
    (ComputableInPolyTime.unary_ceil_rpow p q hq)
    (Filter.eventually_atTop.2 ⟨1, fun n hn => (Nat.ceil_pos.2
      (Real.rpow_pos_of_pos (by exact_mod_cast hn) _)).ne'⟩)

end Cslib.Crypto
