/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BPP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Foundations.Data.BitString.Enumeration
public import CslibFrontier.Foundations.Data.BitString.List.Operations
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.TwoPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation

/-!
# Derandomization by enumerating the seeds of a generator

A pseudorandom generator derandomizes a bounded-error verifier `V` by brute force: on an instance
`x`, run `V` on `x` and the string generated from each seed of some length `k`, and return the
strict majority of the answers [Arora and Barak, Lemma 16.4][AroraBarak07],
[Goldreich, Proposition 8.15][Goldreich2007DraftR4]. This file gives that decider for an arbitrary
seed map `gen x : List Bool → List Bool`, which may depend on the instance, and its two
properties.

* *Correctness.* If, on `x`, the fraction of seeds on which `V` accepts the generated string is
  within `1 / 6` of the fraction of random strings that `V` accepts, then the majority vote gives
  the right answer (`Cslib.Complexity.seedDecider_eq_true_iff`): a bounded-error verifier accepts
  at least `2 / 3` or at most `1 / 3` of its random strings.
* *Running time.* The decider is polynomial-time when the generator is and `2 ^ k` is polynomially
  bounded (`Cslib.Complexity.computableInPolyTime_seedDecider`). For any seed length `k(x)`
  computable in unary in polynomial time, it runs within time and space `2 ^ O(k(x))` times a
  polynomial in the length of `x` (`Cslib.Complexity.exists_computableInO_seedDecider`) when the
  generator is polynomial-time on the instance padded by `2 ^ k(x)`, as a generator running in time
  `2 ^ O(k)` is: the decider is then polynomial-time on the padded instance
  (`Turing.MultiTapeTM.ComputableInPolyTime.exists_computableInO_pad`).

Its instances are the Nisan–Wigderson derandomization
(`Cslib.Complexity.BPP_subset_P_of_isAverageCaseHard`), the derandomization from circuit-secure
generators of polynomial stretch
(`Cslib.Complexity.BPP_subset_DTIME_two_pow_rpow_of_polyStretch_circuitSecurePRG`) and from
generators running in time exponential in the seed
(`Cslib.Complexity.CanonicalDerandomizer.exists_mem_DTIME_of_mem_BPTIME`).

## Main definitions

* `Cslib.Complexity.seedDecider`: the strict majority of a verifier over the generated strings of
  all seeds of a computed length.

## Main results

* `Cslib.Complexity.seedDecider_eq_true_iff`: correctness from a gap below `1 / 6`.
* `Cslib.Complexity.seedDecider_eq_of_boundedError`: the same for an expected Boolean answer.
* `Cslib.Complexity.computableInPolyTime_seedDecider`: polynomial time for logarithmic seeds.
* `Cslib.Complexity.exists_computableInO_seedDecider`: time `2 ^ O(k)` times a polynomial.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, draft][AroraBarak07],
  Chapter 16
* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft
  r4][Goldreich2007DraftR4], Chapter 8
-/

@[expose] public section

open Turing Turing.MultiTapeTM

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM.ComputableInPolyTime

variable {α : Type} {enc : α ↪ List Bool}

/-- The decider obtained from a verifier `V` by enumerating seeds: on an instance `x`, it runs `V`
on `x` and the string `gen x z` for each of the `2 ^ seed x` seeds `z` of `seed x` bits, and
returns the strict majority of the answers. -/
def seedDecider (V : α × List Bool → Bool) (gen : α → List Bool → List Bool) (seed : α → ℕ)
    (x : α) : Bool :=
  BitString.listStrictMajority ((BitString.enumList (seed x)).map fun z => V (x, gen x z))

/-! ### Correctness -/

/-- The strict majority of the votes over all seeds of `ℓ` bits compares the number of seeds voting
`true` with half of `2 ^ ℓ`. -/
private theorem listStrictMajority_map_enumList (ℓ : ℕ) (vote : List Bool → Bool) :
    BitString.listStrictMajority ((BitString.enumList ℓ).map vote) =
      decide (2 ^ ℓ / 2 < #{z : Fin ℓ → Bool | vote (List.ofFn z) = true}) := by
  rw [BitString.enumList, List.map_map, BitString.listStrictMajority_map _ (BitString.nodup_enum ℓ),
    BitString.strictMajorityOn]
  have huniv : (BitString.enum ℓ).toFinset = univ := by ext; simp
  simp only [huniv, card_univ, BitString.card, Function.comp_apply]

/-- A count `Z` of `2 ^ ℓ` seeds within `1 / 6` of the fraction accepted by a bounded-error test is
a strict majority exactly when the test answers `true`. -/
private theorem majority_iff_of_abs_sub_lt {m ℓ Z R : ℕ} {P : Prop}
    (hgap : |((Z : ℝ) / 2 ^ ℓ - (R : ℝ) / 2 ^ m)| < 1 / 6)
    (hdec : (P → 2 * 2 ^ m ≤ 3 * R) ∧ (¬P → 3 * R ≤ 2 ^ m)) :
    P ↔ 2 ^ ℓ / 2 < Z := by
  have h2ℓ : (0 : ℝ) < 2 ^ ℓ := by positivity
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  rw [abs_sub_lt_iff] at hgap
  constructor
  · intro hP
    have hR' : (2 : ℝ) * 2 ^ m ≤ 3 * R := by exact_mod_cast hdec.1 hP
    have hZ' : (2 : ℝ) ^ ℓ < 2 * Z := by
      have := hgap.2
      rw [div_sub_div _ _ h2m.ne' h2ℓ.ne', div_lt_iff₀ (by positivity)] at this
      nlinarith
    have hZ'' : 2 ^ ℓ < 2 * Z := by exact_mod_cast hZ'
    exact (Nat.div_lt_iff_lt_mul two_pos).2 (by omega)
  · intro hlt
    by_contra hP
    have hR' : (3 : ℝ) * R ≤ 2 ^ m := by exact_mod_cast hdec.2 hP
    have hZ' : (2 : ℝ) * Z < 2 ^ ℓ := by
      have := hgap.1
      rw [div_sub_div _ _ h2ℓ.ne' h2m.ne', div_lt_iff₀ (by positivity)] at this
      nlinarith
    have hZ'' : 2 * Z < 2 ^ ℓ := by exact_mod_cast hZ'
    have := (Nat.div_lt_iff_lt_mul two_pos).1 hlt
    omega

/-- **Seed enumeration is correct when the generator fools the verifier on the instance.** Let `V`
answer whether `x ∈ A` with bounded error on random strings of `m` bits: it accepts at least two
thirds of them if `x ∈ A`, and at most one third otherwise. If the fraction of the seeds `z` of
`seed x` bits on which `V` accepts `gen x z` is within `1 / 6` of the fraction of the random
strings of `m` bits that `V` accepts, then `seedDecider V gen seed` answers correctly on `x`. -/
theorem seedDecider_eq_true_iff {A : Set α} {V : α × List Bool → Bool} {x : α} {m : ℕ}
    (hyes : x ∈ A → 2 * 2 ^ m ≤ 3 * acceptCount V x m)
    (hno : x ∉ A → 3 * acceptCount V x m ≤ 2 ^ m)
    (gen : α → List Bool → List Bool) (seed : α → ℕ)
    (hgap : |(#{z : Fin (seed x) → Bool | V (x, gen x (List.ofFn z)) = true} : ℝ) / 2 ^ seed x -
      acceptCount V x m / 2 ^ m| < 1 / 6) :
    seedDecider V gen seed x = true ↔ x ∈ A := by
  rw [seedDecider, listStrictMajority_map_enumList, decide_eq_true_iff]
  exact (majority_iff_of_abs_sub_lt hgap ⟨hyes, hno⟩).symm

/-- **Seed enumeration gives the expected answer.** If `V` answers `b` with bounded error on random
strings of `m` bits at `x` (it accepts at least two thirds of them if `b = true`, at most one third
if `b = false`), and the seeds are within `1 / 6` of the random strings as in
`seedDecider_eq_true_iff`, then `seedDecider V gen seed x = b`. -/
theorem seedDecider_eq_of_boundedError {V : α × List Bool → Bool} {x : α} {m : ℕ} {b : Bool}
    (htrue : b = true → 2 * 2 ^ m ≤ 3 * acceptCount V x m)
    (hfalse : b = false → 3 * acceptCount V x m ≤ 2 ^ m)
    (gen : α → List Bool → List Bool) (seed : α → ℕ)
    (hgap : |(#{z : Fin (seed x) → Bool | V (x, gen x (List.ofFn z)) = true} : ℝ) / 2 ^ seed x -
      acceptCount V x m / 2 ^ m| < 1 / 6) :
    seedDecider V gen seed x = b := by
  have h := majority_iff_of_abs_sub_lt (P := b = true) hgap
    ⟨htrue, fun hb => hfalse (Bool.eq_false_iff.2 hb)⟩
  rw [seedDecider, listStrictMajority_map_enumList]
  cases b <;> simp_all

/-! ### Running time -/

/-- **Seed enumeration in polynomial time.** Let `V` and the generator be polynomial-time, and the
seed length `seed x` be computable in unary in polynomial time. When `2 ^ seed x` is polynomially
bounded in the length of the instance, `seedDecider V gen seed` is polynomial-time. -/
theorem computableInPolyTime_seedDecider {V : α × List Bool → Bool}
    {gen : α → List Bool → List Bool} {seed : α → ℕ}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool)
    (hgen : ComputableInPolyTime (fun p : α × List Bool => gen p.1 p.2) (encPair enc encBits)
      encBits)
    (hseed : ComputableInPolyTime seed enc encUnary)
    (hbudget : PolyBounded (fun x => (enc x).length) fun x => 2 ^ seed x) :
    ComputableInPolyTime (seedDecider V gen seed) enc encBool := by
  have hvote : ComputableInPolyTime (fun p : α × List Bool => V (p.1, gen p.1 p.2))
      (encPair enc encBits) encBool :=
    hV.comp ((fst enc encBits).prod hgen)
  exact bitsStrictMajorityWithInput (mapToBitsWithInput (f := fun x z => V (x, gen x z))
    (bitsEnumList_of_polyBounded hseed hbudget) hvote)

/-- **Seed enumeration in time `2 ^ O(k)`.** Let `V` be polynomial-time, and the seed length
`seed x` be computable in unary in polynomial time. Let the generator be polynomial-time on
instances padded to `(x, N)` with `N = 2 ^ seed x` in unary: `gen'` is polynomial-time on
`((x, N), z)` and agrees with `gen x` on seeds of `seed x` bits when `N = 2 ^ seed x`. A generator
running in time `2 ^ O(k)` on seeds of `k` bits has such a padded form. Then
`seedDecider V gen seed` is computable within time and space `C 2 ^ (D seed x) (|x| + 1) ^ D` for
some constants `C` and `D`: on the padded instance it is polynomial-time. -/
theorem exists_computableInO_seedDecider {V : α × List Bool → Bool}
    {gen : α → List Bool → List Bool} {seed : α → ℕ} (gen' : α × ℕ → List Bool → List Bool)
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool)
    (hgen : ComputableInPolyTime (fun q : (α × ℕ) × List Bool => gen' q.1 q.2)
      (encPair (encPair enc encUnary) encBits) encBits)
    (hgen' : ∀ x z, z.length = seed x → gen' (x, 2 ^ seed x) z = gen x z)
    (hseed : ComputableInPolyTime seed enc encUnary) :
    ∃ C D : ℕ, ComputableInO (seedDecider V gen seed) enc encBool
      (fun x => C * 2 ^ (D * seed x) * ((enc x).length + 1) ^ D)
      (fun x => C * 2 ^ (D * seed x) * ((enc x).length + 1) ^ D) := by
  -- the decider on padded instances `(x, N)`, with seeds of `⌊log₂ N⌋` bits
  set encP := encPair enc encUnary
  have hfst : ComputableInPolyTime (fun p : (α × ℕ) × List Bool => p.1.1)
      (encPair encP encBits) enc := (fst enc encUnary).comp (fst encP encBits)
  have hV' : ComputableInPolyTime (fun p : (α × ℕ) × List Bool => V (p.1.1, p.2))
      (encPair encP encBits) encBool := hV.comp (hfst.prod (snd encP encBits))
  have hlog : ComputableInPolyTime (fun q : α × ℕ => Nat.log 2 q.2) encP encUnary :=
    binary_log_two.comp (unary_to_binary.comp (snd enc encUnary))
  have hbudget : PolyBounded (fun q : α × ℕ => (encP q).length) fun q => 2 ^ Nat.log 2 q.2 := by
    growth_poly
  obtain ⟨C, D, h⟩ := ComputableInPolyTime.exists_computableInO_pad
    (computableInPolyTime_seedDecider hV' hgen hlog hbudget) hseed
  have heq : (fun x => seedDecider (fun p : (α × ℕ) × List Bool => V (p.1.1, p.2))
      gen' (fun q => Nat.log 2 q.2) (x, 2 ^ seed x)) = seedDecider V gen seed := by
    funext x
    simp only [seedDecider, Nat.log_pow Nat.one_lt_two]
    exact congrArg _ (List.map_congr_left fun z hz =>
      congrArg (fun w => V (x, w)) (hgen' x z (BitString.length_of_mem_enumList hz)))
  exact ⟨C, D, heq ▸ h⟩

end Cslib.Complexity
