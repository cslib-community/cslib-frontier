/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Oracle
public import CslibFrontier.Computability.Complexity.Classes.TFNP.SearchToDecision
public import CslibFrontier.Computability.Complexity.Reduction.Turing
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Complexity.Classes.NP.Image
import CslibFrontier.Computability.Complexity.Classes.Oracle.PolyTime
import CslibFrontier.Computability.Complexity.Problems.Primes
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip

/-!
# Self-reducibility of search problems

The decision problem *implicit* in a search problem `R` is its domain `S_R = searchDomain R`, the
instances that have a solution. Goldreich calls `R` *self-reducible* if its search problem is
Cook-reducible to deciding `S_R` [Goldreich, Definition 2.14][Goldreich2006DraftR1]: a
polynomial-time oracle machine with oracle `S_R` finds a solution of every instance that has one
and reports `⊥` on the others. Here (`Cslib.Complexity.SearchSelfReducible`) the machine is a
`Cslib.Complexity.ComputableInPolyTimeWithOracle` program relative to the oracle language
`enc '' searchDomain R`, and the function it computes must satisfy
`Cslib.Complexity.SolvesSearch R`. The oracle of a decision problem is unique, so Goldreich's
quantifier over every solver of the oracle problem (Definition 2.9) is this one oracle language.
This is Goldreich's search-to-decision notion; the one-bit witness-family reductions of the
counting literature are the structure `Cslib.Complexity.SelfReducible`.

The decision problem of `S_R` reduces to the search problem of `R`, so self-reducibility says that
the two are computationally equivalent. Self-reducibility is a property of the relation and not of
its domain. These results show it.

* `Cslib.Complexity.exists_mem_FNP_not_selfReducible` (Exercise 2.14(1)): if `P ≠ NP ∩ coNP`, some
  `R ∈ PC` (`PC` is `Cslib.Complexity.FNP`) is not self-reducible. A total relation in `FNP`
  outside `FPSearch` exists by `Cslib.Complexity.NP_inter_coNP_subset_P_of_TFNP_subset_FPSearch`
  (the guideline's disjoint sum). Every instance has a solution, so the oracle is trivial, and a
  self-reduction would solve `R` in polynomial time.
* `Cslib.Complexity.not_selfReducible_divisorSearch` (Exercise 2.16): for the relation
  `Cslib.Complexity.divisorSearch` of numbers and their non-trivial divisors, the domain is the set
  of composite numbers, which is in `P` because primality is. So if no polynomial-time algorithm
  splits composite numbers, then neither the search problem nor its prefix problem `S'_R` reduces
  to `S_R`.
* `Cslib.Complexity.exists_selfReducible_not_selfReducible` (Exercise 2.17): under the same
  assumption, `Cslib.Complexity.compositeSearch` (`N` is the solution of every composite `N`) and
  `divisorSearch` have the same domain, but only the first is self-reducible.

Natural numbers are encoded in binary (`encNat`); a divisor is written as the binary digits
`encNat Q`, so solutions are no longer than the instance. Oracle languages of typed problems use
a decoder of the instance encoding to be in `P` on words (`Cslib.Complexity.mem_P_image`).

## Main definitions

* `Cslib.Complexity.SearchSelfReducible`: Goldreich's Definition 2.14.
* `Cslib.Complexity.divisorSearch`: non-trivial divisors in binary.
* `Cslib.Complexity.compositeSearch`: composite numbers with themselves as solution.

## Main results

* `Cslib.Complexity.SearchSelfReducible.of_mem_FPSearch`,
  `Cslib.Complexity.SearchSelfReducible.mem_FPSearch`: search problems in `FPSearch` are
  self-reducible, and a self-reducible `FNP` relation whose domain is in `P` is in `FPSearch`.
* `Cslib.Complexity.mem_FPSearch_of_polyTimeTuringReducible_prefixSearch`: the same for a Cook
  reduction of the prefix problem `S'_R` to `S_R`.
* `Cslib.Complexity.exists_mem_FNP_not_selfReducible`: Exercise 2.14(1).
* `Cslib.Complexity.divisorSearch_mem_FPSearch_iff`: the divisor relation is in `FPSearch` exactly
  when some polynomial-time function splits every composite number.
* `Cslib.Complexity.not_selfReducible_divisorSearch`: Exercise 2.16.
* `Cslib.Complexity.exists_selfReducible_not_selfReducible`: Exercise 2.17.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*][Goldreich2006DraftR1],
  Definitions 2.9 and 2.14, the discussion on printed p. 72, and Exercises 2.14, 2.16 and 2.17
  (draft r1.pdf of December 2006, printed pp. 65, 70 and 108).
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

variable {α : Type} {enc : α ↪ List Bool} {R : α → List Bool → Prop}

/-! ### Self-reducibility -/

/-- The search problem `R` is *self-reducible* [Goldreich, Definition 2.14][Goldreich2006DraftR1]:
some function computable in polynomial time relative to the oracle language
`enc '' searchDomain R` of the implicit decision problem solves `R`, returning a solution of every
instance that has one and `none` on the others. -/
@[expose] def SearchSelfReducible (enc : α ↪ List Bool) (R : α → List Bool → Prop) : Prop :=
  ∃ f : α → Option (List Bool),
    ComputableInPolyTimeWithOracle (enc '' searchDomain R) f enc (encOption encBits) ∧
      SolvesSearch R f

/-- A search problem in `FPSearch` is self-reducible, by a solver that makes no request. -/
theorem SearchSelfReducible.of_mem_FPSearch (h : R ∈ FPSearch enc) : SearchSelfReducible enc R :=
  let ⟨_, f, hf, hsolve⟩ := h
  ⟨f, hf.computableInPolyTimeWithOracle _, hsolve⟩

/-- **A self-reducible relation with an easy domain is easy.** If `R ∈ FNP` is self-reducible and
the oracle language of its domain is in `P`, then `R ∈ FPSearch`: the requests are answered by
the decider. -/
theorem SearchSelfReducible.mem_FPSearch (hR : R ∈ FNP enc) (h : SearchSelfReducible enc R)
    (hS : enc '' searchDomain R ∈ P encBits) : R ∈ FPSearch enc :=
  let ⟨f, hf, hsolve⟩ := h
  ⟨hR, f, hf.computableInPolyTime hS, hsolve⟩

/-- If the prefix problem `S'_R` of `R ∈ FNP` is Cook-reducible to `S_R` and the oracle language of
`S_R` is in `P`, then `R ∈ FPSearch`: `S'_R` is then in `P`, and search through prefixes solves
`R`. -/
theorem mem_FPSearch_of_polyTimeTuringReducible_prefixSearch (hR : R ∈ FNP enc)
    (h : PolyTimeTuringReducible (encPair enc encBits) enc (searchDomain (prefixSearch R))
      (searchDomain R))
    (hS : enc '' searchDomain R ∈ P encBits) : R ∈ FPSearch enc :=
  mem_FPSearch_of_prefixSearch_mem_P hR (PWithOracle_eq_P hS _ ▸ h)

/-! ### Exercise 2.14(1) -/

/-- **A search problem in `PC` that is not self-reducible**
[Goldreich, Exercise 2.14(1)][Goldreich2006DraftR1]. If `P ≠ NP ∩ coNP` for an encoding `enc`
with a polynomial-time decoder, some `R ∈ FNP enc` (Goldreich's `PC`) is not self-reducible.
As in the guideline, every instance has a solution (`S_R` is everything) and `R ∉ FPSearch`.
`FPSearch` is `PF ∩ PC`, so for this `R ∈ PC` it says that `R` is not in Goldreich's `PF`. For
instances that are words, take `enc = encBits` and `Decoder.bits`.

The relation comes from `NP_inter_coNP_subset_P_of_TFNP_subset_FPSearch`: some total relation in
`FNP` is not in `FPSearch`. Its domain is everything, so the oracle is in `P`, and a
self-reduction would put it in `FPSearch`. -/
theorem exists_mem_FNP_not_selfReducible (D : Decoder enc)
    (hne : P enc ≠ NP enc ∩ coNP enc) :
    ∃ R ∈ FNP enc, IsTotalSearch R ∧ R ∉ FPSearch enc ∧ ¬SearchSelfReducible enc R := by
  obtain ⟨R, ⟨hR, htot⟩, hRP⟩ := Set.not_subset.mp fun h : TFNP enc ⊆ FPSearch enc =>
    hne ((Set.subset_inter (fun _ h => P_subset_NP h) fun _ h => P_subset_coNP h).antisymm
      (NP_inter_coNP_subset_P_of_TFNP_subset_FPSearch h))
  refine ⟨R, hR, htot, hRP, fun h => hRP (h.mem_FPSearch hR ?_)⟩
  rw [isTotalSearch_iff_searchDomain_eq_univ.mp htot]
  exact mem_P_image D univ_mem_P

/-! ### Exercises 2.16 and 2.17: non-trivial divisors -/

/-- The search problem of non-trivial divisors [Goldreich, Exercise 2.16][Goldreich2006DraftR1]:
the solutions of `N` are the binary digits `encNat Q` of the numbers `Q` with `1 < Q < N` that
divide `N`. -/
@[expose] def divisorSearch (N : ℕ) (w : List Bool) : Prop :=
  ∃ Q, encNat Q = w ∧ 1 < Q ∧ Q < N ∧ Q ∣ N

/-- The composite numbers with themselves as solution: the solution of `N` is `encNat N` when
`N` is composite. -/
@[expose] def compositeSearch (N : ℕ) (w : List Bool) : Prop :=
  w = encNat N ∧ 1 < N ∧ ¬N.Prime

/-- The numbers with a non-trivial divisor are the composite numbers. -/
theorem searchDomain_divisorSearch : searchDomain divisorSearch = {N | 1 < N ∧ ¬N.Prime} := by
  ext N
  simp only [mem_searchDomain, divisorSearch, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, Q, rfl, hQ, hQN, hdvd⟩
    exact ⟨hQ.trans hQN, fun hp => ((hp.eq_one_or_self_of_dvd Q hdvd).elim
      (fun h => by omega) fun h => by omega)⟩
  · rintro ⟨hN, hp⟩
    obtain ⟨Q, hdvd, hQ, hQN⟩ := (Nat.not_prime_iff_exists_dvd_lt (by omega)).mp hp
    exact ⟨_, Q, rfl, by omega, hQN, hdvd⟩

/-- The composite numbers are the domain of `compositeSearch` too. -/
theorem searchDomain_compositeSearch : searchDomain compositeSearch = {N | 1 < N ∧ ¬N.Prime} :=
  Set.ext fun _ => ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨_, rfl, h⟩⟩

/-- **The composite numbers are in `P`**, as the primes are [Agrawal, Kayal, Saxena][AKS2004]. -/
theorem setOf_composite_mem_P : {N : ℕ | 1 < N ∧ ¬N.Prime} ∈ P encNat := by
  obtain ⟨f, hf, hfp⟩ := mem_P.mp primes_mem_P
  refine mem_P.mpr ⟨fun N => decide (1 < N) && !f N, by fun_prop, fun N => ?_⟩
  have h : N.Prime ↔ f N = true := hfp N
  cases hfN : f N <;> simp_all

private theorem length_encNat_le_of_lt {Q N : ℕ} (h : Q < N) :
    (encNat Q).length ≤ (encNat N).length := by
  simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le_size h.le

/-- The divisor relation is in `FNP` (Goldreich's `PC`): a candidate is checked by decoding it,
re-encoding it, and comparing it and its greatest common divisor with `N`. -/
theorem divisorSearch_mem_FNP : divisorSearch ∈ FNP encNat := by
  have hre : ComputableInPolyTime (fun x : ℕ × List Bool => encNat (ofBits x.2))
      (encPair encNat encBits) encBits := (bitsToNat.comp (snd encNat encBits)).encoding_comp
  refine mem_FNP.mpr ⟨⟨.X, fun N w ⟨Q, hw, _, hQN, _⟩ => ?_⟩,
    fun x => decide (encNat (ofBits x.2) = x.2) && decide (1 < ofBits x.2) &&
      decide (ofBits x.2 < x.1) && decide (Nat.gcd (ofBits x.2) x.1 = ofBits x.2),
    by fun_prop, fun N w => ?_⟩
  · simpa [← hw] using length_encNat_le_of_lt hQN
  · simp only [divisorSearch, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨Q, rfl, hQ, hQN, hdvd⟩
      simp [hQ, hQN, Nat.gcd_eq_left hdvd]
    · rintro ⟨⟨⟨hre, hQ⟩, hQN⟩, hgcd⟩
      exact ⟨_, hre, hQ, hQN, hgcd ▸ Nat.gcd_dvd_right _ _⟩

/-- `compositeSearch` is in `FPSearch`: test compositeness, and return `N`. -/
theorem compositeSearch_mem_FPSearch : compositeSearch ∈ FPSearch encNat := by
  obtain ⟨c, hc, hcS⟩ := mem_P.mp setOf_composite_mem_P
  refine mem_FPSearch.mpr ⟨mem_FNP.mpr ⟨⟨.X, fun N w h => by simp [h.1]⟩,
      fun x => decide (x.2 = encNat x.1) && c x.1, by fun_prop,
      fun N w => by
        simp only [compositeSearch, Bool.and_eq_true, decide_eq_true_eq, ← hcS N,
          Set.mem_ofPred_eq]⟩,
    fun N => if c N then some (encNat N) else none, by fun_prop, fun N => ?_⟩
  by_cases hN : c N = true
  · simp only [hN, ite_true, Option.some.injEq]
    exact ⟨fun w hw => ⟨hw.symm, (hcS N).2 hN⟩, fun h => (Option.some_ne_none _ h).elim⟩
  · simp only [hN, Bool.false_eq_true, ite_false, reduceCtorEq, false_imp_iff, implies_true,
      true_and]
    exact fun _ ⟨_, _, h⟩ => hN ((hcS N).1 h)

/-- **The divisor relation is in `FPSearch` exactly when composite numbers can be split in
polynomial time**: when some polynomial-time function on binary numbers returns a non-trivial
divisor of every composite number. The intractability of factoring in
[Goldreich, Exercise 2.16][Goldreich2006DraftR1] is read as the failure of the right side. -/
theorem divisorSearch_mem_FPSearch_iff : divisorSearch ∈ FPSearch encNat ↔
    ∃ f : ℕ → ℕ, ComputableInPolyTime f encNat encNat ∧
      ∀ N, 1 < N → ¬N.Prime → 1 < f N ∧ f N < N ∧ f N ∣ N := by
  constructor
  · rintro ⟨-, s, hs, hsolve⟩
    refine ⟨fun N => ofBits ((s N).getD []), by fun_prop, fun N hN hp => ?_⟩
    have hdom : N ∈ searchDomain divisorSearch := by
      rw [searchDomain_divisorSearch]
      exact ⟨hN, hp⟩
    cases hsN : s N with
    | none => exact (hsolve.notMem hsN hdom).elim
    | some w =>
      obtain ⟨Q, rfl, hQ⟩ := hsolve.rel hsN
      simpa only [hsN, Option.getD_some, ofBits_encNat] using hQ
  · rintro ⟨f, hf, hsplit⟩
    obtain ⟨c, hc, hcS⟩ := mem_P.mp setOf_composite_mem_P
    refine mem_FPSearch.mpr ⟨divisorSearch_mem_FNP,
      fun N => if c N then some (encNat (f N)) else none, by fun_prop,
      fun N => ⟨fun w hw => ?_, fun hw => ?_⟩⟩
    · by_cases hN : c N = true
      · simp only [hN, ite_true, Option.some.injEq] at hw
        obtain ⟨h₁, h₂⟩ := (hcS N).2 hN
        exact ⟨f N, hw, hsplit N h₁ h₂⟩
      · simp [hN] at hw
    · rw [searchDomain_divisorSearch]
      intro hmem
      by_cases hN : c N = true
      · simp [hN] at hw
      · exact hN ((hcS N).1 hmem)

/-- The oracle language of the composite numbers is in `P` on words. -/
private theorem image_composite_mem_P :
    encNat '' searchDomain divisorSearch ∈ P encBits := by
  rw [searchDomain_divisorSearch]
  exact mem_P_image Decoder.nat setOf_composite_mem_P

/-- **The divisor relation is not self-reducible if factoring is hard**
[Goldreich, Exercise 2.16][Goldreich2006DraftR1]. If no polynomial-time function on binary numbers
returns a non-trivial divisor of every composite number, then the search problem of
`divisorSearch` is not Cook-reducible to its implicit decision problem `S_R` (the composite
numbers), and neither is its prefix problem `S'_R` (pairs `(N, y')` such that some solution
begins with `y'`). Factoring is read as finding one non-trivial divisor; see
`divisorSearch_mem_FPSearch_iff`. -/
theorem not_selfReducible_divisorSearch
    (hfact : ¬∃ f : ℕ → ℕ, ComputableInPolyTime f encNat encNat ∧
      ∀ N, 1 < N → ¬N.Prime → 1 < f N ∧ f N < N ∧ f N ∣ N) :
    ¬SearchSelfReducible encNat divisorSearch ∧
      ¬PolyTimeTuringReducible (encPair encNat encBits) encNat
        (searchDomain (prefixSearch divisorSearch)) (searchDomain divisorSearch) :=
  ⟨fun h => hfact (divisorSearch_mem_FPSearch_iff.mp
      (h.mem_FPSearch divisorSearch_mem_FNP image_composite_mem_P)),
    fun h => hfact (divisorSearch_mem_FPSearch_iff.mp
      (mem_FPSearch_of_polyTimeTuringReducible_prefixSearch divisorSearch_mem_FNP h
        image_composite_mem_P))⟩

/-- **Self-reducibility is not a property of the implicit decision problem**
[Goldreich, Exercise 2.17][Goldreich2006DraftR1]. Under the assumption named in the main text
(printed p. 72), the intractability of factoring (read as in `not_selfReducible_divisorSearch`),
there are `R₁, R₂ ∈ FNP` (Goldreich's `PC`) with the same domain such that `R₁` is
self-reducible and `R₂` is not. The witnesses are `compositeSearch` and `divisorSearch`, both
with the composite numbers as domain. -/
theorem exists_selfReducible_not_selfReducible
    (hfact : ¬∃ f : ℕ → ℕ, ComputableInPolyTime f encNat encNat ∧
      ∀ N, 1 < N → ¬N.Prime → 1 < f N ∧ f N < N ∧ f N ∣ N) :
    ∃ R₁ R₂ : ℕ → List Bool → Prop, R₁ ∈ FNP encNat ∧ R₂ ∈ FNP encNat ∧
      searchDomain R₁ = searchDomain R₂ ∧ SearchSelfReducible encNat R₁ ∧
        ¬SearchSelfReducible encNat R₂ :=
  ⟨compositeSearch, divisorSearch, compositeSearch_mem_FPSearch.1, divisorSearch_mem_FNP,
    searchDomain_compositeSearch.trans searchDomain_divisorSearch.symm,
    .of_mem_FPSearch compositeSearch_mem_FPSearch, (not_selfReducible_divisorSearch hfact).1⟩

end Cslib.Complexity
