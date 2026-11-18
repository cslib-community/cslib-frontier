/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Promise.Randomized
import CslibFrontier.Computability.Complexity.Classes.Promise.Probabilistic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.SuppCases
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Splitting the coins of a very-low-error BPP algorithm (Goldreich, Exercise 6.11)

The illustrative paragraph in Goldreich's proof of Theorem 6.9 [Goldreich2007Draft] starts from a
set `S` and an off-line BPP algorithm `A′` that reads `2 p′(|x|)` random bits and errs with
probability smaller than `2 ^ (-(p′(|x|) + 1))`. Splitting the random string as `r′ r″` into two
halves of length `p′(|x|)` pushes the whole error on yes-instances into the choice of `r′` and the
whole error on no-instances into the choice of `r″`. Exercise 6.11 makes this precise with the
promise problem `Π′`:

* `Π′_yes = {(x, r′) : |r′| = p′(|x|) ∧ ∀ r″ ∈ {0,1}^{|r′|}, A′(x, r′ r″) = 1}`;
* `Π′_no = {(x, r′) : x ∉ S}`.

It asks to show (1) that `x ↦ (x, r′)`, for uniform `r′ ∈ {0,1}^{p′(|x|)}`, is a one-sided error
randomized Karp reduction of `S` to `Π′` (no-instances always go to no-instances), and (2) that
`Π′` is in the promise version of `coRP`.

Here `|x|` is the length of the encoding `encA x`, the algorithm `A′ : α × List Bool → Bool` is a
polynomial-time function of the instance and the random string, and the error bound is
`PromiseProblem.SmallOfflineError`, stated by counting the random strings on which `A′` errs.
`Π′` is `PromiseProblem.coinSplit`; it takes the error bound as an argument, because the bound is
what makes its yes- and no-instances disjoint. Its instances `(x, r′)` are encoded by
`encPair encA encBits`.

## Main definitions

* `Cslib.Complexity.PromiseProblem.SmallOfflineError`: the error bound `2 ^ (-(p′(|x|) + 1))`
  with `2 p′(|x|)` random bits.
* `Cslib.Complexity.PromiseProblem.coinSplit`: Goldreich's promise problem `Π′`.

## Main results

* `Cslib.Complexity.PromiseProblem.half_lt_toOuterMeasure_coinSplit_yes`: Goldreich's sampler
  hits `Π′_yes` with probability greater than `1 / 2` on members of `S`.
* `Cslib.Complexity.PromiseProblem.rpReducibleWithError_coinSplit`: Exercise 6.11(1).
* `Cslib.Complexity.PromiseProblem.coinSplit_mem_PromiseCoRP`: Exercise 6.11(2).

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, 2007 draft, Section 6.1.3.2,
  proof of Theorem 6.9, and Exercise 6.11][Goldreich2007Draft]
-/

public section

namespace Cslib.Complexity.PromiseProblem

open Finset Turing.MultiTapeTM Probability

variable {α : Type} {encA : α ↪ List Bool} {S : Set α} {p' : Polynomial ℕ}
  {A' : α × List Bool → Bool}

open Classical in
/-- **The error bound of the illustration in the proof of Goldreich's Theorem 6.9.** On every
instance `x`, the algorithm `A′` reads `2 p′(|x|)` random bits, and fewer than a
`2 ^ (-(p′(|x|) + 1))` fraction of these random strings make it disagree with membership in `S`:
`2 · 2 ^ p′(|x|) · #{r : A′(x, r) ≠ χ_S(x)} < 2 ^ (2 p′(|x|))`. Here `|x|` is the length of
`encA x`. -/
@[expose] def SmallOfflineError (encA : α ↪ List Bool) (S : Set α) (p' : Polynomial ℕ)
    (A' : α × List Bool → Bool) : Prop :=
  ∀ x, 2 * 2 ^ p'.eval (encA x).length *
      #{r : Fin (2 * p'.eval (encA x).length) → Bool | ¬(A' (x, List.ofFn r) = true ↔ x ∈ S)} <
    2 ^ (2 * p'.eval (encA x).length)

/-- Concatenation of two random strings of length `m` as a random string of length `2 m`. -/
private def appendCoins (m : ℕ) : (Fin m → Bool) × (Fin m → Bool) ≃ (Fin (2 * m) → Bool) :=
  Fin.appendEquiv m m |>.trans (Equiv.arrowCongr (finCongr (two_mul m).symm) (Equiv.refl _))

private theorem ofFn_appendCoins (m : ℕ) (r : (Fin m → Bool) × (Fin m → Bool)) :
    List.ofFn (appendCoins m r) = List.ofFn r.1 ++ List.ofFn r.2 := by
  rw [← List.ofFn_fin_append]
  simp only [appendCoins, Equiv.trans_apply]
  exact List.ofFn_congr (two_mul m) _

/-- A random string of length `m` read from a list of length `m`. -/
private theorem exists_ofFn_eq {m : ℕ} {l : List Bool} (hl : l.length = m) :
    ∃ r : Fin m → Bool, List.ofFn r = l := by
  subst hl
  exact ⟨l.get, List.ofFn_get l⟩

/-- **The error moves to the second half.** If fewer than a `2 ^ (-(m + 1))` fraction of the
strings of length `2 m` satisfy `f`, then for every first half `r′` fewer than half of the second
halves `r″` make `r′ r″` satisfy `f`. -/
private theorem card_append_lt {m : ℕ} (f : List Bool → Prop) [DecidablePred f]
    (h : 2 * 2 ^ m * #{r : Fin (2 * m) → Bool | f (List.ofFn r)} < 2 ^ (2 * m))
    (r' : Fin m → Bool) :
    2 * #{r'' : Fin m → Bool | f (List.ofFn r' ++ List.ofFn r'')} < 2 ^ m := by
  have hle : #{r'' : Fin m → Bool | f (List.ofFn r' ++ List.ofFn r'')} ≤
      #{r : Fin (2 * m) → Bool | f (List.ofFn r)} := by
    refine card_le_card_of_injOn (fun r'' => appendCoins m (r', r'')) (fun r'' hr'' => ?_)
      fun a _ b _ hab => by simpa using (appendCoins m).injective hab
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hr'' ⊢
    rwa [ofFn_appendCoins]
  rw [show 2 ^ (2 * m) = 2 ^ m * 2 ^ m by rw [two_mul, pow_add]] at h
  have := lt_of_le_of_lt (Nat.mul_le_mul_left (2 * 2 ^ m) hle) h
  nlinarith [Nat.two_pow_pos m]

/-- **The error moves to the first half.** If fewer than a `2 ^ (-(m + 1))` fraction of the
strings of length `2 m` satisfy `f`, then more than half of the first halves `r′` make `r′ r″`
violate `f` for every second half `r″`. -/
private theorem lt_card_forall_not {m : ℕ} (f : List Bool → Prop) [DecidablePred f]
    (h : 2 * 2 ^ m * #{r : Fin (2 * m) → Bool | f (List.ofFn r)} < 2 ^ (2 * m)) :
    2 ^ m < 2 * #{r' : Fin m → Bool |
      ∀ r'' : Fin m → Bool, ¬f (List.ofFn r' ++ List.ofFn r'')} := by
  set good := ({r' : Fin m → Bool | ∀ r'' : Fin m → Bool,
    ¬f (List.ofFn r' ++ List.ofFn r'')} : Finset _)
  have hbad : goodᶜ ⊆ ({r : Fin (2 * m) → Bool | f (List.ofFn r)} : Finset _).image
      fun r => ((appendCoins m).symm r).1 := by
    intro r' hr'
    simp only [good, mem_compl, mem_filter, mem_univ, true_and, not_forall, not_not] at hr'
    obtain ⟨r'', hr''⟩ := hr'
    refine mem_image.2 ⟨appendCoins m (r', r''), ?_, by simp⟩
    simpa only [mem_filter, mem_univ, true_and, ofFn_appendCoins] using hr''
  have hle := (card_le_card hbad).trans card_image_le
  rw [show 2 ^ (2 * m) = 2 ^ m * 2 ^ m by rw [two_mul, pow_add]] at h
  have hlt := lt_of_le_of_lt (Nat.mul_le_mul_left (2 * 2 ^ m) hle) h
  have hsum : #goodᶜ + #good = 2 ^ m := by
    rw [card_compl_add_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  nlinarith [Nat.two_pow_pos m]

open Classical in
/-- On a no-instance, the erring strings are the accepting ones. -/
private theorem accept_bound (h : SmallOfflineError encA S p' A') {x : α} (hx : x ∉ S) :
    2 * 2 ^ p'.eval (encA x).length *
        #{r : Fin (2 * p'.eval (encA x).length) → Bool | A' (x, List.ofFn r) = true} <
      2 ^ (2 * p'.eval (encA x).length) := by
  simpa [hx] using h x

open Classical in
/-- On a yes-instance, the erring strings are the rejecting ones. -/
private theorem reject_bound (h : SmallOfflineError encA S p' A') {x : α} (hx : x ∈ S) :
    2 * 2 ^ p'.eval (encA x).length *
        #{r : Fin (2 * p'.eval (encA x).length) → Bool | A' (x, List.ofFn r) = false} <
      2 ^ (2 * p'.eval (encA x).length) := by
  simpa [hx] using h x

/-- **Goldreich's promise problem `Π′`** [Goldreich2007Draft, Exercise 6.11]: the yes-instances are
the pairs `(x, r′)` with `|r′| = p′(|x|)` such that `A′(x, r′ r″) = 1` for every `r″` of length
`|r′|`; the no-instances are the pairs `(x, r′)` with `x ∉ S`. The error bound `h` makes the two
sets disjoint. -/
def coinSplit (h : SmallOfflineError encA S p' A') : PromiseProblem (α × List Bool) where
  yes := {q | q.2.length = p'.eval (encA q.1).length ∧
    ∀ r'' : List Bool, r''.length = q.2.length → A' (q.1, q.2 ++ r'') = true}
  no := {q | q.1 ∉ S}
  disjoint := by
    classical
    refine Set.disjoint_left.2 fun ⟨x, w⟩ ⟨hlen, hall⟩ hx => ?_
    change x ∉ S at hx
    change w.length = p'.eval (encA x).length at hlen
    change ∀ r'' : List Bool, r''.length = w.length → A' (x, w ++ r'') = true at hall
    obtain ⟨r', rfl⟩ := exists_ofFn_eq hlen
    have hlt := card_append_lt (fun w => A' (x, w) = true) (accept_bound h hx) r'
    rw [filter_true_of_mem fun r'' _ => hall _ (by simp), card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin] at hlt
    have := Nat.two_pow_pos (p'.eval (encA x).length)
    omega

@[simp] theorem mem_coinSplit_yes (h : SmallOfflineError encA S p' A') {x : α} {r' : List Bool} :
    (x, r') ∈ (coinSplit h).yes ↔ r'.length = p'.eval (encA x).length ∧
      ∀ r'' : List Bool, r''.length = r'.length → A' (x, r' ++ r'') = true :=
  Iff.rfl

@[simp] theorem mem_coinSplit_no (h : SmallOfflineError encA S p' A') {x : α} {r' : List Bool} :
    (x, r') ∈ (coinSplit h).no ↔ x ∉ S :=
  Iff.rfl

/-- **Goldreich's sampler on yes-instances** [Goldreich2007Draft, Exercise 6.11(1)]: for
`x ∈ S`, the pair `(x, r′)` with `r′` uniform in `{0,1}^{p′(|x|)}` is a yes-instance of `Π′` with
probability strictly greater than `1 / 2`. This is the bound of the illustration in the proof of
Theorem 6.9, for the explicit reduction of `rpReducibleWithError_coinSplit`. -/
theorem half_lt_toOuterMeasure_coinSplit_yes (h : SmallOfflineError encA S p' A') {x : α}
    (hx : x ∈ S) :
    1 / 2 < ((ProbComp.eval ((fun w => (x, w)) <$>
      BitString.sampleList (p'.eval (encA x).length))).toOuterMeasure
        (coinSplit h).yes).toReal := by
  classical
  simp only [ProbComp.eval_map, BitString.eval_sampleList]
  rw [BitString.toOuterMeasure_map_uniformList_toReal, lt_div_iff₀ (by positivity)]
  have hgood := lt_card_forall_not (fun w => A' (x, w) = false) (reject_bound h hx)
  have hsub : ({r' : Fin (p'.eval (encA x).length) → Bool |
      ∀ r'' : Fin (p'.eval (encA x).length) → Bool,
        ¬A' (x, List.ofFn r' ++ List.ofFn r'') = false} : Finset _) ⊆
      ({r' | (x, List.ofFn r') ∈ (coinSplit h).yes} : Finset (Fin _ → Bool)) := by
    intro r' hr'
    simp only [mem_filter, mem_univ, true_and] at hr' ⊢
    refine ⟨List.length_ofFn, fun r'' hr'' => ?_⟩
    obtain ⟨s, rfl⟩ := exists_ofFn_eq (hr''.trans List.length_ofFn)
    simpa using hr' s
  have h2 : (2 ^ p'.eval (encA x).length : ℝ) <
      2 * (#{r' : Fin (p'.eval (encA x).length) → Bool |
        (x, List.ofFn r') ∈ (coinSplit h).yes} : ℝ) := by
    exact_mod_cast hgood.trans_le (Nat.mul_le_mul_left 2 (card_le_card hsub))
  linarith

/-- **Goldreich, Exercise 6.11(1)** [Goldreich2007Draft]: mapping `x` to `(x, r′)`, for `r′`
uniform in `{0,1}^{p′(|x|)}`, is a one-sided error randomized Karp reduction of `S` to `Π′`. It
maps every `x ∉ S` to a no-instance of `Π′` with certainty and every `x ∈ S` to a yes-instance
with probability at least `1 / 2`; the strict bound `> 1 / 2` of the source for this sampler is
`half_lt_toOuterMeasure_coinSplit_yes`. This is the `RP` error orientation,
`RPReducibleWithError` between the complements (`rpReducibleWithError_compl_iff`). The reduction
only samples `r′`, so it needs no assumption on the running time of `A′`. -/
theorem rpReducibleWithError_coinSplit (h : SmallOfflineError encA S p' A') :
    RPReducibleWithError encA (encPair encA encBits) (fun _ => 1 / 2) (ofSet S)ᶜ
      (coinSplit h)ᶜ := by
  rw [rpReducibleWithError_compl_iff]
  refine ⟨fun x => (fun w => (x, w)) <$> BitString.sampleList (p'.eval (encA x).length),
    IsPPTOn.of_seeded
      ((ComputableInPolyTime.unary_eval p').comp (ComputableInPolyTime.encoding_length encA))
      ComputableInPolyTime.id',
    fun x hx q hq => ?_, fun x hx => (half_lt_toOuterMeasure_coinSplit_yes h hx).le⟩
  supp_cases hq [BitString.eval_sampleList, BitString.mem_support_uniformList_iff] with
    ⟨w, -, rfl⟩
  exact hx

/-- **Goldreich, Exercise 6.11(2)** [Goldreich2007Draft]: `Π′` is in the promise version of
`coRP`. On input `(x, r′)`, the algorithm rejects if `|r′| ≠ p′(|x|)`, and otherwise draws `r″`
uniformly from `{0,1}^{|r′|}` and outputs `A′(x, r′ r″)`. It accepts every yes-instance with
certainty, and rejects every no-instance with probability at least `1 / 2` (more than `1 / 2` on
inputs with `|r′| = p′(|x|)`). -/
theorem coinSplit_mem_PromiseCoRP
    (hA' : ComputableInPolyTime A' (encPair encA encBits) encBool)
    (h : SmallOfflineError encA S p' A') :
    coinSplit h ∈ PromiseCoRP (encPair encA encBits) := by
  classical
  let V : (α × List Bool) × List Bool → Bool := fun q =>
    (q.1.2.length == p'.eval (encA q.1.1).length) && A' (q.1.1, q.1.2 ++ q.2)
  have hV : ComputableInPolyTime V (encPair (encPair encA encBits) encBits) encBool := by
    polytime [V]
  rw [mem_PromiseCoRP_iff_exists_isPPTOn]
  refine ⟨fun q => (fun w => V (q, w)) <$> BitString.sampleList q.2.length,
    IsPPTOn.of_seeded ((ComputableInPolyTime.length_bits).comp (ComputableInPolyTime.snd _ _)) hV,
    fun ⟨x, r'⟩ ⟨hlen, hall⟩ hfalse => ?_, fun ⟨x, r'⟩ hx => ?_⟩
  · change r'.length = p'.eval (encA x).length at hlen
    change ∀ r'' : List Bool, r''.length = r'.length → A' (x, r' ++ r'') = true at hall
    supp_cases hfalse [BitString.eval_sampleList, BitString.mem_support_uniformList_iff] with
      ⟨w, hw, hVw⟩
    simp [V, hlen, hall w hw] at hVw
  · change x ∉ S at hx
    have hnot : Bool.not <$> ((fun w => V ((x, r'), w)) <$>
        BitString.sampleList r'.length) = (fun w => !V ((x, r'), w)) <$>
          BitString.sampleList r'.length := by
      simp [Functor.map_map]
    rw [hnot, probability_sampleList_verifier (fun q : (α × List Bool) × List Bool => !V q)]
    rw [le_div_iff₀ (by positivity)]
    by_cases hlen : r'.length = p'.eval (encA x).length
    · obtain ⟨s, rfl⟩ := exists_ofFn_eq hlen
      have hlt := card_append_lt (fun w => A' (x, w) = true) (accept_bound h hx) s
      have hsum := card_filter_add_card_filter_not (s := univ)
        fun r'' : Fin (p'.eval (encA x).length) → Bool =>
          A' (x, List.ofFn s ++ List.ofFn r'') = true
      rw [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hsum
      have hacc : acceptCount (fun q : (α × List Bool) × List Bool => !V q) (x, List.ofFn s)
          (List.ofFn s).length = #{r'' : Fin (p'.eval (encA x).length) → Bool |
            ¬A' (x, List.ofFn s ++ List.ofFn r'') = true} := by
        rw [acceptCount, List.length_ofFn]
        congr 1
        ext r''
        simp [V]
      rw [hacc, List.length_ofFn]
      have : (2 ^ p'.eval (encA x).length : ℝ) ≤ 2 * (#{r'' : Fin (p'.eval (encA x).length) →
          Bool | ¬A' (x, List.ofFn s ++ List.ofFn r'') = true} : ℝ) := by
        exact_mod_cast (by omega : 2 ^ p'.eval (encA x).length ≤ 2 * #{r'' : Fin
          (p'.eval (encA x).length) → Bool | ¬A' (x, List.ofFn s ++ List.ofFn r'') = true})
      linarith
    · have hacc : acceptCount (fun q : (α × List Bool) × List Bool => !V q) (x, r')
          r'.length = 2 ^ r'.length := by
        rw [acceptCount, filter_true_of_mem fun r'' _ => by simp [V, hlen], card_univ,
          Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      rw [hacc]
      push_cast
      have : (0 : ℝ) < 2 ^ r'.length := by positivity
      linarith

end Cslib.Complexity.PromiseProblem
