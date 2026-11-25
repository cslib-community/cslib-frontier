/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ZPP
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Computability.Complexity.Classes.P.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Combinatorics.MajorityVote
import CslibFrontier.Foundations.Data.BitString.WordCount
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Set.Finite.List

/-!
# Error thresholds of BPP, RP and ZPP

The thresholds `2 / 3` of `BPP` (`Cslib.Complexity.BPP`) and `1 / 2` of `RP` and `ZPP`
(`Cslib.Complexity.RP`, `Cslib.Complexity.ZPP`) can be replaced by any threshold that is
inverse-polynomially better than a coin flip, and by thresholds exponentially close to certainty.
The relaxed classes take the threshold as a function of the length `n` of the encoded instance:

* `Cslib.Complexity.BPPWithError enc ε`: decided in polynomial time with error at most `ε(n)` on
  every instance, the class `BPP_ε` of [Goldreich, Exercise 6.4][Goldreich2007Draft];
* `Cslib.Complexity.RPWithSuccess enc ρ`: members accepted with probability at least `ρ(n)` and
  non-members never accepted, the class `RP_ρ` of [Goldreich, Exercise 6.5][Goldreich2007Draft];
* `Cslib.Complexity.ZPPWithSuccess enc ρ`: answers never wrong, and an answer other than `none` with
  probability at least `ρ(n)`, the class `ZPP_ρ` of [Goldreich, Exercise 6.6][Goldreich2007Draft].

As everywhere in this library, the machines are deterministic polynomial-time verifiers reading a
random string of polynomial length `p(n)`, and probabilities are counts over these strings
(`Cslib.Complexity.acceptCount`). Thresholds are real numbers.

## Weak-gap amplification

The strict majority of `2 q(n) ^ 2` runs on independent blocks of random bits
(`Cslib.Complexity.repeatMajority`) turns success probability `1 / 2 + 1 / q(n)` into success
probability `4 / 5`: by the exponential-moment bound
`Cslib.five_mul_card_filter_card_filter_le_sq_le`, at most a fifth of the random strings give at
most `q(n) ^ 2` right runs (`Cslib.Complexity.boundedErrorAt_repeatMajority_sq`). The disjunction of
`q(n)` runs (`Cslib.Complexity.repeatAny`) turns acceptance probability `1 / q(n)` into acceptance
probability `1 / 2`, since `(1 - 1 / q) ^ q ≤ 1 / 2`
(`Cslib.Complexity.two_pow_le_two_mul_acceptCount_repeatAny`). Both trial counts depend on the input
length through the polynomial `q`. Combined with the exponential error reduction for `BPP` and `RP`
and with `ZPP = RP ∩ coRP`, this gives the following.

## Main results

* `Cslib.Complexity.BPPWithError_subset_BPP`: an error at most `1 / 2 - 1 / q(n)` at all
  sufficiently large lengths gives `BPP`; the finitely many shorter instances are decided by table
  lookup.
* `Cslib.Complexity.BPP_subset_BPPWithError`, `Cslib.Complexity.RP_subset_RPWithSuccess`,
  `Cslib.Complexity.ZPP_subset_ZPPWithSuccess`: error `2 ^ (-q(n))`.
* `Cslib.Complexity.RPWithSuccess_subset_RP`, `Cslib.Complexity.ZPPWithSuccess_subset_ZPP`:
  success probability `1 / q(n)` gives `RP`, resp. `ZPP`.
* `Cslib.Complexity.BPPWithError_eq_BPP`, `Cslib.Complexity.RPWithSuccess_inv_eq_RP`,
  `Cslib.Complexity.ZPPWithSuccess_inv_eq_ZPP`, `Cslib.Complexity.ZPP_eq_ZPPWithSuccess`:
  Goldreich, Exercises 6.4(1), 6.5(1), 6.6(1) and 6.6(2).
* `Cslib.Complexity.setOf_exists_BPPWithError_rpow_eq_BPP`: Arora–Barak, Lemma 7.9, with the
  printed bound required from some length on.
* `Cslib.Complexity.setOf_exists_BPPWithError_rpow_subset_two_rpow`: Arora–Barak, Theorem 7.10.
* `Cslib.Complexity.RPWithSuccess_succ_rpow_subset_one_sub_two_rpow`: Arora–Barak, Theorem 7.12.

## Corrections of the sources

* Arora–Barak, Lemma 7.9 and Theorem 7.10 require success probability `1 / 2 + |x| ^ (-c)` on
  every string. This is impossible whenever `|x| ^ c < 2`, in particular at length `1`, and
  undefined at length `0`, so the class `BPP_{n^{-c}}` as printed misses every problem with such
  instances. We require the printed bound only from some length on; this class is exactly `BPP`
  (`Cslib.Complexity.setOf_exists_BPPWithError_rpow_eq_BPP`). Scaling to `1 / 2 + (n + 1) ^ (-c)`
  on all instances does not repair the statement: an instance with the empty encoding, such as the
  empty string under `encBits`, would still need success probability `3 / 2`. Bounds of this kind
  at all lengths are instances of `Cslib.Complexity.BPPWithError_subset_BPP`. Theorem 7.12 is
  stated with `(n + 1) ^ (-c)`, which is at most `1`, in place of the printed `n ^ (-c)`, which is
  undefined at `n = 0`.
* Goldreich, Exercise 6.4(1) is stated for every positive polynomial `p`, with
  `ε(n) = 1 / 2 - 1 / p(n)` taking values in `[0, 1]`. For `p = 2`, the class `BPP_0` is `P`, so the
  equality would say `P = BPP`, which is open. We assume `p(n) > 2` for every `n`. Likewise, for
  `p = 1` the classes `RP_1` and `ZPP_1` of Exercises 6.5(1) and 6.6(1) are `P`, and the equalities
  would say `P = RP` and `P = ZPP`; we assume `p(n) ≥ 2`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, draft of
  2007-01-08][AroraBarak07], Section 7.4.1, Lemma 7.9 and Theorems 7.10 and 7.12 (printed pages
  121–122, PDF pages 137–138).
* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft `r3.pdf` of
  February 2007][Goldreich2007Draft], Exercises 6.4–6.6 (printed page 254, PDF page 52).
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Filter Polynomial Turing.MultiTapeTM

variable {α : Type}

/-! ### The relaxed classes -/

/-- `V` decides `A` with error at most `ε(n)`, using random strings whose length is `p` evaluated at
the length `n` of the encoded instance: members are accepted, and non-members rejected, on all but
at most an `ε(n)` fraction of the random strings. -/
def DecidesWithErrorAtMost (enc : α ↪ List Bool) (ε : ℕ → ℝ) (p : Polynomial ℕ)
    (V : α × List Bool → Bool) (A : Set α) : Prop :=
  ∀ a, (a ∈ A → (1 - ε (enc a).length) * 2 ^ p.eval (enc a).length ≤
      (acceptCount V a (p.eval (enc a).length) : ℝ)) ∧
    (a ∉ A → (acceptCount V a (p.eval (enc a).length) : ℝ) ≤
      ε (enc a).length * 2 ^ p.eval (enc a).length)

/-- The problems decided with error at most `ε(n)` by polynomial-time machines reading
polynomially long random strings, where `n` is the length of the encoded instance: the class
`BPP_ε` of [Goldreich, Exercise 6.4][Goldreich2007Draft]. -/
def BPPWithError (enc : α ↪ List Bool) (ε : ℕ → ℝ) : Set (Set α) :=
  {A | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧ DecidesWithErrorAtMost enc ε p V A}

/-- `V` decides `A` with one-sided error and success probability at least `ρ(n)`, using random
strings whose length is `p` evaluated at the length `n` of the encoded instance: members are
accepted on at least a `ρ(n)` fraction of the random strings, and non-members on none. -/
def DecidesWithOneSidedSuccess (enc : α ↪ List Bool) (ρ : ℕ → ℝ) (p : Polynomial ℕ)
    (V : α × List Bool → Bool) (A : Set α) : Prop :=
  ∀ a, (a ∈ A → ρ (enc a).length * 2 ^ p.eval (enc a).length ≤
      (acceptCount V a (p.eval (enc a).length) : ℝ)) ∧
    (a ∉ A → ∀ r : Fin (p.eval (enc a).length) → Bool, V (a, List.ofFn r) = false)

/-- The problems decided with one-sided error and success probability at least `ρ(n)` by
polynomial-time machines reading polynomially long random strings: the class `RP_ρ` of
[Goldreich, Exercise 6.5][Goldreich2007Draft]. -/
def RPWithSuccess (enc : α ↪ List Bool) (ρ : ℕ → ℝ) : Set (Set α) :=
  {A | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧ DecidesWithOneSidedSuccess enc ρ p V A}

/-- `V` decides `A` with zero error and success probability at least `ρ(n)`, using random strings
whose length is `p` evaluated at the length `n` of the encoded instance: an answer `some b` is
always right, `b = true` exactly when `a ∈ A`, and at least a `ρ(n)` fraction of the random strings
give an answer. -/
def DecidesWithZeroErrorSuccess (enc : α ↪ List Bool) (ρ : ℕ → ℝ) (p : Polynomial ℕ)
    (V : α × List Bool → Option Bool) (A : Set α) : Prop :=
  ∀ a, (∀ r : Fin (p.eval (enc a).length) → Bool, ∀ b, V (a, List.ofFn r) = some b →
      (b = true ↔ a ∈ A)) ∧
    ρ (enc a).length * 2 ^ p.eval (enc a).length ≤
      (acceptCount (fun x => (V x).isSome) a (p.eval (enc a).length) : ℝ)

/-- The problems decided with zero error and success probability at least `ρ(n)` by
polynomial-time machines reading polynomially long random strings: the class `ZPP_ρ` of
[Goldreich, Exercise 6.6][Goldreich2007Draft]. -/
def ZPPWithSuccess (enc : α ↪ List Bool) (ρ : ℕ → ℝ) : Set (Set α) :=
  {A | ∃ (p : Polynomial ℕ) (V : α × List Bool → Option Bool),
    ComputableInPolyTime V (encPair enc encBits) (encOption encBool) ∧
      DecidesWithZeroErrorSuccess enc ρ p V A}

variable {enc : α ↪ List Bool}

/-! ### Numeric bridges -/

/-- A count `c` with `2 ^ q c ≤ 2 ^ m` is at most a `2 ^ (-q)` fraction of `2 ^ m`. -/
private theorem cast_le_inv_two_pow_mul {q m c : ℕ} (h : 2 ^ q * c ≤ 2 ^ m) :
    (c : ℝ) ≤ ((2 : ℝ) ^ q)⁻¹ * 2 ^ m := by
  rw [inv_mul_eq_div, le_div_iff₀ (by positivity), mul_comm]
  exact_mod_cast h

/-- If the rejections are at most a `2 ^ (-q)` fraction, the acceptances are at least a
`1 - 2 ^ (-q)` fraction. -/
private theorem one_sub_inv_two_pow_mul_le {q m c : ℕ} (hc : c ≤ 2 ^ m)
    (h : 2 ^ q * (2 ^ m - c) ≤ 2 ^ m) : (1 - ((2 : ℝ) ^ q)⁻¹) * 2 ^ m ≤ c := by
  have := cast_le_inv_two_pow_mul h
  rw [Nat.cast_sub hc] at this; push_cast at this; linarith

/-- A density of at least `1 / 2 + 1 / q` among `2 ^ m` strings, in natural-number form. -/
private theorem two_mul_le_mul_sub_of_le {m g q : ℕ} (hq : 0 < q)
    (h : ((1 : ℝ) / 2 + 1 / q) * 2 ^ m ≤ g) : 2 * 2 ^ m ≤ q * (2 * g - 2 ^ m) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hpos : (0 : ℝ) < 2 ^ m := by positivity
  have hg : 2 ^ m ≤ 2 * g := by
    exact_mod_cast (show (2 : ℝ) ^ m ≤ 2 * g by nlinarith [div_pos one_pos hq'])
  suffices ((2 * 2 ^ m : ℕ) : ℝ) ≤ ((q * (2 * g - 2 ^ m) : ℕ) : ℝ) by exact_mod_cast this
  push_cast [Nat.cast_sub hg]
  nlinarith [show (1 : ℝ) / q * 2 ^ m * q = 2 ^ m by field_simp]

/-- `x ^ (-c) ≥ x ^ (-⌈c⌉₊)` for `x ≥ 1`. -/
private theorem inv_pow_ceil_le_rpow_neg {x : ℝ} (hx : 1 ≤ x) (c : ℝ) :
    (x ^ ⌈c⌉₊)⁻¹ ≤ x ^ (-c) := by
  rw [← Real.rpow_natCast, ← Real.rpow_neg (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hx (neg_le_neg (Nat.le_ceil c))

/-- `2 ^ (-x ^ ⌈d⌉₊) ≤ 2 ^ (-x ^ d)` for `x ≥ 1`. -/
private theorem inv_two_pow_pow_ceil_le {x : ℝ} (hx : 1 ≤ x) (d : ℝ) :
    ((2 : ℝ) ^ (x ^ ⌈d⌉₊))⁻¹ ≤ (2 : ℝ) ^ (-x ^ d) := by
  rw [← Real.rpow_neg_one, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (neg_le_neg (Real.rpow_le_rpow_of_exponent_le hx (Nat.le_ceil d)))

/-- The polynomial `(X + 1) ^ k` is positive and evaluates to `(n + 1) ^ k`. -/
private theorem cast_eval_X_add_one_pow (k n : ℕ) :
    ((((X + 1) ^ k : Polynomial ℕ).eval n : ℕ) : ℝ) = ((n : ℝ) + 1) ^ k := by
  simp

/-- `2 ^ ((X + 1) ^ k)(n) = 2 ^ ((n + 1) ^ k)`, the exponent read as a real number. -/
private theorem eval_two_pow_X_add_one_pow (k n : ℕ) :
    (2 : ℝ) ^ (((X + 1) ^ k : Polynomial ℕ).eval n) = (2 : ℝ) ^ (((n : ℝ) + 1) ^ k) := by
  rw [← Real.rpow_natCast, cast_eval_X_add_one_pow]

/-! ### `BPP` -/

/-- **Weak-gap majority at one instance.** If a single run of `V` gives `b` on a fraction at least
`1 / 2 + 1 / q(n)` of the random strings, that is `2 · 2 ^ p(n) ≤ q(n) (2 G - 2 ^ p(n))` for the
number `G` of such strings, then the strict majority of `2 q(n) ^ 2` runs on independent blocks of
random bits gives `b` with bounded error. -/
theorem boundedErrorAt_repeatMajority_sq {q p : Polynomial ℕ} {V : α × List Bool → Bool} {a : α}
    {b : Bool}
    (h : 2 * 2 ^ p.eval (enc a).length ≤ q.eval (enc a).length *
      (2 * (univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        V (a, List.ofFn r) = b).card - 2 ^ p.eval (enc a).length)) :
    BoundedErrorAt enc (2 * q ^ 2 * p) (repeatMajority enc (q ^ 2) p V) a b := by
  have hsq : (q ^ 2).eval (enc a).length = q.eval (enc a).length ^ 2 := eval_pow _
  unfold BoundedErrorAt
  rw [show ((2 * q ^ 2 * p : Polynomial ℕ).eval (enc a).length) =
      2 * (q ^ 2).eval (enc a).length * p.eval (enc a).length by simp only [eval_mul, eval_ofNat]]
  refine BitString.two_mul_two_pow_le_of_four_mul_card_filter_not_le
    (fun x => repeatMajority enc (q ^ 2) p V (a, List.ofFn x) = b) ?_
  rw [show (univ.filter fun x : BitString (2 * (q ^ 2).eval (enc a).length *
        p.eval (enc a).length) => ¬repeatMajority enc (q ^ 2) p V (a, List.ofFn x) = b) =
      univ.filter fun x => repeatMajority enc (q ^ 2) p V (a, List.ofFn x) = !b from
    filter_congr fun _ _ => by cases b <;> simp]
  have h1 := card_filter_repeatMajority_eq_not_le (enc := enc) (r := q ^ 2) (p := p) (V := V) a b
  have h2 := BitString.five_mul_card_filter_card_filter_block_le (q := q.eval (enc a).length)
    (fun s => V (a, List.ofFn s) = b) h
  rw [← hsq] at h2
  exact (Nat.mul_le_mul_right _ (by decide : 4 ≤ 5)).trans ((Nat.mul_le_mul_left 5 h1).trans h2)

/-- **Weak-gap amplification for `BPP`.** If, at all sufficiently large lengths `n`, the error
bound `ε(n)` is at most `1 / 2 - 1 / q(n)` for a polynomial `q`, then `BPP_ε ⊆ BPP`. The strict
majority of `2 q(n) ^ 2` runs decides the problem with bounded error at these lengths, and the
finitely many instances of the other lengths are decided by table lookup. -/
theorem BPPWithError_subset_BPP {ε : ℕ → ℝ} (q : Polynomial ℕ)
    (hq : ∀ᶠ n in atTop, 0 < q.eval n ∧ ε n ≤ 1 / 2 - 1 / ((q.eval n : ℕ) : ℝ)) :
    BPPWithError enc ε ⊆ BPP enc := by
  rintro A ⟨p, V, hV, hA⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 hq
  let V' : α × List Bool → Bool := fun x =>
    if decide (N ≤ (enc x.1).length) then repeatMajority enc (q ^ 2) p V x else false
  have hV' : ComputableInPolyTime V' (encPair enc encBits) encBool :=
    ComputableInPolyTime.ite'
      (ComputableInPolyTime.unary_le' (.const N)
        ((ComputableInPolyTime.encoding_length enc).comp (.fst _ _)))
      (computableInPolyTime_repeatMajority hV _ _) (.const false)
  have hlong (a : α) (hN' : N ≤ (enc a).length) (b : Bool) (hb : b = true ↔ a ∈ A) :
      BoundedErrorAt enc (2 * q ^ 2 * p) V' a b := by
    obtain ⟨hq₀, hε⟩ := hN _ hN'
    have hsum := acceptCount_add_card_filter_eq_false (V := V) (a := a)
      (n := p.eval (enc a).length)
    have hp2 : (0 : ℝ) < 2 ^ p.eval (enc a).length := pow_pos two_pos _
    refine (boundedErrorAt_repeatMajority_sq (V := V) (two_mul_le_mul_sub_of_le hq₀ ?_)).congr
      fun r => by simp [V', hN']
    cases b
    · have := (hA a).2 (by simpa using hb)
      have hcast : ((univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
          V (a, List.ofFn r) = false).card : ℝ) =
          2 ^ p.eval (enc a).length - acceptCount V a (p.eval (enc a).length) := by
        rw [eq_sub_iff_add_eq, add_comm]; exact_mod_cast hsum
      rw [hcast]; nlinarith
    · have := (hA a).1 (by simpa using hb)
      change _ ≤ ((acceptCount V a _ : ℕ) : ℝ); nlinarith
  have hA' : {a | a ∈ A ∧ N ≤ (enc a).length} ∈ BPP enc :=
    ⟨2 * q ^ 2 * p, V', hV', fun a => ⟨fun ha => hlong a ha.2 true (iff_of_true rfl ha.1),
      fun ha => if hN' : N ≤ (enc a).length then
        hlong a hN' false (iff_of_false Bool.false_ne_true fun h => ha ⟨h, hN'⟩)
      else by simp [BoundedErrorAt, V', hN']⟩⟩
  have hfin : (A ∩ {a | (enc a).length < N}).Finite :=
    ((List.finite_length_lt Bool N).preimage_embedding enc).subset Set.inter_subset_right
  suffices A = {a | a ∈ A ∧ N ≤ (enc a).length} ∪ (A ∩ {a | (enc a).length < N}) from
    this ▸ union_mem_BPP hA' (P_subset_BPP hfin.mem_P)
  ext a; simp only [Set.mem_union, Set.mem_inter_iff]
  exact ⟨fun ha => (le_or_gt N (enc a).length).imp (⟨ha, ·⟩) (⟨ha, ·⟩),
    fun h => h.elim (·.1) (·.1)⟩

/-- **Exponential error reduction into `BPP_ε`.** If `2 ^ (-q(n)) ≤ ε(n)` for a polynomial `q`, then
`BPP ⊆ BPP_ε`. -/
theorem BPP_subset_BPPWithError {ε : ℕ → ℝ} (q : Polynomial ℕ)
    (hq : ∀ n, ((2 : ℝ) ^ q.eval n)⁻¹ ≤ ε n) : BPP enc ⊆ BPPWithError enc ε := fun A hA => by
  obtain ⟨p, V, hV, h⟩ := mem_BPP_iff_forall_decidesWithErrorExponent.1 hA q
  refine ⟨p, V, hV, fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · have := one_sub_inv_two_pow_mul_le acceptCount_le_two_pow
      (errorExponentAt_true_iff.1 ((h a).1 ha))
    nlinarith [hq (enc a).length, pow_pos (two_pos : (0 : ℝ) < 2) (p.eval (enc a).length)]
  · have := cast_le_inv_two_pow_mul (errorExponentAt_false_iff.1 ((h a).2 ha))
    nlinarith [hq (enc a).length, pow_pos (two_pos : (0 : ℝ) < 2) (p.eval (enc a).length)]

/-- **[Goldreich, Exercise 6.4(1)][Goldreich2007Draft]**: for a polynomial `p` with `p(n) > 2` for
every `n`, and `ε(n) = 1 / 2 - 1 / p(n)`, the class `BPP_ε` equals `BPP`, for every encoding of the
instances. Goldreich states the exercise for every positive polynomial; for `p = 2` the class
`BPP_0` is `P`, and the equality would assert the open `P = BPP`; we assume `p(n) > 2`. -/
theorem BPPWithError_eq_BPP {p : Polynomial ℕ} (hp : ∀ n, 2 < p.eval n) :
    BPPWithError enc (fun n => 1 / 2 - 1 / ((p.eval n : ℕ) : ℝ)) = BPP enc := by
  refine (BPPWithError_subset_BPP p (Eventually.of_forall fun n =>
    ⟨by have := hp n; omega, le_rfl⟩)).antisymm (BPP_subset_BPPWithError 3 fun n => ?_)
  have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3)
    (by exact_mod_cast hp n : (3 : ℝ) ≤ p.eval n)
  simp only [eval_ofNat]; linarith [show ((2 : ℝ) ^ 3)⁻¹ = 1 / 8 by norm_num]

/-- **[Arora–Barak, Lemma 7.9][AroraBarak07], with the printed bound from some length on**: for
`c > 0`, the problems decided in polynomial time with success probability at least
`1 / 2 + n ^ (-c)` on all instances of every length `n ≥ N`, for some `N`, are exactly `BPP`, for
every encoding of the instances. The draft requires the bound on every string, which is impossible
whenever `n ^ c < 2`; below `N` nothing is required here (error at most `1`). -/
theorem setOf_exists_BPPWithError_rpow_eq_BPP {c : ℝ} (hc : 0 < c) :
    {A | ∃ N : ℕ, A ∈ BPPWithError enc (fun n => if n < N then 1 else 1 / 2 - (n : ℝ) ^ (-c))} =
      BPP enc := by
  ext A; constructor
  · rintro ⟨N, hA⟩
    refine BPPWithError_subset_BPP (X ^ ⌈c⌉₊) (eventually_atTop.2 ⟨max N 1, fun n hn =>
      ⟨by simp only [eval_pow, eval_X]; exact pow_pos (by omega) _, ?_⟩⟩) hA
    have := inv_pow_ceil_le_rpow_neg (by exact_mod_cast le_of_max_le_right hn : (1 : ℝ) ≤ n) c
    simp only [show ¬n < N by omega, ↓reduceIte, eval_pow, eval_X, Nat.cast_pow, one_div]
    linarith
  · intro hA
    obtain ⟨N, hN⟩ := eventually_atTop.1 (((tendsto_rpow_neg_atTop hc).comp
      tendsto_natCast_atTop_atTop).eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)))
    refine ⟨N, BPP_subset_BPPWithError 2 (fun n => ?_) hA⟩
    simp only [eval_ofNat]
    split_ifs with hn
    · norm_num
    · linarith [show (n : ℝ) ^ (-c) ≤ 1 / 4 from hN n (by omega),
        show ((2 : ℝ) ^ 2)⁻¹ = 1 / 4 by norm_num]

/-- **[Arora–Barak, Theorem 7.10][AroraBarak07]** (error reduction), with the hypothesis of
Lemma 7.9 read from some length on (`Cslib.Complexity.setOf_exists_BPPWithError_rpow_eq_BPP`): for
`c > 0`, a problem decided in polynomial time with success probability at least `1 / 2 + n ^ (-c)`
on all instances of every length `n ≥ N` is, for every `d`, decided in polynomial time with success
probability at least `1 - 2 ^ (-(n + 1) ^ d)` on every instance, where `n` is the length of the
encoded instance. The draft states the error `2 ^ (-|x| ^ d)`, which is trivial at length `0`. -/
theorem setOf_exists_BPPWithError_rpow_subset_two_rpow {c : ℝ} (hc : 0 < c) (d : ℝ) :
    {A | ∃ N : ℕ, A ∈ BPPWithError enc (fun n => if n < N then 1 else 1 / 2 - (n : ℝ) ^ (-c))} ⊆
      BPPWithError enc (fun n => (2 : ℝ) ^ (-((n : ℝ) + 1) ^ d)) := by
  rw [setOf_exists_BPPWithError_rpow_eq_BPP hc]
  exact BPP_subset_BPPWithError ((X + 1) ^ ⌈d⌉₊) fun n => by
    rw [eval_two_pow_X_add_one_pow]
    exact inv_two_pow_pow_ceil_le (by linarith [n.cast_nonneg (α := ℝ)]) d

/-! ### `RP` -/

/-- **Repetition at inverse-polynomial success.** If a single run of `V` accepts `a` on at least a
`1 / q(n)` fraction of the random strings, the disjunction of `q(n)` runs on independent blocks of
random bits accepts on at least half of them, since `(1 - 1 / q) ^ q ≤ 1 / 2`. -/
theorem two_pow_le_two_mul_acceptCount_repeatAny {q p : Polynomial ℕ}
    {V : α × List Bool → Bool} {a : α}
    (h : 2 ^ p.eval (enc a).length ≤
      q.eval (enc a).length * acceptCount V a (p.eval (enc a).length)) :
    2 ^ (q * p).eval (enc a).length ≤
      2 * acceptCount (repeatAny enc q p V) a ((q * p).eval (enc a).length) := by
  have hsum := acceptCount_add_card_filter_eq_false (V := repeatAny enc q p V) (a := a)
    (n := (q * p).eval (enc a).length)
  have hrej := card_filter_repeatAny_eq_false (enc := enc) (q := q) (p := p) (V := V) a
  have hone := acceptCount_add_card_filter_eq_false (V := V) (a := a) (n := p.eval (enc a).length)
  have hc := acceptCount_le_two_pow (V := V) (a := a) (n := p.eval (enc a).length)
  rw [eval_mul] at hsum ⊢
  set k := q.eval (enc a).length; set m := p.eval (enc a).length; set c := acceptCount V a m
  set F := (univ.filter fun u : Fin m → Bool => V (a, List.ofFn u) = false).card
  have hpos : (0 : ℝ) < 2 ^ m := by positivity
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = c / 2 ^ m := ⟨_, rfl⟩
  have hx₁ : x ≤ 1 := by rw [hx, div_le_one hpos]; exact_mod_cast hc
  have hkx : (1 : ℝ) ≤ k * x := by
    rw [hx, ← mul_div_assoc, le_div_iff₀ hpos, one_mul]; exact_mod_cast h
  have hB := Cslib.one_sub_pow_mul_one_add_mul_le_one (by rw [hx]; positivity) hx₁ k
  have hFr : (F : ℝ) = 2 ^ m * (1 - x) := by
    rw [hx, show F = 2 ^ m - c by omega, Nat.cast_sub hc]; push_cast; field_simp
  have hpow : 2 * F ^ k ≤ 2 ^ (k * m) := by
    suffices (2 : ℝ) * (F : ℝ) ^ k ≤ (2 : ℝ) ^ (k * m) by exact_mod_cast this
    rw [hFr, mul_pow, ← pow_mul, mul_comm m]
    nlinarith [pow_nonneg (show 0 ≤ 1 - x by linarith) k, pow_pos hpos k,
      pow_pos (two_pos : (0 : ℝ) < 2) (k * m)]
  omega

/-- **Inverse-polynomial success gives `RP`.** If `ρ(n) ≥ 1 / q(n) > 0` for a polynomial `q`, then
`RP_ρ ⊆ RP`: the disjunction of `q(n)` runs accepts members on at least half of the random
strings. -/
theorem RPWithSuccess_subset_RP {ρ : ℕ → ℝ} (q : Polynomial ℕ)
    (hq : ∀ n, 0 < q.eval n ∧ 1 / ((q.eval n : ℕ) : ℝ) ≤ ρ n) : RPWithSuccess enc ρ ⊆ RP enc := by
  rintro A ⟨p, V, hV, h⟩
  refine ⟨q * p, repeatAny enc q p V, computableInPolyTime_repeatAny hV q p,
    fun a => ⟨fun ha => two_pow_le_two_mul_acceptCount_repeatAny ?_, fun ha => ?_⟩⟩
  · obtain ⟨hq₀, hρ⟩ := hq (enc a).length
    have hq' : (0 : ℝ) < q.eval (enc a).length := by exact_mod_cast hq₀
    have h1 := (mul_le_mul_of_nonneg_right hρ (by positivity)).trans ((h a).1 ha)
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hq', mul_comm] at h1
    exact_mod_cast h1
  · rw [eval_mul]; intro x
    rw [← Bool.not_eq_true, repeatAny_ofFn_eq_true_iff]
    simpa using fun i => (h a).2 ha (BitString.block x i)

/-- **Exponential error reduction into `RP_ρ`.** If `ρ(n) ≤ 1 - 2 ^ (-q(n))` for a polynomial `q`,
then `RP ⊆ RP_ρ`. -/
theorem RP_subset_RPWithSuccess {ρ : ℕ → ℝ} (q : Polynomial ℕ)
    (hq : ∀ n, ρ n ≤ 1 - ((2 : ℝ) ^ q.eval n)⁻¹) : RP enc ⊆ RPWithSuccess enc ρ := fun A hA => by
  obtain ⟨p, V, hV, h⟩ := mem_RP_iff_forall_decidesWithOneSidedErrorExponent.1 hA q
  refine ⟨p, V, hV, fun a => ⟨fun ha => ?_, (h a).2⟩⟩
  have := one_sub_inv_two_pow_mul_le acceptCount_le_two_pow
    (errorExponentAt_true_iff.1 ((h a).1 ha))
  nlinarith [hq (enc a).length, pow_pos (two_pos : (0 : ℝ) < 2) (p.eval (enc a).length)]

/-- **[Goldreich, Exercise 6.5(1)][Goldreich2007Draft]**: for a polynomial `p` with `p(n) ≥ 2` for
every `n`, the class `RP_{1/p}` equals `RP`, for every encoding of the instances. Goldreich states
the exercise for every positive polynomial; for `p = 1` the class `RP_1` is `P`, and
the equality would assert the open `P = RP`; we assume `p(n) ≥ 2`. -/
theorem RPWithSuccess_inv_eq_RP {p : Polynomial ℕ} (hp : ∀ n, 2 ≤ p.eval n) :
    RPWithSuccess enc (fun n => 1 / ((p.eval n : ℕ) : ℝ)) = RP enc := by
  refine (RPWithSuccess_subset_RP p fun n => ⟨by have := hp n; omega, le_rfl⟩).antisymm
    (RP_subset_RPWithSuccess 1 fun n => ?_)
  have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
    (by exact_mod_cast hp n : (2 : ℝ) ≤ p.eval n)
  simp only [eval_one, pow_one]; linarith

/-- **[Arora–Barak, Theorem 7.12][AroraBarak07]** (error reduction for `RP`): a problem decided in
polynomial time with one-sided error and success probability at least `(n + 1) ^ (-c)` is, for every
`d`, decided in polynomial time with one-sided error and success probability at least
`1 - 2 ^ (-(n + 1) ^ d)`, where `n` is the length of the encoded instance. The draft writes `n` in
place of `n + 1`; at `n = 0` its bounds are undefined, resp. trivial. -/
theorem RPWithSuccess_succ_rpow_subset_one_sub_two_rpow (c d : ℝ) :
    RPWithSuccess enc (fun n => ((n : ℝ) + 1) ^ (-c)) ⊆
      RPWithSuccess enc (fun n => 1 - (2 : ℝ) ^ (-((n : ℝ) + 1) ^ d)) :=
  (RPWithSuccess_subset_RP ((X + 1) ^ ⌈c⌉₊) fun n => ⟨by simp, by
    rw [cast_eval_X_add_one_pow, ← inv_eq_one_div]
    exact inv_pow_ceil_le_rpow_neg (by linarith [n.cast_nonneg (α := ℝ)]) c⟩).trans
  (RP_subset_RPWithSuccess ((X + 1) ^ ⌈d⌉₊) fun n => by
    have := inv_two_pow_pow_ceil_le (by linarith [n.cast_nonneg (α := ℝ)] : (1 : ℝ) ≤ n + 1) d
    rw [eval_two_pow_X_add_one_pow]
    linarith)

/-! ### `ZPP` -/

/-- Accepting exactly on the answer `some true` decides the problem with one-sided error and the
same success probability: `ZPP_ρ ⊆ RP_ρ`. -/
theorem ZPPWithSuccess_subset_RPWithSuccess {ρ : ℕ → ℝ} :
    ZPPWithSuccess enc ρ ⊆ RPWithSuccess enc ρ := by
  rintro A ⟨p, V, hV, h⟩
  refine ⟨p, fun x => (V x).getD false, ComputableInPolyTime.optionGetDWithInput hV (.const false),
    fun a => ⟨fun ha => (h a).2.trans ?_, getD_false_eq_false (h a).1⟩⟩
  exact_mod_cast acceptCount_isSome_le_acceptCount_getD (h a).1 ha

/-- `ZPP_ρ` is closed under complement: negate the answers. -/
theorem compl_mem_ZPPWithSuccess {ρ : ℕ → ℝ} {A : Set α} (hA : A ∈ ZPPWithSuccess enc ρ) :
    Aᶜ ∈ ZPPWithSuccess enc ρ := by
  obtain ⟨p, V, hV, h⟩ := hA
  exact ⟨p, fun x => (V x).map Bool.not, by fun_prop, fun a =>
    ⟨map_not_eq_some_iff_mem_compl (h a).1, by simpa only [Option.isSome_map] using (h a).2⟩⟩

/-- **Inverse-polynomial success gives `ZPP`.** If `ρ(n) ≥ 1 / q(n) > 0` for a polynomial `q`, then
`ZPP_ρ ⊆ ZPP`: the problem and its complement are in `RP_ρ ⊆ RP`, and `ZPP = RP ∩ coRP`. -/
theorem ZPPWithSuccess_subset_ZPP {ρ : ℕ → ℝ} (q : Polynomial ℕ)
    (hq : ∀ n, 0 < q.eval n ∧ 1 / ((q.eval n : ℕ) : ℝ) ≤ ρ n) : ZPPWithSuccess enc ρ ⊆ ZPP enc :=
  fun _ hA => ZPP_eq_RP_inter_coRP ▸
    ⟨RPWithSuccess_subset_RP q hq (ZPPWithSuccess_subset_RPWithSuccess hA),
      RPWithSuccess_subset_RP q hq (ZPPWithSuccess_subset_RPWithSuccess
        (compl_mem_ZPPWithSuccess hA))⟩

/-- **Exponential error reduction into `ZPP_ρ`.** If `ρ(n) ≤ 1 - 2 ^ (-q(n))` for a polynomial `q`,
then `ZPP ⊆ ZPP_ρ` (`Cslib.Complexity.exists_zeroError_errorExponent_of_mem_RP_inter_coRP`). -/
theorem ZPP_subset_ZPPWithSuccess {ρ : ℕ → ℝ} (q : Polynomial ℕ)
    (hq : ∀ n, ρ n ≤ 1 - ((2 : ℝ) ^ q.eval n)⁻¹) : ZPP enc ⊆ ZPPWithSuccess enc ρ := fun A hA => by
  rw [ZPP_eq_RP_inter_coRP] at hA
  obtain ⟨p, V, hV, h⟩ := exists_zeroError_errorExponent_of_mem_RP_inter_coRP hA q
  refine ⟨p, V, hV, fun a => ⟨(h a).1, ?_⟩⟩
  have := one_sub_inv_two_pow_mul_le acceptCount_le_two_pow (errorExponentAt_true_iff.1 (h a).2)
  nlinarith [hq (enc a).length, pow_pos (two_pos : (0 : ℝ) < 2) (p.eval (enc a).length)]

/-- **[Goldreich, Exercise 6.6(1)][Goldreich2007Draft]**: for a polynomial `p` with `p(n) ≥ 2` for
every `n`, the class `ZPP_{1/p}` equals `ZPP`, for every encoding of the instances. Goldreich states
the exercise for every positive polynomial; for `p = 1` the class `ZPP_1` is `P`, and
the equality would assert the open `P = ZPP`; we assume `p(n) ≥ 2`. -/
theorem ZPPWithSuccess_inv_eq_ZPP {p : Polynomial ℕ} (hp : ∀ n, 2 ≤ p.eval n) :
    ZPPWithSuccess enc (fun n => 1 / ((p.eval n : ℕ) : ℝ)) = ZPP enc := by
  refine (ZPPWithSuccess_subset_ZPP p fun n => ⟨by have := hp n; omega, le_rfl⟩).antisymm
    (ZPP_subset_ZPPWithSuccess 1 fun n => ?_)
  have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
    (by exact_mod_cast hp n : (2 : ℝ) ≤ p.eval n)
  simp only [eval_one, pow_one]; linarith

/-- **[Goldreich, Exercise 6.6(2)][Goldreich2007Draft]**: for every positive polynomial `p`, the
class `ZPP` equals `ZPP_ρ` for `ρ(n) = 1 - 2 ^ (-p(n))`, for every encoding of the instances. -/
theorem ZPP_eq_ZPPWithSuccess {p : Polynomial ℕ} (hp : ∀ n, 0 < p.eval n) :
    ZPP enc = ZPPWithSuccess enc (fun n => 1 - ((2 : ℝ) ^ p.eval n)⁻¹) := by
  refine (ZPP_subset_ZPPWithSuccess p fun n => le_rfl).antisymm
    (ZPPWithSuccess_subset_ZPP 2 fun n => ⟨by simp, ?_⟩)
  have : ((2 : ℝ) ^ p.eval n)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num)
      ((pow_one (2 : ℝ)).symm.trans_le (pow_le_pow_right₀ (by norm_num) (hp n)))
  simp only [eval_ofNat, Nat.cast_ofNat]; linarith

end Cslib.Complexity
