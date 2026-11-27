/-
Copyright (c) 2026 Vincent Liew, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.LevelWeight
public import Mathlib.Data.Fintype.Perm
import CslibFrontier.Foundations.BooleanAnalysis.DegreeOneWeight
import CslibFrontier.Foundations.BooleanAnalysis.FriedgutKalaiNaor

/-!
# Condorcet elections and Kalai's proof of Arrow's Theorem

A *3-candidate Condorcet election* using a 2-candidate voting rule `f : (ι → Bool) → Bool` runs
the three pairwise elections `0` vs. `1`, `1` vs. `2` and `2` vs. `0` among the candidates
`Fin 3` [O'Donnell, Section 2.5][ODonnell2014]. Each voter `i` ranks the candidates by a
permutation `π i : Equiv.Perm (Fin 3)`, read as the position of each candidate, `0` at the top.
In the election of `c` against `c + 1` (addition in `Fin 3`), voter `i` votes `true` when ranking
`c` above `c + 1` (`BitString.condorcetVotes`), and society elects `c` when `f` returns `true`
on these votes. A candidate is a *Condorcet winner* when it wins both pairwise elections in which
it takes part (`BitString.IsCondorcetWinner`) [O'Donnell, Definition 2.55][ODonnell2014]. The
probability of a Condorcet winner under the *impartial culture assumption*, where every voter
independently picks one of the six rankings uniformly at random, is
`BitString.condorcetWinnerProb f`.

**Kalai's formula** (`BitString.condorcetWinnerProb_eq`) [O'Donnell, Theorem 2.56][ODonnell2014]:
reading `f` as signs `F = signVal ∘ f`, the probability of a Condorcet winner is
`3/4 - 3/4 Stab_{-1/3}[F]`. There is a Condorcet winner exactly when the three outcomes are not
all equal, and the not-all-equal predicate has Fourier expansion
`3/4 - 1/4 (w₁ w₂ + w₁ w₃ + w₂ w₃)`. The votes of different voters in two of the elections form
pairs of strings whose coordinate pairs are independent, with mean-zero signs of correlation
`-1/3`, so each of the three correlations is `Stab_{-1/3}[F]`.

Arrow's Theorem follows (`BitString.exists_eq_of_forall_exists_isCondorcetWinner`): if there is
always a Condorcet winner, then `Stab_{-1/3}[F] = -1/3`, so `f` is a literal `x ↦ b ⊕ x_i`
(`BitString.noiseStability_signVal_eq_iff_of_neg`), and unanimity forces the dictator `x ↦ x_i`.
Arrow's Theorem also allows a different unanimous rule in each election: if there is always a
Condorcet winner, the three rules agree (`BitString.eq_of_forall_exists_isCondorcetWinner`), so they
are one dictator (`BitString.exists_forall_eq_of_forall_exists_isCondorcetWinner`)
[O'Donnell, Exercise 2.51(a)][ODonnell2014]; `BitString.IsCondorcetWinner` takes one rule per
election, and the book's election using `f` is `fun _ => f`.
The same formula bounds the probability by `7/9 + 2/9 W^1[F]`
(`BitString.condorcetWinnerProb_le`) [O'Donnell, Corollary 2.59][ODonnell2014]. With the
Friedgut–Kalai–Naor theorem this gives the robust version: if the probability is at least
`1 - ε`, then `f` is `14409/2 · ε`-close to a dictator or a negated dictator
(`BitString.exists_hammingDist_xor_div_le_of_le_condorcetWinnerProb`)
[O'Donnell, Corollary 2.60][ODonnell2014].

## Main definitions

* `Cslib.BitString.condorcetVotes`: the votes in the election of candidate `c` against `c + 1`.
* `Cslib.BitString.IsCondorcetWinner`: a candidate wins both of its pairwise elections.
* `Cslib.BitString.condorcetWinnerProb`: the probability of a Condorcet winner under impartial
  culture.

## Main results

* `Cslib.BitString.condorcetWinnerProb_eq`: Kalai's formula, Theorem 2.56.
* `Cslib.BitString.exists_eq_of_forall_exists_isCondorcetWinner`: Arrow's Theorem, by Kalai's
  proof.
* `Cslib.BitString.condorcetWinnerProb_le`: Corollary 2.59.
* `Cslib.BitString.exists_hammingDist_xor_div_le_of_le_condorcetWinnerProb`: Corollary 2.60, with
  the explicit constant `14409/2`.
* `Cslib.BitString.eq_of_forall_exists_isCondorcetWinner`,
  `Cslib.BitString.exists_forall_eq_of_forall_exists_isCondorcetWinner`: Exercise 2.51(a), Arrow's
  Theorem for three different unanimous rules.

## Usage

Open `Cslib.BitString`. Rankings are permutations rather than
`Cslib.GameTheory.SocialChoice.Ranking`, a bundled strict order with no `Fintype` instance, so
that the impartial culture is the uniform expectation `𝔼 π : ι → Equiv.Perm (Fin 3)`. The book's
`+1` is `true` throughout: a vote `true` in the election of `c` against `c + 1` is a vote for `c`,
and the book's unanimity, `f(1, …, 1) = 1` and `f(-1, …, -1) = -1`, is
`f (fun _ => true) = true` and `f (fun _ => false) = false`. Arrow's Theorem uses only the first
half. Both the probability and
`Stab_{-1/3}[F]` are unchanged by negating `f`, so the sign convention of `signVal`
(`false ↦ 1`) does not matter. The book states Corollary 2.60 for probability exactly `1 - ε` and
closeness `O(ε)`; here the hypothesis is `1 - ε ≤ condorcetWinnerProb f`, and the constant is the
FKN constant `1601` of `BitString.exists_hammingDist_xor_div_le_of_le_levelWeight_one` times
`9/2`. Guilbaud's formula and Theorem 2.57 need Theorem 2.45, the limit of `Stab_ρ[Maj_n]`, and are
not part of this module ([#2131](https://github.com/cslib-community/cslib-frontier/issues/2131)).

The checked clients in
[CslibFrontierTests/BooleanAnalysisCondorcetElection.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisCondorcetElection.lean)
show that a dictator always gives a Condorcet winner, so Arrow's hypotheses can hold together,
and compute the probability `17/18` for the majority of three voters
[O'Donnell, Exercise 2.50][ODonnell2014].

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014], Section 2.5.
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

section Definitions

variable {ι : Type*}

/-- The votes in the pairwise election of candidate `c` against candidate `c + 1` of a
3-candidate Condorcet election: voter `i`, whose ranking `π i` gives the position of each
candidate (`0` at the top), votes `true`, for `c`, when ranking `c` above `c + 1`
[O'Donnell, Section 2.5][ODonnell2014]. -/
@[expose] def condorcetVotes (π : ι → Equiv.Perm (Fin 3)) (c : Fin 3) (i : ι) : Bool :=
  decide (π i c < π i (c + 1))

/-- Candidate `c` is a **Condorcet winner** of the 3-candidate Condorcet election that decides the
election of each `d` against `d + 1` by the voting rule `F d`, on the rankings `π`: it wins both
pairwise elections in which it takes part, the election of `c` against `c + 1`, where `F c`
returning `true` elects `c`, and that of `c - 1` against `c`, where `F (c - 1)` returning `false`
elects `c` [O'Donnell, Definition 2.55 and Exercise 2.51][ODonnell2014]. The book's election
using one rule `f` is `F = fun _ => f`. -/
@[expose] def IsCondorcetWinner (F : Fin 3 → (ι → Bool) → Bool) (π : ι → Equiv.Perm (Fin 3))
    (c : Fin 3) : Prop :=
  F c (condorcetVotes π c) = true ∧ F (c - 1) (condorcetVotes π (c - 1)) = false

instance (F : Fin 3 → (ι → Bool) → Bool) (π : ι → Equiv.Perm (Fin 3)) (c : Fin 3) :
    Decidable (IsCondorcetWinner F π c) :=
  instDecidableAnd

end Definitions

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The probability of a Condorcet winner in the 3-candidate Condorcet election using the voting
rule `f`, under the *impartial culture assumption*: every voter independently ranks the
candidates by one of the six permutations, uniformly at random
[O'Donnell, Section 2.5][ODonnell2014]. -/
@[expose] noncomputable def condorcetWinnerProb (f : (ι → Bool) → Bool) : ℝ :=
  𝔼 π : ι → Equiv.Perm (Fin 3), if ∃ c, IsCondorcetWinner (fun _ => f) π c then 1 else 0

/-! ### The not-all-equal predicate -/

omit [Fintype ι] [DecidableEq ι] in
/-- There is a Condorcet winner exactly when the three outcomes are not all equal, and the
indicator of that event is `3/4 - 1/4 (w₀ w₁ + w₀ w₂ + w₁ w₂)` in the signs `w_c` of the
outcomes. -/
private theorem ite_exists_isCondorcetWinner (f : (ι → Bool) → Bool)
    (π : ι → Equiv.Perm (Fin 3)) :
    (if ∃ c, IsCondorcetWinner (fun _ => f) π c then (1 : ℝ) else 0) =
      3 / 4 - 1 / 4 *
        (signVal (f (condorcetVotes π 0)) * signVal (f (condorcetVotes π 1)) +
          signVal (f (condorcetVotes π 0)) * signVal (f (condorcetVotes π 2)) +
          signVal (f (condorcetVotes π 1)) * signVal (f (condorcetVotes π 2))) := by
  have hex : (∃ c, IsCondorcetWinner (fun _ => f) π c) ↔
      (f (condorcetVotes π 0) = true ∧ f (condorcetVotes π 2) = false) ∨
      (f (condorcetVotes π 1) = true ∧ f (condorcetVotes π 0) = false) ∨
      (f (condorcetVotes π 2) = true ∧ f (condorcetVotes π 1) = false) := by
    constructor
    · rintro ⟨c, h₁, h₂⟩
      fin_cases c
      exacts [.inl ⟨h₁, h₂⟩, .inr (.inl ⟨h₁, h₂⟩), .inr (.inr ⟨h₁, h₂⟩)]
    · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
      exacts [⟨0, h₁, h₂⟩, ⟨1, h₁, h₂⟩, ⟨2, h₁, h₂⟩]
  simp only [hex]
  cases f (condorcetVotes π 0) <;> cases f (condorcetVotes π 1) <;>
    cases f (condorcetVotes π 2) <;> norm_num

/-! ### Correlated strings with independent coordinates -/

/-- The uniform average of a product of functions of the separate coordinates is the product of
their averages. -/
private theorem expect_prod_apply {α : Type*} [Fintype α] (g : ι → α → ℝ) :
    𝔼 π : ι → α, ∏ i, g i (π i) = ∏ i, 𝔼 a, g i a := by
  simp only [Fintype.expect_eq_sum_div_card, ← Fintype.prod_sum, Fintype.card_fun, Nat.cast_pow,
    prod_div_distrib, prod_const, card_univ]

/-- Two strings whose coordinate pairs `(u (π i), v (π i))` are independent draws, for a uniform
`π i`, with mean-zero signs of correlation `ρ`, correlate `F` with itself by `Stab_ρ[F]`. -/
private theorem expect_mul_comp_eq_noiseStability {α : Type*} [Fintype α] [Nonempty α]
    (u v : α → Bool) {ρ : ℝ} (hu : 𝔼 a, signVal (u a) = 0) (hv : 𝔼 a, signVal (v a) = 0)
    (huv : 𝔼 a, signVal (u a) * signVal (v a) = ρ) (F : (ι → Bool) → ℝ) :
    𝔼 π : ι → α, F (fun i => u (π i)) * F (fun i => v (π i)) = noiseStability ρ F := by
  -- the characters at the two strings are orthogonal across different sets
  have hchi (S T : Finset ι) : 𝔼 π : ι → α,
      chi ℝ S (fun i => u (π i)) * chi ℝ T (fun i => v (π i)) = if S = T then ρ ^ #S else 0 := by
    have hfac (π : ι → α) : chi ℝ S (fun i => u (π i)) * chi ℝ T (fun i => v (π i)) =
        ∏ i, ((if i ∈ S then signVal (u (π i)) else 1) *
          (if i ∈ T then signVal (v (π i)) else 1)) := by
      rw [prod_mul_distrib, prod_ite_mem, prod_ite_mem, univ_inter, univ_inter,
        chi_eq_prod_signVal, chi_eq_prod_signVal]
    have hcoord (i : ι) : 𝔼 a, (if i ∈ S then signVal (u a) else 1) *
        (if i ∈ T then signVal (v a) else 1) =
          if i ∈ S then (if i ∈ T then ρ else 0) else (if i ∈ T then 0 else 1) := by
      by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT, hu, hv, huv]
    rw [expect_congr rfl fun π _ => hfac π, expect_prod_apply (fun i a =>
      (if i ∈ S then signVal (u a) else 1) * (if i ∈ T then signVal (v a) else 1))]
    simp only [hcoord]
    split_ifs with hST
    · subst hST
      calc ∏ i, (if i ∈ S then (if i ∈ S then ρ else 0) else (if i ∈ S then 0 else 1))
          = ∏ i, if i ∈ S then ρ else 1 := prod_congr rfl fun i _ => by split_ifs <;> rfl
        _ = ρ ^ #S := by rw [prod_ite_mem, univ_inter, prod_const]
    · obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ S ↔ i ∈ T) := by
        by_contra! h
        exact hST (ext h)
      refine prod_eq_zero (mem_univ i) ?_
      by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp_all
  calc 𝔼 π : ι → α, F (fun i => u (π i)) * F (fun i => v (π i))
      = 𝔼 π : ι → α, (∑ S, fourierCoeff F S * chi ℝ S (fun i => u (π i))) *
          ∑ T, fourierCoeff F T * chi ℝ T (fun i => v (π i)) := by
        simp only [sum_fourierCoeff_mul_chi]
    _ = ∑ S, ∑ T, fourierCoeff F S * fourierCoeff F T *
          𝔼 π : ι → α, chi ℝ S (fun i => u (π i)) * chi ℝ T (fun i => v (π i)) := by
        simp only [sum_mul_sum, expect_sum_comm, mul_expect]
        exact sum_congr rfl fun S _ => sum_congr rfl fun T _ => expect_congr rfl fun π _ => by ring
    _ = noiseStability ρ F := by
        simp only [hchi, mul_ite, mul_zero, sum_ite_eq, mem_univ, ite_true, noiseStability_eq_sum]
        exact sum_congr rfl fun S _ => by ring

/-- In the elections of `c` and of `d` against their successors, for `c ≠ d`, a uniformly random
ranking votes with mean-zero signs of correlation `-1/3`, and the votes of the electorate correlate
`F` with itself by `Stab_{-1/3}[F]`. -/
private theorem expect_mul_condorcetVotes {c d : Fin 3} (hcd : c ≠ d) (F : (ι → Bool) → ℝ) :
    𝔼 π : ι → Equiv.Perm (Fin 3), F (condorcetVotes π c) * F (condorcetVotes π d) =
      noiseStability (-1 / 3) F := by
  have hsign (b : Bool) : signVal b = ((if b then -1 else 1 : ℤ) : ℝ) := by cases b <;> simp
  have hmean (e : Fin 3) :
      𝔼 σ : Equiv.Perm (Fin 3), signVal (decide (σ e < σ (e + 1))) = 0 := by
    have h : ∑ σ : Equiv.Perm (Fin 3), (if decide (σ e < σ (e + 1)) then -1 else 1 : ℤ) = 0 := by
      revert e
      decide
    simp only [Fintype.expect_eq_sum_div_card, hsign, ← Int.cast_sum, h, Int.cast_zero, zero_div]
  have hcorr : ∑ σ : Equiv.Perm (Fin 3), (if decide (σ c < σ (c + 1)) then -1 else 1 : ℤ) *
      (if decide (σ d < σ (d + 1)) then -1 else 1 : ℤ) = -2 := by
    revert c d
    decide
  have hcorr' : 𝔼 σ : Equiv.Perm (Fin 3),
      signVal (decide (σ c < σ (c + 1))) * signVal (decide (σ d < σ (d + 1))) = -1 / 3 := by
    simp only [Fintype.expect_eq_sum_div_card, hsign, ← Int.cast_mul, ← Int.cast_sum, hcorr,
      Fintype.card_perm, Fintype.card_fin]
    norm_num [Nat.factorial]
  exact expect_mul_comp_eq_noiseStability (fun σ : Equiv.Perm (Fin 3) => decide (σ c < σ (c + 1)))
    (fun σ => decide (σ d < σ (d + 1))) (hmean c) (hmean d) hcorr' F

/-! ### Kalai's formula and its consequences -/

/-- **Kalai's formula** [O'Donnell, Theorem 2.56][ODonnell2014]: in a 3-candidate Condorcet
election using `f`, under the impartial culture assumption, the probability of a Condorcet winner
is `3/4 - 3/4 Stab_{-1/3}[F]`, for `f` read as signs `F = signVal ∘ f`. -/
theorem condorcetWinnerProb_eq (f : (ι → Bool) → Bool) :
    condorcetWinnerProb f = 3 / 4 - 3 / 4 * noiseStability (-1 / 3) (fun x => signVal (f x)) := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  have h01 := expect_mul_condorcetVotes (show (0 : Fin 3) ≠ 1 by decide) F
  have h02 := expect_mul_condorcetVotes (show (0 : Fin 3) ≠ 2 by decide) F
  have h12 := expect_mul_condorcetVotes (show (1 : Fin 3) ≠ 2 by decide) F
  simp only [condorcetWinnerProb, ite_exists_isCondorcetWinner, expect_sub_distrib,
    expect_add_distrib, ← mul_expect, Fintype.expect_const]
  simp only [F] at h01 h02 h12
  rw [h01, h02, h12]
  ring

/-- **Arrow's Theorem**, by Kalai's proof [O'Donnell, Section 2.5][ODonnell2014]: if a voting rule
`f` always gives a Condorcet winner in a 3-candidate Condorcet election and elects the first
candidate when every voter votes for it, then `f` is a dictator, `f x = x_i` for some voter `i`.
By Kalai's formula the hypothesis makes `Stab_{-1/3}[F] = -1/3`, so all the Fourier weight of `F`
is at degree one and `f` is a dictator or a negated dictator; the vote at the all-`true` profile
excludes the negated dictators. The book assumes unanimity, `f (fun _ => true) = true` and
`f (fun _ => false) = false`; only the first half is needed. -/
theorem exists_eq_of_forall_exists_isCondorcetWinner {ι : Type*} [Finite ι]
    {f : (ι → Bool) → Bool} (htrue : f (fun _ => true) = true)
    (h : ∀ π, ∃ c, IsCondorcetWinner (fun _ => f) π c) : ∃ i, f = fun x => x i := by
  cases nonempty_fintype ι
  classical
  have hprob : condorcetWinnerProb f = 1 := by simp [condorcetWinnerProb, h]
  rw [condorcetWinnerProb_eq] at hprob
  obtain ⟨i, b, rfl⟩ := (noiseStability_signVal_eq_iff_of_neg (ρ := -1 / 3) (by norm_num)
    (by norm_num) f).1 (by linarith)
  cases b
  · exact ⟨i, by simp⟩
  · simp at htrue

/-! ### Three different voting rules -/

omit [Fintype ι] [DecidableEq ι] in
/-- Every not-all-equal triple of votes in the elections `0` vs. `1`, `1` vs. `2` and `2` vs. `0`
is cast by some electorate. -/
private theorem exists_condorcetVotes {x y z : ι → Bool} (h : ∀ i, ¬(x i = y i ∧ y i = z i)) :
    ∃ π : ι → Equiv.Perm (Fin 3),
      condorcetVotes π 0 = x ∧ condorcetVotes π 1 = y ∧ condorcetVotes π 2 = z := by
  have hσ (a b c : Bool) (h : ¬(a = b ∧ b = c)) : ∃ σ : Equiv.Perm (Fin 3),
      decide (σ 0 < σ 1) = a ∧ decide (σ 1 < σ 2) = b ∧ decide (σ 2 < σ 0) = c := by
    revert a b c; decide
  choose σ hσ' using fun i => hσ (x i) (y i) (z i) (h i)
  exact ⟨σ, funext fun i => (hσ' i).1, funext fun i => (hσ' i).2.1, funext fun i => (hσ' i).2.2⟩

omit [Fintype ι] [DecidableEq ι] in
/-- There is a Condorcet winner exactly when the three outcomes are not all equal. -/
private theorem exists_isCondorcetWinner_iff (F : Fin 3 → (ι → Bool) → Bool)
    (π : ι → Equiv.Perm (Fin 3)) :
    (∃ c, IsCondorcetWinner F π c) ↔
      ¬(F 0 (condorcetVotes π 0) = F 1 (condorcetVotes π 1) ∧
        F 1 (condorcetVotes π 1) = F 2 (condorcetVotes π 2)) := by
  have hex : (∃ c, IsCondorcetWinner F π c) ↔
      (F 0 (condorcetVotes π 0) = true ∧ F 2 (condorcetVotes π 2) = false) ∨
      (F 1 (condorcetVotes π 1) = true ∧ F 0 (condorcetVotes π 0) = false) ∨
      (F 2 (condorcetVotes π 2) = true ∧ F 1 (condorcetVotes π 1) = false) := by
    constructor
    · rintro ⟨c, h₁, h₂⟩
      fin_cases c
      exacts [.inl ⟨h₁, h₂⟩, .inr (.inl ⟨h₁, h₂⟩), .inr (.inr ⟨h₁, h₂⟩)]
    · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
      exacts [⟨0, h₁, h₂⟩, ⟨1, h₁, h₂⟩, ⟨2, h₁, h₂⟩]
  rw [hex]
  cases F 0 (condorcetVotes π 0) <;> cases F 1 (condorcetVotes π 1) <;>
    cases F 2 (condorcetVotes π 2) <;> decide

omit [Fintype ι] [DecidableEq ι] in
/-- **Unanimous rules that always give a Condorcet winner agree** [O'Donnell, Exercise 2.51(a)]
[ODonnell2014]: if the three pairwise elections are decided by unanimous voting rules `F 0`, `F 1`
and `F 2` and there is always a Condorcet winner, then `F 0 = F 1 = F 2`. Following the book's
hint, the votes `x`, `¬x` and the constant `F c x` in the elections `c`, `c + 1` and `c + 2` are
cast by some electorate, which forces `F (c + 1) (¬x) = ¬F c x`; going around the three elections
gives the claim. -/
theorem eq_of_forall_exists_isCondorcetWinner {F : Fin 3 → (ι → Bool) → Bool}
    (htrue : ∀ c, F c (fun _ => true) = true) (hfalse : ∀ c, F c (fun _ => false) = false)
    (h : ∀ π, ∃ c, IsCondorcetWinner F π c) (c : Fin 3) : F c = F 0 := by
  have hconst (d : Fin 3) (b : Bool) : F d (fun _ => b) = b := by
    cases b; exacts [hfalse d, htrue d]
  have hne (x : ι → Bool) (i : ι) : x i ≠ !x i := by cases x i <;> decide
  -- the three relations `F (d + 1) (¬x) = ¬F d x`
  have R0 (x : ι → Bool) : F 1 (fun i => !x i) = !F 0 x := by
    obtain ⟨π, h0, h1, h2⟩ := exists_condorcetVotes (x := x) (y := fun i => !x i)
      (z := fun _ => F 0 x) fun i hi => hne x i hi.1
    have := (exists_isCondorcetWinner_iff F π).1 (h π)
    rw [h0, h1, h2, hconst] at this
    revert this; cases F 0 x <;> cases F 1 (fun i => !x i) <;> decide
  have R1 (y : ι → Bool) : F 2 (fun i => !y i) = !F 1 y := by
    obtain ⟨π, h0, h1, h2⟩ := exists_condorcetVotes (x := fun _ => F 1 y) (y := y)
      (z := fun i => !y i) fun i hi => hne y i hi.2
    have := (exists_isCondorcetWinner_iff F π).1 (h π)
    rw [h0, h1, h2, hconst] at this
    revert this; cases F 1 y <;> cases F 2 (fun i => !y i) <;> decide
  have R2 (z : ι → Bool) : F 0 (fun i => !z i) = !F 2 z := by
    obtain ⟨π, h0, h1, h2⟩ := exists_condorcetVotes (x := fun i => !z i) (y := fun _ => F 2 z)
      (z := z) fun i hi => hne z i (hi.2.symm.trans hi.1.symm)
    have := (exists_isCondorcetWinner_iff F π).1 (h π)
    rw [h0, h1, h2, hconst] at this
    revert this; cases F 0 (fun i => !z i) <;> cases F 2 z <;> decide
  have hnn (x : ι → Bool) : (fun i => !(!x i)) = x := funext fun i => Bool.not_not _
  have h20 : F 2 = F 0 := funext fun x => by
    have := R1 (fun i => !x i)
    rw [hnn, R0, Bool.not_not] at this
    exact this
  have h10 : F 1 = F 0 := funext fun y => by
    have h := R0 (fun i => !y i)
    rw [hnn] at h
    rw [h, R2, h20, Bool.not_not]
  fin_cases c
  exacts [rfl, h10, h20]

/-- **Arrow's Theorem for three voting rules** [O'Donnell, Exercise 2.51(a)][ODonnell2014]: if the
three pairwise elections are decided by unanimous voting rules and there is always a Condorcet
winner, then all three rules are the same dictator `x ↦ x_i`. -/
theorem exists_forall_eq_of_forall_exists_isCondorcetWinner {ι : Type*} [Finite ι]
    {F : Fin 3 → (ι → Bool) → Bool}
    (htrue : ∀ c, F c (fun _ => true) = true) (hfalse : ∀ c, F c (fun _ => false) = false)
    (h : ∀ π, ∃ c, IsCondorcetWinner F π c) : ∃ i, ∀ c, F c = fun x => x i := by
  have hF : F = fun _ => F 0 := funext (eq_of_forall_exists_isCondorcetWinner htrue hfalse h)
  rw [hF] at h
  obtain ⟨i, hi⟩ := exists_eq_of_forall_exists_isCondorcetWinner (htrue 0) h
  exact ⟨i, fun c => (eq_of_forall_exists_isCondorcetWinner htrue hfalse
    (by rw [hF]; exact h) c).trans hi⟩

/-- `(-1/3) ^ k` is at least `-1/3` at `k = 1` and at least `-1/27` elsewhere. -/
private theorem le_neg_third_pow (k : ℕ) :
    (if k = 1 then -1 / 3 else -1 / 27 : ℝ) ≤ (-1 / 3) ^ k := by
  split_ifs with hk
  · simp [hk]
  rcases Nat.even_or_odd k with he | ho
  · exact (by norm_num : (-1 / 27 : ℝ) ≤ 0).trans (he.pow_nonneg _)
  · have h3 : 3 ≤ k := by obtain ⟨m, rfl⟩ := ho; omega
    have hle : (1 / 3 : ℝ) ^ k ≤ (1 / 3) ^ 3 := pow_le_pow_of_le_one (by norm_num) (by norm_num) h3
    rw [show (-1 / 3 : ℝ) = -(1 / 3) by ring, ho.neg_pow]
    norm_num at hle ⊢
    linarith

/-- **The probability of a Condorcet winner and the degree-one weight**
[O'Donnell, Corollary 2.59][ODonnell2014]: in a 3-candidate Condorcet election using `f`, the
probability of a Condorcet winner is at most `7/9 + 2/9 W^1[F]`, for `f` read as signs
`F = signVal ∘ f`. -/
theorem condorcetWinnerProb_le (f : (ι → Bool) → Bool) :
    condorcetWinnerProb f ≤ 7 / 9 + 2 / 9 * levelWeight 1 (fun x => signVal (f x)) := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  -- `Stab_{-1/3}[F] ≥ -1/27 ∑_S F̂(S)² - 8/27 W^1[F]`, termwise
  have hstab : ∑ S, (if #S = 1 then -1 / 3 else -1 / 27 : ℝ) * fourierCoeff F S ^ 2 ≤
      noiseStability (-1 / 3) F := by
    rw [noiseStability_eq_sum]
    exact sum_le_sum fun S _ => mul_le_mul_of_nonneg_right (le_neg_third_pow _) (sq_nonneg _)
  have hsplit : ∑ S, (if #S = 1 then -1 / 3 else -1 / 27 : ℝ) * fourierCoeff F S ^ 2 =
      -1 / 27 * ∑ S, fourierCoeff F S ^ 2 - 8 / 27 * levelWeight 1 F := by
    rw [levelWeight, sum_filter, mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun S _ => by split_ifs <;> ring
  have hone : ∑ S, fourierCoeff F S ^ 2 = 1 := sum_fourierCoeff_sq_signVal f
  rw [condorcetWinnerProb_eq]
  linarith

/-- **Robust Arrow's Theorem** [O'Donnell, Corollary 2.60][ODonnell2014]: if a 3-candidate
Condorcet election using `f` has a Condorcet winner with probability at least `1 - ε`, then `f` is
`14409/2 · ε`-close to a dictator or a negated dictator: for some voter `i` and bit `b`,
`f x = b ⊕ x_i` except on a fraction at most `14409/2 · ε` of the inputs. Corollary 2.59 gives
`W^1[F] ≥ 1 - 9/2 ε`, and the Friedgut–Kalai–Naor theorem
(`BitString.exists_hammingDist_xor_div_le_of_le_levelWeight_one`, constant `1601`) concludes. The
book states the closeness as `O(ε)`. -/
theorem exists_hammingDist_xor_div_le_of_le_condorcetWinnerProb [Nonempty ι]
    {f : (ι → Bool) → Bool} {ε : ℝ} (h : 1 - ε ≤ condorcetWinnerProb f) :
    ∃ (i : ι) (b : Bool),
      (hammingDist f (fun x => b ^^ x i) : ℝ) / 2 ^ Fintype.card ι ≤ 14409 / 2 * ε := by
  obtain ⟨i, b, hib⟩ := exists_hammingDist_xor_div_le_of_le_levelWeight_one (f := f)
    (δ := 9 / 2 * ε) (by linarith [condorcetWinnerProb_le f])
  exact ⟨i, b, hib.trans_eq (by ring)⟩

end Cslib.BitString
