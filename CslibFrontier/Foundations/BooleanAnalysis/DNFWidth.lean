/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.DNF.ModelCount
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.InformationTheory.Hamming

/-!
# Approximating small formulas by narrow ones

A term of a formula in disjunctive normal form on `k` distinct variables (`Term.width`) fixes
those `k` bits, so it is satisfied on at most `2 ^ (n - k)` of the `2 ^ n` inputs
(`Logic.PL.Term.card_filter_eval_le`). Hence deleting from a DNF of size `s` the terms on more
than `log₂ (s / ε)` variables changes the computed function on at most an `ε` fraction of the
inputs, by the union bound: a function computed by a DNF of size `s` is `ε`-close to one computed
by a DNF of width `log₂ (s / ε)` (`BitString.exists_dnf_hammingDist_div_le`), and likewise for
formulas in conjunctive normal form, by De Morgan duality
(`BitString.exists_cnf_hammingDist_div_le`) [O'Donnell, Proposition 4.9][ODonnell2014].
Closeness is the relative Hamming distance, as in the rest of the Boolean-analysis library.

The formulas here are lists of literals, which may repeat a literal or contain a literal and its
negation; the book excludes the latter [O'Donnell, Definition 4.1][ODonnell2014]. The probability
bound uses the number of distinct variables of a term, `Term.width`. The narrow formula keeps
each surviving term without repeated literals (`Term.length_dedup_of_consistent`) and drops the
contradictory ones, which are never satisfied. So, as the theorems state, every term of the
narrow DNF has no repeated literal (`List.Nodup`) and is consistent (`Term.consistent`), and
every clause of the narrow CNF has no repeated literal and is not a tautology
(`CNF.isTautClause`): Definition 4.1's restriction, carried to clauses by Definition 4.4. Its
width, the length of its terms, is then the book's number of literals.

## Main results

* `Cslib.BitString.exists_dnf_hammingDist_div_le`, `Cslib.BitString.exists_cnf_hammingDist_div_le`:
  a formula of size `s` is `ε`-close to one of width `log₂ (s / ε)`, in literals, and size at most
  `s`, whose terms have no repeated literal and are consistent (clauses: are not tautologies).

## Usage

Open `Cslib.BitString` and `Cslib.Logic.PL`. Formulas are `DNF ι` and `CNF ι` over a finite type of
variables `ι`, read on the cube `ι → Bool` through `DNF.eval` and `CNF.eval`; their size is
`List.length` and the width of a surviving term is its `List.length`; the narrow DNF's terms satisfy
`t.Nodup` and `Term.consistent t = true`, and the narrow CNF's clauses `c.Nodup` and
`CNF.isTautClause c = false` (`Cslib.Logic.PL.Term.isTautClause_negate` relates the two). A function
`f` is `ε`-close to `g` when `(hammingDist f g : ℝ) / 2 ^ Fintype.card ι ≤ ε`, the form of the junta
and affinity closeness results. Only `0 < ε` is assumed; the book takes `ε ∈ (0, 1]`. For the
per-term probability bound alone, use `Cslib.Logic.PL.Term.card_filter_eval_le`, an instance of
`Cslib.BitString.card_le_of_forall_agree` for words that pairwise agree on a set of coordinates.

The checked clients in
[CslibFrontierTests/BooleanAnalysisDNFWidth.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisDNFWidth.lean)
apply both forms to the formula `(x₀ ∧ x₁ ∧ x₂) ∨ ¬x₀` on three variables, with a width-three
term, and to its dual, with `ε = 1 / 2`, and check that the per-term bound is attained by
`x₀ ∧ ¬x₁`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014], Section 4.1.
-/

public section

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Cslib.BitString

open Logic.PL

/-- **A small DNF is close to a narrow one**: a function computed by a formula in disjunctive
normal form with `s` terms is `ε`-close to one computed by a formula with at most `s` terms, each
consistent, without repeated literals and with at most `log₂ (s / ε)` literals
[O'Donnell, Proposition 4.9][ODonnell2014].
The book takes `ε ∈ (0, 1]`; `0 < ε` suffices. -/
theorem exists_dnf_hammingDist_div_le (φ : DNF ι) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : DNF ι, ψ.length ≤ φ.length ∧
      (∀ t ∈ ψ, t.Nodup ∧ t.consistent = true ∧
        (t.length : ℝ) ≤ Real.logb 2 (φ.length / ε)) ∧
      (hammingDist (fun x : ι → Bool => φ.eval x) fun x => ψ.eval x : ℝ) /
        2 ^ Fintype.card ι ≤ ε := by
  set L := Real.logb 2 (φ.length / ε)
  set ψ : DNF ι := (φ.filter fun t => decide ((t.width : ℝ) ≤ L) && t.consistent).map List.dedup
  refine ⟨ψ, (List.length_map _).trans_le (List.length_filter_le _ _), fun t ht => ?_, ?_⟩
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
    simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨σ, hσ⟩ := Term.consistent_iff_exists_eval.1 hs.2.2
    refine ⟨List.nodup_dedup s,
      Term.consistent_iff_exists_eval.2 ⟨σ, by rwa [Term.eval_dedup]⟩, ?_⟩
    rw [Term.length_dedup_of_consistent hs.2.2]
    exact hs.2.1
  set B := (φ.filter fun t => decide ¬((t.width : ℝ) ≤ L)).toFinset
  -- Where the two formulas disagree, some deleted term is satisfied.
  have hsub : ({x : ι → Bool | φ.eval x ≠ ψ.eval x} : Finset (ι → Bool)) ⊆
      B.biUnion fun t => {x | t.eval x = true} := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    simp only [mem_biUnion, B, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, mem_filter,
      mem_univ, true_and]
    by_contra hB
    simp only [not_exists, not_and, and_imp] at hB
    apply hx
    rw [Bool.eq_iff_iff, DNF.eval_eq_true_iff, DNF.eval_eq_true_iff]
    constructor
    · rintro ⟨t, ht, htx⟩
      have hL : (t.width : ℝ) ≤ L := by
        by_contra hL
        exact hB t ht hL htx
      refine ⟨t.dedup, List.mem_map.2 ⟨t, ?_, rfl⟩, by rwa [Term.eval_dedup]⟩
      simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨ht, hL, Term.consistent_of_eval htx⟩
    · rintro ⟨t', ht', htx⟩
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ht'
      exact ⟨t, (List.mem_filter.1 ht).1, by rwa [Term.eval_dedup] at htx⟩
  -- Each deleted term is satisfied on at most an `ε / s` fraction of the inputs.
  have hterm (t : Term ι) (ht : t ∈ B) :
      (#{x : ι → Bool | t.eval x = true} : ℝ) ≤ ε / φ.length * 2 ^ Fintype.card ι := by
    simp only [B, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, not_le] at ht
    have hs : (0 : ℝ) < φ.length := by
      exact_mod_cast List.length_pos_of_mem ht.1
    have hlt : (φ.length : ℝ) / ε < 2 ^ (t.width : ℝ) :=
      (Real.logb_lt_iff_lt_rpow one_lt_two (by positivity)).1 ht.2
    rw [Real.rpow_natCast] at hlt
    calc (#{x : ι → Bool | t.eval x = true} : ℝ)
        ≤ 2 ^ (Fintype.card ι - t.width) := by exact_mod_cast Term.card_filter_eval_le t
      _ = (2 ^ t.width)⁻¹ * 2 ^ Fintype.card ι := by
        rw [pow_sub₀ _ two_ne_zero (show t.width ≤ Fintype.card ι from card_le_univ _), mul_comm]
      _ ≤ ε / φ.length * 2 ^ Fintype.card ι := by
        gcongr
        rw [inv_le_comm₀ (by positivity) (by positivity), inv_div]
        exact hlt.le
  have hB : (#B : ℝ) ≤ φ.length := by
    exact_mod_cast (List.toFinset_card_le _).trans (List.length_filter_le _ _)
  rw [div_le_iff₀ (by positivity)]
  calc (hammingDist (fun x : ι → Bool => φ.eval x) fun x => ψ.eval x : ℝ)
      ≤ ∑ t ∈ B, (#{x : ι → Bool | t.eval x = true} : ℝ) := by
        exact_mod_cast (card_le_card hsub).trans card_biUnion_le
    _ ≤ ∑ _t ∈ B, ε / φ.length * 2 ^ Fintype.card ι := sum_le_sum hterm
    _ = #B * (ε / φ.length * 2 ^ Fintype.card ι) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ φ.length * (ε / φ.length * 2 ^ Fintype.card ι) := by gcongr
    _ ≤ ε * 2 ^ Fintype.card ι := by
      rcases eq_or_ne (φ.length : ℝ) 0 with hs | hs
      · rw [hs, zero_mul]
        positivity
      · rw [← mul_assoc, mul_div_cancel₀ _ hs]

/-- **A small CNF is close to a narrow one**: a function computed by a formula in conjunctive
normal form with `s` clauses is `ε`-close to one computed by a formula with at most `s` clauses,
none a tautology or with a repeated literal, and each with at most `log₂ (s / ε)` literals. The
book's "(or CNF)" is read, following its proof, as giving a CNF in this case
[O'Donnell, Proposition 4.9][ODonnell2014]. The book takes `ε ∈ (0, 1]`; `0 < ε` suffices. -/
theorem exists_cnf_hammingDist_div_le (φ : CNF ι) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : CNF ι, ψ.length ≤ φ.length ∧
      (∀ c ∈ ψ, c.Nodup ∧ CNF.isTautClause c = false ∧
        (c.length : ℝ) ≤ Real.logb 2 (φ.length / ε)) ∧
      (hammingDist (fun x : ι → Bool => φ.eval x) fun x => ψ.eval x : ℝ) /
        2 ^ Fintype.card ι ≤ ε := by
  obtain ⟨ψ, hlen, hwidth, hdist⟩ := exists_dnf_hammingDist_div_le φ.negate hε
  have hφ : φ.negate.length = φ.length := List.length_map _
  refine ⟨ψ.negate, by simpa [DNF.negate, hφ] using hlen, fun c hc => ?_, ?_⟩
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hc
    obtain ⟨hnd, hc, hlen⟩ := hwidth t ht
    exact ⟨hnd.map fun ⟨_, _⟩ ⟨_, _⟩ h => by simp_all only [Prod.mk.injEq, Bool.not_inj_iff],
      by rw [Term.isTautClause_negate, hc, Bool.not_true],
      by rwa [Term.length_negate, ← hφ]⟩
  · refine le_of_eq_of_le ?_ hdist
    congr 2
    unfold hammingDist
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and, DNF.eval_negate, CNF.eval_negate]
    cases φ.eval x <;> cases ψ.eval x <;> decide

end Cslib.BitString
