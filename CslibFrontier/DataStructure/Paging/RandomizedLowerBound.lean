/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Online.Randomized
public import CslibFrontier.DataStructure.Paging.Marking
import CslibFrontier.Foundations.NumberTheory.Harmonic
import CslibFrontier.Probability.PMF.SupportTsum
import CslibFrontier.Tactic.FinsetCard
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The `H_k` randomized paging lower bound and `(k + 1)`-page tightness

This file formalizes the randomized lower bound and sharpness results of
[Fiat, Karp, Luby, McGeoch, Sleator, and Young, *Competitive Paging
Algorithms*][FiatKarpLubyMcGeochSleatorYoung1991] (`arXiv:cs/0205038v1`, numbering verified against
`marking.tex`):

1. **Section 5, Theorem 4 and Corollary 5 (`H_k` lower bound against an oblivious adversary):**
   Over any page universe containing a `(k + 1)`-element subset `S` (`0 < k`), no randomized online
   paging algorithm — whether formulated as a behavioural strategy (`Online.BehavioralStrategy`,
   covering `markingStrategy`) or as a discrete mixture of deterministic strategies
   (`Online.RandStrategy`) — is `(c, b)`-competitive for any `c < H_k` and finite additive constant
   `b ≠ ⊤`, even from a fixed admissible initial cache such as `∅`
   (`not_isCompetitiveFrom_behavioral_of_lt`, `not_isCompetitiveFrom_rand_of_lt`).
   Following Section 5 of the source, an oblivious nemesis maintains a marked subset of `S` and
   constructs subphases (`exists_subphase`) whose expected online cost is at least `1 / u` when `u`
   pages of `S` are unmarked, accumulating at least `H_k` expected faults per phase while a
   capacity-`k` offline schedule faults only once per phase (`exists_phase`, `exists_phases`).
2. **Section 3, Theorem 2 (`markingthm2`, `H_k`-competitiveness on `k + 1` pages):**
   When all requests and the initial cache lie in a set `U` of at most `k + 1` pages (in particular
   on any `[Fintype α]` with `Fintype.card α ≤ k + 1`), each phase of `markingStrategy` contains at
   most one clean request and `#clean ≤ OPT` with zero additive slack
   (`cleanCount_le_scheduleCost_of_subset`), making `markingStrategy` `(H_k, 0)`-competitive
   (`markingStrategy_isCompetitive_of_card_le`) and matching the `H_k` lower bound on `Fin (k + 1)`
   (`markingStrategy_tight_on_fin_succ`).
3. **Section 3 separation for `n ≥ k + 2`
   (`markingStrategy_not_isCompetitive_harmonic_two_fin_four`):**
   Even at `k = 2` on four pages (`Fin 4`), repeating the 8-request cycle `[2, 3, 0, 1, 3, 2, 1, 0]`
   from `{0, 1}` forces `markingStrategy` to incur `8 m` expected faults against `4 m + 1` offline
   faults, refuting `(c, b)`-competitiveness for every `c < 2` (in particular `c = H_2 = 3 / 2`) and
   every `b ≠ ⊤`.

## Main definitions

* `Cslib.DataStructure.Paging.ObliviousPagingCost`: prefix-additive expected-cost interface on a
  `(k + 1)`-page subset (`0 ≤ Δcost` and `1 ≤ ∑_{x ∈ S} Δcost(σ, x)`), satisfied by both
  `BehavioralStrategy` and `RandStrategy`.

## Main results

* `not_isCompetitiveFrom_behavioral_of_lt`, `not_isCompetitive_behavioral_of_lt`,
  `not_isCompetitiveAnyInit_behavioral_of_lt`, `fin_not_isCompetitiveFrom_empty_behavioral_of_lt`:
  `H_k` oblivious-adversary lower bound for `BehavioralStrategy`.
* `not_isCompetitiveFrom_rand_of_lt`, `not_isCompetitive_rand_of_lt`,
  `fin_not_isCompetitiveFrom_empty_rand_of_lt`: `H_k` oblivious-adversary lower bound for
  `RandStrategy`.
* `cleanCount_le_scheduleCost_of_subset`, `markingStrategy_isCompetitive_of_card_le`,
  `markingStrategy_tight_on_fin_succ`: FKLMSY Theorem 2 (`H_k`-competitiveness on `≤ k + 1` pages).
* `markingStrategy_not_isCompetitive_lt_two_fin_four`,
  `markingStrategy_not_isCompetitive_harmonic_two_fin_four`: `markingStrategy` is not
  `H_2`-competitive on four pages at `k = 2`.

## References

* [A. Fiat, R. M. Karp, M. Luby, L. A. McGeoch, D. D. Sleator, and N. E. Young, *Competitive Paging
  Algorithms*][FiatKarpLubyMcGeochSleatorYoung1991], Section 3 (Theorem 2 and `k = 2, n = 4`
  example) and Section 5 (Theorem 4 and Corollary 5).
-/

open scoped ENNReal

public section

namespace Cslib.DataStructure.Paging

open Cslib.DataStructure.Online

section Nemesis

variable {α : Type} [DecidableEq α]

/-! ### Oblivious nemesis sequence construction (FKLMSY Section 5) -/

/-- Abstract oblivious expected-cost functional over a `(k + 1)`-page set `S`: starting at zero on
`[]`, appending a single request `x` incurs nonnegative expected step cost
`cost (σ ++ [x]) - cost σ`, and because any valid capacity-`k` cache misses at least one page of
`S`, the sum of expected step costs over `S` is at least `1` after every prefix `σ`. -/
structure ObliviousPagingCost (S : Finset α) (cost : List α → ℝ) : Prop where
  /-- Empty request sequence incurs zero expected cost. -/
  cost_nil : cost [] = 0
  /-- Appending any single request never decreases expected cost. -/
  step_nonneg : ∀ σ x, 0 ≤ cost (σ ++ [x]) - cost σ
  /-- Across `S`, expected miss probabilities sum to at least `1` after every prefix `σ`. -/
  one_le_sum_step : ∀ σ, (1 : ℝ) ≤ ∑ x ∈ S, (cost (σ ++ [x]) - cost σ)

omit [DecidableEq α] in
private theorem exists_elem_ge_avg {M : Finset α} (hM : M.Nonempty) (f : α → ℝ) :
    ∃ x ∈ M, (∑ y ∈ M, f y) / (M.card : ℝ) ≤ f x := by
  have hpos : (0 : ℝ) < M.card := Nat.cast_pos.mpr hM.card_pos
  by_contra! hlt
  have hsum : ∑ y ∈ M, f y < ∑ _y ∈ M, (∑ z ∈ M, f z) / (M.card : ℝ) :=
    Finset.sum_lt_sum_of_nonempty hM fun y hy => hlt y hy
  rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hpos.ne'] at hsum
  exact lt_irrefl _ hsum

omit [DecidableEq α] in
private theorem sum_tsum_ennreal {β : Type*} (S : Finset α) (f : α → β → ℝ≥0∞) :
    (∑ x ∈ S, ∑' m, f x m) = ∑' m, ∑ x ∈ S, f x m := by
  induction S using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, tsum_zero]
  | cons a s ha ih => simp only [Finset.sum_cons, ih, tsum_add]

private theorem sum_ite_notMem_ennreal (S T : Finset α) :
    (∑ x ∈ S, if x ∈ T then (0 : ℝ≥0∞) else 1) = ((S \ T).card : ℝ≥0∞) := by
  have h : (fun x => if x ∈ T then (0 : ℝ≥0∞) else 1) =
      (fun x => if x ∉ T then (1 : ℝ≥0∞) else 0) := by
    ext x
    by_cases hx : x ∈ T <;> simp only [hx, not_true_eq_false, not_false_eq_true, ↓reduceIte]
  rw [h, Finset.sum_boole, Finset.filter_notMem_eq_sdiff]

private theorem subphase_loop {S M : Finset α} {cost : List α → ℝ}
    (hcost : ObliviousPagingCost S cost) (hMS : M ⊆ S) (hM_ne : M.Nonempty)
    (hU_ne : (S \ M).Nonempty) {ε : ℝ} (hε : 0 < ε) (σ : List α) :
    ∀ (fuel : ℕ) (mid : List α),
      (∀ x ∈ mid, x ∈ M) →
      (fuel : ℝ) * (ε / (M.card : ℝ)) > ((S \ M).card : ℝ)⁻¹ - (cost (σ ++ mid) - cost σ) →
      ε ≤ cost (σ ++ mid) - cost σ →
      ∃ mid' : List α, ∃ j ∈ S \ M,
        (∀ x ∈ mid', x ∈ M) ∧
        (((S \ M).card : ℝ)⁻¹ ≤ cost (σ ++ (mid' ++ [j])) - cost σ)
  | 0, mid, hmid, hfuel, _ => by
    simp only [Nat.cast_zero, zero_mul] at hfuel
    obtain ⟨j, hj⟩ := hU_ne
    have hstep := hcost.step_nonneg (σ ++ mid) j
    have heq : σ ++ (mid ++ [j]) = (σ ++ mid) ++ [j] := (List.append_assoc _ _ _).symm
    refine ⟨mid, j, hj, hmid, ?_⟩
    rw [heq]
    linarith
  | fuel + 1, mid, hmid, hfuel, hbase => by
    set u : ℝ := ((S \ M).card : ℝ)
    have hu_pos : 0 < u := Nat.cast_pos.mpr hU_ne.card_pos
    have hu_ge_one : (1 : ℝ) ≤ u := Nat.one_le_cast.mpr hU_ne.card_pos
    by_cases hdone : u⁻¹ ≤ cost (σ ++ mid) - cost σ
    · obtain ⟨j, hj⟩ := hU_ne
      have hstep := hcost.step_nonneg (σ ++ mid) j
      have heq : σ ++ (mid ++ [j]) = (σ ++ mid) ++ [j] := (List.append_assoc _ _ _).symm
      refine ⟨mid, j, hj, hmid, ?_⟩
      rw [heq]
      linarith
    · by_cases hP : ∑ x ∈ M, (cost ((σ ++ mid) ++ [x]) - cost (σ ++ mid)) ≤ ε
      · have htot := hcost.one_le_sum_step (σ ++ mid)
        have hsplit : ∑ x ∈ S, (cost ((σ ++ mid) ++ [x]) - cost (σ ++ mid)) =
            ∑ x ∈ M, (cost ((σ ++ mid) ++ [x]) - cost (σ ++ mid)) +
              ∑ x ∈ S \ M, (cost ((σ ++ mid) ++ [x]) - cost (σ ++ mid)) := by
          rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hMS]
        have hU_sum : 1 - ε ≤ ∑ x ∈ S \ M, (cost ((σ ++ mid) ++ [x]) - cost (σ ++ mid)) := by
          linarith
        obtain ⟨j, hj, hj_ge⟩ := exists_elem_ge_avg hU_ne
          (fun x => cost ((σ ++ mid) ++ [x]) - cost (σ ++ mid))
        have hj_bound : (1 - ε) / u ≤ cost ((σ ++ mid) ++ [j]) - cost (σ ++ mid) :=
          (div_le_div_of_nonneg_right hU_sum hu_pos.le).trans hj_ge
        have heps_u : u⁻¹ ≤ ε + (1 - ε) / u := by
          rw [inv_eq_one_div, ← sub_nonneg]
          have hcalc : ε + (1 - ε) / u - 1 / u = (u - 1) * ε / u := by field_simp; ring
          rw [hcalc]
          exact div_nonneg (mul_nonneg (by linarith) hε.le) hu_pos.le
        have heq : σ ++ (mid ++ [j]) = (σ ++ mid) ++ [j] := (List.append_assoc _ _ _).symm
        refine ⟨mid, j, hj, hmid, ?_⟩
        rw [heq]
        linarith
      · push Not at hP
        obtain ⟨i, hi, hi_ge⟩ := exists_elem_ge_avg hM_ne
          (fun x => cost ((σ ++ mid) ++ [x]) - cost (σ ++ mid))
        have hM_pos : (0 : ℝ) < M.card := Nat.cast_pos.mpr hM_ne.card_pos
        have hi_step : ε / (M.card : ℝ) ≤ cost ((σ ++ mid) ++ [i]) - cost (σ ++ mid) :=
          (div_le_div_of_nonneg_right hP.le hM_pos.le).trans hi_ge
        have hmid' : ∀ x ∈ mid ++ [i], x ∈ M := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hmid x hx
          · rw [List.mem_singleton.mp hx]
            exact hi
        have heq : σ ++ (mid ++ [i]) = (σ ++ mid) ++ [i] := (List.append_assoc _ _ _).symm
        refine subphase_loop hcost hMS hM_ne hU_ne hε σ fuel (mid ++ [i]) hmid' ?_ ?_
        · rw [heq]
          push_cast at hfuel
          linarith
        · rw [heq]
          have hpos_step : 0 ≤ ε / (M.card : ℝ) := by positivity
          linarith

/-- **Subphase lemma** ([FiatKarpLubyMcGeochSleatorYoung1991], Section 5): for any prefix `σ` and
nonempty marked subset `M ⊂ S` (`M ⊆ S`, `(S \ M).Nonempty`), there is a finite sequence of marked
requests `mid` followed by an unmarked request `j ∈ S \ M` increasing expected cost by at least
`1 / |S \ M|`. -/
theorem exists_subphase {S M : Finset α} {cost : List α → ℝ}
    (hcost : ObliviousPagingCost S cost) (hMS : M ⊆ S) (hM_ne : M.Nonempty)
    (hU_ne : (S \ M).Nonempty) (σ : List α) :
    ∃ mid : List α, ∃ j ∈ S \ M,
      (∀ x ∈ mid, x ∈ M) ∧
      (((S \ M).card : ℝ)⁻¹ ≤ cost (σ ++ (mid ++ [j])) - cost σ) := by
  by_cases hP0 : ∑ x ∈ M, (cost (σ ++ [x]) - cost σ) ≤ 0
  · have htot := hcost.one_le_sum_step σ
    have hsplit : ∑ x ∈ S, (cost (σ ++ [x]) - cost σ) =
        ∑ x ∈ M, (cost (σ ++ [x]) - cost σ) + ∑ x ∈ S \ M, (cost (σ ++ [x]) - cost σ) := by
      rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hMS]
    have hU_sum : (1 : ℝ) ≤ ∑ x ∈ S \ M, (cost (σ ++ [x]) - cost σ) := by linarith
    obtain ⟨j, hj, hj_ge⟩ := exists_elem_ge_avg hU_ne (fun x => cost (σ ++ [x]) - cost σ)
    have hu_pos : (0 : ℝ) < (S \ M).card := Nat.cast_pos.mpr hU_ne.card_pos
    refine ⟨[], j, hj, fun _ h => False.elim (List.not_mem_nil h), ?_⟩
    simp only [List.nil_append]
    have hdiv :
        ((S \ M).card : ℝ)⁻¹ ≤ (∑ x ∈ S \ M, (cost (σ ++ [x]) - cost σ)) / (S \ M).card := by
      rw [inv_eq_one_div]
      exact div_le_div_of_nonneg_right hU_sum hu_pos.le
    exact hdiv.trans hj_ge
  · push Not at hP0
    have hex : ∃ i₀ ∈ M, 0 < cost (σ ++ [i₀]) - cost σ := by
      by_contra! hall
      have : ∑ x ∈ M, (cost (σ ++ [x]) - cost σ) ≤ 0 :=
        Finset.sum_nonpos fun x hx => hall x hx
      linarith
    obtain ⟨i₀, hi₀, hε⟩ := hex
    set ε := cost (σ ++ [i₀]) - cost σ
    have hM_pos : (0 : ℝ) < M.card := Nat.cast_pos.mpr hM_ne.card_pos
    have hstep_pos : 0 < ε / (M.card : ℝ) := div_pos hε hM_pos
    obtain ⟨fuel, hfuel⟩ := exists_nat_gt ((((S \ M).card : ℝ)⁻¹ - ε) / (ε / (M.card : ℝ)))
    have hfuel' : (fuel : ℝ) * (ε / (M.card : ℝ)) > ((S \ M).card : ℝ)⁻¹ - ε :=
      (div_lt_iff₀ hstep_pos).mp hfuel
    exact subphase_loop hcost hMS hM_ne hU_ne hε σ fuel [i₀]
      (fun x hx => by rw [List.mem_singleton.mp hx]; exact hi₀) hfuel' le_rfl

omit [DecidableEq α] in
private theorem exists_growPhase {k : ℕ} {S : Finset α} {cost : List α → ℝ}
    (hcost : ObliviousPagingCost S cost) (hS : S.card = k + 1) :
    ∀ (rem : ℕ) (M : Finset α) (σ : List α),
      M ⊆ S → M.Nonempty → M.card ≤ k → k - M.card = rem →
      ∃ body : List α, ∃ M_end : Finset α,
        M ⊆ M_end ∧ M_end ⊆ S ∧ M_end.card = k ∧
        (∀ x ∈ body, x ∈ M_end) ∧
        ((harmonic (k + 1 - M.card) : ℝ) - 1 ≤ cost (σ ++ body) - cost σ)
  | 0, M, σ, hMS, _, hMk, hrem => by
    have hcard : M.card = k := by omega
    refine ⟨[], M, Finset.Subset.refl M, hMS, hcard, fun _ h => False.elim (List.not_mem_nil h), ?_⟩
    rw [show k + 1 - M.card = 1 by omega, List.append_nil, sub_self]
    simp only [harmonic_succ, harmonic_zero]
    norm_num
  | rem + 1, M, σ, hMS, hM_ne, hMk, hrem => by
    classical
    have hM_lt : M.card < k := by omega
    have hU_card : (S \ M).card = k + 1 - M.card := by finset_card
    have hU_ne : (S \ M).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨mid, j, hj, hmid, hsub_cost⟩ := exists_subphase hcost hMS hM_ne hU_ne σ
    obtain ⟨hjS, hjM⟩ := Finset.mem_sdiff.mp hj
    set M' := insert j M
    have hM'_sub : M' ⊆ S := Finset.insert_subset hjS hMS
    have hM'_ne : M'.Nonempty := ⟨j, Finset.mem_insert_self j M⟩
    have hM'_card : M'.card = M.card + 1 := Finset.card_insert_of_notMem hjM
    obtain ⟨body', M_end, hM'_end, hMend_S, hMend_card, hbody', hgrow_cost⟩ :=
      exists_growPhase hcost hS rem M' (σ ++ (mid ++ [j])) hM'_sub hM'_ne (by omega) (by omega)
    refine ⟨(mid ++ [j]) ++ body', M_end, (Finset.subset_insert j M).trans hM'_end,
      hMend_S, hMend_card, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp hx with hx | hx
        · exact hM'_end (Finset.mem_insert_of_mem (hmid x hx))
        · rw [List.mem_singleton.mp hx]
          exact hM'_end (Finset.mem_insert_self j M)
      · exact hbody' x hx
    · set u' := k - M.card
      have hu1 : k + 1 - M.card = u' + 1 := by omega
      have hu2 : k + 1 - M'.card = u' := by omega
      rw [hU_card, hu1] at hsub_cost
      rw [hu2] at hgrow_cost
      have hharm : (harmonic (u' + 1) : ℝ) = (harmonic u' : ℝ) + ((u' + 1 : ℕ) : ℝ)⁻¹ := by
        rw [harmonic_succ]
        push_cast
        ring
      have heq : σ ++ ((mid ++ [j]) ++ body') = (σ ++ (mid ++ [j])) ++ body' :=
        (List.append_assoc _ _ _).symm
      rw [hu1, hharm, heq]
      linarith

/-- **Single-phase nemesis lemma** ([FiatKarpLubyMcGeochSleatorYoung1991], Section 5): from any
prefix `σ` and full offline cache `M_prev ⊆ S` (`M_prev.card = k`, `0 < k`), there exist a phase
request sequence `phase`, a next cache `M_next ⊆ S` (`M_next.card = k`), and a valid 1-fault
offline schedule moving `M_prev ↦ M_next` such that the online expected cost increases by at least
`H_k`. -/
theorem exists_phase {k : ℕ} (hk : 0 < k) {S M_prev : Finset α} {cost : List α → ℝ}
    (hcost : ObliviousPagingCost S cost) (hS : S.card = k + 1)
    (hM_sub : M_prev ⊆ S) (hM_card : M_prev.card = k) (σ : List α) :
    ∃ phase : List α, ∃ M_next : Finset α, ∃ offStates : List (Finset α),
      M_next ⊆ S ∧ M_next.card = k ∧
      (problem α k).ValidSchedule M_prev phase offStates ∧
      (problem α k).finalState M_prev offStates = M_next ∧
      (problem α k).scheduleCost M_prev phase offStates = 1 ∧
      (harmonic k : ℝ) ≤ cost (σ ++ phase) - cost σ := by
  have hM_ne : M_prev.Nonempty := Finset.card_pos.mp (hM_card ▸ hk)
  have hU_card : (S \ M_prev).card = 1 := by finset_card
  have hU_ne : (S \ M_prev).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨pre, x_new, hx_new, hpre, hcost_pre⟩ := exists_subphase hcost hM_sub hM_ne hU_ne σ
  rw [hU_card, Nat.cast_one, inv_one] at hcost_pre
  obtain ⟨hx_S, hx_notM⟩ := Finset.mem_sdiff.mp hx_new
  obtain ⟨body, M_next, hsing_sub, hMnext_S, hMnext_card, hbody, hcost_body⟩ :=
    exists_growPhase hcost hS (k - 1) {x_new} (σ ++ (pre ++ [x_new]))
      (Finset.singleton_subset_iff.mpr hx_S) (Finset.singleton_nonempty x_new)
      (by simp only [Finset.card_singleton]; exact hk)
      (by simp only [Finset.card_singleton])
  simp only [Finset.card_singleton, Nat.add_sub_cancel] at hcost_body
  have hx_Mnext : x_new ∈ M_next := hsing_sub (Finset.mem_singleton_self x_new)
  have hins_eq : insert x_new M_prev = S := by
    apply Finset.eq_of_subset_of_card_le (Finset.insert_subset hx_S hM_sub)
    rw [Finset.card_insert_of_notMem hx_notM, hM_card, hS]
  have hstep_x : ValidStep k M_prev x_new M_next := by
    refine ⟨hM_card.le, hMnext_card.le, hx_Mnext, ?_⟩
    simp only [hx_notM, ↓reduceIte, hins_eq]
    exact hMnext_S
  have hv_pre := validSchedule_replicate_of_forall_mem hM_card.le hpre
  have hcost_off_pre := scheduleCost_replicate_of_forall_mem (k := k) hpre
  have hv_body := validSchedule_replicate_of_forall_mem hMnext_card.le hbody
  have hcost_off_body := scheduleCost_replicate_of_forall_mem (k := k) hbody
  have hfin_rep : ∀ (n : ℕ) (s : Finset α),
      (problem α k).finalState s (List.replicate n s) = s := by
    intro n s
    induction n with
    | zero => rfl
    | succ n ih => exact ih
  set offStates := List.replicate pre.length M_prev ++ (M_next :: List.replicate body.length M_next)
  have hv_tail : (problem α k).ValidSchedule M_prev (x_new :: body)
      (M_next :: List.replicate body.length M_next) := ⟨hstep_x, hv_body⟩
  refine ⟨(pre ++ [x_new]) ++ body, M_next, offStates, hMnext_S, hMnext_card, ?_, ?_, ?_, ?_⟩
  · rw [List.append_assoc pre [x_new] body, List.singleton_append]
    apply (problem α k).validSchedule_append hv_pre
    rw [hfin_rep]
    exact hv_tail
  · simp only [offStates]
    rw [(problem α k).finalState_append, hfin_rep]
    change (problem α k).finalState M_next (List.replicate body.length M_next) = M_next
    exact hfin_rep _ _
  · rw [List.append_assoc pre [x_new] body, List.singleton_append]
    simp only [offStates]
    rw [(problem α k).scheduleCost_append (List.length_replicate), hcost_off_pre, hfin_rep,
      Nat.zero_add]
    change stepCost M_prev x_new M_next +
      (problem α k).scheduleCost M_next body (List.replicate body.length M_next) = 1
    rw [stepCost_of_notMem hx_notM, hcost_off_body, Nat.add_zero]
  · have heq : σ ++ ((pre ++ [x_new]) ++ body) = (σ ++ (pre ++ [x_new])) ++ body :=
      (List.append_assoc _ _ _).symm
    rw [heq]
    linarith

/-- Iterating `exists_phase` across `m` phases produces a sequence on which online expected cost
increases by at least `m * H_k` while the offline schedule incurs exactly `m` faults. -/
theorem exists_phases {k : ℕ} (hk : 0 < k) {S M₀ : Finset α} {cost : List α → ℝ}
    (hcost : ObliviousPagingCost S cost) (hS : S.card = k + 1)
    (hM₀_sub : M₀ ⊆ S) (hM₀_card : M₀.card = k) :
    ∀ (m : ℕ) (σ : List α),
      ∃ reqs : List α, ∃ offStates : List (Finset α),
        (problem α k).ValidSchedule M₀ reqs offStates ∧
        (problem α k).scheduleCost M₀ reqs offStates = m ∧
        (m : ℝ) * (harmonic k : ℝ) ≤ cost (σ ++ reqs) - cost σ
  | 0, _ => ⟨[], [], trivial, rfl, by simp⟩
  | m + 1, σ => by
    obtain ⟨phase, M₁, ss₁, hM₁_sub, hM₁_card, hv₁, hfin₁, hcost₁, hgain₁⟩ :=
      exists_phase hk hcost hS hM₀_sub hM₀_card σ
    obtain ⟨reqs_rest, ss_rest, hv_rest, hcost_rest, hgain_rest⟩ :=
      exists_phases hk hcost hS hM₁_sub hM₁_card m (σ ++ phase)
    refine ⟨phase ++ reqs_rest, ss₁ ++ ss_rest, ?_, ?_, ?_⟩
    · apply (problem α k).validSchedule_append hv₁
      rwa [hfin₁]
    · rw [(problem α k).scheduleCost_append hv₁.length_eq, hfin₁, hcost₁, hcost_rest, Nat.add_comm]
    · have heq : σ ++ (phase ++ reqs_rest) = (σ ++ phase) ++ reqs_rest :=
        (List.append_assoc _ _ _).symm
      rw [heq]
      push_cast
      linarith

private theorem exists_warmup_aux {k : ℕ} :
    ∀ (xs : List α) (kept cur : Finset α),
      xs.Nodup → Disjoint kept xs.toFinset → kept ⊆ cur → cur.card ≤ k →
      kept.card + xs.length = k →
      ∃ states : List (Finset α),
        (problem α k).ValidSchedule cur xs states ∧
        (problem α k).finalState cur states = kept ∪ xs.toFinset ∧
        (problem α k).scheduleCost cur xs states ≤ xs.length
  | [], kept, cur, _, _, hsub, hcur, hsum => by
    simp only [List.length_nil, Nat.add_zero] at hsum
    have heq : cur = kept := (Finset.eq_of_subset_of_card_le hsub (hcur.trans hsum.symm.le)).symm
    subst heq
    exact ⟨[], trivial, by simp only [List.toFinset_nil, Finset.union_empty]; rfl, le_rfl⟩
  | x :: xs, kept, cur, hnodup, hdisj, hsub, hcur, hsum => by
    rcases List.nodup_cons.mp hnodup with ⟨hxxs, hnodup'⟩
    have hx_kept : x ∉ kept :=
      Finset.disjoint_right.mp hdisj (List.mem_toFinset.mpr List.mem_cons_self)
    have hdisj' : Disjoint (insert x kept) xs.toFinset := by
      rw [List.toFinset_cons, Finset.disjoint_insert_right] at hdisj
      exact Finset.disjoint_insert_left.mpr
        ⟨by simpa only [List.mem_toFinset] using hxxs, hdisj.2⟩
    have hsum' : (insert x kept).card + xs.length = k := by
      rw [Finset.card_insert_of_notMem hx_kept]
      simp only [List.length_cons] at hsum
      omega
    by_cases hx_cur : x ∈ cur
    · have hstep := validStep_hit hcur hx_cur
      obtain ⟨ss, hv, hfin, hcost⟩ := exists_warmup_aux xs (insert x kept) cur hnodup' hdisj'
        (Finset.insert_subset hx_cur hsub) hcur hsum'
      refine ⟨cur :: ss, ⟨hstep, hv⟩, ?_, ?_⟩
      · change (problem α k).finalState cur ss = _
        rw [hfin]
        finset_card [List.toFinset_cons]
      · change stepCost cur x cur + (problem α k).scheduleCost cur xs ss ≤ (x :: xs).length
        rw [stepCost_of_mem hx_cur, Nat.zero_add, List.length_cons]
        omega
    · by_cases hlt : cur.card < k
      · have hstep := validStep_insert hlt hx_cur
        obtain ⟨ss, hv, hfin, hcost⟩ := exists_warmup_aux xs (insert x kept) (insert x cur)
          hnodup' hdisj' (Finset.insert_subset_insert x hsub) hstep.2.1 hsum'
        refine ⟨insert x cur :: ss, ⟨hstep, hv⟩, ?_, ?_⟩
        · change (problem α k).finalState (insert x cur) ss = _
          rw [hfin]
          finset_card [List.toFinset_cons]
        · change stepCost cur x (insert x cur) +
            (problem α k).scheduleCost (insert x cur) xs ss ≤ (x :: xs).length
          rw [stepCost_of_notMem hx_cur, List.length_cons]
          omega
      · have hcur_eq : cur.card = k := by omega
        have hkept_lt : kept.card < cur.card := by
          simp only [List.length_cons] at hsum
          omega
        obtain ⟨e, he_cur, he_not_kept⟩ : ∃ e ∈ cur, e ∉ kept := by
          obtain ⟨e, he⟩ := Finset.card_pos.mp (show 0 < (cur \ kept).card by finset_card)
          exact ⟨e, (Finset.mem_sdiff.mp he).1, (Finset.mem_sdiff.mp he).2⟩
        have hstep := validStep_replace hcur hx_cur he_cur
        have hsub' : insert x kept ⊆ insert x (cur.erase e) := by
          refine Finset.insert_subset_insert x (fun y hy => ?_)
          exact Finset.mem_erase.mpr ⟨fun hye => he_not_kept (hye ▸ hy), hsub hy⟩
        obtain ⟨ss, hv, hfin, hcost⟩ := exists_warmup_aux xs (insert x kept)
          (insert x (cur.erase e)) hnodup' hdisj' hsub' hstep.2.1 hsum'
        refine ⟨insert x (cur.erase e) :: ss, ⟨hstep, hv⟩, ?_, ?_⟩
        · change (problem α k).finalState (insert x (cur.erase e)) ss = _
          rw [hfin]
          finset_card [List.toFinset_cons]
        · change stepCost cur x (insert x (cur.erase e)) +
            (problem α k).scheduleCost (insert x (cur.erase e)) xs ss ≤ (x :: xs).length
          rw [stepCost_of_notMem hx_cur, List.length_cons]
          omega

/-- From any admissible initial cache `s₀` (`s₀.card ≤ k`) and target `k`-page cache `M₀`,
requesting `M₀.toList` reaches terminal offline cache `M₀` in at most `k` faults. -/
private theorem exists_warmup_to_subset {k : ℕ} {s₀ M₀ : Finset α}
    (hs₀ : ValidCache k s₀) (hM₀ : M₀.card = k) :
    ∃ reqs₀ offStates₀,
      (problem α k).ValidSchedule s₀ reqs₀ offStates₀ ∧
      (problem α k).finalState s₀ offStates₀ = M₀ ∧
      (problem α k).scheduleCost s₀ reqs₀ offStates₀ ≤ k := by
  obtain ⟨ss, hv, hfin, hcost⟩ := exists_warmup_aux M₀.toList ∅ s₀ (Finset.nodup_toList M₀)
    (Finset.disjoint_empty_left _) (Finset.empty_subset s₀) hs₀
    (by simp only [Finset.card_empty, Nat.zero_add, Finset.length_toList, hM₀])
  rw [Finset.empty_union, Finset.toList_toFinset] at hfin
  rw [Finset.length_toList, hM₀] at hcost
  exact ⟨M₀.toList, ss, hv, hfin, hcost⟩

/-! ### `ObliviousPagingCost` instances for `BehavioralStrategy` and `RandStrategy` -/

private theorem stepExpectedCost_paging {k : ℕ} (B : BehavioralStrategy (problem α k))
    (m : B.Mem) (p : α) :
    B.stepExpectedCost m p = if p ∈ B.project m then 0 else 1 := by
  simp only [BehavioralStrategy.stepExpectedCost, problem, stepCost]
  by_cases hp : p ∈ B.project m
  · simp only [hp, ↓reduceIte, Nat.cast_zero, mul_zero, tsum_zero]
  · simp only [hp, ↓reduceIte, Nat.cast_one, mul_one]
    exact (B.step m p).tsum_coe

private theorem expectedCost_paging_le_length {k : ℕ} (B : BehavioralStrategy (problem α k))
    {s₀ : Finset α} (hs₀ : ValidCache k s₀) (reqs : List α) :
    B.expectedCost s₀ reqs ≤ reqs.length := by
  rw [BehavioralStrategy.expectedCost]
  simpa only [Nat.cast_one, one_mul] using
    B.expectedCostFrom_le_mul_length (w := 1)
      (fun _ r m' _ => stepCost_le_one _ r (B.project m'))
      ((B.valid_init hs₀).1) reqs

private theorem expectedCost_paging_ne_top {k : ℕ} (B : BehavioralStrategy (problem α k))
    {s₀ : Finset α} (hs₀ : ValidCache k s₀) (reqs : List α) :
    B.expectedCost s₀ reqs ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.natCast_ne_top reqs.length)
    (expectedCost_paging_le_length B hs₀ reqs)

omit [DecidableEq α] in
private theorem one_le_sum_toReal_tsum {β : Type*} (π : PMF β) (S : Finset α)
    (cost₀ : ℝ≥0∞) (cost_next : α → ℝ≥0∞) (step : β → α → ℝ≥0∞)
    (hfin₀ : cost₀ ≠ ⊤)
    (hinc : ∀ x, cost_next x = cost₀ + ∑' b, π b * step b x)
    (hle : ∀ b x, step b x ≤ 1)
    (hsum : ∀ b ∈ π.support, (1 : ℝ≥0∞) ≤ ∑ x ∈ S, step b x) :
    (1 : ℝ) ≤ ∑ x ∈ S, ((cost_next x).toReal - cost₀.toReal) := by
  have hterm_le_one : ∀ x, (∑' b, π b * step b x) ≤ 1 := fun x =>
    Cslib.Probability.PMF.tsum_mul_le_of_support π fun b _ => hle b x
  have hterm_ne_top : ∀ x, (∑' b, π b * step b x) ≠ ⊤ :=
    fun x => ne_top_of_le_ne_top ENNReal.one_ne_top (hterm_le_one x)
  have htoReal_inc : ∀ x, (cost_next x).toReal - cost₀.toReal = (∑' b, π b * step b x).toReal := by
    intro x
    rw [hinc x, ENNReal.toReal_add hfin₀ (hterm_ne_top x), add_sub_cancel_left]
  simp_rw [htoReal_inc]
  have hsum_enn : (1 : ℝ≥0∞) ≤ ∑ x ∈ S, ∑' b, π b * step b x := by
    rw [sum_tsum_ennreal]
    simp only [← Finset.mul_sum]
    calc (1 : ℝ≥0∞) = ∑' b, π b * 1 := by simp only [mul_one, π.tsum_coe]
      _ ≤ ∑' b, π b * ∑ x ∈ S, step b x :=
        Cslib.Probability.PMF.tsum_mul_mono_support π hsum
  have hsum_ne_top : (∑ x ∈ S, ∑' b, π b * step b x) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun x _ => hterm_ne_top x
  have hreal := ENNReal.toReal_mono hsum_ne_top hsum_enn
  rwa [ENNReal.toReal_one, ENNReal.toReal_sum (fun x _ => hterm_ne_top x)] at hreal

/-- Every `BehavioralStrategy (problem α k)` satisfies `ObliviousPagingCost` on any `(k + 1)`-page
subset `S` from any admissible initial cache `s₀`. -/
theorem obliviousPagingCost_behavioral {k : ℕ} (B : BehavioralStrategy (problem α k))
    {s₀ S : Finset α} (hs₀ : ValidCache k s₀) (hS : S.card = k + 1) :
    ObliviousPagingCost S (fun σ => (B.expectedCost s₀ σ).toReal) where
  cost_nil := ENNReal.toReal_zero
  step_nonneg σ x := by
    set μ₀ : PMF B.Mem := PMF.pure (B.init s₀)
    have happ : B.expectedCost s₀ (σ ++ [x]) =
        B.expectedCost s₀ σ + B.expectedCostDist (B.runMemDist μ₀ σ) [x] := by
      simpa only [BehavioralStrategy.expectedCost, ← B.expectedCostDist_pure, μ₀] using
        B.expectedCostDist_append μ₀ σ [x]
    have hfin1 := expectedCost_paging_ne_top B hs₀ σ
    have hfin2 : B.expectedCostDist (B.runMemDist μ₀ σ) [x] ≠ ⊤ := by
      intro htop
      apply expectedCost_paging_ne_top B hs₀ (σ ++ [x])
      rw [happ, htop, add_top]
    rw [happ, ENNReal.toReal_add hfin1 hfin2, add_sub_cancel_left]
    exact ENNReal.toReal_nonneg
  one_le_sum_step σ := by
    set μ₀ : PMF B.Mem := PMF.pure (B.init s₀)
    set ν : PMF B.Mem := B.runMemDist μ₀ σ
    have hν_valid : ∀ m ∈ ν.support, B.ValidMem m := by
      refine B.validMem_runMemDist (fun m hm => ?_) σ
      rw [PMF.support_pure, Set.mem_singleton_iff] at hm
      subst hm
      exact (B.valid_init hs₀).1
    obtain ⟨p₀, _⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    refine one_le_sum_toReal_tsum ν S (B.expectedCost s₀ σ) (fun x => B.expectedCost s₀ (σ ++ [x]))
      B.stepExpectedCost (expectedCost_paging_ne_top B hs₀ σ) (fun x => ?_) (fun m x => ?_)
      (fun m hm => ?_)
    · have h1 : B.expectedCost s₀ (σ ++ [x]) = B.expectedCost s₀ σ + B.expectedCostDist ν [x] := by
        simpa only [BehavioralStrategy.expectedCost, ← B.expectedCostDist_pure, μ₀, ν] using
          B.expectedCostDist_append μ₀ σ [x]
      rw [h1, B.expectedCostDist_cons, B.expectedCostDist_nil, add_zero]
    · rw [stepExpectedCost_paging]
      split_ifs <;> norm_num
    · have hcard_m : (B.project m).card ≤ k :=
        (B.valid_step p₀ (hν_valid m hm) _ (B.step m p₀).support_nonempty.choose_spec).2.1
      have hsdiff_pos : 1 ≤ (S \ B.project m).card := by finset_card
      simp_rw [stepExpectedCost_paging]
      rw [sum_ite_notMem_ennreal S (B.project m)]
      exact_mod_cast hsdiff_pos

omit [DecidableEq α] in
private theorem detStrategy_costFrom_append {P : Problem} (A : DetStrategy P) (m : A.Mem) :
    ∀ reqs₁ reqs₂ : List P.Req,
      A.costFrom m (reqs₁ ++ reqs₂) = A.costFrom m reqs₁ + A.costFrom (A.runMem m reqs₁) reqs₂
  | [], reqs₂ => by simp only [List.nil_append, DetStrategy.costFrom_nil, DetStrategy.runMem_nil,
      Nat.zero_add]
  | r :: rs, reqs₂ => by
    simp only [List.cons_append, DetStrategy.costFrom_cons, DetStrategy.runMem_cons,
      detStrategy_costFrom_append A (A.step m r) rs reqs₂, Nat.add_assoc]

private theorem randStrategy_expectedCost_paging_le_length {k : ℕ}
    (μ : RandStrategy (problem α k)) (s₀ : Finset α) (rs : List α) :
    μ.expectedCost s₀ rs ≤ rs.length := by
  calc μ.expectedCost s₀ rs
      ≤ ∑' A, μ A * (rs.length : ℝ≥0∞) := by
        refine tsum_le_tsum fun A => ?_
        gcongr
        exact Nat.cast_le.mpr (scheduleCost_le_length k s₀ rs _)
    _ = rs.length := by rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

/-- Every `RandStrategy (problem α k)` satisfies `ObliviousPagingCost` on any `(k + 1)`-page subset
`S` from any admissible initial cache `s₀`. -/
theorem obliviousPagingCost_rand {k : ℕ} (μ : RandStrategy (problem α k))
    {s₀ S : Finset α} (hs₀ : ValidCache k s₀) (hS : S.card = k + 1) :
    ObliviousPagingCost S (fun σ => (μ.expectedCost s₀ σ).toReal) where
  cost_nil := by
    have hA0 : ∀ A : DetStrategy (problem α k), A.cost s₀ [] = 0 := fun _ => rfl
    have h0 : μ.expectedCost s₀ [] = 0 := by
      simp only [RandStrategy.expectedCost, hA0, Nat.cast_zero, mul_zero, tsum_zero]
    simp only [h0, ENNReal.toReal_zero]
  step_nonneg σ x := by
    have hsplit : μ.expectedCost s₀ (σ ++ [x]) =
        μ.expectedCost s₀ σ +
          ∑' A, μ A * (A.costFrom (A.runMem (A.init s₀) σ) [x] : ℝ≥0∞) := by
      have hA : ∀ A : DetStrategy (problem α k),
          (A.cost s₀ (σ ++ [x]) : ℝ≥0∞) =
            (A.cost s₀ σ : ℝ≥0∞) + (A.costFrom (A.runMem (A.init s₀) σ) [x] : ℝ≥0∞) := by
        intro A
        rw [A.cost_eq_costFrom hs₀, A.cost_eq_costFrom hs₀, detStrategy_costFrom_append,
          Nat.cast_add]
      simp only [RandStrategy.expectedCost, hA, mul_add, tsum_add]
    have hfin1 : μ.expectedCost s₀ σ ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.natCast_ne_top _)
        (randStrategy_expectedCost_paging_le_length μ s₀ σ)
    have hfin2 : (∑' A, μ A * (A.costFrom (A.runMem (A.init s₀) σ) [x] : ℝ≥0∞)) ≠ ⊤ := by
      intro htop
      apply ne_top_of_le_ne_top (ENNReal.natCast_ne_top _)
        (randStrategy_expectedCost_paging_le_length μ s₀ (σ ++ [x]))
      rw [hsplit, htop, add_top]
    rw [hsplit, ENNReal.toReal_add hfin1 hfin2, add_sub_cancel_left]
    exact ENNReal.toReal_nonneg
  one_le_sum_step σ := by
    set stepA := fun (A : DetStrategy (problem α k)) (x : α) =>
      (A.costFrom (A.runMem (A.init s₀) σ) [x] : ℝ≥0∞)
    have hstepA_eq : ∀ (A : DetStrategy (problem α k)) (x : α),
        stepA A x = if x ∈ A.project (A.runMem (A.init s₀) σ) then 0 else 1 := by
      intro A x
      set m := A.runMem (A.init s₀) σ
      have h1 : A.costFrom m [x] = stepCost (A.project m) x (A.project (A.step m x)) := by
        rw [DetStrategy.costFrom_cons, DetStrategy.costFrom_nil, Nat.add_zero]
      simp only [stepA, m, h1, stepCost]
      split_ifs <;> norm_num
    obtain ⟨p₀, _⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    refine one_le_sum_toReal_tsum μ S (μ.expectedCost s₀ σ) (fun x => μ.expectedCost s₀ (σ ++ [x]))
      stepA (ne_top_of_le_ne_top (ENNReal.natCast_ne_top _)
        (randStrategy_expectedCost_paging_le_length μ s₀ σ))
      (fun x => ?_) (fun A x => ?_) (fun A _ => ?_)
    · have hA : ∀ A : DetStrategy (problem α k),
          (A.cost s₀ (σ ++ [x]) : ℝ≥0∞) = (A.cost s₀ σ : ℝ≥0∞) + stepA A x := by
        intro A
        rw [A.cost_eq_costFrom hs₀, A.cost_eq_costFrom hs₀, detStrategy_costFrom_append,
          Nat.cast_add]
      simp only [RandStrategy.expectedCost, hA, mul_add, tsum_add]
    · rw [hstepA_eq]
      split_ifs <;> norm_num
    · have hvm : A.ValidMem (A.runMem (A.init s₀) σ) :=
        A.validMem_runMem (A.valid_init hs₀).1 σ
      have hcard_m : (A.project (A.runMem (A.init s₀) σ)).card ≤ k :=
        (A.valid_step p₀ hvm).2.1
      have hsdiff_pos : 1 ≤ (S \ A.project (A.runMem (A.init s₀) σ)).card := by finset_card
      simp_rw [hstepA_eq]
      rw [sum_ite_notMem_ennreal S (A.project (A.runMem (A.init s₀) σ))]
      exact_mod_cast hsdiff_pos

/-! ### Main `H_k` lower-bound theorems (FKLMSY Theorem 4 & Corollary 5) -/

private theorem not_competitive_of_oblivious_cost {k : ℕ} (hk : 0 < k) {s₀ S : Finset α}
    {costE : List α → ℝ≥0∞} (hs₀ : ValidCache k s₀) (hS : S.card = k + 1)
    (hobl : ObliviousPagingCost S (fun σ => (costE σ).toReal))
    {c b : ℝ≥0∞} (hc : c < ENNReal.ofReal (harmonic k)) (hb : b ≠ ⊤)
    (hcomp : ∀ reqs offStates, (problem α k).ValidSchedule s₀ reqs offStates →
      costE reqs ≤ c * (problem α k).scheduleCost s₀ reqs offStates + b) : False := by
  have hc_ne_top : c ≠ ⊤ := ne_top_of_lt hc
  have hc_lt : c.toReal < (harmonic k : ℝ) :=
    (ENNReal.lt_ofReal_iff_toReal_lt hc_ne_top).mp hc
  obtain ⟨M₀, hM₀_sub, hM₀_card⟩ :=
    Finset.exists_subset_card_eq (show k ≤ S.card by omega)
  obtain ⟨reqs₀, ss₀, hv₀, hfin₀, hcost₀⟩ := exists_warmup_to_subset hs₀ hM₀_card
  set gap : ℝ := (harmonic k : ℝ) - c.toReal
  have hgap_pos : 0 < gap := sub_pos.mpr hc_lt
  obtain ⟨m, hm⟩ := exists_nat_gt ((c.toReal * (k : ℝ) + b.toReal) / gap)
  have hm_ineq : c.toReal * (k : ℝ) + b.toReal < (m : ℝ) * gap :=
    (div_lt_iff₀ hgap_pos).mp hm
  obtain ⟨reqs_p, ss_p, hv_p, hcost_p, hgain_p⟩ :=
    exists_phases hk hobl hS hM₀_sub hM₀_card m reqs₀
  have hsched : (problem α k).ValidSchedule s₀ (reqs₀ ++ reqs_p) (ss₀ ++ ss_p) := by
    apply (problem α k).validSchedule_append hv₀
    rwa [hfin₀]
  have hoff_le : (problem α k).scheduleCost s₀ (reqs₀ ++ reqs_p) (ss₀ ++ ss_p) ≤ k + m := by
    rw [(problem α k).scheduleCost_append hv₀.length_eq, hfin₀, hcost_p]
    exact Nat.add_le_add_right hcost₀ m
  have hbase_nonneg : 0 ≤ (costE reqs₀).toReal := ENNReal.toReal_nonneg
  have honline_ge : (m : ℝ) * (harmonic k : ℝ) ≤ (costE (reqs₀ ++ reqs_p)).toReal := by linarith
  have hbound := hcomp (reqs₀ ++ reqs_p) (ss₀ ++ ss_p) hsched
  have hrhs_ne_top :
      c * ((problem α k).scheduleCost s₀ (reqs₀ ++ reqs_p) (ss₀ ++ ss_p) : ℝ≥0∞) + b ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top hc_ne_top (ENNReal.natCast_ne_top _), hb⟩
  have hreal_bound := ENNReal.toReal_mono hrhs_ne_top hbound
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top hc_ne_top (ENNReal.natCast_ne_top _)) hb,
    ENNReal.toReal_mul, ENNReal.toReal_natCast] at hreal_bound
  have hoff_real :
      ((problem α k).scheduleCost s₀ (reqs₀ ++ reqs_p) (ss₀ ++ ss_p) : ℝ) ≤
        (k : ℝ) + (m : ℝ) := by
    exact_mod_cast hoff_le
  have hmul_le :
      c.toReal * ((problem α k).scheduleCost s₀ (reqs₀ ++ reqs_p) (ss₀ ++ ss_p) : ℝ) ≤
        c.toReal * ((k : ℝ) + (m : ℝ)) :=
    mul_le_mul_of_nonneg_left hoff_real ENNReal.toReal_nonneg
  have hexpand : (m : ℝ) * gap = (m : ℝ) * (harmonic k : ℝ) - c.toReal * (m : ℝ) := by
    simp only [gap]; ring
  linarith

/-- **Exact `m`-phase randomized lower-bound witness (`BehavioralStrategy`)**: from any full initial
cache `s₀ ⊆ S` (`s₀.card = k`, `S.card = k + 1`, `0 < k`), there is a request sequence on which
`B.expectedCost` is at least `m * H_k` while a valid offline schedule incurs exactly `m` faults. -/
theorem exists_witness_behavioral_of_card_eq {k : ℕ} (hk : 0 < k)
    (B : BehavioralStrategy (problem α k)) {s₀ S : Finset α}
    (hs₀_sub : s₀ ⊆ S) (hs₀_card : s₀.card = k) (hS : S.card = k + 1) (m : ℕ) :
    ∃ reqs offStates,
      (problem α k).ValidSchedule s₀ reqs offStates ∧
      (problem α k).scheduleCost s₀ reqs offStates = m ∧
      (m : ℝ≥0∞) * ENNReal.ofReal (harmonic k) ≤ B.expectedCost s₀ reqs := by
  have hs₀ : ValidCache k s₀ := hs₀_card.le
  have hobl := obliviousPagingCost_behavioral B hs₀ hS
  obtain ⟨reqs, offStates, hv, hcost, hgain⟩ :=
    exists_phases hk hobl hS hs₀_sub hs₀_card m []
  simp only [List.nil_append, hobl.cost_nil, sub_zero] at hgain
  refine ⟨reqs, offStates, hv, hcost, ?_⟩
  rw [← ENNReal.ofReal_natCast m, ← ENNReal.ofReal_mul (Nat.cast_nonneg m),
    ← ENNReal.ofReal_toReal (expectedCost_paging_ne_top B hs₀ reqs)]
  exact ENNReal.ofReal_le_ofReal hgain

/-- **FKLMSY Theorem 4 & Corollary 5 (`BehavioralStrategy.IsCompetitiveFrom`)**
[FiatKarpLubyMcGeochSleatorYoung1991]: over any universe containing a `(k + 1)`-element subset `S`
(`0 < k`), no behavioural randomized paging strategy is `(c, b)`-competitive from any admissible
initial cache `s₀` (including `∅`) for `c < H_k` and finite `b ≠ ⊤`. -/
theorem not_isCompetitiveFrom_behavioral_of_lt {k : ℕ} (hk : 0 < k)
    (B : BehavioralStrategy (problem α k)) {s₀ S : Finset α}
    (hs₀ : ValidCache k s₀) (hS : S.card = k + 1)
    {c b : ℝ≥0∞} (hc : c < ENNReal.ofReal (harmonic k)) (hb : b ≠ ⊤) :
    ¬ B.IsCompetitiveFrom s₀ c b :=
  not_competitive_of_oblivious_cost hk hs₀ hS (obliviousPagingCost_behavioral B hs₀ hS) hc hb

/-- **FKLMSY Corollary 5 (`BehavioralStrategy.IsCompetitive`)**
[FiatKarpLubyMcGeochSleatorYoung1991]: over `≥ k + 1` pages (`0 < k`), no behavioural randomized
paging strategy is `(c, b)`-competitive for `c < H_k` and `b ≠ ⊤`. -/
theorem not_isCompetitive_behavioral_of_lt {k : ℕ} (hk : 0 < k)
    (B : BehavioralStrategy (problem α k)) {S : Finset α} (hS : S.card = k + 1)
    {c b : ℝ≥0∞} (hc : c < ENNReal.ofReal (harmonic k)) (hb : b ≠ ⊤) :
    ¬ B.IsCompetitive c b :=
  fun h => not_isCompetitiveFrom_behavioral_of_lt hk B (validCache_empty k) hS hc hb
    (h ∅ (validCache_empty k))

/-- Over `≥ k + 1` pages (`0 < k`), no behavioural randomized paging strategy is
`(c, b)`-competitive across arbitrary initial caches for `c < H_k` and `b ≠ ⊤`. -/
theorem not_isCompetitiveAnyInit_behavioral_of_lt {k : ℕ} (hk : 0 < k)
    (B : BehavioralStrategy (problem α k)) {S : Finset α} (hS : S.card = k + 1)
    {c b : ℝ≥0∞} (hc : c < ENNReal.ofReal (harmonic k)) (hb : b ≠ ⊤) :
    ¬ B.IsCompetitiveAnyInit c b :=
  fun h => not_isCompetitive_behavioral_of_lt hk B hS hc hb h.toIsCompetitive

/-- Canonical `BehavioralStrategy` lower bound on `Fin n` (`0 < k < n`): no behavioural strategy is
`(c, b)`-competitive from `∅` for `c < H_k` and `b ≠ ⊤`. -/
theorem fin_not_isCompetitiveFrom_empty_behavioral_of_lt {k n : ℕ} (hk : 0 < k) (hkn : k < n)
    (B : BehavioralStrategy (problem (Fin n) k))
    {c b : ℝ≥0∞} (hc : c < ENNReal.ofReal (harmonic k)) (hb : b ≠ ⊤) :
    ¬ B.IsCompetitiveFrom ∅ c b := by
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n))) (by simp only [Finset.card_fin]; omega : k + 1 ≤ _)
  exact not_isCompetitiveFrom_behavioral_of_lt hk B (validCache_empty k) hS hc hb

/-- **FKLMSY Theorem 4 & Corollary 5 (`RandStrategy.IsCompetitiveFrom`)**
[FiatKarpLubyMcGeochSleatorYoung1991]: over any universe containing a `(k + 1)`-element subset `S`
(`0 < k`), no discrete-mixture randomized paging strategy is `(c, b)`-competitive from any
admissible initial cache `s₀` for `c < H_k` and `b ≠ ⊤`. -/
theorem not_isCompetitiveFrom_rand_of_lt {k : ℕ} (hk : 0 < k)
    (μ : RandStrategy (problem α k)) {s₀ S : Finset α}
    (hs₀ : ValidCache k s₀) (hS : S.card = k + 1)
    {c b : ℝ≥0∞} (hc : c < ENNReal.ofReal (harmonic k)) (hb : b ≠ ⊤) :
    ¬ μ.IsCompetitiveFrom s₀ c b :=
  not_competitive_of_oblivious_cost hk hs₀ hS (obliviousPagingCost_rand μ hs₀ hS) hc hb

/-- **FKLMSY Corollary 5 (`RandStrategy.IsCompetitive`)** [FiatKarpLubyMcGeochSleatorYoung1991]:
over `≥ k + 1` pages (`0 < k`), no `RandStrategy` is `(c, b)`-competitive for `c < H_k` and
`b ≠ ⊤`. -/
theorem not_isCompetitive_rand_of_lt {k : ℕ} (hk : 0 < k)
    (μ : RandStrategy (problem α k)) {S : Finset α} (hS : S.card = k + 1)
    {c b : ℝ≥0∞} (hc : c < ENNReal.ofReal (harmonic k)) (hb : b ≠ ⊤) :
    ¬ μ.IsCompetitive c b :=
  fun h => not_isCompetitiveFrom_rand_of_lt hk μ (validCache_empty k) hS hc hb
    (h ∅ (validCache_empty k))

/-- Canonical `RandStrategy` lower bound on `Fin n` (`0 < k < n`): no `RandStrategy` is
`(c, b)`-competitive from `∅` for `c < H_k` and `b ≠ ⊤`. -/
theorem fin_not_isCompetitiveFrom_empty_rand_of_lt {k n : ℕ} (hk : 0 < k) (hkn : k < n)
    (μ : RandStrategy (problem (Fin n) k))
    {c b : ℝ≥0∞} (hc : c < ENNReal.ofReal (harmonic k)) (hb : b ≠ ⊤) :
    ¬ μ.IsCompetitiveFrom ∅ c b := by
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n))) (by simp only [Finset.card_fin]; omega : k + 1 ≤ _)
  exact not_isCompetitiveFrom_rand_of_lt hk μ (validCache_empty k) hS hc hb

/-! ### FKLMSY Theorem 2: `markingStrategy` is `(H_k, 0)`-competitive on `≤ k + 1` pages -/

private theorem cleanCount_active_card_le {k : ℕ} (hk : 0 < k) {U : Finset α}
    (hU : U.card ≤ k + 1) :
    ∀ {tr : MarkTracker α} {s_off : Finset α} {reqs : List α} {offStates : List (Finset α)},
      ValidTracker k tr →
      tr.marked ∪ tr.stale = U →
      tr.marked.card + tr.staleCached = k →
      (∀ p ∈ reqs, p ∈ U) →
      (problem α k).ValidSchedule s_off reqs offStates →
      cleanCount k tr reqs ≤
        (if tr.marked ⊆ s_off then 0 else 1) + (problem α k).scheduleCost s_off reqs offStates
  | tr, s_off, [], [], _, _, _, _, _ => Nat.zero_le _
  | _, _, [], _ :: _, _, _, _, _, hv => nomatch hv
  | _, _, _ :: _, [], _, _, _, _, hv => nomatch hv
  | tr, s_off, p :: rs, s_off' :: ss, htr, hcov, hsum, hmem, ⟨hstep, hrest⟩ => by
    have hpU : p ∈ U := hmem p List.mem_cons_self
    have hmem' : ∀ q ∈ rs, q ∈ U := fun q hq => hmem q (List.mem_cons_of_mem p hq)
    have htr' := validTracker_step hk htr p
    change (if isCleanReq tr p then 1 else 0) + cleanCount k (stepTracker k tr p) rs ≤
      (if tr.marked ⊆ s_off then 0 else 1) +
        (stepCost s_off p s_off' + (problem α k).scheduleCost s_off' rs ss)
    by_cases hpM : p ∈ tr.marked
    · have hclean : isCleanReq tr p = false := by simp [isCleanReq, hpM]
      have hstep_tr : stepTracker k tr p = tr := by simp [stepTracker, hpM]
      rw [hclean, hstep_tr]
      simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
      have hih := cleanCount_active_card_le hk hU htr hcov hsum hmem' hrest
      by_cases hp_off : p ∈ s_off
      · rw [validStep_hit_eq hstep hp_off] at hih ⊢
        rw [stepCost_of_mem hp_off]
        omega
      · rw [stepCost_of_notMem hp_off]
        split_ifs at hih ⊢ <;> omega
    · by_cases ht0 : tr.staleCached = 0
      · have hM_card : tr.marked.card = k := by omega
        have hnotlt : ¬ tr.marked.card < k := by omega
        have hclean : isCleanReq tr p = true := by simp [isCleanReq, hpM, ht0]
        have hstep_tr : stepTracker k tr p = ⟨{p}, tr.marked, k - 1⟩ := by
          simp [stepTracker, hpM, ht0, hnotlt]
        rw [hclean, hstep_tr]
        simp only [↓reduceIte]
        have hcov' : ({p} : Finset α) ∪ tr.marked = U := by
          apply Finset.eq_of_subset_of_card_le
          · refine Finset.union_subset (Finset.singleton_subset_iff.mpr hpU) ?_
            rw [← hcov]
            exact Finset.subset_union_left
          · have hcard : (({p} : Finset α) ∪ tr.marked).card = k + 1 := by finset_card
            omega
        have hsum' : ({p} : Finset α).card + (k - 1) = k := by
          simp only [Finset.card_singleton]; omega
        have hih := cleanCount_active_card_le hk hU (hstep_tr ▸ htr') hcov' hsum' hmem' hrest
        have hp_in_s' : ({p} : Finset α) ⊆ s_off' := Finset.singleton_subset_iff.mpr hstep.2.2.1
        dsimp only at hih
        simp only [hp_in_s', ↓reduceIte, zero_add] at hih
        by_cases hp_off : p ∈ s_off
        · have hnot_sub : ¬ tr.marked ⊆ s_off := by
            intro hsub
            have heq : tr.marked = s_off :=
              Finset.eq_of_subset_of_card_le hsub (hstep.1.trans hM_card.symm.le)
            exact hpM (heq ▸ hp_off)
          simp only [hnot_sub, ↓reduceIte, stepCost_of_mem hp_off]
          omega
        · rw [stepCost_of_notMem hp_off]
          split_ifs <;> omega
      · have hpS : p ∈ tr.stale := by
          rw [← hcov, Finset.mem_union] at hpU
          exact hpU.resolve_left hpM
        have hclean : isCleanReq tr p = false := by simp [isCleanReq, hpM, ht0, hpS]
        have hstep_tr : stepTracker k tr p =
            ⟨insert p tr.marked, tr.stale.erase p, tr.staleCached - 1⟩ := by
          simp [stepTracker, hpM, ht0, hpS]
        rw [hclean, hstep_tr]
        simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
        have hcov' : insert p tr.marked ∪ tr.stale.erase p = U := by
          rw [← hcov]
          finset_card
        have hsum' : (insert p tr.marked).card + (tr.staleCached - 1) = k := by finset_card
        have hih := cleanCount_active_card_le hk hU (hstep_tr ▸ htr') hcov' hsum' hmem' hrest
        dsimp only at hih
        by_cases hp_off : p ∈ s_off
        · rw [validStep_hit_eq hstep hp_off] at hih ⊢
          rw [stepCost_of_mem hp_off]
          by_cases hsub : tr.marked ⊆ s_off
          · have hsub' : insert p tr.marked ⊆ s_off := Finset.insert_subset hp_off hsub
            simp only [hsub, hsub', ↓reduceIte] at hih ⊢
            omega
          · simp only [hsub, ↓reduceIte]
            split_ifs at hih <;> omega
        · rw [stepCost_of_notMem hp_off]
          split_ifs at hih ⊢ <;> omega

private theorem cleanCount_warmup_card_le {k : ℕ} (hk : 0 < k) {U : Finset α}
    (hU : U.card ≤ k + 1) :
    ∀ {M s_off : Finset α} {reqs : List α} {offStates : List (Finset α)},
      M.card ≤ k → M ⊆ U → s_off ⊆ M → (∀ p ∈ reqs, p ∈ U) →
      (problem α k).ValidSchedule s_off reqs offStates →
      cleanCount k ⟨M, ∅, 0⟩ reqs ≤ (problem α k).scheduleCost s_off reqs offStates
  | _, _, [], [], _, _, _, _, _ => Nat.zero_le _
  | _, _, [], _ :: _, _, _, _, _, hv => nomatch hv
  | _, _, _ :: _, [], _, _, _, _, hv => nomatch hv
  | M, s_off, p :: rs, s_off' :: ss, hM_card, hMU, hsub, hmem, ⟨hstep, hrest⟩ => by
    have hpU : p ∈ U := hmem p List.mem_cons_self
    have hmem' : ∀ q ∈ rs, q ∈ U := fun q hq => hmem q (List.mem_cons_of_mem p hq)
    change (if isCleanReq ⟨M, ∅, 0⟩ p then 1 else 0) +
        cleanCount k (stepTracker k ⟨M, ∅, 0⟩ p) rs ≤
      stepCost s_off p s_off' + (problem α k).scheduleCost s_off' rs ss
    by_cases hpM : p ∈ M
    · have hclean : isCleanReq ⟨M, ∅, 0⟩ p = false := by simp [isCleanReq, hpM]
      have hstep_tr : stepTracker k ⟨M, ∅, 0⟩ p = ⟨M, ∅, 0⟩ := by simp [stepTracker, hpM]
      have hs_off'_sub : s_off' ⊆ M := by
        by_cases hp_off : p ∈ s_off
        · rw [validStep_hit_eq hstep hp_off]
          exact hsub
        · exact (validStep_miss_subset hstep hp_off).trans (Finset.insert_subset hpM hsub)
      rw [hclean, hstep_tr]
      simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
      have hih := cleanCount_warmup_card_le hk hU hM_card hMU hs_off'_sub hmem' hrest
      omega
    · have hp_off : p ∉ s_off := fun hp => hpM (hsub hp)
      have hcost1 : stepCost s_off p s_off' = 1 := stepCost_of_notMem hp_off
      have hclean : isCleanReq ⟨M, ∅, 0⟩ p = true := by simp [isCleanReq, hpM]
      rw [hclean, hcost1]
      simp only [↓reduceIte]
      by_cases hlt : M.card < k
      · have hstep_tr : stepTracker k ⟨M, ∅, 0⟩ p = ⟨insert p M, ∅, 0⟩ := by
          simp [stepTracker, hpM, hlt]
        rw [hstep_tr]
        have hs_off'_sub : s_off' ⊆ insert p M :=
          (validStep_miss_subset hstep hp_off).trans (Finset.insert_subset_insert p hsub)
        have hih := cleanCount_warmup_card_le hk hU (by finset_card)
          (Finset.insert_subset hpU hMU) hs_off'_sub hmem' hrest
        omega
      · have hM_eq : M.card = k := by omega
        have hstep_tr : stepTracker k ⟨M, ∅, 0⟩ p = ⟨{p}, M, k - 1⟩ := by
          simp [stepTracker, hpM, hlt]
        rw [hstep_tr]
        have htr_init : ValidTracker k ⟨M, ∅, 0⟩ :=
          ⟨Finset.disjoint_empty_right M, le_rfl, Nat.zero_le k, hM_card,
            fun h => absurd h (Nat.lt_irrefl 0)⟩
        have htr_new : ValidTracker k ⟨{p}, M, k - 1⟩ :=
          hstep_tr ▸ validTracker_step hk htr_init p
        have hcov : ({p} : Finset α) ∪ M = U := by
          apply Finset.eq_of_subset_of_card_le
            (Finset.union_subset (Finset.singleton_subset_iff.mpr hpU) hMU)
          have hcard : (({p} : Finset α) ∪ M).card = k + 1 := by
            rw [Finset.singleton_union, Finset.card_insert_of_notMem hpM, hM_eq]
          omega
        have hsum : ({p} : Finset α).card + (k - 1) = k := by
          simp only [Finset.card_singleton]; omega
        have hact := cleanCount_active_card_le hk hU htr_new hcov hsum hmem' hrest
        have hp_in_s' : ({p} : Finset α) ⊆ s_off' := Finset.singleton_subset_iff.mpr hstep.2.2.1
        dsimp only at hact
        simp only [hp_in_s', ↓reduceIte, zero_add] at hact
        omega

/-- **One-window clean-request bound on `≤ k + 1` pages**
([FiatKarpLubyMcGeochSleatorYoung1991], Section 3, proof of Theorem 2): when the initial cache `s₀`
and all requested pages lie in a set `U` of size at most `k + 1`, `cleanCount` never exceeds the
fault cost of any valid offline schedule from `s₀` (factor `1` instead of `2`). -/
theorem cleanCount_le_scheduleCost_of_subset {k : ℕ} (hk : 0 < k) {U s₀ : Finset α}
    (hU : U.card ≤ k + 1) (hs₀ : ValidCache k s₀) (hs₀U : s₀ ⊆ U)
    {reqs : List α} (hreqs : ∀ p ∈ reqs, p ∈ U) {offStates : List (Finset α)}
    (hv : (problem α k).ValidSchedule s₀ reqs offStates) :
    cleanCount k (initTracker s₀) reqs ≤ (problem α k).scheduleCost s₀ reqs offStates :=
  cleanCount_warmup_card_le hk hU hs₀ hs₀U (Finset.Subset.refl s₀) hreqs hv

/-- Expected-cost bound of `markingStrategy` when `s₀` and `reqs` lie in `U` with `U.card ≤ k + 1`:
`E[MARK] ≤ H_k · OPT`. -/
theorem markingStrategy_expectedCost_le_of_subset {k : ℕ} (hk : 0 < k) {U s₀ : Finset α}
    (hU : U.card ≤ k + 1) (hs₀ : ValidCache k s₀) (hs₀U : s₀ ⊆ U)
    {reqs : List α} (hreqs : ∀ p ∈ reqs, p ∈ U) {offStates : List (Finset α)}
    (hv : (problem α k).ValidSchedule s₀ reqs offStates) :
    (markingStrategy k hk).expectedCost s₀ reqs ≤
      ENNReal.ofReal (harmonic k) * (problem α k).scheduleCost s₀ reqs offStates := by
  rw [expectedCost_markingStrategy_eq hk hs₀]
  have h1 := trackerExpectedCost_le_harmonic_mul_cleanCount hk hs₀ reqs
  have h2 : (cleanCount k (initTracker s₀) reqs : ℚ) ≤
      ((problem α k).scheduleCost s₀ reqs offStates : ℚ) := by
    exact_mod_cast cleanCount_le_scheduleCost_of_subset hk hU hs₀ hs₀U hreqs hv
  have hrat : trackerExpectedCost k (initTracker s₀) reqs ≤
      harmonic k * ((problem α k).scheduleCost s₀ reqs offStates : ℚ) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 (harmonic_nonneg k))
  have hreal : (trackerExpectedCost k (initTracker s₀) reqs : ℝ) ≤
      (harmonic k : ℝ) * ((problem α k).scheduleCost s₀ reqs offStates : ℝ) := by
    simpa only [Rat.cast_mul, Rat.cast_natCast] using (Rat.cast_le (K := ℝ)).mpr hrat
  have hhk : (0 : ℝ) ≤ (harmonic k : ℝ) := by exact_mod_cast harmonic_nonneg k
  calc ENNReal.ofReal (trackerExpectedCost k (initTracker s₀) reqs)
      ≤ ENNReal.ofReal
          ((harmonic k : ℝ) * ((problem α k).scheduleCost s₀ reqs offStates : ℝ)) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (harmonic k) * (problem α k).scheduleCost s₀ reqs offStates := by
        rw [ENNReal.ofReal_mul hhk, ENNReal.ofReal_natCast]

/-- **FKLMSY Theorem 2 (`markingthm2`)** [FiatKarpLubyMcGeochSleatorYoung1991]: on any page
universe of size at most `k + 1` (`0 < k`), `markingStrategy` is `(H_k, 0)`-competitive against an
oblivious adversary. -/
theorem markingStrategy_isCompetitive_of_card_le [Fintype α] {k : ℕ} (hk : 0 < k)
    (hcard : Fintype.card α ≤ k + 1) :
    (markingStrategy (α := α) k hk).IsCompetitive (ENNReal.ofReal (harmonic k)) 0 := by
  intro s₀ hs₀ reqs offStates hv
  rw [add_zero]
  exact markingStrategy_expectedCost_le_of_subset hk (U := Finset.univ)
    (by simpa only [Finset.card_univ] using hcard) hs₀ (Finset.subset_univ _)
    (fun _ _ => Finset.mem_univ _) hv

/-- **Exact `H_k` randomized minimax value on `Fin (k + 1)`** (combining FKLMSY Theorem 2 and
Theorem 4): `markingStrategy` achieves `(H_k, 0)`-competitiveness on `Fin (k + 1)`, while no
behavioural randomized strategy achieves `(c, b)`-competitiveness from `∅` for any `c < H_k` and
`b ≠ ⊤`. -/
theorem markingStrategy_tight_on_fin_succ {k : ℕ} (hk : 0 < k) :
    (markingStrategy (α := Fin (k + 1)) k hk).IsCompetitive (ENNReal.ofReal (harmonic k)) 0 ∧
      ∀ (B : BehavioralStrategy (problem (Fin (k + 1)) k)) {c b : ℝ≥0∞},
        c < ENNReal.ofReal (harmonic k) → b ≠ ⊤ → ¬ B.IsCompetitiveFrom ∅ c b :=
  ⟨markingStrategy_isCompetitive_of_card_le hk (by simp),
    fun B {_ _} hc hb =>
      fin_not_isCompetitiveFrom_empty_behavioral_of_lt hk (Nat.lt_succ_self k) B hc hb⟩

end Nemesis

/-! ### FKLMSY Section 3 separation: `markingStrategy` is not `H_2`-competitive on `Fin 4` -/

section FinFourSeparation

/-- Eight-request cyclic block `[2, 3, 0, 1, 3, 2, 1, 0]` on `Fin 4` realizing the `k = 2, n = 4`
counterexample of [FiatKarpLubyMcGeochSleatorYoung1991], Section 3. -/
private def fin4Block : List (Fin 4) := [2, 3, 0, 1, 3, 2, 1, 0]

private def fin4OffBlockStates : List (Finset (Fin 4)) :=
  [{0, 2}, {0, 3}, {0, 3}, {1, 3}, {1, 3}, {1, 2}, {1, 2}, {0, 2}]

private theorem trackerExpectedCost_append_fin4 (tr : MarkTracker (Fin 4)) :
    ∀ rs₁ rs₂ : List (Fin 4),
      trackerExpectedCost 2 tr (rs₁ ++ rs₂) =
        trackerExpectedCost 2 tr rs₁ + trackerExpectedCost 2 (runTracker 2 tr rs₁) rs₂
  | [], _ => by simp only [List.nil_append, trackerExpectedCost, runTracker, zero_add]
  | p :: ps, rs₂ => by
    simp only [List.cons_append, trackerExpectedCost, runTracker,
      trackerExpectedCost_append_fin4 (stepTracker 2 tr p) ps rs₂, add_assoc]

private theorem runTracker_append_fin4 (tr : MarkTracker (Fin 4)) :
    ∀ rs₁ rs₂ : List (Fin 4),
      runTracker 2 tr (rs₁ ++ rs₂) = runTracker 2 (runTracker 2 tr rs₁) rs₂
  | [], _ => rfl
  | p :: ps, rs₂ => runTracker_append_fin4 (stepTracker 2 tr p) ps rs₂

private theorem clean_pair_fin4 {M stale : Finset (Fin 4)} {a b : Fin 4}
    (hcard : ¬ M.card < 2) (ha : a ∉ M) (hb : b ∉ M) (hab : b ≠ a) :
    trackerExpectedCost 2 ⟨M, stale, 0⟩ [a, b] = 2 ∧
      runTracker 2 ⟨M, stale, 0⟩ [a, b] = ⟨{b, a}, M, 0⟩ := by
  have hs1 : stepTracker 2 ⟨M, stale, 0⟩ a = ⟨{a}, M, 1⟩ := by
    simp only [stepTracker, ha, hcard, ↓reduceIte]
  have hc1 : stepTrackerCost ⟨M, stale, 0⟩ a = 1 := by
    simp only [stepTrackerCost, ha, ↓reduceIte]
  have hba : b ∉ ({a} : Finset (Fin 4)) := by simpa only [Finset.mem_singleton] using hab
  have hs2 : stepTracker 2 ⟨{a}, M, 1⟩ b = ⟨{b, a}, M, 0⟩ := by
    simp only [stepTracker, hba, hb, Nat.one_ne_zero, ↓reduceIte, Nat.sub_self]
  have hc2 : stepTrackerCost ⟨{a}, M, 1⟩ b = 1 := by
    simp only [stepTrackerCost, hba, hb, Nat.one_ne_zero, ↓reduceIte]
  refine ⟨?_, ?_⟩
  · change stepTrackerCost ⟨M, stale, 0⟩ a +
      (stepTrackerCost (stepTracker 2 ⟨M, stale, 0⟩ a) b + 0) = 2
    rw [hc1, hs1, hc2]
    norm_num
  · change stepTracker 2 (stepTracker 2 ⟨M, stale, 0⟩ a) b = _
    rw [hs1, hs2]

private theorem marking_fin4Block_step (stale : Finset (Fin 4)) :
    trackerExpectedCost 2 ⟨{0, 1}, stale, 0⟩ fin4Block = 8 ∧
      runTracker 2 ⟨{0, 1}, stale, 0⟩ fin4Block = ⟨{0, 1}, {2, 3}, 0⟩ := by
  have hsplit : fin4Block = ([2, 3] ++ [0, 1]) ++ ([3, 2] ++ [1, 0]) := rfl
  obtain ⟨hc1, hr1⟩ := clean_pair_fin4 (M := {0, 1}) (stale := stale) (a := 2) (b := 3)
    (by decide) (by decide) (by decide) (by decide)
  rw [Finset.pair_comm 3 2] at hr1
  obtain ⟨hc2, hr2⟩ := clean_pair_fin4 (M := {2, 3}) (stale := {0, 1}) (a := 0) (b := 1)
    (by decide) (by decide) (by decide) (by decide)
  rw [Finset.pair_comm 1 0] at hr2
  obtain ⟨hc3, hr3⟩ := clean_pair_fin4 (M := {0, 1}) (stale := {2, 3}) (a := 3) (b := 2)
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨hc4, hr4⟩ := clean_pair_fin4 (M := {2, 3}) (stale := {0, 1}) (a := 1) (b := 0)
    (by decide) (by decide) (by decide) (by decide)
  refine ⟨?_, ?_⟩
  · rw [hsplit, trackerExpectedCost_append_fin4, trackerExpectedCost_append_fin4,
      runTracker_append_fin4, hc1, hr1, hc2, hr2, trackerExpectedCost_append_fin4, hc3, hr3, hc4]
    norm_num
  · rw [hsplit, runTracker_append_fin4, runTracker_append_fin4, runTracker_append_fin4,
      hr1, hr2, hr3, hr4]

private theorem marking_fin4Block_iter (stale : Finset (Fin 4)) :
    ∀ m : ℕ,
      trackerExpectedCost 2 ⟨{0, 1}, stale, 0⟩ ((List.replicate m fin4Block).flatten) =
        8 * (m : ℚ)
  | 0 => by simp only [List.replicate_zero, List.flatten_nil, trackerExpectedCost, Nat.cast_zero,
      mul_zero]
  | m + 1 => by
    rw [List.replicate_succ, List.flatten_cons, trackerExpectedCost_append_fin4]
    obtain ⟨hc, hr⟩ := marking_fin4Block_step stale
    rw [hc, hr, marking_fin4Block_iter {2, 3} m]
    push_cast
    ring

private theorem offline_fin4Block_first :
    (problem (Fin 4) 2).ValidSchedule ({0, 1} : Finset (Fin 4)) fin4Block fin4OffBlockStates ∧
      (problem (Fin 4) 2).finalState ({0, 1} : Finset (Fin 4)) fin4OffBlockStates = {0, 2} ∧
      (problem (Fin 4) 2).scheduleCost ({0, 1} : Finset (Fin 4)) fin4Block fin4OffBlockStates =
        5 := by
  simp only [fin4Block, fin4OffBlockStates, Problem.ValidSchedule, ValidStep, Problem.finalState,
    Problem.scheduleCost, stepCost]
  decide

private theorem offline_fin4Block_steady :
    (problem (Fin 4) 2).ValidSchedule ({0, 2} : Finset (Fin 4)) fin4Block fin4OffBlockStates ∧
      (problem (Fin 4) 2).finalState ({0, 2} : Finset (Fin 4)) fin4OffBlockStates = {0, 2} ∧
      (problem (Fin 4) 2).scheduleCost ({0, 2} : Finset (Fin 4)) fin4Block fin4OffBlockStates =
        4 := by
  simp only [fin4Block, fin4OffBlockStates, Problem.ValidSchedule, ValidStep, Problem.finalState,
    Problem.scheduleCost, stepCost]
  decide

private theorem offline_fin4Block_iter :
    ∀ m : ℕ, ∃ offStates,
      (problem (Fin 4) 2).ValidSchedule ({0, 2} : Finset (Fin 4))
        ((List.replicate m fin4Block).flatten) offStates ∧
      (problem (Fin 4) 2).scheduleCost ({0, 2} : Finset (Fin 4))
        ((List.replicate m fin4Block).flatten) offStates = 4 * m
  | 0 => ⟨[], trivial, rfl⟩
  | m + 1 => by
    obtain ⟨hv1, hfin1, hcost1⟩ := offline_fin4Block_steady
    obtain ⟨ss, hv_rest, hcost_rest⟩ := offline_fin4Block_iter m
    refine ⟨fin4OffBlockStates ++ ss, ?_, ?_⟩
    · rw [List.replicate_succ, List.flatten_cons]
      apply (problem (Fin 4) 2).validSchedule_append hv1
      rwa [hfin1]
    · rw [List.replicate_succ, List.flatten_cons,
        (problem (Fin 4) 2).scheduleCost_append hv1.length_eq, hfin1, hcost1, hcost_rest]
      omega

/-- **FKLMSY Section 3 (`k = 2, n = 4` separation)** [FiatKarpLubyMcGeochSleatorYoung1991]: on
`Fin 4`, `markingStrategy 2` from `{0, 1}` is not `(c, b)`-competitive for any `c < 2` and
`b ≠ ⊤`. -/
theorem markingStrategy_not_isCompetitive_lt_two_fin_four {c b : ℝ≥0∞}
    (hc : c < 2) (hb : b ≠ ⊤) :
    ¬ (markingStrategy (α := Fin 4) 2 (by omega)).IsCompetitiveFrom ({0, 1} : Finset (Fin 4))
        c b := by
  have hc_ne_top : c ≠ ⊤ := ne_top_of_lt hc
  have hc_real : c.toReal < 2 := by
    have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
    rw [h2] at hc
    exact (ENNReal.lt_ofReal_iff_toReal_lt hc_ne_top).mp hc
  set gap : ℝ := 8 - 4 * c.toReal
  have hgap_pos : 0 < gap := by simp only [gap]; linarith
  obtain ⟨m, hm⟩ := exists_nat_gt ((5 * c.toReal + b.toReal) / gap)
  have hm_ineq : 5 * c.toReal + b.toReal < ((m + 1 : ℕ) : ℝ) * gap := by
    have h := (div_lt_iff₀ hgap_pos).mp hm
    push_cast
    linarith
  obtain ⟨hv0, hfin0, hcost0⟩ := offline_fin4Block_first
  obtain ⟨ss_rest, hv_rest, hcost_rest⟩ := offline_fin4Block_iter m
  set reqs := (List.replicate (m + 1) fin4Block).flatten
  set offStates := fin4OffBlockStates ++ ss_rest
  have hv : (problem (Fin 4) 2).ValidSchedule ({0, 1} : Finset (Fin 4)) reqs offStates := by
    simp only [reqs, List.replicate_succ, List.flatten_cons, offStates]
    apply (problem (Fin 4) 2).validSchedule_append hv0
    rwa [hfin0]
  have hoff_cost :
      (problem (Fin 4) 2).scheduleCost ({0, 1} : Finset (Fin 4)) reqs offStates = 4 * m + 5 := by
    simp only [reqs, List.replicate_succ, List.flatten_cons, offStates]
    rw [(problem (Fin 4) 2).scheduleCost_append hv0.length_eq, hfin0, hcost0, hcost_rest]
    omega
  have hs₀ : ValidCache 2 ({0, 1} : Finset (Fin 4)) := by unfold ValidCache; decide
  have hmark :
      (markingStrategy (α := Fin 4) 2 (by omega)).expectedCost ({0, 1} : Finset (Fin 4)) reqs =
        ENNReal.ofReal (8 * ((m + 1 : ℕ) : ℝ)) := by
    rw [expectedCost_markingStrategy_eq (by omega) hs₀, initTracker,
      marking_fin4Block_iter ∅ (m + 1)]
    push_cast
    rfl
  intro hcomp
  have hbound := hcomp reqs offStates hv
  rw [hmark, hoff_cost] at hbound
  have hrhs_ne_top : c * ((4 * m + 5 : ℕ) : ℝ≥0∞) + b ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hc_ne_top (ENNReal.natCast_ne_top _), hb⟩
  have hreal := ENNReal.toReal_mono hrhs_ne_top hbound
  rw [ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_add (ENNReal.mul_ne_top hc_ne_top (ENNReal.natCast_ne_top _)) hb,
    ENNReal.toReal_mul, ENNReal.toReal_natCast] at hreal
  push_cast at hreal hm_ineq
  simp only [gap] at hm_ineq
  have hc_nonneg : 0 ≤ c.toReal := ENNReal.toReal_nonneg
  have hexpand : ((m : ℝ) + 1) * (8 - 4 * c.toReal) =
      8 * ((m : ℝ) + 1) - c.toReal * (4 * (m : ℝ) + 4) := by ring
  linarith

/-- **FKLMSY Section 3 (`markingStrategy` is not `H_2`-competitive on four pages)**
[FiatKarpLubyMcGeochSleatorYoung1991]: on `Fin 4` at `k = 2`, `markingStrategy` is not
`(H_2, b)`-competitive (`H_2 = 3 / 2`) for any finite additive constant `b ≠ ⊤`. -/
theorem markingStrategy_not_isCompetitive_harmonic_two_fin_four {b : ℝ≥0∞} (hb : b ≠ ⊤) :
    ¬ (markingStrategy (α := Fin 4) 2 (by omega)).IsCompetitive
        (ENNReal.ofReal (harmonic 2)) b := by
  have hlt : ENNReal.ofReal (harmonic 2) < 2 := by
    have hH2 : (harmonic 2 : ℝ) = 3 / 2 := by
      simp only [harmonic_succ, harmonic_zero]
      norm_num
    have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
    rw [hH2, h2]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
  have hs₀ : ValidCache 2 ({0, 1} : Finset (Fin 4)) := by unfold ValidCache; decide
  intro h
  exact markingStrategy_not_isCompetitive_lt_two_fin_four hlt hb (h ({0, 1} : Finset (Fin 4)) hs₀)

end FinFourSeparation

end Cslib.DataStructure.Paging
