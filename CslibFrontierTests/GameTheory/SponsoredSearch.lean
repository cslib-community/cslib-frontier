/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.GameTheory.Mechanism.SponsoredSearch.GSP
import CslibFrontier.GameTheory.Mechanism.SponsoredSearch.VCG
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests and boundary witnesses for sponsored search auctions

Concrete `module`-client checks exercising `Cslib.GameTheory.SponsoredSearch`:

1. Optimal, locally envy-free assignment on 3 bidders and 2 slots (`μ = ![1, 1/2]`,
   `v = ![10, 8, 1]`), explicit `minEnvyFreePrice = ![9/2, 1/2]`, comparison with a larger
   locally envy-free vector `![5, 1/2]`, and the p. 704 generalized Vickrey payment check showing
   bidder 0's per-click payment `9/2` differs from `(1 - μ₁/μ₀) v₁ = 4` when `v₂ = 1 > 0` (and
   agrees when `v₂ = 0`).
2. Misordered assignment (`0 ↦ 1, 1 ↦ 0`): neither optimal nor locally envy-free for any prices.
3. Counterexample to the literal matched-pairs-only reading of (28.9)–(28.10) when
   `unassigned_noEnvy` is omitted (`μ = ![2, 1]`, `v = ![2, 1, 10]`).
4. Counterexample when `StrictAnti μ` is weakened to `Antitone μ` (`μ = ![2, 2, 1]`,
   `v = ![1, 3, 2]`): locally envy-free yet not optimal.
5. Counterexample when `∀ i, 0 < μ i` is dropped (`μ = ![1, 0]`, `v = ![1, 0, 2]`): strictly
   decreasing CTRs, locally envy-free yet not optimal.
6. Non-truthfulness of GSP on the p. 704 example (`μ = ![1, 1/2]`, `v = ![10, 8, 1]`): deviating
   to `z = 2` uniquely swaps the allocation and raises bidder 0's utility from `2` to `9/2`.
7. Exercise 28.1 (p. 715): concrete tie-robust, no-overbidding GSP equilibrium
   (`μ = ![1, 1/2]`, `v = ![10, 9]`, `b = ![1, 8]`) that is *not* optimal and *not* locally
   envy-free for any prices.
8. Explicit Theorem 28.2 equilibria (`n > k`, `n = k`, and all-tied bids `v = ![5, 5, 5]`),
   boundaries (`k = 0`, `k = 1`, negative values `n = k = 1`), and VCG Clarke-pivot payment
   identification.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.SponsoredSearch

open Cslib.GameTheory.SponsoredSearch

private noncomputable def μ2 : Fin 2 → ℝ := ![1, 1 / 2]

private theorem μ2_strictAnti : StrictAnti μ2 := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | exact absurd hab (by decide) | norm_num [μ2]

private theorem μ2_pos : ∀ i : Fin 2, 0 < μ2 i := by
  intro i; fin_cases i <;> norm_num [μ2]

/-- Canonical embedding `0 ↦ 0, 1 ↦ 1` from `Fin 2` into `Fin 3`. -/
private def emb01 : Fin 2 ↪ Fin 3 where
  toFun i := ⟨i.val, by omega⟩
  inj' a b h := Fin.ext (congrArg (Fin.val : Fin 3 → ℕ) h)

@[simp] private theorem emb01_zero : emb01 0 = 0 := rfl
@[simp] private theorem emb01_one : emb01 1 = 1 := rfl

/-- Swapped embedding `0 ↦ 1, 1 ↦ 0` from `Fin 2` into `Fin 3`. -/
private def emb10 : Fin 2 ↪ Fin 3 where
  toFun := ![1, 0]
  inj' a b h := by fin_cases a <;> fin_cases b <;> simp_all

@[simp] private theorem emb10_zero : emb10 0 = 1 := rfl
@[simp] private theorem emb10_one : emb10 1 = 0 := rfl

/-- Embedding `0 ↦ 2, 1 ↦ 0` from `Fin 2` into `Fin 3`. -/
private def emb20 : Fin 2 ↪ Fin 3 where
  toFun := ![2, 0]
  inj' a b h := by fin_cases a <;> fin_cases b <;> simp_all

@[simp] private theorem emb20_zero : emb20 0 = 2 := rfl
@[simp] private theorem emb20_one : emb20 1 = 0 := rfl

private theorem emb01_not_mem_two : (2 : Fin 3) ∉ Set.range emb01 := by
  rintro ⟨i, hi⟩
  fin_cases i <;> exact absurd hi (by decide)

private theorem emb10_not_mem_two : (2 : Fin 3) ∉ Set.range emb10 := by
  rintro ⟨i, hi⟩
  fin_cases i <;> exact absurd hi (by decide)

private theorem maxUnassigned_emb01 (f : Fin 3 → ℝ) :
    maxUnassignedValue f emb01 = f 2 := by
  refine le_antisymm (maxUnassignedValue_le (fun _ j hj => ?_) (fun h => ?_))
    (le_maxUnassignedValue f emb01 emb01_not_mem_two)
  · fin_cases j
    · exact absurd ⟨0, rfl⟩ hj
    · exact absurd ⟨1, rfl⟩ hj
    · exact le_rfl
  · exfalso; apply h
    refine ⟨2, Finset.mem_sdiff.mpr ⟨Finset.mem_univ 2, ?_⟩⟩
    simp only [Finset.mem_map, Finset.mem_univ, true_and, not_exists]
    exact fun r hr => emb01_not_mem_two ⟨r, hr⟩

private theorem maxUnassigned_emb10 (f : Fin 3 → ℝ) :
    maxUnassignedValue f emb10 = f 2 := by
  refine le_antisymm (maxUnassignedValue_le (fun _ j hj => ?_) (fun h => ?_))
    (le_maxUnassignedValue f emb10 emb10_not_mem_two)
  · fin_cases j
    · exact absurd ⟨1, rfl⟩ hj
    · exact absurd ⟨0, rfl⟩ hj
    · exact le_rfl
  · exfalso; apply h
    refine ⟨2, Finset.mem_sdiff.mpr ⟨Finset.mem_univ 2, ?_⟩⟩
    simp only [Finset.mem_map, Finset.mem_univ, true_and, not_exists]
    exact fun r hr => emb10_not_mem_two ⟨r, hr⟩

private theorem maxUnassigned_fin2 (f : Fin 2 → ℝ) (τ : Fin 2 ↪ Fin 2) :
    maxUnassignedValue f τ = 0 := by
  have hnot : ¬(Finset.univ \ Finset.univ.map τ).Nonempty := by
    have hcard : (Finset.univ.map τ).card = Fintype.card (Fin 2) := by simp
    have heq := Finset.eq_univ_of_card (Finset.univ.map τ) hcard
    rw [heq, Finset.sdiff_self]
    exact Finset.not_nonempty_empty
  unfold maxUnassignedValue
  simp only [hnot, ↓reduceDIte]

/-! ### 1. Optimal, locally envy-free 3-bidder 2-slot example and p. 704 check -/

private noncomputable def v3 : Fin 3 → ℝ := ![10, 8, 1]

private theorem v3_nonneg : ∀ j : Fin 3, 0 ≤ v3 j := by
  intro j; fin_cases j <;> norm_num [v3]

private theorem emb01_assortative : IsAssortative v3 emb01 := by
  refine ⟨fun a b hab => ?_, fun i j hj => ?_⟩
  · fin_cases a <;> fin_cases b <;> first
      | exact absurd hab (by decide)
      | norm_num [v3]
  · fin_cases j
    · exact absurd ⟨0, rfl⟩ hj
    · exact absurd ⟨1, rfl⟩ hj
    · fin_cases i <;> norm_num [v3]

private theorem minPrice_v3_one : minEnvyFreePrice μ2 v3 emb01 1 = 1 / 2 := by
  have hlast := minEnvyFreePrice_last μ2 v3 emb01 (by omega)
  rw [maxUnassigned_emb01] at hlast
  change minEnvyFreePrice μ2 v3 emb01 1 = μ2 1 * v3 2 at hlast
  rw [hlast]; norm_num [μ2, v3]

private theorem minPrice_v3_zero : minEnvyFreePrice μ2 v3 emb01 0 = 9 / 2 := by
  have hsub := minEnvyFreePrice_sub_succ μ2 v3 emb01 0 (by omega)
  change minEnvyFreePrice μ2 v3 emb01 0 - minEnvyFreePrice μ2 v3 emb01 1 =
    (μ2 0 - μ2 1) * v3 (emb01 1) at hsub
  have hrhs : (μ2 0 - μ2 1) * v3 (emb01 1) = 4 := by norm_num [μ2, v3]
  rw [minPrice_v3_one, hrhs] at hsub
  linarith

private theorem minPrice_v3 : minEnvyFreePrice μ2 v3 emb01 = ![9 / 2, 1 / 2] := by
  funext i; match i with
  | 0 => exact minPrice_v3_zero
  | 1 => exact minPrice_v3_one

/-- Concrete optimality witness on 3 bidders, 2 slots. -/
example : IsOptimal μ2 v3 emb01 :=
  emb01_assortative.isOptimal μ2_strictAnti.antitone fun i => (μ2_pos i).le

/-- Exact locally envy-free witness `![9/2, 1/2]` on the 3-bidder, 2-slot example. -/
example : IsLocallyEnvyFree μ2 v3 emb01 ![9 / 2, 1 / 2] := by
  rw [← minPrice_v3]
  exact isLocallyEnvyFree_minEnvyFreePrice emb01_assortative μ2_strictAnti.antitone
    (fun i => (μ2_pos i).le) v3_nonneg

/-- Higher slot prices `![5, 1/2]` are also locally envy-free and sit pointwise above
`minEnvyFreePrice = ![9/2, 1/2]`. -/
example : IsLocallyEnvyFree μ2 v3 emb01 ![5, 1 / 2] ∧
    ∀ i : Fin 2, minEnvyFreePrice μ2 v3 emb01 i ≤ (![5, 1 / 2] : Fin 2 → ℝ) i := by
  have hlef : IsLocallyEnvyFree μ2 v3 emb01 ![5, 1 / 2] :=
    { noEnvyAbove := fun i hi => by
        obtain rfl : i = 0 := by omega
        change μ2 0 * v3 (emb01 1) - (![5, 1 / 2] : Fin 2 → ℝ) 0 ≤
          μ2 1 * v3 (emb01 1) - (![5, 1 / 2] : Fin 2 → ℝ) 1
        norm_num [μ2, v3]
      noEnvyBelow := fun i hi => by
        obtain rfl : i = 0 := by omega
        change μ2 1 * v3 (emb01 0) - (![5, 1 / 2] : Fin 2 → ℝ) 1 ≤
          μ2 0 * v3 (emb01 0) - (![5, 1 / 2] : Fin 2 → ℝ) 0
        norm_num [μ2, v3]
      lastSlot_nonneg := fun _ => by
        change 0 ≤ μ2 1 * v3 (emb01 1) - (![5, 1 / 2] : Fin 2 → ℝ) 1
        norm_num [μ2, v3]
      unassigned_noEnvy := fun _ j hj => by
        fin_cases j
        · exact absurd ⟨0, rfl⟩ hj
        · exact absurd ⟨1, rfl⟩ hj
        · change μ2 1 * v3 2 - (![5, 1 / 2] : Fin 2 → ℝ) 1 ≤ 0
          norm_num [μ2, v3] }
  exact ⟨hlef, fun i => minEnvyFreePrice_le hlef (fun r => by fin_cases r <;> norm_num) i⟩

/-- NRTV p. 704 prints the generalized Vickrey per-click price for bidder 1 as `(1 - μ₂/μ₁) v₂`,
which omits `+ (μ₂/μ₁) v₃` when `v₃ > 0`. Here the true charge is `9/2 ≠ 4`. -/
example : minEnvyFreePrice μ2 v3 emb01 0 / μ2 0 = 9 / 2 ∧
    (1 - μ2 1 / μ2 0) * v3 1 = 4 ∧
    (1 - μ2 1 / μ2 0) * v3 1 + (μ2 1 / μ2 0) * v3 2 = minEnvyFreePrice μ2 v3 emb01 0 / μ2 0 := by
  rw [minPrice_v3]
  norm_num [μ2, v3]

/-- When `v₃ = 0`, the book's p. 704 formula matches `minEnvyFreePrice 0 / μ 0`. -/
example : minEnvyFreePrice μ2 ![10, 8, 0] emb01 0 / μ2 0 =
    (1 - μ2 1 / μ2 0) * (![10, 8, 0] : Fin 3 → ℝ) 1 := by
  have h1 := minEnvyFreePrice_last μ2 ![10, 8, 0] emb01 (by omega)
  rw [maxUnassigned_emb01] at h1
  change minEnvyFreePrice μ2 ![10, 8, 0] emb01 1 = μ2 1 * 0 at h1
  have h1z : minEnvyFreePrice μ2 ![10, 8, 0] emb01 1 = 0 := by rw [h1, mul_zero]
  have h0 := minEnvyFreePrice_sub_succ μ2 ![10, 8, 0] emb01 0 (by omega)
  change minEnvyFreePrice μ2 ![10, 8, 0] emb01 0 -
    minEnvyFreePrice μ2 ![10, 8, 0] emb01 1 = (μ2 0 - μ2 1) * 8 at h0
  have hrhs : (μ2 0 - μ2 1) * 8 = 4 := by norm_num [μ2]
  rw [h1z, hrhs, sub_zero] at h0
  rw [h0]; norm_num [μ2]

/-! ### 2. Misordered assignment is neither optimal nor locally envy-free -/

example : ¬IsOptimal μ2 v3 emb10 ∧ ¬∃ p : Fin 2 → ℝ, IsLocallyEnvyFree μ2 v3 emb10 p := by
  have hnot : ¬IsOptimal μ2 v3 emb10 := by
    intro hopt
    have h := hopt emb01
    have h1 : welfare μ2 v3 emb01 = 14 := by
      simp only [welfare, Fin.sum_univ_two, emb01_zero, emb01_one]
      norm_num [μ2, v3]
    have h2 : welfare μ2 v3 emb10 = 13 := by
      simp only [welfare, Fin.sum_univ_two, emb10_zero, emb10_one]
      norm_num [μ2, v3]
    linarith
  exact ⟨hnot, fun h => hnot ((isOptimal_iff_exists_isLocallyEnvyFree μ2_strictAnti μ2_pos).mpr h)⟩

/-! ### 3. Counterexample to literal matched-pairs-only reading (no `unassigned_noEnvy`) -/

/-- With `μ = ![2, 1]`, `v = ![2, 1, 10]`, assignment `emb01` (leaving bidder 2 unassigned), and
prices `p = ![1, 0]`, every matched-pair inequality `(28.9)`–`(28.10)` and last-slot individual
rationality hold, yet `emb01` is NOT optimal (`welfare = 5 < 22`). -/
example :
    let μ : Fin 2 → ℝ := ![2, 1]
    let v : Fin 3 → ℝ := ![2, 1, 10]
    let p : Fin 2 → ℝ := ![1, 0]
    (μ 0 * v (emb01 1) - p 0 ≤ μ 1 * v (emb01 1) - p 1) ∧
    (μ 1 * v (emb01 0) - p 1 ≤ μ 0 * v (emb01 0) - p 0) ∧
    (0 ≤ μ 1 * v (emb01 1) - p 1) ∧
    ¬IsOptimal μ v emb01 ∧
    ¬(μ 1 * v 2 - p 1 ≤ 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [emb01_one]
  · norm_num [emb01_zero]
  · norm_num [emb01_one]
  · intro hopt
    have h := hopt emb20
    have h1 : welfare ![2, 1] ![2, 1, 10] emb20 = 22 := by
      simp only [welfare, Fin.sum_univ_two, emb20_zero, emb20_one]; norm_num
    have h2 : welfare ![2, 1] ![2, 1, 10] emb01 = 5 := by
      simp only [welfare, Fin.sum_univ_two, emb01_zero, emb01_one]; norm_num
    linarith
  · norm_num

/-! ### 4. Counterexample when `StrictAnti μ` is weakened to `Antitone μ` -/

/-- Under weakly decreasing positive CTRs `μ = ![2, 2, 1]`, `v = ![1, 3, 2]`, `σ = id`, and
`p = ![2, 2, 0]`, the assignment is locally envy-free yet strictly suboptimal (`10 < 11`). -/
example :
    let μ : Fin 3 → ℝ := ![2, 2, 1]
    let v : Fin 3 → ℝ := ![1, 3, 2]
    let p : Fin 3 → ℝ := ![2, 2, 0]
    Antitone μ ∧ (∀ i, 0 < μ i) ∧
    IsLocallyEnvyFree μ v (Function.Embedding.refl (Fin 3)) p ∧
    ¬IsOptimal μ v (Function.Embedding.refl (Fin 3)) := by
  let μ : Fin 3 → ℝ := ![2, 2, 1]
  let v : Fin 3 → ℝ := ![1, 3, 2]
  let p : Fin 3 → ℝ := ![2, 2, 0]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first
      | exact absurd hab (by decide)
      | norm_num [μ]
  · intro i; fin_cases i <;> norm_num [μ]
  · refine ⟨fun i hi => ?_, fun i hi => ?_, fun _ => ?_, fun _ j hj => absurd ⟨j, rfl⟩ hj⟩
    · rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · change μ 0 * v 1 - p 0 ≤ μ 1 * v 1 - p 1; norm_num [μ, v, p]
      · change μ 1 * v 2 - p 1 ≤ μ 2 * v 2 - p 2; norm_num [μ, v, p]
    · rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · change μ 1 * v 0 - p 1 ≤ μ 0 * v 0 - p 0; norm_num [μ, v, p]
      · change μ 2 * v 1 - p 2 ≤ μ 1 * v 1 - p 1; norm_num [μ, v, p]
    · change 0 ≤ μ 2 * v 2 - p 2; norm_num [μ, v, p]
  · intro hopt
    have h := hopt (Equiv.swap (0 : Fin 3) 2).toEmbedding
    have h1 : welfare μ v (Function.Embedding.refl (Fin 3)) = 10 := by
      simp only [welfare, Fin.sum_univ_three]; norm_num [μ, v]
    have h2 : welfare μ v (Equiv.swap (0 : Fin 3) 2).toEmbedding = 11 := by
      simp only [welfare, Fin.sum_univ_three, Equiv.coe_toEmbedding]
      norm_num [μ, v, Equiv.swap_apply_def]
    linarith

/-! ### 5. Counterexample when `∀ i, 0 < μ i` is dropped (`μ 1 = 0`) -/

/-- Under strictly decreasing CTRs `μ = ![1, 0]` (last CTR zero), `v = ![1, 0, 2]`, `emb01` is
locally envy-free with `p = ![0, 0]`, yet strictly suboptimal (`1 < 2`). -/
example :
    let μ : Fin 2 → ℝ := ![1, 0]
    let v : Fin 3 → ℝ := ![1, 0, 2]
    StrictAnti μ ∧ IsLocallyEnvyFree μ v emb01 ![0, 0] ∧ ¬IsOptimal μ v emb01 := by
  let μ : Fin 2 → ℝ := ![1, 0]
  let v : Fin 3 → ℝ := ![1, 0, 2]
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first
      | exact absurd hab (by decide)
      | norm_num [μ]
  · refine ⟨fun i hi => ?_, fun i hi => ?_, fun _ => ?_, fun _ j _ => ?_⟩
    · obtain rfl : i = 0 := by omega
      change μ 0 * v (emb01 1) - 0 ≤ μ 1 * v (emb01 1) - 0; norm_num [μ, v]
    · obtain rfl : i = 0 := by omega
      change μ 1 * v (emb01 0) - 0 ≤ μ 0 * v (emb01 0) - 0; norm_num [μ, v]
    · change 0 ≤ μ 1 * v (emb01 1) - 0; norm_num [μ, v]
    · change μ 1 * v j - 0 ≤ 0; fin_cases j <;> norm_num [μ, v]
  · intro hopt
    have h := hopt emb20
    have h1 : welfare μ v emb01 = 1 := by
      simp only [welfare, Fin.sum_univ_two, emb01_zero, emb01_one]; norm_num [μ, v]
    have h2 : welfare μ v emb20 = 2 := by
      simp only [welfare, Fin.sum_univ_two, emb20_zero, emb20_one]; norm_num [μ, v]
    linarith

/-! ### 6. Truthful bidding is NOT a GSP equilibrium (p. 704 example) -/

/-- Under `μ = ![1, 1/2]` and `v = ![10, 8, 1]`, truthful bidding gives bidder `0` utility `2` in
slot `0`. Deviating to `z = 2` yields the unique GSP outcome `emb10` (`0 ↦ 1, 1 ↦ 0`), where
bidder `0` gets slot `1` and utility `9/2 > 2`. -/
example : IsAssortative v3 emb01 ∧
    (∀ σ' : Fin 2 ↪ Fin 3, IsAssortative (Function.update v3 0 2) σ' → σ' = emb10) ∧
    ¬IsGSPEquilibrium μ2 v3 v3 emb01 := by
  have hu0 : Function.update v3 0 2 0 = 2 := Function.update_self 0 2 v3
  have hu1 : Function.update v3 0 2 1 = 8 := by
    rw [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0)]; norm_num [v3]
  have hu2 : Function.update v3 0 2 2 = 1 := by
    rw [Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0)]; norm_num [v3]
  have hout : IsAssortative (Function.update v3 0 2) emb10 := by
    refine ⟨fun a b hab => ?_, fun i j hj => ?_⟩
    · match a, b with
      | 0, 0 => exact le_rfl
      | 0, 1 => change Function.update v3 0 2 0 ≤ Function.update v3 0 2 1; rw [hu0, hu1]; norm_num
      | 1, 0 => exact absurd hab (by decide)
      | 1, 1 => exact le_rfl
    · match j with
      | 0 => exact absurd ⟨1, rfl⟩ hj
      | 1 => exact absurd ⟨0, rfl⟩ hj
      | 2 =>
        match i with
        | 0 => change Function.update v3 0 2 2 ≤ Function.update v3 0 2 1; rw [hu2, hu1]; norm_num
        | 1 => change Function.update v3 0 2 2 ≤ Function.update v3 0 2 0; rw [hu2, hu0]; norm_num
  refine ⟨emb01_assortative, fun σ' hσ' => ?_, fun heq => ?_⟩
  · have hσ0 : σ' 0 = 1 := by
      have hcases : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := fun x => by
        match x with | 0 => left; rfl | 1 => right; left; rfl | 2 => right; right; rfl
      by_cases h1mem : (1 : Fin 3) ∈ Set.range σ'
      · obtain ⟨r, hr⟩ := h1mem
        match r with
        | 0 => exact hr
        | 1 =>
          have h0 := hσ'.antitone (show (0 : Fin 2) ≤ 1 by decide)
          change Function.update v3 0 2 (σ' 1) ≤ Function.update v3 0 2 (σ' 0) at h0
          rw [hr, hu1] at h0
          rcases hcases (σ' 0) with h | h | h
          · rw [h, hu0] at h0; norm_num at h0
          · exact h
          · rw [h, hu2] at h0; norm_num at h0
      · have hle := hσ'.unassigned_le 0 1 h1mem
        rw [hu1] at hle
        rcases hcases (σ' 0) with h | h | h
        · rw [h, hu0] at hle; norm_num at hle
        · exact h
        · rw [h, hu2] at hle; norm_num at hle
    have hσ1 : σ' 1 = 0 := by
      have hne1 : σ' 1 ≠ 1 := fun h => absurd (σ'.injective (h.trans hσ0.symm)) (by decide)
      match h : σ' 1 with
      | 0 => rfl
      | 1 => exact (hne1 h).elim
      | 2 =>
        have h0not : (0 : Fin 3) ∉ Set.range σ' := by
          rintro ⟨r, hr⟩
          match r with
          | 0 => exact absurd (hr.symm.trans hσ0) (by decide)
          | 1 => exact absurd (hr.symm.trans h) (by decide)
        have hle := hσ'.unassigned_le 1 0 h0not
        rw [hu0, h, hu2] at hle; norm_num at hle
    ext i; match i with
    | 0 => exact congrArg Fin.val hσ0
    | 1 => exact congrArg Fin.val hσ1
  · have hdev := heq.noDeviation 0 2 (by norm_num) emb10 hout
    have hnew : gspUtility μ2 v3 (Function.update v3 0 2) emb10 0 = 9 / 2 := by
      have h0 := gspUtility_apply_slot μ2 v3 (Function.update v3 0 2) emb10 1
      rw [emb10_one] at h0
      rw [h0]
      simp only [gspPerClickPrice, nextSlotValue,
        show ¬((1 : Fin 2).val + 1 < 2) by decide, ↓reduceDIte,
        maxUnassigned_emb10, hu2]
      norm_num [μ2, v3]
    have hold : gspUtility μ2 v3 v3 emb01 0 = 2 := by
      have h0 : emb01 0 = 0 := rfl
      rw [← h0, gspUtility_apply_slot]
      simp only [gspPerClickPrice, nextSlotValue,
        show (0 : Fin 2).val + 1 < 2 by decide, ↓reduceDIte]
      change μ2 0 * (v3 0 - v3 (emb01 1)) = 2
      norm_num [μ2, v3]
    linarith

/-! ### 7. Exercise 28.1: a non-optimal, no-overbidding GSP equilibrium -/

/-- Exercise 28.1 (p. 715): on two bidders `v = ![10, 9]` and two slots `μ = ![1, 1/2]`, the bid
profile `b = ![1, 8]` (with no overbidding: `b j ≤ v j` for all `j`) and assignment `swap`
(`0 ↦ 1, 1 ↦ 0`) is a tie-robust GSP equilibrium that is *not* optimal (`14 < 29/2`), hence *not*
locally envy-free for any slot prices. -/
example :
    let v : Fin 2 → ℝ := ![10, 9]
    let b : Fin 2 → ℝ := ![1, 8]
    let σ : Fin 2 ↪ Fin 2 := (Equiv.swap (0 : Fin 2) 1).toEmbedding
    (∀ j, b j ≤ v j) ∧
    IsGSPEquilibrium μ2 v b σ ∧
    ¬IsOptimal μ2 v σ ∧
    ¬∃ p : Fin 2 → ℝ, IsLocallyEnvyFree μ2 v σ p := by
  let v : Fin 2 → ℝ := ![10, 9]
  let b : Fin 2 → ℝ := ![1, 8]
  let σ : Fin 2 ↪ Fin 2 := (Equiv.swap (0 : Fin 2) 1).toEmbedding
  have hσ0 : σ 0 = 1 := rfl
  have hσ1 : σ 1 = 0 := rfl
  have heq : IsGSPEquilibrium μ2 v b σ := by
    refine ⟨fun j => by fin_cases j <;> norm_num [b], ?_, fun j z _ σ' _ => ?_⟩
    · refine ⟨fun x y hxy => ?_, fun _ x hx => ?_⟩
      · fin_cases x <;> fin_cases y <;> first
          | exact absurd hxy (by decide)
          | norm_num [σ, b]
      · exfalso; match x with
        | 0 => exact hx ⟨1, hσ1⟩
        | 1 => exact hx ⟨0, hσ0⟩
    · have hold0 : gspUtility μ2 v b σ 0 = 5 := by
        rw [← hσ1, gspUtility_apply_slot]
        simp only [gspPerClickPrice, nextSlotValue,
          show ¬((1 : Fin 2).val + 1 < 2) by decide, ↓reduceDIte,
          maxUnassigned_fin2, hσ1]
        norm_num [μ2, v]
      have hold1 : gspUtility μ2 v b σ 1 = 8 := by
        rw [← hσ0, gspUtility_apply_slot]
        simp only [gspPerClickPrice, nextSlotValue,
          show (0 : Fin 2).val + 1 < 2 by decide, ↓reduceDIte]
        change μ2 0 * (v 1 - b (σ 1)) = 8
        rw [hσ1]; norm_num [μ2, v, b]
      obtain ⟨s, hs⟩ : j ∈ Set.range σ' :=
        (Finite.injective_iff_surjective.mp σ'.injective) j
      match j, s with
      | 0, 0 =>
        have hstep := gspUtility_apply_slot μ2 v (Function.update b 0 z) σ' 0
        rw [hs] at hstep
        rw [hstep, hold0]
        have hs1 : σ' 1 = 1 := by
          have hne : σ' 1 ≠ σ' 0 := σ'.injective.ne (by decide)
          rw [hs] at hne
          match h : σ' 1 with | 0 => exact (hne h).elim | 1 => rfl
        simp only [gspPerClickPrice, nextSlotValue,
          show (0 : Fin 2).val + 1 < 2 by decide, ↓reduceDIte]
        change μ2 0 * (v 0 - Function.update b 0 z (σ' 1)) ≤ 5
        rw [hs1, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
        norm_num [μ2, v, b]
      | 0, 1 =>
        have hstep := gspUtility_apply_slot μ2 v (Function.update b 0 z) σ' 1
        rw [hs] at hstep
        rw [hstep, hold0]
        simp only [gspPerClickPrice, nextSlotValue,
          show ¬((1 : Fin 2).val + 1 < 2) by decide, ↓reduceDIte,
          maxUnassigned_fin2]
        norm_num [μ2, v]
      | 1, 0 =>
        have hstep := gspUtility_apply_slot μ2 v (Function.update b 1 z) σ' 0
        rw [hs] at hstep
        rw [hstep, hold1]
        have hs1 : σ' 1 = 0 := by
          have hne : σ' 1 ≠ σ' 0 := σ'.injective.ne (by decide)
          rw [hs] at hne
          match h : σ' 1 with | 0 => rfl | 1 => exact (hne h).elim
        simp only [gspPerClickPrice, nextSlotValue,
          show (0 : Fin 2).val + 1 < 2 by decide, ↓reduceDIte]
        change μ2 0 * (v 1 - Function.update b 1 z (σ' 1)) ≤ 8
        rw [hs1, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
        norm_num [μ2, v, b]
      | 1, 1 =>
        have hstep := gspUtility_apply_slot μ2 v (Function.update b 1 z) σ' 1
        rw [hs] at hstep
        rw [hstep, hold1]
        simp only [gspPerClickPrice, nextSlotValue,
          show ¬((1 : Fin 2).val + 1 < 2) by decide, ↓reduceDIte,
          maxUnassigned_fin2]
        norm_num [μ2, v]
  have hnotopt : ¬IsOptimal μ2 v σ := by
    intro hopt
    have h := hopt (Function.Embedding.refl (Fin 2))
    have h1 : welfare μ2 v σ = 14 := by
      simp only [welfare, Fin.sum_univ_two, hσ0, hσ1]; norm_num [μ2, v]
    have h2 : welfare μ2 v (Function.Embedding.refl (Fin 2)) = 29 / 2 := by
      simp only [welfare, Fin.sum_univ_two]; norm_num [μ2, v]
    linarith
  refine ⟨fun j => by fin_cases j <;> norm_num [b, v], heq, hnotopt, fun h =>
    hnotopt ((isOptimal_iff_exists_isLocallyEnvyFree μ2_strictAnti μ2_pos).mpr h)⟩

/-! ### 8. Concrete Theorem 28.2 equilibria, boundary cases, and VCG check -/

/-- Exact computation of `minEnvyFreeBid` and tie-robust equilibrium on `v = ![10, 8, 1]`. -/
example :
    minEnvyFreeBid μ2 v3 emb01 = ![10, 9 / 2, 1] ∧
    IsGSPEquilibrium μ2 v3 ![10, 9 / 2, 1] emb01 ∧
    gspSlotPrice μ2 ![10, 9 / 2, 1] emb01 = ![9 / 2, 1 / 2] := by
  have hbid : minEnvyFreeBid μ2 v3 emb01 = ![10, 9 / 2, 1] := by
    funext j; match j with
    | 0 =>
      have h := minEnvyFreeBid_slot_zero μ2 v3 emb01 (by omega)
      change minEnvyFreeBid μ2 v3 emb01 0 = v3 0 at h
      rw [h]; norm_num [v3]
    | 1 =>
      have h := minEnvyFreeBid_slot_succ μ2 v3 emb01 0 (by omega)
      change minEnvyFreeBid μ2 v3 emb01 1 = minEnvyFreePrice μ2 v3 emb01 0 / μ2 0 at h
      rw [h, minPrice_v3_zero]; norm_num [μ2]
    | 2 =>
      rw [minEnvyFreeBid_of_not_mem_range μ2 v3 emb01 emb01_not_mem_two]; norm_num [v3]
  refine ⟨hbid, ?_, ?_⟩
  · rw [← hbid]
    exact isGSPEquilibrium_minEnvyFreeBid emb01_assortative μ2_strictAnti μ2_pos v3_nonneg
  · rw [← hbid, gspSlotPrice_minEnvyFreeBid μ2_pos, minPrice_v3]

/-- Concrete `n = k = 2` equilibrium: `μ = ![1, 1/2]`, `v = ![10, 6]`, bids `![10, 3]`,
prices `![3, 0]`. -/
example :
    let v : Fin 2 → ℝ := ![10, 6]
    let σ : Fin 2 ↪ Fin 2 := Function.Embedding.refl (Fin 2)
    minEnvyFreePrice μ2 v σ = ![3, 0] ∧
    minEnvyFreeBid μ2 v σ = ![10, 3] ∧
    IsGSPEquilibrium μ2 v ![10, 3] σ := by
  let v : Fin 2 → ℝ := ![10, 6]
  let σ : Fin 2 ↪ Fin 2 := Function.Embedding.refl (Fin 2)
  have h1 : minEnvyFreePrice μ2 v σ 1 = 0 := by
    have hlast := minEnvyFreePrice_last μ2 v σ (by omega)
    change minEnvyFreePrice μ2 v σ 1 = μ2 1 * maxUnassignedValue v σ at hlast
    rw [hlast, maxUnassigned_fin2, mul_zero]
  have h0 : minEnvyFreePrice μ2 v σ 0 = 3 := by
    have hsub := minEnvyFreePrice_sub_succ μ2 v σ 0 (by omega)
    change minEnvyFreePrice μ2 v σ 0 - minEnvyFreePrice μ2 v σ 1 =
      (μ2 0 - μ2 1) * v 1 at hsub
    have hrhs : (μ2 0 - μ2 1) * v 1 = 3 := by norm_num [μ2, v]
    rw [h1, hrhs, sub_zero] at hsub
    exact hsub
  have hp : minEnvyFreePrice μ2 v σ = ![3, 0] := by
    funext i; match i with | 0 => exact h0 | 1 => exact h1
  have hb : minEnvyFreeBid μ2 v σ = ![10, 3] := by
    funext i; match i with
    | 0 =>
      have h := minEnvyFreeBid_slot_zero μ2 v σ (by omega)
      change minEnvyFreeBid μ2 v σ 0 = v 0 at h
      rw [h]; norm_num [v]
    | 1 =>
      have h := minEnvyFreeBid_slot_succ μ2 v σ 0 (by omega)
      change minEnvyFreeBid μ2 v σ 1 = minEnvyFreePrice μ2 v σ 0 / μ2 0 at h
      rw [h, h0]; norm_num [μ2]
  have hσ : IsAssortative v σ :=
    ⟨fun a b hab => by
      match a, b with
      | 0, 0 => exact le_rfl
      | 0, 1 => change v 1 ≤ v 0; norm_num [v]
      | 1, 0 => exact absurd hab (by decide)
      | 1, 1 => exact le_rfl,
      fun _ j hj => absurd ⟨j, rfl⟩ hj⟩
  refine ⟨hp, hb, ?_⟩
  rw [← hb]
  exact isGSPEquilibrium_minEnvyFreeBid hσ μ2_strictAnti μ2_pos
    (fun j => by fin_cases j <;> norm_num [v])

/-- Full-tie case (`n > k`): all 3 bidders value a click at `5`, all 3 bids tie at `5`, yet
`minEnvyFreeBid` is a tie-robust GSP equilibrium regardless of tie-breaking. -/
example :
    let μ : Fin 2 → ℝ := ![2, 1]
    let v : Fin 3 → ℝ := fun _ => 5
    minEnvyFreePrice μ v emb01 = ![10, 5] ∧
    minEnvyFreeBid μ v emb01 = (fun _ => 5) ∧
    IsGSPEquilibrium μ v (fun _ => 5) emb01 := by
  let μ : Fin 2 → ℝ := ![2, 1]
  let v : Fin 3 → ℝ := fun _ => 5
  have hμ : StrictAnti μ := fun a b hab => by
    fin_cases a <;> fin_cases b <;> first | exact absurd hab (by decide) | norm_num [μ]
  have hμ_pos : ∀ i, 0 < μ i := fun i => by fin_cases i <;> norm_num [μ]
  have h1 : minEnvyFreePrice μ v emb01 1 = 5 := by
    have hlast := minEnvyFreePrice_last μ v emb01 (by omega)
    change minEnvyFreePrice μ v emb01 1 = μ 1 * maxUnassignedValue v emb01 at hlast
    rw [hlast, maxUnassigned_emb01]; norm_num [μ, v]
  have h0 : minEnvyFreePrice μ v emb01 0 = 10 := by
    have hsub := minEnvyFreePrice_sub_succ μ v emb01 0 (by omega)
    change minEnvyFreePrice μ v emb01 0 - minEnvyFreePrice μ v emb01 1 =
      (μ 0 - μ 1) * v 1 at hsub
    have hrhs : (μ 0 - μ 1) * v 1 = 5 := by norm_num [μ, v]
    rw [h1, hrhs] at hsub
    linarith
  have hp : minEnvyFreePrice μ v emb01 = ![10, 5] := by
    funext i; match i with | 0 => exact h0 | 1 => exact h1
  have hb : minEnvyFreeBid μ v emb01 = fun _ => 5 := by
    funext j; match j with
    | 0 => exact minEnvyFreeBid_slot_zero μ v emb01 (by omega)
    | 1 =>
      have h := minEnvyFreeBid_slot_succ μ v emb01 0 (by omega)
      change minEnvyFreeBid μ v emb01 1 = minEnvyFreePrice μ v emb01 0 / μ 0 at h
      rw [h, h0]; norm_num [μ]
    | 2 => exact minEnvyFreeBid_of_not_mem_range μ v emb01 emb01_not_mem_two
  have hσ : IsAssortative v emb01 := ⟨fun _ _ _ => le_rfl, fun _ _ _ => le_rfl⟩
  have heq : IsGSPEquilibrium μ v (minEnvyFreeBid μ v emb01) emb01 :=
    isGSPEquilibrium_minEnvyFreeBid hσ hμ hμ_pos (fun _ => by norm_num [v])
  refine ⟨hp, hb, ?_⟩
  rw [hb] at heq
  exact heq

/-- Boundary case `k = 0`: `exists_isGSPEquilibrium_locallyEnvyFree` works for `0` slots. -/
example : ∃ (b : Fin 3 → ℝ) (σ : Fin 0 ↪ Fin 3),
    IsGSPEquilibrium Fin.elim0 v3 b σ ∧
    IsOptimal Fin.elim0 v3 σ ∧
    IsLocallyEnvyFree Fin.elim0 v3 σ (gspSlotPrice Fin.elim0 b σ) := by
  obtain ⟨b, σ, h1, h2, h3, -⟩ := exists_isGSPEquilibrium_locallyEnvyFree
    (μ := Fin.elim0) (v := v3) (fun a => a.elim0) (fun i => i.elim0) v3_nonneg (by decide)
  exact ⟨b, σ, h1, h2, h3⟩

/-- Boundary case `k = 1` with 3 bidders (single-slot second-price / Vickrey auction):
`minEnvyFreePrice` charges the second-highest value `8`, and truthful bidding `v3` IS a
tie-robust GSP equilibrium! -/
example :
    let μ : Fin 1 → ℝ := ![1]
    let σ : Fin 1 ↪ Fin 3 :=
      { toFun := fun _ => 0, inj' := fun a b _ => (Fin.eq_zero a).trans (Fin.eq_zero b).symm }
    minEnvyFreePrice μ v3 σ = ![8] ∧
    minEnvyFreeBid μ v3 σ = v3 ∧
    IsGSPEquilibrium μ v3 v3 σ := by
  let μ : Fin 1 → ℝ := ![1]
  let σ : Fin 1 ↪ Fin 3 :=
    { toFun := fun _ => 0, inj' := fun a b _ => (Fin.eq_zero a).trans (Fin.eq_zero b).symm }
  have h1not : (1 : Fin 3) ∉ Set.range σ := by
    rintro ⟨i, hi⟩; exact absurd (show (0 : Fin 3) = 1 from hi) (by decide)
  have h2not : (2 : Fin 3) ∉ Set.range σ := by
    rintro ⟨i, hi⟩; exact absurd (show (0 : Fin 3) = 2 from hi) (by decide)
  have hmax : maxUnassignedValue v3 σ = 8 := by
    refine le_antisymm (maxUnassignedValue_le (fun _ j hj => ?_) (fun h => ?_)) ?_
    · match j with
      | 0 => exact absurd ⟨0, rfl⟩ hj
      | 1 => norm_num [v3]
      | 2 => norm_num [v3]
    · exfalso; apply h
      refine ⟨1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ 1, ?_⟩⟩
      simp only [Finset.mem_map, Finset.mem_univ, true_and, not_exists]
      exact fun r hr => h1not ⟨r, hr⟩
    · have h := le_maxUnassignedValue v3 σ h1not
      have h8 : v3 1 = 8 := by norm_num [v3]
      rwa [h8] at h
  have hprice : minEnvyFreePrice μ v3 σ = ![8] := by
    funext i; rw [Fin.eq_zero i]
    have hlast := minEnvyFreePrice_last μ v3 σ (by omega)
    change minEnvyFreePrice μ v3 σ 0 = μ 0 * maxUnassignedValue v3 σ at hlast
    rw [hlast, hmax]; norm_num [μ]
  have hbid : minEnvyFreeBid μ v3 σ = v3 := by
    funext j; match j with
    | 0 => exact minEnvyFreeBid_slot_zero μ v3 σ (by omega)
    | 1 => exact minEnvyFreeBid_of_not_mem_range μ v3 σ h1not
    | 2 => exact minEnvyFreeBid_of_not_mem_range μ v3 σ h2not
  have hσ : IsAssortative v3 σ :=
    ⟨fun a b _ => by rw [Fin.eq_zero a, Fin.eq_zero b], fun i j hj => by
      have hσi : σ i = 0 := rfl
      rw [hσi]
      match j with
      | 0 => exact absurd ⟨0, rfl⟩ hj
      | 1 => norm_num [v3]
      | 2 => norm_num [v3]⟩
  have heq : IsGSPEquilibrium μ v3 (minEnvyFreeBid μ v3 σ) σ :=
    isGSPEquilibrium_minEnvyFreeBid (μ := μ) hσ
      (fun a b hab => absurd hab (by rw [Fin.eq_zero a, Fin.eq_zero b]; exact lt_irrefl _))
      (fun i => by rw [Fin.eq_zero i]; norm_num [μ]) v3_nonneg
  rw [hbid] at heq
  exact ⟨hprice, hbid, heq⟩

/-- Boundary case `n = k = 1` with *negative* value (`v = ![-3]`): Theorem 28.1 remains valid
with a negative slot price `p = ![-3]`. -/
example :
    let μ : Fin 1 → ℝ := ![1]
    let v : Fin 1 → ℝ := ![-3]
    let σ : Fin 1 ↪ Fin 1 := Function.Embedding.refl (Fin 1)
    IsOptimal μ v σ ∧ IsLocallyEnvyFree μ v σ ![-3] := by
  refine ⟨fun τ => ?_, ?_⟩
  · have hτ : τ = Function.Embedding.refl (Fin 1) := by
      apply Function.Embedding.ext; intro i
      exact (Fin.eq_zero (τ i)).trans (Fin.eq_zero i).symm
    rw [hτ]
  · refine ⟨fun i hi => by omega, fun i hi => by omega, fun _ => by norm_num, fun _ j hj => ?_⟩
    exact absurd ⟨j, rfl⟩ hj

/-- VCG Clarke-pivot payment identification on `μ = ![1, 1/2]`, `v = ![10, 8, 1]`: for any rule
returning `emb01`, bidder `0` pays `9/2`, bidder `1` pays `1/2`, and bidder `2` pays `0`. -/
example [Fintype (Fin 2 ↪ Fin 3)] [Nonempty (Fin 2 ↪ Fin 3)]
    (f : (Fin 3 → (Fin 2 ↪ Fin 3) → ℝ) → Fin 2 ↪ Fin 3)
    (hf : f (Cslib.GameTheory.Mechanism.linearProfile (slotAlloc μ2) v3) = emb01) :
    (Cslib.GameTheory.Mechanism.vcg f).payment
      (Cslib.GameTheory.Mechanism.linearProfile (slotAlloc μ2) v3) 0 = 9 / 2 ∧
    (Cslib.GameTheory.Mechanism.vcg f).payment
      (Cslib.GameTheory.Mechanism.linearProfile (slotAlloc μ2) v3) 1 = 1 / 2 ∧
    (Cslib.GameTheory.Mechanism.vcg f).payment
      (Cslib.GameTheory.Mechanism.linearProfile (slotAlloc μ2) v3) 2 = 0 := by
  have h0 := vcg_payment_slot_eq_minEnvyFreePrice f hf emb01_assortative
    μ2_strictAnti.antitone (fun i => (μ2_pos i).le) v3_nonneg 0
  have h1 := vcg_payment_slot_eq_minEnvyFreePrice f hf emb01_assortative
    μ2_strictAnti.antitone (fun i => (μ2_pos i).le) v3_nonneg 1
  have h2 := vcg_payment_unassigned_eq_zero f hf emb01_assortative
    μ2_strictAnti.antitone (fun i => (μ2_pos i).le) v3_nonneg emb01_not_mem_two
  rw [minPrice_v3_zero] at h0
  rw [minPrice_v3_one] at h1
  exact ⟨h0, h1, h2⟩

end CslibFrontierTests.GameTheory.SponsoredSearch
