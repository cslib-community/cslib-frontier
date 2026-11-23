/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.GameTheory.Congestion.BeckmannPotential
import CslibFrontier.GameTheory.Congestion.MarginalCostPricing
import CslibFrontier.GameTheory.Congestion.CapacityAugmentation
import CslibFrontier.GameTheory.Congestion.WardropNoRegret

/-!
# Nonatomic routing: Beckmann potential, Pigouvian taxes, capacity augmentation, and no-regret flow

Checked concrete instances exercising the nonatomic selfish routing developments:

* **Pigou uniqueness and Beckmann potential vs. social cost**: on `pigouNetwork (fun x => x) 1`,
  `![1, 0]` is the unique Wardrop equilibrium (`PoS = 4/3`) and minimizes Beckmann's potential
  (`Φ(![1, 0]) = 1/2 < Φ(![1/2, 1/2]) = 5/8`), while `![1/2, 1/2]` minimizes total latency
  (`cost ![1/2, 1/2] = 3/4 < cost ![1, 0] = 1`).
* **Pigouvian marginal-cost taxes**: taxing the congestible link by `f*_e c'_e(f*_e) = 1/2` and the
  constant link by `0` makes the socially optimal split `![1/2, 1/2]` the *unique* Wardrop
  equilibrium of the taxed Pigou network (and `[0, 1/2]` when the constant link is indexed `0`).
* **Braess's four-node Wheatstone network and subnetwork bound**: adding the zero-cost cross edge
  raises the unique Wardrop cost from `3/2` (`![1/2, 1/2]`) to `2 = 4/3 * (3/2)` (`![0, 0, 1]`),
  matching the `4/3` upper bound of `HasAffineLatencies.cost_le_four_thirds_restrictPaths` along
  the explicit two-path embedding `Fin 2 ↪ Fin 3`.
* **Capacity augmentation and concave Pigou bound**: `2r` augmentation and `speedup 2` hold on
  polynomial Pigou networks (`x ^ 4`) while failing in unweighted atomic congestion games
  (`972 > 128`); for affine latencies `(5/4) r` suffices (`δ = 1/4`) whereas `δ = 1/8 < 1/4` fails
  on Pigou (`7/8 < 1`); `Real.sqrt` belongs to `concaveLatencies`, so its price of anarchy is at
  most `4/3` (with `pigouRatio Real.sqrt 1 (4/9) = 27/23 ≤ 4/3`).
* **Online no-regret routing**: on `pigouNetwork (fun x => x) 1`, a two-day flow sequence with
  average external regret `1/8` has time average `![3/4, 1/4]`, which is `(1/8)`-Wardrop (actual
  Wardrop gap `1/16 ≤ 1/8`), whereas quadratic `x ^ 2` breaks literal `ε`-preservation
  (`45/64 > 44/64`) and satisfies the Lipschitz `O(ε + √ε)` bound.
-/

namespace CslibFrontierTests.GameTheory.RoutingBeckmann

open Cslib.GameTheory NonatomicCongestionGame MeasureTheory

/-! ### 1. Pigou uniqueness and Beckmann potential -/

/-- Linear Pigou network `c_0(x) = x`, `c_1(x) = 1` with unit traffic rate. -/
abbrev linearPigou : NonatomicCongestionGame Unit (Fin 2) (Fin 2) :=
  pigouNetwork (fun x => x) 1

theorem linearPigou_hasAffineLatencies : linearPigou.HasAffineLatencies :=
  ⟨![1, 0], ![0, 1],
    fun e => by fin_cases e <;> norm_num,
    fun e => by fin_cases e <;> norm_num,
    fun e x => by fin_cases e <;> simp [linearPigou, pigouNetwork]⟩

/-- `![1, 0]` is the unique Wardrop equilibrium of `linearPigou`, so its price of stability is
`4/3`. -/
example (f : Fin 2 → ℝ) : linearPigou.IsWardrop f ↔ f = ![1, 0] :=
  pigouNetwork_id_isWardrop_iff

/-- Beckmann potential on `linearPigou` strictly prefers `![1, 0]` (`1/2`) over the socially
optimal split `![1/2, 1/2]` (`5/8`), whereas total latency does the opposite (`3/4 < 1`). -/
example :
    linearPigou.beckmannPotential ![1, 0] = 1 / 2 ∧
      linearPigou.beckmannPotential ![1 / 2, 1 / 2] = 5 / 8 ∧
      linearPigou.cost ![1 / 2, 1 / 2] = 3 / 4 ∧
      linearPigou.cost ![1, 0] = 1 := by
  have heflow : ∀ (g : Fin 2 → ℝ) (e : Fin 2), linearPigou.edgeFlow g e = g e := fun g e => by
    simp [edgeFlow, linearPigou, pigouNetwork, Finset.filter_eq]
  have hpot : ∀ g : Fin 2 → ℝ,
      linearPigou.beckmannPotential g = (g 0) ^ 2 / 2 + g 1 := by
    intro g
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    rw [beckmannPotential, Fin.sum_univ_two, heflow, heflow]
    simp only [linearPigou, pigouNetwork, h10, ↓reduceIte]
    rw [integral_id, intervalIntegral.integral_const]
    simp [smul_eq_mul]
  refine ⟨by rw [hpot]; norm_num, by rw [hpot]; norm_num,
    by rw [pigouNetwork_cost]; norm_num, by rw [pigouNetwork_cost]; norm_num⟩

/-- Existence of a Wardrop equilibrium on `linearPigou` from `exists_isWardrop`. -/
example : ∃ f, linearPigou.IsWardrop f :=
  linearPigou.exists_isWardrop
    (fun _ => zero_le_one)
    (fun _ _ => ⟨0, rfl⟩)
    (fun e => by
      fin_cases e
      · exact continuousOn_id
      · exact continuousOn_const)

/-! ### 2. Pigouvian marginal-cost taxes on Pigou's network -/

/-- Even split `![1/2, 1/2]` is socially optimal on `linearPigou`. -/
theorem linearPigou_isOptimal_half : linearPigou.IsOptimal ![1 / 2, 1 / 2] := by
  have hfeas : linearPigou.IsFeasible ![1 / 2, 1 / 2] := by
    have h12 : (![1 / 2, (1 : ℝ) - 1 / 2] : Fin 2 → ℝ) = ![1 / 2, 1 / 2] := by
      ext i; fin_cases i <;> norm_num
    rw [← h12]
    exact pigouNetwork_isFeasible (fun x => x) (by norm_num) (by norm_num)
  refine ⟨hfeas, fun g hg => ?_⟩
  rw [pigouNetwork_cost, pigouNetwork_cost]
  have hsum : g 0 + g 1 = 1 := by
    have hs := hg.2 ()
    simpa [linearPigou, pigouNetwork, Fin.sum_univ_two] using hs
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith [sq_nonneg (g 0 - 1 / 2)]

/-- Latency derivatives `c' 0 x = 1`, `c' 1 x = 0` on `linearPigou`. -/
def linearPigouDeriv : Fin 2 → ℝ → ℝ := fun e _ => if e = 0 then 1 else 0

/-- The Pigouvian tax at `![1/2, 1/2]` is `![1/2, 0]` (`1/2` on the linear link `0` and `0` on the
constant link `1`), it makes `![1/2, 1/2]` the **unique** Wardrop equilibrium of the taxed network,
and every Wardrop equilibrium of the taxed network is socially optimal by
`IsOptimal.cost_eq_of_isWardrop_withTaxes` (even though link `1` is constant, not strictly
increasing). -/
example :
    linearPigou.pigouvianTax linearPigouDeriv ![1 / 2, 1 / 2] = ![1 / 2, 0] ∧
      (∀ f, (linearPigou.withTaxes ![1 / 2, 0]).IsWardrop f →
        linearPigou.cost f = linearPigou.cost ![1 / 2, 1 / 2] ∧ linearPigou.IsOptimal f) ∧
      ∀ f, (linearPigou.withTaxes ![1 / 2, 0]).IsWardrop f ↔ f = ![1 / 2, 1 / 2] := by
  have heflow : ∀ (g : Fin 2 → ℝ) (e : Fin 2), linearPigou.edgeFlow g e = g e := fun g e => by
    simp [edgeFlow, linearPigou, pigouNetwork, Finset.filter_eq]
  have htax : linearPigou.pigouvianTax linearPigouDeriv ![1 / 2, 1 / 2] = ![1 / 2, 0] := by
    ext e
    simp only [pigouvianTax, heflow, linearPigouDeriv]
    fin_cases e <;> norm_num
  have hderiv : ∀ e, HasDerivWithinAt (linearPigou.latency e)
      (linearPigouDeriv e (linearPigou.edgeFlow ![1 / 2, 1 / 2] e))
      (Set.Ici 0) (linearPigou.edgeFlow ![1 / 2, 1 / 2] e) := fun e => by
    fin_cases e
    · change HasDerivWithinAt (fun x : ℝ => x) 1 (Set.Ici 0) _
      exact (hasDerivAt_id _).hasDerivWithinAt
    · simpa [linearPigou, pigouNetwork, linearPigouDeriv] using
        hasDerivWithinAt_const (linearPigou.edgeFlow ![1 / 2, 1 / 2] 1) (Set.Ici 0) (1 : ℝ)
  have hmono : ∀ e, MonotoneOn (linearPigou.latency e) (Set.Ici 0) := fun e x _ y _ hxy => by
    fin_cases e
    · exact hxy
    · exact le_rfl
  refine ⟨htax, fun f hf => ?_, fun f => ⟨fun hf => ?_, fun hf => ?_⟩⟩
  · exact linearPigou_isOptimal_half.cost_eq_of_isWardrop_withTaxes hmono hderiv (htax ▸ hf)
  · have hfeas : linearPigou.IsFeasible f := hf.1
    have hsum : f 0 + f 1 = 1 := by
      have hs := hfeas.2 ()
      simpa [linearPigou, pigouNetwork, Fin.sum_univ_two] using hs
    have hp0 : (linearPigou.withTaxes ![1 / 2, 0]).pathLatency f 0 = f 0 + 1 / 2 := by
      rw [pathLatency]
      change ∑ e ∈ ({0} : Finset (Fin 2)),
          (linearPigou.withTaxes ![1 / 2, 0]).latency e
            ((linearPigou.withTaxes ![1 / 2, 0]).edgeFlow f e) = f 0 + 1 / 2
      rw [Finset.sum_singleton, withTaxes_latency, withTaxes_edgeFlow, heflow]
      rfl
    have hp1 : (linearPigou.withTaxes ![1 / 2, 0]).pathLatency f 1 = 1 := by
      have h10 : (1 : Fin 2) ≠ 0 := by decide
      rw [pathLatency]
      change ∑ e ∈ ({1} : Finset (Fin 2)),
          (linearPigou.withTaxes ![1 / 2, 0]).latency e
            ((linearPigou.withTaxes ![1 / 2, 0]).edgeFlow f e) = 1
      rw [Finset.sum_singleton, withTaxes_latency]
      simp [linearPigou, pigouNetwork, h10]
    have hf0_le : f 0 ≤ 1 / 2 := by
      by_contra hgt
      push Not at hgt
      have hle := hf.2 0 1 rfl (by linarith)
      rw [hp0, hp1] at hle
      linarith
    have hf1_le : f 1 ≤ 1 / 2 := by
      by_contra hgt
      push Not at hgt
      have hle := hf.2 1 0 rfl (by linarith)
      rw [hp1, hp0] at hle
      linarith
    ext i
    fin_cases i
    · change f 0 = 1 / 2; linarith
    · change f 1 = 1 / 2; linarith
  · rw [hf, ← htax]
    exact linearPigou_isOptimal_half.isWardrop_withTaxes_pigouvianTax hderiv

/-- With link `0` constant (`c_0(x) = 1`) and link `1` linear (`c_1(x) = x`), the Pigouvian tax
vector at `![1/2, 1/2]` is `![0, 1/2]` and induces `![1/2, 1/2]` as a Wardrop equilibrium. -/
example :
    let G : NonatomicCongestionGame Unit (Fin 2) (Fin 2) :=
      { commodity := fun _ => ()
        resources := fun p => {p}
        rate := fun _ => 1
        latency := fun e x => if e = 0 then 1 else x }
    let c' : Fin 2 → ℝ → ℝ := fun e _ => if e = 0 then 0 else 1
    G.pigouvianTax c' ![1 / 2, 1 / 2] = ![0, 1 / 2] ∧
      (G.withTaxes ![0, 1 / 2]).IsWardrop ![1 / 2, 1 / 2] := by
  intro G c'
  have heflow : ∀ (g : Fin 2 → ℝ) (e : Fin 2), G.edgeFlow g e = g e := fun g e => by
    simp [edgeFlow, G, Finset.filter_eq]
  have htax : G.pigouvianTax c' ![1 / 2, 1 / 2] = ![0, 1 / 2] := by
    ext e
    simp only [pigouvianTax, heflow, c']
    fin_cases e <;> norm_num
  have hopt : G.IsOptimal ![1 / 2, 1 / 2] := by
    refine ⟨⟨fun p => by fin_cases p <;> norm_num, fun _ => ?_⟩, fun g hg => ?_⟩
    · simp [G, Fin.sum_univ_two]; norm_num
    · have h10 : (1 : Fin 2) ≠ 0 := by decide
      rw [G.cost_eq_sum_edgeFlow, G.cost_eq_sum_edgeFlow, Fin.sum_univ_two, Fin.sum_univ_two]
      simp only [heflow, G, h10, ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one]
      have hsum : g 0 + g 1 = 1 := by
        have hs := hg.2 ()
        simpa [G, Fin.sum_univ_two] using hs
      nlinarith [sq_nonneg (g 1 - 1 / 2)]
  refine ⟨htax, ?_⟩
  rw [← htax]
  exact hopt.isWardrop_withTaxes_pigouvianTax fun e => by
    fin_cases e
    · simpa [G, c'] using
        hasDerivWithinAt_const (G.edgeFlow ![1 / 2, 1 / 2] 0) (Set.Ici 0) (1 : ℝ)
    · change HasDerivWithinAt (fun x : ℝ => x) 1 (Set.Ici 0) _
      exact (hasDerivAt_id _).hasDerivWithinAt

/-! ### 3. Braess's four-node Wheatstone calculation and subnetwork restriction -/

/-- Embedding the two outer paths `0, 1` into the three-path augmented Wheatstone network. -/
def braessEmbed : Fin 2 ↪ Fin 3 where
  toFun i := ⟨i.1, by omega⟩
  inj' a b h := Fin.ext (by simpa using congrArg Fin.val h)

/-- Restricting `braessAugmented` along `braessEmbed` has the exact same feasible flows and cost
`3/2` at `![1/2, 1/2]`, and `HasAffineLatencies.cost_le_four_thirds_restrictPaths` bounds the
augmented Wardrop cost `2` by `4/3 * (3/2) = 2` with equality. -/
example :
    (braessAugmented.restrictPaths braessEmbed).cost ![1 / 2, 1 / 2] = 3 / 2 ∧
      braessAugmented.cost ![0, 0, 1] = 2 ∧
      braessAugmented.cost ![0, 0, 1] ≤
        4 / 3 * (braessAugmented.restrictPaths braessEmbed).cost ![1 / 2, 1 / 2] := by
  have hfeas : (braessAugmented.restrictPaths braessEmbed).IsFeasible ![1 / 2, 1 / 2] := by
    refine ⟨fun p => by fin_cases p <;> norm_num, fun _ => ?_⟩
    simp [restrictPaths, braessAugmented, Fin.sum_univ_two]
    norm_num
  have hcost_sub :
      (braessAugmented.restrictPaths braessEmbed).cost ![1 / 2, 1 / 2] = 3 / 2 := by
    rw [← braessAugmented.cost_extendFlow braessEmbed ![1 / 2, 1 / 2]]
    have hext : extendFlow braessEmbed ![1 / 2, 1 / 2] = ![1 / 2, 1 / 2, 0] := by
      ext p
      fin_cases p
      · exact extendFlow_apply_map braessEmbed ![1 / 2, 1 / 2] 0
      · exact extendFlow_apply_map braessEmbed ![1 / 2, 1 / 2] 1
      · refine extendFlow_eq_zero_of_forall_ne braessEmbed ![1 / 2, 1 / 2] fun q => ?_
        fin_cases q <;> decide
    rw [hext, braessAugmented_cost]
    norm_num
  have hw : braessAugmented.IsWardrop ![0, 0, 1] := braessAugmented_isWardrop_iff.2 rfl
  refine ⟨hcost_sub, braess_paradox.2.2.2.1,
    braessAugmented_hasAffineLatencies.cost_le_four_thirds_restrictPaths braessEmbed hw hfeas⟩

/-! ### 4. Capacity augmentation, affine `δ = 1/4` threshold, and `√x` concave Pigou check -/

/-- On `linearPigou`, `(5/4) r` augmentation (`δ = 1/4`) achieves optimal cost `1` matching the
rate-`1` Wardrop cost `1`, whereas `δ = 1/8 < 1/4` achieves optimal cost `7/8 < 1` (showing
`δ = 1/4` cannot be lowered). -/
example :
    (linearPigou.scaleRate (1 + 1 / 4)).IsFeasible ![1 / 2, 3 / 4] ∧
      linearPigou.cost ![1, 0] ≤ linearPigou.cost ![1 / 2, 3 / 4] ∧
      (linearPigou.scaleRate (1 + 1 / 8)).IsFeasible ![1 / 2, 5 / 8] ∧
      linearPigou.cost ![1 / 2, 5 / 8] = 7 / 8 ∧
      linearPigou.cost ![1 / 2, 5 / 8] < linearPigou.cost ![1, 0] := by
  have hf54 : (linearPigou.scaleRate (1 + 1 / 4)).IsFeasible ![1 / 2, 3 / 4] := by
    refine ⟨fun p => by fin_cases p <;> norm_num, fun _ => ?_⟩
    simp [linearPigou, scaleRate, pigouNetwork, Fin.sum_univ_two]
    norm_num
  have hf98 : (linearPigou.scaleRate (1 + 1 / 8)).IsFeasible ![1 / 2, 5 / 8] := by
    refine ⟨fun p => by fin_cases p <;> norm_num, fun _ => ?_⟩
    simp [linearPigou, scaleRate, pigouNetwork, Fin.sum_univ_two]
    norm_num
  refine ⟨hf54,
    linearPigou_hasAffineLatencies.cost_le_of_scaleRate le_rfl
      (pigouNetwork_isWardrop _ zero_le_one) hf54,
    hf98,
    by rw [pigouNetwork_cost]; norm_num,
    by rw [pigouNetwork_cost, pigouNetwork_cost]; norm_num⟩

/-- `Real.sqrt` belongs to `concaveLatencies`, so any Wardrop flow on `pigouNetwork Real.sqrt 1`
costs at most `4/3` times any feasible flow; at `x = 4/9` its Pigou ratio is `27/23 ≤ 4/3`. -/
example :
    pigouRatio Real.sqrt 1 (4 / 9) = ENNReal.ofReal (27 / 23) ∧
      ∀ f g : Fin 2 → ℝ,
        (pigouNetwork Real.sqrt 1).IsWardrop f →
        (pigouNetwork Real.sqrt 1).IsFeasible g →
        (pigouNetwork Real.sqrt 1).cost f ≤ 4 / 3 * (pigouNetwork Real.sqrt 1).cost g := by
  have hratio : pigouRatio Real.sqrt 1 (4 / 9) = ENNReal.ofReal (27 / 23) := by
    have hsqrt1 : √(1 : ℝ) = 1 := Real.sqrt_one
    have hsqrt49 : √(4 / 9 : ℝ) = 2 / 3 :=
      (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
    simp only [pigouRatio, hsqrt1, hsqrt49]
    norm_num
  refine ⟨hratio, fun f g hf hg => hf.cost_le_four_thirds_of_mem_concaveLatencies (fun e => ?_) hg⟩
  fin_cases e
  · exact sqrt_mem_concaveLatencies
  · change (fun _ => √1) ∈ concaveLatencies
    exact const_mem_concaveLatencies (√1) (Real.sqrt_nonneg 1)

/-! ### 5. Online Wardrop no-regret convergence -/

/-- Two-day flow sequence `f 0 = ![1, 0]`, `f 1 = ![1/2, 1/2]` on `linearPigou`: its average
external regret is `1/8`, so `HasAffineLatencies.isApproxWardrop_timeAverageFlow` certifies that
`timeAverageFlow f 2 = ![3/4, 1/4]` is `(1/8)`-Wardrop (its exact Wardrop gap is `1/16 ≤ 1/8`). -/
example :
    let f : ℕ → Fin 2 → ℝ := fun t => if t = 0 then ![1, 0] else ![1 / 2, 1 / 2]
    linearPigou.HasAvgRegretLe f 2 (1 / 8) ∧
      timeAverageFlow f 2 = ![3 / 4, 1 / 4] ∧
      linearPigou.IsApproxWardrop (1 / 8) (timeAverageFlow f 2) ∧
      linearPigou.cost (timeAverageFlow f 2) -
        linearPigou.pathLatency (timeAverageFlow f 2) 0 = 1 / 16 := by
  intro f
  have heflow : ∀ (g : Fin 2 → ℝ) (e : Fin 2), linearPigou.edgeFlow g e = g e := fun g e => by
    simp [edgeFlow, linearPigou, pigouNetwork, Finset.filter_eq]
  have hreg : linearPigou.HasAvgRegretLe f 2 (1 / 8) := by
    rw [hasAvgRegretLe_unit_iff rfl (by decide)]
    refine ⟨fun t ht => ?_, fun p => ?_⟩
    · have ht2 : t = 0 ∨ t = 1 := by omega
      rcases ht2 with rfl | rfl
      · change linearPigou.IsFeasible ![1, 0]
        have h10 : (![1, (1 : ℝ) - 1] : Fin 2 → ℝ) = ![1, 0] := by
          ext i; fin_cases i <;> norm_num
        rw [← h10]
        exact pigouNetwork_isFeasible (fun x => x) zero_le_one le_rfl
      · exact linearPigou_isOptimal_half.1
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, linearPigou,
        pigouNetwork_cost, pathLatency, heflow, f, ↓reduceIte]
      fin_cases p <;> norm_num [pigouNetwork]
  have havg : timeAverageFlow f 2 = ![3 / 4, 1 / 4] := by
    ext i
    simp only [timeAverageFlow, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, f,
      ↓reduceIte]
    fin_cases i <;> norm_num
  have happ : linearPigou.IsApproxWardrop (1 / 8) (timeAverageFlow f 2) :=
    linearPigou_hasAffineLatencies.isApproxWardrop_timeAverageFlow (by decide) hreg
  have hgap : linearPigou.cost (timeAverageFlow f 2) -
      linearPigou.pathLatency (timeAverageFlow f 2) 0 = 1 / 16 := by
    rw [havg, linearPigou, pigouNetwork_cost]
    have hp0 : linearPigou.pathLatency ![3 / 4, 1 / 4] 0 = 3 / 4 := by
      rw [pathLatency]
      change ∑ e ∈ ({0} : Finset (Fin 2)),
          linearPigou.latency e (linearPigou.edgeFlow ![3 / 4, 1 / 4] e) = 3 / 4
      rw [Finset.sum_singleton, heflow]
      rfl
    change (3 / 4 : ℝ) * (3 / 4) + (1 / 4) * 1 -
        linearPigou.pathLatency ![3 / 4, 1 / 4] 0 = 1 / 16
    rw [hp0]
    norm_num
  exact ⟨hreg, havg, happ, hgap⟩

end CslibFrontierTests.GameTheory.RoutingBeckmann
