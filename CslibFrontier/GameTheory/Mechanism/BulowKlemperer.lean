/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.Bayesian
public import CslibFrontier.GameTheory.Mechanism.OptimalAuction
import CslibFrontier.Foundations.MeasureTheory.Integral.PiUpdate
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.Linarith

/-!
# The Bulow–Klemperer theorem

For a single item and i.i.d. bidders drawn from a regular distribution `μ` with density `f` on
`[0, h]`, the **Bulow–Klemperer theorem** ([BulowKlemperer1996]; [Roughgarden2016], Theorem 5.6;
[Hartline2021], Theorem 5.1.1; locators not re-verified against primary PDF) states that the
expected revenue of the second-price (Vickrey) auction with **no reserve price** and `n + 1`
bidders is at least the expected revenue of Myerson's optimal auction with `n` bidders (and hence
at least that of every DSIC, IR—or Bayes–Nash equilibrium with nonpositive zero-type payments—
single-item mechanism with `n` bidders).

The proof follows the standard virtual-welfare argument:

1. For any valuation distribution with a density, the expected virtual valuation is zero
   (`HasValueDensity.integral_virtualValue_eq_zero`), by applying the one-dimensional revenue
   identity `HasValueDensity.integral_payment_eq_integral_virtualValue_mul` to the constant
   allocation curve `g = 1`.
2. Define an auxiliary `(n + 1)`-bidder allocation rule `auxAllocation`: run Myerson's optimal
   `n`-bidder reserve rule on the first `n` bidders, and whenever none of them wins, award the
   item to the `(n + 1)`-th bidder. Its total allocation is identically `1`, and the extra bidder's
   expected virtual surplus is `0` by independence and step 1, so its expected virtual welfare
   equals Myerson's `n`-bidder optimal revenue.
3. Because `μ` is regular, its virtual valuation `φ` is strictly increasing on `(0, ∞)`. On the
   almost-sure event that all bids are strictly positive, the `(n + 1)`-bidder Vickrey allocation
   gives weight `1` to the highest bidder, which maximizes `∑ᵢ φ(vᵢ) yᵢ` over all nonnegative
   allocations with `∑ᵢ yᵢ = 1`, dominating `auxAllocation` pointwise. Integrating yields
   `E[revenue(Myerson_n)] ≤ E[revenue(Vickrey_{n+1})]`.

## Main results

* `SingleParameter.HasValueDensity.integral_virtualValue_eq_zero`: `E[φ(v)] = 0`.
* `SingleParameter.Vickrey.integral_sum_payment_reserve_le_vickrey_succ`: **Bulow–Klemperer
  theorem** comparing Myerson's `n`-bidder reserve auction to the `(n + 1)`-bidder Vickrey auction.
* `SingleParameter.Vickrey.integral_sum_payment_le_vickrey_succ`: **Bulow–Klemperer theorem** for
  arbitrary DSIC, individually rational `n`-bidder single-item mechanisms.
* `SingleParameter.Vickrey.integral_sum_payment_le_vickrey_succ_of_isBayesNash`: **Bulow–Klemperer
  theorem** for arbitrary Bayes–Nash equilibria of `n`-bidder single-item mechanisms with
  nonpositive zero-type interim payments.

## References

* [J. Bulow, P. Klemperer, *Auctions versus negotiations*][BulowKlemperer1996]
* [T. Roughgarden, *Twenty Lectures on Algorithmic Game Theory*][Roughgarden2016]
* [J. D. Hartline, *Mechanism Design and Approximation*][Hartline2021]
* [R. B. Myerson, *Optimal auction design*][Myerson1981]
-/

open MeasureTheory Set

public section

namespace Cslib.GameTheory.SingleParameter

/-- **Expected virtual valuation is zero**: applying the one-dimensional revenue identity
`HasValueDensity.integral_payment_eq_integral_virtualValue_mul` to the constant curve `g = 1`
gives `E[φ(v)] = E[v − ∫₀ᵛ 1] = 0`. -/
theorem HasValueDensity.integral_virtualValue_eq_zero {μ : Measure ℝ} [IsFiniteMeasure μ]
    {f : ℝ → NNReal} {h : ℝ} (hμ : HasValueDensity μ f h) :
    ∫ v, virtualValue μ f v ∂μ = 0 := by
  have hkey := hμ.integral_payment_eq_integral_virtualValue_mul (g := fun _ => (1 : ℝ))
    measurable_const (B := 1) (fun _ _ => by norm_num)
  have hlhs : (fun v : ℝ => v * 1 - ∫ _ in (0 : ℝ)..v, (1 : ℝ)) = fun _ => 0 := by
    funext v
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hlhs, integral_zero] at hkey
  simpa only [mul_one] using hkey.symm

namespace Vickrey

/-- Auxiliary `(n + 1)`-bidder allocation rule used in the Bulow–Klemperer proof: run the optimal
`n`-bidder reserve rule on the first `n` bidders (`Fin.castSucc`), and award the item to bidder
`Fin.last n` whenever none of the first `n` bidders wins. -/
private noncomputable def auxAllocation {n : ℕ} (φ : ℝ → ℝ) (v : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  Fin.snoc (reserveAllocation φ (fun j : Fin n => v j.castSucc))
    (1 - ∑ j : Fin n, reserveAllocation φ (fun k : Fin n => v k.castSucc) j)

private theorem auxAllocation_nonneg {n : ℕ} (φ : ℝ → ℝ) (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    0 ≤ auxAllocation φ v i := by
  refine Fin.lastCases ?_ ?_ i
  · simp only [auxAllocation, Fin.snoc_last, sub_nonneg]
    exact (reserveAllocation_mem_singleItemFeasible φ _).2
  · intro j
    simp only [auxAllocation, Fin.snoc_castSucc]
    exact reserveAllocation_nonneg φ _ j

private theorem sum_auxAllocation {n : ℕ} (φ : ℝ → ℝ) (v : Fin (n + 1) → ℝ) :
    ∑ i : Fin (n + 1), auxAllocation φ v i = 1 := by
  rw [Fin.sum_univ_castSucc]
  simp only [auxAllocation, Fin.snoc_castSucc, Fin.snoc_last]
  ring

private theorem measurePreserving_comp_castSucc (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (fun (v : Fin (n + 1) → ℝ) (j : Fin n) => v j.castSucc)
      (Measure.pi fun _ : Fin (n + 1) => μ) (Measure.pi fun _ : Fin n => μ) where
  measurable := measurable_pi_iff.2 fun j => measurable_pi_apply j.castSucc
  map_eq := by
    symm
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply (measurable_pi_iff.2 fun j => measurable_pi_apply j.castSucc)
      (MeasurableSet.univ_pi hs)]
    let s' : Fin (n + 1) → Set ℝ := Fin.snoc s Set.univ
    have hpre : (fun (v : Fin (n + 1) → ℝ) (j : Fin n) => v j.castSucc) ⁻¹' Set.univ.pi s =
        Set.univ.pi s' := by
      ext v
      simp only [Set.mem_preimage, Set.mem_univ_pi]
      constructor
      · intro hv i
        refine Fin.lastCases ?_ ?_ i
        · simp only [s', Fin.snoc_last, Set.mem_univ]
        · intro j
          simp only [s', Fin.snoc_castSucc]
          exact hv j
      · intro hv j
        have := hv j.castSucc
        simpa only [s', Fin.snoc_castSucc] using this
    rw [hpre, Measure.pi_pi, Fin.prod_univ_castSucc]
    simp only [s', Fin.snoc_castSucc, Fin.snoc_last, measure_univ, mul_one]

private theorem measurable_auxAllocation {n : ℕ} {φ : ℝ → ℝ} (hφ : Measurable φ)
    (i : Fin (n + 1)) : Measurable fun v : Fin (n + 1) → ℝ => auxAllocation φ v i := by
  have hproj : Measurable fun (v : Fin (n + 1) → ℝ) (j : Fin n) => v j.castSucc :=
    measurable_pi_iff.2 fun j => measurable_pi_apply j.castSucc
  refine Fin.lastCases ?_ ?_ i
  · simp only [auxAllocation, Fin.snoc_last]
    exact measurable_const.sub
      (Finset.measurable_sum Finset.univ fun j _ => (measurable_reserveAllocation hφ j).comp hproj)
  · intro j
    simp only [auxAllocation, Fin.snoc_castSucc]
    exact (measurable_reserveAllocation hφ j).comp hproj

private theorem auxAllocation_abs_le_one {n : ℕ} (φ : ℝ → ℝ) (v : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : |auxAllocation φ v i| ≤ 1 := by
  rw [abs_of_nonneg (auxAllocation_nonneg φ v i)]
  have hsum := sum_auxAllocation φ v
  have hle : auxAllocation φ v i ≤ ∑ j : Fin (n + 1), auxAllocation φ v j :=
    Finset.single_le_sum (f := fun j => auxAllocation φ v j)
      (fun j _ => auxAllocation_nonneg φ v j) (Finset.mem_univ i)
  linarith

private theorem ae_pos {ι : Type*} [Fintype ι] {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {f : ℝ → NNReal} {h : ℝ} (hμ : HasValueDensity μ f h) :
    ∀ᵐ v ∂Measure.pi (fun _ : ι => μ), ∀ i, 0 < v i := by
  rw [ae_all_iff]
  intro i
  have h0 : ∀ᵐ x ∂μ, 0 < x := by
    have := hμ.nullSingletonClass
    have hne : ∀ᵐ x ∂μ, x ≠ 0 := by
      rw [ae_iff]; simp only [ne_eq, not_not, ofPred_eq_eq_singleton, measure_singleton]
    filter_upwards [hμ.ae_mem, hne] with x hx hne
    exact lt_of_le_of_ne hx.1 hne.symm
  exact (Measure.quasiMeasurePreserving_eval (fun _ : ι => μ) i).ae h0

/-- **Bulow–Klemperer theorem (Myerson reserve vs. Vickrey with one extra bidder)**
([BulowKlemperer1996]; [Roughgarden2016], Theorem 5.6; [Hartline2021], Theorem 5.1.1; locators not
re-verified against primary PDF): for i.i.d. regular bidders drawn from `μ`, the expected revenue
of Myerson's optimal `n`-bidder reserve auction is at most the expected revenue of the
`(n + 1)`-bidder Vickrey auction with no reserve price. -/
theorem integral_sum_payment_reserve_le_vickrey_succ
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → NNReal} {h : ℝ}
    (hμ : HasValueDensity μ f h) (hreg : IsRegular μ f h) (n : ℕ) :
    ∫ v, ∑ i : Fin n, (myerson (reserveAllocation (virtualValue μ f))).payment v i
        ∂Measure.pi (fun _ : Fin n => μ) ≤
      ∫ v, ∑ i : Fin (n + 1), (Vickrey.mechanism (ι := Fin (n + 1))).payment v i
        ∂Measure.pi (fun _ : Fin (n + 1) => μ) := by
  set φ := virtualValue μ f
  have hφm : Measurable φ := hμ.measurable_virtualValue
  have hB_res : ∀ v : Fin n → ℝ, 0 ≤ v → ∀ i, |reserveAllocation φ v i| ≤ 1 := fun v _ i => by
    rcases reserveAllocation_binary φ v i with h | h <;> rw [h] <;> norm_num
  have hB_vic : ∀ v : Fin (n + 1) → ℝ, 0 ≤ v → ∀ i, |allocation v i| ≤ 1 := fun v _ i => by
    rcases allocation_binary v i with h | h <;> rw [h] <;> norm_num
  -- Rewrite both sides as expected virtual welfare
  have hLHS : ∫ v, ∑ i : Fin n, (myerson (reserveAllocation φ)).payment v i
        ∂Measure.pi (fun _ : Fin n => μ) =
      ∫ v, ∑ i : Fin n, φ (v i) * reserveAllocation φ v i ∂Measure.pi (fun _ : Fin n => μ) :=
    integral_sum_myersonPayment_eq (fun _ => hμ)
      (fun i => measurable_reserveAllocation hφm i) hB_res
  have hRHS : ∫ v, ∑ i : Fin (n + 1), (Vickrey.mechanism (ι := Fin (n + 1))).payment v i
        ∂Measure.pi (fun _ : Fin (n + 1) => μ) =
      ∫ v, ∑ i : Fin (n + 1), φ (v i) * allocation v i ∂Measure.pi (fun _ : Fin (n + 1) => μ) :=
    mechanism_isDSIC.integral_sum_payment_eq mechanism_isNormalized (fun _ => hμ)
      (fun i => measurable_allocation i) hB_vic
  rw [hLHS, hRHS]
  -- Step 1: expected virtual welfare of `auxAllocation` on Fin (n + 1) equals the LHS
  have haux_int : ∀ i : Fin (n + 1),
      Integrable (fun v : Fin (n + 1) → ℝ => φ (v i) * auxAllocation φ v i)
        (Measure.pi fun _ : Fin (n + 1) => μ) := fun i =>
    integrable_virtualValue_mul (fun _ => hμ) i (measurable_auxAllocation hφm i)
      (fun v _ => auxAllocation_abs_le_one φ v i)
  have hlast_zero : ∫ v : Fin (n + 1) → ℝ,
      φ (v (Fin.last n)) * auxAllocation φ v (Fin.last n)
        ∂Measure.pi (fun _ : Fin (n + 1) => μ) = 0 := by
    let Φ : (Fin (n + 1) → ℝ) → ℝ → ℝ := fun v z => φ z * auxAllocation φ v (Fin.last n)
    have hΦ : ∀ v z, Φ (Function.update v (Fin.last n) z) = Φ v := by
      intro v z
      funext w
      have hproj : (fun j : Fin n => Function.update v (Fin.last n) z j.castSucc) =
          fun j : Fin n => v j.castSucc := by
        funext j
        exact Function.update_of_ne (Fin.castSucc_lt_last j).ne _ _
      simp only [Φ, auxAllocation, Fin.snoc_last, hproj]
    have hstep := integral_apply_eval_eq_integral_integral (μ := fun _ : Fin (n + 1) => μ)
      hΦ (haux_int (Fin.last n))
    rw [hstep]
    have hinner : ∀ v : Fin (n + 1) → ℝ,
        ∫ z, φ z * auxAllocation φ v (Fin.last n) ∂μ = 0 := fun v => by
      rw [integral_mul_const, hμ.integral_virtualValue_eq_zero, zero_mul]
    simp only [Φ, hinner, integral_zero]
  have haux_eq : ∫ v, ∑ i : Fin n, φ (v i) * reserveAllocation φ v i
        ∂Measure.pi (fun _ : Fin n => μ) =
      ∫ v, ∑ i : Fin (n + 1), φ (v i) * auxAllocation φ v i
        ∂Measure.pi (fun _ : Fin (n + 1) => μ) := by
    rw [integral_finsetSum _ fun i _ => haux_int i, Fin.sum_univ_castSucc, hlast_zero, add_zero,
      ← integral_finsetSum _ fun j _ => haux_int j.castSucc]
    have hmp := measurePreserving_comp_castSucc μ n
    have hFint : Integrable (fun v : Fin n → ℝ => ∑ i : Fin n, φ (v i) * reserveAllocation φ v i)
        (Measure.pi fun _ : Fin n => μ) :=
      integrable_finsetSum _ fun i _ => integrable_virtualValue_mul (fun _ => hμ) i
        (measurable_reserveAllocation hφm i) (fun v hv => hB_res v hv i)
    have hmap := integral_map hmp.measurable.aemeasurable
      (by rw [hmp.map_eq]; exact hFint.aestronglyMeasurable)
    rw [hmp.map_eq] at hmap
    rw [hmap]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    exact Finset.sum_congr rfl fun j _ => by simp only [auxAllocation, Fin.snoc_castSucc]
  rw [haux_eq]
  -- Step 2: Vickrey dominates `auxAllocation` pointwise on strictly positive profiles
  refine integral_mono_ae
    (integrable_finsetSum _ fun i _ => haux_int i)
    (integrable_finsetSum _ fun i _ => integrable_virtualValue_mul (fun _ => hμ) i
      (measurable_allocation i) (fun v hv => hB_vic v hv i)) ?_
  filter_upwards [ae_pos (ι := Fin (n + 1)) hμ] with v hv
  obtain ⟨w, hw⟩ := exists_wins v
  have hmono := (hreg.strictMonoOn_Ioi hμ).monotoneOn
  have hle : ∀ i : Fin (n + 1), φ (v i) ≤ φ (v w) := fun i => by
    rcases eq_or_ne i w with rfl | hi
    · exact le_rfl
    · exact hmono (hv i) (hv w) (hw i hi).1
  have hVick : ∑ i : Fin (n + 1), φ (v i) * allocation v i = φ (v w) := by
    rw [Finset.sum_eq_single w
      (fun j _ hj => by
        rw [allocation_eq_zero_iff.2 fun h => hj (h.unique hw), mul_zero])
      (fun h => absurd (Finset.mem_univ w) h),
      allocation_eq_one_iff.2 hw, mul_one]
  rw [hVick]
  calc ∑ i : Fin (n + 1), φ (v i) * auxAllocation φ v i
      ≤ ∑ i : Fin (n + 1), φ (v w) * auxAllocation φ v i :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hle i) (auxAllocation_nonneg φ v i)
    _ = φ (v w) * ∑ i : Fin (n + 1), auxAllocation φ v i := by rw [Finset.mul_sum]
    _ = φ (v w) := by rw [sum_auxAllocation, mul_one]

/-- **Bulow–Klemperer theorem (DSIC form)** ([BulowKlemperer1996]; [Roughgarden2016], Theorem 5.6;
locators not re-verified against primary PDF): for i.i.d. regular bidders drawn from `μ`, every
DSIC, individually rational `n`-bidder single-item mechanism has expected revenue at most that of
the `(n + 1)`-bidder Vickrey auction with no reserve price. -/
theorem integral_sum_payment_le_vickrey_succ
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → NNReal} {h : ℝ}
    (hμ : HasValueDensity μ f h) (hreg : IsRegular μ f h) {n : ℕ}
    {M : Mechanism (Fin n)} (hM : M.IsDSIC) (hIR : M.IsIR)
    (hMX : ∀ v, 0 ≤ v → M.allocation v ∈ singleItemFeasible)
    (hMm : ∀ i, Measurable fun v => M.allocation v i) :
    ∫ v, ∑ i : Fin n, M.payment v i ∂Measure.pi (fun _ : Fin n => μ) ≤
      ∫ v, ∑ i : Fin (n + 1), (Vickrey.mechanism (ι := Fin (n + 1))).payment v i
        ∂Measure.pi (fun _ : Fin (n + 1) => μ) :=
  (integral_sum_payment_le_reserve hμ hreg hM hIR hMX hMm).trans
    (integral_sum_payment_reserve_le_vickrey_succ hμ hreg n)

/-- **Bulow–Klemperer theorem (Bayes–Nash / BIC form)** ([BulowKlemperer1996]; [Hartline2021],
Theorem 5.1.1; locators not re-verified against primary PDF): for i.i.d. regular bidders drawn from
`μ`, every Bayes–Nash equilibrium `β` of an `n`-bidder single-item mechanism with nonpositive
zero-type interim payments has expected revenue at most that of the `(n + 1)`-bidder Vickrey
auction with no reserve price. -/
theorem integral_sum_payment_le_vickrey_succ_of_isBayesNash
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → NNReal} {h : ℝ}
    (hμ : HasValueDensity μ f h) (hreg : IsRegular μ f h) {n : ℕ}
    {M : Mechanism (Fin n)} {β : Fin n → ℝ → ℝ}
    (hBN : M.IsBayesNash (fun _ => μ) (fun _ => h) β)
    (h0 : ∀ i, M.interimPayment (fun _ => μ) β i (β i 0) ≤ 0)
    (hMX : ∀ b, 0 ≤ b → M.allocation b ∈ singleItemFeasible)
    (hp : ∀ i, Integrable (fun v => M.payment (fun j => β j (v j)) i)
      (Measure.pi fun _ : Fin n => μ))
    (hx : ∀ i, Measurable fun v : Fin n → ℝ => M.allocation (fun j => β j (v j)) i) :
    ∫ v, ∑ i : Fin n, M.payment (fun j => β j (v j)) i ∂Measure.pi (fun _ : Fin n => μ) ≤
      ∫ v, ∑ i : Fin (n + 1), (Vickrey.mechanism (ι := Fin (n + 1))).payment v i
        ∂Measure.pi (fun _ : Fin (n + 1) => μ) := by
  set φ := virtualValue μ f
  have hB : ∀ b : Fin n → ℝ, 0 ≤ b → ∀ i, |M.allocation b i| ≤ 1 := fun b hb i => by
    rcases (hMX b hb).1 i with h | h <;> rw [h] <;> norm_num
  have hB_res : ∀ v : Fin n → ℝ, 0 ≤ v → ∀ i, |reserveAllocation φ v i| ≤ 1 := fun v _ i => by
    rcases reserveAllocation_binary φ v i with h | h <;> rw [h] <;> norm_num
  have hrev := hBN.integral_sum_payment_eq (fun _ => hμ) hp hx hB
  have h0sum : ∑ i : Fin n, M.interimPayment (fun _ => μ) β i (β i 0) ≤ 0 :=
    Finset.sum_nonpos fun i _ => h0 i
  have hvw_le : ∫ v, ∑ i : Fin n, φ (v i) * M.allocation (fun j => β j (v j)) i
        ∂Measure.pi (fun _ : Fin n => μ) ≤
      ∫ v, ∑ i : Fin n, φ (v i) * reserveAllocation φ v i
        ∂Measure.pi (fun _ : Fin n => μ) := by
    have hmax := isVirtualWelfareMaximizing_reserveAllocation (ι := Fin n)
      (hreg.strictMonoOn_Ioi hμ).monotoneOn (virtualValue_le μ f 0)
    have hIntL : Integrable (fun v : Fin n → ℝ =>
        ∑ i : Fin n, φ (v i) * M.allocation (fun j => β j (v j)) i)
        (Measure.pi fun _ : Fin n => μ) := by
      refine integrable_finsetSum _ fun i _ => ?_
      have hφ : Integrable (fun v : Fin n → ℝ => φ (v i)) (Measure.pi fun _ : Fin n => μ) :=
        integrable_comp_eval hμ.integrable_virtualValue
      refine Integrable.mono' (hφ.norm.mul_const 1)
        ((hμ.measurable_virtualValue.comp (measurable_pi_apply i)).mul (hx i)).aestronglyMeasurable
        ?_
      filter_upwards [ae_mem_box fun _ : Fin n => hμ] with v hv
      rw [norm_mul, mul_one]
      exact mul_le_of_le_one_right (norm_nonneg _) (hB _ (fun j => hBN.nonneg (hv j)) i)
    have hIntR : Integrable (fun v : Fin n → ℝ =>
        ∑ i : Fin n, φ (v i) * reserveAllocation φ v i)
        (Measure.pi fun _ : Fin n => μ) :=
      integrable_finsetSum _ fun i _ => integrable_virtualValue_mul (fun _ => hμ) i
        (measurable_reserveAllocation hμ.measurable_virtualValue i) (fun v hv => hB_res v hv i)
    refine integral_mono_ae hIntL hIntR ?_
    filter_upwards [ae_mem_box fun _ : Fin n => hμ] with v hv
    exact (hmax v fun j => (hv j).1).2 _ (hMX _ fun j => hBN.nonneg (hv j))
  have hMyerson : ∫ v, ∑ i : Fin n, φ (v i) * reserveAllocation φ v i
        ∂Measure.pi (fun _ : Fin n => μ) =
      ∫ v, ∑ i : Fin n, (myerson (reserveAllocation φ)).payment v i
        ∂Measure.pi (fun _ : Fin n => μ) :=
    (integral_sum_myersonPayment_eq (fun _ => hμ)
      (fun i => measurable_reserveAllocation hμ.measurable_virtualValue i) hB_res).symm
  have hBK := integral_sum_payment_reserve_le_vickrey_succ hμ hreg n
  linarith

end Vickrey

end Cslib.GameTheory.SingleParameter
