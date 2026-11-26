/-
Copyright (c) 2026 Matthew Doty, Nick L. Leppelmeier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Nick L. Leppelmeier
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Analysis.Brouwer.Simplex
public import CslibFrontier.Foundations.Analysis.Kakutani
public import CslibFrontier.GameTheory.Market.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Dynamics.FixedPoints.Defs
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
import CslibFrontier.Foundations.Analysis.Berge
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Order.Lattice

/-!
# The Gale–Nikaido–Debreu lemma

This module proves the **Gale–Nikaido–Debreu (GND) lemma** ([Gale1955]; [Nikaido1956];
[Debreu1956]) on the standard price simplex `priceSimplex G = {p | (∀ g, 0 ≤ p g) ∧ ∑ g, p g = 1}`
for a finite nonempty set of goods `G`.

## Main definitions

* `Cslib.GameTheory.Market.priceSimplex`: standard unit price simplex on a finite type `G`.
* `Cslib.GameTheory.Market.priceRaisingMap`: price-adjustment map sending `p` to
  `(p + z⁺) / (1 + ∑ k, (z p k)⁺)`.

## Main results

* `Cslib.GameTheory.Market.isFixedPt_priceRaisingMap_iff`: fixed-point characterization of
  `priceRaisingMap z` under Walras's law `expenditure p (z p) ≤ 0`.
* `Cslib.GameTheory.Market.exists_excessDemand_le_zero_of_continuousOn`: single-valued GND lemma
  proved via `Cslib.Brouwer.exists_isFixedPt_simplex`.
* `Cslib.GameTheory.Market.exists_excessDemand_le_zero_of_upperHemicontinuousOn`: set-valued GND
  lemma for upper hemicontinuous compact-convex-valued excess demand correspondences satisfying
  Walras's law, proved via `Cslib.Kakutani.exists_mem_of_isClosed_graph`.

## References

* [D. Gale, *The Law of Supply and Demand*][Gale1955] (primary PDF unverified)
* [H. Nikaido, *On the Classical Multilateral Exchange Problem*][Nikaido1956]
  (primary PDF unverified)
* [G. Debreu, *Market Equilibrium*][Debreu1956] (primary PDF unverified)
-/

public section

namespace Cslib.GameTheory.Market

open Finset Set Function Filter Topology

section PriceSimplex

variable {G : Type*} [Fintype G]

/-- The standard unit price simplex `{p : G → ℝ | (∀ g, 0 ≤ p g) ∧ ∑ g, p g = 1}`. -/
@[expose] def priceSimplex (G : Type*) [Fintype G] : Set (G → ℝ) :=
  {p | (∀ g, 0 ≤ p g) ∧ ∑ g, p g = 1}

theorem priceSimplex_nonempty [Nonempty G] : (priceSimplex G).Nonempty := by
  refine ⟨fun _ => 1 / (Fintype.card G : ℝ), fun _ => by positivity, ?_⟩
  simp [Finset.sum_const, Finset.card_univ]

theorem priceSimplex_convex : Convex ℝ (priceSimplex G) := by
  intro p hp q hq a b ha hb hab
  refine ⟨fun g => add_nonneg (mul_nonneg ha (hp.1 g)) (mul_nonneg hb (hq.1 g)), ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
    hp.2, hq.2, mul_one]
  exact hab

theorem priceSimplex_isCompact : IsCompact (priceSimplex G) := by
  have hEq : priceSimplex G = (univ.pi fun _ : G => Icc (0 : ℝ) 1) ∩
      {p : G → ℝ | ∑ g, p g = 1} := by
    ext p
    simp only [priceSimplex, mem_ofPred_eq, mem_inter_iff, mem_univ_pi, Set.mem_Icc]
    refine ⟨fun ⟨hp0, hsum⟩ => ⟨fun g => ⟨hp0 g, ?_⟩, hsum⟩, fun ⟨hpi, hsum⟩ =>
      ⟨fun g => (hpi g).1, hsum⟩⟩
    calc
      p g ≤ ∑ k, p k := single_le_sum (fun k _ => hp0 k) (mem_univ g)
      _ = 1 := hsum
  rw [hEq]
  refine (isCompact_univ_pi fun _ => isCompact_Icc).inter_right ?_
  exact isClosed_singleton.preimage (continuous_finsetSum Finset.univ fun g _ => continuous_apply g)

end PriceSimplex

section SingleValuedGND

variable {G : Type*} [Fintype G]

/-- The Gale–Nikaido–Debreu price-raising map sending `p` to
`fun g => (p g + max 0 (z p g)) / (1 + ∑ k, max 0 (z p k))`. -/
@[expose] noncomputable def priceRaisingMap (z : (G → ℝ) → (G → ℝ)) (p : G → ℝ) : G → ℝ :=
  fun g => (p g + max 0 (z p g)) / (1 + ∑ k, max 0 (z p k))

theorem priceRaisingMap_mem_priceSimplex (z : (G → ℝ) → (G → ℝ))
    {p : G → ℝ} (hp : p ∈ priceSimplex G) :
    priceRaisingMap z p ∈ priceSimplex G := by
  have hS_nn : 0 ≤ ∑ k, max 0 (z p k) := Finset.sum_nonneg fun _ _ => le_max_left 0 _
  have hden_pos : 0 < 1 + ∑ k, max 0 (z p k) := by linarith
  refine ⟨fun g => div_nonneg (add_nonneg (hp.1 g) (le_max_left 0 _)) hden_pos.le, ?_⟩
  simp only [priceRaisingMap, ← Finset.sum_div, Finset.sum_add_distrib, hp.2]
  exact div_self hden_pos.ne'

theorem continuousOn_priceRaisingMap {z : (G → ℝ) → (G → ℝ)}
    (hz : ContinuousOn z (priceSimplex G)) :
    ContinuousOn (priceRaisingMap z) (priceSimplex G) := by
  have hden_pos : ∀ p ∈ priceSimplex G, 1 + ∑ k, max 0 (z p k) ≠ 0 := fun p _ => by
    have : 0 ≤ ∑ k, max 0 (z p k) := Finset.sum_nonneg fun _ _ => le_max_left 0 _
    linarith
  have hterm : ∀ g, ContinuousOn (fun p => max 0 (z p g)) (priceSimplex G) := fun g =>
    (continuous_const.max continuous_id).continuousOn.comp
      ((continuous_apply g).comp_continuousOn hz) (fun _ _ => mem_univ _)
  have hsum : ContinuousOn (fun p => ∑ k, max 0 (z p k)) (priceSimplex G) :=
    continuousOn_finsetSum Finset.univ fun k _ => hterm k
  have hden : ContinuousOn (fun p => 1 + ∑ k, max 0 (z p k)) (priceSimplex G) :=
    continuousOn_const.add hsum
  refine continuousOn_pi.mpr fun g => ?_
  exact ((continuous_apply g).continuousOn.add (hterm g)).div hden hden_pos

/-- Standalone fixed-point characterization of `priceRaisingMap`: for a price vector `p`
satisfying Walras's law `expenditure p (z p) ≤ 0`, `p` is a fixed point of `priceRaisingMap z` iff
excess demand `z p g` is nonpositive for every good `g`. -/
theorem isFixedPt_priceRaisingMap_iff {z : (G → ℝ) → (G → ℝ)} {p : G → ℝ}
    (hwalras : expenditure p (z p) ≤ 0) :
    IsFixedPt (priceRaisingMap z) p ↔ ∀ g, z p g ≤ 0 := by
  constructor
  · intro hfix
    set S : ℝ := ∑ k, max 0 (z p k)
    have hS_nn : 0 ≤ S := Finset.sum_nonneg fun _ _ => le_max_left 0 _
    rcases eq_or_lt_of_le hS_nn with hS0 | hS_pos
    · intro g
      have hg0 : max 0 (z p g) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun k _ => le_max_left 0 (z p k)).mp
          hS0.symm g (Finset.mem_univ g)
      exact max_eq_left_iff.mp hg0
    · have hden_pos : 0 < 1 + S := by linarith
      have hcoord : ∀ g, p g * S = max 0 (z p g) := by
        intro g
        have hg := congrFun hfix g
        dsimp [priceRaisingMap] at hg
        change (p g + max 0 (z p g)) / (1 + S) = p g at hg
        have hmul := (div_eq_iff hden_pos.ne').mp hg
        linarith
      have hagree : ∀ g, p g * max 0 (z p g) = p g * z p g := by
        intro g
        rcases le_or_gt (z p g) 0 with hle | hgt
        · have hmax0 : max 0 (z p g) = 0 := max_eq_left hle
          have hpg0 : p g = 0 :=
            (mul_eq_zero.mp (by rw [hcoord g, hmax0])).resolve_right hS_pos.ne'
          simp [hmax0, hpg0]
        · rw [max_eq_right hgt.le]
      have hsq_sum : ∑ g, (max 0 (z p g)) ^ 2 = S * expenditure p (z p) := by
        calc
          ∑ g, (max 0 (z p g)) ^ 2
              = ∑ g, (p g * S) * max 0 (z p g) := by
                  refine Finset.sum_congr rfl fun g _ => ?_
                  rw [hcoord g, sq]
          _ = S * ∑ g, p g * max 0 (z p g) := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun g _ => by ring
          _ = S * expenditure p (z p) := by
                  rw [expenditure_eq_sum]
                  exact congrArg (S * ·) (Finset.sum_congr rfl fun g _ => hagree g)
      have hsq_nonpos : ∑ g, (max 0 (z p g)) ^ 2 ≤ 0 := by
        rw [hsq_sum]
        exact mul_nonpos_of_nonneg_of_nonpos hS_pos.le hwalras
      have hsq_zero : ∀ g, (max 0 (z p g)) ^ 2 = 0 := fun g =>
        (Finset.sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg (max 0 (z p k))).mp
          (le_antisymm hsq_nonpos (Finset.sum_nonneg fun k _ => sq_nonneg _)) g (Finset.mem_univ g)
      intro g
      exact max_eq_left_iff.mp (sq_eq_zero_iff.mp (hsq_zero g))
  · intro hle
    ext g
    have hmax : ∀ k, max 0 (z p k) = 0 := fun k => max_eq_left (hle k)
    simp [priceRaisingMap, hmax]

/-- **Single-valued Gale–Nikaido–Debreu lemma** ([Gale1955]; [Nikaido1956]; [Debreu1956]): a
continuous excess demand function on the price simplex satisfying Walras's law
`expenditure p (z p) ≤ 0` admits a price vector `p ∈ priceSimplex G` with `z p ≤ 0`. -/
theorem exists_excessDemand_le_zero_of_continuousOn [Nonempty G]
    {z : (G → ℝ) → (G → ℝ)} (hz_cont : ContinuousOn z (priceSimplex G))
    (hwalras : ∀ p ∈ priceSimplex G, expenditure p (z p) ≤ 0) :
    ∃ p ∈ priceSimplex G, ∀ g, z p g ≤ 0 := by
  obtain ⟨p, hp, hfix⟩ := Cslib.Brouwer.exists_isFixedPt_simplex
    (fun _ h => priceRaisingMap_mem_priceSimplex z h) (continuousOn_priceRaisingMap hz_cont)
  exact ⟨p, hp, (isFixedPt_priceRaisingMap_iff (hwalras p hp)).mp hfix⟩

end SingleValuedGND

section SetValuedGND

private lemma continuous_expenditure_pair {G : Type*} [Fintype G] :
    Continuous fun p : (G → ℝ) × (G → ℝ) => expenditure p.1 p.2 := by
  simp_rw [expenditure_eq_sum]
  exact continuous_finsetSum Finset.univ fun g _ =>
    ((continuous_apply g).comp continuous_fst).mul ((continuous_apply g).comp continuous_snd)

/-- **Set-valued Gale–Nikaido–Debreu lemma** ([Gale1955]; [Nikaido1956]; [Debreu1956]): an upper
hemicontinuous correspondence `Z` on the price simplex with nonempty, compact, convex values
satisfying Walras's law `expenditure p z ≤ 0` admits `p ∈ priceSimplex G` and `z ∈ Z p` with
`∀ g, z g ≤ 0`. -/
theorem exists_excessDemand_le_zero_of_upperHemicontinuousOn {G : Type*} [Fintype G] [Nonempty G]
    {Z : (G → ℝ) → Set (G → ℝ)}
    (hZ_ne : ∀ p ∈ priceSimplex G, (Z p).Nonempty)
    (hZ_comp : ∀ p ∈ priceSimplex G, IsCompact (Z p))
    (hZ_conv : ∀ p ∈ priceSimplex G, Convex ℝ (Z p))
    (hZ_uhc : UpperHemicontinuousOn Z (priceSimplex G))
    (hwalras : ∀ p ∈ priceSimplex G, ∀ z ∈ Z p, expenditure p z ≤ 0) :
    ∃ p ∈ priceSimplex G, ∃ z ∈ Z p, ∀ g, z g ≤ 0 := by
  -- Step 1: Bound the union `⋃ p ∈ priceSimplex G, Z p` inside a box `K = [-R, R]^G`.
  have hloc_bdd : ∀ p₀ : priceSimplex G, ∃ r > 0, ∃ M ≥ (0 : ℝ),
      ∀ p ∈ Metric.ball (p₀ : G → ℝ) r ∩ priceSimplex G, Z p ⊆ Metric.closedBall 0 M := by
    intro p₀
    obtain ⟨M₀, hM₀⟩ := (hZ_comp p₀.val p₀.property).isBounded.subset_closedBall (0 : G → ℝ)
    let U : Set (G → ℝ) := ⋃ w ∈ Z p₀.val, Metric.ball w 1
    have hU_open : IsOpen U := isOpen_biUnion fun _ _ => Metric.isOpen_ball
    have hZ_sub : Z p₀.val ⊆ U := fun w hw => mem_biUnion hw (Metric.mem_ball_self zero_lt_one)
    have hev :=
      (upperHemicontinuousOn_iff_forall_isOpen.mp hZ_uhc) p₀.val p₀.property U hU_open hZ_sub
    obtain ⟨r, hr, hr_sub⟩ := Metric.mem_nhdsWithin_iff.mp hev
    refine ⟨r, hr, max M₀ 0 + 1, by linarith [le_max_right M₀ 0], fun p hp z hz => ?_⟩
    obtain ⟨w, hw_mem, hzw⟩ := mem_iUnion₂.mp (hr_sub hp hz)
    have hw_ball : dist w 0 ≤ M₀ := hM₀ hw_mem
    have hdist : dist z 0 ≤ max M₀ 0 + 1 := by
      have h1 := dist_triangle z w 0
      have h2 : dist z w < 1 := Metric.mem_ball.mp hzw
      linarith [le_max_left M₀ 0]
    exact Metric.mem_closedBall.mpr hdist
  choose r hr_pos M hM_nn hr_sub using hloc_bdd
  have hcov : priceSimplex G ⊆ ⋃ p₀ : priceSimplex G, Metric.ball (p₀ : G → ℝ) (r p₀) :=
    fun p hp => mem_iUnion.mpr ⟨⟨p, hp⟩, Metric.mem_ball_self (hr_pos ⟨p, hp⟩)⟩
  obtain ⟨t, ht_cov⟩ := priceSimplex_isCompact.elim_finite_subcover
    (fun p₀ : priceSimplex G => Metric.ball (p₀ : G → ℝ) (r p₀)) (fun _ => Metric.isOpen_ball) hcov
  let R : ℝ := ∑ p₀ ∈ t, M p₀
  have hR_nn : 0 ≤ R := Finset.sum_nonneg fun p₀ _ => hM_nn p₀
  let K : Set (G → ℝ) := univ.pi fun _ : G => Icc (-R) R
  have hZ_sub_K : ∀ p ∈ priceSimplex G, Z p ⊆ K := by
    intro p hp z hz
    obtain ⟨p₀, hp₀t, hp_ball⟩ := mem_iUnion₂.mp (ht_cov hp)
    have hz_ball : dist z 0 ≤ M p₀ := Metric.mem_closedBall.mp (hr_sub p₀ p ⟨hp_ball, hp⟩ hz)
    have hMp₀_le : M p₀ ≤ R := single_le_sum (fun q _ => hM_nn q) hp₀t
    have hz_R : dist z 0 ≤ R := hz_ball.trans hMp₀_le
    rw [dist_zero_right, pi_norm_le_iff_of_nonneg hR_nn] at hz_R
    intro g _
    exact abs_le.mp (hz_R g)
  have hK_ne : K.Nonempty := ⟨0, fun _ _ => ⟨by simp [hR_nn], hR_nn⟩⟩
  have hK_comp : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  have hK_conv : Convex ℝ K := convex_pi fun _ _ => convex_Icc (-R) R
  -- Step 2: Embed `priceSimplex G ×ˢ K` into `G ⊕ G → ℝ`.
  let inl : (G ⊕ G → ℝ) → (G → ℝ) := fun w g => w (Sum.inl g)
  let inr : (G ⊕ G → ℝ) → (G → ℝ) := fun w g => w (Sum.inr g)
  let S : Set (G ⊕ G → ℝ) := {w | inl w ∈ priceSimplex G ∧ inr w ∈ K}
  have hinl_cont : Continuous inl := continuous_pi fun g => continuous_apply (Sum.inl g)
  have hinr_cont : Continuous inr := continuous_pi fun g => continuous_apply (Sum.inr g)
  have hS_eq_image :
      S = (fun p : (G → ℝ) × (G → ℝ) => Sum.elim p.1 p.2) '' (priceSimplex G ×ˢ K) := by
    ext w
    simp only [S, mem_ofPred_eq, Set.mem_image]
    refine ⟨fun ⟨hp, hz⟩ => ⟨(inl w, inr w), ⟨hp, hz⟩, ?_⟩, ?_⟩
    · ext x
      rcases x with g | g <;> rfl
    · rintro ⟨⟨p, z⟩, ⟨hp, hz⟩, rfl⟩
      exact ⟨hp, hz⟩
  have helim_cont : Continuous fun p : (G → ℝ) × (G → ℝ) => Sum.elim p.1 p.2 :=
    continuous_pi fun x => by
      rcases x with g | g
      · exact (continuous_apply g).comp continuous_fst
      · exact (continuous_apply g).comp continuous_snd
  have hS_ne : S.Nonempty := by
    obtain ⟨p, hp⟩ := priceSimplex_nonempty (G := G)
    obtain ⟨z, hz⟩ := hK_ne
    exact ⟨Sum.elim p z, hp, hz⟩
  have hS_comp : IsCompact S := by
    rw [hS_eq_image]
    exact (priceSimplex_isCompact.prod hK_comp).image helim_cont
  have hS_conv : Convex ℝ S := by
    intro w₁ hw₁ w₂ hw₂ a b ha hb hab
    exact ⟨priceSimplex_convex hw₁.1 hw₂.1 ha hb hab, hK_conv hw₁.2 hw₂.2 ha hb hab⟩
  -- Step 3: Kakutani fixed point of `(p, z) ↦ argmax_q (q ⋅ z) × Z(p)`.
  let Φ : (G ⊕ G → ℝ) → Set (G ⊕ G → ℝ) := fun w =>
    {v | (inl v ∈ priceSimplex G ∧
      ∀ q ∈ priceSimplex G, expenditure q (inr w) ≤ expenditure (inl v) (inr w)) ∧
      inr v ∈ Z (inl w)}
  have hΦ_ne : ∀ w ∈ S, (Φ w).Nonempty := by
    intro w hw
    have hexp_cont : Continuous fun q : G → ℝ => expenditure q (inr w) :=
      continuous_expenditure_pair.comp (continuous_id.prodMk continuous_const)
    obtain ⟨p', hp', hmax⟩ := priceSimplex_isCompact.exists_isMaxOn priceSimplex_nonempty
      hexp_cont.continuousOn
    obtain ⟨z', hz'⟩ := hZ_ne (inl w) hw.1
    exact ⟨Sum.elim p' z', ⟨hp', fun q hq => hmax hq⟩, hz'⟩
  have hΦ_sub : ∀ w ∈ S, Φ w ⊆ S := fun w hw v hv =>
    ⟨hv.1.1, hZ_sub_K (inl w) hw.1 hv.2⟩
  have hΦ_conv : ∀ w ∈ S, Convex ℝ (Φ w) := by
    intro w hw v₁ hv₁ v₂ hv₂ a b ha hb hab
    refine ⟨⟨priceSimplex_convex hv₁.1.1 hv₂.1.1 ha hb hab, fun q hq => ?_⟩,
      hZ_conv (inl w) hw.1 hv₁.2 hv₂.2 ha hb hab⟩
    have hinl_lin : inl (a • v₁ + b • v₂) = a • inl v₁ + b • inl v₂ := rfl
    rw [hinl_lin]
    simp_rw [expenditure_eq_sum]
    have h1 := mul_le_mul_of_nonneg_left (hv₁.1.2 q hq) ha
    have h2 := mul_le_mul_of_nonneg_left (hv₂.1.2 q hq) hb
    simp_rw [expenditure_eq_sum] at h1 h2
    have hlhs : ∑ g, q g * inr w g =
        a * ∑ g, q g * inr w g + b * ∑ g, q g * inr w g := by
      rw [← add_mul, hab, one_mul]
    have hrhs : ∑ g, (a • inl v₁ + b • inl v₂) g * inr w g =
        a * ∑ g, inl v₁ g * inr w g + b * ∑ g, inl v₂ g * inr w g := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc,
        Finset.sum_add_distrib, ← Finset.mul_sum]
    linarith
  have hZ_closed : ∀ p ∈ priceSimplex G, IsClosed (Z p) := fun p hp => (hZ_comp p hp).isClosed
  have hZ_graph_closed :
      IsClosed {pq : (G → ℝ) × (G → ℝ) | pq.1 ∈ priceSimplex G ∧ pq.2 ∈ Z pq.1} :=
    Cslib.Berge.isClosed_graph_of_upperHemicontinuousOn
      priceSimplex_isCompact.isClosed hZ_closed hZ_uhc
  have hΦ_graph : IsClosed {p : (G ⊕ G → ℝ) × (G ⊕ G → ℝ) | p.1 ∈ S ∧ p.2 ∈ Φ p.1} := by
    have hEq : {p : (G ⊕ G → ℝ) × (G ⊕ G → ℝ) | p.1 ∈ S ∧ p.2 ∈ Φ p.1} =
        {p | p.1 ∈ S} ∩
        {p | inl p.2 ∈ priceSimplex G} ∩
        (⋂ q ∈ priceSimplex G,
          {p | expenditure q (inr p.1) ≤ expenditure (inl p.2) (inr p.1)}) ∩
        {p | inl p.1 ∈ priceSimplex G ∧ inr p.2 ∈ Z (inl p.1)} := by
      ext ⟨w, v⟩
      simp only [Φ, mem_ofPred_eq, mem_inter_iff, mem_iInter]
      exact ⟨fun ⟨hwS, ⟨hvinl, hmax⟩, hvZ⟩ => ⟨⟨⟨hwS, hvinl⟩, hmax⟩, hwS.1, hvZ⟩,
        fun ⟨⟨⟨hwS, hvinl⟩, hmax⟩, _, hvZ⟩ => ⟨hwS, ⟨hvinl, hmax⟩, hvZ⟩⟩
    rw [hEq]
    refine (((hS_comp.isClosed.preimage continuous_fst).inter
      (priceSimplex_isCompact.isClosed.preimage (hinl_cont.comp continuous_snd))).inter ?_).inter
      (hZ_graph_closed.preimage ((hinl_cont.comp continuous_fst).prodMk
        (hinr_cont.comp continuous_snd)))
    refine isClosed_biInter fun q _ => ?_
    have hlhs : Continuous fun p : (G ⊕ G → ℝ) × (G ⊕ G → ℝ) => expenditure q (inr p.1) :=
      continuous_expenditure_pair.comp (continuous_const.prodMk (hinr_cont.comp continuous_fst))
    have hrhs :
        Continuous fun p : (G ⊕ G → ℝ) × (G ⊕ G → ℝ) => expenditure (inl p.2) (inr p.1) :=
      continuous_expenditure_pair.comp ((hinl_cont.comp continuous_snd).prodMk
        (hinr_cont.comp continuous_fst))
    exact isClosed_le hlhs hrhs
  obtain ⟨w, hwS, hwΦ⟩ :=
    Cslib.Kakutani.exists_mem_of_isClosed_graph hS_ne hS_comp hS_conv hΦ_ne hΦ_sub hΦ_conv hΦ_graph
  refine ⟨inl w, hwS.1, inr w, hwΦ.2, fun g => ?_⟩
  classical
  let e_g : G → ℝ := Pi.single g 1
  have he_mem : e_g ∈ priceSimplex G := by
    refine ⟨fun k => ?_, ?_⟩
    · by_cases hkg : k = g <;> simp [e_g, hkg]
    · simp [e_g]
  have hsingle : expenditure e_g (inr w) = inr w g := by
    rw [expenditure_eq_sum]
    refine (Finset.sum_eq_single g (fun k _ hne => by simp [e_g, hne]) (by simp)).trans ?_
    simp [e_g]
  calc
    inr w g = expenditure e_g (inr w) := hsingle.symm
    _ ≤ expenditure (inl w) (inr w) := hwΦ.1.2 e_g he_mem
    _ ≤ 0 := hwalras (inl w) hwS.1 (inr w) hwΦ.2

end SetValuedGND

end Cslib.GameTheory.Market
