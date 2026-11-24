/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Algebra.Covering.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Multiplicative upper functionals below an upper functional

Proposition A.5 of *VP ≠ VNP over every field* [AnthropicVPVNP2026], for a commutative monoid with
a covering relation (`Cslib.Covering`). Below every upper functional `p₀` there is a multiplicative
upper functional that respects every triple `(x, y, c)` which `p₀` respects
(`Cslib.Covering.IsUpperFunctional.exists_map_mul`). The proof follows the paper:

* by Zorn's lemma there is a minimal upper functional below `p₀` that respects its triples;
* its spectral radius `r(t) = inf p(tⁿ)^(1/n)` is again one, so by minimality `p(tⁿ) = p(t)ⁿ`. The
  radius is the infimum of `Cslib.Covering.radiusSet`
  (`Cslib.Covering.IsUpperFunctional.sInf_radiusSet_eq`);
* localizing at an element `f` with `p(fⁿ) = p(f)ⁿ`
  (`Cslib.Covering.IsUpperFunctional.exists_localize`) makes `p` multiplicative.

## Main results

* `Cslib.Covering.IsUpperFunctional.exists_map_mul`.
* `Cslib.Covering.IsUpperFunctional.exists_localize`.
* `Cslib.Covering.IsUpperFunctional.sInf_radiusSet_eq`: the infimum of the radius set is the
  spectral radius.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Proposition A.5 (§A.4) of the paper; module `Paper.Gauges` (the monoid part, where upper
  functionals are called gauges and respecting a triple is keeping it)
-/

public section

namespace Cslib.Covering

open Finset

variable {M : Type*} [CommMonoid M] {D : Covering M} {p : M → ℝ}

/-- Proof of Proposition A.5: the infimum of a chain (or a directed family) of upper functionals is
an upper functional below them that respects every triple which all of them respect. -/
private theorem prop_gauge_chain {ι : Type*} [Nonempty ι] {P : ι → M → ℝ} (dir : Directed (· ≥ ·) P)
    (hP : ∀ i, IsUpperFunctional D (P i)) :
    IsUpperFunctional D (fun t => ⨅ i, P i t) ∧ (∀ i t, ⨅ j, P j t ≤ P i t) ∧
      ∀ x y c, 0 ≤ c → (∀ i, Respects (P i) x y c) → Respects (fun t => ⨅ i, P i t) x y c :=
  ⟨isUpperFunctional_iInf dir (fun i => (hP i).nonneg) (fun i => (hP i).map_one)
      (fun i s t => ⟨i, (hP i).map_mul_le s t⟩)
      (fun i _ _ t b hb => (hP i).le_sum t b hb),
    fun i t => ciInf_le ⟨0, by rintro _ ⟨j, rfl⟩; exact (hP j).nonneg t⟩ i,
    fun _ _ _ hc h => respects_iInf (fun i => (hP i).nonneg) hc h⟩

/-- Proof of Proposition A.5: by Zorn's lemma there is an upper functional `p` below `p₀` that
respects the triples of `p₀` and is equal to every such upper functional below it. -/
private theorem prop_gauge_minimal {p₀ : M → ℝ} (h₀ : IsUpperFunctional D p₀) :
    ∃ p : M → ℝ,
        IsUpperFunctional D p ∧ (∀ t, p t ≤ p₀ t) ∧
            (∀ x y c, 0 ≤ c → Respects p₀ x y c → Respects p x y c) ∧
      ∀ q : M → ℝ,
          IsUpperFunctional D q → (∀ x y c, 0 ≤ c → Respects p₀ x y c → Respects q x y c) →
              (∀ t, q t ≤ p t) →
        ∀ t, q t = p t := by
  set Q : Set (M → ℝ)ᵒᵈ := {q | IsUpperFunctional D (OrderDual.ofDual q) ∧
    ∀ x y c, 0 ≤ c → Respects p₀ x y c → Respects (OrderDual.ofDual q) x y c} with hQ
  obtain ⟨m, hm0, hmax⟩ := zorn_le_nonempty₀ Q (by
    intro c hcQ hchain y hy
    have : Nonempty c := ⟨⟨y, hy⟩⟩
    obtain ⟨h1, h2, h3⟩ := prop_gauge_chain (D := D) (P := fun i : c => OrderDual.ofDual i.1) (by
      intro i j
      rcases hchain.total i.2 j.2 with hij | hij
      · exact ⟨j, hij, le_refl _⟩
      · exact ⟨i, le_refl _, hij⟩) fun i => (hcQ i.2).1
    exact ⟨OrderDual.toDual (fun t => ⨅ i : c, (OrderDual.ofDual i.1) t),
      ⟨h1, fun x y c hc hk => h3 x y c hc fun i => (hcQ i.2).2 x y c hc hk⟩,
          fun z hz t => h2 ⟨z, hz⟩ t⟩)
    (OrderDual.toDual p₀) ⟨h₀, fun _ _ _ _ hk => hk⟩
  refine ⟨OrderDual.ofDual m, hmax.1.1, hm0, hmax.1.2, fun q h1 h2 h3 t => ?_⟩
  have h4 : OrderDual.ofDual m ≤ q := hmax.2 (y := OrderDual.toDual q) ⟨h1, h2⟩ h3
  exact le_antisymm (h3 t) (h4 t)

/-- Proof of Proposition A.5: the spectral radius `r` is at most the sum of its values along a
cover. If `s` is covered by `t_1, …, t_l`, then `sⁿ` is covered by their words of length `n`, and
the bound `p(t_jᵃ) ≤ c_δ (r(t_j) + δ)ᵃ` gives `r(s) ≤ ∑ r(t_j)`. Here `r(t)` is the infimum of
`Cslib.Covering.radiusSet` (equal to the printed `inf p(tⁿ)^(1/n)` by
`Cslib.Covering.IsUpperFunctional.sInf_radiusSet_eq`), and the words are bounded by induction on
`n`. -/
private theorem prop_gauge_radius_cover (h : IsUpperFunctional D p) {κ : Type} [Fintype κ] (t : M)
    (b : κ → M) (hb : D.CoveredBy t b) :
    sInf (radiusSet p t) ≤ ∑ k, sInf (radiusSet p (b k)) := by
  classical
  have h0 : ∀ t, 0 ≤ sInf (radiusSet p t) := fun t => Real.sInf_nonneg fun _ ha => ha.1.le
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set ε := δ / (Fintype.card κ + 1) with hεd
  have hε : 0 < ε := by positivity
  set a : M → ℝ := fun y => sInf (radiusSet p y) + ε with ha
  have ha0 : ∀ y, 0 < a y := fun y => by have := h0 y; simp only [ha]; linarith
  have hmem : ∀ y, ∃ C : ℝ, ∀ m : ℕ, p (y ^ m) ≤ C * a y ^ m := fun y =>
    (h.mem_radiusSet_of_sInf_lt (show sInf (radiusSet p y) < a y by simp only [ha]; linarith)).2
  choose C hC using hmem
  set S := Finset.univ.image b with hS
  set A := ∑ k, a (b k) with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun k _ => (ha0 _).le
  have key : ∀ n : ℕ, ∀ e : M → ℕ, p ((∏ y ∈ S, y ^ e y) * t ^ n) ≤
      (∏ y ∈ S, C y) * (∏ y ∈ S, a y ^ e y) * A ^ n := by
    intro n
    induction n with
    | zero => intro e; simpa using h.map_prod_pow_le S a C ha0 hC e
    | succ n ih =>
      intro e
      have h1 := h.le_sum _ _ (D.mul ((∏ y ∈ S, y ^ e y) * t ^ n) hb)
      have h2 : t * ((∏ y ∈ S, y ^ e y) * t ^ n) = (∏ y ∈ S, y ^ e y) * t ^ (n + 1) := by
        rw [pow_succ', mul_left_comm]
      rw [h2] at h1
      refine h1.trans ?_
      have h3 : ∀ k, p (b k * ((∏ y ∈ S, y ^ e y) * t ^ n)) ≤
          (∏ y ∈ S, C y) * (∏ y ∈ S, a y ^ e y) * A ^ n * a (b k) := by
        intro k
        set y := b k with hy
        have hyS : y ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ _)
        have h4 := ih (fun z => if z = y then e z + 1 else e z)
        have e1 : ∏ z ∈ S, z ^ (if z = y then e z + 1 else e z) =
            y * ∏ z ∈ S, z ^ e z := by
          rw [← Finset.mul_prod_erase S _ hyS, ← Finset.mul_prod_erase S (fun z => z ^ e z) hyS]
          rw [ite_eq_left rfl, pow_succ', mul_assoc]
          congr 2
          refine Finset.prod_congr rfl fun z hz => ?_
          rw [ite_eq_right (Finset.ne_of_mem_erase hz)]
        have e2 : ∏ z ∈ S, a z ^ (if z = y then e z + 1 else e z) =
            a y * ∏ z ∈ S, a z ^ e z := by
          rw [← Finset.mul_prod_erase S _ hyS,
            ← Finset.mul_prod_erase S (fun z => a z ^ e z) hyS]
          rw [ite_eq_left rfl, pow_succ', mul_assoc]
          congr 2
          refine Finset.prod_congr rfl fun z hz => ?_
          rw [ite_eq_right (Finset.ne_of_mem_erase hz)]
        rw [e1, e2] at h4
        rw [← mul_assoc]
        refine h4.trans (le_of_eq ?_)
        ring
      refine (Finset.sum_le_sum fun k _ => h3 k).trans (le_of_eq ?_)
      rw [← Finset.mul_sum, ← hA]
      ring
  have h5 : sInf (radiusSet p t) ≤ A + ε := by
    refine csInf_le (bddBelow_radiusSet p t) ⟨by linarith, ∏ y ∈ S, C y, fun m => ?_⟩
    have h6 := key m (fun _ => 0)
    simp only [pow_zero, Finset.prod_const_one, one_mul, mul_one] at h6
    refine h6.trans ?_
    have : (0 : ℝ) ≤ ∏ y ∈ S, C y :=
      Finset.prod_nonneg fun y _ => zero_le_one.trans (h.one_le_of_map_pow_le (hC y))
    gcongr
    linarith
  have h7 : A = ∑ k, sInf (radiusSet p (b k)) + Fintype.card κ * ε := by
    rw [hA, ha, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h8 : ((Fintype.card κ : ℝ) + 1) * ε = δ := by rw [hεd]; field_simp
  linarith

/-- Proof of Proposition A.5: the spectral radius `r` is an upper functional. The paper notes
`r(1) = 1` and `r(st) ≤ r(s) r(t)`; covers are `prop_gauge_radius_cover`. -/
private theorem prop_gauge_radius (h : IsUpperFunctional D p) : IsUpperFunctional D
    (fun t => sInf (radiusSet p t)) := by
  classical
  have h0 : ∀ t, 0 ≤ sInf (radiusSet p t) := fun t => Real.sInf_nonneg fun _ ha => ha.1.le
  refine ⟨h0, le_antisymm ?_ ?_, ?_, fun t b hb => prop_gauge_radius_cover h t b hb⟩
  · refine le_of_forall_pos_le_add fun δ hδ => csInf_le (bddBelow_radiusSet p 1) ?_
    simpa [h.map_one] using h.add_mem_radiusSet 1 hδ
  · refine le_csInf ⟨_, h.add_mem_radiusSet 1 one_pos⟩ ?_
    rintro a ⟨ha, C, hC⟩
    by_contra hlt
    rw [not_le] at hlt
    have hC1 := h.one_le_of_map_pow_le hC
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / C by positivity) hlt
    have := hC m
    rw [one_pow, h.map_one] at this
    rw [lt_div_iff₀ (by positivity)] at hm
    linarith
  · intro s t
    have key : ∀ a ∈ radiusSet p s, ∀ b ∈ radiusSet p t, sInf (radiusSet p (s * t)) ≤ a * b := by
      rintro a ⟨ha, C, hC⟩ b ⟨hb, C', hC'⟩
      refine csInf_le (bddBelow_radiusSet p _) ⟨by positivity, C * C', fun m => ?_⟩
      rw [mul_pow, mul_pow]
      have h1 := h.one_le_of_map_pow_le hC
      calc p (s ^ m * t ^ m) ≤ p (s ^ m) * p (t ^ m) := h.map_mul_le _ _
        _ ≤ (C * a ^ m) * (C' * b ^ m) :=
          mul_le_mul (hC m) (hC' m) (h.nonneg _) (by positivity)
        _ = _ := by ring
    exact le_sInf_mul_sInf ⟨_, h.add_mem_radiusSet s one_pos⟩ ⟨_, h.add_mem_radiusSet t one_pos⟩
      (fun a ha => ha.1.le) (fun b hb => hb.1.le) key

/-- Proof of Proposition A.5: `r ≤ p`. -/
private theorem prop_gauge_radius_le (h : IsUpperFunctional D p) (t : M) : sInf (radiusSet p t) ≤
    p t :=
  le_of_forall_pos_le_add fun _ hδ => csInf_le (bddBelow_radiusSet p t) (h.add_mem_radiusSet t hδ)

/-- Proof of Proposition A.5: if `p` respects `(x, y, c)`, then `p(tⁿxⁿ) ≤ cⁿ p(tⁿyⁿ)`, so `r`
respects it. -/
private theorem prop_gauge_radius_respects (h : IsUpperFunctional D p) {x y : M} {c : ℝ}
    (hc : 0 ≤ c) (hk : Respects p x y c) :
    Respects (fun t => sInf (radiusSet p t)) x y c := by
  intro t
  -- first p(s x^m) ≤ c^m p(s y^m) for all m and s
  have h1 : ∀ (m : ℕ) (s : M), p (s * x ^ m) ≤ c ^ m * p (s * y ^ m) := by
    intro m
    induction m with
    | zero => intro s; simp
    | succ m ih =>
      intro s
      calc p (s * x ^ (m + 1)) = p (s * x * x ^ m) := by rw [pow_succ', mul_assoc]
        _ ≤ c ^ m * p (s * x * y ^ m) := ih _
        _ = c ^ m * p (s * y ^ m * x) := by rw [mul_right_comm]
        _ ≤ c ^ m * (c * p (s * y ^ m * y)) := by gcongr; exact hk _
        _ = c ^ (m + 1) * p (s * y ^ (m + 1)) := by
          rw [mul_assoc s, ← pow_succ, pow_succ c m, mul_assoc]
  have h2 : ∀ a ∈ radiusSet p (t * y), sInf (radiusSet p (t * x)) ≤ c * a := by
    rintro a ⟨ha, C, hC⟩
    have hC1 := h.one_le_of_map_pow_le hC
    refine le_of_forall_pos_le_add fun δ hδ =>
        csInf_le (bddBelow_radiusSet p _) ⟨by positivity, C, fun m => ?_⟩
    calc p ((t * x) ^ m) = p (t ^ m * x ^ m) := by rw [mul_pow]
      _ ≤ c ^ m * p (t ^ m * y ^ m) := h1 m _
      _ ≤ c ^ m * (C * a ^ m) := by rw [← mul_pow]; gcongr; exact hC m
      _ = C * (c * a) ^ m := by ring
      _ ≤ C * (c * a + δ) ^ m := by gcongr; linarith
  rcases hc.eq_or_lt with rfl | hc
  · simpa using h2 _ (h.add_mem_radiusSet _ one_pos)
  · have h3 : sInf (radiusSet p (t * x)) / c ≤ sInf (radiusSet p (t * y)) := by
      refine le_csInf ⟨_, h.add_mem_radiusSet _ one_pos⟩ fun a ha => ?_
      rw [div_le_iff₀ hc]
      exact (h2 a ha).trans (mul_comm _ _).le
    rw [div_le_iff₀ hc] at h3
    exact h3.trans (mul_comm _ _).le

/-- If p((tⁿ)ᵐ) ≤ C·aᵐ for all m, then p(tᵐ) ≤ C′·bᵐ for all m, with bⁿ = a. -/
private theorem prop_gauge_radius_root (h : IsUpperFunctional D p) {t : M} {n : ℕ} (hn : 0 < n)
    {a : ℝ} (ha : a ∈ radiusSet p (t ^ n)) :
    a ^ ((n : ℝ)⁻¹) ∈ radiusSet p t := by
  obtain ⟨ha, C, hC⟩ := ha
  have hC1 := h.one_le_of_map_pow_le hC
  set b := a ^ ((n : ℝ)⁻¹) with hb
  have hb0 : 0 < b := Real.rpow_pos_of_pos ha _
  have hbn : b ^ n = a := Real.rpow_inv_natCast_pow ha.le (by omega)
  set E := max 1 (p t / b) with hE
  have hE1 : 1 ≤ E := le_max_left _ _
  refine ⟨hb0, C * E ^ n, fun m => ?_⟩
  have h1 : t ^ m = (t ^ n) ^ (m / n) * t ^ (m % n) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have h2 : b ^ m = a ^ (m / n) * b ^ (m % n) := by
    rw [← hbn, ← pow_mul, ← pow_add, Nat.div_add_mod]
  have h3 : p t ≤ E * b := by
    rw [← div_le_iff₀ hb0]; exact le_max_right _ _
  have h4 : p (t ^ (m % n)) ≤ E ^ n * b ^ (m % n) := by
    calc p (t ^ (m % n)) ≤ p t ^ (m % n) := h.map_pow_le _ _
      _ ≤ (E * b) ^ (m % n) := pow_le_pow_left₀ (h.nonneg t) h3 _
      _ = E ^ (m % n) * b ^ (m % n) := mul_pow _ _ _
      _ ≤ E ^ n * b ^ (m % n) := by
        gcongr
        exact (Nat.mod_lt _ hn).le
  rw [h1, h2]
  calc _ ≤ p ((t ^ n) ^ (m / n)) * p (t ^ (m % n)) := h.map_mul_le _ _
    _ ≤ (C * a ^ (m / n)) * (E ^ n * b ^ (m % n)) :=
      mul_le_mul (hC _) h4 (h.nonneg _) (by positivity)
    _ = _ := by ring

/-- The infimum of the radius set of an upper functional `p` at `t` is its spectral radius
`inf_{n ≥ 1} p(tⁿ)^(1/n)`, the number `r(t)` of the proof of Proposition A.5. (That `r(t) + δ`
belongs to the radius set, `Cslib.Covering.IsUpperFunctional.mem_radiusSet_of_sInf_lt`, is the
bound `p(tᵃ) ≤ c_δ (r(t) + δ)ᵃ`, which the paper takes from Fekete's lemma.) -/
theorem IsUpperFunctional.sInf_radiusSet_eq (h : IsUpperFunctional D p) (t : M) :
    sInf (radiusSet p t) = ⨅ n : ℕ, p (t ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹) := by
  have hbdd : BddBelow (Set.range fun n : ℕ => p (t ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹)) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact Real.rpow_nonneg (h.nonneg _) _⟩
  refine le_antisymm (le_ciInf fun n => ?_) (le_csInf ⟨_, h.add_mem_radiusSet t one_pos⟩ ?_)
  · -- (p(tⁿ) + δ)^(1/n) is such an a, for every δ > 0
    have h1 : ∀ δ : ℝ,
        0 < δ → sInf (radiusSet p t) ≤ (p (t ^ (n + 1)) + δ) ^ (((n + 1 : ℕ) : ℝ)⁻¹) := fun δ hδ =>
      csInf_le (bddBelow_radiusSet p t)
          (prop_gauge_radius_root h n.succ_pos (h.add_mem_radiusSet _ hδ))
    have h2 : Filter.Tendsto (fun δ : ℝ => (p (t ^ (n + 1)) + δ) ^ (((n + 1 : ℕ) : ℝ)⁻¹))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (p (t ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹))) := by
      have h3 : Continuous fun δ : ℝ => (p (t ^ (n + 1)) + δ) ^ (((n + 1 : ℕ) : ℝ)⁻¹) :=
        (Real.continuous_rpow_const (by positivity)).comp (continuous_const.add continuous_id)
      have h4 := h3.tendsto 0
      rw [add_zero] at h4
      exact h4.mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto h2 (Filter.eventually_of_mem self_mem_nhdsWithin fun δ hδ => h1 δ hδ)
  · -- p(tⁿ)^(1/n) ≤ C^(1/n)·a, and C^(1/n) tends to 1
    rintro a ⟨ha, C, hC⟩
    have hC1 := h.one_le_of_map_pow_le hC
    have h1 : ∀ n : ℕ, ⨅ n : ℕ,
        p (t ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹) ≤ C ^ (((n + 1 : ℕ) : ℝ)⁻¹) * a := by
      intro n
      refine (ciInf_le hbdd n).trans ?_
      calc p (t ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹) ≤ (C * a ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹) :=
            Real.rpow_le_rpow (h.nonneg _) (hC _) (by positivity)
        _ = C ^ (((n + 1 : ℕ) : ℝ)⁻¹) * a := by
          rw [Real.mul_rpow (by linarith) (by positivity),
              Real.pow_rpow_inv_natCast ha.le n.succ_ne_zero]
    have h2 : Filter.Tendsto (fun n : ℕ => C ^ (((n + 1 : ℕ) : ℝ)⁻¹) * a) Filter.atTop
        (nhds (C ^ (0 : ℝ) * a)) := by
      refine Filter.Tendsto.mul_const a ?_
      refine ((Real.continuous_const_rpow (by linarith : C ≠ 0)).tendsto 0).comp ?_
      exact (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
    rw [Real.rpow_zero, one_mul] at h2
    exact ge_of_tendsto' h2 h1

/-- Proof of Proposition A.5: if `r = p`, then `p(tⁿ) = p(t)ⁿ`. -/
private theorem prop_gauge_radius_pow (h : IsUpperFunctional D p)
    (hr : ∀ t, sInf (radiusSet p t) = p t) (t : M) (n : ℕ) :
    p (t ^ n) = p t ^ n := by
  refine le_antisymm (h.map_pow_le t n) ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [h.map_one]
  rw [← hr (t ^ n)]
  refine le_csInf ⟨_, h.add_mem_radiusSet _ one_pos⟩ fun a ha => ?_
  have h5 : p t ≤ a ^ ((n : ℝ)⁻¹) := by
    rw [← hr t]
    exact csInf_le (bddBelow_radiusSet p t) (prop_gauge_radius_root h hn ha)
  calc p t ^ n ≤ (a ^ ((n : ℝ)⁻¹)) ^ n := pow_le_pow_left₀ (h.nonneg t) h5 n
    _ = a := Real.rpow_inv_natCast_pow ha.1.le (by omega)

/-- Proof of Proposition A.5, localization: for `f` with `p(f) > 0` and `p(fⁿ) = p(f)ⁿ`, the
function `p_f(t) = inf p(tfⁿ)/p(f)ⁿ` (a nonincreasing sequence) is again an upper functional. Here
`p_f(1) = 1`, submultiplicativity follows from `p(stf^(a+b)) ≤ p(sfᵃ)p(tfᵇ)`, and the other two
properties pass to the limit. The statement says of `q = p_f` what is used: it is an upper
functional below `p`, it respects what `p` respects, and it respects `(1, f, 1/p(f))`, that is,
`p(f) · p_f(t) ≤ p_f(tf)`. -/
theorem IsUpperFunctional.exists_localize (h : IsUpperFunctional D p) {f : M} (hf : 0 < p f)
    (hpow : ∀ n, p (f ^ n) = p f ^ n) :
    ∃ q : M → ℝ, IsUpperFunctional D q ∧ (∀ t, q t ≤ p t) ∧ Respects q 1 f (p f)⁻¹ ∧
      ∀ x y c, 0 ≤ c → Respects p x y c → Respects q x y c := by
  set P : ℕ → M → ℝ := fun n t => p (t * f ^ n) / p f ^ n with hP
  have anti : Antitone P := by
    refine antitone_nat_of_succ_le fun n t => ?_
    simp only [hP]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc p (t * f ^ (n + 1)) * p f ^ n ≤ (p (t * f ^ n) * p f) * p f ^ n := by
          gcongr
          rw [pow_succ, ← mul_assoc]
          exact h.map_mul_le _ _
      _ = p (t * f ^ n) * p f ^ (n + 1) := by ring
  have nonneg : ∀ n t, 0 ≤ P n t := fun n t => div_nonneg (h.nonneg _) (by positivity)
  have hle : ∀ n t, ⨅ j, P j t ≤ P n t := fun n t =>
    ciInf_le ⟨0, by rintro _ ⟨i, rfl⟩; exact nonneg i t⟩ n
  refine ⟨fun t => ⨅ n, P n t, isUpperFunctional_iInf anti.directed_ge nonneg ?_ ?_ ?_, ?_, ?_, ?_⟩
  · intro n
    simp only [hP, one_mul, hpow]
    exact div_self (by positivity)
  · intro n s t
    refine ⟨n + n, ?_⟩
    simp only [hP]
    rw [div_mul_div_comm, ← pow_add]
    gcongr
    have : s * t * f ^ (n + n) = (s * f ^ n) * (t * f ^ n) := by
      rw [pow_add]; exact mul_mul_mul_comm _ _ _ _
    rw [this]
    exact h.map_mul_le _ _
  · intro n κ _ t b hb
    have h1 := h.le_sum _ _ (D.mul (f ^ n) hb)
    simp only [hP]
    rw [← Finset.sum_div]
    gcongr
  · intro t
    simpa [hP] using hle 0 t
  · intro t
    rw [mul_one, Real.mul_iInf_of_nonneg (by positivity)]
    refine le_ciInf fun n => (hle (n + 1) t).trans (le_of_eq ?_)
    simp only [hP]
    rw [pow_succ' f n, ← mul_assoc, pow_succ]
    field_simp
  · intro x y c hc hk
    refine respects_iInf nonneg hc fun n t => ?_
    simp only [hP]
    rw [mul_div_assoc']
    gcongr
    have := hk (t * f ^ n)
    rwa [mul_right_comm, mul_right_comm t y]

/-- **Paper: Proposition A.5**, for a commutative monoid with a covering relation: below every upper
functional `p₀` there is a multiplicative upper functional that respects every triple which `p₀`
respects. -/
theorem IsUpperFunctional.exists_map_mul {p₀ : M → ℝ} (h₀ : IsUpperFunctional D p₀) :
    ∃ F : M → ℝ, IsUpperFunctional D F ∧ (∀ s t, F (s * t) = F s * F t) ∧ (∀ t, F t ≤ p₀ t) ∧
      ∀ x y c, 0 ≤ c → Respects p₀ x y c → Respects F x y c := by
  obtain ⟨p, hp, hle, hkeep, hmin⟩ := prop_gauge_minimal h₀
  -- by minimality `r = p`, that is, `p(tⁿ) = p(t)ⁿ`
  have hrad : ∀ t, sInf (radiusSet p t) = p t :=
    hmin _ (prop_gauge_radius hp)
        (fun x y c hc hk => prop_gauge_radius_respects hp hc (hkeep x y c hc hk))
      (prop_gauge_radius_le hp)
  refine ⟨p, hp, fun s f => le_antisymm (hp.map_mul_le s f) ?_, hle, hkeep⟩
  rcases (hp.nonneg f).eq_or_lt with hf | hf
  · -- if `p(f) = 0`, then `p(tf) = 0` as well
    rw [← hf, mul_zero]
    exact hp.nonneg _
  · -- by minimality `p_f = p`, hence `p(tf) = p(t) p(f)`
    obtain ⟨q, hq, hqle, hqk, hqkeep⟩ :=
        IsUpperFunctional.exists_localize hp hf (prop_gauge_radius_pow hp hrad f)
    have hqp := hmin q hq (fun x y c hc hk => hqkeep x y c hc (hkeep x y c hc hk)) hqle
    have h1 := hqk s
    rw [hqp, hqp, mul_one, inv_mul_eq_div, le_div_iff₀ hf] at h1
    exact h1

end Cslib.Covering
