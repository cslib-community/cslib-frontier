/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Resilience
public import CslibFrontier.Probability.SmallBias.AlmostIndependent
import CslibFrontier.Foundations.BooleanAnalysis.Fourier
import CslibFrontier.Foundations.Data.BitString.Sign
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.StatisticalDistance

/-!
# Non-oblivious bit-fixing extraction and resilient extensions

Resilient functions extract near-uniform bits from non-oblivious bit-fixing (NOBF) sources whose
good coordinates `Qᶜ` are `t`-wise independent (or close to it) while the adversarial coordinates
`Q` depend arbitrarily on the good bits [Chattopadhyay–Zuckerman][ChattopadhyayZuckerman2019].

This module supplies:
1. Uniform extension of a distribution on `Qᶜ` to the full cube (`Cslib.BitString.extendUniform`),
   preserving `t`-wise small-bias and `t`-wise independence, together with the equivalence between
   cube-wide `IsKWiseResilient` and the `Qᶜ`-marginal formulation noted as open in
   `CslibFrontier.Probability.Resilience` (`isKWiseResilient_iff_forall_compl`).
2. A sharp fiberwise NOBF extraction bound
   (`Cslib.BitString.abs_sum_bitVal_sub_le_coalitionInfluence_add_dist`,
   `Cslib.BitString.dist_map_uniformOfFintype_bool_le_of_coalitionInfluence`) with factor `1` on
   both `coalitionInfluence D Q f` and the good-bit marginal distance
   `dist (Z.map Qᶜ.restrict) (D.map Qᶜ.restrict)`.
3. Composition with Fourier smoothing
   (`Cslib.BitString.dist_map_uniformOfFintype_bool_le_of_isKWiseSmallBias_restrict`): if
   `Z.map Qᶜ.restrict` is `t`-wise `γ`-biased outside a coalition `Q` of size `#Q ≤ q ≤ n`, then any
   `t`-independent `(q, ε₂)`-resilient `f` with `t`-independent bias at most `ε₁` outputs a bit
   within statistical distance `ε₁ + ε₂ + n ^ t * γ` of uniform.

## Main definitions

* `Cslib.BitString.extendUniform`: extend a distribution on `Qᶜ` by independent uniform bits on `Q`.

## Main results

* `Cslib.BitString.map_restrict_compl_extendUniform`,
  `Cslib.BitString.isKWiseIndependent_extendUniform`: `extendUniform` preserves the `Qᶜ` marginal
  and `k`-wise independence.
* `Cslib.BitString.isKWiseResilient_iff_forall_compl`: equivalence between `IsKWiseResilient` on the
  cube and on distributions over the good coordinates `Qᶜ`.
* `Cslib.BitString.abs_sum_bitVal_sub_le_coalitionInfluence_add_dist`,
  `Cslib.BitString.dist_map_uniformOfFintype_bool_le_of_coalitionInfluence`: NOBF extraction bounds.
* `Cslib.BitString.dist_map_uniformOfFintype_bool_le_of_isKWiseSmallBias_restrict`: extraction from
  an almost-`t`-wise independent NOBF source.

## References

* [E. Chattopadhyay, D. Zuckerman, *Explicit two-source extractors and resilient
  functions*][ChattopadhyayZuckerman2019]
-/

public section

namespace Cslib.BitString

open Finset Probability Cslib.Probability.PMF
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Uniform extensions from the outside coordinates -/

/-- Extend a distribution `D'` on the coordinates outside `Q` to a distribution on all of
`ι → Bool` by sampling the coordinates in `Q` uniformly and independently. -/
noncomputable def extendUniform (Q : Finset ι) (D' : PMF (↥Qᶜ → Bool)) :
    PMF (ι → Bool) :=
  D'.bind fun u =>
    (PMF.uniformOfFintype (↥Q → Bool)).map fun v i =>
      if h : i ∈ Q then v ⟨i, h⟩ else u ⟨i, mem_compl.mpr h⟩

/-- Projecting `extendUniform Q D'` back to `Qᶜ` recovers `D'`. -/
@[simp] theorem map_restrict_compl_extendUniform (Q : Finset ι) (D' : PMF (↥Qᶜ → Bool)) :
    (extendUniform Q D').map Qᶜ.restrict = D' := by
  rw [extendUniform, PMF.map_bind]
  have hinner (u : ↥Qᶜ → Bool) :
      ((PMF.uniformOfFintype (↥Q → Bool)).map
        (fun v i => if h : i ∈ Q then v ⟨i, h⟩ else u ⟨i, mem_compl.mpr h⟩)).map
          Qᶜ.restrict = PMF.pure u := by
    rw [PMF.map_comp]
    have hfun : (fun (v : ↥Q → Bool) => Qᶜ.restrict fun i =>
        if h : i ∈ Q then v ⟨i, h⟩ else u ⟨i, mem_compl.mpr h⟩) = Function.const _ u := by
      funext _ ⟨i, hi⟩
      dsimp only [Function.const_apply, Finset.restrict]
      rw [dite_eq_right (fun h => absurd h (mem_compl.mp hi))]
    change PMF.map (fun (v : ↥Q → Bool) => Qᶜ.restrict fun i =>
        if h : i ∈ Q then v ⟨i, h⟩ else u ⟨i, mem_compl.mpr h⟩)
      (PMF.uniformOfFintype (↥Q → Bool)) = PMF.pure u
    rw [hfun, PMF.map_const]
  simp_rw [hinner, PMF.bind_pure]

/-- Any restriction `D.map T.restrict` preserves `k`-wise `ε`-bias. -/
theorem isKWiseSmallBias_map_restrict {D : PMF (ι → Bool)} {k : ℕ} {ε : ℝ}
    (hD : IsKWiseSmallBias k ε D) (T : Finset ι) : IsKWiseSmallBias k ε (D.map T.restrict) := by
  intro S hS hSk
  rw [bias_map_restrict]
  exact hD _ hS.map (by simpa [card_map] using hSk)

/-- Any restriction `D.map T.restrict` preserves `k`-wise independence. -/
theorem isKWiseIndependent_map_restrict {D : PMF (ι → Bool)} {k : ℕ}
    (hD : IsKWiseIndependent k D) (T : Finset ι) : IsKWiseIndependent k (D.map T.restrict) :=
  isKWiseSmallBias_map_restrict hD T

/-- If `S` intersects `Q`, then `extendUniform Q D'` has zero bias on `S`. -/
theorem bias_extendUniform_of_not_disjoint {Q S : Finset ι} (hSQ : ¬Disjoint S Q)
    (D' : PMF (↥Qᶜ → Bool)) : bias (extendUniform Q D') S = 0 := by
  obtain ⟨i₀, hi₀S, hi₀Q⟩ := not_disjoint_iff.mp hSQ
  rw [extendUniform, bias, sum_bind_mul]
  refine sum_eq_zero fun u _ => ?_
  rw [sum_map_mul]
  apply mul_eq_zero_of_right
  let S_Q : Finset ↥Q := (S.filter (· ∈ Q)).subtype (· ∈ Q)
  have hS_Q_ne : S_Q.Nonempty := ⟨⟨i₀, hi₀Q⟩, mem_subtype.mpr (mem_filter.mpr ⟨hi₀S, hi₀Q⟩)⟩
  let c : ℝ := ∏ i ∈ S.filter (· ∉ Q),
    (-1 : ℝ) ^ ((if h : i ∈ Q then false else u ⟨i, mem_compl.mpr h⟩).toNat)
  have hchi (v : ↥Q → Bool) :
      chi ℝ S (fun i => if h : i ∈ Q then v ⟨i, h⟩ else u ⟨i, mem_compl.mpr h⟩) =
        c * chi ℝ S_Q v := by
    rw [chi, ← prod_filter_mul_prod_filter_not S (· ∈ Q)]
    have h1 : (∏ i ∈ S.filter (· ∈ Q),
        (-1 : ℝ) ^ ((if h : i ∈ Q then v ⟨i, h⟩ else u ⟨i, mem_compl.mpr h⟩).toNat)) =
        chi ℝ S_Q v := by
      have hmap : S_Q.map (Function.Embedding.subtype (· ∈ Q)) = S.filter (· ∈ Q) := by
        ext i
        simp [S_Q]
      rw [← hmap, prod_map, chi]
      refine prod_congr rfl fun j _ => ?_
      simp [j.2]
    have h2 : (∏ i ∈ S.filter (· ∉ Q),
        (-1 : ℝ) ^ ((if h : i ∈ Q then v ⟨i, h⟩ else u ⟨i, mem_compl.mpr h⟩).toNat)) = c := by
      refine prod_congr rfl fun i hi => ?_
      have hiQ : i ∉ Q := (mem_filter.mp hi).2
      simp [hiQ]
    rw [h1, h2, mul_comm]
  calc ∑ v : ↥Q → Bool, (PMF.uniformOfFintype (↥Q → Bool) v).toReal *
        chi ℝ S (fun i => if h : i ∈ Q then v ⟨i, h⟩ else u ⟨i, mem_compl.mpr h⟩)
      = c * ∑ v : ↥Q → Bool, (PMF.uniformOfFintype (↥Q → Bool) v).toReal * chi ℝ S_Q v := by
        rw [mul_sum]
        refine sum_congr rfl fun v _ => by rw [hchi v]; ring
    _ = c * 0 := by
        rw [sum_uniformOfFintype_mul, expect_chi, ite_eq_right hS_Q_ne.ne_empty]
    _ = 0 := mul_zero c

private theorem map_subtype_compl_eq {Q S : Finset ι} (hSQ : Disjoint S Q) :
    (S.subtype (· ∈ Qᶜ)).map (Function.Embedding.subtype (· ∈ Qᶜ)) = S := by
  ext i
  simp only [mem_map, mem_subtype, Function.Embedding.coe_subtype, Subtype.exists,
    exists_and_right, exists_eq_right, mem_compl]
  exact ⟨fun ⟨_, hiS⟩ => hiS, fun hiS => ⟨Finset.disjoint_left.mp hSQ hiS, hiS⟩⟩

/-- If `S` is disjoint from `Q`, then the bias of `extendUniform Q D'` on `S` equals the bias of
`D'` on `S` embedded into `Qᶜ`. -/
theorem bias_extendUniform_of_disjoint {Q S : Finset ι} (hSQ : Disjoint S Q)
    (D' : PMF (↥Qᶜ → Bool)) : bias (extendUniform Q D') S = bias D' (S.subtype (· ∈ Qᶜ)) := by
  have h := bias_map_restrict (extendUniform Q D') Qᶜ (S.subtype (· ∈ Qᶜ))
  rw [map_subtype_compl_eq hSQ, map_restrict_compl_extendUniform] at h
  exact h.symm

/-- Extending a `k`-wise `ε`-biased distribution on `Qᶜ` by uniform bits on `Q` yields a `k`-wise
`ε`-biased distribution on `ι → Bool` (for `0 ≤ ε`). -/
theorem isKWiseSmallBias_extendUniform {Q : Finset ι} {D' : PMF (↥Qᶜ → Bool)} {k : ℕ} {ε : ℝ}
    (hε : 0 ≤ ε) (hD' : IsKWiseSmallBias k ε D') :
    IsKWiseSmallBias k ε (extendUniform Q D') := by
  intro S hS hSk
  by_cases hSQ : Disjoint S Q
  · rw [bias_extendUniform_of_disjoint hSQ]
    have hsub_ne : (S.subtype (· ∈ Qᶜ)).Nonempty := by
      obtain ⟨i, hiS⟩ := hS
      exact ⟨⟨i, mem_compl.mpr (Finset.disjoint_left.mp hSQ hiS)⟩, mem_subtype.mpr hiS⟩
    have hcard : #(S.subtype (· ∈ Qᶜ)) ≤ k := by
      rwa [← card_map (Function.Embedding.subtype (· ∈ Qᶜ)), map_subtype_compl_eq hSQ]
    exact hD' _ hsub_ne hcard
  · rw [bias_extendUniform_of_not_disjoint hSQ, abs_zero]
    exact hε

/-- Extending a `k`-wise independent distribution on `Qᶜ` by uniform bits on `Q` yields a `k`-wise
independent distribution on `ι → Bool`. -/
theorem isKWiseIndependent_extendUniform {Q : Finset ι} {D' : PMF (↥Qᶜ → Bool)} {k : ℕ}
    (hD' : IsKWiseIndependent k D') : IsKWiseIndependent k (extendUniform Q D') :=
  isKWiseSmallBias_extendUniform le_rfl hD'

/-! ### Outside-marginal equivalence and coalition monotonicity -/

private def defaultExtend (Q : Finset ι) (u : ↥Qᶜ → Bool) (i : ι) : Bool :=
  if h : i ∈ Q then false else u ⟨i, mem_compl.mpr h⟩

private theorem isUndetermined_iff_defaultExtend (Q : Finset ι) (f : (ι → Bool) → Bool)
    (x : ι → Bool) :
    IsUndetermined Q f x ↔ IsUndetermined Q f (defaultExtend Q (Qᶜ.restrict x)) :=
  isUndetermined_congr fun i hi => by
    simp [defaultExtend, Finset.restrict, hi]

private theorem coalitionInfluence_eq_sum_map_restrict (D : PMF (ι → Bool)) (Q : Finset ι)
    (f : (ι → Bool) → Bool) :
    coalitionInfluence D Q f =
      ∑ u : ↥Qᶜ → Bool, ((D.map Qᶜ.restrict) u).toReal *
        if IsUndetermined Q f (defaultExtend Q u) then 1 else 0 := by
  rw [coalitionInfluence]
  have hcongr : (∑ x, (D x).toReal * if IsUndetermined Q f x then 1 else 0) =
      ∑ x, (D x).toReal *
        if IsUndetermined Q f (defaultExtend Q (Qᶜ.restrict x)) then 1 else 0 :=
    sum_congr rfl fun x _ =>
      congrArg (_ * ·) (if_congr (isUndetermined_iff_defaultExtend Q f x) rfl rfl)
  rw [hcongr, ← sum_map_mul D Qᶜ.restrict
    fun u => if IsUndetermined Q f (defaultExtend Q u) then (1 : ℝ) else 0]

/-- Two distributions with the same `Qᶜ`-marginal give `Q` the exact same coalition influence. -/
theorem coalitionInfluence_eq_of_map_restrict_eq {D₁ D₂ : PMF (ι → Bool)} {Q : Finset ι}
    (h : D₁.map Qᶜ.restrict = D₂.map Qᶜ.restrict) (f : (ι → Bool) → Bool) :
    coalitionInfluence D₁ Q f = coalitionInfluence D₂ Q f := by
  rw [coalitionInfluence_eq_sum_map_restrict D₁, coalitionInfluence_eq_sum_map_restrict D₂, h]

/-- **Cube-versus-marginal resilience equivalence**: `t`-independent `(q, ε)`-resilience over all
cube distributions `D` is equivalent to resilience over uniform extensions `extendUniform Q D'` of
`t`-wise independent distributions `D'` on `Qᶜ`, resolving the equivalence left unformalized in
`CslibFrontier.Probability.Resilience`. -/
theorem isKWiseResilient_iff_forall_compl {t q : ℕ} {ε : ℝ} {f : (ι → Bool) → Bool} :
    IsKWiseResilient t q ε f ↔
      ∀ Q : Finset ι, #Q = q → ∀ D' : PMF (↥Qᶜ → Bool), IsKWiseIndependent t D' →
        coalitionInfluence (extendUniform Q D') Q f ≤ ε := by
  constructor
  · intro hf Q hQ D' hD'
    exact hf Q hQ (extendUniform Q D') (isKWiseIndependent_extendUniform hD')
  · intro h Q hQ D hD
    have hD' : IsKWiseIndependent t (D.map Qᶜ.restrict) :=
      isKWiseIndependent_map_restrict hD Qᶜ
    have heq : coalitionInfluence D Q f =
        coalitionInfluence (extendUniform Q (D.map Qᶜ.restrict)) Q f := by
      rw [coalitionInfluence_eq_sum_map_restrict D Q f,
        coalitionInfluence_eq_sum_map_restrict (extendUniform Q (D.map Qᶜ.restrict)) Q f,
        map_restrict_compl_extendUniform]
    have hle := h Q hQ (D.map Qᶜ.restrict)
    exact heq.trans_le (hle hD')

/-- A `t`-independent `(q, ε)`-resilient function bounds every smaller coalition `#Q ≤ q` whenever
`q ≤ Fintype.card ι`. -/
theorem IsKWiseResilient.coalitionInfluence_le_of_card_le {t q : ℕ} {ε : ℝ}
    {f : (ι → Bool) → Bool} (hf : IsKWiseResilient t q ε f) {Q : Finset ι}
    (hQq : #Q ≤ q) (hq : q ≤ Fintype.card ι) {D : PMF (ι → Bool)}
    (hD : IsKWiseIndependent t D) : coalitionInfluence D Q f ≤ ε := by
  obtain ⟨Q', hQQ', hQ'card⟩ := exists_superset_card_eq (show #Q ≤ q from hQq) (by simpa using hq)
  exact (coalitionInfluence_mono D hQQ' f).trans (hf Q' hQ'card D hD)

/-! ### Non-oblivious bit-fixing extraction -/

private noncomputable def fiberBitSum (Z : PMF (ι → Bool)) (Q : Finset ι) (f : (ι → Bool) → Bool)
    (u : ↥Qᶜ → Bool) : ℝ :=
  ∑ x, (Z x).toReal * if Qᶜ.restrict x = u then bitVal ℝ (f x) else 0

private theorem sum_fiberBitSum (Z : PMF (ι → Bool)) (Q : Finset ι) (f : (ι → Bool) → Bool) :
    ∑ u, fiberBitSum Z Q f u = ∑ x, (Z x).toReal * bitVal ℝ (f x) := by
  simp only [fiberBitSum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  simp [mul_ite]

private theorem fiberBitSum_nonneg (Z : PMF (ι → Bool)) (Q : Finset ι) (f : (ι → Bool) → Bool)
    (u : ↥Qᶜ → Bool) : 0 ≤ fiberBitSum Z Q f u := by
  refine sum_nonneg fun x _ => mul_nonneg ENNReal.toReal_nonneg ?_
  split_ifs
  · cases f x <;> norm_num
  · exact le_rfl

private theorem fiberBitSum_le_map_restrict (Z : PMF (ι → Bool)) (Q : Finset ι)
    (f : (ι → Bool) → Bool) (u : ↥Qᶜ → Bool) :
    fiberBitSum Z Q f u ≤ ((Z.map Qᶜ.restrict) u).toReal := by
  rw [fiberBitSum, map_apply_toReal]
  refine sum_le_sum fun x _ => ?_
  by_cases hx : Qᶜ.restrict x = u
  · rw [ite_eq_left hx, ite_eq_left hx.symm]
    refine mul_le_of_le_one_right ENNReal.toReal_nonneg ?_
    cases f x <;> norm_num
  · rw [ite_eq_right hx, ite_eq_right (Ne.symm hx), mul_zero]

private theorem fiberBitSum_eq_of_not_isUndetermined (Z : PMF (ι → Bool)) (Q : Finset ι)
    (f : (ι → Bool) → Bool) {u : ↥Qᶜ → Bool}
    (hu : ¬IsUndetermined Q f (defaultExtend Q u)) :
    fiberBitSum Z Q f u = ((Z.map Qᶜ.restrict) u).toReal * bitVal ℝ (f (defaultExtend Q u)) := by
  rw [fiberBitSum, map_apply_toReal, sum_mul]
  refine sum_congr rfl fun x _ => ?_
  by_cases hx : Qᶜ.restrict x = u
  · have hfx : f x = f (defaultExtend Q u) := by
      by_contra hne
      apply hu
      refine ⟨x, defaultExtend Q u, fun i hi => ?_, fun _ _ => rfl, hne⟩
      have hres := congrArg (fun g : ↥Qᶜ → Bool => g ⟨i, mem_compl.mpr hi⟩) hx
      change x i = u ⟨i, mem_compl.mpr hi⟩ at hres
      simp [defaultExtend, hi, hres]
    rw [ite_eq_left hx, ite_eq_left hx.symm, hfx]
  · rw [ite_eq_right hx, ite_eq_right (Ne.symm hx), mul_zero, zero_mul]

omit [Fintype ι] [DecidableEq ι] in
private theorem dist_eq_sum_max_zero_sub {α : Type*} [Fintype α] (p q : PMF α) :
    dist p q = ∑ a, max 0 ((p a).toReal - (q a).toReal) := by
  rw [dist_eq_sum_filter_lt, sum_filter]
  refine sum_congr rfl fun a _ => ?_
  by_cases h : (q a).toReal < (p a).toReal
  · rw [ite_eq_left h, max_eq_right (sub_nonneg.mpr h.le)]
  · rw [ite_eq_right h, max_eq_left (sub_nonpos.mpr (not_lt.mp h))]

private theorem sum_bitVal_sub_le_coalitionInfluence_add_dist (Z D : PMF (ι → Bool))
    (Q : Finset ι) (f : (ι → Bool) → Bool) :
    (∑ x, (Z x).toReal * bitVal ℝ (f x)) - ∑ x, (D x).toReal * bitVal ℝ (f x) ≤
      coalitionInfluence D Q f + dist (Z.map Qᶜ.restrict) (D.map Qᶜ.restrict) := by
  rw [← sum_fiberBitSum Z Q f, ← sum_fiberBitSum D Q f, ← sum_sub_distrib,
    coalitionInfluence_eq_sum_map_restrict D Q f, dist_eq_sum_max_zero_sub, ← sum_add_distrib]
  refine sum_le_sum fun u _ => ?_
  by_cases hu : IsUndetermined Q f (defaultExtend Q u)
  · rw [ite_eq_left hu, mul_one]
    have hZ := fiberBitSum_le_map_restrict Z Q f u
    have hD := fiberBitSum_nonneg D Q f u
    linarith [le_max_left (0 : ℝ) ((Z.map Qᶜ.restrict u).toReal - (D.map Qᶜ.restrict u).toReal),
      le_max_right (0 : ℝ) ((Z.map Qᶜ.restrict u).toReal - (D.map Qᶜ.restrict u).toReal)]
  · rw [ite_eq_right hu, mul_zero, zero_add,
      fiberBitSum_eq_of_not_isUndetermined Z Q f hu,
      fiberBitSum_eq_of_not_isUndetermined D Q f hu, ← sub_mul]
    have hb0 : 0 ≤ bitVal ℝ (f (defaultExtend Q u)) := by cases f (defaultExtend Q u) <;> norm_num
    have hb1 : bitVal ℝ (f (defaultExtend Q u)) ≤ 1 := by cases f (defaultExtend Q u) <;> norm_num
    calc ((Z.map Qᶜ.restrict u).toReal - (D.map Qᶜ.restrict u).toReal) *
          bitVal ℝ (f (defaultExtend Q u))
        ≤ max 0 ((Z.map Qᶜ.restrict u).toReal - (D.map Qᶜ.restrict u).toReal) *
          bitVal ℝ (f (defaultExtend Q u)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hb0
      _ ≤ max 0 ((Z.map Qᶜ.restrict u).toReal - (D.map Qᶜ.restrict u).toReal) * 1 :=
          mul_le_mul_of_nonneg_left hb1 (le_max_left _ _)
      _ = max 0 ((Z.map Qᶜ.restrict u).toReal - (D.map Qᶜ.restrict u).toReal) := mul_one _

/-- **Sharp NOBF extraction lemma**: if `Z` and `D` agree on `Qᶜ` up to statistical distance
`dist (Z.map Qᶜ.restrict) (D.map Qᶜ.restrict)`, then for any Boolean function `f`, the
expectation of `f` under `Z` differs from its expectation under `D` by at most
`coalitionInfluence D Q f + dist (Z.map Qᶜ.restrict) (D.map Qᶜ.restrict)`. Both terms carry
exact constant `1`. -/
theorem abs_sum_bitVal_sub_le_coalitionInfluence_add_dist (Z D : PMF (ι → Bool))
    (Q : Finset ι) (f : (ι → Bool) → Bool) :
    |(∑ x, (Z x).toReal * bitVal ℝ (f x)) - ∑ x, (D x).toReal * bitVal ℝ (f x)| ≤
      coalitionInfluence D Q f + dist (Z.map Qᶜ.restrict) (D.map Qᶜ.restrict) := by
  have h1 := sum_bitVal_sub_le_coalitionInfluence_add_dist Z D Q f
  have h2 := sum_bitVal_sub_le_coalitionInfluence_add_dist Z D Q (fun x => !f x)
  have hnot_und : ∀ x, IsUndetermined Q (fun y => !f y) x ↔ IsUndetermined Q f x := by
    intro x
    constructor <;> rintro ⟨y, z, hy, hz, hne⟩ <;>
      exact ⟨y, z, hy, hz, fun h => hne (by simpa [Bool.not_eq_eq_eq_not] using h)⟩
  have hinf : coalitionInfluence D Q (fun y => !f y) = coalitionInfluence D Q f := by
    refine sum_congr rfl fun x _ => ?_
    simp only [hnot_und x]
  have hsum_not (P : PMF (ι → Bool)) :
      ∑ x, (P x).toReal * bitVal ℝ (!f x) = 1 - ∑ x, (P x).toReal * bitVal ℝ (f x) := by
    have hpt (x : ι → Bool) :
        (P x).toReal * bitVal ℝ (!f x) = (P x).toReal - (P x).toReal * bitVal ℝ (f x) := by
      cases f x <;> simp [bitVal]
    simp_rw [hpt, sum_sub_distrib, sum_toReal]
  rw [hinf, hsum_not Z, hsum_not D] at h2
  rw [abs_le]
  constructor <;> linarith

/-- **NOBF output distance to uniform**: if `f` is nearly balanced under `D`, then applying `f` to
`Z` gives a bit within `|𝔼_D[bitVal ∘ f] - 1/2| + coalitionInfluence D Q f +
dist (Z.map Qᶜ.restrict) (D.map Qᶜ.restrict)` of uniform. -/
theorem dist_map_uniformOfFintype_bool_le_of_coalitionInfluence (Z D : PMF (ι → Bool))
    (Q : Finset ι) (f : (ι → Bool) → Bool) :
    dist (Z.map f) (PMF.uniformOfFintype Bool) ≤
      |(∑ x, (D x).toReal * bitVal ℝ (f x)) - 1 / 2| + coalitionInfluence D Q f +
        dist (Z.map Qᶜ.restrict) (D.map Qᶜ.restrict) := by
  rw [dist_uniformOfFintype_bool]
  have htrue : ((Z.map f) true).toReal = ∑ x, (Z x).toReal * bitVal ℝ (f x) := by
    have hsum := sum_map_mul Z f (bitVal ℝ)
    simpa [Fintype.sum_bool] using hsum
  rw [htrue]
  have hnobf := abs_sum_bitVal_sub_le_coalitionInfluence_add_dist Z D Q f
  have htri := abs_sub_le
    (∑ x, (Z x).toReal * bitVal ℝ (f x)) (∑ x, (D x).toReal * bitVal ℝ (f x)) (1 / 2)
  linarith

/-- **Extraction from an almost-`t`-wise independent NOBF source**: if `Z.map Qᶜ.restrict` is
`t`-wise `γ`-biased with `#Q ≤ q ≤ n`, and `f` is `t`-independent `(q, ε₂)`-resilient with
`t`-independent bias at most `ε₁`, then `Z.map f` is within `ε₁ + ε₂ + n ^ t * γ` of uniform. -/
theorem dist_map_uniformOfFintype_bool_le_of_isKWiseSmallBias_restrict
    (Z : PMF (ι → Bool)) (Q : Finset ι) (f : (ι → Bool) → Bool) {t q : ℕ}
    {ε₁ ε₂ γ : ℝ} (hQq : #Q ≤ q) (hq : q ≤ Fintype.card ι) (hγ : 0 ≤ γ)
    (hZ : IsKWiseSmallBias t γ (Z.map Qᶜ.restrict))
    (hf_bias : ∀ D' : PMF (ι → Bool), IsKWiseIndependent t D' →
      |(∑ x, (D' x).toReal * bitVal ℝ (f x)) - 1 / 2| ≤ ε₁)
    (hf_res : IsKWiseResilient t q ε₂ f) :
    dist (Z.map f) (PMF.uniformOfFintype Bool) ≤ ε₁ + ε₂ + (Fintype.card ι : ℝ) ^ t * γ := by
  obtain ⟨D', hD'_ind, hdist⟩ := exists_isKWiseIndependent_dist_le_of_isKWiseSmallBias hγ hZ
  let D : PMF (ι → Bool) := extendUniform Q D'
  have hD_ind : IsKWiseIndependent t D := isKWiseIndependent_extendUniform hD'_ind
  have hmain := dist_map_uniformOfFintype_bool_le_of_coalitionInfluence Z D Q f
  have hD_bias := hf_bias D hD_ind
  have hD_res := hf_res.coalitionInfluence_le_of_card_le hQq hq hD_ind
  have hm : D.map Qᶜ.restrict = D' := map_restrict_compl_extendUniform Q D'
  rw [hm] at hmain
  have hcard : (Fintype.card ↥Qᶜ : ℝ) ^ t * γ ≤ (Fintype.card ι : ℝ) ^ t * γ := by
    gcongr
    have hle : Fintype.card ↥Qᶜ ≤ Fintype.card ι := by
      rw [Fintype.card_coe]
      exact card_le_univ Qᶜ
    exact_mod_cast hle
  linarith

end Cslib.BitString
