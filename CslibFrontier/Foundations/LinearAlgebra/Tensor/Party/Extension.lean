/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Foundations.Algebra.Covering.Gauge
import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Duality

/-!
# Extending spectral points to more parties

Proposition A.7 (prop:extend) of *VP ≠ VNP over every field* [AnthropicVPVNP2026]. Let
`ι : I → I'` and `π l : I' → I` be maps with `π l ∘ ι = id`, let `θ l ≥ 0` add up to `1`, let `F` be
a spectral point on `I` and `C` a tensor on `I`. Then there is a spectral point `F'` on `I'` with
`F' t ≤ ∏ l, F (π l t) ^ θ l` for all `t`, and `F' (ι C) = F C`
(`Cslib.PartyTensor.SpectralPoint.exists_extend`).

The proof follows the paper. The infimum of `∑ f (b j)` over the covers `(b j)` of `t`, where `f` is
the product on the right, is an upper functional `p ≤ f` with `p (ι A) = F A` for all `A`.
Localizing it at `ι C` (`Cslib.Covering.IsUpperFunctional.exists_localize`) and taking a spectral
point below the result (`Cslib.PartyTensor.UpperFunctional.exists_spectralPoint_le`) gives `F'`.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Paper.Extension`.

## Main results

* `Cslib.PartyTensor.SpectralPoint.exists_extend`.
-/

public section

namespace Cslib.PartyTensor

open Finset Covering

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]
  {I' : Type} [Fintype I'] [DecidableEq I'] {L : Type} [Fintype L]

namespace SpectralPoint

/-- The product `f t = ∏ l, F (π l t) ^ θ l` of Proposition A.7 (prop:extend). -/
private noncomputable def extendProduct (π : L → I' → I) (θ : L → ℝ) (F : SpectralPoint K I)
    (t : PartyTensor K I') : ℝ :=
  ∏ l, F (push (π l) t) ^ θ l

/-- The product `f` is multiplicative and monotone, `f ≥ 0` and `f 1 = 1`. -/
private theorem extendProduct_spec (π : L → I' → I) (θ : L → ℝ) (hθ : ∀ l, 0 ≤ θ l)
    (F : SpectralPoint K I) :
    (∀ t, 0 ≤ extendProduct π θ F t) ∧ extendProduct π θ F 1 = 1 ∧
    (∀ s t, extendProduct π θ F (s * t) = extendProduct π θ F s * extendProduct π θ F t) ∧
    ∀ {s t}, s ≤ t → extendProduct π θ F s ≤ extendProduct π θ F t := by
  refine ⟨fun t => Finset.prod_nonneg fun l _ => Real.rpow_nonneg (F.nonneg _) _, ?_,
    fun s t => ?_, fun {s t} h => ?_⟩
  · refine Finset.prod_eq_one fun l _ => ?_
    rw [F.congr (antisymmRel_push_one _), F.map_one, Real.one_rpow]
  · rw [extendProduct, extendProduct, extendProduct, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [F.congr (antisymmRel_push_mul _ s t), F.map_mul, Real.mul_rpow (F.nonneg _) (F.nonneg _)]
  · exact Finset.prod_le_prod₀ (fun l _ => Real.rpow_nonneg (F.nonneg _) _) fun l _ =>
      Real.rpow_le_rpow (F.nonneg _) (F.monotone (push_le_push _ h)) (hθ l)

/-- A cover of `ιA` by `b_j` gives a cover of `A` by `a_j` with `a_j ≤ π_l b_j` for every `l`. As in
the paper: if `ιA = ∑ s_j` with `s_j ≤ b_j`, then every `s_j` has trivial index sets outside
`ι(I)`, like `ιA`, so `s_j = ιa_j` with `∑ a_j = A`; and push-forwards preserve restrictions. -/
private theorem exists_cover_of_coveredBy_push (ι : I → I') {A : PartyTensor K I} {κ : Type}
    [Fintype κ] {b : κ → PartyTensor K I'} (h : (push ι A).CoveredBy b) :
    ∃ c : κ → PartyTensor K I, A.CoveredBy c ∧
      ∀ k, ∀ π : I' → I, (∀ i, π (ι i) = i) → c k ≤ push π (b k) := by
  obtain ⟨v, hv, hr⟩ := coveredBy_iff.1 h
  let emb : (∀ i, A.Index i) → ∀ q, (push ι A).Index q := fun x _ j => x j.1
  refine ⟨fun k => A.withEntry fun x => v k (emb x), CoveredBy.withEntry A _ fun x => hv (emb x),
    fun k π hπ => ?_⟩
  have h1 : push ι (A.withEntry fun x => v k (emb x)) ≤ (push ι A).withEntry (v k) :=
    le_of_entry_eq (fun _ x => x) fun x => by
      rw [push_entry]
      refine congrArg (v k) (funext fun _ => funext fun ⟨_, heq⟩ => ?_)
      subst heq
      rfl
  have h4 := antisymmRel_push_push π ι (A.withEntry fun x => v k (emb x))
  rw [show π ∘ ι = id from funext hπ] at h4
  exact (h4.trans (antisymmRel_push_id _)).ge.trans (push_le_push π (h1.trans (hr k)))

/-- `φ(A) ≤ ∑ φ(a_j) ≤ ∑ f(b_j)` for every cover `(b_j)` of `ιA`. -/
private theorem le_sum_extendProduct (ι : I → I') (π : L → I' → I) (hπ : ∀ l i, π l (ι i) = i)
    (θ : L → ℝ) (hθ : ∀ l, 0 ≤ θ l) (hθ1 : ∑ l, θ l = 1) (F : SpectralPoint K I)
    (A : PartyTensor K I) {κ : Type} [Fintype κ] (b : κ → PartyTensor K I')
    (hb : (push ι A).CoveredBy b) : F A ≤ ∑ k, extendProduct π θ F (b k) := by
  obtain ⟨a, ha, hr⟩ := exists_cover_of_coveredBy_push ι hb
  refine (F.le_sum A a ha).trans (Finset.sum_le_sum fun k _ => ?_)
  -- `F (a k)` is at most every factor `F (π l (b k))`, so at most their weighted geometric mean
  rcases (F.nonneg (a k)).eq_or_lt with h0 | h0
  · rw [← h0]
    exact (extendProduct_spec π θ hθ F).1 _
  · calc F (a k) = F (a k) ^ (∑ l, θ l) := by rw [hθ1, Real.rpow_one]
      _ = ∏ l, F (a k) ^ θ l := Real.rpow_sum_of_pos h0 _ _
      _ ≤ extendProduct π θ F (b k) := Finset.prod_le_prod₀
        (fun l _ => Real.rpow_nonneg h0.le _) fun l _ =>
          Real.rpow_le_rpow h0.le (F.monotone (hr k _ (hπ l))) (hθ l)

/-- `f(ιA) = φ(A)`, as `π_l ι = id`. -/
private theorem extendProduct_push (ι : I → I') (π : L → I' → I) (hπ : ∀ l i, π l (ι i) = i)
    (θ : L → ℝ) (hθ1 : ∑ l, θ l = 1) (F : SpectralPoint K I) (A : PartyTensor K I) :
    extendProduct π θ F (push ι A) = F A := by
  have retr (l : L) : AntisymmRel (· ≤ ·) (push (π l) (push ι A)) A := by
    have h := antisymmRel_push_push (π l) ι A
    rw [show π l ∘ ι = id from funext (hπ l)] at h
    exact h.trans (antisymmRel_push_id _)
  have h1 : extendProduct π θ F (push ι A) = ∏ l, F A ^ θ l :=
    Finset.prod_congr rfl fun l _ => by rw [F.congr (retr l)]
  rw [h1]
  rcases (F.nonneg A).eq_or_lt with h0 | h0
  · obtain ⟨l, hl⟩ : ∃ l, θ l ≠ 0 := by
      by_contra! hne
      simp [hne] at hθ1
    rw [← h0]
    exact Finset.prod_eq_zero (Finset.mem_univ l) (Real.zero_rpow hl)
  · rw [← Real.rpow_sum_of_pos h0, hθ1, Real.rpow_one]

/-- There is an upper functional `p ≤ f` with `p(ιA) = φ(A)` for all `A`: the infimum `p(t)` of
`∑ f(b_j)` over the covers `(b_j)` of `t`. -/
private theorem exists_upperFunctional_extend (ι : I → I') (π : L → I' → I)
    (hπ : ∀ l i, π l (ι i) = i) (θ : L → ℝ) (hθ : ∀ l, 0 ≤ θ l) (hθ1 : ∑ l, θ l = 1)
    (F : SpectralPoint K I) :
    ∃ p : UpperFunctional K I', (∀ t, p t ≤ extendProduct π θ F t) ∧
      ∀ A : PartyTensor K I, p (push ι A) = F A := by
  classical
  obtain ⟨f0, f1, fmul, fmono⟩ := extendProduct_spec π θ hθ F
  set f : PartyTensor K I' → ℝ := extendProduct π θ F
  have hcongr {s t : PartyTensor K I'} (h : AntisymmRel (· ≤ ·) s t) : f s = f t :=
    le_antisymm (fmono h.1) (fmono h.2)
  -- the sums `∑ f (b k)` over the covers of a class of tensors
  set S : Antisymmetrization (PartyTensor K I') (· ≤ ·) → Set ℝ := fun m =>
    {W | ∃ (κ : Type) (_ : Fintype κ) (b : κ → Antisymmetrization (PartyTensor K I') (· ≤ ·)),
      (tensorCovering K I').CoveredBy m b ∧ ∑ k, f (ofAntisymmetrization (· ≤ ·) (b k)) = W}
  have hne (t) : (S t).Nonempty :=
    ⟨_, Unit, inferInstance, fun _ => t, (tensorCovering K I').refl t, rfl⟩
  have h0 (t w) : w ∈ S t → 0 ≤ w := by
    rintro ⟨_, _, _, -, rfl⟩
    exact Finset.sum_nonneg fun _ _ => f0 _
  have hlow (A : PartyTensor K I) (w) :
      w ∈ S (toAntisymmetrization (· ≤ ·) (push ι A)) → F A ≤ w := by
    rintro ⟨κ, _, b, hb, rfl⟩
    refine le_sum_extendProduct ι π hπ θ hθ hθ1 F A _ (tensorCovering_coveredBy.1 ?_)
    simpa only [toAntisymmetrization_ofAntisymmetrization] using hb
  have hup (t : PartyTensor K I') : f t ∈ S (toAntisymmetrization (· ≤ ·) t) :=
    ⟨Unit, inferInstance, fun _ => toAntisymmetrization (· ≤ ·) t, (tensorCovering K I').refl _,
      by simpa using hcongr (antisymmRel_ofAntisymmetrization_toAntisymmetrization t)⟩
  have hpre : IsUpperFunctional (tensorCovering K I') (fun t => sInf (S t)) := by
    refine isUpperFunctional_sInf hne h0 (by simpa only [f1, toAntisymmetrization_one] using hup 1)
      (fun w hw => ?_) ?_ ?_
    · rw [← toAntisymmetrization_one,
        ← (toAntisymmetrization_eq _ _ _).2 (antisymmRel_push_one (K := K) ι)] at hw
      simpa only [F.map_one] using hlow 1 w hw
    · rintro s t _ ⟨κ, _, b, hb, rfl⟩ _ ⟨κ', _, b', hb', rfl⟩
      refine ⟨Σ _ : κ, κ', inferInstance, _, (tensorCovering K I').mul_mul hb hb', ?_⟩
      rw [Fintype.sum_sigma, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        (hcongr (antisymmRel_ofAntisymmetrization_mul _ _)).trans (fmul _ _)
    · intro κ _ t b hb w hw
      choose μ _ c hc hw using hw
      refine ⟨_, ⟨Σ k, μ k, inferInstance, _, (tensorCovering K I').bind hb hc, rfl⟩, ?_⟩
      rw [Fintype.sum_sigma]
      exact (Finset.sum_congr rfl fun k _ => hw k).le
  have Pf (t) : UpperFunctional.ofIsUpperFunctional hpre t ≤ f t := by
    rw [UpperFunctional.ofIsUpperFunctional_apply]
    exact csInf_le ⟨0, h0 _⟩ (hup t)
  refine ⟨UpperFunctional.ofIsUpperFunctional hpre, Pf, fun A => le_antisymm
    ((Pf _).trans (extendProduct_push ι π hπ θ hθ1 F A).le) ?_⟩
  rw [UpperFunctional.ofIsUpperFunctional_apply]
  exact le_csInf (hne _) (hlow A)

/-- Localization: with `c = φ(C)` and `p(ιCⁿ) = cⁿ`, the function `q(t) = inf p(t ιCⁿ)/cⁿ` is an
upper functional below `p` that respects `(1, ιC, 1/c)`. Stated for any upper functional `p` and
tensor `f` with `p f > 0` and `p (f ^ n) = p f ^ n`. -/
private theorem exists_localize (p : UpperFunctional K I) (f : PartyTensor K I) (hf : 0 < p f)
    (hpow : ∀ n, p (f ^ n) = p f ^ n) :
    ∃ q : UpperFunctional K I, (∀ t, q t ≤ p t) ∧ ∀ t, q (t * 1) ≤ (p f)⁻¹ * q (t * f) := by
  obtain ⟨q, hq, hle, hk, -⟩ := p.isUpperFunctional_lift.exists_localize
    (f := toAntisymmetrization (· ≤ ·) f) (by simpa using hf)
    (fun n => by rw [← toAntisymmetrization_pow, UpperFunctional.lift_toAntisymmetrization,
      UpperFunctional.lift_toAntisymmetrization, hpow])
  refine ⟨UpperFunctional.ofIsUpperFunctional hq, fun t => ?_, fun t => ?_⟩
  · rw [UpperFunctional.ofIsUpperFunctional_apply]
    exact (hle _).trans (UpperFunctional.lift_toAntisymmetrization p t).le
  · simpa only [UpperFunctional.ofIsUpperFunctional_apply, toAntisymmetrization_mul,
      toAntisymmetrization_one, UpperFunctional.lift_toAntisymmetrization] using
      hk (toAntisymmetrization (· ≤ ·) t)

/-- **Paper: Proposition A.7 (prop:extend).** Let `ι : I → I'` and `π l : I' → I` be maps with
`π l ∘ ι = id`, let `θ l ≥ 0` add up to `1`, let `F` be a spectral point on `I` and `C` a tensor on
`I`. Then some spectral point `F'` on `I'` satisfies `F' t ≤ ∏ l, F (π l t) ^ θ l` for all `t`, and
`F' (ι C) = F C`. The maps are indexed by any finite type `L`. -/
theorem exists_extend (ι : I → I') (π : L → I' → I) (hπ : ∀ l i, π l (ι i) = i) (θ : L → ℝ)
    (hθ : ∀ l, 0 ≤ θ l) (hθ1 : ∑ l, θ l = 1) (F : SpectralPoint K I) (C : PartyTensor K I) :
    ∃ F' : SpectralPoint K I', (∀ t, F' t ≤ ∏ l, F (push (π l) t) ^ θ l) ∧
      F' (push ι C) = F C := by
  obtain ⟨p, pf, pA⟩ := exists_upperFunctional_extend ι π hπ θ hθ hθ1 F
  rcases (F.nonneg C).eq_or_lt with hC | hC
  · -- `F C = 0` (the printed case `C = 0`)
    obtain ⟨F', hF', -⟩ := p.exists_spectralPoint_le
    exact ⟨F', fun t => (hF' t).trans (pf t),
      le_antisymm ((hF' _).trans (pA C).le) (by rw [← hC]; exact F'.nonneg _)⟩
  · obtain ⟨q, hq, hqk⟩ := exists_localize p (push ι C) (by rwa [pA]) (fun n => by
      rw [← p.congr (antisymmRel_push_pow ι C n), pA, pA, F.map_pow])
    -- a spectral point `F' ≤ q` that respects this triple has `c ≤ F' (ι C) ≤ f (ι C) = c`
    obtain ⟨F', hF', hk⟩ := q.exists_spectralPoint_le
    refine ⟨F', fun t => (hF' t).trans ((hq t).trans (pf t)),
      le_antisymm ((hF' _).trans ((hq _).trans (pA C).le)) ?_⟩
    have h1 := hk 1 (push ι C) _ (by rw [pA]; positivity) hqk 1
    rw [F'.congr (antisymmRel_one_mul _), F'.congr (antisymmRel_one_mul _), F'.map_one, pA,
      inv_mul_eq_div, le_div_iff₀ hC, one_mul] at h1
    exact h1

end SpectralPoint

end Cslib.PartyTensor
