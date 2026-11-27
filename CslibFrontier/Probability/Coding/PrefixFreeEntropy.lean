/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.Entropy
public import Mathlib.InformationTheory.Coding.PrefixFree
import CslibFrontier.Probability.Divergence
import CslibFrontier.Probability.MinEntropy
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import Mathlib.InformationTheory.Coding.Kraft

/-!
# Kraft–Gibbs Compression Bounds for Shannon Entropy

This module connects Mathlib's `InformationTheory.IsPrefixFree` and Kraft inequality
(`Mathlib/InformationTheory/Coding/Kraft.lean`) to finite-distribution Shannon entropy and
conditional entropy (`CslibFrontier/Probability/Entropy.lean`,
`CslibFrontier/Probability/Divergence.lean`). Deterministic prefix-free concatenation combinators
and
basic binary codes (`finIdxBits`, `eliasGamma`) live in
`CslibFrontier/Foundations/Data/BitString/List/PrefixFree.lean`.

## Main results

* `Cslib.Probability.Coding.entropy_le_expected_length_of_isPrefixFree`: for any finite `p : PMF α`
  and prefix-free encoding `enc` injective on `p.support`, `entropy p` is at most the expected
  codeword length under `p` ([CoverThomas2006], Theorem 5.3.1).
* `Cslib.Probability.Coding.conditionalEntropy_le_expected_length_of_isPrefixFree`: fiberwise
  Kraft–Gibbs lower bound for `conditionalEntropy joint`.
* `Cslib.Probability.Coding.conditionalEntropy_map_le_expected_length_of_isPrefixFree`: transcript
  compression form bounding `H(target(ω) | obs(ω))` by expected message length `E[|msg(ω)|]`.
* `Cslib.Probability.Coding.logb_prob_add_logb_card_le_conditionalEntropy`,
  `Cslib.Probability.Coding.logb_prob_add_logb_le_conditionalEntropy_of_fiber_le`,
  `Cslib.Probability.Coding.logb_le_conditionalEntropy_of_fiber_le`: lower bounds on conditional
  entropy `H(target | obs)` (conditioned on an event `W` or unconditioned) from joint or fiberwise
  point-mass upper bounds.

## References

* [T. M. Cover, J. A. Thomas, *Elements of Information Theory*][CoverThomas2006], Section 5.2 and
  Theorem 5.3.1.
* [L. G. Kraft, *A Device for Quantizing, Grouping, and Coding Amplitude-Modulated
  Pulses*][Kraft1949].
-/

public section

open scoped BigOperators ENNReal

namespace Cslib.Probability.Coding

open InformationTheory Cslib.Probability.PMF

/-- **Kraft–Gibbs source coding lower bound** ([CoverThomas2006], Theorem 5.3.1): if `enc` is
injective on `p.support` and its image on `p.support` is prefix-free, then `entropy p` is at most
the expected codeword length under `p`. -/
theorem entropy_le_expected_length_of_isPrefixFree {α : Type*} [Fintype α]
    (p : PMF α) (enc : α → List Bool)
    (hinj : Set.InjOn enc p.support)
    (hpf : IsPrefixFree (enc '' p.support)) :
    entropy p ≤ ∑ a, (p a).toReal * ((enc a).length : ℝ) := by
  classical
  let s : Finset α := Finset.univ.filter fun a => a ∈ p.support
  have hs_mem (a : α) : a ∈ s ↔ a ∈ p.support := by simp [s]
  have hs_coe : (s : Set α) = p.support := Set.ext hs_mem
  obtain ⟨a₀, ha₀⟩ := p.support_nonempty
  set Z : ℝ := ∑ a ∈ s, (2⁻¹ : ℝ) ^ (enc a).length
  have hZ_le : Z ≤ 1 := by
    have hS_pf : IsPrefixFree ((s.image enc : Finset (List Bool)) : Set (List Bool)) := by
      simpa only [Finset.coe_image, hs_coe] using hpf
    simpa only [Z, Fintype.card_bool, Nat.cast_ofNat, one_div,
      Finset.sum_image (hs_coe.symm ▸ hinj)] using hS_pf.finsetSum_one_div_card_pow_length_le_one
  have hZ_pos : 0 < Z :=
    Finset.sum_pos (fun a _ => by positivity) ⟨a₀, (hs_mem a₀).mpr ha₀⟩
  let f : α → ℝ≥0∞ := fun a =>
    if a ∈ s then ENNReal.ofReal ((2⁻¹ : ℝ) ^ (enc a).length / Z) else 0
  have hf_sum : ∑ a, f a = 1 := by
    simp only [f, Finset.sum_ite_mem, Finset.univ_inter]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => by positivity), ← Finset.sum_div,
      div_self hZ_pos.ne', ENNReal.ofReal_one]
  let q : PMF α := PMF.ofFintype f hf_sum
  have hq_toReal (a : α) (ha : a ∈ p.support) :
      (q a).toReal = (2⁻¹ : ℝ) ^ (enc a).length / Z := by
    simp only [q, PMF.ofFintype_apply, f, ite_eq_left ((hs_mem a).mpr ha)]
    exact ENNReal.toReal_ofReal (by positivity)
  have hmass_ge (a : α) (ha : a ∈ p.support) :
      (2 : ℝ) ^ (-((enc a).length : ℝ)) ≤ (q a).toReal := by
    rw [hq_toReal a ha, Real.rpow_neg (by norm_num), Real.rpow_natCast, ← inv_pow]
    exact le_div_self (by positivity) hZ_pos hZ_le
  have hsupp : p.support ⊆ q.support := fun a ha => (PMF.mem_support_iff q a).mpr fun h0 =>
    not_le.mpr (by simp [h0]) (hmass_ge a ha)
  refine (entropy_le_sum_mul_surprisal hsupp).trans (Finset.sum_le_sum fun a _ => ?_)
  by_cases ha : a ∈ p.support
  · exact mul_le_mul_of_nonneg_left (surprisal_le_of_mass_ge q a (hmass_ge a ha))
      ENNReal.toReal_nonneg
  · simp [(PMF.apply_eq_zero_iff p a).mpr ha]

/-- **Conditional Kraft–Gibbs compression bound**: if for each observable `obs`, `enc obs` is
injective on `(conditionalSnd joint obs).support` with prefix-free image, then
`conditionalEntropy joint` is at most the expected codeword length under `joint`. -/
theorem conditionalEntropy_le_expected_length_of_isPrefixFree {Obs α : Type*}
    [Fintype Obs] [Fintype α]
    (joint : PMF (Obs × α)) (enc : Obs → α → List Bool)
    (hinj : ∀ obs ∈ (joint.map Prod.fst).support,
      Set.InjOn (enc obs) (conditionalSnd joint obs).support)
    (hpf : ∀ obs ∈ (joint.map Prod.fst).support,
      IsPrefixFree (enc obs '' (conditionalSnd joint obs).support)) :
    conditionalEntropy joint ≤ ∑ oa, (joint oa).toReal * ((enc oa.1 oa.2).length : ℝ) := by
  rw [conditionalEntropy_eq_sum, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun obs _ => ?_
  by_cases hobs : obs ∈ (joint.map Prod.fst).support
  · have hbound := entropy_le_expected_length_of_isPrefixFree (conditionalSnd joint obs)
      (enc obs) (hinj obs hobs) (hpf obs hobs)
    calc ((joint.map Prod.fst) obs).toReal * entropy (conditionalSnd joint obs)
        ≤ ((joint.map Prod.fst) obs).toReal *
            ∑ a, (conditionalSnd joint obs a).toReal * ((enc obs a).length : ℝ) := by gcongr
      _ = ∑ a, (joint (obs, a)).toReal * ((enc obs a).length : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← mul_assoc, ← ENNReal.toReal_mul, marginal_mul_conditionalSnd]
  · have hm0 : (joint.map Prod.fst) obs = 0 := (PMF.apply_eq_zero_iff _ _).mpr hobs
    simp [hm0, fun a => le_antisymm (hm0 ▸ apply_le_map_fst joint obs a) bot_le]

/-- **Communication transcript compression bound**: if a message `msg ω` sent over an outcome space
`p : PMF Ω` is prefix-free on each observation fiber `{ω ∈ p.support | obs ω = o}` and uniquely
determines `target ω` given `obs ω` on `p.support`, then `H(target(ω) | obs(ω)) ≤ E[|msg(ω)|]`. -/
theorem conditionalEntropy_map_le_expected_length_of_isPrefixFree {Ω Obs α : Type*}
    [Fintype Ω] [Finite Obs] [Finite α]
    (p : PMF Ω) (obs : Ω → Obs) (target : Ω → α) (msg : Ω → List Bool)
    (hpf : ∀ o : Obs, IsPrefixFree (msg '' {ω ∈ p.support | obs ω = o}))
    (hdec : ∀ ω₁ ∈ p.support, ∀ ω₂ ∈ p.support,
      obs ω₁ = obs ω₂ → msg ω₁ = msg ω₂ → target ω₁ = target ω₂) :
    conditionalEntropy (p.map fun ω => (obs ω, target ω)) ≤
      ∑ ω, (p ω).toReal * ((msg ω).length : ℝ) := by
  classical
  let := Fintype.ofFinite Obs
  let := Fintype.ofFinite α
  let W : Finset (List Bool) := Finset.univ.image msg
  let cw : Ω → {w // w ∈ W} := fun ω => ⟨msg ω, Finset.mem_image_of_mem msg (Finset.mem_univ ω)⟩
  let joint_cw : PMF (Obs × {w // w ∈ W}) := p.map fun ω => (obs ω, cw ω)
  let joint_tgt : PMF (Obs × α) := p.map fun ω => (obs ω, target ω)
  obtain ⟨ω_def, _⟩ := p.support_nonempty
  let dec : Obs × {w // w ∈ W} → Obs × α := fun oc =>
    if h : ∃ ω ∈ p.support, obs ω = oc.1 ∧ cw ω = oc.2 then
      (oc.1, target (Classical.choose h))
    else
      (oc.1, target ω_def)
  have hmap_dec : joint_cw.map dec = joint_tgt := by
    rw [PMF.map_comp]
    refine Cslib.Probability.PMF.map_congr_on_support p _ _ fun ω hω => ?_
    have hex : ∃ ω' ∈ p.support, obs ω' = obs ω ∧ cw ω' = cw ω := ⟨ω, hω, rfl, rfl⟩
    obtain ⟨hω', hobs', hcw'⟩ := Classical.choose_spec hex
    simp only [Function.comp_apply, dec, dite_eq_left hex]
    exact Prod.ext rfl (hdec (Classical.choose hex) hω' ω hω hobs' (congrArg Subtype.val hcw'))
  have hent_le : conditionalEntropy joint_tgt ≤ conditionalEntropy joint_cw := by
    have hm_fst : joint_tgt.map Prod.fst = joint_cw.map Prod.fst := by
      simp only [joint_tgt, joint_cw, PMF.map_comp, Function.comp_def]
    rw [conditionalEntropy, conditionalEntropy, hm_fst, ← hmap_dec]
    exact sub_le_sub_right (entropy_map_le joint_cw dec) _
  have hcw_pf : ∀ o ∈ (joint_cw.map Prod.fst).support,
      IsPrefixFree (Subtype.val '' (conditionalSnd joint_cw o).support) := by
    intro o ho
    refine (hpf o).anti ?_
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨ω, hω, hpair⟩ := (PMF.mem_support_map_iff _ _ _).mp
      ((mem_support_conditionalSnd_iff joint_cw o ho c).mp hc)
    rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
    exact ⟨ω, ⟨hω, rfl⟩, rfl⟩
  exact hent_le.trans ((conditionalEntropy_le_expected_length_of_isPrefixFree joint_cw
    (fun _ c => c.val) (fun _ _ => Subtype.val_injective.injOn) hcw_pf).trans_eq
    (sum_map_mul p (fun ω => (obs ω, cw ω)) fun oc => ((oc.2.val).length : ℝ)))

/-- Conditioning `μ` on `{W = true}` scales any pushforward point mass by at most `Pr[W]⁻¹`. -/
private theorem toReal_map_conditionalSnd_event_le {Ω α : Type*}
    (μ : PMF Ω) (W : Ω → Bool) (hW0 : (μ.map W) true ≠ 0) (f : Ω → α) (x : α) :
    (((conditionalSnd (μ.map fun ω => (W ω, ω)) true).map f) x).toReal ≤
      (((μ.map W) true).toReal)⁻¹ * ((μ.map f) x).toReal := by
  let joint := μ.map fun ω => (W ω, ω)
  let p := conditionalSnd joint true
  have hfst : joint.map Prod.fst = μ.map W := _root_.PMF.map_comp _ _ _
  have hsnd : joint.map Prod.snd = μ := (_root_.PMF.map_comp _ _ _).trans (_root_.PMF.map_id μ)
  have hWt := PMF.apply_ne_top (μ.map W) true
  have hscale (ω : Ω) : p ω ≤ ((μ.map W) true)⁻¹ * μ ω := by
    rw [mul_comm, ← div_eq_mul_inv,
      ENNReal.le_div_iff_mul_le (Or.inl hW0) (Or.inl hWt),
      mul_comm, ← hfst, marginal_mul_conditionalSnd, ← hsnd]
    exact le_map_apply joint Prod.snd (true, ω)
  rw [← ENNReal.toReal_inv, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hW0) (PMF.apply_ne_top _ _))
    (map_apply_le_mul hscale f x)

open Classical in
/-- Lower bound on conditional entropy under an event `W` of conditional probability
`(μ.map W) true`, when the prior joint distribution on `(obs, target)` has point masses
bounded by `1 / |ObsT × TgtT|`. -/
theorem logb_prob_add_logb_card_le_conditionalEntropy {Ω ObsT TgtT : Type*}
    [Finite Ω] [Fintype ObsT] [Fintype TgtT] [Nonempty ObsT] [Nonempty TgtT]
    (μ : PMF Ω) (W : Ω → Bool) (obs : Ω → ObsT) (target : Ω → TgtT) (hW0 : (μ.map W) true ≠ 0)
    (hmass : ∀ ot : ObsT × TgtT,
      ((μ.map fun ω => (obs ω, target ω)) ot).toReal ≤ (Fintype.card (ObsT × TgtT) : ℝ)⁻¹) :
    let p := PMF.conditionalSnd (μ.map fun ω => (W ω, ω)) true
    Real.logb 2 (((μ.map W) true).toReal) + Real.logb 2 (Fintype.card TgtT) ≤
      PMF.conditionalEntropy (p.map fun ω => (obs ω, target ω)) := by
  let _ := Fintype.ofFinite Ω
  dsimp only
  set p : PMF Ω := PMF.conditionalSnd (μ.map fun ω => (W ω, ω)) true
  set joint_ot : PMF (ObsT × TgtT) := p.map fun ω => (obs ω, target ω)
  set pW_real : ℝ := ((μ.map W) true).toReal
  have hpW_pos : 0 < pW_real := ENNReal.toReal_pos hW0 (PMF.apply_ne_top (μ.map W) true)
  have hcObs : (0 : ℝ) < (Fintype.card ObsT : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hcTgt : (0 : ℝ) < (Fintype.card TgtT : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hcard_ot : (Fintype.card ObsT : ℝ) * (Fintype.card TgtT : ℝ) =
      (Fintype.card (ObsT × TgtT) : ℝ) := by exact_mod_cast (Fintype.card_prod ObsT TgtT).symm
  have hmin : Real.logb 2 (pW_real * (Fintype.card ObsT : ℝ) * (Fintype.card TgtT : ℝ)) ≤
      PMF.entropy joint_ot := by
    refine le_trans ?_ (PMF.minEntropy_le_entropy joint_ot)
    rw [PMF.le_minEntropy_iff joint_ot]; intro ot
    rw [Real.rpow_neg (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by positivity),
      mul_assoc pW_real, hcard_ot, mul_inv]
    exact (toReal_map_conditionalSnd_event_le μ W hW0 _ ot).trans
      (mul_le_mul_of_nonneg_left (hmass ot) (inv_nonneg.mpr hpW_pos.le))
  rw [Real.logb_mul (mul_pos hpW_pos hcObs).ne' hcTgt.ne',
    Real.logb_mul hpW_pos.ne' hcObs.ne'] at hmin
  rw [PMF.conditionalEntropy]
  linarith [PMF.entropy_le_log_card (joint_ot.map Prod.fst)]

open Classical in
/-- Fiberwise event-conditioned conditional entropy lower bound: if under prior `μ : PMF Ω`, every
observation-target pair `(o, t)` has joint probability at most `((μ.map obs) o).toReal / M`, then
conditioning on any event `W` with `(μ.map W) true ≠ 0` leaves at least `log₂ Pr[W] + log₂ M` bits
of conditional entropy `H_p(target | obs)` (by fiberwise min-entropy plus non-negativity of KL
divergence `D(P(obs | W) ‖ P(obs)) ≥ 0`). -/
theorem logb_prob_add_logb_le_conditionalEntropy_of_fiber_le {Ω ObsT TgtT : Type*}
    [Finite Ω] [Finite ObsT] [Finite TgtT]
    (μ : PMF Ω) (W : Ω → Bool) (obs : Ω → ObsT) (target : Ω → TgtT) {M : ℝ} (hM : 0 < M)
    (hW0 : (μ.map W) true ≠ 0)
    (hfiber : ∀ (o : ObsT) (t : TgtT),
      ((μ.map fun ω => (obs ω, target ω)) (o, t)).toReal ≤ ((μ.map obs) o).toReal / M) :
    let p := PMF.conditionalSnd (μ.map fun ω => (W ω, ω)) true
    Real.logb 2 (((μ.map W) true).toReal) + Real.logb 2 M ≤
      PMF.conditionalEntropy (p.map fun ω => (obs ω, target ω)) := by
  let _ := Fintype.ofFinite Ω
  let _ := Fintype.ofFinite ObsT
  let _ := Fintype.ofFinite TgtT
  dsimp only
  set p : PMF Ω := PMF.conditionalSnd (μ.map fun ω => (W ω, ω)) true
  set J : PMF (ObsT × TgtT) := p.map fun ω => (obs ω, target ω)
  set r : PMF ObsT := J.map Prod.fst
  set q : PMF ObsT := μ.map obs
  set pW : ℝ := ((μ.map W) true).toReal
  have hpW_pos : 0 < pW := ENNReal.toReal_pos hW0 (PMF.apply_ne_top (μ.map W) true)
  have hr_le (o : ObsT) : (r o).toReal ≤ pW⁻¹ * (q o).toReal := by
    simpa only [r, J, _root_.PMF.map_comp, Function.comp_def] using
      toReal_map_conditionalSnd_event_le μ W hW0 obs o
  have hsupp : r.support ⊆ q.support := fun o ho =>
    (_root_.PMF.mem_support_iff _ _).mpr fun h0 =>
      (ENNReal.toReal_pos ((_root_.PMF.mem_support_iff _ _).mp ho)
        (PMF.apply_ne_top r o)).not_ge (by simpa [h0] using hr_le o)
  have hterm (o : ObsT) :
      (r o).toReal * (Real.logb 2 pW + Real.logb 2 M) -
        (r o).toReal * PMF.surprisal r o + (r o).toReal * PMF.surprisal q o ≤
      (r o).toReal * PMF.entropy (PMF.conditionalSnd J o) := by
    by_cases ho : o ∈ r.support
    · have hro : 0 < (r o).toReal := ENNReal.toReal_pos ((_root_.PMF.mem_support_iff _ _).mp ho)
        (PMF.apply_ne_top r o)
      have hqo : 0 < (q o).toReal := ENNReal.toReal_pos
        ((_root_.PMF.mem_support_iff _ _).mp (hsupp ho)) (PMF.apply_ne_top q o)
      have hmin : Real.logb 2 (pW * (r o).toReal * M / (q o).toReal) ≤
          PMF.entropy (PMF.conditionalSnd J o) := by
        refine le_trans ?_ (PMF.minEntropy_le_entropy _)
        rw [PMF.le_minEntropy_iff]; intro t
        rw [Real.rpow_neg (by norm_num),
          Real.rpow_logb (by norm_num) (by norm_num) (by positivity), inv_div]
        have hm : (r o).toReal * (PMF.conditionalSnd J o t).toReal = (J (o, t)).toReal :=
          (ENNReal.toReal_mul ..).symm.trans (congrArg _ (PMF.marginal_mul_conditionalSnd J o t))
        rw [le_div_iff₀ (by positivity)]
        calc (PMF.conditionalSnd J o t).toReal * (pW * (r o).toReal * M)
            = (J (o, t)).toReal * (pW * M) := by rw [← hm]; ring
          _ ≤ pW⁻¹ * ((q o).toReal / M) * (pW * M) :=
            mul_le_mul_of_nonneg_right ((toReal_map_conditionalSnd_event_le μ W hW0 _ (o, t)).trans
              (mul_le_mul_of_nonneg_left (hfiber o t) (inv_nonneg.mpr hpW_pos.le))) (by positivity)
          _ = (q o).toReal := by field_simp
      have hlog : Real.logb 2 (pW * (r o).toReal * M / (q o).toReal) =
          Real.logb 2 pW + Real.logb 2 M - PMF.surprisal r o + PMF.surprisal q o := by
        rw [Real.logb_div (mul_pos (mul_pos hpW_pos hro) hM).ne' hqo.ne',
          Real.logb_mul (mul_pos hpW_pos hro).ne' hM.ne', Real.logb_mul hpW_pos.ne' hro.ne']
        dsimp only [PMF.surprisal]; ring
      linarith [mul_le_mul_of_nonneg_left (hlog ▸ hmin) hro.le]
    · simp [(_root_.PMF.apply_eq_zero_iff r o).mpr ho]
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun (o : ObsT) _ => hterm o
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    PMF.sum_toReal r, one_mul, ← PMF.entropy_eq_sum_surprisal r] at hsum
  change Real.logb 2 pW + Real.logb 2 M ≤ PMF.conditionalEntropy J
  linarith [PMF.entropy_le_sum_mul_surprisal hsupp, PMF.conditionalEntropy_eq_sum J]

/-- Unconditioned specialization of `logb_prob_add_logb_le_conditionalEntropy_of_fiber_le`: if
`((μ.map fun ω => (obs ω, target ω)) (o, t)).toReal ≤ ((μ.map obs) o).toReal / M` for all `(o, t)`,
then `Real.logb 2 M ≤ PMF.conditionalEntropy (μ.map fun ω => (obs ω, target ω))`. -/
theorem logb_le_conditionalEntropy_of_fiber_le {Ω ObsT TgtT : Type*}
    [Finite Ω] [Finite ObsT] [Finite TgtT]
    (μ : PMF Ω) (obs : Ω → ObsT) (target : Ω → TgtT) {M : ℝ} (hM : 0 < M)
    (hfiber : ∀ (o : ObsT) (t : TgtT),
      ((μ.map fun ω => (obs ω, target ω)) (o, t)).toReal ≤ ((μ.map obs) o).toReal / M) :
    Real.logb 2 M ≤ PMF.conditionalEntropy (μ.map fun ω => (obs ω, target ω)) := by
  classical
  have htrue : (μ.map fun _ => true) true = 1 := by simp
  have hcond : PMF.conditionalSnd (μ.map fun ω => (true, ω)) true = μ := by
    ext ω
    simpa [_root_.PMF.map_comp, Function.comp_def, htrue] using
      (PMF.marginal_mul_conditionalSnd (μ.map fun ω => (true, ω)) true ω).trans
        (PMF.map_apply_of_injective μ (fun _ _ h => congrArg Prod.snd h) ω)
  simpa only [htrue, ENNReal.toReal_one, Real.logb_one, zero_add, hcond] using
    logb_prob_add_logb_le_conditionalEntropy_of_fiber_le μ (fun _ => true) obs target hM
      (htrue ▸ one_ne_zero) hfiber

end Cslib.Probability.Coding
