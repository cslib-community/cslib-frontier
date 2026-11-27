/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.FPAUS
public import CslibFrontier.Computability.Complexity.Classes.FPAUS.SelfReducible
public import CslibFrontier.Computability.Probabilistic.Retry
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Probability.Option
import CslibFrontier.Tactic.ENNRealToReal

/-!
# Precision and failure in almost uniform generation

A supported sampler with small total-variation error gives the pointwise guarantees of Jerrum,
Valiant and Vazirani [JerrumValiantVazirani1986, §6] by asking for one additional precision bit
per witness bit. Conversely, retrying a JVV generator reduces the failure probability while
preserving the ratios between witness probabilities.
-/

public section

namespace Cslib.Complexity

open Cslib.Probability Turing.MultiTapeTM
open scoped ENNReal

variable {α : Type} {enc : α ↪ List Bool} {W : α → Finset (List Bool)}
  {S : α → ℕ → ProbComp (Option (List Bool))}

/-- Ask a total-variation sampler for enough precision to resolve the mass of each witness. -/
def SelfReducible.atWitnessPrecision (R : SelfReducible enc W)
    (S : α → ℕ → ProbComp (Option (List Bool))) (x : α) (q : ℕ) : ProbComp (Option (List Bool)) :=
  S x (q + 2 + R.len x)

/-- A supported sampler with dyadic total-variation error gives the JVV guarantee at increased
precision. There are at most `2 ^ R.len x` witnesses, and the common reference mass is the
reciprocal of their number. -/
theorem SelfReducible.isFPAUS_atWitnessPrecision (R : SelfReducible enc W)
    (hppt : IsPPTOn (encPair enc encUnary) (encOption encBits) (Function.uncurry S))
    (hvalid : ∀ x q w, w ∉ W x → ProbComp.eval (S x q) (some w) = 0)
    (hclose : ∀ x q, CloseTo (ProbComp.eval (S x q)) (uniformWitness (W x))
      (ENNReal.ofReal ((1 / 2 : ℝ) ^ q))) :
    IsFPAUS enc W (R.atWitnessPrecision S) := by
  have hδ (q : ℕ) : (1 / 2 : ℝ) ^ (q + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  refine ⟨?_, fun x q => hvalid x _, ?_, ?_⟩
  · have hlen := R.len_polytime.comp (ComputableInPolyTime.fst enc encUnary)
    have h : ComputableInPolyTime (fun a : α × ℕ => (a.1, a.2 + 2 + R.len a.1))
        (encPair enc encUnary) (encPair enc encUnary) := by fun_prop
    exact hppt.preprocess h
  · intro x q hW
    have h := (hclose x (q + 2 + R.len x)).abs_toReal_sub_le (by positivity) {none}
    rw [PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_apply_singleton,
      uniformWitness_none hW] at h
    simp only [ENNReal.toReal_zero, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at h
    exact h.trans ((pow_le_pow_of_le_one (by norm_num) (by norm_num) (by lia)).trans_eq (pow_one _))
  · intro x
    rcases (W x).eq_empty_or_nonempty with hW | hW
    · exact ⟨1, by simp, fun q w hw => by simp [hW] at hw⟩
    have hN : (0 : ℝ) < (W x).card := by exact_mod_cast Finset.card_pos.mpr hW
    have h1 : (1 : ℝ) ≤ (W x).card := by exact_mod_cast Finset.card_pos.mpr hW
    refine ⟨1 / (W x).card, ⟨by positivity, (div_le_one hN).2 h1⟩, ?_⟩
    intro q w hw
    have h := (hclose x (q + 2 + R.len x)).abs_toReal_sub_le (by positivity) {some w}
    rw [PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_apply_singleton,
      uniformWitness_some_toReal, ite_eq_left hw, abs_le] at h
    have hscale : (1 / 2 : ℝ) ^ (R.len x) ≤ 1 / (W x).card := by
      rw [div_pow, one_pow]
      exact one_div_le_one_div_of_le hN (by exact_mod_cast R.card_le_two_pow_len x)
    set ε := (1 / 2 : ℝ) ^ (q + 1)
    have he : 0 ≤ ε := by positivity
    have he1 : ε ≤ 1 := hδ q
    have herr : (1 / 2 : ℝ) ^ (q + 2 + R.len x) ≤ ε * (1 / (W x).card) / 2 := by
      rw [pow_add, show q + 2 = q + 1 + 1 from rfl, pow_succ]
      change ε * (1 / 2) * _ ≤ _
      calc _ ≤ (ε * (1 / 2)) * (1 / (W x).card) := by gcongr
        _ = _ := by ring
    change 1 / _ / (1 + ε) ≤ _ ∧ _ ≤ (1 + ε) * (1 / _)
    dsimp only [SelfReducible.atWitnessPrecision]
    constructor
    · apply (div_le_iff₀ (by positivity)).2
      have hp : 0 ≤ 1 / ((W x).card : ℝ) := by positivity
      nlinarith [mul_nonneg (sub_nonneg.mpr he1) (mul_nonneg he hp),
        mul_le_mul_of_nonneg_right (show 1 / ((W x).card : ℝ) - ε * (1 / (W x).card) / 2 ≤
          (ProbComp.eval (S x (q + 2 + R.len x)) (some w)).toReal by linarith)
          (show 0 ≤ 1 + ε by positivity)]
    · have hp : 0 ≤ ε * (1 / ((W x).card : ℝ)) := by positivity
      linarith [h.2]

/-- Retry a JVV generator to approximate the unconditional uniform law used by the counting
estimator. Each run uses two extra precision bits, and at most `q + 2` independent runs are
needed. -/
@[expose] def retrySampler (S : α → ℕ → ProbComp (Option (List Bool))) (x : α) (q : ℕ) :
    ProbComp (Option (List Bool)) :=
  Option.join <$> OracleComp.retry (fun o : Option (List Bool) => o.isSome) (S x (q + 2)) (q + 2)

private theorem retrySampler_masses (S : α → ℕ → ProbComp (Option (List Bool))) (x : α) (q : ℕ) :
    let p := ProbComp.eval (S x (q + 2))
    let μ := ProbComp.eval (retrySampler S x q)
    μ none = p none ^ (q + 2) ∧
      ∀ w, μ (some w) = p (some w) * ∑ i ∈ Finset.range (q + 2), p none ^ i := by
  let p := ProbComp.eval (S x (q + 2))
  let r := ProbComp.eval
    (OracleComp.retry (fun o : Option (List Bool) => o.isSome) (S x (q + 2)) (q + 2))
  have hbad : p.toOuterMeasure {o | ¬ o.isSome = true} = p none := by
    have heq : {o : Option (List Bool) | ¬ o.isSome = true} = {none} := by
      ext (_ | o) <;> simp
    rw [heq, PMF.toOuterMeasure_apply_singleton]
  have hnone : r none = p none ^ (q + 2) := by
    dsimp only [r, p] at *
    rw [ProbComp.eval_eq_evalWith, OracleComp.evalWith_retry_none,
      ← ProbComp.eval_eq_evalWith, hbad]
  have hsome (o : Option (List Bool)) : r (some o) =
      (if o.isSome then p o else 0) * ∑ i ∈ Finset.range (q + 2), p none ^ i := by
    dsimp only [r, p] at *
    rw [ProbComp.eval_eq_evalWith, OracleComp.evalWith_retry_some,
      ← ProbComp.eval_eq_evalWith, hbad]
  dsimp only [retrySampler]
  rw [ProbComp.eval_map]
  change (r.map Option.join) none = _ ∧ ∀ w, (r.map Option.join) (some w) = _
  constructor
  · rw [PMF.map_apply, tsum_eq_single none]
    · simpa using hnone
    · rintro (_ | _ | w) h <;> simp [hsome] at *
  · intro w
    rw [PMF.map_apply, tsum_eq_single (some (some w))]
    · simpa using hsome (some w)
    · rintro (_ | _ | v) hv
      · simp
      · simp
      · simp [show w ≠ v from fun e => hv (by simp [e])]

/-- Retrying turns JVV's per-witness relative accuracy and bounded failure into an additive
total-variation guarantee. -/
theorem IsFPAUS.closeTo_retrySampler (hS : IsFPAUS enc W S) (x : α) (q : ℕ) :
    CloseTo (ProbComp.eval (retrySampler S x q)) (uniformWitness (W x))
      (ENNReal.ofReal ((1 / 2 : ℝ) ^ q)) := by
  let μ := ProbComp.eval (retrySampler S x q)
  let p := ProbComp.eval (S x (q + 2))
  obtain ⟨hnone, hsome⟩ := retrySampler_masses S x q
  have hvalid (w : List Bool) (hw : w ∉ W x) : μ (some w) = 0 := by
    rw [hsome, hS.valid _ _ _ hw, zero_mul]
  refine closeTo_uniformWitness_of_le (by positivity) (fun w hw => ?_)
    (fun hW w => hvalid w (by simp [hW]))
  have hW : (W x).Nonempty := ⟨w, hw⟩
  have hN : (0 : ℝ) < (W x).card := by exact_mod_cast Finset.card_pos.mpr hW
  have hfail := hS.failure x (q + 2) hW
  set ε := (1 / 2 : ℝ) ^ q
  have he : 0 ≤ ε := by positivity
  have hf : (μ none).toReal ≤ ε / 4 := by
    rw [hnone]
    ennreal_to_real
    calc _ ≤ (1 / 2 : ℝ) ^ (q + 2) := by gcongr
      _ = _ := by rw [pow_add]; ring
  obtain ⟨φ, -, hφ⟩ := hS.pointwise x
  let K := ∑ i ∈ Finset.range (q + 2), (p none).toReal ^ i
  have hK : 0 ≤ K := Finset.sum_nonneg fun _ _ => pow_nonneg ENNReal.toReal_nonneg _
  have hm (v : List Bool) : (μ (some v)).toReal = (p (some v)).toReal * K := by
    dsimp only [K]
    ennreal_to_real using hsome v
  have hε' : (1 / 2 : ℝ) ^ (q + 2 + 1) = ε / 8 := by rw [pow_add, pow_add]; ring
  have hp (v : List Bool) (hv : v ∈ W x) := hφ (q + 2) v hv
  have hl := (hp w hw).1
  rw [hε', div_le_iff₀ (by positivity)] at hl
  have hbound (v : List Bool) (hv : v ∈ W x) :
      (μ (some v)).toReal ≤ (μ (some w)).toReal * (1 + ε / 8) ^ 2 := by
    have hu := (hp v hv).2
    rw [hε'] at hu
    rw [hm, hm]
    calc (p (some v)).toReal * K ≤ ((1 + ε / 8) * ((p (some w)).toReal * (1 + ε / 8))) * K :=
          mul_le_mul_of_nonneg_right (hu.trans (mul_le_mul_of_nonneg_left hl (by positivity))) hK
      _ = _ := by ring
  have hsum := Finset.sum_le_card_nsmul (W x) (fun v => (μ (some v)).toReal) _ hbound
  rw [nsmul_eq_mul] at hsum
  have htotal := μ.tsum_coe
  rw [Probability.tsum_option_eq, tsum_eq_sum (s := W x) hvalid] at htotal
  ennreal_to_real at htotal ⊢
  rw [div_le_iff₀ hN]
  have hc : (1 - ε) * (1 + ε / 8) ^ 2 ≤ 1 - ε / 4 := by
    nlinarith [sq_nonneg ε, mul_nonneg (sq_nonneg ε) he]
  have hge : 1 - ε / 4 ≤ ((μ (some w)).toReal * (W x).card) * (1 + ε / 8) ^ 2 := by
    nlinarith only [hsum, htotal, hf]
  exact le_of_mul_le_mul_right (hc.trans hge) (by positivity : 0 < (1 + ε / 8) ^ 2)

/-- The bounded retry and its extra precision preserve strict polynomial running time. -/
theorem IsFPAUS.isPPTOn_retrySampler (hS : IsFPAUS enc W S) :
    IsPPTOn (encPair enc encUnary) (encOption encBits) (Function.uncurry (retrySampler S)) := by
  have hprec : ComputableInPolyTime (fun a : α × ℕ => a.2 + 2) (encPair enc encUnary) encUnary := by
    fun_prop
  have hp := hS.isPPTOn.preprocess ((ComputableInPolyTime.fst enc encUnary).prod hprec)
  have hj : ComputableInPolyTime (Option.join (α := List Bool)) (encOption (encOption encBits))
      (encOption encBits) :=
    ((ComputableInPolyTime.optionGetD (encOption encBits)).comp
      (ComputableInPolyTime.id'.prod (ComputableInPolyTime.const none))).of_enc_eq fun o => by
        cases o <;> rfl
  exact (hp.retry (good := fun o : Option (List Bool) => o.isSome) (by fun_prop) hprec).map hj

end Cslib.Complexity
